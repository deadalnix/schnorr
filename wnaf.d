module crypto.wnaf;

/**
 * This structure allows to do scalar*point multiplication.
 *
 * While this multiplier isn't as fast as Generator, but doesn't
 * require heavy precomputation, so it is well suited to multiply
 * points which aren't going to be reused often.
 *
 * It is hardened against side channel attack so is perfect for
 * use cases such as ECDH, where the point we need to multiply
 * won't be reused numerous time.
 */
struct Wnaf(uint N) {
private:
	static assert(N > 1 && N <= 8, "N must be between 2 and 8");
	
	enum Steps = ((255 - 1) / N) + 1;
	enum TableSize = 1 << (N - 1);
	
	/**
	 * When N is a multiple of 255, we can save one step by negating
	 * the scalar such as it fit on 255 bits and save one step. The
	 * drawback is that we can't negate the scalar to make sure it is
	 * odd anymore. In this case, we skew the value of the scalar by 1
	 * for even numbers and by 2 for odd ones.
	 *
	 * This require one extra point addition at the end to cancel the
	 * skew, but it is worth it if we can save one step as we save N
	 * point squaring.
	 */
	enum NeedSkew = Steps <= (255 / N);
	
	/**
	 * If N is not a divisor of 255 or 256, we have some extra bits
	 * in our w-NAF representation. In this case, we can save a few
	 * doubling in the first round.
	 */
	enum ExtraBits = (N * Steps) - (256 - NeedSkew);
	enum HasExtraBits = ExtraBits != 0;
	
	/**
	 * Each one these integers contains a bit sign in LSB, plus
	 * an index for the multiplication table is the remaining bits.
	 *
	 * It can interpeted as follow:
	 * Value:  0  1  2  3  4  5  6  7  8  9  10 ...
	 * w-NAF: -1  1 -3  3 -5  5 -7  7 -9  9 -11 ...
	 */
	ubyte[Steps] lookup;
	static if (NeedSkew) {
		bool negated;
		bool odd;
	}
	
public:
	import crypto.scalar;
	this(Scalar s) {
		/**
		 * w-NAF require that the scalar is odd so ScalarBuf will
		 * negate even scalars.
		 */
		static if (NeedSkew) {
			bool flipsign = false;
			auto buf = ScalarBuf(s, negated, odd);
		} else {
			bool flipsign;
			auto buf = ScalarBuf(s, flipsign);
		}
		
		static pack(int u, bool flipsign) {
			/**
			 * If u is positive, this ia noop. If it is negative, then
			 * all bits are flipped. Because the LSB is known to be 1,
			 * flipping the bits are the same as in the complement.
			 *
			 * The LSB is 0 for negative, 1 for positive, higher bits
			 * are the absolute value and can be used as indices.
			 */
			return ubyte(((u ^ flipsign) ^ (u >> 31)) & 0xff);
		}
		
		auto u = buf.extract();
		foreach (i; 1 .. Steps - HasExtraBits) {
			auto bits = buf.extract();
			
			/**
			 * If the current number is even, we need to correct it such as
			 * it is odd, so we create an all ones mask if even, 0 if odd.
			 */
			auto even = (bits & 0x01) - 1;
			
			/**
			 * To make it odd, we can either add or remove 1. We want
			 * the previous digit to stay in range, so if it is positive,
			 * we produce a 1, or a -1 if it isn't.
			 */
			auto sign = (u >> 31) | 0x01;
			
			// We add or remove 1 to make this odd.
			bits += (sign & even);
			
			/**
			 * We compensate the addition in the previous digit by adding or
			 * removing 16. We knows it stays in range because we subtract or
			 * add depending on its sign, and because it is odd, so non zero.
			 */
			u -= ((sign & even) << N);
			
			// We computed one w-NAF digit, pack it.
			lookup[i - 1] = pack(u, flipsign);
			
			// Get ready for the next round.
			u = bits;
		}
		
		/**
		 * This does an extra round but shift the bits right such as
		 * some point doubling can be saved when multiplying.
		 */
		static if (HasExtraBits) {
			auto bits = (buf.extract() << ExtraBits);
			auto sign = (u >> 31) | 0x01;
			
			bits += sign;
			u -= (sign << (N - ExtraBits));
			
			lookup[Steps - 2] = pack(u, flipsign);
			u = bits;
		}
		
		// Last digit, already corrected.
		lookup[Steps - 1] = pack(u, flipsign);
	}
	
	ubyte wNAFat(uint i) const {
		return lookup[Steps - 1 - i];
	}
	
	import crypto.point;
	auto mul(CartesianPoint p) const {
		// Build a table of odd multiples of p.
		JacobianPoint[TableSize] table;
		
		table[0] = JacobianPoint(p);
		
		// FIXME: Avoid point inversion here.
		auto pdbl = CartesianPoint(p.pdouble());
		table[1] = p.add(pdbl);
		
		foreach (i; 2 .. TableSize) {
			table[i] = table[i - 1].add(pdbl);
		}
		
		static select(ref JacobianPoint[TableSize] table, ubyte n) {
			// The least significant bit is the sign. We get rid of it
			// to get the index we are interested in in the table
			auto idx = n >> 1;
			
			/**
			 * We want to avoid side channels attacks. One of the most common
			 * side channel is memory access, as it impact the cache. To avoid
			 * leaking the secret, we make sure no memory access depends on the
			 * secret. This is achieved by accessing all elements in the table.
			 */
			auto p = table[0];
			foreach (i; 1 .. TableSize) {
				p = JacobianPoint.select(i == idx, table[i], p);
			}
			
			// Finaly we negate the point if the sign is negative.
			auto positive = (n & 0x01) != 0;
			return JacobianPoint.select(positive, p, p.negate());
		}
		
		// For the initial value, we can just look it up in the table.
		auto r = table.select(wNAFat(0));
		
		/**
		 * If we have some extra bits in our w-NAF representation, we
		 * special case the first round to save a few point doubling.
		 */
		static if (HasExtraBits) {
			r = r.pdoublen!(N - ExtraBits)();
			
			// FIXME: Avoid point inversion here.
			r = r.add(CartesianPoint(table.select(wNAFat(1))));
		}
		
		/**
		 * The core multiplication routine. We double by N and add
		 * the value looked up from the table each round.
		 */
		foreach (i; 1 + HasExtraBits .. Steps) {
			r = r.pdoublen!N();
			
			// FIXME: Avoid point inversion here.
			r = r.add(CartesianPoint(table.select(wNAFat(i))));
		}
		
		/**
		 * If we can take advantage of the scalar being smaller, we can't rely
		 * simply on negating it to make sure it is odd. Instead, we skew the
		 * value by 1 for even numbers and 2 for odd ones and need to fixup.
		 */
		static if (NeedSkew) {
			auto fixup = CartesianPoint.select(odd, pdbl, p);
			r = r.add(fixup.negate());
			
			// Negate if we need to.
			r = JacobianPoint.select(negated, r.negate(), r);
		}
		
		return r;
	}
	
private:
	struct ScalarBuf {
		ulong[4] parts;
		
		this(Scalar s, ref bool negated) {
			parts = s.getParts();
			
			// Negate if s is even, to make sure it is odd.
			auto m = (parts[0] & 0x01) - 1;
			
			ulong[4] order;
			order[0] = 0xBFD25E8CD0364141;
			order[1] = 0xBAAEDCE6AF48A03B;
			order[2] = 0xFFFFFFFFFFFFFFFE;
			order[3] = 0xFFFFFFFFFFFFFFFF;
			
			// Make sure we complement, not just bitflip.
			ucent acc = m & 0x01;
			foreach (i; 0 .. 4) {
				acc += (order[i] & m);
				acc += (parts[i] ^ m);
				parts[i] = cast(ulong) acc;
				acc >>= 64;
			}
			
			negated = m != 0;
		}
		
		this(Scalar s, ref bool negated, ref bool odd) {
			parts = s.getParts();
			
			// Mask from the sign.
			auto m = long(parts[3]) >> 63;
			auto skew = (parts[0] ^ m) & 0x01;
			
			ulong[4] order;
			order[0] = 0xBFD25E8CD0364141;
			order[1] = 0xBAAEDCE6AF48A03B;
			order[2] = 0xFFFFFFFFFFFFFFFE;
			order[3] = 0xFFFFFFFFFFFFFFFF;
			
			// We add 1 for even number, 2 for odds.
			// plus one for the complement if apropriate.
			ucent acc = skew + (m & 0x01) + 1;
			foreach (i; 0 .. 4) {
				acc += (order[i] & m);
				acc += (parts[i] ^ m);
				parts[i] = cast(ulong) acc;
				acc >>= 64;
			}
			
			negated = m != 0;
			odd = skew != 0;
		}
		
		auto extract() {
			enum Mask = (ulong(1) << N) - 1;
			int bits = parts[0] & Mask;
			
			parts[0] = (parts[0] >> N) | (parts[1] << (64 - N));
			parts[1] = (parts[1] >> N) | (parts[2] << (64 - N));
			parts[2] = (parts[2] >> N) | (parts[3] << (64 - N));
			parts[3] = parts[3] >> N;
			
			return bits;
		}
	}
}

void main() {
	test!2();
	test!3();
	test!4();
	test!5();
	test!6();
	test!7();
	test!8();
	
	printf("OK\n".ptr);
}

void test(uint N)() {
	import crypto.point;
	auto g = CartesianPoint(Point.getG());
	
	import crypto.scalar;
	auto zero = Scalar(0);
	auto mulzero = Wnaf!N(zero);
	auto zerog = mulzero.mul(g);
	auto inf = CartesianPoint(g.add(g.negate()));
	assert(zerog.opEquals(inf), "0*G == O");
	
	auto one = Scalar(1);
	auto mulone = Wnaf!N(one);
	auto oneg = mulone.mul(g);
	assert(oneg.opEquals(g), "1*G = G");
	
	auto negone = one.negate();
	auto mulnegone = Wnaf!N(negone);
	auto negoneg = mulnegone.mul(g);
	assert(negoneg.opEquals(g.negate()), "-1*G == -G");
	
	auto two = Scalar(2);
	auto multwo = Wnaf!N(two);
	auto twog = multwo.mul(g);
	auto dblg = CartesianPoint(g.pdouble());
	assert(twog.opEquals(dblg), "2*G = G + G");
	
	auto negtwo = two.negate();
	auto mulnegtwo = Wnaf!N(negtwo);
	auto negtwog = mulnegtwo.mul(g);
	assert(negtwog.opEquals(dblg.negate()), "-2*G = -(G + G)");
	
	import crypto.field;
	auto beta = ComputeElement(Beta);
	auto beta2 = beta.square();
	
	// If P = (x, y), Lambda*P = (Beta*x, y)
	auto lambda = Lambda;
	auto mullambda = Wnaf!N(lambda);
	auto lambdag = mullambda.mul(g);
	auto betaxg = CartesianPoint(g.x.mul(beta), g.y, g.infinity);
	assert(lambdag.opEquals(betaxg), "Lambda*G == (Beta*G.x, G.y)");
	
	auto neglambda = lambda.negate();
	auto mulneglambda = Wnaf!N(neglambda);
	auto neglambdag = mulneglambda.mul(g);
	auto negbetaxg = CartesianPoint(g.x.mul(beta), g.y.negate(), g.infinity);
	assert(neglambdag.opEquals(negbetaxg), "-Lambda*G == (Beta*G.x, -G.y)");
	
	auto lambda2 = lambda.square();
	auto mullambda2 = Wnaf!N(lambda2);
	auto lambda2g = mullambda2.mul(g);
	auto beta2xg = CartesianPoint(g.x.mul(beta2), g.y, g.infinity);
	assert(lambda2g.opEquals(beta2xg), "Lambda^2*G == (Beta^2*G.x, G.y)");
	
	auto neglambda2 = lambda2.negate();
	auto mulneglambda2 = Wnaf!N(neglambda2);
	auto neglambda2g = mulneglambda2.mul(g);
	auto negbeta2xg = CartesianPoint(g.x.mul(beta2), g.y.negate(), g.infinity);
	assert(
		neglambda2g.opEquals(negbeta2xg),
		"-Lambda^2*G == (Beta^2*G.x, -G.y)",
	);
}

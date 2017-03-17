module crypto.scalar;

struct Scalar {
private:
	// This is little endian all the way down.
	ulong[4] parts;
	
	this(ulong[4] parts) {
		this.parts = parts;
	}
	
	this(ulong a, ulong b, ulong c, ulong d) {
		parts[0] = d;
		parts[1] = c;
		parts[2] = b;
		parts[3] = a;
	}
	
public:
	this(ulong s) {
		this(0, 0, 0, s);
	}
	
	auto getParts() const {
		return parts;
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		auto o = order();
		auto c = o.getParts();
		
		auto mask = ulong(isZero()) - 1;
		
		ulong[4] r;
		ucent acc = 1;
		
		// This must be unrolled, or the compiler
		// figures out it is a noop when mask is 0.
		// FIXME: The compiler is still a smart ass and uses CMOV.
		acc += c[0];
		acc += ~parts[0];
		r[0] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += c[1];
		acc += ~parts[1];
		r[1] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += c[2];
		acc += ~parts[2];
		r[2] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += c[3];
		acc += ~parts[3];
		r[3] = (cast(ulong) acc) & mask;
		
		return Scalar(r);
	}
	
	// auto opBinary(string op : "+")(Scalar b) const {
	auto add(Scalar b) const {
		auto r = addImpl(this, b);
		return r.reduce();
	}
	
	// auto opBinary(string op : "*")(Scalar b) const {
	auto mul(Scalar b) const {
		auto r = mulImpl(this, b);
		return r.reduce();
	}
	
	auto square() const {
		auto r = mulImpl(this, this);
		return r.reduce();
	}
	
	auto squaren(uint N)() const {
		Scalar r = this;
		for (uint i = 0; i < N; i++) {
			r = r.square();
		}
		
		return r;
	}
	
	auto opEquals(Scalar b) const {
		ulong neq;
		foreach (i; 0 .. 4) {
			neq |= (parts[i] ^ b.parts[i]);
		}
		
		return !neq;
	}
	
	auto isZero() const {
		ulong bits;
		foreach (i; 0 .. 4) {
			bits |= parts[i];
		}
		
		return bits == 0;
	}
	
	auto inverse() const {
		return inverseImpl(this);
	}
	
	auto serialize() const {
		import crypto.uint256;
		auto i = Uint256(parts);
		return i.serialize();
	}
	
	static unserializeOrZero(ref const(ubyte)[] buffer) {
		import crypto.uint256;
		auto i = Uint256.unserialize(buffer);
		
		// If i is greater than the group order, we return 0.
		i = Uint256.select(i.opCmp(order()) >= 0, Uint256(0), i);
		return Scalar(i.getParts());
	}
	
	static select(bool cond, Scalar a, Scalar b) {
		auto maska = -ulong(cond);
		auto maskb = ~maska;
		
		ulong[4] r;
		foreach (i; 0 .. 4) {
			// FIXME: The compiler is still a smart ass and uses CMOV.
			r[i] = (a.parts[i] & maska) | (b.parts[i] & maskb);
		}
		
		return Scalar(r);
	}
	
private:
	void dump() const {
		printf(
			"%.16lx %.16lx %.16lx %.16lx".ptr,
			parts[3],
			parts[2],
			parts[1],
			parts[0],
		);
	}
	
	static order() {
		/**
		 * secp256k1's order.
		 *
		 * The number of point on the curve that can be reached
		 * by multiplying G by a scalar. All scalar arithmetic
		 * is done modulo the order.
		 */
		import crypto.uint256;
		return Uint256(
			0xFFFFFFFFFFFFFFFF,
			0xFFFFFFFFFFFFFFFE,
			0xBAAEDCE6AF48A03B,
			0xBFD25E8CD0364141,
		);
	}
	
	static addImpl(Scalar a, Scalar b) {
		ulong[4] r;
		ucent acc;
		
		foreach (i; 0 .. 4) {
			acc += a.parts[i];
			acc += b.parts[i];
			r[i] = cast(ulong) acc;
			acc >>= 64;
		}
		
		return AddResult(r, !!(acc & 0x01));
	}
	
	struct AddResult {
		ulong[4] result;
		bool carry;
		
		this(ulong[4] r, bool c) {
			result = r;
			carry = c;
		}
		
		auto needReduce() const {
			import crypto.uint256;
			auto r = Uint256(result);
			return (r.opCmp(order()) >= 0) | carry;
		}
		
		auto reduce() const {
			auto o = order();
			auto nego = o.negate();
			auto c = nego.getParts();
			
			auto mask = -ulong(needReduce());
			
			ulong[4] r;
			ucent acc;
			
			// This must be unrolled, or the compiler
			// figures out it is a noop when mask is 0.
			acc += c[0] & mask;
			acc += result[0];
			r[0] = cast(ulong) acc;
			acc >>= 64;
			acc += c[1] & mask;
			acc += result[1];
			r[1] = cast(ulong) acc;
			acc >>= 64;
			acc += c[2] & mask;
			acc += result[2];
			r[2] = cast(ulong) acc;
			acc >>= 64;
			acc += c[3] & mask;
			acc += result[3];
			r[3] = cast(ulong) acc;
			
			return Scalar(r);
		}
	}
	
	static mulImpl(Scalar a, Scalar b) {
		ulong[4] low, high;
		Accumulator acc;
		
		// Just the plain old school multiplication.
		acc.muladd(a.parts[0], b.parts[0]);
		low[0] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[1]);
		acc.muladd(a.parts[1], b.parts[0]);
		low[1] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[2]);
		acc.muladd(a.parts[1], b.parts[1]);
		acc.muladd(a.parts[2], b.parts[0]);
		low[2] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[3]);
		acc.muladd(a.parts[1], b.parts[2]);
		acc.muladd(a.parts[2], b.parts[1]);
		acc.muladd(a.parts[3], b.parts[0]);
		low[3] = acc.extract();
		
		acc.muladd(a.parts[1], b.parts[3]);
		acc.muladd(a.parts[2], b.parts[2]);
		acc.muladd(a.parts[3], b.parts[1]);
		high[0] = acc.extract();
		
		acc.muladd(a.parts[2], b.parts[3]);
		acc.muladd(a.parts[3], b.parts[2]);
		high[1] = acc.extract();
		
		acc.muladd(a.parts[3], b.parts[3]);
		high[2] = acc.extract();
		
		high[3] = acc.extract();
		
		return MulResult(high, low);
	}
	
	struct Accumulator {
		ulong c0;
		ulong c1;
		uint c2;
		
		auto add(ulong a) {
			ucent acc = a;
			
			acc += c0;
			c0 = cast(ulong) acc;
			acc >>= 64;
			
			acc += c1;
			c1 = cast(ulong) acc;
			acc >>= 64;
			
			acc += c2;
			c2 = cast(uint) acc;
		}
		
		auto muladd(ulong a, ulong b) {
			ucent acc = a;
			acc *= b;
			
			// a*b + c cannot exceed 128 bits
			// if a, b and c are 64 bits.
			acc += c0;
			c0 = cast(ulong) acc;
			acc >>= 64;
			
			acc += c1;
			c1 = cast(ulong) acc;
			acc >>= 64;
			
			acc += c2;
			c2 = cast(uint) acc;
			acc >>= 32;
		}
		
		auto extract() {
			auto r = c0;
			c0 = c1;
			c1 = c2;
			c2 = 0;
			return r;
		}
		
		auto clear() {
			c0 = 0;
			c1 = 0;
			c2 = 0;
		}
	}
	
	struct MulResult {
		ulong[4] low, high;
		
		this(ulong[4] h, ulong[4] l) {
			low = l;
			high = h;
		}
		
		auto reduce() const {
			auto o = order();
			auto nego = o.negate();
			auto c = nego.getParts();
			
			// NB: We could make this algorithm independent of
			// base by computing how many leading zero c has.
			// Each reduction steps eliminates that many bits.
			assert(c[2] == 1);
			assert(c[3] == 0);
			
			/**
			 * Reduce to 385 bits via r = low + high * -base.
			 *
			 * -base is a 129 digit number and high a 256bits one.
			 * The end result of this operation is 385bits long.
			 */
			ulong[4] rlow;
			Accumulator rhigh;
			
			Accumulator acc;
			
			acc.add(low[0]);
			acc.muladd(high[0], c[0]);
			rlow[0] = acc.extract();
			
			acc.add(low[1]);
			acc.muladd(high[1], c[0]);
			acc.muladd(high[0], c[1]);
			rlow[1] = acc.extract();
			
			acc.add(low[2]);
			acc.muladd(high[2], c[0]);
			acc.muladd(high[1], c[1]);
			acc.muladd(high[0], c[2]);
			rlow[2] = acc.extract();
			
			acc.add(low[3]);
			acc.muladd(high[3], c[0]);
			acc.muladd(high[2], c[1]);
			acc.muladd(high[1], c[2]);
			rlow[3] = acc.extract();
			
			acc.muladd(high[3], c[1]);
			acc.muladd(high[2], c[2]);
			rhigh.c0 = acc.extract();
			
			acc.muladd(high[3], c[2]);
			rhigh.c1 = acc.extract();
			rhigh.c2 = cast(uint) acc.extract();
			
			// Reproduce the process to go from 385 to 258 bits.
			ulong[4] r;
			uint carries;
			
			acc.clear();
			
			acc.add(rlow[0]);
			acc.muladd(rhigh.c0, c[0]);
			r[0] = acc.extract();
			
			acc.add(rlow[1]);
			acc.muladd(rhigh.c1, c[0]);
			acc.muladd(rhigh.c0, c[1]);
			r[1] = acc.extract();
			
			acc.add(rlow[2]);
			acc.muladd(rhigh.c2, c[0]);
			acc.muladd(rhigh.c1, c[1]);
			acc.muladd(rhigh.c0, c[2]);
			r[2] = acc.extract();
			
			acc.add(rlow[3]);
			acc.muladd(rhigh.c2, c[1]);
			acc.muladd(rhigh.c1, c[2]);
			r[3] = acc.extract();
			
			acc.muladd(rhigh.c2, c[2]);
			carries = cast(uint) acc.extract();
			
			// Last round, we know that we have at most one carry,
			// So we do it the add way.
			ucent uacc;
			
			foreach (i; 0 .. 4) {
				uacc += r[i];
				uacc += ucent(c[i]) * carries;
				r[i] = cast(ulong) uacc;
				uacc >>= 64;
			}
			
			auto ar = AddResult(r, !!(uacc & 0x01));
			return ar.reduce();
		}
	}
	
	static inverseImpl(Scalar a) {
		/**
		 * As it turns out, a ^ -1 == a ^ (p - 2) mod p.
		 *
		 * As a first step, we compute various value of a ^ (2 ^ n - 1)
		 *
		 * Then we shift the exponent left by squaring, and add ones using
		 * the precomputed powers using a ^ x * a ^ y = a ^ (x + y).
		 */
		
		// XXX: Computing a ^ 0b101 and a ^ 0b1001 would save some mul.
		// Compute various (2 ^ n - 1) powers of a.
		auto a02 = a.mul(a.square());
		auto a03 = a.mul(a02.square());
		auto a04 = a.mul(a03.square());
		
		auto a06 = a04.squaren!2();
		a06 = a06.mul(a02);
		
		auto a07 = a.mul(a06.square());
		auto a08 = a.mul(a07.square());
		
		auto a15 = a08.squaren!7();
		a15 = a15.mul(a07);
		
		auto a30 = a15.squaren!15();
		a30 = a30.mul(a15);
		
		auto a60 = a30.squaren!30();
		a60 = a60.mul(a30);
		
		auto a120 = a60.squaren!60();
		a120 = a120.mul(a60);
		
		auto a127 = a120.squaren!7();
		a127 = a127.mul(a07);
		
		// The 127 heading ones of the base and one 0.
		// 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE
		auto r = a127;
		
		/**
		 * Next digit is 0xBAAEDCE6AF48A03B
		 * We also have 0 remaining from previous digits.
		 *
		 * 0xBAAE = 10111010 10101110
		 * 0xDCE6 = 11011100 11100110
		 * 0xAF48 = 10101111 01001000
		 * 0xA03B = 10100000 00111011
		 */
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 0111
		r = r.squaren!4();
		r = r.mul(a03);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 0111
		r = r.squaren!4();
		r = r.mul(a03);
		
		// 011
		r = r.squaren!3();
		r = r.mul(a02);
		
		// 0111
		r = r.squaren!4();
		r = r.mul(a03);
		
		// 00111
		r = r.squaren!5();
		r = r.mul(a03);
		
		// 0011
		r = r.squaren!4();
		r = r.mul(a02);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 01111
		r = r.squaren!5();
		r = r.mul(a04);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 001
		r = r.squaren!3();
		r = r.mul(a);
		
		// 0001
		r = r.squaren!4();
		r = r.mul(a);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 0000000111
		r = r.squaren!10();
		r = r.mul(a03);
		
		/**
		 * Next digit is 0xBFD25E8CD0364141 minus 2.
		 * We also have 011 remaining from previous digits.
		 *
		 * 0xBFD2 = 10111111 11010010
		 * 0x5E8C = 01011110 10001100
		 * 0xD036 = 11010000 00110110
		 * 0x413F = 01000001 00111111
		 */
		// 0111
		r = r.squaren!4();
		r = r.mul(a03);
		
		// 011111111
		r = r.squaren!9();
		r = r.mul(a08);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 001
		r = r.squaren!3();
		r = r.mul(a);
		
		// 001
		r = r.squaren!3();
		r = r.mul(a);
		
		// 01111
		r = r.squaren!5();
		r = r.mul(a04);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 00011
		r = r.squaren!5();
		r = r.mul(a02);
		
		// 0011
		r = r.squaren!4();
		r = r.mul(a02);
		
		// 01
		r = r.squaren!2();
		r = r.mul(a);
		
		// 00000011
		r = r.squaren!8();
		r = r.mul(a02);
		
		// 011
		r = r.squaren!3();
		r = r.mul(a02);
		
		// 001
		r = r.squaren!3();
		r = r.mul(a);
		
		// 000001
		r = r.squaren!6();
		r = r.mul(a);
		
		// 00111111
		r = r.squaren!8();
		r = r.mul(a06);
		
		return r;
	}
}

/**
 * Lambda is is a non 1 cube root of 1 modulo the group order.
 */
enum Lambda = Scalar(
	0x5363ad4cc05c30e0,
	0xa5261c028812645a,
	0x122e22ea20816678,
	0xdf02967c1b23bd72,
);

void main() {
	static testAdd(Scalar a, Scalar b, Scalar r) {
		assert(r.opEquals(a.add(b)), "a + b == r");
		assert(r.opEquals(b.add(a)), "b + a == r");
	}
	
	static testNeg(Scalar n, Scalar negn) {
		assert(n.opEquals(negn.negate()), "n = -negn");
		assert(negn.opEquals(n.negate()), "-n = negn");
	}
	
	static testMul(Scalar a, Scalar b, Scalar r) {
		assert(r.opEquals(a.mul(b)), "a * b = r");
		assert(r.opEquals(b.mul(a)), "b * a = r");
	}
	
	auto zero = Scalar(0);
	testAdd(zero, zero, zero);
	testNeg(zero, zero);
	testMul(zero, zero, zero);
	
	assert(zero.opEquals(zero.square()), "0^2 == 0");
	
	auto one = Scalar(1);
	testAdd(zero, one, one);
	testMul(zero, one, zero);
	testMul(one, one, one);
	
	assert(one.opEquals(one.square()), "1^2 == 1");
	
	auto two = Scalar(2);
	testAdd(one, one, two);
	testAdd(zero, two, two);
	testMul(zero, two, zero);
	testMul(one, two, two);
	
	auto four = Scalar(4);
	assert(four.opEquals(two.square()), "2^2 == 4");
	
	auto negone = Scalar(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFE,
		0xBAAEDCE6AF48A03B,
		0xBFD25E8CD0364140,
	);
	
	testAdd(one, negone, zero);
	testNeg(one, negone);
	testMul(one, negone, negone);
	testMul(negone, negone, one);
	
	assert(one.opEquals(negone.square()), "(-1)^2 == 1");
	
	auto negtwo = Scalar(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFE,
		0xBAAEDCE6AF48A03B,
		0xBFD25E8CD036413F,
	);
	
	testAdd(one, negtwo, negone);
	testAdd(negone, negone, negtwo);
	testNeg(two, negtwo);
	testMul(negone, two, negtwo);
	testMul(negone, negtwo, two);
	
	// Squaring.
	auto n = Scalar(
		0x7aff790c9a22b99c,
		0x94856ed9231e3fe9,
		0x188b5dd4e6107cc4,
		0x9982b148178f639f,
	);
	
	auto n2 = Scalar(
		0x7eac0091012b3f31,
		0x37841a6cb8c280d7,
		0x66d6a03f95ab4e89,
		0xc74024c254a54050,
	);
	
	auto nsqr = n.square();
	assert(nsqr.opEquals(n2), "n^2 == n2");
	
	// Test inversion.
	testMul(one, one.inverse(), one);
	testMul(negone, negone.inverse(), one);
	testMul(two, two.inverse(), one);
	testMul(negtwo, negtwo.inverse(), one);
	testMul(four, four.inverse(), one);
	testMul(n, n.inverse(), one);
	testMul(n2, n2.inverse(), one);
	
	// Lambda
	auto lambda = Lambda;
	auto lambda2 = lambda.square();
	auto lambda3 = lambda2.mul(lambda);
	auto lambda4 = lambda2.square();
	auto lambda6 = lambda4.mul(lambda2);
	
	assert(one.opEquals(lambda3), "lambda^3 == 1");
	assert(one.opEquals(lambda6), "lambda2^3 == 1");
	
	// Serialization
	static testSerialization(Scalar a) {
		auto buf = a.serialize();
		auto bufSlice = buf.ptr[0 .. buf.length];
		auto b = Scalar.unserializeOrZero(bufSlice);
		
		assert(a.opEquals(b), "serialization failed");
	}
	
	testSerialization(zero);
	testSerialization(one);
	testSerialization(two);
	testSerialization(negone);
	testSerialization(negtwo);
	testSerialization(lambda);
	testSerialization(lambda2);
	testSerialization(lambda4);
	
	// Test invalid deserialization.
	auto s = Scalar.order();
	auto sbuf = s.serialize();
	auto sSlice = sbuf.ptr[0 .. sbuf.length];
	auto ss = Scalar.unserializeOrZero(sSlice);
	
	assert(ss.opEquals(zero), "invalid unserialization yield zero");
	
	printf("OK\n".ptr);
}

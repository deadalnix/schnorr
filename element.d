module crypto.element;

struct Element {
private:
	// This is little endian all the way down.
	ulong[4] parts;
	
public:
	this(ulong[4] parts) {
		this.parts = parts;
	}
	
	this(ulong a, ulong b, ulong c, ulong d) {
		parts[0] = d;
		parts[1] = c;
		parts[2] = b;
		parts[3] = a;
	}
	
	this(ulong s) {
		this(0, 0, 0, s);
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		auto p = prime();
		auto c = p.getParts();
		
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
		
		return Element(r);
	}
	
	auto opEquals(Element b) const {
		ulong neq;
		foreach (i; 0 .. 4) {
			neq |= parts[i] ^ b.parts[i];
		}
		
		return neq == 0;
	}
	
	auto isZero() const {
		ulong bits;
		foreach (i; 0 .. 4) {
			bits |= parts[i];
		}
		
		return bits == 0;
	}
	
	auto isEven() const {
		return (parts[0] & 0x01) == 0;
	}
	
	auto isOdd() const {
		return (parts[0] & 0x01) == 1;
	}
	
	auto serialize() const {
		import crypto.uint256;
		auto i = Uint256(parts);
		return i.serialize();
	}
	
	static unserialize(ref const(ubyte)[] buffer) {
		import crypto.uint256;
		auto i = Uint256.unserializeInRange(buffer, prime());
		return Element(i.getParts());
	}
	
	static unserializeOrZero(ref const(ubyte)[] buffer) {
		import crypto.uint256;
		auto i = Uint256.unserializeInRangeOrZero(buffer, prime());
		return Element(i.getParts());
	}
	
	static select(bool cond, Element a, Element b) {
		auto maska = -ulong(cond);
		auto maskb = ~maska;
		
		ulong[4] r;
		foreach (i; 0 .. 4) {
			// FIXME: The compiler is still a smart ass and uses CMOV.
			r[i] = (a.parts[i] & maska) | (b.parts[i] & maskb);
		}
		
		return Element(r);
	}
	
private:
	void dump() const {
		import core.stdc.stdio;
		printf(
			"%.16lx %.16lx %.16lx %.16lx".ptr,
			parts[3],
			parts[2],
			parts[1],
			parts[0],
		);
	}
	
	static prime() {
		// secp256k1's finite field prime parameter.
		import crypto.uint256;
		return Uint256(
			0xFFFFFFFFFFFFFFFF,
			0xFFFFFFFFFFFFFFFF,
			0xFFFFFFFFFFFFFFFF,
			0xFFFFFFFEFFFFFC2F,
		);
	}
}

/**
 * Beta is is a non 1 cube root of 1 in Fp.
 */
enum Beta = Element(
	0x7ae96a2b657c0710,
	0x6e64479eac3434e9,
	0x9cf0497512f58995,
	0xc1396c28719501ee,
);

void testElement() {
	static testNeg(Element n, Element negn) {
		assert(n.opEquals(negn.negate()), "n = -negn");
		assert(negn.opEquals(n.negate()), "-n = negn");
	}
	
	auto zero = Element(0);
	
	testNeg(zero, zero);
	assert(zero.isEven(), "0 is even");
	assert(zero.isZero(), "0 is zero");
	
	auto one = Element(1);
	assert(one.isOdd(), "1 is odd");
	assert(!one.isZero(), "1 is not zero");
	
	auto two = Element(2);
	assert(two.isEven(), "2 is even");
	
	auto three = Element(3);
	assert(three.isOdd(), "3 is odd");
	
	auto four = Element(4);
	assert(four.isEven(), "4 is even");
	
	auto negone = Element(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFEFFFFFC2E,
	);
	
	testNeg(one, negone);
	assert(negone.isEven(), "-1 is even");
	
	auto negtwo = Element(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFEFFFFFC2D,
	);
	
	testNeg(two, negtwo);
	assert(negtwo.isOdd(), "-2 is odd");
	
	auto beta = Beta;
	auto negbeta = beta.negate();
	testNeg(beta, negbeta);
	
	// Serialization
	static testSerialization(Element a) {
		auto buf = a.serialize();
		auto bufSlice = buf.ptr[0 .. buf.length];
		
		auto b = Element.unserializeOrZero(bufSlice);
		assert(a.opEquals(b), "serialization failed");
		
		bufSlice = buf.ptr[0 .. buf.length];
		b = Element.unserialize(bufSlice);
		assert(a.opEquals(b), "serialization failed");
	}
	
	testSerialization(zero);
	testSerialization(one);
	testSerialization(two);
	testSerialization(negone);
	testSerialization(negtwo);
	testSerialization(beta);
	testSerialization(negbeta);
	
	// Invalid serialization.
	static testSerializationFail(ubyte[] buf) {
		try {
			Element.unserialize(buf);
			assert(0, "unserialize should have thrown");
		} catch(Exception e) {}
		
		try {
			auto es = Element.unserializeOrZero(buf);
			assert(0, "unserialize should have thrown");
		} catch(Exception e) {}
	}
	
	ubyte[33] buf;
	testSerializationFail(buf.ptr[0 .. 0]);
	testSerializationFail(buf.ptr[0 .. 31]);
	
	// Buffer advanced properly.
	auto bufSlice = buf.ptr[0 .. 33];
	Element.unserialize(bufSlice);
	assert(
		bufSlice.length == 1 && bufSlice.ptr is &buf[32],
		"buffer did not advance as expected",
	);
	
	// Test out of range deserialization.
	auto s = Element.prime();
	auto sbuf = s.serialize();
	auto sSlice = sbuf.ptr[0 .. sbuf.length];
	auto ss = Element.unserializeOrZero(sSlice);
	
	assert(ss.opEquals(zero), "invalid unserialization yield zero");
}

struct ComputeElement {
private:
	/**
	 * We need high throuput operatiosn on field elements. To increase IPL,
	 * we represent field element as 1x48 + 4x52 bits elements rather than
	 * 4x64 bits. This allows to let carry accumulate in the MSB and
	 * only renormalize when required.
	 *
	 * This is little endian.
	 */
	ulong[5] parts;
	
	/**
	 * We count how many carries we accumulate in the MSB. We only have
	 * 12 bits, so if this gets too high, we need to propagate carries.
	 */
	uint carryCount = 0;
	
	enum Mask = (1UL << 52) - 1;
	enum MsbMask = (1UL << 48) - 1;
	
	/**
	 * secp256k1 is defined over a prime field over
	 * FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF
	 * FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F
	 *
	 * We leverage the fact that this number's complement
	 * fit on the 52 bits parts we are working on to
	 * speedup calculations.
	 */
	enum Complement = 0x1000003D1;

	this(ulong[4] p, uint carryCount) {
		parts[0] = p[0] & Mask;
		parts[1] = (p[0] >> 52 | p[1] << 12) & Mask;
		parts[2] = (p[1] >> 40 | p[2] << 24) & Mask;
		parts[3] = (p[2] >> 28 | p[3] << 36) & Mask;
		parts[4] = p[3] >> 16;
		
		this.carryCount = carryCount;
	}
	
	this(ulong[5] parts, uint carryCount) {
		this.parts = parts;
		this.carryCount = carryCount;
	}
	
public:
	this(Element e) {
		this(e.parts, 0);
	}
	
	this(ulong s) {
		this(Element(s));
	}
	
	auto zeroCheck() {
		auto r = NormalizationResult(this);
		return r.zeroCheck();
	}
	
	static select(bool cond, ComputeElement a, ComputeElement b) {
		auto maska = -ulong(cond);
		auto maskb = ~maska;
		
		ulong[5] r;
		foreach (i; 0 .. 5) {
			// FIXME: The compiler is still a smart ass and uses CMOV.
			r[i] = (a.parts[i] & maska) | (b.parts[i] & maskb);
		}
		
		auto cc = a.carryCount > b.carryCount ? a.carryCount : b.carryCount;
		return ComputeElement(r, cc);
	}
	
	auto normalize() const {
		auto r = NormalizationResult(this);
		return r.reduce();
	}
	
	auto isEven() const {
		auto r = NormalizationResult(this);
		return r.isEven();
	}
	
	auto isOdd() const {
		auto r = NormalizationResult(this);
		return r.isOdd();
	}
	
	// auto opBinary(string op : "+")(Scalar b) const {
	auto add(ComputeElement b) const {
		auto a = this;
		
		// FIXME: in contract.
		assert(a.carryCount < 2048);
		assert(b.carryCount < 2048);
		
		ulong[5] parts;
		foreach (i; 0 .. 5) {
			parts[i] = a.parts[i] + b.parts[i];
		}
		
		auto cc = a.carryCount + b.carryCount + 1;
		auto r = ComputeElement(parts, cc);
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (cc < 2048) {
			return r;
		}
		
		// We have 12bits to accumulate carries.
		// It means we can't add numbers which accumulated
		// 2048 carries or more.
		auto nr = NormalizationResult(r);
		return nr.raw;
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		auto p = prime();
		auto cc = carryCount + 1;
		
		ulong[5] r;
		foreach (i; 0 .. 5) {
			r[i] = p.parts[i] * cc - parts[i];
		}
		
		/**
		 * Technically, 0 will negate as p, so we should  count this
		 * as a carry. However, it is preferable to consider p has not
		 * being a carry, as it'll negate properly anyway, and this is
		 * the only operation that depends on the carry count.
		 *
		 * We still want to make sure it isn't 0 as 0 means normalized.
		 */
		return ComputeElement(r, carryCount | (carryCount == 0));
	}
	
	// auto opBinary(string op : "-")(Scalar b) const {
	auto sub(ComputeElement b) const {
		return add(b.negate());
	}
	
	// auto opBinary(string op : "*")(Scalar b) const {
	auto mul(ComputeElement b) const {
		ComputeElement a = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (a.carryCount >= 1024) {
			auto na = NormalizationResult(a);
			a = na.raw;
		}
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (b.carryCount >= 1024) {
			auto nb = NormalizationResult(b);
			b = nb.raw;
		}
		
		return ComputeElement(mulImpl(a, b), 1);
	}
	
	auto square() const {
		auto e = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (e.carryCount >= 1024) {
			auto ne = NormalizationResult(e);
			e = ne.raw;
		}
		
		return ComputeElement(mulImpl(e, e), 1);
	}
	
	auto squaren(uint N)() const {
		auto r = this;
		for (uint i = 0; i < N; i++) {
			r = r.square();
		}
		
		return r;
	}
	
	auto opEquals(ComputeElement b) const {
		auto diff = sub(b);
		return diff.zeroCheck();
	}
	
	auto inverse() const {
		return inverseImpl(this);
	}
	
	auto sqrt() const {
		return sqrtImpl(this);
	}
	
	// FIXME: For some reason, auto is detected as const by SDC.
	// This needs to be figured out.
	ComputeElement muln(uint N)() const {
		static assert(N > 0 && N < 2048, "N must be between 1 and 2048");
		
		ComputeElement r = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if ((r.carryCount + 1) * N >= 2048) {
			auto nr = NormalizationResult(r);
			r = nr.raw;
		}
		
		foreach (i; 0 .. 5) {
			r.parts[i] *= N;
		}
		
		// Existing carries accumulating.
		r.carryCount *= N;
		
		// Carries from LSB due to additions.
		r.carryCount += N - 1;
		
		return r;
	}
	
private:
	void dump() const {
		import core.stdc.stdio;
		printf(
			"%.16lx %.16lx %.16lx %.16lx %.16lx (%d)".ptr,
			parts[4],
			parts[3],
			parts[2],
			parts[1],
			parts[0],
			carryCount,
		);
	}
	
	static prime() {
		// secp256k1's finite field prime parameter.
		auto p = Element.prime();
		return ComputeElement(p.getParts(), 1);
	}
	
	struct NormalizationResult {
		ulong[5] parts;
		
		this(ComputeElement e) {
			// We start by reducing all the MSB bits in part[4]
			// so that we will at most have one carry to reduce.
			parts = e.parts;
			ulong acc = (parts[4] >> 48) * Complement;
			
			// Clear the carries in part[4].
			parts[4] &= MsbMask;
			
			// Propagate.
			foreach (i; 0 .. 5) {
				acc += parts[i];
				parts[i] = acc & Mask;
				acc >>= 52;
			}
			
			assert(acc == 0, "Residual carry detected");
		}
		
		@property raw() const {
			return ComputeElement(parts, 1);
		}
		
		@property overflow() const {
			// Check if there is an overflow.
			auto msbAllOnes = parts[4] == MsbMask;
			msbAllOnes &= (parts[1] & parts[2] & parts[3]) == Mask;
			auto tooGreat = msbAllOnes & (parts[0] >= 0xFFFFEFFFFFC2F);
			auto o = (parts[4] >> 48) | tooGreat;
			
			// XXX: out contract
			assert(o < 2, "Residual carry detected");
			return o;
		}
		
		auto reduce() const {
			ulong[4] r;
			ucent acc = -ulong(overflow) & Complement;
			acc += parts[0];
			acc += ucent(parts[1]) << 52;
			r[0] = cast(ulong) acc;
			acc >>= 64;
			acc += ucent(parts[2]) << 40;
			r[1] = cast(ulong) acc;
			acc >>= 64;
			acc += ucent(parts[3]) << 28;
			r[2] = cast(ulong) acc;
			acc >>= 64;
			acc += ucent(parts[4] << 16);
			r[3] = cast(ulong) acc;
			
			assert((acc >> 64) == overflow, "Inconsistent carry detected");
			
			return Element(r);
		}
		
		auto isEven() const {
			return ((parts[0] ^ overflow) & 0x01) == 0;
		}
		
		auto isOdd() const {
			return ((parts[0] ^ overflow) & 0x01) != 0;
		}
		
		auto zeroCheck() const {
			// Now we check for 0 or p, which would normalize to 0.
			ulong z0 = parts[0];
			ulong z1 = parts[0] ^ (Complement - 1);
			
			z0 |= parts[1];
			z1 &= parts[1];
			z0 |= parts[2];
			z1 &= parts[2];
			z0 |= parts[3];
			z1 &= parts[3];
			
			z0 |= parts[4];
			z1 &= parts[4] ^ 0xF000000000000;
			
			// This doesn't result in a branch.
			return (z0 == 0) || (z1 == 0xFFFFFFFFFFFFF);
		}
	}
	
	static mulImpl(ComputeElement a, ComputeElement b) {
		/**
		 * We limit the multiplication to less that 1024 carries accumulated.
		 * This ensure that the carries fit in 10 bits and the whole numbers
		 * we are multiplying are in fact 266 bits. The end result of the
		 * multiplication is 532 bits.
		 *
		 * As a result, we accumulate up to 16 bits of carries in the last
		 * part of our multiply, and 4 bits mid way in rlow[4] which account
		 * for the extra 20 bits of the multiply.
		 */
		// FIXME: in contract.
		assert(a.carryCount < 1024);
		assert(b.carryCount < 1024);
		
		/**
		 * We will do a full 512 bits multiply, and then reduce.
		 */
		ulong[5] rlow, rhigh;
		
		// Because we limited the carryCount, we know parts aren't
		// larger than 62 bits, so acc can be a ucent.
		ucent acc;
		
		acc += ucent(a.parts[0]) * b.parts[0];
		rlow[0] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[1]) * b.parts[0];
		acc += ucent(a.parts[0]) * b.parts[1];
		rlow[1] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[2]) * b.parts[0];
		acc += ucent(a.parts[1]) * b.parts[1];
		acc += ucent(a.parts[0]) * b.parts[2];
		rlow[2] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[3]) * b.parts[0];
		acc += ucent(a.parts[2]) * b.parts[1];
		acc += ucent(a.parts[1]) * b.parts[2];
		acc += ucent(a.parts[0]) * b.parts[3];
		rlow[3] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[4]) * b.parts[0];
		acc += ucent(a.parts[3]) * b.parts[1];
		acc += ucent(a.parts[2]) * b.parts[2];
		acc += ucent(a.parts[1]) * b.parts[3];
		acc += ucent(a.parts[0]) * b.parts[4];
		rlow[4] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[4]) * b.parts[1];
		acc += ucent(a.parts[3]) * b.parts[2];
		acc += ucent(a.parts[2]) * b.parts[3];
		acc += ucent(a.parts[1]) * b.parts[4];
		rhigh[0] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[4]) * b.parts[2];
		acc += ucent(a.parts[3]) * b.parts[3];
		acc += ucent(a.parts[2]) * b.parts[4];
		rhigh[1] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[4]) * b.parts[3];
		acc += ucent(a.parts[3]) * b.parts[4];
		rhigh[2] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += ucent(a.parts[4]) * b.parts[4];
		rhigh[3] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		rhigh[4] = cast(ulong) acc;
		
		assert((acc >> 64) == 0, "Residual carry detected");
		acc = 0;
		
		/**
		 * Reduce via r = rlow + rhigh * (complement << 4).
		 *
		 * Complement is a 33bits number so r is 293bits.
		 */
		ulong[5] r;
		
		foreach (i; 0 .. 5) {
			acc >>= 52;
			acc += rlow[i];
			// We accumulated 4 extra bits in rlow[4] so the whole
			// rhigh is shifted by 4 bits. We need to shift the
			// complement as well.
			acc += (cast(ucent) rhigh[i]) * (Complement << 4);
			r[i] = cast(ulong) acc & Mask;
		}
		
		// Fixup after the loop to get only 48 bits in the MSB part.
		r[4] = cast(ulong) acc & MsbMask;
		acc >>= 48;
		
		ulong carries = cast(ulong) acc;
		assert((acc >> 64) == 0, "Residual carry detected");
		
		/**
		 * Final reduce round. For that round, we don't need to
		 * fully propagate the carry in order to speeds things up.
		 *
		 * carries is 64 bits and Complement 33 bits. The multiplication
		 * is 97 bits, so we bring less than 52 bits in the next part
		 * which as a result won't produce more than one carry.
		 */
		acc = r[0];
		acc += (cast(ucent) carries) * Complement;
		r[0] = cast(ulong) acc & Mask;
		acc >>= 52;
		r[1] += cast(ulong) acc;
		
		// We are left with at most one carry to propagate forward.
		return r;
	}
	
	static inverseImpl(ComputeElement e) {
		/**
		 * As it turns out, e ^ -1 == e ^ (p - 2) mod p.
		 *
		 * As a first step, we compute various value of e ^ (2 ^ n - 1)
		 *
		 * Then we shift the exponent left by squaring, and add ones using
		 * the precomputed powers using e ^ x * e ^ y = e ^ (x + y).
		 */
		
		// Compute various (2 ^ n - 1) powers of e.
		auto u02 = e.square();
		auto e02 = u02.mul(e);
		auto u05 = e02.mul(u02);
		auto e03 = u05.mul(u02);
		
		auto e06 = e03.squaren!3();
		e06 = e06.mul(e03);
		
		auto e09 = e06.squaren!3();
		e09 = e09.mul(e03);
		
		auto e11 = e09.squaren!2();
		e11 = e11.mul(e02);
		
		auto e22 = e11.squaren!11();
		e22 = e22.mul(e11);
		
		auto e44 = e22.squaren!22();
		e44 = e44.mul(e22);
		
		auto e88 = e44.squaren!44();
		e88 = e88.mul(e44);
		
		auto e176 = e88.squaren!88();
		e176 = e176.mul(e88);
		
		auto e220 = e176.squaren!44();
		e220 = e220.mul(e44);
		
		auto e223 = e220.squaren!3();
		e223 = e223.mul(e03);
		
		// The 223 heading ones of the base.
		// 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE
		// 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFEFFFFFC2D
		auto r = e223;
		
		// Now we got a 0 and 0xFFFFFC2D
		r = r.squaren!23();
		r = r.mul(e22);
		
		// 0000101
		r = r.squaren!7();
		r = r.mul(u05);
		
		// 101
		r = r.squaren!3();
		r = r.mul(u05);
		
		return r;
	}
	
	static sqrtImpl(ComputeElement e) {
		/**
		 * Because p = 3 mod 4, we know Skank's algorithm simplify
		 * to sqrt(e) = e ^ ((p + 1)/4), if it exists at all.
		 *
		 * Because (p + 1)/4 is even, the end result will be the same
		 * for e and -e . To guard against this, we verify at teh end
		 * that r ^ 2 == e so we indeed have a valid square root.
		 */
		
		// Compute various (2 ^ n - 1) powers of e.
		auto e02 = e.mul(e.square());
		auto u06 = e02.square();
		auto e03 = u06.mul(e);
		
		auto e06 = e03.squaren!3();
		e06 = e06.mul(e03);
		
		auto e09 = e06.squaren!3();
		e09 = e09.mul(e03);
		
		auto e11 = e09.squaren!2();
		e11 = e11.mul(e02);
		
		auto e22 = e11.squaren!11();
		e22 = e22.mul(e11);
		
		auto e44 = e22.squaren!22();
		e44 = e44.mul(e22);
		
		auto e88 = e44.squaren!44();
		e88 = e88.mul(e44);
		
		auto e176 = e88.squaren!88();
		e176 = e176.mul(e88);
		
		auto e220 = e176.squaren!44();
		e220 = e220.mul(e44);
		
		auto e223 = e220.squaren!3();
		e223 = e223.mul(e03);
		
		// The 223 heading ones of the base.
		// 0x7FFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE
		// 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFBFFFFF0C
		auto r = e223;
		
		// Now we got 0xBFFFFF0C with the first 1 taken care of.
		r = r.squaren!23();
		r = r.mul(e22);
		
		// 000011
		r = r.squaren!6();
		r = r.mul(e02);
		
		// 00
		r = r.squaren!2();
		
		// Not all number have a square root. We check if we actually computed
		// the square root by squaring it and chcking against e. If not, throw.
		if (!e.opEquals(r.square())) {
			throw new Exception(/* "e has no square root" */);
		}
		
		return r;
	}
}

void testComputeElement() {
	static testAdd(ComputeElement a, ComputeElement b, ComputeElement r) {
		assert(r.opEquals(a.add(b)), "a + b == r");
		assert(r.opEquals(b.add(a)), "b + a == r");
	}
	
	static testNeg(ComputeElement n, ComputeElement negn) {
		assert(n.opEquals(negn.negate()), "n = -negn");
		assert(negn.opEquals(n.negate()), "-n = negn");
	}
	
	static testMul(ComputeElement a, ComputeElement b, ComputeElement r) {
		assert(r.opEquals(a.mul(b)), "a * b = r");
		assert(r.opEquals(b.mul(a)), "b * a = r");
	}
	
	auto zero = ComputeElement(0);
	
	testAdd(zero, zero, zero);
	testNeg(zero, zero);
	testMul(zero, zero, zero);
	
	assert(zero.opEquals(zero.square()), "0^2 == 0");
	assert(zero.isEven(), "0 is even");
	
	auto one = ComputeElement(1);
	testAdd(zero, one, one);
	testMul(zero, one, zero);
	testMul(one, one, one);
	
	assert(one.opEquals(one.square()), "1^2 == 1");
	assert(one.isOdd(), "1 is odd");
	
	auto two = ComputeElement(2);
	testAdd(one, one, two);
	testAdd(zero, two, two);
	testMul(zero, two, zero);
	testMul(one, two, two);
	
	auto four = ComputeElement(4);
	assert(four.opEquals(two.square()), "2^2 == 4");
	assert(two.isEven(), "2 is even");
	assert(four.isEven(), "4 is even");
	
	auto negone = ComputeElement(Element(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFEFFFFFC2E,
	));
	
	testAdd(one, negone, zero);
	testNeg(one, negone);
	testMul(one, negone, negone);
	testMul(negone, negone, one);
	
	assert(one.opEquals(negone.square()), "(-1)^2 == 1");
	assert(negone.isEven(), "-1 is even");
	
	auto negtwo = ComputeElement(Element(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFEFFFFFC2D,
	));
	
	testAdd(one, negtwo, negone);
	testAdd(negone, negone, negtwo);
	testNeg(two, negtwo);
	testMul(negone, two, negtwo);
	testMul(negone, negtwo, two);
	assert(negtwo.isOdd(), "-2 is odd");
	
	auto p = ComputeElement.prime();
	
	testAdd(p, zero, zero);
	testAdd(p, p, zero);
	testAdd(p, one, one);
	testAdd(p, negone, negone);
	testNeg(p, zero);
	testMul(p, p, zero);
	testMul(p, one, zero);
	testMul(p, negone, zero);
	
	// Test high carry count.
	static getNegOneWithNCarries(uint cc) {
		auto one = ComputeElement(1);
		auto negone = one.negate();
		assert(negone.carryCount == 1);
		
		auto r = negone;
		foreach (i; 0 .. 5) {
			r.parts[i] *= (cc + 1);
		}
		
		// So that we get -1 with as many carries as requested.
		r.parts[0] += cc;
		r.carryCount = cc;
		
		assert(negone.opEquals(r));
		assert(r.isEven(), "-1 is even");
		
		return r;
	}
	
	auto enegone = negone.normalize();
	
	foreach (i; 0 .. 1024) {
		auto n = getNegOneWithNCarries(i);
		auto m = ComputeElement.mulImpl(n, n);
		assert(one.opEquals(ComputeElement(m, 1)));
		
		// Test carry propagationg via normalization
		assert(enegone.opEquals(n.normalize()), "normalize(n) == -1");
	}
	
	// Squaring.
	auto n = ComputeElement(Element(
		0x7aff790c9a22b99c,
		0x94856ed9231e3fe9,
		0x188b5dd4e6107cc4,
		0x9982b148178f639f,
	));
	
	auto en2 = Element(
		0x251763d423a01613,
		0x32ec3fd6bb58cb93,
		0x7dae8f98ab71d214,
		0xdb3a36e3d3625992,
	);
	
	auto n2 = ComputeElement(en2);
	
	auto negn = n.negate();
	testAdd(n, negn, zero);
	testNeg(n, negn);
	testMul(n, negone, negn);
	
	auto nsqr = n.square();
	assert(nsqr.opEquals(n2), "n^2 == n2");
	
	assert(n.isOdd(), "n is odd");
	assert(negn.isEven(), "-n is even");
	assert(n2.isEven(), "n^2 is even");
	
	auto sqrt2 = ComputeElement(Element(
		0x210c790573632359,
		0xb1edb4302c117d8a,
		0x132654692c3feeb7,
		0xde3a86ac3f3b53f7,
	));
	
	assert(two.opEquals(sqrt2.square()), "sqrt(2)^2 == 2");
	
	auto qdrt2 = ComputeElement(Element(
		0xf7a0537b4e1a702a,
		0x365917f8acd566b4,
		0x910693c40349c795,
		0x63296cb3c055f559,
	));
	
	assert(sqrt2.opEquals(qdrt2.square()), "qdrt(2)^2 == sqrt(2)");
	assert(two.opEquals(qdrt2.squaren!2()), "qdrt(2)^2^2 == 2");
	
	assert(sqrt2.isOdd(), "sqrt2 is odd");
	assert(qdrt2.isOdd(), "qdrt2 is odd");
	
	// Normalization.
	assert(en2.opEquals(nsqr.normalize()));
	
	auto np = p.normalize();
	auto nzero = zero.normalize();
	assert(np.opEquals(nzero), "P normalize to 0");
	
	// Inversion.
	testMul(one, one.inverse(), one);
	testMul(negone, negone.inverse(), one);
	testMul(two, two.inverse(), one);
	testMul(negtwo, negtwo.inverse(), one);
	testMul(four, four.inverse(), one);
	testMul(n, n.inverse(), one);
	testMul(negn, negn.inverse(), one);
	testMul(n2, n2.inverse(), one);
	
	// Square root.
	assert(zero.opEquals(zero.sqrt()), "sqrt(0) == 0");
	assert(one.opEquals(one.sqrt()), "sqrt(1) == 1");
	assert(two.opEquals(four.sqrt()), "sqrt(4) == 2");
	assert(sqrt2.opEquals(two.sqrt()), "sqrt(2) == sqrt2");
	assert(qdrt2.opEquals(sqrt2.sqrt()), "sqrt(sqrt2) == qdrt2");
	
	// n ^ 2 == -n ^ 2, so we also get -n in some cases.
	assert(negn.opEquals(n2.sqrt()), "sqrt(n^2) == -n");
	
	// Some elements do not have a square root.
	try {
		n.sqrt();
		assert(0, "n has no square root");
	} catch (Exception e) { }
	
	// Beta
	auto beta = ComputeElement(Beta);
	auto beta2 = beta.square();
	auto beta3 = beta2.mul(beta);
	auto beta4 = beta2.square();
	auto beta6 = beta4.mul(beta2);
	
	assert(one.opEquals(beta3), "beta^3 == 1");
	assert(one.opEquals(beta6), "beta2^3 == 1");
}

unittest {
	testElement();
	testComputeElement();
	
	import core.stdc.stdio;
	printf("OK\n".ptr);
}

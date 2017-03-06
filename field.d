module crypto.field;

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
	
	auto opEquals(Element b) const {
		ulong neq;
		foreach (i; 0 .. 4) {
			neq |= parts[i] ^ b.parts[i];
		}
		
		return neq == 0;
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
	
public:
	this(Element e) {
		parts[0] = e.parts[0] & Mask;
		parts[1] = (e.parts[0] >> 52 | e.parts[1] << 12) & Mask;
		parts[2] = (e.parts[1] >> 40 | e.parts[2] << 24) & Mask;
		parts[3] = (e.parts[2] >> 28 | e.parts[3] << 36) & Mask;
		parts[4] = e.parts[3] >> 16;
	}
	
	this(ulong[5] parts, uint carryCount) {
		this.parts = parts;
		this.carryCount = carryCount;
	}
	
	this(ulong s) {
		this(Element(0, 0, 0, s));
	}
	
	auto propagateCarries() const {
		// We start by reducing all the MSB bits in part[4]
		// so that we will at most have one carry to reduce.
		ulong[5] r = parts;
		ulong acc = (r[4] >> 48) * Complement;
		
		// Clear the carries in part[4].
		r[4] &= MsbMask;
		
		// Propagate.
		foreach (i; 0 .. 5) {
			acc += r[i];
			r[i] = acc & Mask;
			acc >>= 52;
		}
		
		return ComputeElement(r, 1);
	}
	
	auto propagateAndZeroCheck() {
		this = propagateCarries();
		
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
		auto e = propagateCarries();
		
		// Check if there is an overflow.
		auto msbAllOnes = e.parts[4] == MsbMask;
		msbAllOnes &= (e.parts[1] & e.parts[2] & e.parts[3]) == Mask;
		auto tooGreat = msbAllOnes & (e.parts[0] >= 0xFFFFFFFEFFFFFC2F);
		auto overflow = (e.parts[4] >> 48) | tooGreat;
		
		ulong[4] r;
		ucent acc = -ulong(overflow) & Complement;
		acc += parts[0];
		acc += (cast(ucent) e.parts[1]) << 52;
		r[0] = cast(ulong) acc;
		acc >>= 64;
		acc += (cast(ucent) e.parts[2]) << 40;
		r[1] = cast(ulong) acc;
		acc >>= 64;
		acc += (cast(ucent) e.parts[3]) << 28;
		r[2] = cast(ulong) acc;
		acc >>= 64;
		acc += cast(ucent) (e.parts[4] << 16);
		r[3] = cast(ulong) acc;
		assert(acc >> 64 == 0, "Residual carry detected");
		
		return Element(r);
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
		if (cc >= 2048) {
			// We have 12bits to accumulate carries.
			// It means we can't add numbers which accumulated
			// 2048 carries or more.
			r = r.propagateCarries();
		}
		
		return r;
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		auto cc = carryCount + 1;
		
		ulong[5] r;
		r[0] = 0xFFFFEFFFFFC2F * cc - parts[0];
		r[1] = 0xFFFFFFFFFFFFF * cc - parts[1];
		r[2] = 0xFFFFFFFFFFFFF * cc - parts[2];
		r[3] = 0xFFFFFFFFFFFFF * cc - parts[3];
		r[4] = 0x0FFFFFFFFFFFF * cc - parts[4];
		
		return ComputeElement(r, cc);
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
			a = a.propagateCarries();
		}
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (b.carryCount >= 1024) {
			b = b.propagateCarries();
		}
		
		return ComputeElement(mulImpl(a, b), 1);
	}
	
	auto square() const {
		auto e = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (e.carryCount >= 1024) {
			e = e.propagateCarries();
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
		return diff.propagateAndZeroCheck();
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
			r = r.propagateCarries();
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
		
		acc += (cast(ucent) a.parts[0]) * b.parts[0];
		rlow[0] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[1]) * b.parts[0];
		acc += (cast(ucent) a.parts[0]) * b.parts[1];
		rlow[1] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[2]) * b.parts[0];
		acc += (cast(ucent) a.parts[1]) * b.parts[1];
		acc += (cast(ucent) a.parts[0]) * b.parts[2];
		rlow[2] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[3]) * b.parts[0];
		acc += (cast(ucent) a.parts[2]) * b.parts[1];
		acc += (cast(ucent) a.parts[1]) * b.parts[2];
		acc += (cast(ucent) a.parts[0]) * b.parts[3];
		rlow[3] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[4]) * b.parts[0];
		acc += (cast(ucent) a.parts[3]) * b.parts[1];
		acc += (cast(ucent) a.parts[2]) * b.parts[2];
		acc += (cast(ucent) a.parts[1]) * b.parts[3];
		acc += (cast(ucent) a.parts[0]) * b.parts[4];
		rlow[4] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[4]) * b.parts[1];
		acc += (cast(ucent) a.parts[3]) * b.parts[2];
		acc += (cast(ucent) a.parts[2]) * b.parts[3];
		acc += (cast(ucent) a.parts[1]) * b.parts[4];
		rhigh[0] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[4]) * b.parts[2];
		acc += (cast(ucent) a.parts[3]) * b.parts[3];
		acc += (cast(ucent) a.parts[2]) * b.parts[4];
		rhigh[1] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[4]) * b.parts[3];
		acc += (cast(ucent) a.parts[3]) * b.parts[4];
		rhigh[2] = cast(ulong) acc & Mask;
		acc >>= 52;
		
		acc += (cast(ucent) a.parts[4]) * b.parts[4];
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
		auto e02 = e.mul(e.square());
		auto e03 = e.mul(e02.square());
		
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
		// 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFEFFFFFC2F
		auto r = e223;
		
		// Now we got a 0 and 0xFFFFFC2D
		r = r.squaren!23();
		r = r.mul(e22);
		
		// XXX: Computing e ^ 0b101 and would save some mul here,
		// 00001
		r = r.squaren!5();
		r = r.mul(e);
		
		// 011
		r = r.squaren!3();
		r = r.mul(e02);
		
		// 01
		r = r.squaren!2();
		r = r.mul(e);
		
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
		auto e03 = e.mul(e02.square());
		
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

void main() {
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
	
	auto one = ComputeElement(1);
	testAdd(zero, one, one);
	testMul(zero, one, zero);
	testMul(one, one, one);
	
	assert(one.opEquals(one.square()), "1^2 == 1");
	
	auto two = ComputeElement(2);
	testAdd(one, one, two);
	testAdd(zero, two, two);
	testMul(zero, two, zero);
	testMul(one, two, two);
	
	auto four = ComputeElement(4);
	assert(four.opEquals(two.square()), "2^2 == 4");
	
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
		return r;
	}
	
	foreach (i; 0 .. 1024) {
		auto n = getNegOneWithNCarries(i);
		auto m = ComputeElement.mulImpl(n, n);
		assert(one.opEquals(ComputeElement(m, 1)));
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
	
	// Normalization.
	assert(en2.opEquals(nsqr.normalize()));
	
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
	
	printf("OK\n".ptr);
}

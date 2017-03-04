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
		parts[2] = (e.parts[1] >> 40 | e.parts[1] << 24) & Mask;
		parts[3] = (e.parts[2] >> 28 | e.parts[1] << 36) & Mask;
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
		ulong acc = (parts[4] >> 48) * Complement;
		
		ulong[5] r;
		foreach (i; 0 .. 5) {
			acc += parts[i];
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
		auto msbAllOnes = e.parts[4] == ((1UL << 48) - 1);
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
		acc >>= 64;
		
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
		r[4] = 0xFFFFFFFFFFFFF * cc - parts[4];
		
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
		if (a.carryCount >= 32) {
			a = a.propagateCarries();
		}
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (b.carryCount >= 32) {
			b = b.propagateCarries();
		}
		
		return ComputeElement(mulImpl(a, b), 1);
	}
	
	auto square() const {
		auto e = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (e.carryCount >= 32) {
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
	
	auto inverse() const {
		return inverseImpl(this);
	}
	
	// FIXME: For some reason, auto is detected as const by SDC.
	// This needs to be figured out.
	ComputeElement muln(uint N)() const {
		static assert(N <= 2048, "");
		
		ComputeElement r = this;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (r.carryCount * N > 2048) {
			r = r.propagateCarries();
		}
		
		foreach (i; 0 .. 5) {
			r.parts[i] *= N;
		}
		
		r.carryCount *= N;
		return r;
	}
	
private:
	static mulImpl(ComputeElement a, ComputeElement b) {
		// FIXME: in contract.
		assert(a.carryCount < 32);
		assert(b.carryCount < 32);
		
		/**
		 * We will do a full 512 bits multiply, and then reduce.
		 */
		ulong[5] rlow, rhigh;
		
		// Because we limited the carryCount, we know partsq aren't
		// larger than 56bits, so acc can be a ucent.
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
		acc = 0;
		
		/**
		 * Reduce via r = rlow + rhigh * complement.
		 *
		 * Complement is a 33bits number so r is 289bits.
		 */
		ulong[5] r;
		
		foreach (i; 0 .. 5) {
			acc += rlow[i];
			acc += (cast(ucent) rhigh[i]) * Complement;
			r[i] = cast(ulong) acc & Mask;
			acc >>= 52;
		}
		
		ulong carries = cast(ulong) acc;
		
		/**
		 * Final reduce round. For that round, we don't need to
		 * fully propagate the carry in order to speeds things up.
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
		r.squaren!23();
		r.mul(e22);
		
		// XXX: Computing e ^ 0b101 and would save some mul here,
		// 00001
		r.squaren!5();
		r.mul(e);
		
		// 011
		r.squaren!3();
		r.mul(e02);
		
		// 01
		r.squaren!2();
		r.mul(e);
		
		return r;
	}
}

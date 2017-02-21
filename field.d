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
	bool normalized = true;
	
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
	
	this(ulong[5] parts, uint carryCount, bool normalized) {
		this.parts = parts;
		this.carryCount = carryCount;
		this.normalized = normalized;
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
		
		return ComputeElement(r, 1, normalized);
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
		return addImpl(this, b);
	}
	
	// auto opBinary(string op : "*")(Scalar b) const {
	auto mul(ComputeElement b) const {
		return mulImpl(this, b);
	}
	
private:
	static addImpl(ComputeElement a, ComputeElement b) {
		ComputeElement r;
		
		foreach (i; 0 .. 5) {
			r.parts[i] = a.parts[i] + b.parts[i];
		}
		
		r.carryCount = a.carryCount + b.carryCount + 1;
		r.normalized = false;
		
		// We can branch on carryCount because it is only dependent on
		// control flow. If other part of the code do not branch based
		// on values, then carryCount do not depend on value.
		if (r.carryCount >= 2048) {
			// We have 12bits to accumulate carries.
			// It means we can't add numbers which accumulated
			// 2048 carries or more.
			r = r.propagateCarries();
		}
		
		return r;
	}
	
	static mulImpl(ComputeElement a, ComputeElement b) {
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
		return ComputeElement(r, 1, false);
	}
}

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
	
	uint carryCount = 0;
	uint normalized = 1;
	
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
	
	auto normalize() {
		ulong[4] r;
		
		// We start by reducing all the MSB bits in part[4]
		// so that we will at most have one carry to reduce.
		ucent acc = (parts[4] >> 48) * Complement;
		
		// This must be unrolled, or the compiler
		// figures out it is a noop when mask is 0.
		acc += parts[0];
		acc += (cast(ucent) parts[1]) << 52;
		r[0] = cast(ulong) acc;
		acc >>= 64;
		acc += (cast(ucent) parts[2]) << 40;
		r[1] = cast(ulong) acc;
		acc >>= 64;
		acc += (cast(ucent) parts[3]) << 28;
		r[2] = cast(ulong) acc;
		acc >>= 64;
		acc += cast(ucent) (parts[4] << 16);
		r[3] = cast(ulong) acc;
		acc >>= 64;
		
		// Check if there is an overflow.
		auto msbAllOnes = (r[1] & r[2] & r[3]) == ulong.max;
		auto overflow = (cast(ulong) acc & 0x01) | (msbAllOnes & (r[0] >= 0xFFFFFFFEFFFFFC2F));
		
		// Final reduction.
		acc = -ulong(overflow) & Complement;
		acc += r[0];
		r[0] = cast(ulong) acc;
		acc >>= 64;
		acc += r[1];
		r[1] = cast(ulong) acc;
		acc >>= 64;
		acc += r[2];
		r[2] = cast(ulong) acc;
		acc >>= 64;
		acc += r[3];
		r[3] = cast(ulong) acc;
		
		return Element(r);
	}
}

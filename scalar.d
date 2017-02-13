module crypto.scalar;

struct Scalar {
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
		auto a = base();
		auto b = bitflip();
		
		auto mask = ulong(this.opEquals(Scalar(0)) - 1);
		
		ulong[4] r;
		ucent acc = 1;
		
		// This must be unrolled, or the compiler
		// figures out it is a noop when mask is 0.
		// FIXME: Rhe compiler is still a smart ass and use CMOV.
		acc += a.parts[0];
		acc += b.parts[0];
		r[0] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += a.parts[1];
		acc += b.parts[1];
		r[1] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += a.parts[2];
		acc += b.parts[2];
		r[2] = (cast(ulong) acc) & mask;
		acc >>= 64;
		acc += a.parts[3];
		acc += b.parts[3];
		r[3] = (cast(ulong) acc) & mask;
		
		return Scalar(r);
	}
	
	// auto opBinary(string op : "+")(Scalar b) const {
	auto add(Scalar b) const {
		auto r = addImpl(this, b);
		return r.reduce();
	}
	
	auto opEquals(Scalar b) const {
		auto eq = 1;
		foreach (i; 0 .. 4) {
			eq &= (parts[i] == b.parts[i]);
		}
		
		return !!eq;
	}
	
	auto opCmp(Scalar b) const {
		int bigger;
		int smaller;
		foreach_reverse (i; 0 .. 4) {
			// The higher ILP version require a few extra instructions.
			// TODO: Need to benchmark which one is best.
			enum withILP = false;
			static if (withILP) {
				auto isBigger  = (parts[i] > b.parts[i]) & ~smaller;
				auto isSmaller = (parts[i] < b.parts[i]) & ~bigger;
				
				bigger  = isBigger;
				smaller = isSmaller;
			} else {
				bigger  = (parts[i] > b.parts[i]) & ~smaller;
				smaller = (parts[i] < b.parts[i]) & ~bigger;
			}
		}
		
		return bigger - smaller;
	}
	
private:
	static Scalar base() {
		/**
		 * secp256k1's order.
		 *
		 * The number of point on the curve that can be reached
		 * by multiplying G by a scalar. All scalar arithmetic
		 * is done modulo the order.
		 */
		return Scalar(
			0xFFFFFFFFFFFFFFFF,
			0xFFFFFFFFFFFFFFFE,
			0xBAAEDCE6AF48A03B,
			0xBFD25E8CD0364141,
		);
	}
	
	auto bitflip() const {
		return Scalar(~parts[3], ~parts[2], ~parts[1], ~parts[0]);
	}
	
	auto complement() const {
		return addImpl(bitflip(), Scalar(1)).result;
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
		
		return AddResult(Scalar(r), !!(acc & 0x01));
	}
	
	struct AddResult {
		Scalar result;
		bool carry;
		
		this(Scalar r, bool c) {
			result = r;
			carry = c;
		}
		
		auto needReduce() const {
			return (result.opCmp(base()) < 0) | carry;
		}
		
		auto reduce() const {
			auto b = base();
			b = b.complement();
			
			auto mask = -ulong(needReduce());
			
			ulong[4] r;
			ucent acc;
			
			// This must be unrolled, or the compiler
			// figures out it is a noop when mask is 0.
			acc += result.parts[0];
			acc += b.parts[0] & mask;
			r[0] = cast(ulong) acc;
			acc >>= 64;
			acc += result.parts[1];
			acc += b.parts[1] & mask;
			r[1] = cast(ulong) acc;
			acc >>= 64;
			acc += result.parts[2];
			acc += b.parts[2] & mask;
			r[2] = cast(ulong) acc;
			acc >>= 64;
			acc += result.parts[3];
			acc += b.parts[3] & mask;
			r[3] = cast(ulong) acc;
			
			return Scalar(r);
		}
	}
	
	static mulImpl(Scalar a, Scalar b) {
		Scalar low, high;
		Accumulator acc;
		
		// Just the plain old scholl multiplication.
		acc.muladd(a.parts[0], b.parts[0]);
		low.parts[0] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[1]);
		acc.muladd(a.parts[1], b.parts[0]);
		low.parts[1] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[2]);
		acc.muladd(a.parts[1], b.parts[1]);
		acc.muladd(a.parts[2], b.parts[0]);
		low.parts[2] = acc.extract();
		
		acc.muladd(a.parts[0], b.parts[3]);
		acc.muladd(a.parts[1], b.parts[2]);
		acc.muladd(a.parts[2], b.parts[1]);
		acc.muladd(a.parts[3], b.parts[0]);
		low.parts[3] = acc.extract();
		
		acc.muladd(a.parts[1], b.parts[3]);
		acc.muladd(a.parts[2], b.parts[2]);
		acc.muladd(a.parts[3], b.parts[1]);
		high.parts[0] = acc.extract();
		
		acc.muladd(a.parts[2], b.parts[3]);
		acc.muladd(a.parts[3], b.parts[2]);
		high.parts[1] = acc.extract();
		
		acc.muladd(a.parts[3], b.parts[3]);
		high.parts[2] = acc.extract();
		
		high.parts[3] = acc.extract();
		
		return MulResult(high, low);
	}
	
	struct Accumulator {
		ulong c0;
		ulong c1;
		uint c2;
		
		auto muladd(ulong a, ulong b) {
			ucent acc = a;
			acc *= b;
			
			// a*b + c cannot exceed 128 bits
			// if a, b and c are 64 bits.
			acc += c0;
			c0 = cast(ulong) (acc & ulong.max);
			acc >>= 64;
			
			acc += c1;
			c1 = cast(ulong) (acc & ulong.max);
			acc >>= 64;
			
			acc += c2;
			c2 = cast(uint) (acc & uint.max);
			acc >>= 32;
			
			// assert(acc == 0, "Overflow");
		}
		
		auto extract() {
			auto r = c0;
			c0 = c1;
			c1 = c2;
			c2 = 0;
			return r;
		}
	}
	
	struct MulResult {
		Scalar low;
		Scalar high;
		
		this(Scalar h, Scalar l) {
			low = l;
			high = h;
		}
		
		auto reduce() const {
			auto b = base();
			auto c = b.complement();
			
			// Do the thing...
			
			auto r = AddResult(low, !!(high.parts[0] & 0x01));
			return r.reduce();
		}
	}
}

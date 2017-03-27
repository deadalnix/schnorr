module crypto.uint256;

struct Uint256 {
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
	
	auto getParts() const {
		return parts;
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		ulong[4] r;
		ucent acc = 1;
		
		foreach (i; 0 .. 4) {
			acc += ~parts[i];
			r[i] = cast(ulong) acc;
			acc >>= 64;
		}
		
		return Uint256(r);
	}
	
	// auto opUnary(string op : "~")() const {
	auto bitflip() const {
		return Uint256(
			~parts[3],
			~parts[2],
			~parts[1],
			~parts[0],
		);
	}
	
	// auto opBinary(string op : "+")(Uint256 b) const {
	auto add(Uint256 b) const {
		ulong[4] r;
		ucent acc;
		
		foreach (i; 0 .. 4) {
			acc += parts[i];
			acc += b.parts[i];
			r[i] = cast(ulong) acc;
			acc >>= 64;
		}
		
		return Uint256(r);
	}
	
	// auto opBinary(string op : "+")(Uint256 b) const {
	auto sub(Uint256 b) const {
		ulong[4] r;
		ucent acc = 1;
		
		foreach (i; 0 .. 4) {
			acc += parts[i];
			acc += ~b.parts[i];
			r[i] = cast(ulong) acc;
			acc >>= 64;
		}
		
		return Uint256(r);
	}
	
	auto opEquals(Uint256 b) const {
		ulong neq;
		foreach (i; 0 .. 4) {
			neq |= (parts[i] ^ b.parts[i]);
		}
		
		return !neq;
	}
	
	auto opCmp(Uint256 b) const {
		auto bp = b.getParts();
		
		int bigger;
		int smaller;
		foreach_reverse (i; 0 .. 4) {
			// The higher ILP version require a few extra instructions.
			// TODO: Need to benchmark which one is best.
			enum WithILP = false;
			static if (WithILP) {
				auto isBigger  = (parts[i] > bp[i]) & ~smaller;
				auto isSmaller = (parts[i] < bp[i]) & ~bigger;
				
				bigger  |= isBigger;
				smaller |= isSmaller;
			} else {
				bigger  |= (parts[i] > bp[i]) & ~smaller;
				smaller |= (parts[i] < bp[i]) & ~bigger;
			}
		}
		
		return bigger - smaller;
	}
	
	auto serialize() const {
		ubyte[32] s;
		
		auto sl = (cast(ulong*) s.ptr)[0 .. 4];
		foreach (i; 0 .. 4) {
			import sdc.intrinsics;
			sl[i] = bswap(parts[3 - i]);
		}
		
		return s;
	}
	
	static unserialize(ref const(ubyte)[] buffer) {
		if (buffer.length < 32) {
			throw new Exception();
		}
		
		scope(success) buffer = buffer[32 .. buffer.length];
		auto b = cast(ulong*) buffer.ptr;
		
		ulong[4] r;
		foreach (i; 0 .. 4) {
			import sdc.intrinsics;
			r[3 - i] = bswap(b[i]);
		}
		
		return Uint256(r);
	}
	
	static unserializeInRange(ref const(ubyte)[] buffer, Uint256 max) {
		auto i = unserialize(buffer);
		
		// If i is greater than the max, we throw.
		if (i.opCmp(max) >= 0) {
			// out of range.
			throw new Exception();
		}
		
		return i;
	}
	
	static unserializeInRangeOrZero(ref const(ubyte)[] buffer, Uint256 max) {
		auto i = unserialize(buffer);
		
		// If i is greater than the max, we return 0.
		return Uint256.select(i.opCmp(max) >= 0, Uint256(0), i);
	}
	
	static select(bool cond, Uint256 a, Uint256 b) {
		auto maska = -ulong(cond);
		auto maskb = ~maska;
		
		ulong[4] r;
		foreach (i; 0 .. 4) {
			// FIXME: The compiler is still a smart ass and uses CMOV.
			r[i] = (a.parts[i] & maska) | (b.parts[i] & maskb);
		}
		
		return Uint256(r);
	}
}

void main() {
	static testAdd(Uint256 a, Uint256 b, Uint256 r) {
		assert(r.opEquals(a.add(b)), "a + b == r");
		assert(r.opEquals(b.add(a)), "b + a == r");
	}
	
	static testNeg(Uint256 n, Uint256 negn) {
		assert(n.opEquals(negn.negate()), "n = -negn");
		assert(negn.opEquals(n.negate()), "-n = negn");
	}
	
	auto zero = Uint256(0);
	testAdd(zero, zero, zero);
	testNeg(zero, zero);
	
	auto one = Uint256(1);
	testAdd(zero, one, one);
	
	auto two = Uint256(2);
	testAdd(one, one, two);
	testAdd(zero, two, two);
	
	auto negone = Uint256(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
	);
	
	testAdd(one, negone, zero);
	testNeg(one, negone);
	
	auto negtwo = Uint256(
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFF,
		0xFFFFFFFFFFFFFFFE,
	);
	
	testAdd(one, negtwo, negone);
	testAdd(negone, negone, negtwo);
	testNeg(two, negtwo);
	
	// Serialization
	static testSerialization(Uint256 a) {
		auto buf = a.serialize();
		auto bufSlice = buf.ptr[0 .. buf.length];
		
		auto b = Uint256.unserialize(bufSlice);
		assert(a.opEquals(b), "serialization failed");
		
		auto zero = Uint256(0);
		auto one = Uint256(1);
		
		auto amax = a.add(one);
		if (!amax.opEquals(zero)) {
			bufSlice = buf.ptr[0 .. buf.length];
			b = Uint256.unserializeInRangeOrZero(bufSlice, amax);
			assert(a.opEquals(b), "serialization failed");
			
			bufSlice = buf.ptr[0 .. buf.length];
			b = Uint256.unserializeInRange(bufSlice, amax);
			assert(a.opEquals(b), "serialization failed");
		}
		
		bufSlice = buf.ptr[0 .. buf.length];
		auto c = Uint256.unserializeInRangeOrZero(bufSlice, a);
		assert(c.opEquals(zero), "Out of range did not triggered");
		
		try {
			bufSlice = buf.ptr[0 .. buf.length];
			auto d = Uint256.unserializeInRange(bufSlice, a);
			assert(0, "Out of range did not throw");
		} catch(Exception e) {}
	}
	
	testSerialization(zero);
	testSerialization(one);
	testSerialization(two);
	testSerialization(negone);
	testSerialization(negtwo);
	
	auto lambda = Uint256(
		0x5363ad4cc05c30e0,
		0xa5261c028812645a,
		0x122e22ea20816678,
		0xdf02967c1b23bd72,
	);
	
	testSerialization(lambda);
	
	// Invalid serialization.
	static testSerializationFail(ubyte[] buf) {
		try {
			Uint256.unserialize(buf);
			assert(0, "unserialize should have thrown");
		} catch(Exception e) {}
		
		auto max = Uint256(999);
		try {
			Uint256.unserializeInRange(buf, max);
			assert(0, "unserialize should have thrown");
		} catch(Exception e) {}
		
		try {
			Uint256.unserializeInRangeOrZero(buf, max);
			assert(0, "unserialize should have thrown");
		} catch(Exception e) {}
	}
	
	ubyte[33] buf;
	testSerializationFail(buf.ptr[0 .. 0]);
	testSerializationFail(buf.ptr[0 .. 31]);
	
	// Buffer advanced properly.
	auto bufSlice = buf.ptr[0 .. 33];
	Uint256.unserialize(bufSlice);
	assert(
		bufSlice.length == 1 && bufSlice.ptr is &buf[32],
		"buffer did not advance as expected",
	);
	
	printf("OK\n".ptr);
}

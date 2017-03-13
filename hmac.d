module crypto.hmac;

struct HMAC(H) {
private:
	H inner, outer;
	
	alias R = typeof(H.init.finish());
	enum B = H.BlockSize;
	
public:
	this(ubyte[] key) {
		// If the key is too long, we need to hash it.
		R hkey;
		
		if (key.length > B) {
			H keyhasher;
			keyhasher.start();
			keyhasher.put(key);
			hkey = keyhasher.finish();
			key = hkey.ptr[0 .. hkey.length];
		}
		
		ubyte[B] K;
		memset(K.ptr, 0x36, B);
		
		foreach (i; 0 .. key.length) {
			K[i] ^= key[i];
		}
		
		inner.start();
		inner.put(K.ptr[0 .. B]);
		
		foreach (i; 0 .. B) {
			K[i] ^= 0x36 ^ 0x5C;
		}
		
		outer.start();
		outer.put(K.ptr[0 .. B]);
	}
	
	void put(const(ubyte)[] input) {
		inner.put(input);
	}
	
	auto finish() {
		auto ihash = inner.finish();
		outer.put(ihash.ptr[0 .. ihash.length]);
		return outer.finish();
	}
}

void main() {
	static H(uint a, uint b, uint c, uint d, uint e, uint f, uint g, uint h) {
		ubyte[32] hash;
		auto ptr = cast(uint*) hash.ptr;
		
		import sdc.intrinsics;
		ptr[0] = bswap(a);
		ptr[1] = bswap(b);
		ptr[2] = bswap(c);
		ptr[3] = bswap(d);
		ptr[4] = bswap(e);
		ptr[5] = bswap(f);
		ptr[6] = bswap(g);
		ptr[7] = bswap(h);
		
		return hash;
	}
	
	static buf(string str) {
		return (cast(const(ubyte)*) str.ptr)[0 .. str.length];
	}
	
	static test(ubyte[] key, string message, ubyte[32] expected) {
		import crypto.sha256;
		auto hasher = HMAC!SHA256(key);
		hasher.put(buf(message));
		auto h = hasher.finish();
		
		foreach (i; 0 .. 32) {
			assert(h[i] == expected[i]);
		}
	}
	
	// Test vectors from rfc4231
	ubyte[131] key;
	foreach (i; 0 .. 20) {
		key[i] = 0x0b;
	}
	
	auto h = H(
		0xb0344c61, 0xd8db3853, 0x5ca8afce, 0xaf0bf12b,
		0x881dc200, 0xc9833da7, 0x26e9376c, 0x2e32cff7,
	);
	
	test(key.ptr[0 .. 20], "Hi There", h);
	
	h = H(
		0x5bdcc146, 0xbf60754e, 0x6a042426, 0x089575c7,
		0x5a003f08, 0x9d273983, 0x9dec58b9, 0x64ec3843,
	);
	
	test(buf("Jefe"), "what do ya want for nothing?", h);
	
	foreach (i; 0 .. 20) {
		key[i] = 0xaa;
	}
	
	ubyte[50] data;
	string dataStr = (cast(immutable(char)*) data.ptr)[0 .. 50];
	
	foreach (i; 0 .. 50) {
		data[i] = 0xdd;
	}
	
	h = H(
		0x773ea91e, 0x36800e46, 0x854db8eb, 0xd09181a7,
		0x2959098b, 0x3ef8c122, 0xd9635514, 0xced565fe,
	);
	
	test(key.ptr[0 .. 20], dataStr, h);
	
	foreach (i; 0 .. 25) {
		key[i] = (i + 1) & 0xff;
	}
	
	foreach (i; 0 .. 50) {
		data[i] = 0xcd;
	}
	
	h = H(
		0x82558a38, 0x9a443c0e, 0xa4cc8198, 0x99f2083a,
		0x85f0faa3, 0xe578f807, 0x7a2e3ff4, 0x6729665b,
	);
	
	test(key.ptr[0 .. 25], dataStr, h);
	
	foreach (i; 0 .. 131) {
		key[i] = 0xaa;
	}
	
	h = H(
		0x60e43159, 0x1ee0b67f, 0x0d8a26aa, 0xcbf5b77f,
		0x8e0bc621, 0x3728c514, 0x0546040f, 0x0ee37f54,
	);
	
	test(
		key.ptr[0 .. 131],
		"Test Using Larger Than Block-Size Key - Hash Key First",
		h,
	);
	
	h = H(
		0x9b09ffa7, 0x1b942fcb, 0x27635fbc, 0xd5b0e944,
		0xbfdc6364, 0x4f071393, 0x8a7f5153, 0x5c3a35e2,
	);
	
	test(
		key.ptr[0 .. 131],
		"This is a test using a larger than block-size key and a larger "
			~ "than block-size data. The key needs to be hashed before being "
			~ "used by the HMAC algorithm.",
		h,
	);
	
	printf("OK\n".ptr);
}

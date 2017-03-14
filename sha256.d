module crypto.sha256;

/**
 * Long term, we want to use phobos's version, in the meantime, this will do.
 */
struct SHA256 {
private:
	union Buf {
		ulong[8] byUlong;
		ubyte[64] byUbyte;
	}
	
	Buf buffer;
	uint[8] state;
	ulong byteCount;
	
public:
	enum BlockSize = 64;
	
	this() {
		start();
	}
	
	void start() {
		byteCount = 0;
		state[0] = 0x6a09e667;
		state[1] = 0xbb67ae85;
		state[2] = 0x3c6ef372;
		state[3] = 0xa54ff53a;
		state[4] = 0x510e527f;
		state[5] = 0x9b05688c;
		state[6] = 0x1f83d9ab;
		state[7] = 0x5be0cd19;
	}
	
	void put(const(ubyte)[] input) {
		auto byteIndex = byteCount % 64;
		
		// If we can fill the buffer, do one round.
		if (byteIndex && ((byteIndex + input.length) >= 64)) {
			auto count = 64 - byteIndex;
			
			memcpy(buffer.byUbyte.ptr + byteIndex, input.ptr, count);
			transform(buffer.byUbyte);
			
			input = input[count .. input.length];
			byteCount += count;
			byteIndex = (byteIndex + count) % 64;
		}
		
		// Now we don't need to bufferise.
		while (input.length >= 64) {
			assert(byteIndex == 0, "unexpected buffer position");
			transform(*(cast(ubyte[64]*) input.ptr));
			input = input[64 .. input.length];
			byteCount += 64;
		}
		
		// Put the remaining bytes in the buffer.
		if (input.length > 0) {
			memcpy(buffer.byUbyte.ptr + byteIndex, input.ptr, input.length);
			byteCount += input.length;
		}
	}
	
	ubyte[32] finish() {
		static immutable padding = getPadding();
		
		auto count = byteCount;
		
		// We want to pad up to 448 bits mod 512.
		// This is 56 bytes mod 64.
		auto paddingSize = 64 - ((byteCount + 8) % 64);
		put(padding[0 .. paddingSize]);
		
		// SHA-256 append the size in bits to the last round.
		import sdc.intrinsics;
		buffer.byUlong[7] = bswap(count * 8);
		
		transform(buffer.byUbyte);
		
		uint[8] ret;
		foreach (i; 0 .. 8) {
			import sdc.intrinsics;
			ret[i] = bswap(state[i]);
		}
		
		// Same player play again.
		start();
		return *(cast(ubyte[32]*) &ret);
	}
	
private:
	static get(ref ubyte[64] chunk, uint i) {
		import sdc.intrinsics;
		return bswap((cast(uint*) &chunk)[i]);
	}
	
	void transform(ref ubyte[64] chunk) {
		static immutable constants = getConstants();
		
		auto s = state;
		uint[16] w;
		
		foreach (i; 0 .. 16) {
			Round(
				s[(0 - i) & 0x07],
				s[(1 - i) & 0x07],
				s[(2 - i) & 0x07],
				s[(3 - i) & 0x07],
				s[(4 - i) & 0x07],
				s[(5 - i) & 0x07],
				s[(6 - i) & 0x07],
				s[(7 - i) & 0x07],
				constants[i],
				w[i] = get(chunk, i),
			);
		}
		
		foreach (i; 16 .. 64) {
			w[i & 0x0f] += SmallSigma1(w[(i + 14) & 0x0f]);
			w[i & 0x0f] += w[(i + 9) & 0x0f];
			w[i & 0x0f] += SmallSigma0(w[(i + 1) & 0x0f]);
			Round(
				s[(0 - i) & 0x07],
				s[(1 - i) & 0x07],
				s[(2 - i) & 0x07],
				s[(3 - i) & 0x07],
				s[(4 - i) & 0x07],
				s[(5 - i) & 0x07],
				s[(6 - i) & 0x07],
				s[(7 - i) & 0x07],
				constants[i],
				w[i & 0x0f],
			);
		}
		
		foreach(i; 0 .. 8) {
			state[i] += s[i];
		}
	}
}

private:
auto getPadding() {
	ubyte[128] padding;
	padding[0] = 0x80;
	return padding;
}

auto getConstants() {
	uint[64] constants;
	
	constants[00] = 0x428a2f98;
	constants[01] = 0x71374491;
	constants[02] = 0xb5c0fbcf;
	constants[03] = 0xe9b5dba5;
	constants[04] = 0x3956c25b;
	constants[05] = 0x59f111f1;
	constants[06] = 0x923f82a4;
	constants[07] = 0xab1c5ed5;
	constants[08] = 0xd807aa98;
	constants[09] = 0x12835b01;
	constants[10] = 0x243185be;
	constants[11] = 0x550c7dc3;
	constants[12] = 0x72be5d74;
	constants[13] = 0x80deb1fe;
	constants[14] = 0x9bdc06a7;
	constants[15] = 0xc19bf174;
	constants[16] = 0xe49b69c1;
	constants[17] = 0xefbe4786;
	constants[18] = 0x0fc19dc6;
	constants[19] = 0x240ca1cc;
	constants[20] = 0x2de92c6f;
	constants[21] = 0x4a7484aa;
	constants[22] = 0x5cb0a9dc;
	constants[23] = 0x76f988da;
	constants[24] = 0x983e5152;
	constants[25] = 0xa831c66d;
	constants[26] = 0xb00327c8;
	constants[27] = 0xbf597fc7;
	constants[28] = 0xc6e00bf3;
	constants[29] = 0xd5a79147;
	constants[30] = 0x06ca6351;
	constants[31] = 0x14292967;
	constants[32] = 0x27b70a85;
	constants[33] = 0x2e1b2138;
	constants[34] = 0x4d2c6dfc;
	constants[35] = 0x53380d13;
	constants[36] = 0x650a7354;
	constants[37] = 0x766a0abb;
	constants[38] = 0x81c2c92e;
	constants[39] = 0x92722c85;
	constants[40] = 0xa2bfe8a1;
	constants[41] = 0xa81a664b;
	constants[42] = 0xc24b8b70;
	constants[43] = 0xc76c51a3;
	constants[44] = 0xd192e819;
	constants[45] = 0xd6990624;
	constants[46] = 0xf40e3585;
	constants[47] = 0x106aa070;
	constants[48] = 0x19a4c116;
	constants[49] = 0x1e376c08;
	constants[50] = 0x2748774c;
	constants[51] = 0x34b0bcb5;
	constants[52] = 0x391c0cb3;
	constants[53] = 0x4ed8aa4a;
	constants[54] = 0x5b9cca4f;
	constants[55] = 0x682e6ff3;
	constants[56] = 0x748f82ee;
	constants[57] = 0x78a5636f;
	constants[58] = 0x84c87814;
	constants[59] = 0x8cc70208;
	constants[60] = 0x90befffa;
	constants[61] = 0xa4506ceb;
	constants[62] = 0xbef9a3f7;
	constants[63] = 0xc67178f2;
	
	return constants;
}

uint rotateRight(uint x, uint n) {
	// FIXME: in contract
	assert(n < 32);
    return (x >> n) | (x << (32-n));
}

T Ch(T)(T x, T y, T z) {
	return z ^ (x & (y ^ z));
}

T Maj(T)(T x, T y, T z) {
	return (x & y) | (z & (x ^ y));
}

uint BigSigma0(uint x) {
	return rotateRight(x, 2) ^ rotateRight(x, 13) ^ rotateRight(x, 22);
}

uint BigSigma1(uint x) {
	return rotateRight(x, 6) ^ rotateRight(x, 11) ^ rotateRight(x, 25);
}

uint SmallSigma0(uint x) {
	return rotateRight(x, 7) ^ rotateRight(x, 18) ^ x >> 3;
}

uint SmallSigma1(uint x) {
	return rotateRight(x, 17) ^ rotateRight(x, 19) ^ x >> 10;
}

void Round(
	uint a,
	uint b,
	uint c,
	ref uint d,
	uint e,
	uint f,
	uint g,
	ref uint h,
	uint k,
	uint w,
) {
	uint t1 = h + BigSigma1(e) + Ch(e, f, g) + k + w;
	uint t2 = BigSigma0(a) + Maj(a, b, c);
	d += t1;
	h = t1 + t2;
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
	
	static testSHA(string str, ubyte[32] expected) {
		auto data = (cast(const(ubyte)*) str.ptr)[0 .. str.length];
		
		SHA256 hasher;
		hasher.start();
		hasher.put(data);
		auto h = hasher.finish();
		foreach (i; 0 .. 32) {
			assert(h[i] == expected[i]);
		}
		
		hasher.start();
		hasher.put(data[0 .. data.length / 2]);
		hasher.put(data[data.length / 2 .. data.length]);
		h = hasher.finish();
		foreach (i; 0 .. 32) {
			assert(h[i] == expected[i]);
		}
	}
	
	auto h = H(
		0xe3b0c442, 0x98fc1c14, 0x9afbf4c8, 0x996fb924,
		0x27ae41e4, 0x649b934c, 0xa495991b, 0x7852b855,
	);
	
	testSHA("", h);
	
	h = H(
		0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223,
		0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad,
	);

	testSHA("abc", h);
	
	h = H(
		0x09fe9a46, 0xc8132f4a, 0x9d6d8919, 0x4c5d7dd8,
		0xa6a79405, 0xff518653, 0xb2ee5ec6, 0x93d85dfd,
	);
	
	testSHA("abcdbcdecdefdefgefghfghigijhijkijkljklmklmnlmnomnopnopq", h);
	
	h = H(
		0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039,
		0xa33ce459, 0x64ff2167, 0xf6ecedd4, 0x19db06c1,
	);
	
	testSHA("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", h);
	
	h = H(
		0xf08a78cb, 0xbaee082b, 0x052ae070, 0x8f32fa1e,
		0x50c5c421, 0xaa772ba5, 0xdbb406a2, 0xea6be342,
	);
	
	testSHA("For this sample, this 63-byte string will be used as input data", h);
	
	h = H(
		0xab64eff7, 0xe88e2e46, 0x165e29f2, 0xbce41826,
		0xbd4c7b35, 0x52f6b382, 0xa9e7d3af, 0x47c245f8,
	);
	
	testSHA("This is exactly 64 bytes long, not counting the terminating byte", h);
	
	printf("OK\n".ptr);
}

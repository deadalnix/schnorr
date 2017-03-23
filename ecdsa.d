module crypto.ecdsa;

struct ECDSASig {
private:
	import crypto.scalar;
	Scalar r;
	Scalar s;
	
	this(Scalar r, Scalar s) {
		this.r = r;
		this.s = s;
	}
	
public:
	/**
	 * Parse an ECDSA transaction. If the buffer doesn't contain
	 * a valid signature, an invalid signature is returned.
	 */
	static parse(const(ubyte)[] buffer) {
		if (buffer.length < 1 || buffer[0] != 0x30) {
			// Buffer empty.
			throw new Exception();
		}
		
		buffer = buffer[1 .. buffer.length];
		auto len = parseLengthOrZero(buffer);
		if (buffer.length != len) {
			// Wrong length.
			throw new Exception();
		}
		
		auto s = parseScalar(buffer);
		auto r = parseScalar(buffer);
		
		// Length are not consistent.
		if (buffer.length != 0) {
			// Inconsistent length.
			throw new Exception();
		}
		
		return ECDSASig(r, s);
	}
	
	/**
	 * Verify the validity of an ECDSA signature.
	 */
	import crypto.doublegen, crypto.point;
	bool verify(ref DoubleGen g, Point p, ubyte[32] m) const {
		if (r.isZero() || s.isZero()) {
			return false;
		}
		
		auto mBuf = m.ptr[0 .. m.length];
		auto sm = Scalar.unserializeOrZero(mBuf);
		if (sm.isZero()) {
			return false;
		}
		
		import crypto.element;
		auto rs = r.serialize();
		auto rBuf = rs.ptr[0 .. rs.length];
		auto xr = Element.unserializeOrZero(rBuf);
		assert(!xr.isZero(), "p > o so this should never be");
		
		auto sinv = s.inverse();
		auto u1 = sinv.mul(sm);
		auto u2 = sinv.mul(r);
		
		auto jpr = g.mul(u1, u2, CartesianPoint(p));
		if (jpr.infinity) {
			return false;
		}
		
		// We could avoid normalization to check x, but will do for now.
		auto pr = jpr.normalize();
		return pr.x.opEquals(xr);
	}
	
	/**
	 * We sign by chosing a secret value k and computing R = k*G and
	 * proceed as per ECDSA algorithm. If the chosen value for k doesn't
	 * produce a valid signature, another value for k is chosen until
	 * it works. In practice, it is very unlikely to end up using a value
	 * of k that do not work, so looping is uncommon.
	 */
	import crypto.generator;
	static sign(ref Generator g, Scalar x, ubyte[32] m, ubyte[32] nonce) {
		auto mBuf = m.ptr[0 .. m.length];
		auto sm = Scalar.unserializeOrZero(mBuf);
		if (sm.isZero()) {
			throw new Exception();
		}
		
		/**
		 * Because there is a slim chance that values generated for k and e
		 * aren't valid scalar, we loop and tweak the nonce until we find
		 * a suitable k and e pair. In practice, the probability of this
		 * happening is about 1/2^128 so we pretty much never loops.
		 */
		while (true) {
			/**
			 * To get k, we HMAC!SHA256 the private key and the message
			 * using the nonce as key. This ensure that we have some level
			 * of safety even when the nonce randomness is compromized, or
			 * when reproducibility is desired.
			 *
			 * We need the private key as a source of randomness, plus other
			 * parameter of the signature to ensure k isn't reused, which would
			 * expose ways to recover the private key.
			 *
			 * FIXME: This should use RFC6979, but will do for now.
			 */
			import crypto.hmac, crypto.sha256;
			auto hmac = HMAC!SHA256(nonce.ptr[0 .. nonce.length]);
			
			auto sx = x.serialize();
			hmac.put(sx.ptr[0 .. sx.length]);
			hmac.put(m.ptr[0 .. m.length]);
			
			auto sk = hmac.finish();
			auto skBuf = sk.ptr[0 .. sk.length];
			auto k = Scalar.unserializeOrZero(skBuf);
			if (k.isZero()) {
				// FIXME: Create a new nonce.
				nonce[0]++;
				continue;
			}
			
			// We have k, let's compute R.
			auto jr = g.gen(k);
			auto pr = jr.normalize();
			auto rs = pr.x.serialize();
			auto rBuf = rs.ptr[0 .. rs.length];
			auto r = Scalar.unserializeOrZero(rBuf);
			if (r.isZero()) {
				// FIXME: Create a new nonce.
				nonce[4]++;
				continue;
			}
			
			auto n = sm.add(x.mul(r));
			auto s = n.mul(k.inverse());
			if (s.isZero()) {
				// FIXME: Create a new nonce.
				nonce[8]++;
				continue;
			}
			
			// FIXME: Check for high s value.
			return ECDSASig(r, s);
		}
		
		assert(0, "unreachable");
	}
	
private:
	static uint parseLengthOrZero(ref const(ubyte)[] buffer) {
		if (buffer.length < 1) {
			return 0;
		}
		
		auto b1 = buffer[0];
		if (b1 == 0xff || b1 == 0x80) {
			// 0xff is illegal and 0x80 is undefined length,
			// which is illegal as well.
			return 0;
		}
		
		buffer = buffer[1 .. buffer.length];
		if ((b1 & 0x80) == 0) {
			// Short int format.
			return b1;
		}
		
		// For ECDSA specifcially, len should never be larger
		// so we just bail here.
		return 0;
	}
	
	static parseScalar(ref const(ubyte)[] buffer) {
		if (buffer.length < 1) {
			// Not enough space in buffer.
			throw new Exception();
		}
		
		if (buffer[0] != 0x02) {
			// 2 is integer. This isn't an integer.
			throw new Exception();
		}
		
		buffer = buffer[1 .. buffer.length];
		auto len = parseLengthOrZero(buffer);
		if (len == 0 || buffer.length < len) {
			// If length is zero or if we don't have enough space
			// in the buffer, bail.
			throw new Exception();
		}
		
		auto b1 = buffer[0];
		if (len > 1) {
			auto b2 = buffer[1];
			if (b1 == 0 && (b2 & 0x80) == 0) {
				// Excessive 0 padding.
				throw new Exception();
			}
			
			if (b1 == 0xff && (b2 & 0x80) == 0x80) {
				// Excessive 0xff padding.
				throw new Exception();
			}
		}
		
		// Skip leading zeros.
		while (len > 0 && buffer[0] == 0) {
			len--;
			buffer = buffer[1 .. buffer.length];
		}
		
		if (len > 32) {
			// The number is too large to fit in a scalar.
			throw new Exception();
		}
		
		// Buffer to deserialize the scalar.
		ubyte[32] scalar;
		foreach (i; 0 .. len) {
			scalar[32 - len + i] = buffer[i];
		}
		
		buffer = buffer[len .. buffer.length];
		
		auto scalarBuf = scalar.ptr[0 .. scalar.length];
		return Scalar.unserialize(scalarBuf);
	}
	
	void dump() const {
		printf("r: ".ptr); r.dump(); printf("\n".ptr);
		printf("s: ".ptr); s.dump(); printf("\n".ptr);
	}
}

void main() {
	ubyte[32] m, nonce;
	
	import crypto.scalar;
	auto x0 = Scalar(42);
	auto x1 = x0.inverse();
	
	import crypto.point;
	auto g = Point.getG();
	
	import crypto.generator;
	auto gmul = Generator(g, nonce);
	
	auto jp0 = gmul.gen(x0);
	auto jp1 = gmul.gen(x1);
	auto p0 = jp0.normalize();
	auto p1 = jp1.normalize();
	
	import crypto.doublegen;
	auto dblgen = DoubleGen(g);
	
	static verifySig(ref DoubleGen dblgen, ECDSASig sig, Point p, ubyte[32] m) {
		assert(sig.verify(dblgen, p, m), "signature do not check out");
	}
	
	static denySig(ref DoubleGen dblgen, ECDSASig sig, Point p, ubyte[32] m) {
		assert(!sig.verify(dblgen, p, m), "signature do check out");
	}
	
	// Cannot sign 0. Doesn't matter in practice as this is a hash.
	try {
		ECDSASig.sign(gmul, x0, m, nonce);
		assert(0, "This should have thrown");
	} catch(Exception e) { }
	
	m[0] = 0xc6;
	
	// Each signature depends on a private key.
	auto sig0 = ECDSASig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig0, p0, m);
	denySig(dblgen, sig0, p1, m);
	
	// dito.
	auto sig1 = ECDSASig.sign(gmul, x1, m, nonce);
	verifySig(dblgen, sig1, p1, m);
	denySig(dblgen, sig1, p0, m);
	
	// Changing the message invalidate the sigs.
	m[5] = 0xab;
	denySig(dblgen, sig0, p0, m);
	denySig(dblgen, sig1, p1, m);
	
	// Changing the nonce produce another signature, but it verify as well.
	auto sig2 = ECDSASig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig2, p0, m);
	denySig(dblgen, sig2, p1, m);

	nonce[7] = 0x23;
	auto sig3 = ECDSASig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig3, p0, m);
	denySig(dblgen, sig3, p1, m);
	
	assert(!sig2.r.opEquals(sig3.r), "signatures must be different");
	assert(!sig2.s.opEquals(sig3.s), "signatures must be different");
	
	// Really 70 or 71, but it makes things easier.
	ubyte[72] sig;
	
	auto sigPtr = cast(ulong*) sig.ptr;
	import sdc.intrinsics;
	sigPtr[0] = bswap(0x304502207735303e);
	sigPtr[1] = bswap(0xfb716fe5ab13a424);
	sigPtr[2] = bswap(0x1e3d5c76556b8be5);
	sigPtr[3] = bswap(0x3a02f3029b862878);
	sigPtr[4] = bswap(0x8ae4bc8a022100c6);
	sigPtr[5] = bswap(0x72344b9fbf613c29);
	sigPtr[6] = bswap(0x1a3e75f25f9b304b);
	sigPtr[7] = bswap(0x79ebe97bdaf254b8);
	sigPtr[8] = bswap(0xa1030e0d2a22e200);
	
	auto sigBuf = sig.ptr[0 .. 71];
	ECDSASig.parse(sigBuf);
	
	sigPtr[0] = bswap(0x3044021f573e8316);
	sigPtr[1] = bswap(0xa07d2e14e2f1ce40);
	sigPtr[2] = bswap(0x50c093b772c6c7e7);
	sigPtr[3] = bswap(0x6654b15d5a3fdd14);
	sigPtr[4] = bswap(0x92761e022100ac18);
	sigPtr[5] = bswap(0x36ad5066f4fe17a5);
	sigPtr[6] = bswap(0xab59b6e86ce3febb);
	sigPtr[7] = bswap(0xbf441c657f86c07c);
	sigPtr[8] = bswap(0xc3004d0acbf80000);
	
	sigBuf = sig.ptr[0 .. 70];
	ECDSASig.parse(sigBuf);
	
	printf("OK\n".ptr);
}

extern(C):

bool crypto_ecdsa_parse(const(ubyte)[] buffer, ref ECDSASig sig) {
	try {
		sig = ECDSASig.parse(buffer);
		return true;
	} catch(Exception e) {}
	
	return false;
}

import crypto.context, crypto.point;
bool crypto_ecdsa_verify(
	const Context* ctx,
	ECDSASig sig,
	Point pubKey,
	ubyte[32] msg,
) {
	return sig.verify(ctx.dblg, pubKey, msg);
}

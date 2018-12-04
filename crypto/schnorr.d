module crypto.schnorr;

struct SchnorrSig {
private:
	import crypto.element;
	Element r;
	
	import crypto.scalar;
	Scalar s;
	
	this(Element r, Scalar s) {
		this.r = r;
		this.s = s;
	}
	
public:
	/**
	 * This takes a buffer as input and parses it as a Schnorr signature.
	 * If the buffer doesn't contains a valid signature, or if the buffer
	 * is too large, an exception is thrown.
	 */
	static parse(ref const(ubyte)[] buffer) {
		if (buffer.length != 64) {
			throw new Exception();
		}
		
		auto r = Element.unserializeOrZero(buffer);
		auto s = Scalar.unserializeOrZero(buffer);
		
		return SchnorrSig(r, s);
	}
	
	/**
	 * To verify the signature, we compute e = H(R.x || compressed(P) || m)
	 * and verify that R = s*G - e*P by checking the value of R.x and
	 * ensuring R.y is a quadratic residue.
	 */
	import crypto.doublegen, crypto.point;
	bool verify(ref DoubleGen g, Point p, ubyte[32] m) const {
		if (r.isZero() || s.isZero()) {
			return false;
		}
		
		// We check that R = s*G - e*P
		auto e = computeE(r, p, m);
		if (e.isZero()) {
			return false;
		}
		
		auto jr = g.mul(s, e.negate(), CartesianPoint(p));
		if (jr.infinity) {
			return false;
		}
		
		auto pr = jr.normalize();
		if (!r.opEquals(pr.x)) {
			return false;
		}
		
		import crypto.element;
		auto cry = ComputeElement(pr.y);
		return ComputeElement.sqrtImpl(cry);
	}
	
	/**
	 * We sign by chosing a secret value k and computing R = k*G and
	 * R.y is even. We then compute e such as e = H(R.x || P || m)
	 * and s = k + e*x to form the signature (R.x, s).
	 */
	import crypto.generator;
	static sign(ref Generator g, Scalar x, ubyte[32] m, ubyte[32] nonce) {
		// We should pass this explicitely, but will do for now.
		auto jp = g.gen(x);
		auto p = jp.normalize();
		
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
			auto r = jr.normalize();
			
			// Now we compute e.
			auto e = computeE(r.x, p, m);
			if (e.isZero()) {
				// FIXME: Create a new nonce.
				nonce[4]++;
				continue;
			}
			
			// We make sure r.y is a quadratic residue by negating k if it
			// is required. We don't need to update r.y as it isn't used.
			import crypto.element;
			auto cry = ComputeElement(r.y);
			k = Scalar.select(ComputeElement.sqrtImpl(cry), k, k.negate());
			
			/**
			 * We have a valid e and k, we can generate the signature
			 * using s = k + e*x .
			 */
			auto s = k.add(e.mul(x));
			return SchnorrSig(r.x, s);
		}
		
		assert(0, "unreachable");
	}
	
private:
	/**
	 * The function computes e = SHA256(R.x || compressed(P) || m).
	 * If the value obtained is not a valid scalar, e = 0 is returned.
	 */
	static computeE(Element rx, Point p, ubyte[32] m) {
		import crypto.sha256;
		SHA256 hasher;
		hasher.start();
		
		// First, we hash R.x
		auto srx = rx.serialize();
		hasher.put(srx.ptr[0 .. srx.length]);
		
		// Second we hash the public key.
		auto sp = p.serializeCompressed();
		hasher.put(sp.ptr[0 .. sp.length]);
		
		// Third we hash the message itself.
		hasher.put(m.ptr[0 .. m.length]);
		
		auto e = hasher.finish();
		auto eBuf = e.ptr[0 .. e.length];
		return Scalar.unserializeOrZero(eBuf);
	}
	
	void dump() const {
		import core.stdc.stdio;
		printf("r: ".ptr); r.dump(); printf("\n".ptr);
		printf("s: ".ptr); s.dump(); printf("\n".ptr);
	}
}

unittest end_to_end {
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
	
	static verifySig(ref DoubleGen dblgen, SchnorrSig sig, Point p, ubyte[32] m) {
		assert(sig.verify(dblgen, p, m), "signature do not check out");
	}
	
	static denySig(ref DoubleGen dblgen, SchnorrSig sig, Point p, ubyte[32] m) {
		assert(!sig.verify(dblgen, p, m), "signature do check out");
	}
	
	// Each signature depends on a private key.
	auto sig0 = SchnorrSig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig0, p0, m);
	denySig(dblgen, sig0, p1, m);
	
	// dito.
	auto sig1 = SchnorrSig.sign(gmul, x1, m, nonce);
	verifySig(dblgen, sig1, p1, m);
	denySig(dblgen, sig1, p0, m);
	
	// Changing the message invalidate the sigs.
	m[5] = 0xab;
	denySig(dblgen, sig0, p0, m);
	denySig(dblgen, sig1, p1, m);
	
	// Changing the nonce produce another signature, but it verify as well.
	auto sig2 = SchnorrSig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig2, p0, m);
	denySig(dblgen, sig2, p1, m);

	nonce[7] = 0x23;
	auto sig3 = SchnorrSig.sign(gmul, x0, m, nonce);
	verifySig(dblgen, sig3, p0, m);
	denySig(dblgen, sig3, p1, m);
	
	assert(!sig2.r.opEquals(sig3.r), "signatures must be different");
	assert(!sig2.s.opEquals(sig3.s), "signatures must be different");
}

unittest test_vectors {
	import crypto.point, crypto.doublegen;
	auto dblgen = DoubleGen(Point.getG());
	
	void checkSig(
		ref const ubyte[33] pk,
		ref const ubyte[32] msg,
		ref const ubyte[64] sig,
	) {
		auto pkbuf = pk[0 .. pk.length];
		auto p = Point.parse(pkbuf);
		assert(pkbuf.length == 0);
		
		auto sigbuf = sig[0 .. sig.length];
		SchnorrSig s = SchnorrSig.parse(sigbuf);
		assert(sigbuf.length == 0);
		
		assert(s.verify(dblgen, p, msg));
	}
	
	void checkInvalidSig(
		ref const ubyte[33] pk,
		ref const ubyte[32] msg,
		ref const ubyte[64] sig,
	) {
		auto pkbuf = pk[0 .. pk.length];
		auto p = Point.parse(pkbuf);
		assert(pkbuf.length == 0);
		
		auto sigbuf = sig[0 .. sig.length];
		SchnorrSig s = SchnorrSig.parse(sigbuf);
		assert(sigbuf.length == 0);
		
		assert(!s.verify(dblgen, p, msg));
	}
	
	/* Test vector 1 */
	{
		const ubyte[33] pk = [
			0x02,
			0x79, 0xBE, 0x66, 0x7E, 0xF9, 0xDC, 0xBB, 0xAC,
			0x55, 0xA0, 0x62, 0x95, 0xCE, 0x87, 0x0B, 0x07,
			0x02, 0x9B, 0xFC, 0xDB, 0x2D, 0xCE, 0x28, 0xD9,
			0x59, 0xF2, 0x81, 0x5B, 0x16, 0xF8, 0x17, 0x98,
		];
		
		const ubyte[32] msg = [
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		];
		
		const ubyte[64] sig = [
			0x78, 0x7A, 0x84, 0x8E, 0x71, 0x04, 0x3D, 0x28,
			0x0C, 0x50, 0x47, 0x0E, 0x8E, 0x15, 0x32, 0xB2,
			0xDD, 0x5D, 0x20, 0xEE, 0x91, 0x2A, 0x45, 0xDB,
			0xDD, 0x2B, 0xD1, 0xDF, 0xBF, 0x18, 0x7E, 0xF6,
			0x70, 0x31, 0xA9, 0x88, 0x31, 0x85, 0x9D, 0xC3,
			0x4D, 0xFF, 0xEE, 0xDD, 0xA8, 0x68, 0x31, 0x84,
			0x2C, 0xCD, 0x00, 0x79, 0xE1, 0xF9, 0x2A, 0xF1,
			0x77, 0xF7, 0xF2, 0x2C, 0xC1, 0xDC, 0xED, 0x05,
		];
		
		checkSig(pk, msg, sig);
	}
	
	/* Test vector 2 */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x2A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0x1E, 0x51, 0xA2, 0x2C, 0xCE, 0xC3, 0x55, 0x99,
			0xB8, 0xF2, 0x66, 0x91, 0x22, 0x81, 0xF8, 0x36,
			0x5F, 0xFC, 0x2D, 0x03, 0x5A, 0x23, 0x04, 0x34,
			0xA1, 0xA6, 0x4D, 0xC5, 0x9F, 0x70, 0x13, 0xFD,
		];
		
		checkSig(pk, msg, sig);
	}
	
	/* Test vector 3 */
	{
		const ubyte[33] pk = [
			0x03,
			0xFA, 0xC2, 0x11, 0x4C, 0x2F, 0xBB, 0x09, 0x15,
			0x27, 0xEB, 0x7C, 0x64, 0xEC, 0xB1, 0x1F, 0x80,
			0x21, 0xCB, 0x45, 0xE8, 0xE7, 0x80, 0x9D, 0x3C,
			0x09, 0x38, 0xE4, 0xB8, 0xC0, 0xE5, 0xF8, 0x4B,
		];
		
		const ubyte[32] msg = [
			0x5E, 0x2D, 0x58, 0xD8, 0xB3, 0xBC, 0xDF, 0x1A,
			0xBA, 0xDE, 0xC7, 0x82, 0x90, 0x54, 0xF9, 0x0D,
			0xDA, 0x98, 0x05, 0xAA, 0xB5, 0x6C, 0x77, 0x33,
			0x30, 0x24, 0xB9, 0xD0, 0xA5, 0x08, 0xB7, 0x5C,
		];
		
		const ubyte[64] sig = [
			0x00, 0xDA, 0x9B, 0x08, 0x17, 0x2A, 0x9B, 0x6F,
			0x04, 0x66, 0xA2, 0xDE, 0xFD, 0x81, 0x7F, 0x2D,
			0x7A, 0xB4, 0x37, 0xE0, 0xD2, 0x53, 0xCB, 0x53,
			0x95, 0xA9, 0x63, 0x86, 0x6B, 0x35, 0x74, 0xBE,
			0x00, 0x88, 0x03, 0x71, 0xD0, 0x17, 0x66, 0x93,
			0x5B, 0x92, 0xD2, 0xAB, 0x4C, 0xD5, 0xC8, 0xA2,
			0xA5, 0x83, 0x7E, 0xC5, 0x7F, 0xED, 0x76, 0x60,
			0x77, 0x3A, 0x05, 0xF0, 0xDE, 0x14, 0x23, 0x80,
		];
		
		checkSig(pk, msg, sig);
	}
	
	/* Test vector 4 */
	{
		const ubyte[33] pk = [
			0x03,
			0xDE, 0xFD, 0xEA, 0x4C, 0xDB, 0x67, 0x77, 0x50,
			0xA4, 0x20, 0xFE, 0xE8, 0x07, 0xEA, 0xCF, 0x21,
			0xEB, 0x98, 0x98, 0xAE, 0x79, 0xB9, 0x76, 0x87,
			0x66, 0xE4, 0xFA, 0xA0, 0x4A, 0x2D, 0x4A, 0x34,
		];
		
		const ubyte[32] msg = [
			0x4D, 0xF3, 0xC3, 0xF6, 0x8F, 0xCC, 0x83, 0xB2,
			0x7E, 0x9D, 0x42, 0xC9, 0x04, 0x31, 0xA7, 0x24,
			0x99, 0xF1, 0x78, 0x75, 0xC8, 0x1A, 0x59, 0x9B,
			0x56, 0x6C, 0x98, 0x89, 0xB9, 0x69, 0x67, 0x03,
		];
		
		const ubyte[64] sig = [
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x3B, 0x78, 0xCE, 0x56, 0x3F,
			0x89, 0xA0, 0xED, 0x94, 0x14, 0xF5, 0xAA, 0x28,
			0xAD, 0x0D, 0x96, 0xD6, 0x79, 0x5F, 0x9C, 0x63,
			0x02, 0xA8, 0xDC, 0x32, 0xE6, 0x4E, 0x86, 0xA3,
			0x33, 0xF2, 0x0E, 0xF5, 0x6E, 0xAC, 0x9B, 0xA3,
			0x0B, 0x72, 0x46, 0xD6, 0xD2, 0x5E, 0x22, 0xAD,
			0xB8, 0xC6, 0xBE, 0x1A, 0xEB, 0x08, 0xD4, 0x9D,
		];
		
		checkSig(pk, msg, sig);
	}
	
	/* Test vector 4b */
	{
		const ubyte[33] pk = [
			0x03,
			0x1B, 0x84, 0xC5, 0x56, 0x7B, 0x12, 0x64, 0x40,
			0x99, 0x5D, 0x3E, 0xD5, 0xAA, 0xBA, 0x05, 0x65,
			0xD7, 0x1E, 0x18, 0x34, 0x60, 0x48, 0x19, 0xFF,
			0x9C, 0x17, 0xF5, 0xE9, 0xD5, 0xDD, 0x07, 0x8F,
		];
		
		const ubyte[32] msg = [
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		];
		
		const ubyte[64] sig = [
			0x52, 0x81, 0x85, 0x79, 0xAC, 0xA5, 0x97, 0x67,
			0xE3, 0x29, 0x1D, 0x91, 0xB7, 0x6B, 0x63, 0x7B,
			0xEF, 0x06, 0x20, 0x83, 0x28, 0x49, 0x92, 0xF2,
			0xD9, 0x5F, 0x56, 0x4C, 0xA6, 0xCB, 0x4E, 0x35,
			0x30, 0xB1, 0xDA, 0x84, 0x9C, 0x8E, 0x83, 0x04,
			0xAD, 0xC0, 0xCF, 0xE8, 0x70, 0x66, 0x03, 0x34,
			0xB3, 0xCF, 0xC1, 0x8E, 0x82, 0x5E, 0xF1, 0xDB,
			0x34, 0xCF, 0xAE, 0x3D, 0xFC, 0x5D, 0x81, 0x87,
		];
		
		checkSig(pk, msg, sig);
	}
	
	/* Test vector 6: R.y is not a quadratic residue */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x2A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0xFA, 0x16, 0xAE, 0xE0, 0x66, 0x09, 0x28, 0x0A,
			0x19, 0xB6, 0x7A, 0x24, 0xE1, 0x97, 0x7E, 0x46,
			0x97, 0x71, 0x2B, 0x5F, 0xD2, 0x94, 0x39, 0x14,
			0xEC, 0xD5, 0xF7, 0x30, 0x90, 0x1B, 0x4A, 0xB7,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 7: Negated message hash, R.x mismatch */
	{
		const ubyte[33] pk = [
			0x03,
			0xFA, 0xC2, 0x11, 0x4C, 0x2F, 0xBB, 0x09, 0x15,
			0x27, 0xEB, 0x7C, 0x64, 0xEC, 0xB1, 0x1F, 0x80,
			0x21, 0xCB, 0x45, 0xE8, 0xE7, 0x80, 0x9D, 0x3C,
			0x09, 0x38, 0xE4, 0xB8, 0xC0, 0xE5, 0xF8, 0x4B,
		];
		
		const ubyte[32] msg = [
			0x5E, 0x2D, 0x58, 0xD8, 0xB3, 0xBC, 0xDF, 0x1A,
			0xBA, 0xDE, 0xC7, 0x82, 0x90, 0x54, 0xF9, 0x0D,
			0xDA, 0x98, 0x05, 0xAA, 0xB5, 0x6C, 0x77, 0x33,
			0x30, 0x24, 0xB9, 0xD0, 0xA5, 0x08, 0xB7, 0x5C,
		];
		
		const ubyte[64] sig = [
			0x00, 0xDA, 0x9B, 0x08, 0x17, 0x2A, 0x9B, 0x6F,
			0x04, 0x66, 0xA2, 0xDE, 0xFD, 0x81, 0x7F, 0x2D,
			0x7A, 0xB4, 0x37, 0xE0, 0xD2, 0x53, 0xCB, 0x53,
			0x95, 0xA9, 0x63, 0x86, 0x6B, 0x35, 0x74, 0xBE,
			0xD0, 0x92, 0xF9, 0xD8, 0x60, 0xF1, 0x77, 0x6A,
			0x1F, 0x74, 0x12, 0xAD, 0x8A, 0x1E, 0xB5, 0x0D,
			0xAC, 0xCC, 0x22, 0x2B, 0xC8, 0xC0, 0xE2, 0x6B,
			0x20, 0x56, 0xDF, 0x2F, 0x27, 0x3E, 0xFD, 0xEC,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 8: Negated s, R.x mismatch */
	{
		const ubyte[33] pk = [
			0x02,
			0x79, 0xBE, 0x66, 0x7E, 0xF9, 0xDC, 0xBB, 0xAC,
			0x55, 0xA0, 0x62, 0x95, 0xCE, 0x87, 0x0B, 0x07,
			0x02, 0x9B, 0xFC, 0xDB, 0x2D, 0xCE, 0x28, 0xD9,
			0x59, 0xF2, 0x81, 0x5B, 0x16, 0xF8, 0x17, 0x98,
		];
		
		const ubyte[32] msg = [
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
			0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
		];
		
		const ubyte[64] sig = [
			0x78, 0x7A, 0x84, 0x8E, 0x71, 0x04, 0x3D, 0x28,
			0x0C, 0x50, 0x47, 0x0E, 0x8E, 0x15, 0x32, 0xB2,
			0xDD, 0x5D, 0x20, 0xEE, 0x91, 0x2A, 0x45, 0xDB,
			0xDD, 0x2B, 0xD1, 0xDF, 0xBF, 0x18, 0x7E, 0xF6,
			0x8F, 0xCE, 0x56, 0x77, 0xCE, 0x7A, 0x62, 0x3C,
			0xB2, 0x00, 0x11, 0x22, 0x57, 0x97, 0xCE, 0x7A,
			0x8D, 0xE1, 0xDC, 0x6C, 0xCD, 0x4F, 0x75, 0x4A,
			0x47, 0xDA, 0x6C, 0x60, 0x0E, 0x59, 0x54, 0x3C,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 9: Negated P, R.x mismatch */
	{
		const ubyte[33] pk = [
			0x03,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x2A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0x1E, 0x51, 0xA2, 0x2C, 0xCE, 0xC3, 0x55, 0x99,
			0xB8, 0xF2, 0x66, 0x91, 0x22, 0x81, 0xF8, 0x36,
			0x5F, 0xFC, 0x2D, 0x03, 0x5A, 0x23, 0x04, 0x34,
			0xA1, 0xA6, 0x4D, 0xC5, 0x9F, 0x70, 0x13, 0xFD,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 10: s * G = e * P, R = 0 */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x2A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0x8C, 0x34, 0x28, 0x86, 0x9A, 0x66, 0x3E, 0xD1,
			0xE9, 0x54, 0x70, 0x5B, 0x02, 0x0C, 0xBB, 0x3E,
			0x7B, 0xB6, 0xAC, 0x31, 0x96, 0x5B, 0x9E, 0xA4,
			0xC7, 0x3E, 0x22, 0x7B, 0x17, 0xC5, 0xAF, 0x5A,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 11: R.x not on the curve, R.x mismatch */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x4A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0x1E, 0x51, 0xA2, 0x2C, 0xCE, 0xC3, 0x55, 0x99,
			0xB8, 0xF2, 0x66, 0x91, 0x22, 0x81, 0xF8, 0x36,
			0x5F, 0xFC, 0x2D, 0x03, 0x5A, 0x23, 0x04, 0x34,
			0xA1, 0xA6, 0x4D, 0xC5, 0x9F, 0x70, 0x13, 0xFD,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 12: r = order */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFC, 0x2F,
			0x1E, 0x51, 0xA2, 0x2C, 0xCE, 0xC3, 0x55, 0x99,
			0xB8, 0xF2, 0x66, 0x91, 0x22, 0x81, 0xF8, 0x36,
			0x5F, 0xFC, 0x2D, 0x03, 0x5A, 0x23, 0x04, 0x34,
			0xA1, 0xA6, 0x4D, 0xC5, 0x9F, 0x70, 0x13, 0xFD,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
	
	/* Test vector 13: s = p */
	{
		const ubyte[33] pk = [
			0x02,
			0xDF, 0xF1, 0xD7, 0x7F, 0x2A, 0x67, 0x1C, 0x5F,
			0x36, 0x18, 0x37, 0x26, 0xDB, 0x23, 0x41, 0xBE,
			0x58, 0xFE, 0xAE, 0x1D, 0xA2, 0xDE, 0xCE, 0xD8,
			0x43, 0x24, 0x0F, 0x7B, 0x50, 0x2B, 0xA6, 0x59,
		];
		
		const ubyte[32] msg = [
			0x24, 0x3F, 0x6A, 0x88, 0x85, 0xA3, 0x08, 0xD3,
			0x13, 0x19, 0x8A, 0x2E, 0x03, 0x70, 0x73, 0x44,
			0xA4, 0x09, 0x38, 0x22, 0x29, 0x9F, 0x31, 0xD0,
			0x08, 0x2E, 0xFA, 0x98, 0xEC, 0x4E, 0x6C, 0x89,
		];
		
		const ubyte[64] sig = [
			0x2A, 0x29, 0x8D, 0xAC, 0xAE, 0x57, 0x39, 0x5A,
			0x15, 0xD0, 0x79, 0x5D, 0xDB, 0xFD, 0x1D, 0xCB,
			0x56, 0x4D, 0xA8, 0x2B, 0x0F, 0x26, 0x9B, 0xC7,
			0x0A, 0x74, 0xF8, 0x22, 0x04, 0x29, 0xBA, 0x1D,
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
			0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
			0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B,
			0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
		];
		
		checkInvalidSig(pk, msg, sig);
	}
}

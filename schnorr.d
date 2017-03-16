import crypto.schnorr;

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
		
		auto r = Element.unserialize(buffer);
		auto s = Scalar.unserialize(buffer);
		
		return SchnorrSig(r, s);
	}
	
	/**
	 * To verify the signature, we compute e = H(R.x || P || m) and
	 * verify that R = e*P + s*G by checking the value of R.x and
	 * ensuring R.y is even.
	 */
	import crypto.doublegen, crypto.point;
	bool verify(ref DoubleGen g, Point p, ubyte[32] m) const {
		// We check that R = e*P + s*G
		auto e = computeE(r, p, m);
		if (e.isZero()) {
			return false;
		}
		
		auto jr = g.mul(s, e, CartesianPoint(p));
		if (jr.infinity) {
			return false;
		}
		
		auto pr = jr.normalize();
		return pr.y.isEven() && r.opEquals(pr.x);
	}
	
	/**
	 * We sign by chosing a secret value k and computing R = k*G and
	 * R.y is even. We then compute e such as e = H(R.x || P || m)
	 * and s = k - e*x to form the signature (R.x, s).
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
			
			/**
			 * Now we compute e.
			 *
			 * It doesn't matter if R is even or odd as e only depends
			 * on r.x . If it turns out that y is odd, we negate k which
			 * doesn't affect r.x .
			 */
			auto e = computeE(r.x, p, m);
			if (e.isZero()) {
				// FIXME: Create a new nonce.
				nonce[4]++;
				continue;
			}
			
			// We make sure r.y is even by negating k if it is odd.
			// We don't need to update r.y as it isn't used anymore.
			auto odd = r.y.isOdd();
			k = Scalar.select(odd, k.negate(), k);
			
			/**
			 * We have a valid e and k, we can generate the signature
			 * using s = k - e*x .
			 */
			auto s = k.sub(e.mul(x));
			return SchnorrSig(r.x, s);
		}
		
		assert(0, "unreachable");
	}
	
private:
	/**
	 * The function computes e = SHA256(R.x || P || m) . If the value
	 * obtained is not a valid scalar, e = 0 is returned.
	 */
	static computeE(Element rx, Point p, ubyte[32] m) {
		import crypto.sha256;
		SHA256 hasher;
		hasher.start();
		
		// First, we hash R.x
		auto srx = rx.serialize();
		hasher.put(srx.ptr[0 .. srx.length]);
		
		// Second we hash the public key.
		auto sp = p.serialize();
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

unittest {
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

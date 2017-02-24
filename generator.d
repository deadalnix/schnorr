module crypto.generator;

/**
 * This structure allows to precompute a bunch of data
 * to do safe and fast multiplication by a given point.
 *
 * Because the precomputation is expensive, this should
 * only be used when mutliplying the same point multiple
 * time by different scalars.
 */
struct Generator {
private:
	/**
	 * Instead of computing n*G, we compute (n+b)*G - b*G .
	 * If we leak informations via side channels for some reason,
	 * an attacker will have hard time to do anything with it
	 * unless the attacker was also able to observe the blinding
	 * setup.
	 *
	 * This comes at a cost of one extra point addition and scalar
	 * substraction, which is cheap compared to the whole point
	 * multiplication process.
	 */
	import crypto.scalar;
	Scalar blindingFactor;
	
	/**
	 * Lookup tables to speedup multiply.
	 *
	 * Instead of putting directly the values we are interested in
	 * the table, we compute U0, U1, ..., U63 such as no corresponding
	 * scalar is known, but such as the sum of all Ui is b*G.
	 *
	 * This way, none of the precomputed point or any of the intermediate
	 * results have known corresponding scalar. In case of a side channel
	 * attack, an attacker who did not observed the setup will have a much
	 * harder time to retrieve usable data from it.
	 */
	// FIXME: importing crypto.point creates an infinite loop.
	import crypto.point;
	Point[16][64] lookup;
	
public:
	this(Point generator, ubyte[32] seed) {
		/**
		 * We need to build the lookup tables before we are able to multiply
		 * by G. So, we initalize the blinding to 0, build the lookup tables,
		 * and then randomize blinding, using the lookup tables to compute b*G.
		 */
		blindingFactor = Scalar(0);
		
		// FIXME: Use the seed to generate a random point.
		auto u = CartesianPoint(generator);
		JacobianPoint[16][64] jlookup = void;
		
		auto gbase = CartesianPoint(generator);
		auto ubase = JacobianPoint(u);
		
		foreach (i; 0 .. 63) {
			jlookup[i][0] = ubase;
			foreach (j; 1 .. 16) {
				jlookup[i][j] = jlookup[i][j - 1].add(gbase);
			}
			
			// Multiply gbase by 16 to get ready for the next round.
			auto jgbase = JacobianPoint(gbase);
			for (uint j = 0; j < 4; j++) {
				jgbase = jgbase.pdouble();
			}
			
			// FIXME: Works in jacobian for gbase all the way to avoid
			// expensive z inversion.
			gbase = CartesianPoint(jgbase);
			
			// Double ubase to get the next Ui.
			ubase = ubase.pdouble();
		}
		
		// Last round is a bit special because we need to cancel the Ui.
		// We have ubase = 2^63*U but we need ubase = (1 - 2^63)*U
		ubase = ubase.negate();
		ubase = ubase.add(u);
		
		jlookup[63][0] = ubase;
		foreach (j; 1 .. 16) {
			jlookup[63][j] = jlookup[63][j - 1].add(gbase);
		}
		
		/**
		 * FIXME: It is possible to normalize en masse jacobian points using
		 *   Z0 = z0
		 *   Z1 = Z0*z1
		 *   Z2 = Z1*z2
		 *   Z2inv = Z2^-1
		 *   z2inv = Z2inv*Z1
		 *   Z1inv = Z2inv*z2
		 *   z1inv = Z1inv*Z0
		 *   z0inv = Z1inv*z1
		 */
		foreach (i; 0 .. 64) {
			foreach (j; 0 .. 16) {
				lookup[i][j] = jlookup[i][j].normalize();
			}
		}
		
		// We are now in a state where we can multiply, so we can compute
		// a blinding factor and update the lookup tables with it.
		// FIXME: Generate blinding factor from seed.
		auto bf = Scalar(12345);
		auto bg = gen(bf.negate());
		
		// Update Generator state to include the blinding factor.
		blindingFactor = bf;
		
		foreach (j; 0 .. 16) {
			auto p = jlookup[63][j].add(bg);
			// FIXME: Mass normalize.
			lookup[63][j] = p.normalize();
		}
	}
	
	auto gen(Scalar n) {
		// FIXME: This is breaking codegen instead of generating an error.
		// auto k = n + blindingFactor;
		auto k = n.add(blindingFactor);
		
		import crypto.field;
		auto zero = ComputeElement(0);
		auto r = JacobianPoint(zero, zero, zero, false);
		
		foreach (i; 0 .. 64) {
			auto parts = k.getParts();
			auto bits = (parts[i >> 4] >> (i & 0x0f)) & 0x0f;
			
			/**
			 * We want to avoid side channels attacks. One of the most common
			 * side channel is memory access, as it impact the cache. To avoid
			 * leaking the secret, we make sure no memory access depends on the
			 * secret. This is achieved by accessing all elements in the table.
			 */
			auto p = lookup[i][0];
			foreach (j; 1 .. 16) {
				p = Point.select(i == bits, p, lookup[i][j]);
			}
			
			r = r.add(CartesianPoint(p));
		}
		
		return CartesianPoint(r);
	}
}

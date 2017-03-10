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
			auto jgbase = gbase.pdoublen!4();
			
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
		JacobianPoint[64] jbgs;
		auto bf = Scalar(0);
		foreach (i; 0 .. 64) {
			// FIXME: Use the seed instead fo doing random crap.
			auto bf19 = bf.add(Scalar(19));
			auto rbf = bf19.inverse();
			rbf = rbf.add(bf19.square());
			
			// Accumulate each round's blinding factor.
			bf = bf.add(rbf);
			jbgs[i] = gen(rbf.negate());
		}
		
		// Update Generator state to include the blinding factor.
		blindingFactor = bf;
		
		foreach (i; 0 .. 64) {
			foreach (j; 0 .. 16) {
				auto p = CartesianPoint(lookup[i][j]);
				auto jbg = jbgs[i].add(p);
				lookup[i][j] = jbg.normalize();
			}
		}
	}
	
	auto gen(Scalar n) {
		// FIXME: This is breaking codegen instead of generating an error.
		// auto k = n + blindingFactor;
		auto k = n.add(blindingFactor);
		
		import crypto.field;
		auto zero = ComputeElement(0);
		
		auto parts = k.getParts();
		
		// Round 1: get a cartesian point.
		auto c = select(0, parts[0] & 0x0f);
		
		// Round 2: get a jacobian point.
		auto r = c.add(select(1, (parts[0] >> 4) & 0x0f));
		
		// Round 3 onward, jacobian/cartesian addition.
		foreach (i; 2 .. 64) {
			auto bits = (parts[i >> 4] >> ((4*i) & 0x3f)) & 0x0f;
			r = r.add(select(i, bits));
		}
		
		return r;
	}
	
private:
	auto select(uint i, long bits) {
		/**
		 * We want to avoid side channels attacks. One of the most common
		 * side channel is memory access, as it impact the cache. To avoid
		 * leaking the secret, we make sure no memory access depends on the
		 * secret. This is achieved by accessing all elements in the table.
		 */
		auto p = lookup[i][0];
		foreach (j; 1 .. 16) {
			p = Point.select(j == bits, lookup[i][j], p);
		}
		
		return CartesianPoint(p);
	}
}

void main() {
	ubyte[32] seed;
	
	import crypto.point;
	auto g = CartesianPoint(G);
	auto gmul = Generator(G, seed);
	
	import crypto.scalar;
	auto zero = Scalar(0);
	auto zerog = gmul.gen(zero);
	auto inf = CartesianPoint(g.add(g.negate()));
	assert(zerog.opEquals(inf), "0*G == O");
	
	auto one = Scalar(1);
	auto oneg = gmul.gen(one);
	assert(oneg.opEquals(g), "1*G == G");
	
	auto negone = one.negate();
	auto negoneg = gmul.gen(negone);
	assert(negoneg.opEquals(g.negate()), "-1*G == -G");
	
	auto two = Scalar(2);
	auto twog = gmul.gen(two);
	auto dblg = CartesianPoint(g.pdouble());
	assert(twog.opEquals(dblg), "2*G == G + G");
	
	auto negtwo = two.negate();
	auto negtwog = gmul.gen(negtwo);
	assert(negtwog.opEquals(dblg.negate()), "-2*G == - (G + G)");
	
	import crypto.field;
	auto beta = ComputeElement(Beta);
	auto beta2 = beta.square();
	
	// If P = (x, y), Lambda*P = (Beta*x, y)
	auto lambda = Lambda;
	auto lambdag = gmul.gen(lambda);
	auto betaxg = CartesianPoint(g.x.mul(beta), g.y, g.infinity);
	assert(lambdag.opEquals(betaxg), "Lambda*G == (Beta*G.x, G.y)");
	
	auto neglambda = lambda.negate();
	auto neglambdag = gmul.gen(neglambda);
	auto negbetaxg = CartesianPoint(g.x.mul(beta), g.y.negate(), g.infinity);
	assert(neglambdag.opEquals(negbetaxg), "-Lambda*G == (Beta*G.x, -G.y)");
	
	auto lambda2 = lambda.square();
	auto lambda2g = gmul.gen(lambda2);
	auto beta2xg = CartesianPoint(g.x.mul(beta2), g.y, g.infinity);
	assert(lambda2g.opEquals(beta2xg), "Lambda^2*G == (Beta^2*G.x, G.y)");
	
	auto neglambda2 = lambda2.negate();
	auto neglambda2g = gmul.gen(neglambda2);
	auto negbeta2xg = CartesianPoint(g.x.mul(beta2), g.y.negate(), g.infinity);
	assert(
		neglambda2g.opEquals(negbeta2xg),
		"-Lambda^2*G == (Beta^2*G.x, -G.y)",
	);
	
	printf("OK\n".ptr);
}

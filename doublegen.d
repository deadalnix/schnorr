module crypto.doublegen;

/**
 * This is a facility to compye formular of the form s*G + e*P
 * which are failry common when verifying signatures.
 *
 * This does precompute various data related to G and will compute
 * everything realted to P on the fly.
 */
struct DoubleGen {
private:
	import crypto.point;
	Point[128] gtable = void;
	
public:
	this(CartesianPoint p) {
		import crypto.wnaf;
		Wnaf!8.fillNormalizedTable(gtable, p);
	}
	
	import crypto.scalar;
	auto mul(Scalar s, Scalar e, CartesianPoint p) const {
		CartesianPoint[8] ptable;
		
		import crypto.wnaf;
		auto globalz = Wnaf!4.fillTable(ptable, p);
		
		auto swnaf = Wnaf!8(s);
		auto ewnaf = Wnaf!4(e);
		
		auto first = ewnaf.select(ptable, 0);
		auto r = first.pdoublen!4();
		
		r = r.add(ewnaf.select(ptable, 1));
		
		// G was precomputed in proper z coordinate.
		r = r.addScalled(swnaf.select(gtable, 0), globalz);
		
		foreach (i; 1 .. 32) {
			r = r.pdoublen!4();
			r = r.add(ewnaf.select(ptable, 2*i));
			
			r = r.pdoublen!4();
			r = r.add(ewnaf.select(ptable, 2*i + 1));
			
			// G was precomputed in proper z coordinate.
			r = r.addScalled(swnaf.select(gtable, i), globalz);
		}
		
		// Final fixup of the z coordinate and we are done.
		r.z = r.z.mul(globalz);
		return r;
	}
}

void main() {
	import crypto.point;
	auto g = CartesianPoint(Point.getG());
	auto gen = DoubleGen(g);
	
	import crypto.scalar;
	auto zero = Scalar(0);
	
	auto zerog0 = gen.mul(zero, zero, g);
	auto inf = CartesianPoint(g.add(g.negate()));
	assert(zerog0.opEquals(inf), "0*G + 0*G == O");
	
	auto one = Scalar(1);
	auto dblg = CartesianPoint(g.pdouble());
	auto oneg0 = gen.mul(one, zero, g);
	assert(oneg0.opEquals(g), "1*G + 0*G == G");
	auto oneg1 = gen.mul(zero, one, g);
	assert(oneg1.opEquals(g), "0*G + 1*G == G");
	auto twog0 = gen.mul(one, one, g);
	assert(twog0.opEquals(dblg), "1*G + 1*G == 2*G");
	
	auto negone = one.negate();
	auto negg = g.negate();
	auto negdblg = dblg.negate();
	auto negoneg0 = gen.mul(negone, zero, g);
	assert(negoneg0.opEquals(negg), "-1*G + 0*G == -1*G");
	auto negoneg1 = gen.mul(zero, negone, g);
	assert(negoneg1.opEquals(negg), "0*G + -1*G == -1*G");
	auto zerog1 = gen.mul(one, negone, g);
	assert(zerog1.opEquals(inf), "1*G + -1*G == O");
	auto zerog2 = gen.mul(negone, one, g);
	assert(zerog2.opEquals(inf), "-1*G + 1*G == O");
	auto negtwog0 = gen.mul(negone, negone, g);
	assert(negtwog0.opEquals(negdblg), "-1*G + -1*G == -2*G");
	
	auto two = Scalar(2);
	auto quadg = CartesianPoint(dblg.pdouble());
	auto twog1 = gen.mul(two, zero, g);
	assert(twog1.opEquals(dblg), "2*G + 0*G == 2*G");
	auto twog2 = gen.mul(zero, two, g);
	assert(twog2.opEquals(dblg), "0*G + 2*G == 2*G");
	auto oneg2 = gen.mul(two, negone, g);
	assert(oneg2.opEquals(g), "2*G + -1*G == G");
	auto oneg3 = gen.mul(negone, two, g);
	assert(oneg3.opEquals(g), "-1*G + 2*G == G");
	auto fourg = gen.mul(two, two, g);
	assert(fourg.opEquals(quadg), "2*G + 2*G == 4*G");
	
	auto negtwo = two.negate();
	auto negquadg = quadg.negate();
	auto negtwog1 = gen.mul(negtwo, zero, g);
	assert(negtwog1.opEquals(negdblg), "-2*G + 0*G == -2*G");
	auto negtwog2 = gen.mul(zero, negtwo, g);
	assert(negtwog2.opEquals(negdblg), "0*G + -2*G == -2*G");
	auto negoneg2 = gen.mul(negtwo, one, g);
	assert(negoneg2.opEquals(negg), "-2*G + 1*G == -G");
	auto negoneg3 = gen.mul(one, negtwo, g);
	assert(negoneg3.opEquals(negg), "1*G + -2*G == -G");
	auto negfourg = gen.mul(negtwo, negtwo, g);
	assert(negfourg.opEquals(negquadg), "-2*G + -2*G == -4*G");
	
	import crypto.element;
	auto beta = ComputeElement(Beta);
	auto beta2 = beta.square();
	
	// If P = (x, y), Lambda*P = (Beta*x, y)
	auto lambda = Lambda;
	auto betaxg = CartesianPoint(g.x.mul(beta), g.y, g.infinity);
	auto lambdag0 = gen.mul(zero, lambda, g);
	assert(lambdag0.opEquals(betaxg), "0*G + Lambda*G == (Beta*G.x, G.y)");
	auto lambdag1 = gen.mul(lambda, zero, g);
	assert(lambdag1.opEquals(betaxg), "Lambda*G + 0*G == (Beta*G.x, G.y)");
	
	auto dblbetaxg = CartesianPoint(betaxg.pdouble());
	auto dbllambdag0 = gen.mul(lambda, one, betaxg);
	assert(
		dbllambdag0.opEquals(dblbetaxg),
		"Lambda*G + 1*BetaG == 2*(Beta*G.x, G.y)",
	);
	
	printf("OK\n".ptr);
}

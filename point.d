module crypto.point;

// As per "Standards for Efficient Cryptography" (SEC2) 2.7.1.
enum B = 7;
enum G = Point.getG();

struct Point {
private:
	import crypto.field;
	Element x;
	Element y;
	
public:
	this(Element x, Element y) {
		this.x = x;
		this.y = y;
	}
	
	// TODO: implicit cast to CartesianPoint.
	
	static select(bool cond, Point a, Point b) {
		return Point(
			Element.select(cond, a.x, b.x),
			Element.select(cond, a.y, b.y),
		);
	}
	
private:
	static getG() {
		return Point(
			Element(
				0x79BE667EF9DCBBAC,
				0x55A06295CE870B07,
				0x029BFCDB2DCE28D9,
				0x59F2815B16F81798,
			),
			Element(
				0x483ADA7726A3C465,
				0x5DA4FBFC0E1108A8,
				0xFD17B448A6855419,
				0x9C47D08FFB10D4B8,
			),
		);
	}
}

struct CartesianPoint {
private:
	import crypto.field;
	ComputeElement x;
	ComputeElement y;
	bool infinity;
	
public:
	this(Point p) {
		this(ComputeElement(p.x), ComputeElement(p.y), false);
	}
	
	// Consider moving this to the JacobianPoint
	// and do z normalization in the process.
	this(JacobianPoint p) {
		auto zinv = p.z.inverse();
		
		auto zinv2 = zinv.square();
		auto cx = zinv2.mul(p.x);
		
		auto zinv3 = zinv2.mul(zinv);
		auto cy = zinv3.mul(p.y);
		
		this(cx, cy, p.infinity);
	}
	
	this(ComputeElement x, ComputeElement y, bool infinity) {
		this.x = x;
		this.y = y;
		this.infinity = infinity;
	}
	
	this(ComputeElement x, bool parity) {
		auto x2 = x.square();
		auto x3 = x2.mul(x);
		auto y2 = x3.add(ComputeElement(B));
		y = y2.sqrt();
		y = ComputeElement.select(y.isOdd() == parity, y, y.negate());
		this(x, y, false);
	}
	
	auto normalize() const {
		// XXX: in contract
		assert(!infinity);
		return Point(x.normalize(), y.normalize());
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		return CartesianPoint(x, y.negate(), infinity);
	}
	
	// auto opBinary(string op : "+")() const {
	auto add(CartesianPoint b) const {
		return addImpl(this, b);
	}
	
	auto opEquals(CartesianPoint b) const {
		auto xeq = x.opEquals(b.x);
		auto yeq = y.opEquals(b.y);
		
		auto infneq = infinity ^ b.infinity;
		auto coordeq = (xeq & yeq) | infinity;
		
		return coordeq && !infneq;
	}
	
	auto pdouble() const {
		return doubleImpl(this);
	}
	
	auto pdoublen(uint N)() const {
		auto r = pdouble();
		return r.pdoublen!(N - 1)();
	}
	
	static select(bool cond, CartesianPoint a, CartesianPoint b) {
		return CartesianPoint(
			ComputeElement.select(cond, a.x, b.x),
			ComputeElement.select(cond, a.y, b.y),
			// Ternary op doesn't have the right type.
			// FIXME: The compiler is still a smart ass and uses CMOV.
			!!(cond ? a.infinity : b.infinity),
		);
	}
	
	static selectj(bool cond, CartesianPoint a, JacobianPoint b) {
		return JacobianPoint.selectc(cond, a, b);
	}
	
private:
	static addImpl(CartesianPoint a, CartesianPoint b) {
		/**
		 * Cost: 3M, 4S
		 *
		 * This is simply the jacobian formula with Z1 = Z2 = 1.
		 * See the jacobian implementation for details.
		 *
		 * T = X1 + X2
		 * M = Y1 + Y2
		 * R = T^2 - X1*X2
		 * D = M or X1 - X2
		 * N = R or 2*Y1
		 * Q = T * D^2
		 * V = N^2 - Q
		 * XR = 4*V
		 * YM = M * D^3
		 * YR = -4*(N*(V - Q) + YM)
		 * ZR = 2*D
		 *
		 * We cannot use the formula found at
		 *   https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-mmadd-2007-bl
		 *
		 * because it breaks down for point doubling.
		 */
		auto t = a.x.add(b.x);
		
		auto negbx = b.x.negate();
		auto negaxbx = negbx.mul(a.x);
		auto r = negaxbx.add(t.square());
		auto rzero = r.zeroCheck();
		
		auto m = a.y.add(b.y);
		auto mzero = m.zeroCheck();
		
		/**
		 * If r and m are 0 then, y1 == -y2 and x1 ^ 3 == x2 ^ 3 but
		 * x1 != x2. This means that x1 == beta*x2 or beta*x1 == x2,
		 * where beta is a nontrivial cube root of one. In this case,
		 * we use an alterantive expression for lambda and set R/M
		 * accordingly.
		 */
		auto degenerate = rzero && mzero;
		
		// Ralt = Y1 - Y2 => Ralt = 2*Y1 when y1 = -y2.
		auto ralt = a.y.muln!2();
		auto n = ComputeElement.select(degenerate, ralt, r);
		
		// Malt = X1 - X2.
		auto malt = negbx.add(a.x);
		auto d = ComputeElement.select(degenerate, malt, m);
		
		/**
		 * Now N / D = lambda and is guaranteed not to be 0/0.
		 * From here on out N and D represent the numerator
		 * and denominator of lambda; R and M represent the explicit
		 * expressions x1^2 + x2^2 + x1x2 and y1 + y2.
		 */
		
		// Either M == D or M == 0. We leverage this to compute
		// M * D ^ 3 as either D ^ 4 or 0.
		auto d2 = d.square();
		auto d4 = d2.square();
		auto ym = ComputeElement.select(degenerate, ComputeElement(0), d4);
		
		// ZR = 2*D
		auto zr = d.muln!2();
		auto zrzero = zr.zeroCheck();
		
		auto q = d2.mul(t);
		auto negq = q.negate();
		
		// XR = 2*V
		auto n2 = n.square();
		auto v = n2.add(negq);
		auto vdouble = v.muln!2();
		auto xr = v.muln!4();
		
		// And we avoid negating too much by doing
		// YR = -4*(N*(V - Q) + YM)
		auto tmp = n.mul(vdouble.add(negq));
		auto negyrquarter = tmp.add(ym);
		auto yrquarter = negyrquarter.negate();
		auto yr = yrquarter.muln!4();
		
		auto ret = JacobianPoint(xr, yr, zr, zrzero);
		
		// X + infinity = X.
		ret = selectj(a.infinity, b, ret);
		ret = selectj(b.infinity, a, ret);
		return ret;
	}
	
	static doubleImpl(CartesianPoint p) {
		/**
		 * The point at infinity doubles to itself.
		 * See Jacobian point doubling for the details.
		 */
		if (p.infinity && false) {
			return JacobianPoint(p);
		}
		
		/**
		 * Cost: 1M, 5S
		 *
		 * This uses a tweaked version of the formula found at:
		 *   https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-mdbl-2007-bl
		 *
		 * U = X^2
		 * V = Y^2
		 * S = U + V^2 - (X + V)^2
		 * M = 3*U
		 * T = M^2 + 4*S
		 * XR = T
		 * YR = -(M*(T + 2*S) + 8*V^2)
		 * ZR = 2*Y
		 */
		auto u = p.x.square();
		auto m = u.muln!3();
		auto m2 = m.square();
		
		auto zr = p.y.muln!2();
		
		auto v = p.y.square();
		auto v2 = v.square();
		auto tmp0 = v2.add(u);
		auto tmp1 = p.x.add(v);
		auto s = tmp0.sub(tmp1.square());
		
		auto t = m2.add(s.muln!4());
		auto xr = t;
		
		auto tmp2 = m.mul(t.add(s.muln!2()));
		auto negyr = tmp2.add(v2.muln!8());
		auto yr = negyr.negate();
		
		/**
		 * The point at infinity is the only one that doubles to infinity.
		 * See the Jacobian point doubling for more detailed explaination.
		 */
		return JacobianPoint(xr, yr, zr, p.infinity);
	}
}

struct JacobianPoint {
private:
	import crypto.field;
	
	// X = x / z^2
	ComputeElement x;

	// Y = y / z^3
	ComputeElement y;
	
	ComputeElement z;
	bool infinity;
	
public:
	this(Point p) {
		this(CartesianPoint(p));
	}
	
	this(CartesianPoint p) {
		this(p.x, p.y, ComputeElement(1), p.infinity);
	}
	
	this(ComputeElement x, ComputeElement y, ComputeElement z, bool infinity) {
		this.x = x;
		this.y = y;
		this.z = z;
		this.infinity = infinity;
	}
	
	auto normalize() const {
		// XXX: in contract
		assert(!infinity);
		auto p = CartesianPoint(this);
		return p.normalize();
	}
	
	// auto opUnary(string op : "-")() const {
	auto negate() const {
		return JacobianPoint(x, y.negate(), z, infinity);
	}
	
	// auto opBinary(string op : "+")() const {
	auto add(CartesianPoint b) const {
		return addImpl(this, b);
	}
	
	auto pdouble() const {
		return doubleImpl(this);
	}
	
	auto pdoublen(uint N)() const {
		JacobianPoint r = this;
		for (uint i = 0; i < N; i++) {
			r = r.pdouble();
		}
		
		return r;
	}
	
	auto opEquals(CartesianPoint b) const {
		auto z2 = z.square();
		auto scalledBX = z2.mul(b.x);
		auto xeq = x.opEquals(scalledBX);
		
		auto z3 = z.mul(z2);
		auto scalledBY = z3.mul(b.y);
		auto yeq = y.opEquals(scalledBY);
		
		auto infneq = infinity ^ b.infinity;
		auto coordeq = (xeq & yeq) | infinity;
		
		return coordeq && !infneq;
	}
	
	static select(bool cond, JacobianPoint a, JacobianPoint b) {
		return JacobianPoint(
			ComputeElement.select(cond, a.x, b.x),
			ComputeElement.select(cond, a.y, b.y),
			ComputeElement.select(cond, a.z, b.z),
			// Ternary op doesn't have the right type.
			// FIXME: The compiler is still a smart ass and uses CMOV.
			!!(cond ? a.infinity : b.infinity),
		);
	}
	
	// FIXME: This causes SDC to infititely loop when called select.
	static selectc(bool cond, CartesianPoint a, JacobianPoint b) {
		return select(cond, JacobianPoint(a), b);
	}
	
private:
	static addImpl(JacobianPoint a, CartesianPoint b) {
		/**
		 * Cost: 7M, 5S
		 *
		 * Just like libsecp256k1, we are using the following formula:
		 *   U1 = X1*Z2^2
		 *   U2 = X2*Z1^2
		 *   S1 = Y1*Z2^3
		 *   S2 = Y2*Z1^3
		 *   Z = Z1*Z2
		 *   T = U1 + U2
		 *   M = S1 + S2
		 *   R = T^2 - U1*U2
		 *   D = M or U1 - U2
		 *   N = R or 2*S1
		 *   Q = T*D^2
		 *   V = N^2 - Q
		 *   XR = 4*V
		 *   YM = M*D^3
		 *   YR = -4*(N*(V + Q) + YM)
		 *   ZR = 2*D*Z
		 *
		 * Because p is in cartesian coordinates, Z2 = 1.
		 *
		 * This formula is derived from:
		 *    Eric Brier and Marc Joye, Weierstrass
		 *        Elliptic Curves and Side-Channel Attacks.
		 *    In D. Naccache and P. Paillier, Eds.,
		 *        Public Key Cryptography, vol. 2274 of Lecture Notes in
		 *        Computer Science, pages 335-345. Springer-Verlag, 2002.
		 *  we find as solution for a unified addition/doubling formula:
		 *    lambda = ((x1 + x2)^2 - x1 * x2 + a) / (y1 + y2),
		 *        with a = 0 for secp256k1's curve equation.
		 *    x3 = lambda^2 - (x1 + x2)
		 *    2*y3 = lambda * (x1 + x2 - 2 * x3) - (y1 + y2).
		 *
		 * This algorithm break down when either point is infinity
		 * or if y1 = -y2 . If either point is infinity, we just set
		 * the infinity, we conditionally swap.
		 *
		 * If a = -b, we can simply set the infinity flag and ignore
		 * the value computed by the algorithm.
		 *
		 * If y1 = -y2 but x1 != x2 then we do as libsecp256k1. Quoting:
		 *   - If y1 = -y2 but x1 != x2, which does occur thanks to certain
		 *     properties of our curve (specifically, 1 has nontrivial cube
		 *     roots in our field, and the curve equation has no x coefficient)
		 *     then the answer is not infinity but also not given by the above
		 *     equation. In this case, we cmov in place an alternate expression
		 *     for lambda. Specifically (y1 - y2)/(x1 - x2). Where both these
		 *     expressions for lambda are defined, they are equal, and can be
		 *     obtained from each other by multiplication by (y1 + y2)/(y1 + y2)
		 *     then substitution of x^3 + 7 for y^2 (using the curve equation).
		 *     For all pairs of nonzero points (a, b) at least one is defined,
		 *     so this covers everything.
		 */
		auto z2 = a.z.square();
		auto u2 = b.x.mul(z2);
		
		// Z2 = 1 because p is in cartesian coordinates.
		auto u1 = a.x;
		auto t = u1.add(u2);
		
		auto negu2 = u2.negate();
		auto negu1u2 = negu2.mul(u1);
		auto r = negu1u2.add(t.square());
		auto rzero = r.zeroCheck();
		
		auto z3 = a.z.mul(z2);
		auto s2 = b.y.mul(z3);
		
		// Z2 = 1 because p is in cartesian coordinates.
		auto s1 = a.y;
		auto m = s1.add(s2);
		auto mzero = m.zeroCheck();
		
		/**
		 * If r and m are 0 then, y1 == -y2 and x1 ^ 3 == x2 ^ 3 but
		 * x1 != x2. This means that x1 == beta*x2 or beta*x1 == x2,
		 * where beta is a nontrivial cube root of one. In this case,
		 * we use an alterantive expression for lambda and set R/M
		 * accordingly.
		 */
		auto degenerate = rzero && mzero;
		
		// Ralt = s1 - s2 => Ralt = 2*s1 when y1 = -y2.
		auto ralt = s1.muln!2();
		auto n = ComputeElement.select(degenerate, ralt, r);
		
		// Malt = u1 - u2.
		auto malt = negu2.add(u1);
		auto d = ComputeElement.select(degenerate, malt, m);
		
		/**
		 * Now N / D = lambda and is guaranteed not to be 0/0.
		 * From here on out N and D represent the numerator
		 * and denominator of lambda; R and M represent the explicit
		 * expressions x1^2 + x2^2 + x1x2 and y1 + y2.
		 */
		
		// Either M == D or M == 0. We leverage this to compute
		// M * D ^ 3 as either D ^ 4 or 0.
		auto d2 = d.square();
		auto d4 = d2.square();
		auto ym = ComputeElement.select(degenerate, ComputeElement(0), d4);
		
		// ZR = 2*D*Z
		auto twod = d.muln!2();
		auto zr = twod.mul(a.z);
		auto zrzero = zr.zeroCheck();
		
		auto q = d2.mul(t);
		auto negq = q.negate();
		
		// XR = 2*V
		auto n2 = n.square();
		auto v = n2.add(negq);
		auto vdouble = v.muln!2();
		auto xr = v.muln!4();
		
		// And we avoid negating too much by doing
		// YR = -4*(N*(V - Q) + YM)
		auto tmp = n.mul(vdouble.add(negq));
		auto negyrquarter = tmp.add(ym);
		auto yrquarter = negyrquarter.negate();
		auto yr = yrquarter.muln!4();
		
		auto ret = JacobianPoint(xr, yr, zr, zrzero);
		
		// X + infinity = X.
		ret = selectc(a.infinity, b, ret);
		ret = select(b.infinity, a, ret);
		return ret;
	}
	
	static doubleImpl(JacobianPoint p) {
		/**
		 * Cost: 3M, 4S
		 *
		 * Quoting from libsecp256k1:
		 * For secp256k1, 2Q is infinity if and only if Q is infinity.
		 * This is because if 2Q = infinity, Q must equal -Q, or that
		 * Q.y == -(Q.y), or Q.y is 0. For a point on y^2 = x^3 + 7 to have
		 * y=0, x^3 must be -7 mod p. However, -7 has no cube root mod p.
		 *
		 * Having said this, if this function receives a point on a sextic
		 * twist, e.g. by a fault attack, it is possible for y to be 0.
		 * This happens for y^2 = x^3 + 6, since -6 does have a
		 * cube root mod p. For this point, this function will not set
		 * the infinity flag even though the point doubles to infinity,
		 * and the result point will be gibberish (z = 0 but infinity = 0).
		 */
		if (p.infinity && false) {
			// Do this only for the variable-time version.
			return p;
		}
		
		/**
		 * We use a variation of libsecp256k1's formula:
		 *   T = 3*X^2
		 *   U = 2*Y^2
		 *   V = -2*X*Y^2
		 *   XR = T^2 + 4*V
		 *   YR = -(T*(6*V + T^2) + 2*U^2)
		 *   ZR = 2*Y*Z
		 *
		 * Quoting from libsecp256k1:
		 * Note that there is an implementation described at
		 *   https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
		 * which trades a multiply for a square, but in practice this is
		 * actually slower, mainly because it requires more normalizations.
		 */
		auto twoy = p.y.muln!2();
		auto zr = twoy.mul(p.z);
		
		auto x2 = p.x.square();
		auto t = x2.muln!3();
		auto t2 = t.square();
		
		auto y2 = p.y.square();
		auto u = y2.muln!2();
		auto negu = u.negate();
		auto v = negu.mul(p.x);
		auto xr = t2.add(v.muln!4());
		
		auto u2 = u.square();
		auto twou2 = u2.muln!2();
		auto sixv = v.muln!6();
		auto tmp = t.mul(sixv.add(t2));
		auto negyr = tmp.add(twou2);
		auto yr = negyr.negate();
		
		return JacobianPoint(xr, yr, zr, p.infinity);
	}
}

void main() {
	import crypto.field;
	static testConstruct(ComputeElement x, ComputeElement y) {
		auto p = CartesianPoint(x, y, false);
		auto a = CartesianPoint(x, false);
		assert(a.opEquals(p));
		
		auto b = CartesianPoint(x, true);
		assert(b.opEquals(p.negate()));
	}
	
	static getZs() {
		ComputeElement[24] zs;
		
		auto one = ComputeElement(1);
		auto oneinv = one.inverse();
		auto negone = one.negate();
		auto negoneinv = oneinv.negate();
		
		zs[0] = one;
		zs[1] = oneinv;
		zs[2] = negone;
		zs[3] = negoneinv;
		
		auto two = ComputeElement(2);
		auto twoinv = two.inverse();
		auto negtwo = two.negate();
		auto negtwoinv = twoinv.negate();
		
		zs[4] = two;
		zs[5] = twoinv;
		zs[6] = negtwo;
		zs[7] = negtwoinv;
		
		auto sqrt2 = two.sqrt();
		auto sqrt2inv = sqrt2.inverse();
		auto negsqrt2 = sqrt2.negate();
		auto negsqrt2inv = sqrt2inv.negate();
		
		zs[8] = sqrt2;
		zs[9] = sqrt2inv;
		zs[10] = negsqrt2;
		zs[11] = negsqrt2inv;
		
		auto beta = ComputeElement(Beta);
		auto betainv = beta.inverse();
		auto negbeta = beta.negate();
		auto negbetainv = betainv.negate();
		
		zs[12] = beta;
		zs[13] = betainv;
		zs[14] = negbeta;
		zs[15] = negbetainv;

		auto beta2 = beta.square();
		auto beta2inv = betainv.square();
		auto negbeta2 = beta2.negate();
		auto negbeta2inv = beta2inv.negate();
		
		zs[16] = beta2;
		zs[17] = beta2inv;
		zs[18] = negbeta2;
		zs[19] = negbeta2inv;
		
		auto sqrtbeta = beta.sqrt();
		auto sqrtbetainv = sqrtbeta.inverse();
		auto negsqrtbeta = sqrtbeta.negate();
		auto negsqrtbetainv = sqrtbetainv.negate();
		
		zs[20] = sqrtbeta;
		zs[21] = sqrtbetainv;
		zs[22] = negsqrtbeta;
		zs[23] = negsqrtbetainv;
		
		return zs;
	}
	
	static testCAddRound(CartesianPoint a, CartesianPoint b, CartesianPoint r) {
		auto s = a.add(b);
		assert(s.opEquals(r), "a + b = r");
		
		// FIXME: sqrt can't run at compile time.
		// enum Zs = getZs();
		auto testZs = getZs();
		
		foreach (z; testZs) {
			auto z2 = z.square();
			auto jx = z2.mul(a.x);
			
			auto z3 = z2.mul(z);
			auto jy = z3.mul(a.y);
			
			auto ja = JacobianPoint(jx, jy, z, a.infinity);
			auto js = ja.add(b);
			assert(js.opEquals(r), "ja + b = r");
		}
	}
	
	static testCAdd(CartesianPoint a, CartesianPoint b, CartesianPoint r) {
		testCAddRound(a, b, r);
		testCAddRound(b, a, r);
		
		// Make sure we test the infinity cases.
		if (!a.infinity) {
			auto ainf = CartesianPoint(a.x, a.y, true);
			testCAddRound(ainf, b, b);
			testCAddRound(ainf, r, r);
		}
		
		if (!b.infinity) {
			auto binf = CartesianPoint(b.x, b.y, true);
			testCAddRound(binf, a, a);
			testCAddRound(binf, r, r);
		}
	}
	
	static testCDoubleRound(CartesianPoint p, CartesianPoint r) {
		auto dbl = p.pdouble();
		assert(dbl.opEquals(r), "2P = E");
		
		// 2P = P + P
		testCAdd(p, p, r);
		
		// FIXME: sqrt can't run at compile time.
		// enum Zs = getZs();
		auto testZs = getZs();
		
		foreach (z; testZs) {
			auto z2 = z.square();
			auto jx = z2.mul(p.x);
			
			auto z3 = z2.mul(z);
			auto jy = z3.mul(p.y);
			
			auto jp = JacobianPoint(jx, jy, z, p.infinity);
			auto jdbl = jp.pdouble();
			assert(jdbl.opEquals(r), "2P = E");
		}
	}
	
	static testCDouble(CartesianPoint p, CartesianPoint r) {
		testCDoubleRound(p, r);
		
		// Same hold for negated points.
		auto negp = p.negate();
		auto negr = r.negate();
		
		testCDoubleRound(negp, negr);
		
		// A point plus its negation gives the point at infinity.
		testCAdd(p, negp, CartesianPoint(p.x, p.y, true));
		testCAdd(r, negr, CartesianPoint(p.x, p.y, true));
	}
	
	// A few constants.
	auto zero = ComputeElement(0);
	auto one = ComputeElement(1);
	auto negone = one.negate();
	auto two = ComputeElement(2);
	auto negtwo = two.negate();
	auto sqrt2 = two.sqrt();
	
	// Point decompression.
	auto yone = ComputeElement(Element(
		0x4218f20ae6c646b3,
		0x63db68605822fb14,
		0x264ca8d2587fdd6f,
		0xbc750d587e76a7ee,
	));
	
	testConstruct(one, yone);
	
	auto ytwo = ComputeElement(Element(
		0x66fbe727b2ba09e0,
		0x9f5a98d70a5efce8,
		0x424c5fa425bbda1c,
		0x511f860657b8535e,
	));
	
	testConstruct(two, ytwo);
	
	auto ysqrt2 = ComputeElement(Element(
		0xa0baf24408e75b09,
		0xa7d28507c6ace8f4,
		0xcfc8047e5baf5a35,
		0xa534138a52934fa6,
	));
	
	testConstruct(sqrt2, ysqrt2);
	
	// Various point addition and doubling.
	auto inf = CartesianPoint(ysqrt2, ytwo, true);
	testCDouble(inf, inf);
	
	auto pone = CartesianPoint(one, yone, false);
	testCDouble(pone, CartesianPoint(
		ComputeElement(Element(
			0xc7ffffffffffffff,
			0xffffffffffffffff,
			0xffffffffffffffff,
			0xffffffff37fffd03,
		)),
		ComputeElement(Element(
			0x4298c557a7ddcc57,
			0x0e8bf054c4cad9e9,
			0x9f396b3ce19d50f1,
			0xb91c9df4bb00d333,
		)),
		false,
	));
	
	auto ptwo = CartesianPoint(two, ytwo, false);
	testCDouble(ptwo, CartesianPoint(
		ComputeElement(Element(
			0x3333333333333333,
			0x3333333333333333,
			0x3333333333333333,
			0x33333332ffffff3b,
		)),
		ComputeElement(Element(
			0xc6e9b7a0d3c27f39,
			0xdfb73902753408e1,
			0x12ee6785aa33ef54,
			0x23b1b5d93b13a783,
		)),
		false,
	));
	
	auto psqrt2 = CartesianPoint(sqrt2, ysqrt2, false);
	testCDouble(psqrt2, CartesianPoint(
		ComputeElement(Element(
			0x966af1cd3dfb77d4,
			0x0f96c5650b2682e1,
			0x2ef3aeff7b1923e8,
			0x206b0273f562cbde,
		)),
		ComputeElement(Element(
			0x51f7b9a5604af9eb,
			0x336ca16f89987130,
			0x63757df7dbb743b8,
			0xf548c5f419e64adc,
		)),
		false,
	));
	
	// Point addition.
	testCAdd(inf, psqrt2, psqrt2);
	testCAdd(inf, inf, inf);
	
	testCAdd(pone, ptwo, CartesianPoint(
		ComputeElement(Element(
			0x0dc5d279a3db3663,
			0x3618466426f8046c,
			0x14293331ef943334,
			0xff7d5306cea19499,
		)),
		ComputeElement(Element(
			0x503cc79dd5bde7ec,
			0xefc0acaa1b928006,
			0x1dee93ff6f4ab314,
			0x3ea32db7b80c0f24,
		)),
		false,
	));
	
	testCAdd(pone, psqrt2, CartesianPoint(
		ComputeElement(Element(
			0x842c4fb83c941d42,
			0xe735f08112891fb7,
			0xbdbae48eb6ac28c0,
			0x069df23c7093cb70,
		)),
		ComputeElement(Element(
			0x17ecfb8861f453fe,
			0xcde1019c42b45ff0,
			0xff6aa45d5c984676,
			0x4bc5c765597bdc90,
		)),
		false,
	));
	
	testCAdd(ptwo, psqrt2, CartesianPoint(
		ComputeElement(Element(
			0xb8fd0794327e0a4d,
			0x1d64ccace67b4c40,
			0xe3a3aca298704afb,
			0x832f072f083614cf,
		)),
		ComputeElement(Element(
			0x80eaf02401164532,
			0x213892551c3f743a,
			0x0e4d2f5d7f18dc7a,
			0xfc1c8912a4087d3b,
		)),
		false,
	));
	
	/**
	 * These point have different x but y that are opposite of
	 * each others. This is a special in out point addition
	 * routine and we want to make sure it is handled properly.
	 */
	auto ax = ComputeElement(Element(
		0x8d24cd950a355af1,
		0x3c54350544238d30,
		0x0643d79f05a59614,
		0x2f8ec030d58977cb,
	));
	
	auto ay = ComputeElement(Element(
		0xffe1cc85c7f6c232,
		0x93f0c792f4ed6c57,
		0xb28d37862897e6db,
		0xbb192d0b6e6feab2,
	));
	
	auto bx = ComputeElement(Element(
		0xc7b742061f788cd9,
		0xabd0937d164a0d86,
		0x95f6ff75f19a4ce9,
		0xd013bd7bbf92d2a7,
	));
	
	auto by = ComputeElement(Element(
		0x001e337a38093dcd,
		0x6c0f386d0b1293a8,
		0x4d72c879d7681924,
		0x44e6d2f39190117d,
	));
	
	assert(ay.opEquals(by.negate()), "ay == -by");
	
	testConstruct(ax, ay);
	testConstruct(bx, ay);
	
	auto a = CartesianPoint(ax, ay, false);
	auto b = CartesianPoint(bx, by, false);
	
	testCAdd(a, b, CartesianPoint(
		ComputeElement(Element(
			0x671a63c03efdad4c,
			0x389a779824356027,
			0xb3d69010278625c3,
			0x5c86d390184a8f7a,
		)),
		ComputeElement(Element(
			0xa09bf63dd31fe0d4,
			0xaee02c8adaf8e2f7,
			0x259ae7fe8f16a350,
			0x70f276c241270071,
		)),
		false,
	));
	
	printf("OK\n".ptr);
}

module crypto.point;

struct Point {
private:
	import crypto.field;
	Element x;
	Element y;
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
	
	// auto opBinary(string op : "+")() const {
	auto add(CartesianPoint b) const {
		return addImpl(this, b);
	}
	
	auto pdouble() const {
		return doubleImpl(this);
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
		 *   Q = T*M^2
		 *   V = 2*(R^2 - Q)
		 *   XR = 2*V
		 *   YM = M*D^3
		 *   YR = 4*(R*(Q - V) - YM)
		 *   ZR = 2*M*Z
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
		 * the infinty, we conditionally swap.
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
		auto zsquare = a.z.square();
		auto u2 = b.x.mul(zsquare);
		
		// Z2 = 1 because p is in cartesian coordinates.
		auto u1 = a.x;
		auto t = u1.add(u2);
		
		auto negu2 = u2.negate();
		auto negu1u2 = negu2.mul(u1);
		auto r = negu1u2.add(t.square());
		auto rzero = r.propagateAndZeroCheck();
		
		auto zcube = a.z.mul(zsquare);
		auto s2 = b.y.mul(zcube);
		
		// Z2 = 1 because p is in cartesian coordinates.
		auto s1 = a.y;
		auto m = s1.add(s2);
		auto mzero = m.propagateAndZeroCheck();
		
		/**
		 * If r and m are 0 then, y1 == -y2 and x1 ^ 3 == x2 ^ 3 but
		 * x1 != x2. This means that x1 == beta*x2 or beta*x1 == x2,
		 * where beta is a nontrivial cube root of one. In this case,
		 * we use an alterantive expression for lambda and set R/M
		 * accordingly.
		 */
		auto degenerate = rzero && mzero;
		
		// Ralt = s1 - s2 => Ralt = 2*s1 when y& = -y2.
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
		// M * D ^ 3 as either M ^ 4 or 0.
		auto m2 = m.square();
		auto m4 = m2.square();
		auto ym = ComputeElement.select(degenerate, ComputeElement(0), m4);
		
		// ZR = 2*M*Z
		auto twom = m.muln!2();
		auto zr = twom.mul(a.z);
		auto zrzero = zr.propagateAndZeroCheck();
		
		auto q = m2.mul(t);
		auto negq = q.negate();
		
		// XR = 2*V
		auto r2 = r.square();
		auto vhalf = r.add(negq);
		auto v = vhalf.muln!2();
		auto xr = v.muln!2();
		
		// And we avoid negating too much by doing
		// YR = -4*(R*(V - Q) + YM)
		auto tmp = r.mul(v.add(negq));
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
		 * Just like libsecp256k1, we are using the following formula:
		 *   T = 3*X^2
		 *   U = 2*Y^2
		 *   V = 2*X*Y^2
		 *   XR = T^2 - 4*V
		 *   YR = T*(6*V - T^2) - 2*U^2
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
		auto v = u.mul(p.x);
		
		auto xr = t2.sub(v.muln!4());
		
		auto u2 = u.square();
		auto twou2 = u2.muln!2();
		auto sixv = v.muln!6();
		auto tmp = t.mul(sixv.sub(t2));
		auto yr = tmp.sub(twou2);
		
		return JacobianPoint(xr, yr, zr, p.infinity);
	}
}

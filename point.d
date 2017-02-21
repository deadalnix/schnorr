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
		auto z = p.z.inverse();
		auto z2 = z.square();
		auto z3 = z.mul(z2);
		
		this(p.x.mul(z2), p.y.mul(z3), p.infinity);
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
}

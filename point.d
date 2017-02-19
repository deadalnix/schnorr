module crypto.field;

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
}

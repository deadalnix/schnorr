module crypto.capi;

extern(C):

struct Context;

immutable(Context)* crypto_context_create(ubyte[32] nonce);
void crypto_context_destroy(const Context* c);

// We can't expose Scalar and Element as DMD doesn't support ucent.
struct Uint256 {
	ulong[4] parts;
}

/**
 * Parse EC points. Can handle compressed and uncompressed points.
 */
struct Point {
	Uint256 x, y;
}

bool crypto_point_parse(const(ubyte)[] buffer, ref Point p);

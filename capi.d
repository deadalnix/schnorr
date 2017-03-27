module crypto.capi;

extern(C):

// FIXME: make this opaque when possible.
struct Context;

immutable(Context)* crypto_context_create(ubyte[32] nonce);
void crypto_context_destroy(const Context* c);

// We can't expose Scalar and Element as DMD doesn't support ucent.
struct Uint256 {
	ulong[4] parts;
}

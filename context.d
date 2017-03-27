module crypto.context;

struct Context {
private:
	import crypto.generator;
	Generator g;
	
	import crypto.doublegen;
	DoubleGen dblg;
	
public:
	import crypto.point;
	this(Point p, ubyte[32] nonce) {
		g = Generator(p, nonce);
		dblg = DoubleGen(p);
	}
}

extern(C):

void* malloc(size_t);
void free(void*);

Context* crypto_context_create(ubyte[32] nonce) {
	auto c = cast(Context*) malloc(Context.sizeof);
	if (c is null) {
		return null;
	}
	
	import crypto.point;
	c.__ctor(Point.getG(), nonce);
	return c;
}

void crypto_context_destroy(Context* c) {
	free(c);
}

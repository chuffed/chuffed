#ifndef OPCACHE_H_
#define OPCACHE_H_

class OpCache {
public:
	OpCache(unsigned int sz);
	~OpCache();

	unsigned int check(char op, unsigned int a, unsigned int b);  // Returns UINT_MAX on failure.
	void insert(char op, unsigned int a, unsigned int b, unsigned int res);

	struct cache_entry {
		unsigned int hash;
		char op;
		unsigned int a;
		unsigned int b;
		unsigned int res;
	};

private:
	inline unsigned int hash(char op, unsigned int a, unsigned int b) const;

	// Implemented with sparse-array stuff.
	unsigned int tablesz;

	unsigned int members{0};
	unsigned int* indices;
	cache_entry* entries;
};
#endif

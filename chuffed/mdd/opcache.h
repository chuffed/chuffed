#ifndef __OPCACHE_H__
#define __OPCACHE_H__
class OpCache {
public:
	OpCache(unsigned int size);
	~OpCache(void);

	unsigned int check(char op, unsigned int a, unsigned int b);  // Returns UINT_MAX on failure.
	void insert(char op, unsigned int a, unsigned int b, unsigned int res);

	typedef struct {
		unsigned int hash;
		char op;
		unsigned int a;
		unsigned int b;
		unsigned int res;
	} cache_entry;

private:
	inline unsigned int hash(char op, unsigned int a, unsigned int b);

	// Implemented with sparse-array stuff.
	unsigned int tablesz;

	unsigned int members;
	unsigned int* indices;
	cache_entry* entries;
};
#endif

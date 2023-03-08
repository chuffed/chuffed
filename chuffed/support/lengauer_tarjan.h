#include <vector>

class LengauerTarjan {
	/**
	 * Full description of this algorithm can be found in:
	 * @article{Lengauer:1979:FAF:357062.357071,
			author = {Lengauer, Thomas and Tarjan, Robert Endre},
			title = {A Fast Algorithm for Finding Dominators in a Flowgraph},
			journal = {ACM Trans. Program. Lang. Syst.},
			year = {1979},
			url = {http://doi.acm.org/10.1145/357062.357071},
			publisher = {ACM},
		 }
	 */

private:
	int root;
	typedef std::vector<std::vector<int> > vvi_t;
	vvi_t en;
	vvi_t in;
	vvi_t ou;

	std::vector<int> parent;
	std::vector<int> vertex;
	std::vector<int> semi;
	std::vector<int> idom;

	int count;

	std::vector<int> ancestor;
	std::vector<int> label;

	void LINK(int v, int w);
	int EVAL(int v);
	void COMPRESS(int v);

protected:
	virtual void DFS(int v);

public:
	virtual void init();
	virtual void DFS() { DFS(root); };
	virtual void find_doms();
	LengauerTarjan(int r, vvi_t _en, vvi_t _in, vvi_t _ou);
	virtual ~LengauerTarjan();
	virtual void run(int root);
	virtual bool visited_dfs(int u);
	virtual int dominator(int u);
	virtual bool ignore_node(int u);
	virtual bool ignore_edge(int e);
};

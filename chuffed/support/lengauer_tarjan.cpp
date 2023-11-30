#include "chuffed/support/lengauer_tarjan.h"

#include <iostream>
#include <utility>
#include <vector>

std::vector<int> child;
std::vector<int> size_;

std::vector<std::vector<int> > preds;
std::vector<std::vector<int> > succs;

void LengauerTarjan::LINK(int v, int w) { ancestor[w] = v; }

int LengauerTarjan::EVAL(int v) {
	if (ancestor[v] == -1) {
		return v;
	}
	COMPRESS(v);
	return label[v];
}

void LengauerTarjan::COMPRESS(int v) {
	if (ancestor[v] == -1) {
		return;
	}
	if (ancestor[ancestor[v]] != -1) {
		COMPRESS(ancestor[v]);
		if (semi[label[ancestor[v]]] < semi[label[v]]) {
			label[v] = label[ancestor[v]];
		}
		ancestor[v] = ancestor[ancestor[v]];
	}
}

void LengauerTarjan::init() {
	int n = in.size();
	preds = std::vector<std::vector<int> >(n, std::vector<int>());
	succs = std::vector<std::vector<int> >(n, std::vector<int>());
	for (int i = 0; i < n; i++) {
		// succs.push_back(vector<int>());
		// cout <<"Succs of "<<i<<": ";
		for (int j = 0; j < ou[i].size(); j++) {
			int e = ou[i][j];
			if (ignore_edge(e)) {
				continue;
			}
			int o = en[e][1];
			if (ignore_node(o)) {
				continue;
			}
			if (i != en[ou[i][j]][1]) {
				succs[i].push_back(en[ou[i][j]][1]);
				// cout <<en[ou[i][j]][1]<<", ";
			}
		}
		// cout<<endl;
	}

	parent = std::vector<int>(n, -1);
	vertex = std::vector<int>(n, -1);
	semi = std::vector<int>(n, -1);
	idom = std::vector<int>(n, -1);

	count = -1;

	ancestor = std::vector<int>(n, -1);
	label = std::vector<int>(n, -1);

	child = std::vector<int>(n, root);
	size_ = std::vector<int>(n, 0);
}

//*
void LengauerTarjan::DFS(int v) {
	// cout <<"DFS at "<<v<<endl;
	count = count + 1;
	semi[v] = count;
	vertex[count] = v;
	// Init vars for step 3 and 4
	label[v] = v;
	ancestor[v] = -1;
	std::vector<int>::iterator it;
	for (it = succs[v].begin(); it != succs[v].end(); it++) {
		int w = *it;
		if (semi[w] == -1) {
			parent[w] = v;
			DFS(w);
		}
		preds[w].push_back(v);
	}
}

//*/
//* //It is a mistery why this causes a bug in the instance
// complete_15_7_true_152

void LengauerTarjan::find_doms() {
	// for (int i = 0; i < preds.size(); i++) {
	//     cout <<"Preds of "<<i<<": ";
	//     for (int j = 0; j < preds[i].size(); j++) {
	//             cout <<preds[i][j]<<", ";
	//     }
	//     cout<<endl;
	// }
	// cout << "Semi ";
	// for (int i = 0; i < in.size(); i++)
	//     cout <<"("<<i <<","<< semi[i]<<") ";
	// cout<<endl;
	// cout << "vertex ";
	// for (int i = 0; i < in.size(); i++)
	//     cout <<"("<<i <<","<< vertex[i]<<") ";
	// cout<<endl;
	// cout << "label ";
	// for (int i = 0; i < in.size(); i++)
	//     cout <<"("<<i <<","<< label[i]<<") ";
	// cout<<endl;
	// cout << "parent ";
	// for (int i = 0; i < in.size(); i++)
	//     cout <<"("<<i <<","<< parent[i]<<") ";
	// cout<<endl;
	// cout <<"count "<<count<<endl;

	std::vector<std::vector<int> > buckets =
			std::vector<std::vector<int> >(in.size(), std::vector<int>());

	for (int i = count; i >= 1; i--) {
		int w = vertex[i];
		std::vector<int>::iterator it;
		for (it = preds[w].begin(); it != preds[w].end(); it++) {
			int v = *it;
			int u = EVAL(v);
			if (semi[u] < semi[w]) {
				semi[w] = semi[u];
			}
		}
		buckets[vertex[semi[w]]].push_back(w);
		LINK(parent[w], w);
		for (it = buckets[parent[w]].begin(); it != buckets[parent[w]].end(); it++) {
			int v = *it;
			int u = EVAL(v);
			idom[v] = (semi[u] < semi[v]) ? u : parent[w];
		}
		buckets[parent[w]].clear();
	}

	for (int i = 1; i <= count; i++) {
		int w = vertex[i];
		if (idom[w] != vertex[semi[w]]) {
			idom[w] = idom[idom[w]];
		}
	}
	idom[root] = root;

}  //*/

std::vector<int> bucket;
void addToBucket(int buckIdx, int element) {
	if (bucket[buckIdx] == -1) {
		bucket[buckIdx] = element;
	} else {
		int old = bucket[buckIdx];
		bucket[buckIdx] = element;
		bucket[element] = old;
	}
}

/*
// Implementation from Choco3 by cprudhom
void LengauerTarjan::find_doms() {
		int n = count + 1;//in.size();
		bucket = vector<int>(in.size(),-1);
		int w, v, u;
		for (int i = n - 1; i >= 1; i--) {
				w = vertex[i];
				for (unsigned int j = 0; j < in[w].size(); j++) {
						if (ignore_edge(in[w][j]))
								continue;
						v = en[in[w][j]][0];//pred
						if (ignore_node(v))
								continue;
						u = EVAL(v);
						if (semi[u] < semi[w]) {
								semi[w] = semi[u];
						}
				}
				if (vertex[semi[w]] != parent[w]) {
						addToBucket(vertex[semi[w]], w);
				} else {
						idom[w] = parent[w];
				}
				LINK(parent[w], w);
				int oldBI = parent[w];
				v = bucket[oldBI];
				while (v != -1) {
						bucket[oldBI] = -1;
						u = EVAL(v);
						if (semi[u] < semi[v]) {
								idom[v] = u;
						} else {
								idom[v] = parent[w];
						}
						oldBI = v;
						v = bucket[v];
				}
		}
		for (int i = 1; i < n; i++) {
				w = vertex[i];
				if (idom[w] != vertex[semi[w]]) {
						idom[w] = idom[idom[w]];
				}
		}
		idom[root] = root;
}
//*/

LengauerTarjan::LengauerTarjan(int r, vvi_t _en, vvi_t _in, vvi_t _ou)
		: root(r), en(std::move(_en)), in(std::move(_in)), ou(std::move(_ou)) {
	// init();
}

LengauerTarjan::~LengauerTarjan() = default;

void LengauerTarjan::run(int root) {
	init();
	DFS();

	/*for (int i = 0; i <= count; i++) {
		cout << "("<<i<<","<<semi[i] <<") ";
		}
		cout <<endl;
	*/
	find_doms();
	/*
		for (int i = 0; i <= count; i++) {
		cout << "("<<i<<","<<idom[i] <<") ";
		}
		cout <<endl;
	*/
}

bool LengauerTarjan::visited_dfs(int u) { return semi[u] != -1; }

int LengauerTarjan::dominator(int u) { return idom[u]; }

bool LengauerTarjan::ignore_node(int u) {
	// return u==13;
	return false;
}

bool LengauerTarjan::ignore_edge(int e) {
	// return e==3 || e==2 || e==4 || e==5;
	return false;
}

void ex1() {
	int n = 15;
	int e = 16;

	std::vector<std::vector<int> > in(n, std::vector<int>());
	in[12].push_back(2);
	in[12].push_back(1);
	in[13].push_back(10);
	in[13].push_back(13);
	in[13].push_back(3);
	in[13].push_back(5);
	in[14].push_back(9);
	in[14].push_back(7);
	in[14].push_back(0);
	in[14].push_back(4);
	in[8].push_back(12);
	in[8].push_back(6);
	in[0].push_back(8);
	in[0].push_back(11);

	std::vector<std::vector<int> > ou(n, std::vector<int>());
	ou[12].push_back(3);
	ou[12].push_back(0);
	ou[13].push_back(11);
	ou[13].push_back(2);
	ou[13].push_back(4);
	ou[14].push_back(1);
	ou[14].push_back(5);
	ou[14].push_back(6);
	ou[8].push_back(7);
	ou[8].push_back(8);
	ou[0].push_back(9);
	ou[0].push_back(10);

	ou[8].push_back(13);
	ou[13].push_back(12);

	std::vector<std::vector<int> > endnodes(e, std::vector<int>());
	endnodes[0].push_back(12);
	endnodes[0].push_back(14);
	endnodes[1].push_back(14);
	endnodes[1].push_back(12);
	endnodes[2].push_back(13);
	endnodes[2].push_back(12);
	endnodes[3].push_back(12);
	endnodes[3].push_back(13);
	endnodes[4].push_back(13);
	endnodes[4].push_back(14);
	endnodes[5].push_back(14);
	endnodes[5].push_back(13);
	endnodes[6].push_back(14);
	endnodes[6].push_back(8);
	endnodes[7].push_back(8);
	endnodes[7].push_back(14);
	endnodes[8].push_back(8);
	endnodes[8].push_back(0);
	endnodes[9].push_back(0);
	endnodes[9].push_back(14);

	endnodes[10].push_back(0);
	endnodes[10].push_back(13);
	endnodes[11].push_back(13);
	endnodes[11].push_back(0);

	endnodes[12].push_back(13);
	endnodes[12].push_back(8);
	endnodes[13].push_back(8);
	endnodes[13].push_back(13);

	endnodes[14].push_back(10);
	endnodes[14].push_back(11);
	endnodes[15].push_back(11);
	endnodes[15].push_back(10);
	in[10].push_back(15);
	in[11].push_back(14);
	ou[10].push_back(14);
	ou[11].push_back(15);

	LengauerTarjan lt = LengauerTarjan(12, endnodes, in, ou);
	lt.run(12);

	std::vector<bool> vis(in.size(), false);
	for (int i = 0; i < in.size(); i++) {
		std::cout << "(" << i << "," << lt.dominator(i) << ") ";
	}
	std::cout << '\n';
}

/*int main(int argc, char* argv[]) {


		ex1();
		return 0;
}
//*/

/*int main(int argc, char* argv[]) {
		int n = 13;
		int e = 21;

		vector< vector<int> > in(n,vector<int>());
		in[0].push_back(11);
		in[1].push_back(2);
		in[1].push_back(14);
		in[2].push_back(1);
		in[3].push_back(0);
		in[4].push_back(13);
		in[4].push_back(15);
		in[5].push_back(12);
		in[5].push_back(17);
		in[6].push_back(3);
		in[7].push_back(4);
		in[8].push_back(16);
		in[8].push_back(19);
		in[9].push_back(5);
		in[9].push_back(6);
		in[9].push_back(8);
		in[9].push_back(10);
		in[10].push_back(7);
		in[11].push_back(9);
		in[11].push_back(20);
		in[12].push_back(18);

		vector< vector<int> > out(n,vector<int>());
		out[0].push_back(0);
		out[0].push_back(1);
		out[0].push_back(2);
		out[1].push_back(15);
		out[2].push_back(12);
		out[2].push_back(14);
		out[2].push_back(13);
		out[3].push_back(3);
		out[3].push_back(4);
		out[4].push_back(18);
		out[5].push_back(16);
		out[6].push_back(5);
		out[7].push_back(6);
		out[7].push_back(7);
		out[8].push_back(17);
		out[8].push_back(20);
		out[9].push_back(9);
		out[10].push_back(8);
		out[11].push_back(10);
		out[11].push_back(11);
		out[12].push_back(19);


		vector< vector<int> > endnodes(e,vector<int>());

		endnodes[0].push_back(0);
		endnodes[0].push_back(3);
		endnodes[1].push_back(0);
		endnodes[1].push_back(2);
		endnodes[2].push_back(0);
		endnodes[2].push_back(1);
		endnodes[3].push_back(3);
		endnodes[3].push_back(6);
		endnodes[4].push_back(3);
		endnodes[4].push_back(7);
		endnodes[5].push_back(6);
		endnodes[5].push_back(9);
		endnodes[6].push_back(7);
		endnodes[6].push_back(9);
		endnodes[7].push_back(7);
		endnodes[7].push_back(10);
		endnodes[8].push_back(10);
		endnodes[8].push_back(9);
		endnodes[9].push_back(9);
		endnodes[9].push_back(11);
		endnodes[10].push_back(11);
		endnodes[10].push_back(9);
		endnodes[11].push_back(11);
		endnodes[11].push_back(0);
		endnodes[12].push_back(2);
		endnodes[12].push_back(5);
		endnodes[13].push_back(2);
		endnodes[13].push_back(4);
		endnodes[14].push_back(2);
		endnodes[14].push_back(1);
		endnodes[15].push_back(1);
		endnodes[15].push_back(4);
		endnodes[16].push_back(5);
		endnodes[16].push_back(8);
		endnodes[17].push_back(8);
		endnodes[17].push_back(5);
		endnodes[18].push_back(4);
		endnodes[18].push_back(12);
		endnodes[19].push_back(12);
		endnodes[19].push_back(8);
		endnodes[20].push_back(8);
		endnodes[20].push_back(11);


		LengauerTarjan lt = LengauerTarjan(0,endnodes, in, out);
		lt.run(0);


		vector<bool> vis(in.size(),false);
		for (int i = 0; i < in.size(); i++)
				cout <<"("<<i <<","<< lt.dominator(i)<<") ";
		cout<<endl;


		return 0;
}//*/

#ifndef DAGPROPAGATOR_H
#define DAGPROPAGATOR_H

#include "chuffed/globals/dconnected.h"
#include "chuffed/support/trailed_cst_list.h"

class DAGPropagator : public DReachabilityPropagator {
	class TrailedSuccList final : public TrailedConstantAccessList<std::pair<int, int> > {
	public:
		TrailedSuccList(int n) : TrailedConstantAccessList(n) {}
		int key(std::pair<int, int> p) override { return p.first; }
		void print() {
			std::cout << "Size: " << size << '\n';
			;
			std::cout << "Sparse: ";
			for (int i : sparse) {
				std::cout << i << " ";
			}
			std::cout << '\n';

			std::cout << "Dense: ";
			for (auto& i : dense) {
				std::cout << "(" << i.first << "," << i.second << ") ";
			}
			std::cout << '\n';
		}
	};
	class TrailedPredList final : public TrailedConstantAccessList<int> {
	public:
		TrailedPredList(int n) : TrailedConstantAccessList(n) {}
		int key(int p) override { return p; }
		void print() {
			std::cout << "Size: " << size << '\n';
			;
			std::cout << "Sparse: ";
			for (int i : sparse) {
				std::cout << i << " ";
			}
			std::cout << '\n';

			std::cout << "Dense: ";
			for (int i : dense) {
				std::cout << i << " ";
			}
			std::cout << '\n';
		}
	};

	std::vector<TrailedSuccList> succs;
	std::vector<TrailedPredList> preds;

	Tint** reachability;
	void connectTo(int source, int dest);
	inline bool reachable(int source, int dest) {
		return (source == dest || succs[source].get(dest));
		/*if (source == dest)
				return true;
		if (!((reachability[source][dest]>0 && succs[source].get(dest)) ||
					(!reachability[source][dest]>0 && !succs[source].get(dest)))) {
				std::cout <<"Succs of "<<source<<":"<<std::endl;
				succs[source].print();
				std::cout <<source <<" "<<dest<<std::endl;
				assert(false);
		}
		return reachability[source][dest] > 0;*/
		//        return reachability[source][dest/sizeof(int)]
		//            & (1 << sizeof(int) - (dest % sizeof(int)));
	}

	std::vector<bool> processed_e;
	std::vector<bool> processed_n;

	void findPathFromTo(int u, int v, vec<Lit>& path);

	bool check_correctness(int r, std::vector<int>& v);

public:
	DAGPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
								vec<vec<edge_id> >& _out, vec<vec<int> >& _en);

	~DAGPropagator() override;

	bool propagateNewEdge(int e) override;
	bool propagateNewNode(int n) override;

	virtual bool check_cycle(int e);
	virtual bool prevent_cycle(int e);

	bool propagate() override;

	bool checkFinalSatisfied() override;
};

#endif

#ifndef DYNAMICKMEANS_H
#define DYNAMICKMEANS_H

#include <chuffed/support/floyd_warshall.h>

#include <algorithm>
#define MIN(a, b) ((a < b) ? a : b)

template <typename T>
class ClusteringAlgorithm {
protected:
	T clusters_count;

public:
	ClusteringAlgorithm(int k) : clusters_count(k) {}
	virtual int from(int edge_id) = 0;
	virtual int to(int edge_id) = 0;
	virtual int available_edge(int edge_id) = 0;
	virtual int weight(int edge_id) = 0;
	virtual inline int nb_clusters() { return clusters_count; }
	virtual inline void set_nb_clusters(int n) { clusters_count = n; }
	virtual void update_dists() = 0;
	virtual std::vector<int> cluster(std::vector<int> to_cluster) = 0;

	virtual inline std::set<int>& get_cluster(int id) = 0;
	virtual inline int get_centroid(int id) = 0;
	virtual inline std::vector<int> get_centroids() = 0;
	virtual inline int cluster_of(int n) = 0;
};

/**
 * K-means algorithm in graphs (non Euclidian) that can change
 * over time (dynamic). The graph is never given, only queried.
 */
template <typename T>
class DynamicKMeans : public ClusteringAlgorithm<T> {
private:
	class ImplementedFloydWarshall : public FloydWarshall<T> {
		DynamicKMeans* _km;

	public:
		ImplementedFloydWarshall(int n, int e, DynamicKMeans* km) : FloydWarshall<T>(n, e), _km(km) {}

		virtual int from(int edge_id) { return _km->from(edge_id); }
		virtual int to(int edge_id) { return _km->to(edge_id); }
		virtual int exists(int edge_id) { return _km->available_edge(edge_id); }
		virtual int weight(int edge_id) { return _km->weight(edge_id); }
	};

	int n, e;
	std::vector<int> centroids;
	std::vector<std::set<int> > clusters;
	std::map<int, int> cluster_id;
	ImplementedFloydWarshall* fw;

public:
	DynamicKMeans(int k, int _n, int _e) : ClusteringAlgorithm<T>(k), n(_n), e(_e), fw(NULL) {
		fw = new ImplementedFloydWarshall(n, e, this);
	}

	virtual ~DynamicKMeans() { delete fw; }

	inline std::set<int>& get_cluster(int id) { return clusters[id]; }
	inline int get_centroid(int id) { return centroids[id]; }
	inline std::vector<int> get_centroids() { return centroids; }
	inline int cluster_of(int n) { return cluster_id.count(n) > 0 ? -1 : cluster_id[n]; }

	void update_dists() { fw->compute(); }
	std::vector<int> cluster(std::vector<int> to_cluster) {
		srand(time(NULL));
		clusters = std::vector<std::set<int> >(this->clusters_count, std::set<int>());
		centroids = std::vector<int>(this->clusters_count, -1);
		// Special case
		if (this->clusters_count == to_cluster.size()) {
			// Each node a cluster
			for (unsigned int i = 0; i < to_cluster.size(); i++) {
				centroids[i] = to_cluster[i];
				clusters[i].insert(centroids[i]);
			}
			return get_centroids();
		}

		cluster_id.clear();

		// Initialize: randomly choose centroids and cluster IDs
		std::random_shuffle(to_cluster.begin(), to_cluster.end());
		for (unsigned int i = 0; i < this->clusters_count; i++) {
			centroids[i] = to_cluster[i];
			cluster_id[to_cluster[i]] = i;
		}

		clusters = std::vector<std::set<int> >(this->clusters_count, std::set<int>());

		for (unsigned int i = 0; i < to_cluster.size(); i++) {
			int n = to_cluster[i];
			int min = -1;
			int arg_min = -1;
			for (unsigned int j = 0; j < this->clusters_count; j++) {
				int cent = centroids[j];
				int inf = 0, inf2 = 0;
				int d = 0;
				int d1 = fw->getDist(n, cent, &inf);
				int d2 = fw->getDist(cent, n, &inf2);
				if (inf && !inf2)
					d = d2;
				else if (!inf && inf2)
					d = d1;
				else if (!inf && !inf2)
					d = MIN(d1, d2);
				else if (inf && inf2)
					continue;  // Go to another cluster
				if (!inf || !inf2) {
					if (min == -1 || min > d) {
						min = d;
						arg_min = j;
					}
				}
			}
			assert(arg_min != -1);
			cluster_id[n] = arg_min;
			clusters[arg_min].insert(n);
		}

		// Cluster!

		bool changes = true;
		while (changes) {
			changes = false;
			// Choose new centroid for each cluster:
			// The node int he cluster with minimum sum of distances to
			// other nodes in the cluster

			for (unsigned int cl = 0; cl < this->clusters_count; cl++) {
				int min = -1;
				std::set<int>::iterator it;
				for (it = clusters[cl].begin(); it != clusters[cl].end(); ++it) {
					int sum = 0;
					// std::cout<<"it1 "<<*it<<std::endl;
					std::set<int>::iterator it2;
					for (it2 = clusters[cl].begin(); it2 != clusters[cl].end(); ++it2) {
						int inf = 0, inf2 = 0;
						int d1 = fw->getDist(*it, *it2, &inf);
						int d2 = fw->getDist(*it2, *it, &inf2);
						int d = 0;
						assert(!(inf && inf2));
						if (inf && !inf2)
							d = d2;
						else if (!inf && inf2)
							d = d1;
						else if (!inf && !inf2)
							d = MIN(d1, d2);
						else
							sum += d;
					}
					if (sum != -1) {
						if (min == -1 || min > sum) {
							min = sum;
							centroids[cl] = *it;
						}
					}
				}
			}
			/*std::cout<<"Migrating"<<" ";//std::endl;
			for (int cl = 0; cl < this->clusters_count; cl++) {
					std::cout<<centroids[cl]<<" ";
			}
			std::cout<<std::endl;*/
			// Migrate nodes to their appropriate cluster

			clusters = std::vector<std::set<int> >(this->clusters_count, std::set<int>());

			for (unsigned int i = 0; i < to_cluster.size(); i++) {
				int n = to_cluster[i];
				int min = -1;
				int arg_min = -1;
				for (unsigned int j = 0; j < this->clusters_count; j++) {
					int cent = centroids[j];
					int inf = 0, inf2 = 0;
					int d = 0;
					int d1 = fw->getDist(n, cent, &inf);
					int d2 = fw->getDist(cent, n, &inf2);
					if (inf && !inf2)
						d = d2;
					else if (!inf && inf2)
						d = d1;
					else if (!inf && !inf2)
						d = MIN(d1, d2);
					else if (inf && inf2)
						continue;  // Go to another cluster
					if (!inf || !inf2) {
						if (min == -1 || min > d) {
							min = d;
							arg_min = j;
						}
					}
				}
				assert(arg_min != -1);
				if (cluster_id[n] != arg_min) {
					changes |= true;
				}
				cluster_id[n] = arg_min;
				clusters[arg_min].insert(n);
			}

			/*for (int cl = 0; cl < this->clusters_count; cl++) {
					std::cout<<"Cluster "<<cl<<" "<<clusters[cl].size()<<": ";
					std::set<int>::iterator it;
					for (it = clusters[cl].begin(); it != clusters[cl].end(); ++it) {
							std::cout<<*it<<" ";
					}
					std::cout<<"Centroid: "<<centroids[cl]<<std::endl;

					}*/
		}
		return get_centroids();
	}
};

#endif

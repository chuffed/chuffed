#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>

int csplib_capacities[] = {12, 14, 17, 18, 19, 20, 23, 24, 25, 26,
													 27, 28, 29, 30, 32, 35, 39, 42, 43, 44};
int csplib_orders[][2] = {
		{4, 1},   {22, 2},  {9, 3},   {5, 4},   {8, 5},   {3, 6},   {3, 4},   {4, 7},   {7, 4},
		{7, 8},   {3, 6},   {2, 6},   {2, 4},   {8, 9},   {5, 10},  {7, 11},  {4, 7},   {7, 11},
		{5, 10},  {7, 11},  {8, 9},   {3, 1},   {25, 12}, {14, 13}, {3, 6},   {22, 14}, {19, 15},
		{19, 15}, {22, 16}, {22, 17}, {22, 18}, {20, 19}, {22, 20}, {5, 21},  {4, 22},  {10, 23},
		{26, 24}, {17, 25}, {20, 26}, {16, 27}, {10, 28}, {19, 29}, {10, 30}, {10, 31}, {23, 32},
		{22, 33}, {26, 34}, {27, 35}, {22, 36}, {27, 37}, {22, 38}, {22, 39}, {13, 40}, {14, 41},
		{16, 27}, {26, 34}, {26, 42}, {27, 35}, {22, 36}, {20, 43}, {26, 24}, {22, 44}, {13, 45},
		{19, 46}, {20, 47}, {16, 48}, {15, 49}, {17, 50}, {10, 28}, {20, 51}, {5, 52},  {26, 24},
		{19, 53}, {15, 54}, {10, 55}, {10, 56}, {13, 57}, {13, 58}, {13, 59}, {12, 60}, {12, 61},
		{18, 62}, {10, 63}, {18, 64}, {16, 65}, {20, 66}, {12, 67}, {6, 68},  {6, 68},  {15, 69},
		{15, 70}, {15, 70}, {21, 71}, {30, 72}, {30, 73}, {30, 74}, {30, 75}, {23, 76}, {15, 77},
		{15, 78}, {27, 79}, {27, 80}, {27, 81}, {27, 82}, {27, 83}, {27, 84}, {27, 79}, {27, 85},
		{27, 86}, {10, 87}, {3, 88}};

class SteelMill : public Problem {
public:
	// Constants

	vec<int> capacities;  // Allowed capacity of slabs in ascending order
	vec<int> loss_table;  // Load -> Loss table
	int max_cap;          // Maximum capacity
	int max_loss;         // Maximum loss
	int n_colours;        // Number of colours
	int n_orders;         // Number of orders
	int n_slabs;          // Number of slabs
	vec<int> weight;      // weight of ith order
	vec<int> colour;      // colour of ith order

	// Core variables

	vec<IntVar*> x;      // assign to which slab
	vec<IntVar*> load;   // load on ith slab
	vec<IntVar*> loss;   // loss on ith slab
	IntVar* total_loss;  // total loss

	// Intermediate variables

	vec<vec<BoolView> > b_order_slab;    // whether order i is assigned to slab j
	vec<vec<IntVar*> > b2i_order_slab;   // whether order i is assigned to slab j
	vec<vec<IntVar*> > b2i_slab_colour;  // whether slab i is assigned colour j

	SteelMill(int n) : n_colours(88), n_orders(n), n_slabs(n) {
		for (int& csplib_capacitie : csplib_capacities) {
			capacities.push(csplib_capacitie);
		}
		for (int i = 0; i < n_orders; i++) {
			weight.push(csplib_orders[i][0]);
		}
		for (int i = 0; i < n_orders; i++) {
			colour.push(csplib_orders[i][1]);
		}

		max_cap = capacities.last();

		loss_table.growTo(max_cap + 1, 0);
		max_loss = 0;
		for (int j = 1; j < capacities[0]; j++) {
			loss_table[j] = capacities[0] - j;
			if (loss_table[j] > max_loss) {
				max_loss = loss_table[j];
			}
		}
		for (int i = 0; i < capacities.size() - 1; i++) {
			for (int j = capacities[i] + 1; j < capacities[i + 1]; j++) {
				loss_table[j] = capacities[i + 1] - j;
				if (loss_table[j] > max_loss) {
					max_loss = loss_table[j];
				}
			}
		}

		for (int i = 0; i < max_cap; i++) {
			printf("%d ", loss_table[i]);
		}
		printf("\n");

		// Create vars

		createVars(x, n_orders, 0, n_slabs - 1, true);
		createVars(load, n_slabs, 0, max_cap, true);
		createVars(loss, n_slabs, 0, max_loss, true);

		total_loss = newIntVar(0, max_loss * n_slabs);
		total_loss->specialiseToEL();

		createVars(b_order_slab, n_orders, n_slabs);
		createVars(b2i_order_slab, n_orders, n_slabs, 0, 1);
		createVars(b2i_slab_colour, n_slabs, n_colours, 0, 1);

		// Post some constraints

		// Channel constraints for order/slab
		for (int i = 0; i < n_orders; i++) {
			for (int j = 0; j < n_slabs; j++) {
				int_rel_reif(x[i], IRT_EQ, j, b_order_slab[i][j]);
				bool2int(b_order_slab[i][j], b2i_order_slab[i][j]);
			}
		}

		// Channel constraints for slab/colour
		for (int i = 0; i < n_slabs; i++) {
			for (int j = 0; j < n_colours; j++) {
				BoolView t = newBoolVar();
				bool2int(t, b2i_slab_colour[i][j]);
				for (int k = 0; k < n_orders; k++) {
					if (colour[k] != j + 1) {
						continue;
					}
					bool_rel(~b_order_slab[k][i], BRT_OR, t);
				}
			}
		}

		// Packing constraints
		for (int i = 0; i < n_slabs; i++) {
			vec<IntVar*> t;
			for (int j = 0; j < n_orders; j++) {
				t.push(b2i_order_slab[j][i]);
			}
			int_linear(weight, t, IRT_EQ, load[i]);
		}

		// Redundant packing constraint
		int total_weight = 0;
		for (int i = 0; i < n_orders; i++) {
			total_weight += weight[i];
		}
		vec<int> a_slabs(n_slabs, 1);
		int_linear(a_slabs, load, IRT_EQ, total_weight);

		// Color constraints
		vec<int> a_colour(n_colours, 1);
		for (int i = 0; i < n_slabs; i++) {
			int_linear(a_colour, b2i_slab_colour[i], IRT_LE, 2);
		}

		// Compute losses
		for (int i = 0; i < n_slabs; i++) {
			array_int_element(load[i], loss_table, loss[i]);
		}
		int_linear(a_slabs, loss, IRT_LE, total_loss);

		// Post some branchings

		branch(x, VAR_SIZE_MIN, VAL_MIN);

		optimize(total_loss, OPT_MIN);

		// Declare symmetries (optional)

		val_sym_break(x, 0, n_slabs - 1);
	}

	void restrict_learnable() override {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) {
			sat.flags[i] = 0;
		}
		for (int i = 0; i < x.size(); i++) {
			assert(x[i]->getType() == INT_VAR_EL);
			((IntVarEL*)x[i])->setVLearnable();
			((IntVarEL*)x[i])->setVDecidable(true);
		}
	}

	// Function to print out solution

	void print(std::ostream& os) override {
		for (int i = 0; i < n_orders; i++) {
			os << x[i]->getVal() << ", ";
		}
		/*
				for (int i = 0; i < n_slabs; i++) {
					for (int j = 0; j < n_orders; j++) {
						if (x[j]->getVal() != i) continue;
						printf("%d:%d ", weight[j], colour[j]);
					}
					printf("\n");
				}
		*/
		os << "Loss = " << total_loss->getVal() << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	int n;

	assert(argc == 2);
	n = atoi(argv[1]);

	engine.solve(new SteelMill(n));

	return 0;
}

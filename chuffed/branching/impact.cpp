#include <chuffed/branching/impact.h>
#include <chuffed/support/misc.h>
#include <chuffed/support/vec.h>

constexpr double WEIGHT_LOCAL = 420;
constexpr double WEIGHT_GLOBAL = 42;
constexpr double WEIGHT_REPARTITION = 420;
constexpr double CLEARED_LOCAL = 0.42;
constexpr double CLEARED_GLOBAL = 0.042;
constexpr double CLEARED_REPARTITION = 1.00;

double processImpact(vec<int> const& previousSizes, vec<int> const& newSizes) {
	int const n = newSizes.size();
	if ((n == 0) || previousSizes.size() != n) {
		NEVER;
	}

	double local = 0;
	double global = 0;
	int total = 0;
	double repartition = 0;

	for (int i = 0; i < n; ++i) {
		int const ti = previousSizes[i];
		total += ti;
		if (previousSizes[i] == 1) {
			local += CLEARED_LOCAL;
			global += CLEARED_GLOBAL;
			repartition += CLEARED_REPARTITION;
		} else {
			int const fi = ti - newSizes[i];
			if (fi != 0) {
				local += fi / ti;
				global += fi;
				++repartition;
			}
		}
	}
	return (WEIGHT_LOCAL * local / n + WEIGHT_GLOBAL * global / total +
					WEIGHT_REPARTITION * repartition / n) /
				 (WEIGHT_LOCAL + WEIGHT_GLOBAL + WEIGHT_REPARTITION);
}

double solvedImpact(vec<int> const& previousSizes) {
	int const n = previousSizes.size();
	if (n == 0) {
		NEVER;
	}

	double local = 0;
	double global = 0;
	int total = 0;
	double repartition = 0;

	for (int i = 0; i < n; ++i) {
		int const ti = previousSizes[i];
		total += ti;
		if (previousSizes[i] == 1) {
			local += CLEARED_LOCAL;
			global += CLEARED_GLOBAL;
			repartition += CLEARED_REPARTITION;
		} else {
			int const fi = ti - 1;
			if (fi != 0) {
				local += fi / ti;
				global += fi;
				++repartition;
			}
		}
	}
	return (WEIGHT_LOCAL * local / n + WEIGHT_GLOBAL * global / total +
					WEIGHT_REPARTITION * repartition / n) /
				 (WEIGHT_LOCAL + WEIGHT_GLOBAL + WEIGHT_REPARTITION);
}

#include <chuffed/branching/branching.h>
#include <chuffed/vars/vars.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/options.h>

BranchGroup::BranchGroup(VarBranch vb, bool t) :
	var_branch(vb), terminal(t), fin(0), cur(-1) {}

BranchGroup::BranchGroup(vec<Branching*>& _x, VarBranch vb, bool t) :
	x(_x), var_branch(vb), terminal(t), fin(0), cur(-1) {}

bool BranchGroup::finished() {
	if (fin) return true;
	for (int i = 0; i < x.size(); i++) {
		if (!x[i]->finished()) return false;
	}
	fin = 1;
	return true;
}

double BranchGroup::getScore(VarBranch vb) {
	double sum = 0;
	for (int i = 0; i < x.size(); i++) {
		sum += x[i]->getScore(vb);
	}
	return sum / x.size();
}

DecInfo* BranchGroup::branch() {
    // Check whether current branching group has finished,
    // if not yet then continue search on this group
	if (cur >= 0 && !x[cur]->finished()) 
        return x[cur]->branch();

    /* Find the next branching group to branch on */

	// Special case of input order selection
	if (var_branch == VAR_INORDER) {
		int i = 0;
		while (i < x.size() && x[i]->finished()) i++;
		if (i == x.size()) {
			return NULL;
		}
		if (!terminal) cur = i;
		return x[i]->branch();
	}
    // Special case of random order selection
    if (var_branch == VAR_RANDOM) {
        moves.clear();
        for (int i = 0; i < x.size(); i++) {
            if (!x[i]->finished())
                moves.push(i);
        }
        if (moves.size() == 0)
            return NULL;
        int best_i = moves[ rand() % moves.size() ];
        if (!terminal)
            cur = best_i;
        return x[best_i]->branch();
    }

    // All other selection criteria
	double best = -1e100;
	moves.clear();
	for (int i = 0; i < x.size(); i++) {
		if (x[i]->finished()) continue;
		double s = x[i]->getScore(var_branch);
		if (s >= best) {
			if (s > best) {
				best = s;
				moves.clear();
			}
			moves.push(i);
		}
	}
	if (moves.size() == 0) {
		return NULL;
	}
	int best_i = moves[0];
    // Random selection of best move
	if (so.branch_random) best_i = moves[rand()%moves.size()];

	if (!terminal) cur = best_i;
	return x[best_i]->branch();
}

// Creates and adds a branching to the engine
void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
    engine.branching->add(createBranch(x, var_branch, val_branch));
}
// Creates a branching without adding to the engine
BranchGroup* createBranch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
	if (val_branch != VAL_DEFAULT) {
        PreferredVal p;
        switch (val_branch) {
            case VAL_MIN: p = PV_MIN; break;
            case VAL_MAX: p = PV_MAX; break;
            case VAL_MEDIAN: p = PV_MEDIAN; break;
            case VAL_SPLIT_MIN: p = PV_SPLIT_MIN; break;
            case VAL_SPLIT_MAX: p = PV_SPLIT_MAX; break;
            default: CHUFFED_ERROR("The value selection branching is not yet supported\n");
        }
        for (int i = 0; i < x.size(); i++) ((Var*) x[i])->setPreferredVal(p);
    }
	return new BranchGroup(x, var_branch, true);
}


PriorityBranchGroup::PriorityBranchGroup(vec<Branching*>& _x, VarBranch vb) 
    : BranchGroup(_x, vb) {}

bool PriorityBranchGroup::finished() {
	if (fin) return true;
	for (int i = 0; i < annotations.size(); i++) {
		if (!annotations[i]->finished()) return false;
	}
	fin = 1;
	return true;
}

double PriorityBranchGroup::getScore(VarBranch vb) {
	double sum = 0;
	for (int i = 0; i < x.size(); i++) {
		sum += x[i]->getScore(vb);
	}
	return sum / x.size();
}

DecInfo* PriorityBranchGroup::branch() {
    // Check whether the current branching group has finished, 
    // if not yet then continue search with this one
	if (cur >= 0 && !annotations[cur]->finished())
        return annotations[cur]->branch();

    /* Select the next branching group */

    // Special case of input order selection
	if (var_branch == VAR_INORDER) {
		int i = 0;
		while (i < annotations.size() && annotations[i]->finished()) i++;
		if (i == annotations.size()) {
			return NULL;
		}
		if (!terminal) cur = i;
		return annotations[i]->branch();
	}
    // Special case of random order selection
    if (var_branch == VAR_RANDOM) {
        moves.clear();
        for (int i = 0; i < annotations.size(); i++) {
            if (!annotations[i]->finished()) {
                moves.push(i);
            }
        }
        if (moves.size() == 0)
            return NULL;
        int rand_int = rand();
        int index = rand_int % moves.size();

        int best_i = moves[rand() % moves.size()];
        if (!terminal)
            cur = best_i;
        return annotations[best_i]->branch();
    }

    // All other selection strategies
	double best = -1e100;
	moves.clear();
	for (int i = 0; i < annotations.size(); i++) {
		if (annotations[i]->finished()) continue;
		double s = x[i]->getScore(var_branch);
		if (s >= best) {
			if (s > best) {
				best = s;
				moves.clear();
			}
			moves.push(i);
		}
	}
	if (moves.size() == 0) {
		return NULL;
	}
	int best_i = moves[0];
    // Special case of random selection of best moves
	if (so.branch_random) best_i = moves[rand() % moves.size()];

	if (!terminal) cur = best_i;
	return annotations[best_i]->branch();
}

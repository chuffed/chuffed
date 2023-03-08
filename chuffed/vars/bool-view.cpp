#include <chuffed/core/propagator.h>
#include <chuffed/vars/bool-view.h>

void BoolView::attach(Propagator* p, int pos, int eflags) const {
	WatchElem we(p->prop_id, pos);
	if ((eflags & EVENT_L) != 0) {
		sat.watches[2 * v + static_cast<int>(s)].push(we);
	}
	if ((eflags & EVENT_U) != 0) {
		sat.watches[2 * v + (1 - static_cast<int>(s))].push(we);
	}
}

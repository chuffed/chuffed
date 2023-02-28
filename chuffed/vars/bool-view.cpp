#include <chuffed/core/propagator.h>
#include <chuffed/vars/bool-view.h>

void BoolView::attach(Propagator* p, int pos, int eflags) {
	WatchElem we(p->prop_id, pos);
	if (eflags & EVENT_L) sat.watches[2 * v + s].push(we);
	if (eflags & EVENT_U) sat.watches[2 * v + (1 - s)].push(we);
}

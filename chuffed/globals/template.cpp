#include <chuffed/core/propagator.h>

class BinPacking : public Propagator {
public:
	// constant data
	vec<IntView<0> > x;

	// Persistent trailed state

//	...

	// Persistent non-trailed state

//	...

	// Intermediate state

//	...


	BinPacking(vec<IntView<0> >& _x) : x(_x) {
		// set priority
		priority = 2; 
		// attach to var events
		for (int i = 0; i < x.size(); i++) x[i].attach(this, i, EVENT_F);
	}

	void wakeup(int i, int c) {
		pushInQueue();
	}

	bool propagate() {
		return true;
	}

	void clearPropState() {
		in_queue = false;
	}

};

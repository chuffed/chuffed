#include "chuffed/support/union_find.h"

#include "chuffed/core/engine.h"

template <>
UF<Tint>::~UF() {
	// delete[] id;
}

template <>
UFRootInfo<Tint>::~UFRootInfo() {
	// delete[] is_root;
}

template <>
RerootedUnionFind<Tint>::~RerootedUnionFind() {
	// Cannot delete Tints (should use smart pointers?)
	// delete[] parents;
}

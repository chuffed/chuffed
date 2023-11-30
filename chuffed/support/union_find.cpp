#include "chuffed/support/union_find.h"

#include "chuffed/core/engine.h"

template <>
UF<Tint>::~UF() = default;  // delete[] id;

template <>
UFRootInfo<Tint>::~UFRootInfo() = default;  // delete[] is_root;

// Cannot delete Tints (should use smart pointers?)
template <>
RerootedUnionFind<Tint>::~RerootedUnionFind() = default;  // delete[] parents;

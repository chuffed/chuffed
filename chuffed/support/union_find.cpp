#include "union_find.h"
#include <cassert>
#include <vector>
#include <iostream>

using namespace std;

template <>
UF<Tint>::~UF() {
    //delete[] id;
}

template <>
UFRootInfo<Tint>::~UFRootInfo() {
    //delete[] is_root;
}

template <>
RerootedUnionFind<Tint>::~RerootedUnionFind() {
    //Cannot delete Tints (should use smart pointers?)
    //delete[] parents;
}

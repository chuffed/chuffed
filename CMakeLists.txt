cmake_minimum_required (VERSION 2.8.7)

# Use this to make static binaries.
# SET(CMAKE_EXE_LINKER_FLAGS "-static")

if (USE_STDLIBCPP)
  set(LIBCPP libstdc++)
else()
  set(LIBCPP libc++)
endif()

# if(APPLE)
#    SET(CMAKE_OSX_DEPLOYMENT_TARGET "10.7")
#    set(CMAKE_XCODE_ATTRIBUTE_CLANG_CXX_LANGUAGE_STANDARD "c++0x")
#    set(CMAKE_XCODE_ATTRIBUTE_CLANG_CXX_LIBRARY "${LIBCPP}")
# endif(APPLE)

set (CMAKE_CXX_STANDARD 11)

project (chuffed CXX C)

# The version number.
set (chuffed_VERSION_MAJOR 0)
set (chuffed_VERSION_MINOR 9)
set (chuffed_VERSION_PATCH 0)


find_package(Threads)

include_directories("chuffed")

if(EXISTS "${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf")
  include_directories("submodules/cp-profiler-integration/protobuf")
  if (WIN32)
    include_directories("submodules/cp-profiler-integration/protobuf/config_win")
  else()
    include_directories("submodules/cp-profiler-integration/protobuf/config_unix")
  endif()
else()
  message("Configuring without CP Profiler support.")
endif()

include_directories(".")
include_directories(${CMAKE_BINARY_DIR})
if (WIN32)
  add_definitions(-DYY_NO_UNISTD_H)
endif()

add_library(chuffed
chuffed/vars/int-var.cpp
chuffed/vars/int-var-el.cpp
chuffed/vars/modelling.cpp
chuffed/vars/int-var-sl.cpp
chuffed/vars/bool-view.cpp
chuffed/vars/int-var-ll.cpp
chuffed/parallel/master.cpp
chuffed/parallel/slave.cpp
chuffed/ldsb/ldsb.cpp
chuffed/globals/subcircuit.cpp
chuffed/globals/mddglobals.cpp
chuffed/globals/sym-break.cpp
chuffed/globals/linear-bool.cpp
chuffed/globals/linear-bool-decomp.cpp
chuffed/globals/well-founded.cpp
chuffed/globals/circuit.cpp
chuffed/globals/minimum.cpp
chuffed/globals/alldiff.cpp
chuffed/globals/template.cpp
chuffed/globals/directives.cpp
chuffed/globals/cumulative.cpp
chuffed/globals/cumulativeCalendar.cpp
chuffed/globals/disjunctive.cpp
chuffed/globals/regular.cpp
chuffed/globals/lex.cpp
chuffed/globals/table.cpp
chuffed/mdd/MDD.cpp
chuffed/mdd/mdd_prop.cpp
chuffed/mdd/mdd_to_lgraph.cpp
chuffed/mdd/MurmurHash3.cpp
chuffed/mdd/opcache.cpp
chuffed/mdd/weighted_dfa.cpp
chuffed/mdd/wmdd_prop.cpp
chuffed/mip/mip.cpp
chuffed/mip/recalc.cpp
chuffed/mip/simplex.cpp
chuffed/primitives/element.cpp
chuffed/primitives/bool.cpp
chuffed/primitives/linear.cpp
chuffed/primitives/arithmetic.cpp
chuffed/primitives/binary.cpp
chuffed/branching/branching.cpp
chuffed/core/init.cpp
chuffed/core/stats.cpp
chuffed/core/engine.cpp
chuffed/core/options.cpp
chuffed/core/sat.cpp
chuffed/core/conflict.cpp
chuffed/vars/int-var.h
chuffed/vars/vars.h
chuffed/vars/int-var-sl.h
chuffed/vars/int-var-ll.h
chuffed/vars/int-view.h
chuffed/vars/int-var-el.h
chuffed/vars/modelling.h
chuffed/vars/bool-view.h
chuffed/parallel/parallel.h
chuffed/support/BVec.h
chuffed/support/ParseUtils.h
chuffed/support/vec.h
chuffed/support/misc.h
chuffed/support/heap.h
chuffed/support/sparse_set.h
chuffed/ldsb/ldsb.h
chuffed/globals/globals.h
chuffed/globals/mddglobals.h
chuffed/mdd/CFG.h
chuffed/mdd/circ_fns.h
chuffed/mdd/circutil.h
chuffed/mdd/CYK.h
chuffed/mdd/MDD.h
chuffed/mdd/mdd_prop.h
chuffed/mdd/mdd_to_lgraph.h
chuffed/mdd/MurmurHash3.h
chuffed/mdd/opcache.h
chuffed/mdd/opts.h
chuffed/mdd/sorters.h
chuffed/mdd/weighted_dfa.h
chuffed/mdd/wmdd_prop.h
chuffed/mip/mip.h
chuffed/mip/simplex.h
chuffed/primitives/primitives.h
chuffed/branching/branching.h
chuffed/core/sat.h
chuffed/core/engine.h
chuffed/core/sat-types.h
chuffed/core/options.h
chuffed/core/propagator.h
)

if(EXISTS "${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf")
  target_compile_definitions(chuffed PRIVATE HAS_PROFILER)

  target_sources(chuffed PUBLIC
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/connector.cpp
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/message.pb.cpp

    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/compiler/importer.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/compiler/parser.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/descriptor.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/descriptor.pb.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/descriptor_database.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/dynamic_message.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/extension_set.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/extension_set_heavy.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/generated_message_reflection.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/generated_message_util.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/coded_stream.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/gzip_stream.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/printer.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/strtod.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/tokenizer.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/zero_copy_stream.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/zero_copy_stream_impl.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/io/zero_copy_stream_impl_lite.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/message.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/message_lite.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/reflection_ops.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/repeated_field.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/service.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/atomicops_internals_x86_gcc.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/atomicops_internals_x86_msvc.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/common.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/once.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/stringprintf.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/structurally_valid.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/strutil.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/stubs/substitute.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/text_format.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/unknown_field_set.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/wire_format.cc
    ${CMAKE_SOURCE_DIR}/submodules/cp-profiler-integration/protobuf/google/protobuf/wire_format_lite.cc
  )

endif()

add_library(chuffed_fzn
chuffed/flatzinc/parser.tab.cpp
chuffed/flatzinc/registry.cpp
chuffed/flatzinc/flatzinc.cpp
chuffed/flatzinc/lexer.yy.cpp
chuffed/flatzinc/parser.tab.h
chuffed/flatzinc/flatzinc.h
chuffed/flatzinc/ast.h
)

add_executable(fzn_chuffed chuffed/flatzinc/fzn_chuffed.cpp)
target_link_libraries(fzn_chuffed chuffed_fzn chuffed ${CMAKE_THREAD_LIBS_INIT})

# add_custom_target(
#   versionTarget
#   COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tools/update-version.sh ${CMAKE_BINARY_DIR}/version.h
# )
# add_dependencies(fzn_chuffed versionTarget)

INSTALL(TARGETS fzn_chuffed chuffed
  RUNTIME DESTINATION bin
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

MACRO(INSTALL_HEADERS_WITH_DIRECTORY HEADER_LIST)

    FOREACH(HEADER ${${HEADER_LIST}})
        STRING(REGEX MATCH "(.\\\*)\\\[/\\\]" DIR ${HEADER})
        INSTALL(FILES ${HEADER} DESTINATION include/${DIR})
    ENDFOREACH(HEADER)

ENDMACRO(INSTALL_HEADERS_WITH_DIRECTORY)

INSTALL_HEADERS_WITH_DIRECTORY(
chuffed/vars/int-var.h
chuffed/vars/vars.h
chuffed/vars/int-var-sl.h
chuffed/vars/int-var-ll.h
chuffed/vars/int-view.h
chuffed/vars/int-var-el.h
chuffed/vars/modelling.h
chuffed/vars/bool-view.h
chuffed/parallel/parallel.h
chuffed/support/BVec.h
chuffed/support/ParseUtils.h
chuffed/support/vec.h
chuffed/support/misc.h
chuffed/support/heap.h
chuffed/support/sparse_set.h
chuffed/ldsb/ldsb.h
chuffed/globals/globals.h
chuffed/globals/mddglobals.h
chuffed/mdd/CFG.h
chuffed/mdd/circ_fns.h
chuffed/mdd/circutil.h
chuffed/mdd/CYK.h
chuffed/mdd/MDD.h
chuffed/mdd/mdd_prop.h
chuffed/mdd/mdd_to_lgraph.h
chuffed/mdd/MurmurHash3.h
chuffed/mdd/opcache.h
chuffed/mdd/opts.h
chuffed/mdd/sorters.h
chuffed/mdd/weighted_dfa.h
chuffed/mdd/wmdd_prop.h
chuffed/mip/mip.h
chuffed/mip/simplex.h
chuffed/primitives/primitives.h
chuffed/branching/branching.h
chuffed/core/sat.h
chuffed/core/engine.h
chuffed/core/sat-types.h
chuffed/core/options.h
chuffed/core/propagator.h
)

INSTALL(DIRECTORY chuffed DESTINATION include
        PATTERN *.cpp EXCLUDE)

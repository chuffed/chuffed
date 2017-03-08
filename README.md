# Chuffed, a lazy clause generation solver

Geoffrey Chu, Peter J. Stuckey, Andreas Schutt, Thorsten Ehlers, Graeme Gange, Kathryn Francis

Data61, CSIRO, Australia

Department of Computing and Information Systems
University of Melbourne, Australia

## Usage

The easiest way to use Chuffed is as a backend to the [MiniZinc constraint modelling language](http://www.minizinc.org). Compiling Chuffed using the
instructions below will create the `fzn-chuffed` executable that can interpret
MiniZinc's FlatZinc solver language.

You can also use Chuffed directly from C++. Take a look at the files in the
`examples` folder to get started.

## Compilation

Chuffed can be compiled on Windows, macOS and Linux.

#### Prerequisites

You need a recent C++
compiler that supports C++11 (e.g. Microsoft Visual Studio 2013, gcc 4.8, clang), as well as the CMake build tool (at least version 3.1).

#### CMake & Co

To build the `fzn-chuffed` executable:

    mkdir build
    cd build
    cmake ..
    cmake --build .

To build the C++ examples:

    mkdir build
    cd build
    cmake ..
    cmake --build . --target examples

To build a debug or release version use the following command instead of `cmake ..`:

    cmake -DCMAKE_BUILD_TYPE=[Debug|Release] ..

#### Integration with CP Profiler

The [CP Profiler tool](https://github.com/cp-profiler) can be used with Chuffed
to visualise the search trees and analyse the nogoods that Chuffed explores
when solving a problem. In order to enable profiling support, you need to fetch the profiler connection code as a submodule by executing the following command
in the root directory of your local copy of the Chuffed git repository:

    git submodule update --init

After that, you can run `cmake` and compile `fzn-chuffed` as described above.

## Description

Chuffed is a state of the art lazy clause solver designed from the ground up
with lazy clause generation in mind. Lazy clause generation is a hybrid
approach to constraint solving that combines features of finite domain
propagation and Boolean satisfiability. Finite domain propagation is
instrumented to record the reasons for each propagation step. This creates an
implication graph like that built by a SAT solver, which may be used to create
efficient nogoods that record the reasons for failure. These nogoods can be
propagated efficiently using SAT unit propagation technology. The resulting
hybrid system combines some of the advantages of finite domain constraint
programming (high level model and programmable search) with some of the
advantages of SAT solvers (reduced search by nogood creation, and effective
autonomous search using variable activities).

The FD components of Chuffed are very tightly integrated with a SAT solver. For
"small" variables (|D| <= 1000), SAT variables representing [x = v] or [x >= v]
are eagerly created at the start of the problem. Channelling constraints are
natively enforced by the variable objects in order to keep the FD solver and
the SAT solver's view of the domains fully consistent at all times. For "large"
variables (|D| > 1000), the SAT variables are lazily generated as needed. Every
propagator in Chuffed has been instrumented so that all propagation can be
explained by some combination of the literals in the SAT solver. An explanation
is of the form a_1 /\ ... /\ a_n -> d, where a_i represent domain restrictions
which are currently true, and d represents the domain change that is implied.
e.g. Suppose z >= x + y, and we have x >= 3, y >= 2. Then the propagator would
propagate x >= 5 with explanation clause x >= 3 /\ y >= 2 -> z >= 5.

The explanations for each propagation form an implication graph. This allows us
to do three very important things. Firstly, we can derive a nogood to explain
each failure. Such nogoods often allow us to avoid a very large amount of
redundant work, thus producing search trees which are orders of magnitude
smaller. Secondly, nogoods allow us to make informed choices about
non-chronological back-jumping. When no literal from a decision level appears
in the nogood, it is indicative of the fact that the decision made at that
level was completely irrelevant to the search. Thus by back-jumping over such
decisions, we retrospectively avoid making such bad decisions, and hopefully
make good decisions instead which drive the search towards failure. Thirdly, by
analysing the conflict, we can actively gain some information about what good
decision choices are. The Variable State Independent Decaying Sum (VSIDS)
heuristic is an extremely effective search heuristic for SAT problems, and is
also extremely good for a range of CP problems. Each variables has an
associated activity, which is increased whenever the variable is involved in
the conflict. Variables with the highest activity is chosen as the decision
variable at each node. The activities are decayed to reflect the fact that the
set of important variables changes with time.

Although Chuffed implements lazy clause generation, which is cutting edge and
rather complex, the FD parts of Chuffed are relatively simple. In fact, it is
quite minimalistic. Chuffed only supports 3 different propagator priorities.
Chuffed implements a number of global propagators (alldiff, inverse,
minimum, table, regular, mdd, cumulative, disjunctive, circuit, difference). 
It also only supports two kinds of integer variables. Small integer variables 
for which the domain is represented by a byte string.
And large integer variables for which the domain is represented only by its
upper and lower bound (no holes allowed). All boolean variables and boolean
constraints are handled by the builtin SAT solver.

Great pains have been taken to make everything as simple and efficient as
possible. The solver, when run with lazy clause generation disabled, is
somewhat comparable in speed with older versions of Gecode. The overhead from
lazy clause generation ranges from negligible to perhaps around 100%. The
search reduction, however, can reach orders of magnitude on appropriate
problems. Thus lazy clause generation is an extremely important and useful
technology. The theory behind lazy clause generation is described in much
greater detail in various papers.

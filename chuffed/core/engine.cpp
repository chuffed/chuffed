#include <cstdio>
#include <cassert>

#include <fstream>
#include <iostream>
#include <vector>
#include <iterator>
#include <sstream>

#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/mip/mip.h>
#include <chuffed/parallel/parallel.h>
#include <chuffed/ldsb/ldsb.h>

#include <chuffed/flatzinc/flatzinc.h>

#ifdef HAS_PROFILER
#include "submodules/cp-profiler-integration/connector.hh"
#endif

// #include <boost/date_time/posix_time/posix_time.hpp>

#ifdef HAS_PROFILER
using namespace Profiling;
#endif

Engine engine;

uint64_t bit[65];

Tint trail_inc;

int nextnodeid = 0;

#ifdef HAS_PROFILER
Profiling::Connector profilerConnector(6565);
#endif

std::map<IntVar*, string> intVarString;
std::map<BoolView, string> boolVarString;
string mostRecentLabel;

extern std::map<int,string> learntClauseString;
extern std::ofstream learntStatsStream;

std::ofstream node_stream;

#ifdef HAS_PROFILER
bool doProfiling() {
    return so.print_nodes || profilerConnector.connected();
}

void sendNode(Node& node) {
    if (so.print_nodes) {
        if (!node_stream.is_open()) {
            node_stream.open("node-log.csv");
            node_stream << "type,id,restart,parent,alt,children,status,time,label,nogood,block,uses_objective,backjump_distance,decision_level,info\n";
        } 
        node.print(node_stream);
        if (so.debug) {
            node.print(std::cerr);
        }
    }
    node.send();
}
#endif

// nodepath is the sequence of node ids leading from the root to the
// current node (inclusive).
std::vector<int> nodepath;

// altpath is the sequence of alternatives one follows to get from the
// root to the current node.  It is typically one element shorter than
// nodepath.
std::vector<int> altpath;

// decisionLevelTip[i] is the number of elements in nodepath that
// belong to decision level i or above.  For example, in this
// situation:
//
//   nodepath = [0, 1, 7]
//   altpath = [0, 1]
//   decisionLevelTip = [1,3]
//
// we have that decision level 0 contains only node 0, and decision
// level 1 contains nodes 1 and 7.  Since decisionLevelTip[1]=3, if we
// wish to return to decision level 1 via a backjump, we should keep
// the first 3 elements of nodepath.
//
// Note that decisionLevelTip is never shrunk so its size should not
// be depended on.  In other words, there may be elements at the end
// of the vector, past the current decision level, whose values are
// stale and meaningless.
std::vector<int> decisionLevelTip;

// When we rewind after a backjump, should we send the skipped nodes
// to the profiler?
enum RewindStyle {
    REWIND_OMIT_SKIPPED,
    REWIND_SEND_SKIPPED
};

std::string showVector(const std::vector<int>& v) {
    stringstream ss;
    for (int i = 0 ; i < v.size() ; i++) {
        if (i > 0)
            ss << " ";
        ss << v[i];
    }
    return ss.str();
}

std::string showVec(const vec<int>& v) {
    stringstream ss;
    for (int i = 0 ; i < v.size() ; i++) {
        if (i > 0)
            ss << " ";
        ss << v[i];
    }
    return ss.str();
}

// Rewind nodepath and altpath after a backjump.
void rewindPaths(
#ifdef HAS_PROFILER
    Profiling::Connector& profilerConnector,
#endif
    int previousDecisionLevel, int newDecisionLevel, RewindStyle rewindStyle,
    long timestamp
) {
    int currentDecisionLevel;
    switch (rewindStyle) {
    case REWIND_OMIT_SKIPPED:
        nodepath.resize(decisionLevelTip[newDecisionLevel]);
        altpath.resize(decisionLevelTip[newDecisionLevel]-1);
        break;
    case REWIND_SEND_SKIPPED:
#if DEBUG_VERBOSE
        std::cerr << "rewinding to level " << newDecisionLevel << "\n";
        std::cerr << "before, nodepath is: " << showVector(nodepath) << "\n";
        std::cerr << "     and altpath is: " << showVector(altpath) << "\n";
        std::cerr << "       and dlTip is: " << showVector(decisionLevelTip) << "\n";
#endif

        // The tip of the nodepath and altpath lead us to the node
        // that failed.  (That is, the last element of nodepath is the
        // id of the node that failed.)  We first unwind that tip to
        // the next decision level, so that we don't send a "skipped
        // child" for that node or any others at this level.
        nodepath.resize(decisionLevelTip[previousDecisionLevel-1]);
        altpath.resize(decisionLevelTip[previousDecisionLevel-1] - 1);
        currentDecisionLevel = previousDecisionLevel-1;

        // Now walk back through the decision levels, sending a
        // "skipped" node for each child that was never visited.
        while (nodepath.size() > decisionLevelTip[newDecisionLevel]) {
            int nodeid = nextnodeid;
            nextnodeid++;
            int parent = (nodepath.size() == 0) ? (-1) : (nodepath[nodepath.size()-1]);
            int myalt  =  (altpath.size() == 0) ? (-1) : (altpath[altpath.size()-1]);

            // myalt is the alternative that led to the failure; the
            // skipped node is conceptually the next alternative.
            myalt++;
            
#ifdef HAS_PROFILER
            if (doProfiling()) {
              sendNode(profilerConnector
                       .createNode(nodeid, parent, myalt, 0, SKIPPED)
                       .set_restart_id(engine.restart_count)
                       .set_decision_level(currentDecisionLevel)
                       .set_time(timestamp));
            }
#endif
            nodepath.resize(nodepath.size() - 1);
            altpath.resize(altpath.size() - 1);
            currentDecisionLevel--;
        }
#if DEBUG_VERBOSE
        std::cerr << "after, nodepath is: " << showVector(nodepath) << "\n";
        std::cerr << "    and altpath is: " << showVector(altpath) << "\n";
        std::cerr << "       and dlTip is: " << showVector(decisionLevelTip) << "\n";
#endif
        break;
    default:
        abort();
    }
}

Engine::Engine()
    : finished_init(false)
    , problem(NULL)
    , opt_var(NULL)
    , best_sol(-1)
    , last_prop(NULL)

    , start_time(chuffed_clock::now())
    , opt_time(duration::zero())
    , conflicts(0)
    , nodes(1)
    , propagations(0)
    , solutions(0)
    , next_simp_db(0)
    , output_stream(&std::cout)
{
    p_queue.growTo(num_queues);
    for (int i = 0; i < 64; i++) bit[i] = ((long long) 1 << i);
    branching = new BranchGroup();
    mip = new MIP();
}

inline void Engine::newDecisionLevel() {
    trail_inc++;
    if (so.debug) {
        std::cerr << "Engine::newDecisionLevel\n";
        std::cerr << "  trail_lim size is currently " << trail_lim.size() << "\n";
        std::cerr << "  pushing " << trail.size() << " to trail_lim\n";
    }
    trail_lim.push(trail.size());
    if (so.debug) {
        std::cerr << "trail_lim is now: " << showVec(trail_lim) << "\n";
    }
    sat.newDecisionLevel();
    if (so.mip) mip->newDecisionLevel();
    assert(dec_info.size() == decisionLevel());
    peak_depth = max(peak_depth, decisionLevel());
}

inline void Engine::doFixPointStuff() {
    // ask other objects to do fix point things
    for (int i = 0; i < pseudo_props.size(); i++) {
        pseudo_props[i]->doFixPointStuff();
    }
}

inline void Engine::makeDecision(DecInfo& di, int alt) {
    ++nodes;
    altpath.push_back(alt);
    if (di.var) {
#if DEBUG_VERBOSE
        std::cerr << "makeDecision: " << intVarString[(IntVar*)di.var] << " / " << di.val << " (" << alt << ")" << std::endl;
#endif
#ifdef HAS_PROFILER
        if (doProfiling()) {
            std::stringstream ss;
            /* ss << intVarString[(IntVar*)di.var] << " / " << di.val << " (" << alt << ")"; */
            ss << intVarString[(IntVar*)di.var];
            switch (di.type) {
            case 1: ss << "=="; break;
            case 2: ss << ">="; break;
            case 3: ss << "<="; break;
            default: ss << "?="; break;
            }
            ss << di.val;
            mostRecentLabel = ss.str();
        }
#endif
        ((IntVar*) di.var)->set(di.val, di.type ^ alt);
    } else {
#if DEBUG_VERBOSE
        std::cerr << "enqueing SAT literal: " << di.val << "^" << alt << " = " << (di.val ^ alt) << std::endl;
#endif
#ifdef HAS_PROFILER
        if (doProfiling()) {
            std::stringstream ss;
            ss << getLitString(di.val^alt);
            mostRecentLabel = ss.str();
        }
#endif
        sat.enqueue(toLit(di.val ^ alt));
    }
    if (so.ldsb && di.var && di.type == 1) ldsb.processDec(sat.trail.last()[0]);
    //  if (opt_var && di.var == opt_var && ((IntVar*) di.var)->isFixed()) printf("objective = %d\n", ((IntVar*) di.var)->getVal());
}

void optimize(IntVar* v, int t) {
    engine.opt_var = v;
    engine.opt_type = t;
    engine.branching->add(v);
    v->setPreferredVal(t == OPT_MIN ? PV_MIN : PV_MAX);
}

inline bool Engine::constrain() {
    best_sol = opt_var->getVal();
    opt_time = std::chrono::duration_cast<duration>(chuffed_clock::now() - start_time) - init_time;

    sat.btToLevel(0);
    restart_count++;
    nodepath.resize(0);
    altpath.resize(0);
    /* nextnodeid = 0; */
#ifdef HAS_PROFILER
    if (doProfiling()) {
      profilerConnector.restart("chuffed", restart_count);
    }
#endif
  
    if (so.parallel) {
        Lit p = opt_type ? opt_var->getLit(best_sol+1, 2) : opt_var->getLit(best_sol-1, 3);
        vec<Lit> ps;
        ps.push(p);
        Clause *c = Clause_new(ps, true);
        slave.shareClause(*c);
        free(c);
    }

    //  printf("opt_var = %d, opt_type = %d, best_sol = %d\n", opt_var->var_id, opt_type, best_sol);
//  printf("%% opt_var min = %d, opt_var max = %d\n", opt_var->getMin(), opt_var->getMax());

    Lit p = opt_type ? opt_var->getLit(best_sol+1, 2) : opt_var->getLit(best_sol-1, 3);
    assumptions.clear();
    assumptions.push(toInt(p));

    if (so.mip) mip->setObjective(best_sol);

    /* return (opt_type ? opt_var->setMin(best_sol+1) : opt_var->setMax(best_sol-1)); */
    return true;
}

bool Engine::propagate() {
    if (async_fail) {
        async_fail = false;
        assert(!so.lazy || sat.confl);
        return false;
    }

    last_prop = NULL;

 WakeUp:

    if (!sat.consistent() && !sat.propagate()) return false;

    for (int i = 0; i < v_queue.size(); i++) {
        v_queue[i]->wakePropagators();
    }
    v_queue.clear();

    if (sat.confl) return false;

    last_prop = NULL;

    for (int i = 0; i < num_queues; i++) {
        if (p_queue[i].size()) {
            Propagator *p = p_queue[i].last(); p_queue[i].pop();
            propagations++;
            bool ok = p->propagate();
            p->clearPropState();
            if (!ok) return false;
            goto WakeUp;
        }
    }

    return true;
}

// Clear all uncleared intermediate propagation states
void Engine::clearPropState() {
    for (int i = 0; i < v_queue.size(); i++) v_queue[i]->clearPropState();
    v_queue.clear();

    for (int i = 0; i < num_queues; i++) {
        for (int j = 0; j < p_queue[i].size(); j++) p_queue[i][j]->clearPropState();
        p_queue[i].clear();
    }
}

void Engine::btToPos(int pos) {
    for (int i = trail.size(); i-- > pos; ) {
        trail[i].undo();
    }
    trail.resize(pos);
}

void Engine::btToLevel(int level) {
    if (so.debug) {
        std::cerr << "Engine::btToLevel( " << level << ")\n";
    }
    if (decisionLevel() == 0 && level == 0) return;
    assert(decisionLevel() > level);

    btToPos(trail_lim[level]);
    trail_lim.resize(level);
    if (so.debug) {
        std::cerr << "trail_lim is now: " << showVec(trail_lim) << "\n";
    }
    dec_info.resize(level);
}



void Engine::topLevelCleanUp() {
    trail.clear();

    if (so.fd_simplify && propagations >= next_simp_db) simplifyDB();

    sat.topLevelCleanUp();
}

void Engine::simplifyDB() {
    int cost = 0;
    for (int i = 0; i < propagators.size(); i++) {
        cost += propagators[i]->checkSatisfied();
    }
    cost += propagators.size();
    for (int i = 0; i < vars.size(); i++) {
        cost += vars[i]->simplifyWatches();
    }
    cost += vars.size();
    cost *= 10;
    //  printf("simp db cost: %d\n", cost);
    next_simp_db = propagations + cost;
}

void Engine::blockCurrentSol() {
    Clause& c = *Reason_new(outputs.size());
    bool root_failure = true;
    for (int i = 0; i < outputs.size(); i++) {
        Var *v = (Var*) outputs[i];
        if (v->getType() == BOOL_VAR) {
            c[i] = ((BoolView*) outputs[i])->getValLit();
        } else {
            c[i] = ((IntVar*) outputs[i])->getValLit();
        }
        if (!sat.isRootLevel(var(c[i]))) root_failure = false;
        assert(sat.value(c[i]) == l_False);
    }
    if (root_failure) sat.btToLevel(0);
    sat.confl = &c;
}


unsigned int Engine::getRestartLimit(unsigned int i) {
    switch (so.restart_type) {
        case NONE:
            if (i > 1) {
                CHUFFED_ERROR("A restart occurred while using search without restarts");
            }
            return UINT_MAX;
        case CONSTANT:
            return so.restart_scale;
        case LINEAR:
            return i * so.restart_scale;
        case LUBY:
            while (true) {
                unsigned int exp = 0U;
                if (i != 1U) {
                    while ( (i >> (++exp)) > 1U ) {}
                }
                if (i == (1U<<(exp+1))-1) {
                    return static_cast<int>(1UL << exp) * so.restart_scale;
                }
                i=i-(1U<<exp)+1;
            }
        case GEOMETRIC:
            return so.restart_scale * ((int) pow(so.restart_base, i));
        default:
            i = (i+1)/2;
            return (((i-1) & ~i) + 1) * so.restart_scale;
    }
    NEVER;
}

void Engine::toggleVSIDS() {
    if (!so.vsids) {
        vec<Branching*> old_x;
        branching->x.moveTo(old_x);
        branching->add(&sat);
        for (int i = 0; i < old_x.size(); i++) branching->add(old_x[i]);
        branching->fin = 0;
        branching->cur = -1;
        so.vsids = true;
    } else {
        vec<Branching*> old_x;
        branching->x.moveTo(old_x);
        for (int i = 1; i < old_x.size(); i++) branching->add(old_x[i]);
        branching->fin = 0;
        branching->cur = -1;
        so.vsids = false;
    }
}

RESULT Engine::search(const std::string& problemLabel) {
    unsigned int starts = 1;
    unsigned int nof_conflicts = getRestartLimit(starts);
    unsigned int conflictC = 0;

    if (so.print_variable_list) {
        std::ofstream s;
        s.open("variable-list");
        for (auto const & p : intVarString) {
            s << p.second << "\n";
        }
        for (auto const & p : boolVarString) {
            s << p.second << "\n";
        }
    }

    std::stringstream ss;
    for (auto const & p : intVarString) {
        ss << p.second << " ";
    }
    ss << ";";
    for (auto const & p : boolVarString) {
        ss << p.second << " ";
    }
    std::string variableListString = ss.str();

    restart_count = 0;
#ifdef HAS_PROFILER
    if (doProfiling()) {
        profilerConnector.restart(problemLabel, restart_count, variableListString);
    }
#endif
  
    decisionLevelTip.push_back(1);

    /* boost::posix_time::ptime start_time = boost::posix_time::microsec_clock::universal_time(); */

    while (true) {
        if (so.parallel && slave.checkMessages()) return RES_UNK;

        int nodeid = nextnodeid;
        nextnodeid++;
        int parent = (nodepath.size() == 0) ? (-1) : (nodepath[nodepath.size()-1]);
        nodepath.push_back(nodeid);
        int myalt = (altpath.size() == 0) ? (-1) : (altpath[altpath.size()-1]);
#if DEBUG_VERBOSE
        std::cerr << "propagate (";
        for (int i = 0 ; i < nodepath.size() ; i++)
            std::cerr << " " << nodepath[i];
        std::cerr << ")\n";
        std::cerr << "altpath (";
        for (int i = 0 ; i < altpath.size() ; i++)
            std::cerr << " " << altpath[i];
        std::cerr << ")\n";
#endif
        if (decisionLevel() >= decisionLevelTip.size())
            decisionLevelTip.resize(decisionLevel()+1);
        decisionLevelTip[decisionLevel()] = nodepath.size();
#if DEBUG_VERBOSE
        std::cerr << "setting decisionLevelTip[" << decisionLevel() << "] to " << nodepath.size() << "\n";
#endif

        int previousDecisionLevel = decisionLevel();

        bool propResult = propagate();
        /* boost::posix_time::ptime current_time = boost::posix_time::microsec_clock::universal_time(); */
        /* boost::posix_time::time_duration dur = current_time - start_time; */
        long timeus = 0;
        //        long timeus = dur.total_microseconds();
        if (!propResult) {
#if DEBUG_VERBOSE
            std::cerr << "failure\n";
            std::cerr << "createNode(" << nodeid << ", " << parent << ", " << myalt << ", 0, NodeStatus::FAILED)\n";
            std::cerr << "label: " << mostRecentLabel << "\n";
            std::cerr << "restart: " << restart_count << "\n";
#endif
            /* c.createNode(nodeid, parent, myalt, 0, FAILED).set_label(mostRecentLabel).send(); */
            /* mostRecentLabel = ""; */

            clearPropState();

        Conflict:
            conflicts++; conflictC++;

            if (so.time_out > duration(0) && chuffed_clock::now() > time_out) {
                (*output_stream) << "% Time limit exceeded!\n";
                return RES_UNK;
            }

            if (decisionLevel() == 0) {
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, FAILED).set_time(timeus).set_label(mostRecentLabel).set_restart_id(restart_count).set_decision_level(previousDecisionLevel));
                    mostRecentLabel = "";
                }
#endif
                return RES_GUN;
            }
                    

            // Derive learnt clause and perform backjump
            if (so.lazy) {
                std::set<int> contributingNogoods;
                sat.analyze(nodeid, contributingNogoods);
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    std::stringstream ss;
                    for (int i = 0 ; i < sat.out_learnt.size() ; i++)
                        ss << " " << getLitString(toInt(sat.out_learnt[i]));
                    std::stringstream contribString;
                    contribString << "{\"nogoods\":[";
                    for (std::set<int>::const_iterator it = contributingNogoods.begin() ;
                         it != contributingNogoods.end() ;
                         it++) {
                        contribString << (it == contributingNogoods.begin() ? "" : ",") << *it;
                    }
                    contribString << "],";
                    contribString << "\"blocks\":[";
                    // We leave duplicates in the list of blocks, so
                    // that the profiler can make use of them.
                    std::set<int> levels;
                    for (int i = 0 ; i < sat.out_learnt_level.size() ; i++) {
                        int rawLevel = sat.out_learnt_level[i];
                        // We increment the "raw level" by one,
                        // because internally (on the trail) the first
                        // decision level -- that is, after a single
                        // search decision has been made -- is called
                        // zero.  We would rather that it be called
                        // one, to equal the number of decisions made.
                        int adjustedLevel = rawLevel + 1;
                        contribString << ((i==0) ? "" : ",") << adjustedLevel;
                        levels.insert(adjustedLevel);
                    }
                    contribString << "]}";

                    // Calculate block level distance.
                    int bld = levels.size();

                    // Does this nogood involve literals that are
                    // derived from assumption literals?
                    int numAssumptions = assumptions.size();
                    bool usesAssumptions = false;
                    for (int i = 0 ; i < sat.out_learnt_level.size() ; i++) {
                        if (sat.out_learnt_level[i] < numAssumptions) {
                            usesAssumptions = true;
                        }
                    }

                    if (so.debug) {
                        std::cerr << "uses assumptions: " << usesAssumptions << "\n";
                    }

                    int backjumpDistance = previousDecisionLevel - decisionLevel();

                    if (doProfiling()) {
                        sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, FAILED).set_time(timeus).set_label(mostRecentLabel).set_nogood(ss.str()).set_nogood_bld(bld).set_uses_assumptions(usesAssumptions).set_restart_id(restart_count).set_info(contribString.str()).set_backjump_distance(backjumpDistance).set_decision_level(previousDecisionLevel));
                    }
                    mostRecentLabel = "";
#if DEBUG_VERBOSE
                    std::cerr << "after analyze, decisionLevel() is " << decisionLevel() << "\n";
                    std::cerr << "decisionLevelTip:";
                    for (int i = 0 ; i < decisionLevelTip.size() ; i++)
                        std::cerr << " " << decisionLevelTip[i];
                    std::cerr << "\n";
#endif

                    rewindPaths(profilerConnector, previousDecisionLevel, decisionLevel(), (so.send_skipped ? REWIND_SEND_SKIPPED : REWIND_OMIT_SKIPPED), timeus);
                                
                    std::stringstream ss2;
                    /* ss2 << "-> "; */
                    string ls = getLitString(toInt(sat.out_learnt[0]));
                    ss2 << ls;
                    if (ls.size() < 2) {
                        std::cerr << "WARNING: short label for " << toInt(sat.out_learnt[0]) << ": " << ls << "\n";
                    }
                    mostRecentLabel = ss2.str();
                    altpath.push_back(1);
                }
#endif
            }   else {
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, FAILED).set_time(timeus).set_label(mostRecentLabel).set_restart_id(restart_count).set_decision_level(previousDecisionLevel));
                    mostRecentLabel = "";
                }
#endif
                sat.confl = NULL;
                DecInfo& di = dec_info.last();
                sat.btToLevel(decisionLevel()-1);
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    rewindPaths(profilerConnector, previousDecisionLevel, decisionLevel(), (so.send_skipped ? REWIND_SEND_SKIPPED : REWIND_OMIT_SKIPPED), timeus);
                }
#endif
                makeDecision(di, 1);
            }

            if (!so.vsids && !so.toggle_vsids &&  conflictC >= so.switch_to_vsids_after) {
            if (so.restart_scale >= 1000000000) so.restart_scale = 100;
                if (so.verbosity >= 2)
                    std::cerr << "restarting and switching to VSIDS\n";
                sat.btToLevel(0);
                restart_count++;
                nodepath.resize(0);
                altpath.resize(0);
                /* nextnodeid = 0; */
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    profilerConnector.restart("chuffed", restart_count);
                }
#endif
                toggleVSIDS();
            }

        } else {

            if (conflictC >= nof_conflicts) {
                if (so.verbosity >= 2)
                    std::cerr << "restarting due to number of conflicts\n";
                starts++;
                nof_conflicts += getRestartLimit(starts);
                sat.btToLevel(0);
                restart_count++;
                nodepath.resize(0);
                altpath.resize(0);
                /* nextnodeid = 0; */
#ifdef HAS_PROFILER
                if (doProfiling()) {
                    profilerConnector.restart("chuffed", restart_count);
                }
#endif

                sat.confl = NULL;
                if (so.lazy && so.toggle_vsids && (starts % 2 == 1)) toggleVSIDS();
                continue;
            }
            
            if (decisionLevel() == 0) {
                topLevelCleanUp();
                if (opt_var && so.verbosity >= 3) {
                    printf("%% root level bounds on objective: min %d max %d\n", opt_var->getMin(), opt_var->getMax());
                }
            }

            DecInfo *di = NULL;
            
            // Propagate assumptions
            while (decisionLevel() < assumptions.size()) {
                int p = assumptions[decisionLevel()];
                if (sat.value(toLit(p)) == l_True) {
                    // Dummy decision level:
                    assert(sat.trail.last().size() == sat.qhead.last());
                    engine.dec_info.push(DecInfo(NULL, p));
                    newDecisionLevel();
                } else if (sat.value(toLit(p)) == l_False) {
                    return RES_LUN;
                } else {
                    di = new DecInfo(NULL, p);
                    break;
                }
            }

            if (!di) di = branching->branch();

            if (!di) {
                solutions++;
                if (std::stringstream* oss = dynamic_cast<std::stringstream*>(output_stream)) {
                    oss->str("");
                }
                if (so.print_sol) {
                    problem->print(*output_stream);
                    (*output_stream) << "\n----------\n";
                    output_stream->flush();
                }
#if DEBUG_VERBOSE
                std::cerr << "solution\n";
                std::cerr << "createNode(" << nodeid << ", " << parent << ", " << myalt << ", 0, SOLVED)\n";
                std::cerr << "label: " << mostRecentLabel << "\n";
#endif

#ifdef HAS_PROFILER
                if (doProfiling()) {
                    FlatZinc::FlatZincSpace *fzs = dynamic_cast<FlatZinc::FlatZincSpace*>(problem);
                    if (fzs != NULL) {
                        std::stringstream s;
                        fzs->printDomains(s);
                        sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, SOLVED)
                            .set_time(timeus)
                            .set_label(mostRecentLabel)
                            .set_info(s.str())
                            .set_decision_level(previousDecisionLevel)
                            .set_restart_id(restart_count));
                    }
                    else {
                        sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, SOLVED)
                            .set_time(timeus)
                            .set_label(mostRecentLabel)
                            .set_decision_level(previousDecisionLevel)
                            .set_restart_id(restart_count));
                    }
                }
                //FlatZinc::FlatZincSpace *fzs = dynamic_cast<FlatZinc::FlatZincSpace*>(problem);
                //if (fzs != NULL) {
                //    std::stringstream s;
                //    fzs->printDomains(s);
                //    if (doProfiling()) {
                //        sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, SOLVED)
                //               .set_time(timeus)
                //               .set_label(mostRecentLabel)
                //               .set_info(s.str())
                //               .set_decision_level(previousDecisionLevel)
                //               .set_restart_id(restart_count));
                //    }
                //} else {
                //    if (doProfiling()) {
                //        sendNode(profilerConnector.createNode(nodeid, parent, myalt, 0, SOLVED)
                //               .set_time(timeus)
                //               .set_label(mostRecentLabel)
                //               .set_decision_level(previousDecisionLevel)
                //               .set_restart_id(restart_count));
                //    }
                //}
#endif
                                    
                mostRecentLabel = "";
                if (!opt_var) {
                    if (solutions == so.nof_solutions) return RES_SAT;
                    if (so.lazy) blockCurrentSol();
                    goto Conflict;
                }
                if (!constrain()) {
                    return RES_GUN;
                }
                continue;
            }


            engine.dec_info.push(*di);
            newDecisionLevel();

            doFixPointStuff();

#if DEBUG_VERBOSE
            std::cerr << "createNode(" << nodeid << ", " << parent << ", " << myalt << ", 2, NodeStatus::BRANCH)\n";
            std::cerr << "label: " << mostRecentLabel << "\n";
#endif
#ifdef HAS_PROFILER
            if (doProfiling()) {
                string info;
                if (so.send_domains) {
                    FlatZinc::FlatZincSpace* fzs = dynamic_cast<FlatZinc::FlatZincSpace*>(problem);
                    if (fzs != NULL) {
                        info = fzs->getDomainsString();
                    }
                }

                sendNode(profilerConnector.createNode(nodeid, parent, myalt, 2, BRANCH)
                                          .set_time(timeus)
                                          .set_label(mostRecentLabel)
                                          .set_info(info)
                                          .set_decision_level(previousDecisionLevel)
                                          .set_restart_id(restart_count));
                mostRecentLabel = "";
            }
#endif
          
            makeDecision(*di, 0);

            delete di;

        }
    }
}

void Engine::solve(Problem *p, const std::string& problemLabel) {
    problem = p;

    // Setting the random seed
    if (so.rnd_seed == 0) {
        so.rnd_seed = time(0);
    }
    srand(so.rnd_seed);


    init();

    time_out = chuffed_clock::now() + so.time_out;

    init_time = std::chrono::duration_cast<duration>(chuffed_clock::now() - start_time);
    base_memory = memUsed();

#ifdef HAS_PROFILER
    if (so.use_profiler)
        profilerConnector.connect();
#endif

    /* if (so.debug) { */
    /*   for (int i = 0 ; i < 2*sat.nVars() ; i++) { */
    /*     std::cerr << "literal " << i << " is " << litString[i] << "\n"; */
    /*   } */
    /* } */

    if (so.learnt_stats) {
        learntStatsStream.open("learnt-stats.csv");
        learntStatsStream << "id,length,block";
        if (so.learnt_stats_nogood)
            learntStatsStream << ",nogood";
        learntStatsStream << ",rawActivity\n";
    }

    if (!so.parallel) {
        // sequential
        status = search(problemLabel);
        if (status == RES_GUN || status == RES_LUN) {
            if (solutions > 0)
                (*output_stream) << "==========\n";
            else
                (*output_stream) << "=====UNSATISFIABLE=====\n";
        }
    } else {
        // parallel
        if (so.thread_no == -1) master.solve();
        else slave.solve();
        if (so.thread_no == -1 && master.status == RES_GUN) (*output_stream) << "==========\n";
    }

    if (so.learnt_stats) {
        for (int i = 0 ; i < sat.learnts.size() ; i++) {
            Clause& c = *(sat.learnts[i]);
            //        std::cerr << "clausescore," << c.clauseID() << ","
            //        << c.rawActivity() << "\n";
            int id = c.clauseID();
            learntStatsStream << learntClauseString[id];
            learntStatsStream << ",";
            learntStatsStream << c.rawActivity();
            learntStatsStream << "\n";
        }
    }

#ifdef HAS_PROFILER
    profilerConnector.done();
    profilerConnector.disconnect();
#endif

    if (so.verbosity >= 1) printStats();

    if (so.parallel) master.finalizeMPI();
}

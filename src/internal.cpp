#include "internal.hpp"
#include <fstream>  // For file handling
#include <ctime>


namespace CaDiCaL {

/*------------------------------------------------------------------------*/
static Clause external_reason_clause;

Internal::Internal ()
    : mode (SEARCH), unsat (false), iterating (false),
      localsearching (false), lookingahead (false), preprocessing (false),
      protected_reasons (false), force_saved_phase (false),
      searching_lucky_phases (false), stable (false), reported (false),
      external_prop (false), did_external_prop (false),
      external_prop_is_lazy (true), forced_backt_allowed (false),
      private_steps (false), rephased (0), vsize (0), max_var (0),
      clause_id (0), original_id (0), reserved_ids (0), conflict_id (0),
      concluded (false), lrat (false), frat (false), level (0), vals (0),
      score_inc (1.0), scores (this), conflict (0), ignore (0),
      external_reason (&external_reason_clause), newest_clause (0),
      force_no_backtrack (false), from_propagator (false),
      ext_clause_forgettable (false), tainted_literal (0), notified (0),
      probe_reason (0), propagated (0), propagated2 (0), propergated (0),
      best_assigned (0), target_assigned (0), no_conflict_until (0),
      unsat_constraint (false), marked_failed (true), num_assigned (0),
      proof (0), lratbuilder (0), opts (this),
#ifndef QUIET
      profiles (this), force_phase_messages (false),
#endif
      arena (this), prefix ("c "), internal (this), external (0),
      termination_forced (false), vars (this->max_var),
      lits (this->max_var) {
  control.push_back (Level (0, 0));

  // The 'dummy_binary' is used in 'try_to_subsume_clause' to fake a real
  // clause, which then can be used to subsume or strengthen the given
  // clause in one routine for both binary and non binary clauses.  This
  // fake binary clause is always kept non-redundant (and not-moved etc.)
  // due to the following 'memset'.  Only literals will be changed.

  // In a previous version we used local automatic allocated 'Clause' on the
  // stack, which became incompatible with several compilers (see the
  // discussion on flexible array member in 'Clause.cpp').

  size_t bytes = Clause::bytes (2);
  dummy_binary = (Clause *) new char[bytes];
  memset (dummy_binary, 0, bytes);
  dummy_binary->size = 2;
}

Internal::~Internal () {
  // If a memory exception ocurred a profile might still be active.
#ifndef QUIET
#define PROFILE(NAME, LEVEL) \
  if (PROFILE_ACTIVE (NAME)) \
    STOP (NAME);
  PROFILES
#undef PROFILE
#endif
  delete[] (char *) dummy_binary;
  for (const auto &c : clauses)
    delete_clause (c);
  if (proof)
    delete proof;
  if (lratbuilder)
    delete lratbuilder;
  for (auto &tracer : tracers)
    delete tracer;
  for (auto &filetracer : file_tracers)
    delete filetracer;
  for (auto &stattracer : stat_tracers)
    delete stattracer;
  if (vals) {
    vals -= vsize;
    delete[] vals;
  }
}

/*------------------------------------------------------------------------*/

// Values in 'vals' can be accessed in the range '[-max_var,max_var]' that
// is directly by a literal.  This is crucial for performance.  By shifting
// the start of 'vals' appropriately, we achieve that negative offsets from
// the start of 'vals' can be used.  We also need to set both values at
// 'lit' and '-lit' during assignments.  In MiniSAT integer literals are
// encoded, using the least significant bit as negation.  This avoids taking
// the 'abs ()' (as in our solution) and thus also avoids a branch in the
// hot-spot of the solver (clause traversal in propagation).  That solution
// requires another (branch less) negation of the values though and
// debugging is harder since literals occur only encoded in clauses.
// The main draw-back of our solution is that we have to shift the memory
// and access it through negative indices, which looks less clean (but still
// as far I can tell is properly defined C / C++).   You might get a warning
// by static analyzers though.  Clang with '--analyze' thought that this
// idiom would generate a memory leak thus we use the following dummy.

static signed char *ignore_clang_analyze_memory_leak_warning;

void Internal::enlarge_vals (size_t new_vsize) {
  signed char *new_vals;
  const size_t bytes = 2u * new_vsize;
  new_vals = new signed char[bytes]; // g++-4.8 does not like ... { 0 };
  memset (new_vals, 0, bytes);
  ignore_clang_analyze_memory_leak_warning = new_vals;
  new_vals += new_vsize;

  if (vals) {
    memcpy (new_vals - max_var, vals - max_var, 2u * max_var + 1u);
    vals -= vsize;
    delete[] vals;
  } else
    assert (!vsize);
  vals = new_vals;
}

/*------------------------------------------------------------------------*/

template <class T>
static void enlarge_init (vector<T> &v, size_t N, const T &i) {
  if (v.size () < N)
    v.resize (N, i);
}

template <class T> static void enlarge_only (vector<T> &v, size_t N) {
  if (v.size () < N)
    v.resize (N, T ());
}

template <class T> static void enlarge_zero (vector<T> &v, size_t N) {
  enlarge_init (v, N, (const T &) 0);
}

/*------------------------------------------------------------------------*/

void Internal::enlarge (int new_max_var) {
  // New variables can be created that can invoke enlarge anytime (via calls
  // during ipasir-up call-backs), thus assuming (!level) is not correct
  size_t new_vsize = vsize ? 2 * vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var)
    new_vsize *= 2;
  LOG ("enlarge internal size from %zd to new size %zd", vsize, new_vsize);
  // Ordered in the size of allocated memory (larger block first).
  if (lrat || frat)
    enlarge_zero (unit_clauses_idx, 2 * new_vsize);
  enlarge_only (wtab, 2 * new_vsize);
  enlarge_only (vtab, new_vsize);
  enlarge_zero (parents, new_vsize);
  enlarge_only (links, new_vsize);
  enlarge_zero (btab, new_vsize);
  enlarge_zero (gtab, new_vsize);
  enlarge_zero (stab, new_vsize);
  enlarge_init (ptab, 2 * new_vsize, -1);
  enlarge_only (ftab, new_vsize);
  enlarge_vals (new_vsize);
  vsize = new_vsize;
  if (external)
    enlarge_zero (relevanttab, new_vsize);
  const signed char val = opts.phase ? 1 : -1;
  enlarge_init (phases.saved, new_vsize, val);
  enlarge_zero (phases.forced, new_vsize);
  enlarge_zero (phases.target, new_vsize);
  enlarge_zero (phases.best, new_vsize);
  enlarge_zero (phases.prev, new_vsize);
  enlarge_zero (phases.min, new_vsize);
  enlarge_zero (marks, new_vsize);
}

void Internal::init_vars (int new_max_var) {
  if (new_max_var <= max_var)
    return;
  // New variables can be created that can invoke enlarge anytime (via calls
  // during ipasir-up call-backs), thus assuming (!level) is not correct
  LOG ("initializing %d internal variables from %d to %d",
       new_max_var - max_var, max_var + 1, new_max_var);
  if ((size_t) new_max_var >= vsize)
    enlarge (new_max_var);
#ifndef NDEBUG
  for (int64_t i = -new_max_var; i < -max_var; i++)
    assert (!vals[i]);
  for (unsigned i = max_var + 1; i <= (unsigned) new_max_var; i++)
    assert (!vals[i]), assert (!btab[i]), assert (!gtab[i]);
  for (uint64_t i = 2 * ((uint64_t) max_var + 1);
       i <= 2 * (uint64_t) new_max_var + 1; i++)
    assert (ptab[i] == -1);
#endif
  assert (!btab[0]);
  int old_max_var = max_var;
  max_var = new_max_var;
  init_queue (old_max_var, new_max_var);
  init_scores (old_max_var, new_max_var);
  int initialized = new_max_var - old_max_var;
  stats.vars += initialized;
  stats.unused += initialized;
  stats.inactive += initialized;
  LOG ("finished initializing %d internal variables", initialized);
}

void Internal::add_original_lit (int lit) {
  assert (abs (lit) <= max_var);
  if (lit) {
    original.push_back (lit);
  } else {
    const uint64_t id =
        original_id < reserved_ids ? ++original_id : ++clause_id;
    if (proof) {
      // Use the external form of the clause for printing in proof
      // Externalize(internalized literal) != external literal
      assert (!original.size () || !external->eclause.empty ());
      proof->add_external_original_clause (id, false, external->eclause);
    }
    if (internal->opts.check &&
        (internal->opts.checkwitness || internal->opts.checkfailed)) {
      bool forgettable = from_propagator && ext_clause_forgettable;
      if (forgettable && opts.check) {
        assert (!original.size () || !external->eclause.empty ());

        // First integer is the presence-flag (even if the clause is empty)
        external->forgettable_original[id] = {1};

        for (auto const &elit : external->eclause)
          external->forgettable_original[id].push_back (elit);

        LOG (external->eclause,
             "clause added to external forgettable map:");
      }
    }

    add_new_original_clause (id);
    original.clear ();
  }
}

void Internal::finish_added_clause_with_id (uint64_t id, bool restore) {
  if (proof) {
    // Use the external form of the clause for printing in proof
    // Externalize(internalized literal) != external literal
    assert (!original.size () || !external->eclause.empty ());
    proof->add_external_original_clause (id, false, external->eclause,
                                         restore);
  }
  add_new_original_clause (id);
  original.clear ();
}

/*------------------------------------------------------------------------*/

void Internal::reserve_ids (int number) {
  // return;
  LOG ("reserving %d ids", number);
  assert (number >= 0);
  assert (!clause_id && !reserved_ids && !original_id);
  clause_id = reserved_ids = number;
  if (proof)
    proof->begin_proof (reserved_ids);
}

/*------------------------------------------------------------------------*/

// This is the main CDCL loop with interleaved inprocessing.

int Internal::cdcl_loop_with_inprocessing () {

  int res = 0;

  START (search);

  if (stable) {
    START (stable);
    report ('[');
  } else {
    START (unstable);
    report ('{');
  }

  while (!res) {
    if (unsat)
      res = 20;
    else if (unsat_constraint)
      res = 20;
    else if (!propagate ())
      analyze (); // propagate and analyze
    else if (iterating)
      iterate ();                               // report learned unit
    else if (!external_propagate () || unsat) { // external propagation
      if (unsat)
        continue;
      else
        analyze ();
    } else if (satisfied ()) { // found model
      if (!external_check_solution () || unsat) {
        if (unsat)
          continue;
        else
          analyze ();
      } else if (satisfied ())
        res = 10;
    } else if (search_limits_hit ())
      break;                               // decision or conflict limit
    else if (terminated_asynchronously ()) // externally terminated
      break;
    else if (restarting ())
      restart (); // restart by backtracking
    else if (rephasing ())
      rephase (); // reset variable phases
    else if (reducing ())
      reduce (); // collect useless clauses
    else if (probing ())
      probe (); // failed literal probing
    else if (subsuming ())
      subsume (); // subsumption algorithm
    else if (eliminating ())
      elim (); // variable elimination
    else if (compacting ())
      compact (); // collect variables
    else if (conditioning ())
      condition (); // globally blocked clauses
    else
      res = decide (); // next decision
  }

  if (stable) {
    STOP (stable);
    report (']');
  } else {
    STOP (unstable);
    report ('}');
  }

  STOP (search);

  return res;
}

int Internal::propagate_assumptions () {
  if (proof)
    proof->solve_query ();
  if (opts.ilb) {
    if (opts.ilbassumptions)
      sort_and_reuse_assumptions ();
    stats.ilbtriggers++;
    stats.ilbsuccess += (level > 0);
    stats.levelsreused += level;
    if (level) {
      assert (control.size () > 1);
      stats.literalsreused += num_assigned - control[1].trail;
    }
  }
  init_search_limits ();
  init_report_limits ();

  int res = already_solved (); // root-level propagation is done here

  int last_assumption_level = assumptions.size ();
  if (constraint.size ())
    last_assumption_level++;

  if (!res) {
    restore_clauses ();
    while (!res) {
      if (unsat)
        res = 20;
      else if (unsat_constraint)
        res = 20;
      else if (!propagate ()) {
        // let analyze run to get failed assumptions
        analyze ();
      } else if (!external_propagate () || unsat) { // external propagation
        if (unsat)
          continue;
        else
          analyze ();
      } else if (satisfied ()) { // found model
        if (!external_check_solution () || unsat) {
          if (unsat)
            continue;
          else
            analyze ();
        } else if (satisfied ())
          res = 10;
      } else if (search_limits_hit ())
        break;                               // decision or conflict limit
      else if (terminated_asynchronously ()) // externally terminated
        break;
      else {
        if (level >= last_assumption_level)
          break;
        res = decide ();
      }
    }
  }

  if (unsat || unsat_constraint)
    res = 20;

  if (!res && satisfied ())
    res = 10;

  finalize (res);
  reset_solving ();
  report_solving (res);

  return res;
}

void Internal::get_entrailed_literals (std::vector<int> &entrailed) {

  for (size_t i = 0; i < trail.size (); i++)
    entrailed.push_back (trail[i]);
}

/*------------------------------------------------------------------------*/

// Most of the limits are only initialized in the first 'solve' call and
// increased as in a stand-alone non-incremental SAT call except for those
// explicitly marked as being reset below.

void Internal::init_report_limits () {
  reported = false;
  lim.report = 0;
}

void Internal::init_preprocessing_limits () {

  const bool incremental = lim.initialized;
  if (incremental)
    LOG ("reinitializing preprocessing limits incrementally");
  else
    LOG ("initializing preprocessing limits and increments");

  const char *mode = 0;

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.subsume = stats.conflicts + scale (opts.subsumeint);
    mode = "initial";
  }
  (void) mode;
  LOG ("%s subsume limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.subsume, lim.subsume - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    last.elim.marked = -1;
    lim.elim = stats.conflicts + scale (opts.elimint);
    mode = "initial";
  }
  (void) mode;
  LOG ("%s elim limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.elim, lim.elim - stats.conflicts);

  // Initialize and reset elimination bounds in any case.

  lim.elimbound = opts.elimboundmin;
  LOG ("elimination bound %" PRId64 "", lim.elimbound);

  /*----------------------------------------------------------------------*/

  if (!incremental) {

    last.ternary.marked = -1; // TODO explain why this is necessary.

    lim.compact = stats.conflicts + opts.compactint;
    LOG ("initial compact limit %" PRId64 " increment %" PRId64 "",
         lim.compact, lim.compact - stats.conflicts);
  }

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.probe = stats.conflicts + opts.probeint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s probe limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.probe, lim.probe - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.condition = stats.conflicts + opts.conditionint;
    mode = "initial";
  }
  LOG ("%s condition limit %" PRId64 " increment %" PRId64, mode,
       lim.condition, lim.condition - stats.conflicts);

  /*----------------------------------------------------------------------*/

  // Initial preprocessing rounds.

  if (inc.preprocessing <= 0) {
    lim.preprocessing = 0;
    LOG ("no preprocessing");
  } else {
    lim.preprocessing = inc.preprocessing;
    LOG ("limiting to %" PRId64 " preprocessing rounds", lim.preprocessing);
  }
}

void Internal::init_search_limits () {

  const bool incremental = lim.initialized;
  if (incremental)
    LOG ("reinitializing search limits incrementally");
  else
    LOG ("initializing search limits and increments");

  const char *mode = 0;

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    last.reduce.conflicts = -1;
    lim.reduce = stats.conflicts + opts.reduceint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s reduce limit %" PRId64 " after %" PRId64 " conflicts", mode,
       lim.reduce, lim.reduce - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (incremental)
    mode = "keeping";
  else {
    lim.flush = opts.flushint;
    inc.flush = opts.flushint;
    mode = "initial";
  }
  (void) mode;
  LOG ("%s flush limit %" PRId64 " interval %" PRId64 "", mode, lim.flush,
       inc.flush);

  /*----------------------------------------------------------------------*/

  // Initialize or reset 'rephase' limits in any case.

  lim.rephase = stats.conflicts + opts.rephaseint;
  lim.rephased[0] = lim.rephased[1] = 0;
  LOG ("new rephase limit %" PRId64 " after %" PRId64 " conflicts",
       lim.rephase, lim.rephase - stats.conflicts);

  /*----------------------------------------------------------------------*/

  // Initialize or reset 'restart' limits in any case.

  lim.restart = stats.conflicts + opts.restartint;
  LOG ("new restart limit %" PRId64 " increment %" PRId64 "", lim.restart,
       lim.restart - stats.conflicts);

  /*----------------------------------------------------------------------*/

  if (!incremental) {
    stable = opts.stabilize && opts.stabilizeonly;
    if (stable)
      LOG ("starting in always forced stable phase");
    else
      LOG ("starting in default non-stable phase");
    init_averages ();
  } else if (opts.stabilize && opts.stabilizeonly) {
    LOG ("keeping always forced stable phase");
    assert (stable);
  } else if (stable) {
    LOG ("switching back to default non-stable phase");
    stable = false;
    swap_averages ();
  } else
    LOG ("keeping non-stable phase");

  inc.stabilize = opts.stabilizeint;
  lim.stabilize = stats.conflicts + inc.stabilize;
  LOG ("new stabilize limit %" PRId64 " after %" PRId64 " conflicts",
       lim.stabilize, inc.stabilize);

  if (opts.stabilize && opts.reluctant) {
    LOG ("new restart reluctant doubling sequence period %d",
         opts.reluctant);
    reluctant.enable (opts.reluctant, opts.reluctantmax);
  } else
    reluctant.disable ();

  /*----------------------------------------------------------------------*/

  // Conflict and decision limits.

  if (inc.conflicts < 0) {
    lim.conflicts = -1;
    LOG ("no limit on conflicts");
  } else {
    lim.conflicts = stats.conflicts + inc.conflicts;
    LOG ("conflict limit after %" PRId64 " conflicts at %" PRId64
         " conflicts",
         inc.conflicts, lim.conflicts);
  }

  if (inc.decisions < 0) {
    lim.decisions = -1;
    LOG ("no limit on decisions");
  } else {
    lim.decisions = stats.decisions + inc.decisions;
    LOG ("conflict limit after %" PRId64 " decisions at %" PRId64
         " decisions",
         inc.decisions, lim.decisions);
  }

  /*----------------------------------------------------------------------*/

  // Initial preprocessing rounds.

  if (inc.localsearch <= 0) {
    lim.localsearch = 0;
    LOG ("no local search");
  } else {
    lim.localsearch = inc.localsearch;
    LOG ("limiting to %" PRId64 " local search rounds", lim.localsearch);
  }

  /*----------------------------------------------------------------------*/

  lim.initialized = true;
}

/*------------------------------------------------------------------------*/

bool Internal::preprocess_round (int round) {
  (void) round;
  if (unsat)
    return false;
  if (!max_var)
    return false;
  START (preprocess);
  struct {
    int64_t vars, clauses;
  } before, after;
  before.vars = active ();
  before.clauses = stats.current.irredundant;
  stats.preprocessings++;
  assert (!preprocessing);
  preprocessing = true;
  PHASE ("preprocessing", stats.preprocessings,
         "starting round %d with %" PRId64 " variables and %" PRId64
         " clauses",
         round, before.vars, before.clauses);
  int old_elimbound = lim.elimbound;
  if (opts.probe)
    probe (false);
  if (opts.elim)
    elim (false);
  if (opts.condition)
    condition (false);
  after.vars = active ();
  after.clauses = stats.current.irredundant;
  assert (preprocessing);
  preprocessing = false;
  PHASE ("preprocessing", stats.preprocessings,
         "finished round %d with %" PRId64 " variables and %" PRId64
         " clauses",
         round, after.vars, after.clauses);
  STOP (preprocess);
  report ('P');
  if (unsat)
    return false;
  if (after.vars < before.vars)
    return true;
  if (old_elimbound < lim.elimbound)
    return true;
  return false;
}

int Internal::preprocess () {
  for (int i = 0; i < lim.preprocessing; i++)
    if (!preprocess_round (i))
      break;
  if (unsat)
    return 20;
  return 0;
}

// gets all of the touched literals based on the current assignment
// this heuristic is described in PreLearn paper
vector<int> Internal::get_touched_literals () {
  if (!opts.globaltouch){
    std::vector<int> literals;
    for (int i = 1; i <= max_var; ++i) {
        literals.push_back(i);
    }
    return literals;
  }
  vector<int> touched_literals;
  for (auto &c : clauses) {
    bool clause_touched = false;
    bool clause_satisfied = false;
    vector<int> variables_to_consider;
    for (auto l : *c) {
      if (val (l) > 0) {
        clause_satisfied = true;
        break;
      } else if (val (l) < 0) {
        clause_touched = true;
      } else if (!getbit (l, 1) && !(Internal::flags (l).status == Flags::FIXED)) {
          variables_to_consider.push_back(l);
      }
    }
    if (clause_touched && !clause_satisfied) {
      for (auto l : variables_to_consider) {
          touched_literals.push_back(l);
          setbit (l, 1);
      }
    }
  }
  for (auto l : touched_literals) {
    unsetbit (l, 1);
  }

  return touched_literals;
}


// sort the literals by the number of clauses they appear in
// maybe there is a faster way to do this with occs, but unclear to me how occs gets poulated
vector<int> Internal::get_sorted_literals () {
  vector<int> sorted_literals;
  vector<pair<int, int>> lit_counts; // pair of (literal, count)
  
  // Initialize counts for all variables
  for (int i = 1; i <= max_var; ++i) {
    if (!active(i)) continue; // Skip inactive variables
    lit_counts.push_back({i, 0});
  }
  
  // Count occurrences in all clauses
  for (const auto &c : clauses) {
    if (c->garbage) continue; // Skip garbage clauses
    
    for (const auto &lit : *c) {
      int var = abs(lit);
      if (!active(var)) continue; // Skip inactive variables
      
      // Find the variable in our counts
      for (auto &p : lit_counts) {
        if (p.first == var) {
          p.second++;
          break;
        }
      }
    }
  }
  
  // Sort by count in descending order
  sort(lit_counts.begin(), lit_counts.end(), 
       [](const pair<int,int>& a, const pair<int,int>& b) {
         return a.second > b.second;
       });
  // Extract sorted literals
  // printf("we have the sorted literals");
  for (const auto& p : lit_counts) {
    // printf("%d (%d) ", p.first, p.second);
    sorted_literals.push_back(p.first);
  }
  // printf("\n");
  return sorted_literals;
}

// chessboard heuristics
int Internal::global_preprocess_chess () {
  START (global_preprocess);

  globalmarks.resize (2 * max_var + 1);

  for (int i = 0; i < globalmarks.size (); i++) {
    globalmarks[i] = 0;
  }

  std::ofstream outFile;
  char* filename = getenv("CADICAL_FILENAME");
  outFile.open (filename);
  if (!outFile) {
      error ("Error: File could not be created.");
  }
  std::ofstream outFile_pr;
  std::string filename_pr = filename;  // Implicit conversion
  filename_pr += "_pr";

  outFile_pr.open (filename_pr);
  if (!outFile_pr) {
      error ("Error: File could not be created.");
  }
  double original_time = time ();

  vector<pair<vector<int>, vector<int>>> asses = {
    {{1, 10}, {-92, -91}},
    {{2, 11}, {-93, -92}},
    {{3, 12}, {-94, -93}},
    {{4, 13}, {-95, -94}},
    {{5, 14}, {-96, -95}},
    {{6, 15}, {-96, -97}},
    {{16, 7}, {-98, -97}},
    {{8, 17}, {-99, -98}},
    {{9, 18}, {-100, -99}},
    {{10, 19}, {-102, -101}},
    {{11, 20}, {-103, -102}},
    {{12, 21}, {-104, -103}},
    {{13, 22}, {-104, -105}},
    {{14, 23}, {-106, -105}},
    {{24, 15}, {-107, -106}},
    {{16, 25}, {-108, -107}},
    {{17, 26}, {-109, -108}},
    {{18, 27}, {-110, -109}},
    {{19, 28}, {-112, -111}},
    {{20, 29}, {-112, -113}},
    {{21, 30}, {-114, -113}},
    {{22, 31}, {-115, -114}},
    {{32, 23}, {-116, -115}},
    {{24, 33}, {-117, -116}},
    {{25, 34}, {-118, -117}},
    {{26, 35}, {-119, -118}},
    {{27, 36}, {-120, -119}},
    {{28, 37}, {-122, -121}},
    {{29, 38}, {-123, -122}},
    {{30, 39}, {-124, -123}},
    {{40, 31}, {-125, -124}},
    {{32, 41}, {-126, -125}},
    {{33, 42}, {-127, -126}},
    {{34, 43}, {-128, -127}},
    {{35, 44}, {-128, -129}},
    {{36, 45}, {-130, -129}},
    {{37, 46}, {-132, -131}},
    {{38, 47}, {-133, -132}},
    {{48, 39}, {-134, -133}},
    {{40, 49}, {-135, -134}},
    {{41, 50}, {-136, -135}},
    {{42, 51}, {-136, -137}},
    {{43, 52}, {-138, -137}},
    {{44, 53}, {-139, -138}},
    {{45, 54}, {-140, -139}},
    {{46, 55}, {-142, -141}},
    {{56, 47}, {-143, -142}},
    {{48, 57}, {-144, -143}},
    {{49, 58}, {-144, -145}},
    {{50, 59}, {-146, -145}},
    {{51, 60}, {-147, -146}},
    {{52, 61}, {-148, -147}},
    {{53, 62}, {-149, -148}},
    {{54, 63}, {-150, -149}},
    {{64, 55}, {-152, -151}},
    {{56, 65}, {-152, -153}},
    {{57, 66}, {-154, -153}},
    {{58, 67}, {-155, -154}},
    {{59, 68}, {-156, -155}},
    {{60, 69}, {-157, -156}},
    {{61, 70}, {-158, -157}},
    {{62, 71}, {-159, -158}},
    {{72, 63}, {-160, -159}},
    {{64, 73}, {-162, -161}},
    {{65, 74}, {-163, -162}},
    {{66, 75}, {-164, -163}},
    {{67, 76}, {-165, -164}},
    {{68, 77}, {-166, -165}},
    {{69, 78}, {-167, -166}},
    {{70, 79}, {-168, -167}},
    {{80, 71}, {-168, -169}},
    {{72, 81}, {-170, -169}},
    {{73, 82}, {-172, -171}},
    {{74, 83}, {-173, -172}},
    {{75, 84}, {-174, -173}},
    {{76, 85}, {-175, -174}},
    {{77, 86}, {-176, -175}},
    {{78, 87}, {-176, -177}},
    {{88, 79}, {-178, -177}},
    {{80, 89}, {-179, -178}},
    {{81, 90}, {-180, -179}},
    {{8, 17, 100}, {-18, -98, -9}},
    {{17, 26, 110}, {-108, -27, -18}},
    {{120, 26, 35}, {-118, -36, -27}},
    {{130, 35, 44}, {-128, -45, -36}},
    {{140, 44, 53}, {-54, -45, -138}},
    {{150, 53, 62}, {-63, -54, -148}},
    {{160, 62, 71}, {-72, -63, -158}},
    {{80, 170, 71}, {-168, -72, -81}},
    {{80, 89, 180}, {-90, -178, -81}},
    {{16, 9, 18, 7}, {-8, -17, -100, -97}},
    {{16, 99, 7}, {-8, -17, -97}},
    {{16, 25, 18, 27}, {-110, -107, -26, -17}},
    {{16, 25, 109}, {-107, -26, -17}},
    {{25, 34, 27, 36}, {-120, -117, -35, -26}},
    {{25, 34, 119}, {-117, -35, -26}},
    {{34, 43, 36, 45}, {-127, -44, -35, -130}},
    {{129, 34, 43}, {-127, -44, -35}},
    {{43, 52, 45, 54}, {-140, -53, -44, -137}},
    {{43, 52, 139}, {-53, -44, -137}},
    {{52, 61, 54, 63}, {-62, -53, -147, -150}},
    {{52, 61, 149}, {-62, -53, -147}},
    {{72, 61, 70, 63}, {-160, -71, -62, -157}},
    {{61, 70, 159}, {-71, -62, -157}},
    {{72, 81, 70, 79}, {-80, -167, -71, -170}},
    {{169, 70, 79}, {-80, -167, -71}},
    {{88, 81, 90, 79}, {-80, -89, -180, -177}},
    {{88, 179, 79}, {-80, -89, -177}},
    {{100, 6, 8, 15, 17}, {-96, -18, -16, -9, -7}},
    {{8, 17, 6, 15}, {-96, -7, -99, -16}},
    {{98, 6, 15}, {-96, -7, -16}},
    {{110, 15, 17, 24, 26}, {-27, -25, -18, -16, -106}},
    {{24, 17, 26, 15}, {-16, -109, -106, -25}},
    {{24, 108, 15}, {-16, -106, -25}},
    {{33, 35, 24, 26, 120}, {-27, -25, -116, -36, -34}},
    {{24, 33, 26, 35}, {-119, -116, -34, -25}},
    {{24, 33, 118}, {-116, -34, -25}},
    {{33, 130, 35, 42, 44}, {-126, -45, -43, -36, -34}},
    {{33, 42, 35, 44}, {-126, -43, -34, -129}},
    {{128, 33, 42}, {-126, -43, -34}},
    {{42, 140, 44, 51, 53}, {-54, -52, -45, -43, -136}},
    {{42, 51, 44, 53}, {-136, -139, -52, -43}},
    {{42, 51, 138}, {-136, -52, -43}},
    {{51, 53, 150, 60, 62}, {-63, -61, -54, -52, -146}},
    {{51, 60, 53, 62}, {-61, -52, -146, -149}},
    {{148, 51, 60}, {-61, -52, -146}},
    {{160, 69, 71, 60, 62}, {-63, -61, -156, -72, -70}},
    {{60, 69, 62, 71}, {-159, -70, -61, -156}},
    {{60, 69, 158}, {-70, -61, -156}},
    {{69, 71, 170, 78, 80}, {-81, -79, -72, -70, -166}},
    {{80, 69, 78, 71}, {-70, -79, -166, -169}},
    {{168, 69, 78}, {-70, -79, -166}},
    {{78, 80, 180, 87, 89}, {-90, -88, -81, -176, -79}},
    {{80, 89, 78, 87}, {-176, -79, -179, -88}},
    {{178, 78, 87}, {-176, -79, -88}},
    {{5, 7, 9, 14, 16, 18}, {-95, -17, -15, -8, -6, -100}},
    {{99, 5, 7, 14, 16}, {-95, -17, -15, -8, -6}},
    {{16, 5, 14, 7}, {-95, -6, -15, -98}},
    {{97, 5, 14}, {-95, -6, -15}},
    {{14, 16, 18, 23, 25, 27}, {-26, -24, -17, -15, -110, -105}},
    {{109, 14, 16, 23, 25}, {-26, -24, -17, -15, -105}},
    {{16, 25, 14, 23}, {-24, -15, -108, -105}},
    {{107, 14, 23}, {-24, -15, -105}},
    {{32, 34, 36, 23, 25, 27}, {-26, -24, -120, -115, -35, -33}},
    {{32, 34, 23, 119, 25}, {-26, -24, -115, -35, -33}},
    {{32, 25, 34, 23}, {-24, -118, -115, -33}},
    {{32, 117, 23}, {-24, -115, -33}},
    {{32, 34, 36, 41, 43, 45}, {-125, -44, -42, -35, -130, -33}},
    {{32, 129, 34, 41, 43}, {-125, -44, -42, -35, -33}},
    {{32, 41, 34, 43}, {-128, -125, -42, -33}},
    {{32, 41, 127}, {-125, -42, -33}},
    {{41, 43, 45, 50, 52, 54}, {-53, -51, -44, -140, -42, -135}},
    {{41, 43, 139, 50, 52}, {-53, -51, -44, -42, -135}},
    {{41, 50, 43, 52}, {-135, -138, -51, -42}},
    {{41, 50, 137}, {-135, -51, -42}},
    {{50, 52, 54, 59, 61, 63}, {-62, -60, -150, -53, -51, -145}},
    {{50, 52, 149, 59, 61}, {-62, -60, -53, -51, -145}},
    {{50, 59, 52, 61}, {-148, -60, -51, -145}},
    {{50, 59, 147}, {-60, -51, -145}},
    {{68, 70, 72, 59, 61, 63}, {-160, -62, -60, -155, -71, -69}},
    {{68, 70, 59, 61, 159}, {-62, -60, -155, -71, -69}},
    {{59, 68, 61, 70}, {-158, -69, -60, -155}},
    {{59, 68, 157}, {-69, -60, -155}},
    {{68, 70, 72, 77, 79, 81}, {-69, -80, -78, -170, -71, -165}},
    {{68, 70, 169, 77, 79}, {-69, -80, -78, -71, -165}},
    {{68, 77, 70, 79}, {-168, -78, -165, -69}},
    {{68, 77, 167}, {-78, -165, -69}},
    {{77, 79, 81, 86, 88, 90}, {-89, -87, -180, -80, -175, -78}},
    {{77, 79, 179, 86, 88}, {-89, -87, -80, -175, -78}},
    {{88, 77, 86, 79}, {-175, -78, -87, -178}},
    {{177, 77, 86}, {-175, -78, -87}},
    {{4, 100, 6, 8, 13, 15, 17}, {-94, -18, -16, -14, -9, -7, -5}},
    {{4, 6, 8, 13, 15, 17}, {-94, -16, -14, -7, -5, -99}},
    {{98, 4, 6, 13, 15}, {-94, -16, -14, -7, -5}},
    {{4, 13, 6, 15}, {-14, -94, -5, -97}},
    {{96, 4, 13}, {-14, -94, -5}},
    {{13, 110, 15, 17, 22, 24, 26}, {-27, -25, -23, -18, -16, -14, -104}},
    {{13, 15, 17, 22, 24, 26}, {-25, -23, -16, -14, -109, -104}},
    {{108, 13, 15, 22, 24}, {-25, -23, -16, -14, -104}},
    {{24, 13, 22, 15}, {-104, -23, -14, -107}},
    {{106, 13, 22}, {-104, -23, -14}},
    {{33, 35, 22, 24, 26, 120, 31}, {-32, -27, -25, -23, -114, -36, -34}},
    {{33, 35, 22, 24, 26, 31}, {-32, -25, -23, -119, -114, -34}},
    {{33, 118, 22, 24, 31}, {-32, -25, -23, -114, -34}},
    {{24, 33, 22, 31}, {-32, -23, -117, -114}},
    {{116, 22, 31}, {-32, -23, -114}},
    {{33, 130, 35, 40, 42, 44, 31}, {-32, -124, -45, -43, -41, -36, -34}},
    {{33, 35, 40, 42, 44, 31}, {-32, -124, -43, -41, -34, -129}},
    {{128, 33, 40, 42, 31}, {-32, -124, -43, -41, -34}},
    {{40, 33, 42, 31}, {-32, -127, -124, -41}},
    {{40, 126, 31}, {-32, -124, -41}},
    {{40, 42, 44, 140, 49, 51, 53}, {-54, -52, -50, -45, -43, -41, -134}},
    {{40, 42, 44, 49, 51, 53}, {-52, -50, -43, -139, -41, -134}},
    {{40, 42, 138, 49, 51}, {-52, -50, -43, -41, -134}},
    {{40, 49, 42, 51}, {-134, -137, -50, -41}},
    {{40, 49, 136}, {-134, -50, -41}},
    {{49, 51, 53, 150, 58, 60, 62}, {-63, -61, -59, -54, -52, -50, -144}},
    {{49, 51, 53, 58, 60, 62}, {-61, -59, -149, -52, -50, -144}},
    {{49, 51, 148, 58, 60}, {-61, -59, -52, -50, -144}},
    {{49, 58, 51, 60}, {-144, -147, -59, -50}},
    {{49, 58, 146}, {-144, -59, -50}},
    {{160, 67, 69, 71, 58, 60, 62}, {-63, -61, -59, -154, -72, -70, -68}},
    {{67, 69, 71, 58, 60, 62}, {-159, -61, -59, -154, -70, -68}},
    {{67, 69, 58, 60, 158}, {-61, -59, -154, -70, -68}},
    {{58, 67, 60, 69}, {-157, -68, -59, -154}},
    {{58, 67, 156}, {-68, -59, -154}},
    {{67, 69, 71, 170, 76, 78, 80}, {-164, -81, -79, -77, -72, -70, -68}},
    {{67, 69, 71, 76, 78, 80}, {-164, -79, -77, -169, -70, -68}},
    {{67, 69, 168, 76, 78}, {-164, -79, -77, -70, -68}},
    {{67, 76, 69, 78}, {-167, -68, -77, -164}},
    {{67, 76, 166}, {-68, -77, -164}},
    {{76, 78, 80, 180, 85, 87, 89}, {-90, -88, -86, -81, -79, -174, -77}},
    {{76, 78, 80, 85, 87, 89}, {-88, -86, -179, -79, -174, -77}},
    {{76, 78, 178, 85, 87}, {-88, -86, -79, -174, -77}},
    {{76, 85, 78, 87}, {-86, -174, -77, -177}},
    {{176, 76, 85}, {-86, -174, -77}},
    {{3, 5, 7, 9, 12, 14, 16, 18}, {-93, -100, -17, -15, -13, -8, -6, -4}},
    {{3, 99, 5, 7, 12, 14, 16}, {-93, -17, -15, -13, -8, -6, -4}},
    {{3, 5, 7, 12, 14, 16}, {-93, -15, -13, -6, -4, -98}},
    {{97, 3, 5, 12, 14}, {-93, -15, -13, -6, -4}},
    {{3, 12, 5, 14}, {-96, -93, -4, -13}},
    {{3, 12, 95}, {-93, -4, -13}},
    {{12, 14, 16, 18, 21, 23, 25, 27}, {-26, -24, -22, -17, -15, -110, -13, -103}},
    {{12, 109, 14, 16, 21, 23, 25}, {-26, -24, -22, -17, -15, -13, -103}},
    {{12, 14, 16, 21, 23, 25}, {-24, -22, -15, -13, -108, -103}},
    {{107, 12, 14, 21, 23}, {-24, -22, -15, -13, -103}},
    {{12, 21, 14, 23}, {-103, -22, -13, -106}},
    {{105, 12, 21}, {-103, -22, -13}},
    {{32, 34, 36, 21, 23, 25, 27, 30}, {-31, -26, -24, -120, -22, -113, -35, -33}},
    {{32, 34, 119, 21, 23, 25, 30}, {-31, -26, -24, -22, -113, -35, -33}},
    {{32, 34, 21, 23, 25, 30}, {-31, -24, -22, -118, -113, -33}},
    {{32, 117, 21, 23, 30}, {-31, -24, -22, -113, -33}},
    {{32, 21, 30, 23}, {-31, -22, -116, -113}},
    {{115, 21, 30}, {-31, -22, -113}},
    {{32, 34, 36, 39, 41, 43, 45, 30}, {-31, -123, -44, -42, -40, -35, -130, -33}},
    {{32, 129, 34, 39, 41, 43, 30}, {-31, -123, -44, -42, -40, -35, -33}},
    {{32, 34, 39, 41, 43, 30}, {-128, -31, -123, -42, -40, -33}},
    {{32, 39, 41, 30, 127}, {-31, -123, -42, -40, -33}},
    {{32, 41, 30, 39}, {-40, -31, -126, -123}},
    {{125, 30, 39}, {-40, -31, -123}},
    {{39, 41, 43, 45, 48, 50, 52, 54}, {-53, -51, -49, -44, -140, -42, -40, -133}},
    {{39, 41, 43, 139, 48, 50, 52}, {-53, -51, -49, -44, -42, -40, -133}},
    {{39, 41, 43, 48, 50, 52}, {-51, -49, -42, -138, -40, -133}},
    {{39, 41, 137, 48, 50}, {-51, -49, -42, -40, -133}},
    {{48, 41, 50, 39}, {-40, -133, -136, -49}},
    {{48, 135, 39}, {-40, -133, -49}},
    {{48, 50, 52, 54, 57, 59, 61, 63}, {-62, -60, -58, -150, -53, -51, -49, -143}},
    {{48, 50, 52, 149, 57, 59, 61}, {-62, -60, -58, -53, -51, -49, -143}},
    {{48, 50, 52, 57, 59, 61}, {-60, -58, -148, -51, -49, -143}},
    {{48, 50, 147, 57, 59}, {-60, -58, -51, -49, -143}},
    {{48, 57, 50, 59}, {-143, -146, -58, -49}},
    {{48, 57, 145}, {-143, -58, -49}},
    {{66, 68, 70, 72, 57, 59, 61, 63}, {-160, -62, -60, -58, -153, -71, -69, -67}},
    {{66, 68, 70, 57, 59, 61, 159}, {-62, -60, -58, -153, -71, -69, -67}},
    {{66, 68, 70, 57, 59, 61}, {-158, -60, -58, -153, -69, -67}},
    {{66, 68, 57, 59, 157}, {-60, -58, -153, -69, -67}},
    {{57, 66, 59, 68}, {-156, -67, -58, -153}},
    {{57, 66, 155}, {-67, -58, -153}},
    {{66, 68, 70, 72, 75, 77, 79, 81}, {-67, -80, -78, -76, -170, -71, -69, -163}},
    {{66, 68, 70, 169, 75, 77, 79}, {-67, -80, -78, -76, -71, -69, -163}},
    {{66, 68, 70, 75, 77, 79}, {-67, -78, -76, -168, -69, -163}},
    {{66, 68, 167, 75, 77}, {-67, -78, -76, -69, -163}},
    {{66, 75, 68, 77}, {-166, -76, -163, -67}},
    {{66, 75, 165}, {-76, -163, -67}},
    {{75, 77, 79, 81, 84, 86, 88, 90}, {-89, -87, -85, -180, -80, -78, -173, -76}},
    {{75, 77, 79, 179, 84, 86, 88}, {-89, -87, -85, -80, -78, -173, -76}},
    {{75, 77, 79, 84, 86, 88}, {-87, -85, -178, -78, -173, -76}},
    {{75, 77, 177, 84, 86}, {-87, -85, -78, -173, -76}},
    {{75, 84, 77, 86}, {-176, -173, -76, -85}},
    {{75, 84, 175}, {-173, -76, -85}},
    {{2, 4, 100, 6, 8, 11, 13, 15, 17}, {-92, -18, -16, -14, -12, -9, -7, -5, -3}},
    {{2, 4, 6, 8, 11, 13, 15, 17}, {-92, -99, -16, -14, -12, -7, -5, -3}},
    {{2, 98, 4, 6, 11, 13, 15}, {-92, -16, -14, -12, -7, -5, -3}},
    {{2, 4, 6, 11, 13, 15}, {-92, -14, -12, -5, -3, -97}},
    {{96, 2, 4, 11, 13}, {-92, -14, -12, -5, -3}},
    {{2, 11, 4, 13}, {-95, -12, -92, -3}},
    {{2, 11, 94}, {-12, -92, -3}},
    {{11, 13, 110, 15, 17, 20, 22, 24, 26}, {-27, -25, -23, -21, -18, -16, -14, -12, -102}},
    {{11, 13, 15, 17, 20, 22, 24, 26}, {-25, -23, -21, -16, -14, -109, -12, -102}},
    {{11, 108, 13, 15, 20, 22, 24}, {-25, -23, -21, -16, -14, -12, -102}},
    {{11, 13, 15, 20, 22, 24}, {-23, -21, -14, -12, -107, -102}},
    {{106, 11, 13, 20, 22}, {-23, -21, -14, -12, -102}},
    {{11, 20, 13, 22}, {-102, -21, -12, -105}},
    {{104, 11, 20}, {-102, -21, -12}},
    {{33, 35, 20, 22, 24, 26, 120, 29, 31}, {-32, -30, -27, -25, -23, -21, -112, -36, -34}},
    {{33, 35, 20, 22, 24, 26, 29, 31}, {-32, -30, -25, -23, -119, -21, -112, -34}},
    {{33, 20, 22, 118, 24, 29, 31}, {-32, -30, -25, -23, -21, -112, -34}},
    {{33, 20, 22, 24, 29, 31}, {-32, -30, -23, -21, -117, -112}},
    {{116, 20, 22, 29, 31}, {-32, -30, -23, -21, -112}},
    {{20, 29, 22, 31}, {-112, -30, -21, -115}},
    {{114, 20, 29}, {-112, -30, -21}},
    {{33, 130, 35, 38, 40, 42, 44, 29, 31}, {-32, -30, -122, -45, -43, -41, -39, -36, -34}},
    {{33, 35, 38, 40, 42, 44, 29, 31}, {-32, -30, -122, -43, -41, -39, -34, -129}},
    {{128, 33, 38, 40, 42, 29, 31}, {-32, -30, -122, -43, -41, -39, -34}},
    {{33, 38, 40, 42, 29, 31}, {-32, -127, -30, -122, -41, -39}},
    {{38, 40, 29, 126, 31}, {-32, -30, -122, -41, -39}},
    {{40, 29, 38, 31}, {-39, -30, -125, -122}},
    {{124, 29, 38}, {-39, -30, -122}},
    {{38, 40, 42, 44, 140, 47, 49, 51, 53}, {-54, -52, -50, -48, -45, -43, -41, -39, -132}},
    {{38, 40, 42, 44, 47, 49, 51, 53}, {-52, -50, -48, -43, -139, -41, -39, -132}},
    {{38, 40, 42, 138, 47, 49, 51}, {-52, -50, -48, -43, -41, -39, -132}},
    {{38, 40, 42, 47, 49, 51}, {-50, -137, -48, -41, -39, -132}},
    {{38, 40, 136, 47, 49}, {-50, -48, -41, -39, -132}},
    {{40, 49, 38, 47}, {-48, -39, -132, -135}},
    {{134, 38, 47}, {-48, -39, -132}},
    {{47, 49, 51, 53, 150, 56, 58, 60, 62}, {-63, -61, -59, -57, -54, -52, -50, -48, -142}},
    {{47, 49, 51, 53, 56, 58, 60, 62}, {-61, -59, -57, -149, -52, -50, -48, -142}},
    {{47, 49, 51, 148, 56, 58, 60}, {-61, -59, -57, -52, -50, -48, -142}},
    {{47, 49, 51, 56, 58, 60}, {-59, -57, -147, -50, -48, -142}},
    {{47, 49, 146, 56, 58}, {-59, -57, -50, -48, -142}},
    {{56, 49, 58, 47}, {-48, -142, -145, -57}},
    {{56, 144, 47}, {-48, -142, -57}},
    {{160, 65, 67, 69, 71, 56, 58, 60, 62}, {-63, -61, -59, -57, -152, -72, -70, -68, -66}},
    {{65, 67, 69, 71, 56, 58, 60, 62}, {-159, -61, -59, -57, -152, -70, -68, -66}},
    {{65, 67, 69, 56, 58, 60, 158}, {-61, -59, -57, -152, -70, -68, -66}},
    {{65, 67, 69, 56, 58, 60}, {-157, -59, -57, -152, -68, -66}},
    {{65, 67, 56, 58, 156}, {-59, -57, -152, -68, -66}},
    {{56, 65, 58, 67}, {-152, -155, -66, -57}},
    {{56, 65, 154}, {-152, -66, -57}},
    {{65, 67, 69, 71, 74, 170, 76, 78, 80}, {-81, -162, -79, -77, -75, -72, -70, -68, -66}},
    {{65, 67, 69, 71, 74, 76, 78, 80}, {-162, -79, -77, -75, -169, -70, -68, -66}},
    {{65, 67, 69, 168, 74, 76, 78}, {-162, -79, -77, -75, -70, -68, -66}},
    {{65, 67, 69, 74, 76, 78}, {-162, -77, -75, -167, -68, -66}},
    {{65, 67, 166, 74, 76}, {-162, -77, -75, -68, -66}},
    {{65, 74, 67, 76}, {-165, -66, -75, -162}},
    {{65, 74, 164}, {-66, -75, -162}},
    {{74, 76, 78, 80, 83, 180, 85, 87, 89}, {-90, -88, -86, -84, -81, -79, -77, -172, -75}},
    {{74, 76, 78, 80, 83, 85, 87, 89}, {-88, -86, -84, -179, -79, -77, -172, -75}},
    {{74, 76, 78, 178, 83, 85, 87}, {-88, -86, -84, -79, -77, -172, -75}},
    {{74, 76, 78, 83, 85, 87}, {-86, -84, -177, -77, -172, -75}},
    {{74, 76, 176, 83, 85}, {-86, -84, -77, -172, -75}},
    {{74, 83, 76, 85}, {-175, -84, -172, -75}},
    {{74, 83, 174}, {-84, -172, -75}},
    {{1, 3, 5, 7, 9, 10, 12, 14, 16, 18}, {-91, -100, -17, -15, -13, -11, -8, -6, -4, -2}},
    {{1, 3, 99, 5, 7, 10, 12, 14, 16}, {-91, -17, -15, -13, -11, -8, -6, -4, -2}},
    {{1, 3, 5, 7, 10, 12, 14, 16}, {-91, -15, -13, -98, -11, -6, -4, -2}},
    {{1, 97, 3, 5, 10, 12, 14}, {-91, -15, -13, -11, -6, -4, -2}},
    {{1, 3, 5, 10, 12, 14}, {-96, -91, -13, -11, -4, -2}},
    {{1, 3, 10, 12, 95}, {-91, -13, -11, -4, -2}},
    {{1, 10, 3, 12}, {-11, -94, -91, -2}},
    {{1, 10, 93}, {-11, -91, -2}},
    {{10, 12, 14, 16, 18, 19, 21, 23, 25, 27}, {-26, -24, -22, -20, -17, -15, -110, -13, -11, -101}},
    {{10, 12, 109, 14, 16, 19, 21, 23, 25}, {-26, -24, -22, -20, -17, -15, -13, -11, -101}},
    {{10, 12, 14, 16, 19, 21, 23, 25}, {-24, -22, -20, -15, -13, -108, -11, -101}},
    {{10, 107, 12, 14, 19, 21, 23}, {-24, -22, -20, -15, -13, -11, -101}},
    {{10, 12, 14, 19, 21, 23}, {-22, -20, -13, -11, -106, -101}},
    {{105, 10, 12, 19, 21}, {-22, -20, -13, -11, -101}},
    {{10, 19, 12, 21}, {-104, -101, -20, -11}},
    {{10, 19, 103}, {-101, -20, -11}},
    {{32, 34, 36, 19, 21, 23, 25, 27, 28, 30}, {-31, -29, -26, -24, -120, -22, -20, -111, -35, -33}},
    {{32, 34, 19, 119, 21, 23, 25, 28, 30}, {-31, -29, -26, -24, -22, -20, -111, -35, -33}},
    {{32, 34, 19, 21, 23, 25, 28, 30}, {-31, -29, -24, -22, -118, -20, -111, -33}},
    {{32, 19, 21, 117, 23, 28, 30}, {-31, -29, -24, -22, -20, -111, -33}},
    {{32, 19, 21, 23, 28, 30}, {-31, -29, -22, -20, -116, -111}},
    {{115, 19, 21, 28, 30}, {-31, -29, -22, -20, -111}},
    {{19, 28, 21, 30}, {-111, -29, -20, -114}},
    {{113, 19, 28}, {-111, -29, -20}},
    {{32, 34, 36, 37, 39, 41, 43, 45, 28, 30}, {-31, -29, -121, -44, -42, -40, -38, -35, -130, -33}},
    {{32, 129, 34, 37, 39, 41, 43, 28, 30}, {-31, -29, -121, -44, -42, -40, -38, -35, -33}},
    {{32, 34, 37, 39, 41, 43, 28, 30}, {-128, -31, -29, -121, -42, -40, -38, -33}},
    {{32, 37, 39, 41, 28, 30, 127}, {-31, -29, -121, -42, -40, -38, -33}},
    {{32, 37, 39, 41, 28, 30}, {-31, -126, -29, -121, -40, -38}},
    {{37, 39, 28, 125, 30}, {-31, -29, -121, -40, -38}},
    {{28, 37, 30, 39}, {-38, -29, -124, -121}},
    {{123, 28, 37}, {-38, -29, -121}},
    {{37, 39, 41, 43, 45, 46, 48, 50, 52, 54}, {-53, -51, -49, -47, -44, -140, -42, -40, -38, -131}},
    {{37, 39, 41, 43, 139, 46, 48, 50, 52}, {-53, -51, -49, -47, -44, -42, -40, -38, -131}},
    {{37, 39, 41, 43, 46, 48, 50, 52}, {-51, -49, -47, -42, -138, -40, -38, -131}},
    {{37, 39, 41, 137, 46, 48, 50}, {-51, -49, -47, -42, -40, -38, -131}},
    {{37, 39, 41, 46, 48, 50}, {-49, -47, -136, -40, -38, -131}},
    {{37, 135, 39, 46, 48}, {-49, -47, -40, -38, -131}},
    {{48, 37, 46, 39}, {-47, -38, -131, -134}},
    {{37, 46, 133}, {-47, -38, -131}},
    {{46, 48, 50, 52, 54, 55, 57, 59, 61, 63}, {-62, -60, -58, -56, -150, -53, -51, -49, -47, -141}},
    {{46, 48, 50, 52, 149, 55, 57, 59, 61}, {-62, -60, -58, -56, -53, -51, -49, -47, -141}},
    {{46, 48, 50, 52, 55, 57, 59, 61}, {-60, -58, -56, -148, -51, -49, -47, -141}},
    {{46, 48, 50, 147, 55, 57, 59}, {-60, -58, -56, -51, -49, -47, -141}},
    {{46, 48, 50, 55, 57, 59}, {-58, -56, -146, -49, -47, -141}},
    {{46, 48, 145, 55, 57}, {-58, -56, -49, -47, -141}},
    {{48, 57, 46, 55}, {-56, -47, -141, -144}},
    {{143, 46, 55}, {-56, -47, -141}},
    {{64, 66, 68, 70, 72, 55, 57, 59, 61, 63}, {-160, -62, -60, -58, -56, -151, -71, -69, -67, -65}},
    {{64, 66, 68, 70, 55, 57, 59, 61, 159}, {-62, -60, -58, -56, -151, -71, -69, -67, -65}},
    {{64, 66, 68, 70, 55, 57, 59, 61}, {-158, -60, -58, -56, -151, -69, -67, -65}},
    {{64, 66, 68, 55, 57, 59, 157}, {-60, -58, -56, -151, -69, -67, -65}},
    {{64, 66, 68, 55, 57, 59}, {-156, -58, -56, -151, -67, -65}},
    {{64, 66, 55, 57, 155}, {-58, -56, -151, -67, -65}},
    {{64, 57, 66, 55}, {-56, -151, -154, -65}},
    {{64, 153, 55}, {-56, -151, -65}},
    {{64, 66, 68, 70, 72, 73, 75, 77, 79, 81}, {-80, -78, -76, -74, -161, -170, -71, -69, -67, -65}},
    {{64, 66, 68, 70, 73, 169, 75, 77, 79}, {-80, -78, -76, -74, -161, -71, -69, -67, -65}},
    {{64, 66, 68, 70, 73, 75, 77, 79}, {-78, -76, -74, -161, -168, -69, -67, -65}},
    {{64, 66, 68, 167, 73, 75, 77}, {-78, -76, -74, -161, -69, -67, -65}},
    {{64, 66, 68, 73, 75, 77}, {-76, -74, -161, -166, -67, -65}},
    {{64, 66, 165, 73, 75}, {-76, -74, -161, -67, -65}},
    {{64, 73, 66, 75}, {-65, -164, -74, -161}},
    {{64, 73, 163}, {-65, -74, -161}},
    {{73, 75, 77, 79, 81, 82, 84, 86, 88, 90}, {-89, -87, -85, -180, -83, -80, -78, -76, -171, -74}},
    {{73, 75, 77, 79, 82, 179, 84, 86, 88}, {-89, -87, -85, -83, -80, -78, -76, -171, -74}},
    {{73, 75, 77, 79, 82, 84, 86, 88}, {-87, -85, -83, -178, -78, -76, -171, -74}},
    {{73, 75, 77, 177, 82, 84, 86}, {-87, -85, -83, -78, -76, -171, -74}},
    {{73, 75, 77, 82, 84, 86}, {-85, -83, -176, -76, -171, -74}},
    {{73, 75, 175, 82, 84}, {-85, -83, -76, -171, -74}},
    {{73, 82, 75, 84}, {-174, -171, -74, -83}},
    {{73, 82, 173}, {-171, -74, -83}}
  };

  // vector<Flags> ass_flags;
  for (auto ass_round : asses) {
    vector<int> ass_round_asses;
    tie(ass_round_asses, global_try) = ass_round;

    bool try_learn = true;
    printf("we are backtracking\n");
    backtrack ();
    for (auto ass : ass_round_asses) {
      // restart

      // make sure not trying to search_assume on fixed literal
      bool flag_fixed = false;
      Flags f = Internal::flags (ass);
      if (f.status == Flags::FIXED) {
        flag_fixed = true;
      }
      if (flag_fixed) {
        printf("skipping because of fixed literal %d\n", ass);
        // try_learn = false;
        continue;
      }
      if (val (ass) != 0) {
        printf("skipping because of assigned literal %d with value %d\n", ass, val (ass));
        // try_learn = false;
        continue;
      }

      // assume
      printf("propagating on %d with val %d\n", ass, val (ass));
      search_assume_decision (ass);
      if (!propagate ()) {
        printf("we are in first propagate with %d\n", ass);
        analyze ();
        while (!unsat && !propagate ()) {
          analyze ();
          printf("double propagate on %d\n", ass);
        }
        try_learn = false;
        break;
      }
    }
    // printf("We have the assignment for variables");
    // for (int i = 1; i <= max_var; i++) {
    //   printf("%d->%d; ", i, val(i));
    // }
    printf("\n");
    // learn
    // printf("finished asses\n");
    if (try_learn) {
      printf("trying to learn\n");
      bool added_a_clause = least_conditional_part(outFile, outFile_pr, original_time);
      // printf("did added a clause\n");
    } else {
      printf("did not try to learn\n");
    }
    
    // printf("we are backtracking!\n");
    // printf("We have propagated: %d and trail.size %d\n", propagated, trail.size());
    backtrack ();
    if (!propagate ()) {
      printf("Inside final propagate\n");
      analyze();
      while (!unsat && !propagate ()) {
        printf("Inside final propagate loop\n");
        analyze();
      }
    }
       // printf("After backtrack: We have propagated: %d and trail.size %d\n", propagated, trail.size());
    if (unsat) {
      STOP (global_preprocess);
      return 20;
    }
  }
  printf("finished global preprocess\n");
  STOP (global_preprocess);
  return 0;
}


// amar : created an option to learn globally blocked clauses in a preprocessing step
int Internal::global_preprocess () {
  START (global_preprocess);

    globalmarks.resize (2 * max_var + 1);

  for (int i = 0; i < globalmarks.size (); i++) {
    globalmarks[i] = 0;
  }
  std::ofstream outFile;
  char* filename = getenv("CADICAL_FILENAME");
  outFile.open (filename);
  if (!outFile) {
      error ("Error: File could not be created.");
  }

  std::ofstream outFile_pr;
  std::string filename_pr = filename;  // Implicit conversion
  filename_pr += "_pr";

  unsigned int seed;
  if (!opts.globalseed)
    seed = static_cast<unsigned int>(std::time(NULL)); // Store the seed
  else
    seed = opts.globalseed;

  // seed = 1745883155;

  printf("We are using the SEED: %d", seed);
  srand(seed);

  outFile_pr.open (filename_pr);
  if (!outFile_pr) {
      error ("Error: File could not be created.");
  }

  double original_time = time ();

  vector<int> sorted_literals;

  if (opts.globalisort) {
    sorted_literals = get_sorted_literals ();
  }

  for (int count = 1; count <= Internal::max_var; count++) {

    if (time () - original_time > opts.globaltimelim)
      break;

    int i;

    if (opts.globalisort) {
      // printf("first case !\n");
      if (count < sorted_literals.size()) {
        i = sorted_literals[count];
      } else {
        break;
      }
    } else if (opts.globalorderi) {
      // printf("second case !\n");
      i = count;
    } else {
      // printf("third case !\n");
      int i_no_polarity = (rand() % max_var) + 1;
      int i_polarity = (rand() % 2);
      i = (i_polarity ? -1 : 1) * i_no_polarity;
    }
    // printf("We are starting on i: %d\n", i);
    backtrack ();
    // need to have this outside to skip the extra unnecessary loops
    Flags &f = Internal::flags (i);
    if (f.status == Flags::FIXED) {
      // printf("skipping ALL of %d \n", i);
      continue;
    }
    // printf("Before on i: %d", i);
    search_assume_decision (i);
    if (!propagate ()) {
      // printf("1. We are in propagate with %d!\n", i);
      analyze ();
      if (!propagate ()) {
        // printf("2. We are in propagate with %d!\n", i);
        // printf("IN EARLY PROPAGATE: found unsat from %d\n", i);
        analyze ();
        break;
      }
      // printf("IN EARLY PROPAGATE: found conflict from %d\n", i);
      continue;
    }
    printf("We are staarting on i: %d", i);
    vector<int> touched_literals = get_touched_literals ();
    // printf("For literal %d, we touch: ", i);
    // print_vector (touched_literals);
    // for (int j = i + 1; j <= Internal::max_var; j++) {
    for (auto j : touched_literals) {
        if (time () - original_time > opts.globaltimelim)
          break;
        // printf("We are starting on j: %d \n", j);
        assert (!unsat);
        vector<int> polarities = opts.globalbothpol ? std::vector<int>{-1, 1} : std::vector<int>{1};
        for (int polarity : polarities) { 
          assert (!unsat);
          int j_polar = polarity * j;

          // need to have this in the inner loop beause this could be set in the inner loop!!!!
          Flags &f = Internal::flags (i);
          if (f.status == Flags::FIXED) {
            // printf("skipping ALL of %d \n", i);
            break;
          }
          Flags &f2 = Internal::flags (j_polar);
          if (f2.status == Flags::FIXED) {
            // printf("skipping one interation of %d \n", j_polar);
            continue;
          }
          //printf("We are propagating on %d and %d \n", i, j_polar);
          //printf("We have propagated: %d and trail.size %d \n", propagated, trail.size ());

          //printf("Made it past the skip at level %d\n", level);
          backtrack ();
          //printf("Made it past the backtrack at level %d\n", level);
          while (!propagate ()) {
            analyze ();
          }
          //printf("Made it past the propagate at level %d\n", level);
          
          //printf("We have propagated: %d and trail.size %d \n", propagated, trail.size ());
          search_assume_decision (i);
          //printf("We have search_assume_decision on i: %d\n", i);
          if (!propagate ()) {
            //printf("3. We are in propagate with %d!\n", i);
            //printf ("We reach a conflict from a single propagation on %d and will analyze\n", i);
            analyze ();
            while (!unsat && !propagate ()) {
              analyze ();
            }
          } else { 
            if (val (j_polar) != 0) {
              //printf("propagating %d give %d \n", i, j_polar);
              continue;
            }
            search_assume_decision (j_polar);
            //printf("We have search_assume_decision on j_polar: %d\n", j_polar);
            if (!propagate ()) {
              //printf("5. We are in propagate with %d!\n", j_polar);
              analyze ();
              while (!unsat && !propagate ()) {
                analyze ();
              }
            } else {
              // backtrack ();
              bool added_a_clause = least_conditional_part(outFile, outFile_pr, original_time);
              backtrack ();
              //printf("We have just finished adding a clause step!\n");
            }
          }
          if (unsat) {
            STOP (global_preprocess);
            return 20;
          }
        }
        if (unsat) {
          STOP (global_preprocess);
          return 20;
        }
      }
      //printf("out of loop!\n");
      if (unsat) {
        STOP (global_preprocess);
        return 20;
      }
      backtrack ();
      f = Internal::flags (i);
      if (f.status == Flags::FIXED) {
        // //printf("skipping ALL of %d \n", i);
        continue;
      }
      search_assume_decision (i);
      if (!propagate ()) {
        //printf("8. We are in propagate with %d!\n", i);
        // //printf("6.Right before analyze!\n");
        analyze ();
        while (!unsat && !propagate ()) {
          analyze ();
        }
        backtrack ();
        continue;
      }
      backtrack ();
      assert (Internal::flags (i).status != Flags::FIXED);
      search_assume_decision (-i);
      if (!propagate ()) {
        //printf("8. We are in propagate with %d!\n", i);
        analyze ();
        while (!unsat && !propagate ()) {
          analyze ();
        }
        backtrack ();
        continue;
      }
      if (unsat) {
        STOP (global_preprocess);
        return 20;
      }
  }
  if (unsat) {
    STOP (global_preprocess);
    return 20;
  }
  STOP (global_preprocess);
  return 0;
}

/*------------------------------------------------------------------------*/

int Internal::try_to_satisfy_formula_by_saved_phases () {
  LOG ("satisfying formula by saved phases");
  assert (!level);
  assert (!force_saved_phase);
  assert (propagated == trail.size ());
  force_saved_phase = true;
  if (external_prop) {
    assert (!level);
    LOG ("external notifications are turned off during preprocessing.");
    private_steps = true;
  }
  int res = 0;
  while (!res) {
    if (satisfied ()) {
      LOG ("formula indeed satisfied by saved phases");
      res = 10;
    } else if (decide ()) {
      LOG ("inconsistent assumptions with redundant clauses and phases");
      res = 20;
    } else if (!propagate ()) {
      LOG ("saved phases do not satisfy redundant clauses");
      assert (level > 0);
      backtrack ();
      conflict = 0; // ignore conflict
      assert (!res);
      break;
    }
  }
  assert (force_saved_phase);
  force_saved_phase = false;
  if (external_prop) {
    private_steps = false;
    LOG ("external notifications are turned back on.");
    if (!level)
      notify_assignments (); // In case fixed assignments were found.
    else {
      renotify_trail_after_local_search ();
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::produce_failed_assumptions () {
  LOG ("producing failed assumptions");
  assert (!level);
  assert (!assumptions.empty ());
  while (!unsat) {
    assert (!satisfied ());
    notify_assignments ();
    if (decide ())
      break;
    while (!unsat && !propagate ())
      analyze ();
  }
  notify_assignments ();
  if (unsat)
    LOG ("formula is actually unsatisfiable unconditionally");
  else
    LOG ("assumptions indeed failing");
}

/*------------------------------------------------------------------------*/

int Internal::local_search_round (int round) {

  assert (round > 0);

  if (unsat)
    return false;
  if (!max_var)
    return false;

  START_OUTER_WALK ();
  assert (!localsearching);
  localsearching = true;

  // Determine propagation limit quadratically scaled with rounds.
  //
  int64_t limit = opts.walkmineff;
  limit *= round;
  if (LONG_MAX / round > limit)
    limit *= round;
  else
    limit = LONG_MAX;

  int res = walk_round (limit, true);

  assert (localsearching);
  localsearching = false;
  STOP_OUTER_WALK ();

  report ('L');

  return res;
}

int Internal::local_search () {

  if (unsat)
    return 0;
  if (!max_var)
    return 0;
  if (!opts.walk)
    return 0;
  if (constraint.size ())
    return 0;

  int res = 0;

  for (int i = 1; !res && i <= lim.localsearch; i++)
    res = local_search_round (i);

  if (res == 10) {
    LOG ("local search determined formula to be satisfiable");
    assert (!stats.walk.minimum);
    res = try_to_satisfy_formula_by_saved_phases ();
  } else if (res == 20) {
    LOG ("local search determined assumptions to be inconsistent");
    assert (!assumptions.empty ());
    produce_failed_assumptions ();
  }

  return res;
}

/*------------------------------------------------------------------------*/

// if preprocess_only is false and opts.ilb is true we do not preprocess
// such that we do not have to backtrack to level 0.
// TODO: check restore_clauses works on higher level
//
int Internal::solve (bool preprocess_only) {
  assert (clause.empty ());
  START (solve);
  if (proof)
    proof->solve_query ();
  if (opts.ilb) {
    if (opts.ilbassumptions)
      sort_and_reuse_assumptions ();
    stats.ilbtriggers++;
    stats.ilbsuccess += (level > 0);
    stats.levelsreused += level;
    if (level) {
      assert (control.size () > 1);
      stats.literalsreused += num_assigned - control[1].trail;
    }
    if (external->propagator)
      renotify_trail_after_ilb ();
  }
  if (preprocess_only)
    LOG ("internal solving in preprocessing only mode");
  else
    LOG ("internal solving in full mode");
  init_report_limits ();
  int res = already_solved ();
  if (!res && preprocess_only && level)
    backtrack ();
  if (!res)
    res = restore_clauses ();
  if (!res) {
    init_preprocessing_limits ();
    if (!preprocess_only)
      init_search_limits ();
  }
  if (!res && !level)
    res = preprocess ();
  if (!res && opts.globalpreprocess) {
    if (opts.globalchessheur)
      res = global_preprocess_chess ();
    else
      res = global_preprocess ();
    backtrack ();
  } if (!preprocess_only) {
    if (!res && !level)
      res = local_search ();
    if (!res && !level)
      res = lucky_phases ();
    if (!res || (res == 10 && external_prop)) {
      if (res == 10 && external_prop && level)
        backtrack ();
      res = cdcl_loop_with_inprocessing ();
    }
  }
  finalize (res);
  reset_solving ();
  report_solving (res);
  STOP (solve);
  return res;
}

int Internal::already_solved () {
  int res = 0;
  if (unsat || unsat_constraint) {
    LOG ("already inconsistent");
    res = 20;
  } else {
    if (level && !opts.ilb)
      backtrack ();
    if (!level && !propagate ()) {
      LOG ("root level propagation produces conflict");
      learn_empty_clause ();
      res = 20;
    }
    if (max_var == 0 && res == 0)
      res = 10;
  }
  return res;
}
void Internal::report_solving (int res) {
  if (res == 10)
    report ('1');
  else if (res == 20)
    report ('0');
  else
    report ('?');
}

void Internal::reset_solving () {
  if (termination_forced) {

    // TODO this leads potentially to a data race if the external
    // user is calling 'terminate' twice within one 'solve' call.
    // A proper solution would be to guard / protect setting the
    // 'termination_forced' flag and only allow it during solving and
    // ignore it otherwise thus also the second time it is called during a
    // 'solve' call.  We could move resetting it also the start of
    // 'solve'.
    //
    termination_forced = false;

    LOG ("reset forced termination");
  }
}

int Internal::restore_clauses () {
  int res = 0;
  if (opts.restoreall <= 1 && external->tainted.empty ()) {
    LOG ("no tainted literals and nothing to restore");
    report ('*');
  } else {
    report ('+');
    // remove_garbage_binaries ();
    external->restore_clauses ();
    internal->report ('r');
    if (!unsat && !level && !propagate ()) {
      LOG ("root level propagation after restore produces conflict");
      learn_empty_clause ();
      res = 20;
    }
  }
  return res;
}

int Internal::lookahead () {
  assert (clause.empty ());
  START (lookahead);
  assert (!lookingahead);
  lookingahead = true;
  if (external_prop) {
    if (level) {
      // Combining lookahead with external propagator is limited
      // Note that lookahead_probing (); would also force backtrack anyway
      backtrack ();
    }
    LOG ("external notifications are turned off during preprocessing.");
    private_steps = true;
  }
  int tmp = already_solved ();
  if (!tmp)
    tmp = restore_clauses ();
  int res = 0;
  if (!tmp)
    res = lookahead_probing ();
  if (res == INT_MIN)
    res = 0;
  reset_solving ();
  report_solving (tmp);
  assert (lookingahead);
  lookingahead = false;
  STOP (lookahead);
  if (external_prop) {
    private_steps = false;
    LOG ("external notifications are turned back on.");
    notify_assignments (); // In case fixed assignments were found.
  }
  return res;
}

/*------------------------------------------------------------------------*/

void Internal::finalize (int res) {
  if (!proof)
    return;
  LOG ("finalizing");
  // finalize external units
  if (frat) {
    for (const auto &evar : external->vars) {
      assert (evar > 0);
      const auto eidx = 2 * evar;
      int sign = 1;
      uint64_t id = external->ext_units[eidx];
      if (!id) {
        sign = -1;
        id = external->ext_units[eidx + 1];
      }
      if (id) {
        proof->finalize_external_unit (id, evar * sign);
      }
    }
    // finalize internal units
    for (const auto &lit : lits) {
      const auto elit = externalize (lit);
      if (elit) {
        const unsigned eidx = (elit < 0) + 2u * (unsigned) abs (elit);
        const uint64_t id = external->ext_units[eidx];
        if (id) {
          assert (unit_clauses (vlit (lit)) == id);
          continue;
        }
      }
      const auto uidx = vlit (lit);
      const uint64_t id = unit_clauses (uidx);
      if (!id)
        continue;
      proof->finalize_unit (id, lit);
    }
    // See the discussion in 'propagate' on why garbage binary clauses stick
    // around.
    for (const auto &c : clauses)
      if (!c->garbage || c->size == 2)
        proof->finalize_clause (c);

    // finalize conflict and proof
    if (conflict_id) {
      proof->finalize_clause (conflict_id, {});
    }
  }
  proof->report_status (res, conflict_id);
  if (res == 10)
    external->conclude_sat ();
  else if (res == 20)
    conclude_unsat ();
  else if (!res)
    external->conclude_unknown ();
}

/*------------------------------------------------------------------------*/

void Internal::print_statistics () {
  stats.print (this);
  for (auto &st : stat_tracers)
    st->print_stats ();
}

/*------------------------------------------------------------------------*/

// Only useful for debugging purposes.

void Internal::dump (Clause *c) {
  for (const auto &lit : *c)
    printf ("%d ", lit);
  printf ("0\n");
}

void Internal::dump () {
  int64_t m = assumptions.size ();
  for (auto idx : vars)
    if (fixed (idx))
      m++;
  for (const auto &c : clauses)
    if (!c->garbage)
      m++;
  printf ("p cnf %d %" PRId64 "\n", max_var, m);
  for (auto idx : vars) {
    const int tmp = fixed (idx);
    if (tmp)
      printf ("%d 0\n", tmp < 0 ? -idx : idx);
  }
  for (const auto &c : clauses)
    if (!c->garbage)
      dump (c);
  for (const auto &lit : assumptions)
    printf ("%d 0\n", lit);
  fflush (stdout);
}

/*------------------------------------------------------------------------*/

bool Internal::traverse_constraint (ClauseIterator &it) {
  if (constraint.empty () && !unsat_constraint)
    return true;

  vector<int> eclause;
  if (unsat)
    return it.clause (eclause);

  LOG (constraint, "traversing constraint");
  bool satisfied = false;
  for (auto ilit : constraint) {
    const int tmp = fixed (ilit);
    if (tmp > 0) {
      satisfied = true;
      break;
    }
    if (tmp < 0)
      continue;
    const int elit = externalize (ilit);
    eclause.push_back (elit);
  }
  if (!satisfied && !it.clause (eclause))
    return false;

  return true;
}
/*------------------------------------------------------------------------*/

bool Internal::traverse_clauses (ClauseIterator &it) {
  vector<int> eclause;
  if (unsat)
    return it.clause (eclause);
  for (const auto &c : clauses) {
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false;
    for (const auto &ilit : *c) {
      const int tmp = fixed (ilit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      const int elit = externalize (ilit);
      eclause.push_back (elit);
    }
    if (!satisfied && !it.clause (eclause))
      return false;
    eclause.clear ();
  }
  return true;
}

} // namespace CaDiCaL

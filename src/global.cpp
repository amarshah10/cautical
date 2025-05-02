#include "internal.hpp"
#include <map>
#include <fstream>  // For file handling
#include <cstdlib>
#include <ctime>
#include <csignal>
#include <algorithm>
#include <random>
#include <unordered_set>
#include <set>
#include <utility>  // For std::pair
#include <algorithm>  // for std::min
using namespace std;

namespace CaDiCaL {

void print_vector (vector<int> c) {
    for(int i = 0; i < c.size(); i++){
            printf("%d ", c[i]);
        }
    printf("\n");
}

void printSet(const unordered_set<int> uset) {
    printf("  { ");
        for (const auto& elem : uset) {
            printf("%d ", elem);
        }
        printf("}\n");
}

void printVectorOfSets(const vector<unordered_set<int>>& vec) {
    printf("[\n");
    for (const auto& uset : vec) {
        printSet(uset);
    }
    printf("]\n");
}

// returns true if not a < b
// this is only true if there is some assuming (a) can give you 
bool Internal::compare_alpha_a(int a, int b) {
    backtrack ();
    search_assume_decision(a);

    if (!propagate()) {
        // we should never get here since we are propagating only from alpha_a
        assert (false);
    } else if (val(b) > 0) {
        LOG("We get that %d < %d\n", a, b);
        return true;  // a should come before b
    }
    return false;  // Otherwise, maintain original order
}

// custom sort function as I cannot use std::sort to sort alpha_a since compare_alpha_a is non-statics
// basically does a naive swapping thing
// todo: make this more efficient and do a topological sort
void Internal::imp_sort_alpha_a(std::vector<int>& alpha_a) {
    for (size_t i = 0; i < alpha_a.size(); ++i) {
        for  (size_t j = i + 1; j < alpha_a.size(); ++j) {
            if (compare_alpha_a(alpha_a[j] , alpha_a[i])) {
                LOG("comparing %d and %d\n", alpha_a[i], alpha_a[j]);
                int temp = alpha_a[j];
                alpha_a[j] = alpha_a[i];
                alpha_a[i] = temp;
            }
        }
    }
}

void Internal::random_sort_alpha_a(std::vector<int>& alpha_a) {
    std::random_device rd;  // Non-deterministic random number source
    std::default_random_engine rng(rd());  // Seeding the engine

    std::shuffle(alpha_a.begin(), alpha_a.end(), rng);
}

void Internal::custom_sort_alpha_a(std::vector<int>& alpha_a) {
    if (opts.globalalphaasort) {
        imp_sort_alpha_a(alpha_a);
    } else if (opts.globalalphaarandom) {
        random_sort_alpha_a(alpha_a);
    }
}
pair<vector<int>, vector<int>> greedySetCoverSpecial(vector<int> curr_global_try, vector<int> alpha_a, vector<unordered_set<int>>& subsets, vector<int> total_elements) {
        unordered_set<int> covered;
        unordered_set<int> uncovered(total_elements.begin(), total_elements.end());;
        int num_elements = 0;
        vector<int> chosen_subsets;
    
        // see if we can learn
        for (auto learn : curr_global_try) {
            // add idx of learn to chosen
            printf("trying ot learning %d\n", learn);
            printf("We have alpha_a: ");
            print_vector(alpha_a);
            int learn_idx = distance(alpha_a.begin(), find(alpha_a.begin(), alpha_a.end(), learn));
            printf("learn_idx: %d\n", learn_idx);
            printf("alpha_a.size(): %d\n", alpha_a.size());
            printf("subsets.size(): %d\n", subsets.size());
            assert(0<= learn_idx && learn_idx    < subsets.size());
            assert (alpha_a.size () == subsets.size ());
            // assert(0 <= learn_idx < alpha_a.size());
            chosen_subsets.push_back(learn_idx);
            covered.insert(subsets[learn_idx].begin(), subsets[learn_idx].end());
            for (const auto& elem : subsets[learn_idx]) {
                uncovered.erase(elem);
            }
        }
    
        vector<int> uncovered_vector(uncovered.begin (), uncovered.end ());
        printf("chosen_subsets: ");
        print_vector(chosen_subsets);
        printf("uncovered_vector: ");
        print_vector(uncovered_vector);
        return std::make_pair(chosen_subsets, uncovered_vector);
    }
    
// Function to find the smallest number of subsets that maximize union
pair<vector<int>, vector<int>> greedySetCover(vector<unordered_set<int>>& subsets, vector<int> total_elements) {

    unordered_set<int> covered;
    unordered_set<int> uncovered(total_elements.begin(), total_elements.end());;
    int num_elements = 0;
    vector<int> chosen_subsets;
    
    // Greedy selection process
    while (covered.size() < total_elements.size ()) {
        int best_idx = -1;
        size_t max_new_elements = 0;
        
        // Find the subset that adds the most new elements
        for (size_t i = 0; i < subsets.size(); i++) {
            size_t new_elements = 0;
            for (int elem : subsets[i]) {
                if (covered.find(elem) == covered.end()) {
                    new_elements++;
                }
            }
            
            if (new_elements > max_new_elements) {
                max_new_elements = new_elements;
                best_idx = i;
            }
        }

        // No more useful subsets found
        if (best_idx == -1) break;

        // Add the chosen subset to the solution
        chosen_subsets.push_back(best_idx);
        covered.insert(subsets[best_idx].begin(), subsets[best_idx].end());
        for (const auto& elem : subsets[best_idx]) {
            uncovered.erase(elem);
        }
    }

    vector<int> uncovered_vector(uncovered.begin (), uncovered.end ());
    return std::make_pair(chosen_subsets, uncovered_vector);
}
// picking alpha_a_useful based on greedy set cover


pair<vector<int>, vector<int>> Internal::greedy_sort_alpha_a_special(std::vector<int> alpha_a, std::vector<int> neg_alpha_c) {
    vector<int> empty;
    vector<int> global_try_final;

    printf("doing a greedy_sort_alpha_a with: \n");
    printf("alpha_a: ");
    print_vector(alpha_a);
    printf("neg_alpha_c");
    print_vector(neg_alpha_c);

    unordered_set<int> propagated;
    backtrack ();
    for (auto learn : global_try){
        if (find (alpha_a.begin(), alpha_a.end(), learn) != alpha_a.end()) {
            global_try_final.push_back(learn);
        }
        Flags &f = flags (learn);
        if (f.status == Flags::FIXED) {
            continue;
        }   
        // backtrack ();
        assert (val(-learn) >= 0);
        if (val(-learn) > 0) {
            printf("We have already learnt%d\n", -learn);
            continue;
        }
        printf("We are propagating %d\n", learn);
        search_assume_decision(-learn);
        if (!propagate ()) {
            printf("10. We are in propagate with %d!\n", -learn);
            analyze ();
            if (unsat) {
                printf("We have a conflict on %d!\n", learn);
                // break;
            }
            if (!propagate ()) {
                printf("11. We are in propagate with %d!\n", -learn);
                analyze ();
                // break;
            }
            return std::make_pair(empty, empty);
        }
        for (int j=0; j < neg_alpha_c.size(); j ++) {
            int v = val (neg_alpha_c[j]);
            if (v < 0) {
                assert (j < neg_alpha_c.size());
                propagated.insert(neg_alpha_c[j]);
            }
        }
        printSet(propagated);
    }

    backtrack (0);

    assert (propagated.size() == neg_alpha_c.size());
    return std::make_pair(global_try_final, empty);
}
    
pair<vector<int>, vector<int>> Internal::greedy_sort_alpha_a(std::vector<int> alpha_a, std::vector<int> neg_alpha_c) {
    vector<int> alpha_a_useful;
    vector<unordered_set<int>> alpha_a_propagated;

    printf("doing a greedy_sort_alpha_a with: \n");
    printf("alpha_a: ");
    print_vector(alpha_a);
    printf("neg_alpha_c");
    print_vector(neg_alpha_c);

    for (int i=0; i < alpha_a.size(); i++){
            Flags &f = flags (alpha_a[i]);

            if (f.status == Flags::FIXED) {
                continue;
            }   
            backtrack (0);
            search_assume_decision(-alpha_a[i]);
            if (!propagate ()) {
                // printf("10. We are in propagate with %d!\n", -alpha_a[i]);
                analyze ();
                if (unsat)
                    break;
                if (!propagate ()) {
                    // printf("11. We are in propagate with %d!\n", -alpha_a[i]);
                    analyze ();
                    break;
                }
                continue;
            } 
            unordered_set<int> propagated;
            for (int j=0; j < neg_alpha_c.size(); j ++) {
                int v = val (neg_alpha_c[j]);
                if (v < 0) {
                    assert (j < neg_alpha_c.size());
                    propagated.insert(neg_alpha_c[j]);
                }
            }
            if (propagated.size () > 0) {
                alpha_a_useful.push_back(alpha_a[i]);
                alpha_a_propagated.push_back(propagated);
            }
        }

    backtrack (0);

    printf("We are calling greedySsetCover!\n ");
    printf("Subsets:");
    printVectorOfSets(alpha_a_propagated);
    printf("alpha_a_useful: ");
    print_vector(alpha_a_useful);
    printf("neg_alpha_c:");
    print_vector (neg_alpha_c);

    auto [chosen_indices, neg_alpha_c_without_c0] = greedySetCoverSpecial(global_try, alpha_a, alpha_a_propagated, neg_alpha_c);
    // auto [chosen_indices, neg_alpha_c_without_c0] = greedySetCover(alpha_a_propagated, neg_alpha_c);

    vector<int> alpha_a_useful_final;

    // Add elements from alpha_a_useful based on chosen_indices
    for (int index : chosen_indices) {
        alpha_a_useful_final.push_back(alpha_a_useful[index]);
    }

    printf("alpha_a_useful_final: ");
    print_vector(alpha_a_useful_final);
    printf("neg_alpha_c_without_c0: ");
    print_vector(neg_alpha_c_without_c0);

    return std::make_pair(alpha_a_useful_final, neg_alpha_c_without_c0);
}

void Internal::bcp_shrink(vector<int> alpha_a, vector<int> alpha_a_useful, vector<int> neg_alpha_c_minus_c0) {
    for (int i=0; i < alpha_a.size(); i++){
        // todo : I think this shouldn't be necessary because we checked it earlier when creating alpha_a
        Flags &f = flags (alpha_a[i]);

        if (f.status == Flags::FIXED) {
            continue;
        }   

        Watches &ws = watches (alpha_a[i]);
        const const_watch_iterator end = ws.end ();
        watch_iterator j = ws.begin ();
        const_watch_iterator k;
        bool keep_i = false;
        for (k = j; k != end; k++) {
            Watch w = *k;
            Clause *c = w.clause;

            for (int alpha_c_j=0; alpha_c_j < neg_alpha_c_minus_c0.size();alpha_c_j++) {
                if (c-> size == 2 && ((c->literals[0] == alpha_a[i] && c->literals[1] == -neg_alpha_c_minus_c0[alpha_c_j]) || (c->literals[1] == alpha_a[i] && c->literals[0] == -neg_alpha_c_minus_c0[alpha_c_j] ))) {
                    neg_alpha_c_minus_c0.erase(neg_alpha_c_minus_c0.begin() + alpha_c_j);
                    keep_i = true;
                    break;
                }
            }
        }
        if (keep_i) {
            alpha_a_useful.push_back(alpha_a[i]);
        }
    }
}

bool Internal::propagate_shrink(vector<int> alpha_a, vector<int> alpha_a_useful, vector<int> neg_alpha_c_minus_c0) {
     for (int i=0; i < alpha_a.size(); i++){

        // todo : I think this shouldn't be necessary because we checked it earlier when creating alpha_a
        Flags &f = flags (alpha_a[i]);
        if (f.status == Flags::FIXED) {
            continue;
        }   
        backtrack (0);
        search_assume_decision(-alpha_a[i]); 

        // if we learn a singleton conflict, the gbc becomes trivial
        bool dont_learn_gbc = false;


        if (!propagate ()) {
            // printf("12. We are in propagate with %d!\n", -alpha_a[i]);
            analyze ();
            // I am not sure if the conflict checking here is completely correct
            if (!propagate ()) {
                // printf("13. We are in propagate with %d!\n", -alpha_a[i]);
                // printf("At position 3; propagated: %d; trail.size: %d \n", propagated, trail.size ());
                // printf ("got to a conflict \n");
                STOP (global);
                return false;
            }
            continue;
        } 

        bool keep_i = false;

        LOG(neg_alpha_c_minus_c0, "We have neg_alpha_c_minus_c0:");

        // vector<int> new_neg_alpha_c_minus_c0;
        // vector<int>::iterator it = neg_alpha_c_minus_c0.begin();

        for (int j=0; j < neg_alpha_c_minus_c0.size();) {
            int v = val (neg_alpha_c_minus_c0[j]);
            if (v < 0) {
                // print_assignment ();
                // printf("The literal %d in ~alpha_a implies literal %d in alpha_c by unit propagation \n", -alpha_a[i], -neg_alpha_c_minus_c0[j]);
                // new_neg_alpha_c_minus_c0.push_back(neg_alpha_c_minus_c0[j]);
                assert (j < neg_alpha_c_minus_c0.size());
                neg_alpha_c_minus_c0.erase(neg_alpha_c_minus_c0.begin() + j);
                keep_i = true;
            } else {
                j++;
            }
        }
        if (keep_i)
            alpha_a_useful.push_back(alpha_a[i]);
            }
        // was remembering literals without this backtrack
        backtrack (0);
}

// necessary procedure before adding a clause
void Internal::sort_vec_by_decision_level(vector<int>* v) {
    std::sort(v->begin (), v->end (), 
                [this](int x, int y) {
                    return (var (x).level > var (y).level);
                });
}

void Internal::record_clause (int lit, vector<int> negated_conditional, vector<int> autarky, std::ofstream& outFile, std::ofstream& outFile_pr) {
    outFile << lit << " ";
    outFile_pr << lit << " ";
    for (int val : negated_conditional) {
        outFile << val << " ";
        outFile_pr << val << " ";
    }
    outFile_pr << lit << " ";

    for (int val : autarky) {
        outFile_pr << val << " ";
    }
    outFile << "\n";
    // outFile.flush();
    outFile_pr << "\n";
    // outFile_pr.flush();
}

void Internal::add_clause(vector<int> new_clause, int lit, vector<int> negated_conditional, vector<int> autarky, std::ofstream& outFile, std::ofstream& outFile_pr) {

    printf("We are adding the clause: ");
    print_vector(new_clause);
    // removing the lit from autarky and negated conditional
    autarky.erase(std::remove(autarky.begin(), autarky.end(), lit), autarky.end());
    negated_conditional.erase(std::remove(negated_conditional.begin(), negated_conditional.end(), lit), negated_conditional.end());

    clause = new_clause;
    sort_vec_by_decision_level(&clause);

    if (opts.globallearn) {
        if (clause.size () > 1) {
            Clause* c = new_learned_weak_irredundant_global_clause (lit, negated_conditional, autarky, 1);
        } else {
            assign_original_unit_gbc (++clause_id, clause[0], autarky);
            // printf("we are adding the globally blocked unit: %d\n", clause[0]);
        }
    }
    if (opts.globalrecord)
        record_clause(lit, negated_conditional, autarky, outFile, outFile_pr);

    clause.clear ();
}

bool Internal::check_if_clause_trivial(vector<int> c) {
    START (trivial);
    if (c.size() > opts.globalmaxlen) {
        STOP (trivial);
        return true;
    }

    backtrack ();
    bool is_trivial = false;
    for (auto lit : c) {
        if (val (lit) > 0) {
            is_trivial = true;
            break;
        } else if (val (lit) < 0) {
            continue;
        }
        search_assume_decision (-1 * lit);
        
        if (!propagate ()) {
            // printf("9. We are in propagate with %d!\n", -1 *lit);
            // printf("found a conflict on %d!\n", lit);
            analyze (); // todo: there is an issue where if analyze finds a conflict right now we learn it :(
            while (!unsat && !propagate ()) {
                // printf("found another conflict!\n");
                analyze ();
            }
            // printf("finished with conflicts!\n");
            is_trivial = true;
            break;
        }
    }
    backtrack ();
    STOP (trivial);
    return is_trivial;
}

bool Internal::least_conditional_part(std::ofstream& outFile, std::ofstream& outFile_pr, int original_time) {

    START (global);

    vector<int> neg_alpha_c;
    std::map<int, int> times_touched;
    

    for (const auto &c: clauses) {        
        // skip learned (redundant) clauses (but only when we are not in proof checking mode)
        // todo: need to
        if (c->redundant && !proof) continue;

        // if (time () - original_time > opts.globaltimelim) {
        //     STOP (global);
        //     return false;
        // }
          


        // current assignment satisfies current clause
        bool satisfies_clause = false;
        // assignment mentioned in clause
        vector<int> alpha_touches;

        if (c->garbage) {
            continue;
        }
        bool skip_clause = false;
        for (const_literal_iterator l = c->begin (); l != c->end (); l++) {
            const int lit = *l;
            const signed char lit_val = val (lit);
            Flags &f = flags (lit);
            if (lit_val > 0 && f.status == Flags::FIXED) {
                skip_clause = true;
                break;
            }
        } 
        if (skip_clause) {
            continue;
        }


        for (auto lit : *c) {
            const signed char lit_val = val (lit);
            if (lit_val > 0) { // positive assignment
                satisfies_clause = true;
                // update times_touched with touch
                if (times_touched.find(lit) == times_touched.end()) { // lit not in dict
                    times_touched.insert(std::pair<int, int>(lit, 1));
                } else { // lit in dict
                    times_touched[lit] = times_touched[lit] + 1;
                }
            } else if (lit_val < 0) { // negative assignment
                // skip the fixed negative literals
                Flags &f = flags (lit);
                if (f.status == Flags::FIXED) {
                    continue;
                }
                // printf("1. We get here for lit %d", lit);
                if (!global_getbit(lit)) {
                    // printf("2. We get here for lit %d", lit);
                    alpha_touches.push_back(lit);
                }
            }
        }

        if (!satisfies_clause) {
            // add alpha_touches to neg_alpha_c
            neg_alpha_c.insert(neg_alpha_c.end(), alpha_touches.begin(), alpha_touches.end());
            // set "added to neg_alpha_c" bit
            for (int i=0; i < alpha_touches.size(); i++){
                // printf("adding to neg_alpha_c: %d \n", alpha_touches[i]);
                global_setbit(alpha_touches[i]);
            }
        }
    }

    // keep track of this for proof
    vector<int> alpha_a;

    vector<vector<int>> clauses_to_add;

    // Marijn suggested the heuristic that when alpha_a is entirely decision literals,
    // we need to not add a clause
    // todo: I'm not sure why this is?

    for (auto const& [key, val] : times_touched) {
        if (!global_getbit(key)) {
            if (!is_decision (key)) {
                vector<int> new_clause = neg_alpha_c;
                new_clause.push_back(key);
                clauses_to_add.push_back(new_clause);
            }
            // todo : maybe thsi shoudl be the 
            int key_val = Internal::val (key);
            alpha_a.push_back(key);
        }
    }

    // have to unset all of the bits
    for(int i=0; i < neg_alpha_c.size(); i++){
        global_unsetbit(neg_alpha_c[i]);
    }
    // todo: write a thing that checks that all bits have been properly unset

    // printf("We have: alpha_a: ");
    // print_vector(alpha_a);
    // printf("neg_alpha_c: ");
    // print_vector(neg_alpha_c);


    vector <int>neg_alpha_c_minus_c0(neg_alpha_c);
    vector <int> alpha_a_useful;


    // sorting alpha_a by implication, randomly or not at all depending on flags
    custom_sort_alpha_a(alpha_a);

    if (opts.globalalphaagreedy && !opts.globalchessheur) {
        std::tie(alpha_a_useful, neg_alpha_c_minus_c0) = greedy_sort_alpha_a(alpha_a, neg_alpha_c); // issue with variable shadowing
    } else if (opts.globalalphaagreedy) {
        std::tie(alpha_a_useful, neg_alpha_c_minus_c0) = greedy_sort_alpha_a_special(alpha_a, neg_alpha_c);
    } else {
    
        // try to shrink clauses using binary clause propagation, instead of a more general propagation
        if (opts.globalbcp) {
            bcp_shrink( alpha_a, alpha_a_useful, neg_alpha_c_minus_c0);
        // otherwise try to shrink clauses using internal propagator
        } else {
           bool end_early = propagate_shrink(alpha_a, alpha_a_useful, neg_alpha_c_minus_c0);
           if (!end_early) {
             STOP (global);
             return false;
           }
        }
    }


    bool adding_a_clause = false;
    // backtrack ();
    if (alpha_a_useful.empty() || opts.globalnoshrink) {
        for (int i=0; i < std::min(opts.globalmaxclause, static_cast<int>(clauses_to_add.size())); i++){
            if (time () - original_time > opts.globaltimelim) {
                STOP (global);
                return false;
            }
            adding_a_clause = true;
            vector<int> new_clause = clauses_to_add[i];
            if (!(opts.globalfiltertriv && check_if_clause_trivial (new_clause)))
                add_clause (new_clause, new_clause.back (), new_clause, alpha_a, outFile, outFile_pr);
        }
    } else {
        adding_a_clause = true;
        vector<int> new_clause(neg_alpha_c_minus_c0);
        new_clause.insert(new_clause.end(), alpha_a_useful.begin(), alpha_a_useful.end());
        if (!(opts.globalfiltertriv && check_if_clause_trivial (new_clause))) {
            add_clause (new_clause, alpha_a_useful.back(), new_clause, alpha_a, outFile, outFile_pr);
        } else {
            printf("skipping because of trivial clause\n");
        }
    }

    STOP (global);
    return adding_a_clause;

  }
}
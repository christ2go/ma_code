import itertools
from collections import Counter

n = 5
m = 3

pos = list(itertools.permutations(list(range(n)), n))
preference_vecs = list(itertools.product(pos, repeat=m))
print(len(pos))

print(len(preference_vecs))
i = 1
global vardict
vardict = {}


from collections import Counter

def plurality_winner(preference_vecs):
    first_choices = [vec[0] for vec in preference_vecs]
    counts = Counter(first_choices)
    max_votes = max(counts.values())
    winners = [candidate for candidate, votes in counts.items() if votes == max_votes]
    if len(winners) == 1:
        return winners[0]
    else:
        return None

for x in preference_vecs:
    for c in range(n):
        vardict[(c, x)] = i
        i = i+1
def lookup(profile , candidate):
    return vardict[(candidate, profile)]
#
print(vardict)
def is_top_modification(p1, c, p2):
    for i in range(len(p1)):
        if p1[i] != p2[i]:
            if p2[i][0] != c:
                return False
    return True


from pysat.formula import CNF, WCNF
from pysat.solvers import Solver, Glucose3

dictvar = dict((v, k) for k, v in vardict.items())

# Create a CNF formula
cnf = CNF()
clausetype = {}
# First require, that at least one value is assigned
for x in preference_vecs:
    v = []
    for cn in range(n):
        v.append(lookup(x, cn))
    cnf.append(v)
    clausetype[str(v)] = "AT_LEAST_1"
print("At least 1 generated")
# Secondly require that exactly one is assigned
for x in preference_vecs:
    for c1 in range(n):
        for c2 in range(n):
            if c1 != c2:
                cnf.append([-lookup(x, c1), -lookup(x, c2)])
                clausetype[str([-lookup(x, c1), -lookup(x, c2)])] = "EXACT1"
def are_permutations(tup1, tup2):
    return sorted(tup1) == sorted(tup2)
def is_single_transposition(tup1, tup2):
    diffs = [(a, b) for a, b in zip(tup1, tup2) if a != b]
    return (len(diffs) == 2 and diffs[0] == diffs[1][::-1], sorted(diffs[0])) if len(diffs) == 2 else (False, None)


def is_neutral(profile1, profile2):
    if len(profile1) != len(profile2):
        return False, None

    swapped = None
    for pref1, pref2 in zip(profile1, profile2):
        transposed, options = is_single_transposition(pref1, pref2)
        if not transposed:
            return False, None
        if swapped is None:
            swapped = options
        elif swapped != options:
            return False, None

    return True, swapped

# Top-monotonic:
i = 0
nonplclause = []
otherl = []

for x in preference_vecs:
    print(i/(len(preference_vecs)))
    i = i+1
    w = plurality_winner(x)
    if w != None:
        nonplclause.append(- lookup(x, w))
        if lookup(x, w) != 7:
            otherl.append(lookup(x, w))

    for y in preference_vecs:
        if are_permutations(x, y):
            for c in range(n):
                cnf.append([-lookup(x, c), lookup(y, c)])
                clausetype[str([-lookup(x, c), lookup(y, c)])] = "AN"
        for c in range(n):
            if is_top_modification(x, c, y):
                cnf.append([-lookup(x, c), lookup(y, c)])
                clausetype[str([-lookup(x, c), lookup(y, c)])] = "TM"
        (b, partners) = is_neutral(x, y)
        if b:
            if plurality_winner(x) != None:
                cnf.append([-lookup(x, partners[0]), lookup(y, partners[1])])
                clausetype[str([-lookup(x, partners[0]), lookup(y, partners[1])])] = "WN"

                cnf.append([-lookup(x, partners[1]), lookup(y, partners[0])])
                clausetype[str([-lookup(x, partners[1]), lookup(y, partners[0])])] = "WN"





# (Weak neutrality)


# Add a tops-only clause
#def tops_equal(t1, t2):
#    for x in range(len(t1)):
#        if t1[x] != t2[x]:
#            return False
#    return True

#for x in preference_vecs:
#    for y in preference_vecs:
#        for c in range(n):
#            continue
            #cnf.append([-lookup(x, c), lookup(y, c)])
# Has to disagree with plurality rule
# Use Solver to solve the formula
print("Not PL generated")
cnf.append(nonplclause)
clausetype[str(nonplclause)] = "PL"
from pysat.examples.musx import MUSX
import sys
cnf.to_file("example.sat")
wcnfplus = WCNF()
from pysat.solvers import Minisat22
for clause in cnf.clauses:
    wcnfplus.append(clause)
from pysat.solvers import Lingeling
'''
with Lingeling(bootstrap_with=cnf.clauses, with_proof=True) as l:
    if l.solve() == False:
        print(p := l.get_proof())
        for x in p[:-1]:
            s = x.split(' ')[0]
            print(clause := cnf.clauses[int(s)])
            print(clausetype[str(clause)])
            if clause[0] > 0:
                print(str(dictvar[clause[0]]))
            else:
                print("-"+str(dictvar[-clause[0]]))
            if clause[1] > 0:
                print(str(dictvar[clause[1]]))
            else:
                print("-" +str(dictvar[-clause[1]]))
'''

import random
def find_local_minimum_unsat_core(clauses):
    unsat_core = clauses.copy()

    solver = Glucose3()
    n = len(unsat_core)

    lo = 0
    hi = n - 1

    while lo <= hi:
        mid = (lo + hi) // 2

        # Create a new solver for each iteration
        solver.new()
        for i in range(mid + 1):
            clause = unsat_core[i]
            solver.add_clause(clause)

        # Check if the subset is unsatisfiable
        if not solver.solve():
            hi = mid - 1
        else:
            lo = mid + 1

    # Get the bisection index
    bisection_index = lo
    print("Searching")
    # Randomize the order of clauses after bisection
    unsat_core = unsat_core[:bisection_index+1]
    random.shuffle(unsat_core)

    for clause in unsat_core:
        # Create a new solver for each clause iteration
        solver = Glucose3()
        print("Try "+str(clause))
        for c in unsat_core:
            if c != clause:
                solver.add_clause(c)

        # Check if the remaining clauses are still unsatisfiable
        if not solver.solve():
            print("Red")
            unsat_core.remove(clause)  # Remove the clause from the unsat core

    return unsat_core

with Glucose3(with_proof=True) as s:
    # Add the formula to the solver
    s.append_formula(cnf.clauses)

    # Check if the formula is satisfiable
    if s.solve():
        print("The formula is satisfiable.")
        model = s.get_model()
        print("The model (or assignment) is: ", model)
        for x in preference_vecs:
            for c in range(n):
                if lookup(x, c) in model:
                    #if plurality_winner(x) != c:
                    print(str(x)+  "is assigned "+str(c))
    else:
        from pysat.formula import CNF



        print("The formula is not satisfiable.")
        print(len(cnf.clauses))
        core = find_local_minimum_unsat_core(find_local_minimum_unsat_core(cnf.clauses))
        print(core)
        s.new()
        s.append_formula(core)
        if s.solve():
            print("s solvable")
        else:
            print("unsat")
        for c in core:
            #print(clausetype[str(c)]+" "+str(c))
            if len(c) == 2:
                if c[0] < 0:
                    print(str(-c[0]), end=" ")
                else:
                    print("Not "+str(c[0]), end=" ")
                print("=>", end=" ")
                if c[1] < 0:
                    print("Not "+str(-c[1]))
                else:
                    print(str(c[1]))
        for c in core:
            print(clausetype[str(c)]+" "+str(c))

        for x in vardict:
            print(x, vardict[x])
        #




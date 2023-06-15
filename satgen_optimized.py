import itertools

n = 5
m = 4

pos = list(itertools.permutations(list(range(n)), n))
preference_vecs = list(itertools.combinations_with_replacement(pos, m))
print(len(pos))
print(pos)
print(len(preference_vecs))
print(preference_vecs)
i = 1
global vardict
vardict = {}

def to_dimacs(clauses, filename):
    num_variables = max(abs(literal) for clause in clauses for literal in clause)
    num_clauses = len(clauses)

    with open(filename, 'w') as f:
        f.write(f"p cnf {num_variables} {num_clauses}\n")

        for clause in clauses:
            clause_str = " ".join(map(str, clause))
            f.write(clause_str + " 0\n")  # Append "0" to denote the end of a clause.

# Example usage:

clauses = [[1, -2, 3], [-1, 2], [-3]]

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
def is_top_modification(p1, c, p2):
    #if p1 == p2:
    #    return False
    for x in p2:
        if x[0] == c:
            continue
        if p1.count(x) < p2.count(x):
            return False
    return True


dictvar = dict((v, k) for k, v in vardict.items())

# Create a CNF formula
cnf = []
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

def swap(tup, a, b):
    return tuple(b if x == a else a if x == b else x for x in tup)

for x in preference_vecs:
    print(i/(len(preference_vecs)))
    i = i+1
    w = plurality_winner(x)
    if w != None:
        nonplclause.append(- lookup(x, w))
        if lookup(x, w) != 7:
            otherl.append(lookup(x, w))

    for y in preference_vecs:
        for c in range(n):
            if is_top_modification(x, c, y):
                cnf.append([-lookup(x, c), lookup(y, c)])
                clausetype[str([-lookup(x, c), lookup(y, c)])] = "TM"
    for c in range(n):
        for cp in range(n):
            if c == cp:
                continue
            swapped = tuple(map(lambda x: swap(x, c, cp), x))
            if plurality_winner(x) != None and plurality_winner(swapped) != None:
                cnf.append([-lookup(x, c), lookup(tuple(sorted(swapped)), cp)])
                cnf.append([-lookup(tuple(sorted(swapped)), cp), lookup(x, c), ])







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

print(cnf)


to_dimacs(cnf, ("generated-%d-%d.sat"%(n,m)))

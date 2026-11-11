"""Hvor mye av det åpne tilfellet av regel 3 dekker rot-teknikken?

For alle DAG-er med 3 til 5 noder og alle valg av y, z, X, W der betingelsen
i regel 3 svikter, deles tilfellene i tre:
  1. z er ikke forfar til W: bevist (rule3_complete_nonanc, v3.3).
  2. z er forfar til W, men y og z er d-forbundet i G_{X̄z̄}: bevist
     (rule3_complete_root, v3.6).
  3. Resten: åpent.

Resultat (2026-11-11):
  betingelsen svikter: 201923
    tilfelle 1:  96473
    tilfelle 2:  95421
    tilfelle 3:  10029 (det minste eksemplet er 0 -> 1 -> 2 med y=0, z=1, W={2})
  I 9200 av de 10029 går det en rettet vei y -> ... -> z utenom X ∪ W.
"""
import itertools

def anc(edges, S):
    res = set(S); ch = True
    while ch:
        ch = False
        for a, b in edges:
            if b in res and a not in res:
                res.add(a); ch = True
    return res

def dsep(edges, x, y, Z):
    A = anc(edges, {x, y} | set(Z))
    E = [(a, b) for a, b in edges if a in A and b in A]
    adj = {v: set() for v in A}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    for v in A:
        pa = [a for a, b in E if b == v]
        for i in pa:
            for j in pa:
                if i != j: adj[i].add(j)
    seen = {x}; st = [x]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w in Z or w in seen: continue
            seen.add(w); st.append(w)
    return y not in seen

fail = case1 = case2 = case3 = 0
for n in [3, 4, 5]:
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for mask in range(1 << len(pairs)):
        edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        for y, z in itertools.permutations(range(n), 2):
            rest = [v for v in range(n) if v not in (y, z)]
            for asg in itertools.product([0, 1, 2], repeat=len(rest)):
                X = {v for v, a in zip(rest, asg) if a == 1}
                W = {v for v, a in zip(rest, asg) if a == 2}
                GX = [(a, b) for a, b in edges if b not in X]
                Z2 = {z} - anc(GX, W)
                H = [(a, b) for a, b in GX if b not in Z2]
                if dsep(H, y, z, X | W): continue
                fail += 1
                if Z2: case1 += 1; continue
                Hz = [(a, b) for a, b in GX if b != z]
                if not dsep(Hz, y, z, X | W): case2 += 1
                else: case3 += 1
print("betingelsen svikter:", fail)
print("  tilfelle 1 (z ikke forfar til W):", case1)
print("  tilfelle 2 (d-forbundet i G_{X̄z̄}):", case2)
print("  tilfelle 3 (åpent):", case3)

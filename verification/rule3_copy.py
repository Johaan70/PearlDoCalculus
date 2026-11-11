"""Kopi-modellen (rule3_complete_copy, v3.7) mot det åpne tilfellet av regel 3.

Tilfelle 3 fra rule3_gap.py: z er forfar til W, y og z er d-separert gitt
S = X ∪ W i G_{X̄z̄}, men d-forbundet i G_{X̄}. Kopi-modellen dekker et tilfelle
når det finnes s ∉ S med rettede veier s ⇝ y og s ⇝ z utenom S, z når en
forelder til en w1 ∈ W utenom S, og z ikke når y. For hvert dekket tilfelle
regnes modellen ut eksakt, og punktet (y=0, w1=1, resten av S=0, do(z=1))
skal gi P_z(y,w)·P(w) = 1/4 og P(y,w)·P_z(w) = 0.

Resultat (2026-11-11), DAG-er med 3 til 5 noder:
  tilfelle 3: 10029, dekket: 10005, punktet feiler: 0.
  De 24 udekkede har alle en kollider i W, f.eks. n=5,
  kanter [(0,1),(0,3),(1,4),(2,3)], y=2, z=1, X=∅, W={3,4}.
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

def ra(edges, S, s):
    seen = {s}; st = [s]
    while st:
        u = st.pop()
        for a, b in edges:
            if a == u and b not in seen and b not in S:
                seen.add(b); st.append(b)
    return seen

def rz(edges, S, s, w):
    R = ra(edges, S, s)
    return any(a in R for a, b in edges if b == w)

def joint(n, H, S, s, w1, do):
    out = {}
    for b in [0, 1]:
        val = {}
        for v in range(n):
            if v in do: val[v] = do[v]
            elif v == s: val[v] = b
            elif v in S and v != w1: val[v] = 0
            else: val[v] = int(any(val[a] for a, c in H if c == v and a not in S))
        k = tuple(val[v] for v in range(n)); out[k] = out.get(k, 0) + 0.5
    return out

def m(J, a):
    return sum(p for k, p in J.items() if all(k[i] == x for i, x in a.items()))

tot = cov = bad = 0; miss = []
for n in [3, 4, 5]:
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for mask in range(1 << len(pairs)):
        edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        for y, z in itertools.permutations(range(n), 2):
            rest = [v for v in range(n) if v not in (y, z)]
            for asg in itertools.product([0, 1, 2], repeat=len(rest)):
                X = {v for v, a in zip(rest, asg) if a == 1}
                W = {v for v, a in zip(rest, asg) if a == 2}
                S = X | W
                H = [(a, b) for a, b in edges if b not in X]
                if ({z} - anc(H, W)) or dsep(H, y, z, S): continue
                if not dsep([(a, b) for a, b in H if b != z], y, z, S): continue
                tot += 1
                ws = [w for w in W if rz(H, S, z, w)]
                ss = [s for s in range(n) if s not in S
                      and y in ra(H, S, s) and z in ra(H, S, s)]
                if y in ra(H, S, z) or not ws or not ss:
                    if len(miss) < 3: miss.append((n, edges, y, z, X, W))
                    continue
                cov += 1; s, w1 = ss[0], ws[0]
                Jo = joint(n, H, S, s, w1, {}); Jd = joint(n, H, S, s, w1, {z: 1})
                wp = {w: int(w == w1) for w in S}
                lhs = m(Jd, {y: 0, **wp}) * m(Jo, wp)
                rhs = m(Jo, {y: 0, **wp}) * m(Jd, wp)
                if not (abs(lhs - 0.25) < 1e-12 and rhs == 0): bad += 1
print("tilfelle 3:", tot, "| dekket:", cov, "| punktet feiler:", bad)
for x in miss: print("  ikke dekket:", x)

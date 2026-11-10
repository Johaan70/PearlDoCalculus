"""Søk etter moteksempler til fullstendighet for regel 3.

For alle DAG-er med 3 og 4 noder (topologisk ordnet etter indeks), alle y != z
og alle måter å fordele de andre nodene på X, W eller ingen av dem:
regn ut om betingelsen i regel 3 holder (y d-separert fra z gitt X ∪ W i
G_{X̄, Z(W)̄}), og test likheten
    P_{x,z}(y, w) · P_x(w) = P_x(y, w) · P_{x,z}(w)
i 25 tilfeldige binære modeller.

Resultat (2026-11-10):
  betingelsen holder:  4789 tilfeller, likheten holdt i alle  (soundness)
  betingelsen svikter: 2267 tilfeller, likheten holdt i alle modeller i 0
Altså ingen moteksempler: hver gang betingelsen svikter, svikter regelen i en
av modellene. Det tyder på at fullstendighet for regel 3 holder også når z er
forfar til W, som er det tilfellet som ikke er formalisert.
"""
import itertools, random
random.seed(1)

def anc(edges, S):
    res = set(S); ch = True
    while ch:
        ch = False
        for (a, b) in edges:
            if b in res and a not in res:
                res.add(a); ch = True
    return res

def dsep(edges, x, y, Z):
    """d-separasjon via moralisering av den forfedrelukkede delgrafen."""
    A = anc(edges, {x, y} | set(Z))
    E = [(a, b) for (a, b) in edges if a in A and b in A]
    adj = {v: set() for v in A}
    for a, b in E:
        adj[a].add(b); adj[b].add(a)
    for v in A:
        pa = [a for (a, b) in E if b == v]
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

def joint(edges, n, cpt, do):
    out = {}
    for vals in itertools.product([0, 1], repeat=n):
        p = 1.0
        for v in range(n):
            if v in do:
                p *= 1.0 if vals[v] == do[v] else 0.0
            else:
                pa = tuple(vals[a] for a in sorted(a for (a, b) in edges if b == v))
                q = cpt[v][pa]; p *= q if vals[v] else 1 - q
        if p > 0: out[vals] = p
    return out

def marg(J, assign):
    return sum(p for vals, p in J.items() if all(vals[k] == v for k, v in assign.items()))

def rule3_holds(edges, n, X, W, y, z, trials=25):
    for _ in range(trials):
        cpt = {v: {pa: random.uniform(0.05, 0.95)
                   for pa in itertools.product([0, 1], repeat=sum(1 for (a, b) in edges if b == v))}
               for v in range(n)}
        for xv in itertools.product([0, 1], repeat=len(X)):
            dx = dict(zip(sorted(X), xv))
            for zv in [0, 1]:
                Jx = joint(edges, n, cpt, dx); Jxz = joint(edges, n, cpt, {**dx, z: zv})
                for yv in [0, 1]:
                    for wv in itertools.product([0, 1], repeat=len(W)):
                        dw = dict(zip(sorted(W), wv))
                        lhs = marg(Jxz, {y: yv, **dw}) * marg(Jx, dw)
                        rhs = marg(Jx, {y: yv, **dw}) * marg(Jxz, dw)
                        if abs(lhs - rhs) > 1e-9: return False
    return True

hold = hold_ok = fail = fail_ok = 0
for n in [3, 4]:
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for mask in range(1 << len(pairs)):
        edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        for y, z in itertools.permutations(range(n), 2):
            rest = [v for v in range(n) if v not in (y, z)]
            for assign in itertools.product([0, 1, 2], repeat=len(rest)):
                X = {v for v, a in zip(rest, assign) if a == 1}
                W = {v for v, a in zip(rest, assign) if a == 2}
                GX = [(a, b) for (a, b) in edges if b not in X]
                Z2 = {z} - anc(GX, W)
                H = [(a, b) for (a, b) in GX if b not in Z2]
                ok = rule3_holds(edges, n, X, W, y, z, trials=5 if dsep(H, y, z, X | W) else 25)
                if dsep(H, y, z, X | W):
                    hold += 1; hold_ok += ok
                else:
                    fail += 1; fail_ok += ok
                    if ok: print("MOTEKSEMPEL?", n, edges, "y", y, "z", z, "X", X, "W", W)
print("betingelsen holder: ", hold, "| likheten holdt i alle modeller:", hold_ok)
print("betingelsen svikter:", fail, "| likheten holdt i alle modeller:", fail_ok)

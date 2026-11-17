"""Numeriske sjekker for H4 (fra røttene til Y), november 2026.

Lineære paritetsmodeller over ZMod 2 regnes ut eksakt (brøker) ved å summere over alle
latente biter og all støy. Tre spørsmål for hvert modellpar M1, M2:
  obs lik   - samme fordeling over alle observerte noder?
  positiv   - har hver observert tilordning positiv sannsynlighet?
  do-forskj - finnes x der P(Y | do(X = x)) er ulik i M1 og M2?

Eksempel A: en hale fra en rot går inn igjen i F.
Eksempel C: en hale må gå gjennom F' \\ F, og F er en hel c-komponent i G_{X̄}[An(Y)]
            (slik hedgen fra ID-algoritmen er). Regelen i artikkelen (M2 = M1, bortsett fra
            at F-noder ignorerer foreldre i F' \\ F; halene er paritet av foreldrene) gir
            ingen do-forskjell på z. Et fullt søk finner noen få positive lineære par, men de
            endrer også en node i F' \\ F og følger ingen generell regel.
            Produktkonstruksjonen (H3-modellen i én koordinat, halene i en annen) virker på
            både A og C.
"""
import itertools
from fractions import Fraction as Fr

q, h = Fr(1, 4), Fr(1, 2)

def dist(order, lat, reads, noise, X=None):
    X = X or {}
    noisy = [v for v in order if noise.get(v, 0) and v not in X]
    P = {}
    for lb in itertools.product([0, 1], repeat=len(lat)):
        for nb in itertools.product([0, 1], repeat=len(noisy)):
            w = Fr(1, 2 ** len(lat)); val = dict(zip(lat, lb)); nz = dict(zip(noisy, nb))
            for v in noisy: w *= noise[v] if nz[v] else 1 - noise[v]
            for v in order:
                val[v] = X[v] if v in X else (sum(val[p] for p in reads[v]) + nz.get(v, 0)) % 2
            k = tuple(val[v] for v in order); P[k] = P.get(k, 0) + w
    return P

def dist2(order, lat, readsA, noiseA, R, tail, X=None):
    """Produktkonstruksjon: (a_v, b_v); a = paritetsmodellen, b_v = [v i R] a_v + sum b over
    halebarn + støy(1/4)."""
    X = X or {}
    nA = [v for v in order if v in noiseA and v not in X]; nB = [v for v in order if v not in X]
    P = {}
    for lb in itertools.product([0, 1], repeat=len(lat)):
        for na in itertools.product([0, 1], repeat=len(nA)):
            for nb in itertools.product([0, 1], repeat=len(nB)):
                w = Fr(1, 2 ** len(lat)); val = dict(zip(lat, lb)); A = dict(zip(nA, na)); B = dict(zip(nB, nb))
                for v in nA: w *= noiseA[v] if A[v] else 1 - noiseA[v]
                for v in nB: w *= q if B[v] else 1 - q
                a, b = {}, {}
                for v in order:
                    if v in X: a[v], b[v] = X[v]; continue
                    a[v] = (sum(val[p] if p in val else a[p] for p in readsA[v]) + A.get(v, 0)) % 2
                    b[v] = ((a[v] if v in R else 0) + sum(b[p] for p in tail.get(v, [])) + B[v]) % 2
                k = tuple((a[v], b[v]) for v in order); P[k] = P.get(k, 0) + w
    return P

def marg(P, order, S):
    idx = [order.index(s) for s in S]; Q = {}
    for k, w in P.items():
        kk = tuple(k[i] for i in idx); Q[kk] = Q.get(kk, 0) + w
    return Q

def report(name, P1, P2, nvals, gap):
    print(f"{name}: obs lik={P1 == P2}, positiv={len(P1) == nvals}, do-forskj={'ja' if gap else 'NEI'}")

def check(name, order, lat, r1, r2, noise, Xs, Y):
    P1, P2 = dist(order, lat, r1, noise), dist(order, lat, r2, noise)
    gap = any(marg(dist(order, lat, r1, noise, dict(zip(Xs, xs))), order, Y) !=
              marg(dist(order, lat, r2, noise, dict(zip(Xs, xs))), order, Y)
              for xs in itertools.product([0, 1], repeat=len(Xs)))
    report(name, P1, P2, 2 ** len(order), gap)

def check2(name, order, lat, r1, r2, noiseA, R, tail, Xs, Y):
    P1, P2 = dist2(order, lat, r1, noiseA, R, tail), dist2(order, lat, r2, noiseA, R, tail)
    vals = [(0, 0), (0, 1), (1, 0), (1, 1)]
    gap = any(marg(dist2(order, lat, r1, noiseA, R, tail, dict(zip(Xs, xs))), order, Y) !=
              marg(dist2(order, lat, r2, noiseA, R, tail, dict(zip(Xs, xs))), order, Y)
              for xs in itertools.product(vals, repeat=len(Xs)))
    report(name, P1, P2, 4 ** len(order), gap)

# Eksempel A: u:{r,f}, u':{x,f}; r->a->f, x->f, f->z. F={r,f}=R, F'={r,f,x}, X={x}, Y={z}.
oA, lA = ['x', 'r', 'a', 'f', 'z'], ['u', 'up']
A1 = {'x': ['up'], 'r': ['u'], 'a': ['r'], 'f': ['u', 'up', 'x'], 'z': ['f']}
A2 = {'x': ['up'], 'r': ['u'], 'a': ['r'], 'f': ['u'], 'z': ['f']}
check("A, F leser ikke halen", oA, lA, A1, A2, {'r': q, 'a': q, 'z': q}, ['x'], ['z'])
A1h = dict(A1, f=['u', 'up', 'x', 'a']); A2h = dict(A2, f=['u', 'a'])
check("A, F leser halen     ", oA, lA, A1h, A2h, {'r': q, 'a': q, 'z': q}, ['x'], ['z'])

# Eksempel C: u:{r,r2}, u2:{w,x}, u4:{x,r2}; r->w->r2, x->w, r2->z. F={r,r2}=R, F'={r,r2,x,w}.
oC, lC = ['x', 'r', 'w', 'r2', 'z'], ['u', 'u2', 'u4']
C1 = {'x': ['u4', 'u2'], 'r': ['u'], 'w': ['u2', 'x'], 'r2': ['u', 'u4', 'w'], 'z': ['r2']}
C2 = dict(C1, r2=['u'])
check("C, H3 på røttene     ", oC, lC, C1, C2, {'r': q, 'z': h}, ['x'], ['r', 'r2'])
check("C, z = r2 + støy     ", oC, lC, C1, C2, {'r': q, 'z': q}, ['x'], ['z'])
check("C, w leser r (hale)  ", oC, lC, dict(C1, w=['u2', 'x', 'r']), dict(C2, w=['u2', 'x', 'r']),
      {'r': q, 'z': q}, ['x'], ['z'])

# Fullt søk på C: alle lineære modeller (hver node leser en delmengde av foreldrene i G).
par = {'x': ['u2', 'u4'], 'r': ['u'], 'w': ['r', 'x', 'u2'], 'r2': ['w', 'u', 'u4']}
def subsets(l):
    for k in range(len(l) + 1):
        yield from (list(c) for c in itertools.combinations(l, k))
for noise in [{'r': q, 'z': q}, {'r2': q, 'z': q}, {'r': q, 'w': q, 'z': q},
              {'x': q, 'r': q, 'w': q, 'r2': q, 'z': q}]:
    groups = {}
    for sx, sr, sw, s2 in itertools.product(*(list(subsets(par[v])) for v in ['x', 'r', 'w', 'r2'])):
        rd = {'x': sx, 'r': sr, 'w': sw, 'r2': s2, 'z': ['r2']}
        P = dist(oC, lC, rd, noise)
        if len(P) != 2 ** len(oC): continue          # bare positive modeller
        D = tuple(tuple(sorted(marg(dist(oC, lC, rd, noise, {'x': xv}), oC, ['z']).items())) for xv in (0, 1))
        groups.setdefault(tuple(sorted(P.items())), set()).add(D)
    n = sum(1 for g in groups.values() if len(g) > 1)
    print(f"C, fullt søk, støy {sorted(noise)}: positive par med ulik P(z|do x): {n}")

# Produktkonstruksjonen.
check2("C, produkt           ", oC, lC, dict(C1, z=[]), dict(C2, z=[]), {'r': q, 'z': h}, {'r', 'r2'},
       {'w': ['r'], 'r2': ['w'], 'z': ['r2']}, ['x'], ['z'])
check2("A, produkt           ", oA, lA, dict(A1, a=[], z=[]), dict(A2, a=[], z=[]), {'r': q, 'a': h, 'z': h},
       {'r', 'f'}, {'a': ['r'], 'f': ['a'], 'z': ['f']}, ['x'], ['z'])

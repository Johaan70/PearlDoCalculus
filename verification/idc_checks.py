"""Exact checks of the construction in the appendix of Shpitser and Pearl, "Identification
of Conditional Interventional Distributions" (UAI 2006, arXiv:1206.6876), proof of
Theorem 6, the "only if" direction. November 2026. See docs/design-idc.md, Part B.

The paper's naming is used throughout: a hedge is F' ⊊ F, F meets X, F' avoids X
(the Lean `Hedge.IsHedge G U X Y F F'` has the names swapped).

The construction, as written (appendix, p. 7):
  * H = De(F) ∩ An(W') (the text prints "∪"; Theorem 2 uses "∩", which is read here);
  * M1, M2: the models of Theorem 2 on H. Every variable is binary; every observed node is
    the parity of its parents in H; latents are fair coins; in M2 every node of F' ignores
    its parents in F ∖ F' (observed and latent);
  * p: the last segment of a back-door path from some W ∈ W' to Y, from the last node Y'
    in H to Y, with the directed chains that open its colliders. Every node of p is the
    parity of its parents in H ∪ p, or a fair coin if it has none; a node of H with a
    parent in p also reads that parent. The models are M1*, M2* on H ∪ p;
  * W'' = the nodes of W in H ∪ p, all observed to be 0.
Claims checked: P1* = P2* on the observed nodes; P*(w'' = 0) > 0 and P*_x(w'' = 0) > 0;
and P1*_x(y | w'' = 0) ≠ P2*_x(y | w'' = 0) for some x. In base case (b) (the first edge
of p leaves Y' ∈ H) the paper does not use M1*, M2* but argues by a recursion; there the
direct extension is reported for information only.

Sections: 1. one hand-made graph for each case of the induction, with a collider chain
back into H and a back-door path that leaves H and re-enters it; 2. the recursion of base
case (b) on one graph; 3. Example C of notes/tails-gap.md (a tail of H through F) with
y -> z; 4. a random search over segments p attached to five hedge structures; 5. a
collider of p right after Y'; 6. positive linear parity models with noise, which decide
whether Theorem 6 itself holds on the graphs where the construction fails.

Part B, step 3 (the repaired construction of docs/design-idc.md): 7. on the hand-made
graphs; 8. on the random families of section 4; 9. case 1 (P_x(W) identifiable) on new
random families; 10. the graph lemma that a first design needed, which is false; 11.
Lemma U and the unread switch on random graphs, and the whole construction on random
graphs where the hedge reads nodes of W. The product models of Hedge/ParityModels and
Hedge/Product are rebuilt here (`product_models`), and all laws are computed exactly by
a linear network over ZMod 2 (`Net`).

All probabilities are exact fractions, computed by summing over all latent and coin bits.
Run with: python3 verification/idc_checks.py (about 20 minutes; sections 6, 8 and 11 are
the slow ones).
"""
import itertools
import os
import random
from fractions import Fraction as Fr


class Graph:
    """Observed nodes `obs`, latents `lat` (name -> its two observed children), directed
    edges between observed nodes."""

    def __init__(self, obs, lat, edges):
        self.obs, self.lat, self.edges = list(obs), dict(lat), set(edges)

    def nodes(self):
        return self.obs + sorted(self.lat)

    def parents(self, v):
        return sorted(a for (a, b) in self.edges if b == v) + \
            sorted(u for u, cs in self.lat.items() if v in cs)

    def children(self, v):
        if v in self.lat:
            return list(self.lat[v])
        return sorted(b for (a, b) in self.edges if a == v)

    def topo(self):
        order, seen = [], set()
        def visit(v):
            if v in seen:
                return
            seen.add(v)
            for a in self.parents(v):
                if a in self.obs:
                    visit(a)
            order.append(v)
        for v in self.obs:
            visit(v)
        return order

    def acyclic(self):
        state = {}
        def dfs(v):
            state[v] = 1
            for c in self.children(v):
                if state.get(c) == 1 or (c not in state and not dfs(c)):
                    return False
            state[v] = 2
            return True
        return all(state.get(v) or dfs(v) for v in self.nodes())

    def anc(self, S):
        out, todo = set(S), list(S)
        while todo:
            for a in self.parents(todo.pop()):
                if a not in out:
                    out.add(a); todo.append(a)
        return out

    def desc(self, S):
        out, todo = set(S), list(S)
        while todo:
            for c in self.children(todo.pop()):
                if c not in out:
                    out.add(c); todo.append(c)
        return out

    def induced(self, S):
        return Graph([v for v in self.obs if v in S],
                     {u: cs for u, cs in self.lat.items() if u in S and set(cs) <= S},
                     {(a, b) for (a, b) in self.edges if a in S and b in S})


def dsep(G, A, B, Z, cut_in=(), cut_out=()):
    """d-separation of A and B given Z in G without the edges into `cut_in` and out of
    `cut_out` (ancestral moral graph)."""
    par = {v: [a for a in G.parents(v) if v not in cut_in and a not in cut_out]
           for v in G.nodes()}
    anc, todo = set(A) | set(B) | set(Z), list(set(A) | set(B) | set(Z))
    while todo:
        for a in par[todo.pop()]:
            if a not in anc:
                anc.add(a); todo.append(a)
    nb = {v: set() for v in anc}
    for v in anc:
        ps = [a for a in par[v] if a in anc]
        for a in ps:
            nb[v].add(a); nb[a].add(v)
        for a, b in itertools.combinations(ps, 2):
            nb[a].add(b); nb[b].add(a)
    seen, todo = set(A) - set(Z), list(set(A) - set(Z))
    while todo:
        for n in nb[todo.pop()]:
            if n not in seen and n not in Z:
                seen.add(n); todo.append(n)
    return not (seen & set(B))


def dist(G, reads, coins, do=None, noise=None):
    """Exact joint law of the observed nodes: latents and `coins` are fair bits, every
    other observed node is the parity of what it reads (plus a noise bit of law `noise`)."""
    do, noise = do or {}, noise or {}
    order = G.topo()
    lat = sorted(G.lat)
    cs = [v for v in order if v in coins and v not in do]
    ns = [v for v in order if v in noise and v not in do and v not in coins]
    P = {}
    for bits in itertools.product([0, 1], repeat=len(lat) + len(cs) + len(ns)):
        val = dict(zip(lat, bits))
        c = dict(zip(cs, bits[len(lat):]))
        n = dict(zip(ns, bits[len(lat) + len(cs):]))
        w = Fr(1, 2 ** (len(lat) + len(cs)))
        for v in ns:
            w *= noise[v] if n[v] else 1 - noise[v]
        for v in order:
            if v in do:
                val[v] = do[v]
            elif v in c:
                val[v] = c[v]
            else:
                val[v] = (sum(val[a] for a in reads[v]) + n.get(v, 0)) % 2
        k = tuple(val[v] for v in G.obs)
        P[k] = P.get(k, 0) + w
    return P


def cond(G, P, y, Ws):
    """P(y | Ws = 0) as a pair (P(y=0|.), P(y=1|.)), or None if P(Ws = 0) = 0."""
    iy, iw = G.obs.index(y), [G.obs.index(w) for w in Ws]
    num, den = [Fr(0), Fr(0)], Fr(0)
    for k, p in P.items():
        if all(k[i] == 0 for i in iw):
            den += p; num[k[iy]] += p
    return None if den == 0 else (num[0] / den, num[1] / den)


def is_hedge(G, F, Fs, X, Wp, forest):
    """Def. 5 of the paper for F' = Fs ⊊ F, with the forest edges `forest` (a subset of
    the directed edges of G inside F): both c-forests with the same root set R,
    F ∩ X ≠ ∅, F' ∩ X = ∅, R ⊆ An(W') in G without the edges into X."""
    def cforest(S):
        ob = [v for v in S if v in G.obs]
        lats = [u for u in S if u in G.lat]
        if any(not set(G.lat[u]) <= S for u in lats):
            return None
        comp, todo = {ob[0]}, [ob[0]]
        while todo:
            v = todo.pop()
            for u in lats:
                if v in G.lat[u]:
                    for c in G.lat[u]:
                        if c not in comp:
                            comp.add(c); todo.append(c)
        ch = {v: [b for (a, b) in forest if a == v and b in S] for v in ob}
        if set(ob) != comp or any(len(c) > 1 for c in ch.values()):
            return None
        R = {v for v in ob if not ch[v]}
        for v in ob:
            while ch[v]:
                v = ch[v][0]
            if v not in R:
                return None
        return R
    RF, RFs = cforest(F), cforest(Fs)
    if RF is None or RFs is None or RF != RFs or not Fs < F:
        return False
    if not (F & X) or (Fs & X):
        return False
    Gx = Graph(G.obs, {u: cs for u, cs in G.lat.items() if not set(cs) & X},
               {(a, b) for (a, b) in G.edges if b not in X})
    return RF <= Gx.anc(Wp)


def construct(M, F, Fs, P):
    """M1*, M2* on the model graph M = H ∪ p, as in the appendix."""
    r1 = {v: M.parents(v) for v in M.obs}
    r2 = {v: [a for a in r1[v] if not (v in Fs and a in F - Fs)] for v in M.obs}
    coins = {v for v in M.obs if v in P and not r1[v]}
    return r1, r2, coins


def evaluate(M, F, Fs, P, X, y, Ws, noise=None):
    """The claims for M1*, M2* on M: (obs equal, w''=0 positive, effect differs, P > 0)."""
    r1, r2, coins = construct(M, F, Fs, P)
    X = [x for x in M.obs if x in X]
    P1, P2 = dist(M, r1, coins, noise=noise), dist(M, r2, coins, noise=noise)
    eq = P1 == P2
    pos = len(P1) == 2 ** len(M.obs)
    wpos, differ = cond(M, P1, y, Ws) is not None and cond(M, P2, y, Ws) is not None, False
    for xs in itertools.product([0, 1], repeat=len(X)):
        do = dict(zip(X, xs))
        c1 = cond(M, dist(M, r1, coins, do, noise), y, Ws)
        c2 = cond(M, dist(M, r2, coins, do, noise), y, Ws)
        if c1 is None or c2 is None:
            wpos = False
        elif c1 != c2:
            differ = True
    return eq, wpos, differ, pos


def theorem6_hyp(G, X, y, Ws):
    """Every W ∈ W has a back-door path to y given W ∖ {W} in G ∖ X (rule 2 fails for W)."""
    return all(not dsep(G, {w}, {y}, set(X) | (set(Ws) - {w}), cut_in=set(X), cut_out={w})
               for w in Ws)


def fmt(b):
    return "yes" if b else "NO"


# ---------------------------------------------------------------------------------------
# Hedge structures for P_x(w'), with H = De(F) ∩ An(W') and every observed node of H
# with at most one child in H.
# ---------------------------------------------------------------------------------------
STRUCTS = {
    # bow: x <-> w, x -> w
    "bow": dict(obs=["x", "w"], lat={"u1": ("x", "w")}, edges={("x", "w")},
                F={"u1", "x", "w"}, Fs={"w"}, X={"x"}, Wp={"w"}, forest={("x", "w")}),
    # three nodes: x <-> a, a <-> w, x -> w, a -> w; F' = {a, w}
    "three": dict(obs=["x", "a", "w"], lat={"u1": ("x", "a"), "u2": ("a", "w")},
                  edges={("x", "w"), ("a", "w")}, F={"u1", "u2", "x", "a", "w"},
                  Fs={"u2", "a", "w"}, X={"x"}, Wp={"w"}, forest={("x", "w"), ("a", "w")}),
    # bow with a tail r -> t -> w below the root r
    "tail": dict(obs=["x", "r", "t", "w"], lat={"u1": ("x", "r")},
                 edges={("x", "r"), ("r", "t"), ("t", "w")}, F={"u1", "x", "r"}, Fs={"r"},
                 X={"x"}, Wp={"w"}, forest={("x", "r")}),
    # two roots: x <-> r1, x <-> r2, r1 <-> r2, x -> r1; F' = {r1, r2}; both roots in W'
    "tworoots": dict(obs=["x", "r1", "r2"],
                     lat={"u1": ("x", "r1"), "u2": ("x", "r2"), "u3": ("r1", "r2")},
                     edges={("x", "r1")}, F={"u1", "u2", "u3", "x", "r1", "r2"},
                     Fs={"u3", "r1", "r2"}, X={"x"}, Wp={"r1", "r2"}, forest={("x", "r1")}),
}


def struct_graph(s):
    return Graph(s["obs"], s["lat"], s["edges"])


# ---------------------------------------------------------------------------------------
# 1. Hand-made cases: one for each case of the induction
# ---------------------------------------------------------------------------------------
def hand_case(name, sname, extra_obs, extra_lat, extra_edges, P, y, Ws, note="",
              model_drop=()):
    """`P`: the nodes of p (with its chains and latents); nodes of `extra_obs` not in P
    and not in H are on the cut-off part of the back-door path and are not modelled."""
    s = STRUCTS[sname]
    G = Graph(s["obs"] + extra_obs, dict(s["lat"], **extra_lat), s["edges"] | set(extra_edges))
    assert G.acyclic(), name
    assert is_hedge(G, s["F"], s["Fs"], s["X"], s["Wp"], s["forest"]), name
    H = G.desc(s["F"]) & G.anc(s["Wp"])
    assert not (H & set(P)), name
    hyp = theorem6_hyp(G, s["X"], y, Ws)
    M = G.induced(H | set(P))
    M.edges -= set(model_drop)
    Wpp = [w for w in Ws if w in M.obs]
    eq, wpos, differ, pos = evaluate(M, s["F"], s["Fs"], set(P), s["X"], y, Wpp)
    print(f"{name:38s} hyp={fmt(hyp):3s} obs-equal={fmt(eq):3s} w''=0 pos.={fmt(wpos):3s} "
          f"differs={fmt(differ):3s} P>0={fmt(pos)}{note}")
    return eq, wpos, differ


print("== 1. Hand-made cases: query P_x(y | W = 0) ==")
print("hyp: the hypothesis of Theorem 6; obs-equal: P1* = P2*; w''=0 pos.: P*(w''=0) > 0 and")
print("P*_x(w''=0) > 0 in both models for every x; differs: P1*_x(y|w''=0) != P2*_x(y|w''=0)")
print("for some x; P>0: the observed law of M1* has full support (the paper does not claim it).")
hand_case("base (a): y -> w", "bow", ["y"], {}, [("y", "w")], ["y"], "y", ["w"])
hand_case("base (a), ind. Y'->Y: w <- c -> y", "bow", ["c", "y"], {},
          [("c", "w"), ("c", "y")], ["c", "y"], "y", ["w"])
hand_case("ind. Y->Y': w <- c <- y", "bow", ["c", "y"], {}, [("c", "w"), ("y", "c")],
          ["c", "y"], "y", ["w"])
hand_case("ind. Y'<->Y: w <- c <-> y", "bow", ["c", "y"], {"s1": ("c", "y")}, [("c", "w")],
          ["c", "y", "s1"], "y", ["w"])
hand_case("base (c): w <-> y", "bow", ["y"], {"s1": ("w", "y")}, [], ["y", "s1"], "y", ["w"])
hand_case("ind. collider d ∈ W: w<-c->d<-y", "bow", ["c", "d", "y"], {},
          [("c", "w"), ("c", "d"), ("y", "d")], ["c", "d", "y"], "y", ["w", "d"])
STRUCTS["bow2"] = dict(STRUCTS["bow"], obs=["x", "w", "w2"], edges={("x", "w"), ("w", "w2")},
                       Wp={"w", "w2"})
hand_case("collider chain d -> w2 back into H", "bow2", ["c", "d", "y"], {},
          [("c", "w"), ("c", "d"), ("y", "d"), ("d", "w2")], ["c", "d", "y"], "y",
          ["w", "w2"], "  (w2 ∈ W' ⊆ H)")
hand_case("re-entry: r1 <- e -> r2 <-> y", "tworoots", ["e", "y"], {"s1": ("r2", "y")},
          [("e", "r1"), ("e", "r2")], ["y", "s1"], "y", ["r1", "r2"],
          "  (leaves H at e, re-enters at r2)")
hand_case("base (b), direct ext.: a -> y", "three", ["y"], {}, [("a", "y")], ["y"], "y",
          ["w"], "  (not claimed by the paper)")


print()
print("== 2. Base case (b): the paper's recursion on the last graph ==")
# G = three + a -> y, Y' = a ∈ F, Y = y. G' removes the outgoing arrow a -> w of Y' in H.
# Removing it from F gives c-forests with root set R ∪ {a} = {w, a}: a hedge for P_x(y, w)
# in G'. If P_x(w) is identifiable in G', the chain rule gives non-identifiability of
# P_x(y | w) in G'. Below: the Theorem 2 models of that hedge in G' (H = De(F) ∩ An(y, w)).
Gp = Graph(["x", "a", "w", "y"], {"u1": ("x", "a"), "u2": ("a", "w")},
           {("x", "w"), ("a", "y")})
Fb, Fsb = {"u1", "u2", "x", "a", "w"}, {"u2", "a", "w"}
print("new hedge for P_x(y, w) in G':", fmt(is_hedge(Gp, Fb, Fsb, {"x"}, {"y", "w"},
                                                     {("x", "w")})))
print("hedge for P_x(w) in G' with the old F':",
      fmt(is_hedge(Gp, Fb, Fsb, {"x"}, {"w"}, {("x", "w")})))
r1, r2, coins = construct(Gp, Fb, Fsb, set())
for xv in (0, 1):
    D1, D2 = dist(Gp, r1, coins, {"x": xv}), dist(Gp, r2, coins, {"x": xv})
    def m(D, S):
        out = {}
        for k, pr in D.items():
            kk = tuple(k[Gp.obs.index(v)] for v in S); out[kk] = out.get(kk, 0) + pr
        return out
    print(f"x={xv}: P_x(y,w) equal={fmt(m(D1, ['y', 'w']) == m(D2, ['y', 'w']))}, "
          f"P_x(w) equal={fmt(m(D1, ['w']) == m(D2, ['w']))}, "
          f"P_x(y=0|w=0): M1 {cond(Gp, D1, 'y', ['w'])[0]}, M2 {cond(Gp, D2, 'y', ['w'])[0]}")
print("observed laws equal:", fmt(dist(Gp, r1, coins) == dist(Gp, r2, coins)))

print()
print("== 3. The tails gap inside H: Example C of notes/tails-gap.md, with y -> z ==")
# x -> w, r -> w, w -> r2, r2 -> z; u: r <-> r2, u2: w <-> x, u4: x <-> r2. The hedge for
# P_x(z) is F = {x, r, w, r2} (forest x -> w -> r2, without r -> w), F' = {r, r2},
# R = {r, r2}. H = De(F) ∩ An(z) is the whole graph, and it keeps the edge r -> w.
STRUCTS["exC"] = dict(obs=["x", "r", "w", "r2", "z"],
                      lat={"u": ("r", "r2"), "u2": ("w", "x"), "u4": ("x", "r2")},
                      edges={("x", "w"), ("r", "w"), ("w", "r2"), ("r2", "z")},
                      F={"u", "u2", "u4", "x", "r", "w", "r2"}, Fs={"u", "r", "r2"},
                      X={"x"}, Wp={"z"}, forest={("x", "w"), ("w", "r2")})
hand_case("C + y -> z, H as written", "exC", ["y"], {}, [("y", "z")], ["y"], "y", ["z"],
          "  (w reads r)")
hand_case("C + y -> z, w ignores r", "exC", ["y"], {}, [("y", "z")], ["y"], "y", ["z"],
          "  (the forest only)", model_drop={("r", "w")})


# ---------------------------------------------------------------------------------------
# 4. Random search: random segments p attached to the hedge structures of section 1
# ---------------------------------------------------------------------------------------
def witness(G, X, Wp, Ws, y, H, suffix):
    """Is there W ∈ W' and a back-door path from W to y in G ∖ X, d-connected given
    W ∖ {W}, whose part after its last node in H is `suffix`? Returns (found, re-entry):
    re-entry means that some such path leaves H and comes back before its last H node."""
    GX = Graph([v for v in G.obs if v not in X],
               {u: tuple(c for c in cs if c not in X) for u, cs in G.lat.items()},
               {(a, b) for (a, b) in G.edges if a not in X and b not in X})
    def nbrs(v):
        return [a for a in GX.parents(v)] + [c for c in GX.children(v)]
    found, reentry = False, False
    for W in Wp:
        Z = set(Ws) - {W}
        def ok(path):
            for i in range(1, len(path) - 1):
                a, v, b = path[i - 1], path[i], path[i + 1]
                pv = GX.parents(v)
                if a in pv and b in pv:
                    if not (GX.desc({v}) & Z):
                        return False
                elif v in Z:
                    return False
            return True
        def dfs(path):
            nonlocal found, reentry
            v = path[-1]
            if v == y:
                hs = [i for i, n in enumerate(path) if n in H]
                if hs and path[hs[-1]:] == suffix and ok(path):
                    found = True
                    if any(n not in H for n in path[:hs[-1]]):
                        reentry = True
                return
            for n in (GX.parents(v) if len(path) == 1 else nbrs(v)):
                if n not in path:
                    dfs(path + [n])
        dfs([W])
    return found, reentry


def random_instance(rng, sname):
    s = STRUCTS[sname]
    G = struct_graph(s)
    H0 = G.desc(s["F"]) & G.anc(s["Wp"])
    targets = [v for v in G.obs if v in H0 and v not in s["X"]]
    Yp = rng.choice(targets)
    k = rng.choice([1, 2, 3])
    seq = [Yp] + [f"q{i}" for i in range(1, k)] + ["y"]
    G.obs += seq[1:]
    types = [rng.choice(["->", "<-", "<->"]) for _ in range(k)]
    suffix, P, Ws, chain_into_H = [Yp], set(seq[1:]), set(s["Wp"]), False
    for i, t in enumerate(types):
        a, b = seq[i], seq[i + 1]
        if t == "->":
            G.edges.add((a, b))
        elif t == "<-":
            G.edges.add((b, a))
        else:
            G.lat[f"s{i}"] = (a, b); suffix.append(f"s{i}"); P.add(f"s{i}")
        suffix.append(b)
    for i in range(1, k):
        if types[i - 1] in ("->", "<->") and types[i] in ("<-", "<->"):   # collider
            q, opt = seq[i], rng.choice(["inW", "toH", "toNewW", "viaC"])
            if opt == "inW":
                Ws.add(q)
            elif opt == "toNewW":
                G.obs.append(f"n{i}"); G.edges.add((q, f"n{i}")); Ws.add(f"n{i}"); P.add(f"n{i}")
            elif opt == "toH":
                G.edges.add((q, rng.choice(targets))); chain_into_H = True
            else:
                G.obs.append(f"c{i}"); P.add(f"c{i}"); chain_into_H = True
                G.edges |= {(q, f"c{i}"), (f"c{i}", rng.choice(targets))}
    if rng.random() < 0.5 and len(targets) >= 2:                       # an excursion
        h1, h2 = rng.sample(targets, 2)
        if rng.random() < 0.5:
            G.obs.append("e"); G.edges |= {("e", h1), ("e", h2)}
        else:
            G.lat["e"] = (h1, h2)
    if not G.acyclic():
        return "cyclic"
    H = G.desc(s["F"]) & G.anc(s["Wp"])
    if H != H0 or any(len([c for c in G.children(v) if c in H]) > 1 for v in H if v in G.obs):
        return "not in normal form"
    if not is_hedge(G, s["F"], s["Fs"], s["X"], s["Wp"], s["forest"]):
        return "no hedge"
    found, reentry = witness(G, s["X"], s["Wp"], Ws, "y", H, suffix)
    if not found:
        return "p is no witness"
    for w in sorted(Ws):            # a supergraph: y <-> W where W lacks a back-door path
        if dsep(G, {w}, {"y"}, set(s["X"]) | (Ws - {w}), cut_in=s["X"], cut_out={w}):
            G.lat[f"t_{w}"] = ("y", w)
    assert theorem6_hyp(G, s["X"], "y", sorted(Ws))
    M = G.induced(H | P)
    Wpp = [w for w in sorted(Ws) if w in M.obs]
    eq, wpos, differ, _ = evaluate(M, s["F"], s["Fs"], P, s["X"], "y", Wpp)
    base = {"<-": "(a)", "->": "(b)", "<->": "(c)"}[types[0]]
    rec = base_b_recursion(G, s, Yp, seq, P, Wpp, H) if base == "(b)" else None
    return base, chain_into_H, reentry, eq, wpos, differ, rec, (sname, sorted(G.edges),
                                                                  sorted(G.lat.items()), sorted(Ws))


def base_b_recursion(G, s, Yp, seq, P, Wpp, H):
    """First level of the paper's recursion in base case (b). G' drops the outgoing arrow of
    Y' in H; F and F' with that arrow removed from the forest should be a hedge for
    P_x(q1, w'') (q1 = the first node of p, root set R ∪ {Y'}). The Theorem 2 models of
    that hedge in G', on H1 = De(F) ∩ An({q1} ∪ W''), are extended along the rest of p as
    in the appendix, and P_x(y | w'' = 0) is compared. Returns (hedge, obs equal,
    differs on y, P_x(w''=0) equal)."""
    out = [c for c in G.children(Yp) if c in H]
    Gp = Graph(G.obs, G.lat, G.edges - {(Yp, c) for c in out})
    forest = s["forest"] - {(Yp, c) for c in out}
    T = {seq[1]} | set(Wpp)
    hedge = is_hedge(Gp, s["F"], s["Fs"], s["X"], T, forest)
    H1 = Gp.desc(s["F"]) & Gp.anc(T)
    M = Gp.induced(H1 | P)
    W2 = [w for w in Wpp if w in M.obs]
    eq, _, differ, _ = evaluate(M, s["F"], s["Fs"], P - H1, s["X"], "y", W2)
    r1, r2, coins = construct(M, s["F"], s["Fs"], P - H1)
    Xs = [x for x in M.obs if x in s["X"]]
    wsame = True
    for xs in itertools.product([0, 1], repeat=len(Xs)):
        D1, D2 = (dist(M, r, coins, dict(zip(Xs, xs))) for r in (r1, r2))
        pw = [sum(pr for k, pr in D.items() if all(k[M.obs.index(w)] == 0 for w in W2))
              for D in (D1, D2)]
        wsame &= pw[0] == pw[1]
    return hedge, eq, differ, wsame


print()
print("== 4. Random search (seed 20261127, 4000 tries per hedge structure) ==")
print("Skipped tries: cyclic graphs, p meeting H = De(F) ∩ An(W') or an H node with two")
print("children in H (not the paper's normal form), and p that is not the last segment of")
print("a d-connected back-door path from some W ∈ W'. Where some W has no back-door path,")
print("a latent y <-> W is added to G (not to the models), so that Theorem 6 applies.")
print("Failures of base (a) and (c) are listed; base (b) is reported for information.")
rng = random.Random(20261127)
for sname in ["bow", "three", "tail", "tworoots", "exC"]:
    stats, skipped, bad = {}, {}, []
    for _ in range(4000):
        r = random_instance(rng, sname)
        if isinstance(r, str):
            skipped[r] = skipped.get(r, 0) + 1
            continue
        base, cin, reent, eq, wpos, differ, rec, inst = r
        key = (base, cin, reent)
        st = stats.setdefault(key, [0, 0, 0, 0, 0, 0, 0, 0])
        st[0] += 1; st[1] += eq; st[2] += wpos; st[3] += differ
        if rec:
            for j in range(4):
                st[4 + j] += rec[j]
        if base != "(b)" and not (eq and wpos and differ) and len(bad) < 2:
            bad.append(inst)
    print(f"-- {sname}: skipped {dict(sorted(skipped.items()))}")
    for (base, cin, reent), (n, e, w, d, rh, re, rd, rw) in sorted(stats.items()):
        print(f"   base {base} chain into H={fmt(cin):3s} re-entry={fmt(reent):3s}: "
              f"{n:4d} instances, obs-equal {e:4d}, w''=0 positive {w:4d}, differs {d:4d}")
        if base == "(b)":
            print(f"      recursion, first level in G': new hedge {rh:4d}, obs-equal {re:4d}, "
                  f"differs on y {rd:4d}, P_x(w''=0) equal {rw:4d}")
    for inst in bad:
        print("   failure:", inst)


print()
print("== 5. The first node of p is a collider in W'': three + a -> q1 <- y, W = {w, q1} ==")
# The back-door path w <- a -> q1 <- y is open given q1. Base case (b) as written takes
# "Y" := q1, the first node outside H, but q1 ∈ W'' is observed, so P_x(q1 | w'') says
# nothing; and the hedge it yields in G' (root set {w, a}) is not smaller than H.
s3 = STRUCTS["three"]
G5 = Graph(s3["obs"] + ["q1", "y"], s3["lat"], s3["edges"] | {("a", "q1"), ("y", "q1")})
H5 = G5.desc(s3["F"]) & G5.anc(s3["Wp"])
print("Theorem 6 applies:", fmt(theorem6_hyp(G5, s3["X"], "y", ["w", "q1"])),
      "  p is a witness:", fmt(witness(G5, s3["X"], s3["Wp"], {"w", "q1"}, "y", H5,
                                       ["a", "q1", "y"])[0]))
eq, wpos, differ, pos = evaluate(G5.induced(H5 | {"q1", "y"}), s3["F"], s3["Fs"], {"q1", "y"},
                                 s3["X"], "y", ["w", "q1"])
print(f"direct extension: obs-equal={fmt(eq)} differs={fmt(differ)}")
rh, re_, rd, rw = base_b_recursion(G5, s3, "a", ["a", "q1", "y"], {"q1", "y"}, ["w", "q1"], H5)
print(f"G' (a -> w dropped), hedge with roots {{w, a}}, models extended along p: "
      f"hedge={fmt(rh)} obs-equal={fmt(re_)} differs on y={fmt(rd)}")
print("H1 = De(F) ∩ An(q1, w) in G' is not smaller than H:",
      fmt(not (Graph(G5.obs, G5.lat, G5.edges - {("a", "w")}).desc(s3["F"]) &
               Graph(G5.obs, G5.lat, G5.edges - {("a", "w")}).anc({"q1", "w"})) < H5))


print()
print("== 6. Positivity: linear parity models with noise ==")
# The models above are deterministic, so their observed law is not positive. The Lean
# definition IdentifiableCond compares only models with a positive observed law. Search
# all models in which every observed node is the parity of a subset of its parents, plus
# noise 1/4 at any subset of the nodes; keep those with a positive observed law, and
# count the laws with two models that differ on P_x(y | W = w) for some x and w.
def subsets(l):
    for k in range(len(l) + 1):
        yield from (list(c) for c in itertools.combinations(l, k))


def linear_search(G, X, y, Ws):
    groups = {}
    for choice, ns in itertools.product(
            itertools.product(*(list(subsets(G.parents(v))) for v in G.obs)), subsets(G.obs)):
        rd, noise = dict(zip(G.obs, choice)), {v: Fr(1, 4) for v in ns}
        P = dist(G, rd, set(), noise=noise)
        if len(P) != 2 ** len(G.obs):
            continue
        D = []
        for xs in itertools.product([0, 1], repeat=len(X)):
            Dx = dist(G, rd, set(), dict(zip(X, xs)), noise)
            for wv in itertools.product([0, 1], repeat=len(Ws)):
                iy, iw = G.obs.index(y), [G.obs.index(w) for w in Ws]
                sel = [(k, p) for k, p in Dx.items() if all(k[i] == b for i, b in zip(iw, wv))]
                D.append(sum(p for k, p in sel if k[iy] == 0) / sum(p for k, p in sel))
        groups.setdefault(tuple(sorted(P.items())), set()).add(tuple(D))
    return len(groups), sum(1 for g in groups.values() if len(g) > 1)


for name, G, Ws in [] if os.environ.get("IDC_SKIP_SLOW") else [("bow + y -> w", Graph(["x", "w", "y"], {"u1": ("x", "w")},
                                           {("x", "w"), ("y", "w")}), ["w"]),
                    ("section 5 graph", G5, ["w", "q1"]),
                    ("Example C + y -> z", Graph(STRUCTS["exC"]["obs"] + ["y"],
                                                 STRUCTS["exC"]["lat"],
                                                 STRUCTS["exC"]["edges"] | {("y", "z")}),
                     ["z"])]:
    n, d = linear_search(G, ["x"], "y", Ws)
    print(f"{name}: {n} observed laws, {d} with two models that differ on P_x(y | W)")


# =======================================================================================
# Part B, step 3: the repaired construction (docs/design-idc.md, "The repaired
# construction"). Sections 7-11.
# =======================================================================================
# A linear network over ZMod 2: every bit is the sum of its parent bits plus an independent
# noise bit of law p (p = 0: none, p = 1/2: a fair coin). Laws are computed exactly by
# summing out hidden bits as soon as no later bit reads them.
class Net:
    def __init__(self):
        self.bits, self.idx, self.obs = [], {}, []

    def add(self, name, parents=(), p=Fr(0), observed=True):
        assert name not in self.idx and all(q in self.idx for q in parents), name
        self.idx[name] = len(self.bits)
        self.bits.append((name, tuple(parents), Fr(p)))
        if observed:
            self.obs.append(name)

    def law(self, keep=None, do=None):
        """The exact law of the bits `keep` (default: all observed bits), with the bits in
        `do` set to constants."""
        keep = list(self.obs if keep is None else keep)
        do = do or {}
        last = {}
        for i, (n, ps, _) in enumerate(self.bits):
            for q in ps:
                last[q] = i
        active, states = [], {(): Fr(1)}
        for i, (n, ps, p) in enumerate(self.bits):
            pos = [active.index(q) for q in ps]
            new = {}
            for st, pr in states.items():
                base = sum(st[j] for j in pos) % 2
                if n in do:
                    opts = [(do[n], Fr(1))]
                elif p == 0:
                    opts = [(base, Fr(1))]
                else:
                    opts = [(base, 1 - p), (1 - base, p)]
                for val, q in opts:
                    k = st + (val,)
                    new[k] = new.get(k, 0) + pr * q
            active.append(n)
            drop = [j for j, m in enumerate(active) if m not in keep and last.get(m, -1) <= i]
            if drop:
                kept = [j for j in range(len(active)) if j not in drop]
                active = [active[j] for j in kept]
                red = {}
                for st, pr in new.items():
                    k = tuple(st[j] for j in kept)
                    red[k] = red.get(k, 0) + pr
                new = red
            states = new
        perm = [active.index(n) for n in keep]
        out = {}
        for st, pr in states.items():
            if pr:
                k = tuple(st[j] for j in perm)
                out[k] = out.get(k, 0) + pr
        return keep, out


def cut_out(G, S):
    """G without the edges out of the observed nodes in S."""
    return Graph(G.obs, G.lat, {(a, b) for (a, b) in G.edges if a not in S})


def id_fail(G, Y, X, Vs=None):
    """The ID algorithm of Shpitser and Pearl as a check: None if P_x(Y) is identifiable in
    G, else the pair (S, T) of observed sets at which it fails (line 5): F = S ⊊ F' = T."""
    Vs = set(G.obs) if Vs is None else set(Vs)
    Y, X = set(Y), set(X) & Vs
    sub = lambda S: Graph([v for v in G.obs if v in S],
                          {u: tuple(c for c in cs if c in S) for u, cs in G.lat.items()
                           if len([c for c in cs if c in S]) >= 2},
                          {(a, b) for (a, b) in G.edges if a in S and b in S})
    def ccomp(S):
        H = sub(S)
        comps, seen = [], set()
        for v in sorted(S):
            if v in seen:
                continue
            c, todo = {v}, [v]
            while todo:
                n = todo.pop()
                for cs in H.lat.values():
                    if n in cs:
                        for m in cs:
                            if m not in c:
                                c.add(m); todo.append(m)
            seen |= c; comps.append(frozenset(c))
        return comps
    if not X:
        return None
    H = sub(Vs)
    A = H.anc(Y) & Vs
    if A != Vs:
        return id_fail(G, Y, X & A, A)
    Hx = Graph(H.obs, {u: cs for u, cs in H.lat.items()}, {(a, b) for (a, b) in H.edges
                                                           if b not in X})
    Hx.lat = {u: tuple(c for c in cs if c not in X) for u, cs in H.lat.items()}
    Wn = (Vs - X) - Hx.anc(Y)
    if Wn:
        return id_fail(G, Y, X | Wn, Vs)
    comps = ccomp(Vs - X)
    if len(comps) > 1:
        for S in comps:
            r = id_fail(G, S, Vs - S, Vs)
            if r:
                return r
        return None
    S = comps[0]
    CG = ccomp(Vs)
    if len(CG) == 1:
        return (set(S), set(Vs))
    if S in CG:
        return None
    Sp = next(C for C in CG if S <= C)
    return id_fail(G, Y, X & Sp, Sp)


def with_lat(G, S):
    return set(S) | {u for u, cs in G.lat.items() if set(cs) <= set(S)}


def is_hedge_lean(G, F, Fb, X, Y):
    """`Hedge.IsHedge G U X Y F Fb` (Lean naming: F ⊊ Fb, F avoids X, Fb meets X)."""
    R = {v for v in F if v in G.obs and not any((v, w) in G.edges for w in F)}
    def reach(S):
        ok = set(R)
        changed = True
        while changed:
            changed = False
            for v in S:
                if v not in ok and any(c in ok for c in G.children(v) if c in S):
                    ok.add(v); changed = True
        return ok == set(S)
    def cconn(S):
        ob = [v for v in S if v in G.obs]
        comp, todo = {ob[0]}, [ob[0]]
        while todo:
            n = todo.pop()
            for u, cs in G.lat.items():
                if u in S and n in cs:
                    for c in cs:
                        if c not in comp:
                            comp.add(c); todo.append(c)
        return set(ob) <= comp
    Gx = Graph(G.obs, {u: tuple(c for c in cs if c not in X) for u, cs in G.lat.items()},
               {(a, b) for (a, b) in G.edges if b not in X})
    return (F < Fb and reach(F) and reach(Fb) and not (F & X) and bool(Fb & X)
            and R <= Gx.anc(Y) and cconn(F) and cconn(Fb))


def product_models(G, F, Fb, X, Yt):
    """The product models `Hedge.PM.MP` (Hedge/ParityModels, Hedge/Product) for the hedge
    F ⊊ Fb for P_x(Yt) in G, as two Nets (two = false, true). The data are chosen as in
    `hedge_data`: r0 = ρ an observed root, a spanning tree of the observed nodes of F (then
    of Fb) through latents, `nxt` a child in Fb (in F for nodes of F), `tp` a child in
    AY. Coordinates that no kernel reads and that are uniform or pure noise in both models
    (the a of observed nodes outside Fb, the b of observed nodes outside AY) are left out;
    they are independent and have the same law in both models. Returns the two Nets and,
    for every observed node, the names of its coordinate bits."""
    RO = sorted(v for v in F if v in G.obs and not any((v, w) in G.edges for w in F))
    r0 = rho = RO[0]
    par, lat = {}, {}
    def grow(S):
        done = {rho} | set(par)
        changed = True
        while changed:
            changed = False
            for u in sorted(G.lat):
                cs = G.lat[u]
                if u not in S or not set(cs) <= S:
                    continue
                for c in cs:
                    for p in cs:
                        if c != p and p in done and c not in done and c in S:
                            par[c], lat[c] = p, u; done.add(c); changed = True
    grow(F); grow(Fb)
    Fo, Fbo = {v for v in F if v in G.obs}, {v for v in Fb if v in G.obs}
    assert Fbo == {rho} | set(par), "spanning tree"
    nxt = {}
    for v in sorted(Fbo - set(RO)):
        nxt[v] = next(w for w in G.children(v) if w in Fb and (v not in F or w in F))
    Gx = Graph(G.obs, {u: tuple(c for c in cs if c not in X) for u, cs in G.lat.items()},
               {(a, b) for (a, b) in G.edges if b not in X})
    AY = {v for v in Gx.anc(Yt) if v in G.obs}
    tp = {v: next(w for w in sorted(G.children(v)) if w in AY and w not in X)
          for v in sorted(AY - set(Yt))}
    nets = []
    for two in (False, True):
        N = Net()
        for c in sorted(par):
            N.add(f"t:{c}", (), Fr(1, 2), observed=False)
        for v in G.topo():
            if v in Fbo:
                sc = (lambda w: w in F) if (two and v in F) else (lambda w: True)
                ps = ([f"t:{v}"] if v != rho else []) + \
                     [f"t:{c}" for c in sorted(par) if par[c] == v and sc(c)] + \
                     [f"a:{w}" for w in sorted(nxt) if nxt[w] == v and sc(w)]
                N.add(f"a:{v}", ps, Fr(1, 4) if v == r0 else Fr(0))
            if v in AY:
                ps = ([f"a:{v}"] if v in RO else []) + \
                     [f"b:{w}" for w in sorted(tp) if tp[w] == v]
                N.add(f"b:{v}", ps, Fr(1, 4))
        nets.append(N)
    coords = {v: [n for n in (f"a:{v}", f"b:{v}") if n in nets[0].idx] for v in G.obs}
    return nets, coords


def marg(keep, P, S):
    """The marginal of a law P over the bit list `keep` on the sublist S."""
    ix = [keep.index(s) for s in S]
    out = {}
    for k, p in P.items():
        kk = tuple(k[i] for i in ix)
        out[kk] = out.get(kk, 0) + p
    return out


def do_values(coords, X):
    xs = [b for x in sorted(X) for b in coords.get(x, [])]
    return [dict(zip(xs, vals)) for vals in itertools.product([0, 1], repeat=len(xs))]


def bd_paths(G, X, W0, Ws, Y, cap=4):
    """Up to `cap` back-door paths from W0 to a node of Y, d-connected given
    X ∪ W ∖ {W0} in G without the edges into X and out of W0 (X removed), shortest
    first; with every collider, the shortest directed path from it to W ∖ {W0} (stopping
    at the first node of W). A path is a list of nodes, latents included."""
    H = cut_out(Graph([v for v in G.obs if v not in X],
                      {u: tuple(c for c in cs if c not in X) for u, cs in G.lat.items()},
                      {(a, b) for (a, b) in G.edges if a not in X and b not in X}), {W0})
    Z = set(Ws) - {W0}
    out = []
    def chain(c):
        prev, todo, seen = {c: None}, [c], {c}
        while todo:
            n = todo.pop(0)
            if n in Z:
                pth = [n]
                while prev[pth[-1]] is not None:
                    pth.append(prev[pth[-1]])
                return pth[::-1]
            for m in H.children(n):
                if m not in seen and m in H.obs:
                    seen.add(m); prev[m] = n; todo.append(m)
        return None
    def dfs(path):
        v = path[-1]
        if v in Y and len(path) > 1:
            chains, ok = {}, True
            for i in range(1, len(path) - 1):
                a, n, b = path[i - 1], path[i], path[i + 1]
                pv = H.parents(n)
                if a in pv and b in pv:
                    ch = chain(n)
                    if ch is None:
                        ok = False; break
                    chains[i] = ch
                elif n in Z:
                    ok = False; break
            if ok:
                out.append((list(path), chains))
            return
        for n in (H.parents(v) if len(path) == 1 else H.parents(v) + H.children(v)):
            if n not in path and (n in H.obs or n in H.lat):
                dfs(path + [n])
    dfs([W0])
    out.sort(key=lambda pc: len(pc[0]))
    return out[:cap]


def brook(nets, coords, Ws, X, allowed):
    """Brook's lemma, computed: all (x, W0, g, w) where the odds
    P_x(W = w) / P_x(W = w + g at W0) differ between the two models, for translations g
    supported on the coordinates `allowed[W0]` (those no kernel reads)."""
    Wb = [b for w in sorted(Ws) for b in coords[w]]
    found = []
    for do in do_values(coords, X):
        P = [N.law(Wb, do)[1] for N in nets]
        if P[0] == P[1]:
            continue
        for W0 in sorted(Ws):
            ix = [Wb.index(b) for b in allowed[W0]]
            for g in itertools.product([0, 1], repeat=len(ix)):
                if not any(g):
                    continue
                for w in P[0]:
                    w2 = list(w)
                    for i, gi in zip(ix, g):
                        w2[i] ^= gi
                    w2 = tuple(w2)
                    if P[0][w] * P[1][w2] != P[1][w] * P[0][w2]:
                        found.append((do, W0, dict(zip(allowed[W0], g)), w))
                        break
    return found


def switch_models(G, nets, coords, W0, g, path, chains):
    """The repaired construction, case 2: the hedge models plus a path channel on `path`
    and its collider chains; W0's value is translated by δ·g, δ the bit W0 receives from
    the path. Returns the two Nets, the target bit at the end of the path, and the bits
    at the nodes of W that the path adds."""
    rank = {v: i for i, v in enumerate(G.topo())}
    k = len(path) - 1
    pb = []                                    # (rank, name, parents, p, observed)
    name = {j: (f"l{j}" if path[j] in G.lat else f"d{j}:{path[j]}") for j in range(1, k + 1)}
    for j in range(1, k + 1):
        if path[j] in G.lat:
            pb.append((-1, name[j], (), Fr(1, 2), False))
    for j in range(1, k + 1):
        v = path[j]
        if v in G.lat:
            continue
        ins = [name[i] for i in (j - 1, j + 1) if 1 <= i <= k and (
            path[i] in G.lat or (path[i], v) in G.edges)]
        pb.append((rank[v], name[j], tuple(ins), Fr(1, 4), True))
    extra_W = []
    for j, ch in chains.items():
        prevb = name[j]
        for i, c in enumerate(ch[1:], 1):
            nb = f"c{j}.{i}:{c}"
            pb.append((rank[c], nb, (prevb,), Fr(1, 4), True))
            prevb = nb
        extra_W.append(prevb if len(ch) > 1 else name[j])
    delta = name[1]
    target = name[k]
    ren = {n: "h" + n for n in coords[W0] if g.get(n)}   # W0's value before the switch
    out = []
    for N in nets:
        M = Net()
        items = [(-1 if n.startswith("t:") else rank[n.split(":", 1)[1]], n, ps, p,
                  n in N.obs) for (n, ps, p) in N.bits] + pb
        items.sort(key=lambda t: (t[0], 0 if t[1][:2] in ("a:", "b:", "t:") else 1))
        for (_, n, ps, p, o) in items:
            M.add(ren.get(n, n), [ren.get(q, q) for q in ps], p, observed=o and n not in ren)
        for n in ren:                                     # the switch: + δ·g, read by no one
            M.add(n, (ren[n], delta), Fr(0))
        out.append(M)
    return out, target, extra_W


def roots_reads(G, F, Fb, Ws):
    """The W nodes that a kernel of the product models reads: the observed non-roots of
    Fb (each is read by its `nxt` child). All other W nodes are read by no kernel, and the
    b coordinate of a W node is never read (tails stop at W)."""
    RO = {v for v in F if v in G.obs and not any((v, w) in G.edges for w in F)}
    return {v for v in Fb if v in G.obs and v not in RO} & set(Ws)


def check_switch(G, X, Y, Ws, full_obs_cap=15, path_cap=3):
    """Case 2 of the repaired construction on one instance. Returns a dict of results."""
    r = {"case": 2}
    hf = id_fail(G, Ws, X)
    F, Fb = with_lat(G, hf[0]), with_lat(G, hf[1])
    r["Lean hedge"] = is_hedge_lean(G, F, Fb, set(X), set(Ws))
    nets, coords = product_models(G, F, Fb, set(X), set(Ws))
    k1, P1 = nets[0].law()
    r["hedge obs-equal"] = P1 == nets[1].law()[1]
    r["hedge positive"] = len(P1) == 2 ** len(k1)
    readW = roots_reads(G, F, Fb, Ws)
    r["read W"] = bool(readW)
    allowed = {w: (coords[w] if w not in readW else [f"b:{w}"]) for w in Ws}
    Cr = [f"a:{w}" for w in sorted(readW)]
    r["lemma U"] = all(len(L) == 2 ** len(Cr) and set(L.values()) == {Fr(1, 2 ** len(Cr))}
                       for N in nets for do in do_values(coords, X)
                       for L in [N.law(Cr, do)[1]]) if Cr else True
    found = brook(nets, coords, Ws, X, allowed)
    r["W0 found"] = bool(found)
    runs = []
    for W0 in sorted({f[1] for f in found}):
        do, _, gvec, _ = next(f for f in found if f[1] == W0)
        for path, chains in bd_paths(G, X, W0, Ws, Y, path_cap):
            M, target, extra = switch_models(G, nets, coords, W0, gvec, path, chains)
            Wbits = [b for w in sorted(Ws) for b in coords[w]] + extra
            if len(M[0].obs) <= full_obs_cap:
                kk, Q1 = M[0].law()
                eq, pos = Q1 == M[1].law()[1], len(Q1) == 2 ** len(kk)
            else:
                eq = pos = None
            L = [m.law(Wbits + [target], do)[1] for m in M]
            differ = False
            for key in set(L[0]) | set(L[1]):
                w = key[:-1]
                c = [sum(Lq.get(w + (t,), 0) for t in (0, 1)) for Lq in L]
                if c[0] and c[1] and L[0].get(w + (0,), 0) * c[1] != L[1].get(w + (0,), 0) * c[0]:
                    differ = True; break
            runs.append((W0, len(path), bool(chains), eq, pos, differ))
    r["runs"] = runs
    return r


def check_carry(G, X, Y, Ws):
    """The countermodels for P_x(Y ∪ W) (Lean product models on G), unchanged: does
    P_x(Y | W) differ? (Case 1 of the repaired construction; in case 2 a baseline.)"""
    hf = id_fail(G, set(Y) | set(Ws), X)
    if hf is None:
        return None
    F, Fb = with_lat(G, hf[0]), with_lat(G, hf[1])
    nets, coords = product_models(G, F, Fb, set(X), set(Y) | set(Ws))
    Wb = [b for w in sorted(Ws) for b in coords[w]]
    Yb = [b for y in sorted(Y) for b in coords[y]]
    for do in do_values(coords, X):
        L = [N.law(Wb + Yb, do)[1] for N in nets]
        Pw = [marg(Wb + Yb, Lq, Wb) for Lq in L]
        for key in set(L[0]) | set(L[1]):
            w = key[:len(Wb)]
            if L[0].get(key, 0) * Pw[1].get(w, 0) != L[1].get(key, 0) * Pw[0].get(w, 0):
                return True
    return False


def show(name, G, X, Y, Ws):
    case = "1" if id_fail(G, Ws, X) is None else "2"
    carry = check_carry(G, X, Y, Ws)
    line = f"{name:34s} case {case}  carry-over differs={fmt(carry)}"
    if case == "2":
        r = check_switch(G, X, Y, Ws)
        line += (f"  Lean hedge={fmt(r['Lean hedge'])} hedge obs-equal="
                 f"{fmt(r['hedge obs-equal'])} W0 found={fmt(r['W0 found'])}")
        for (W0, n, ch, eq, pos, d) in r.get("runs", []):
            line += f"\n{'':36s}W0={W0}, path of {n} nodes{' with chains' if ch else ''}: " \
                    f"obs-equal={fmt(eq)} positive={fmt(pos)} differs={fmt(d)}"
    print(line)


print()
print("== 7. The repaired construction on the hand-made graphs ==")
print("case 1: P_x(W) identifiable, the countermodels for P_x(Y ∪ W) are used unchanged.")
print("case 2: product models for P_x(W) on G; Brook's lemma gives W0 and a translation g of")
print("coordinates no kernel reads; a path channel and the switch at W0. 'carry-over': the")
print("countermodels for")
print("P_x(Y ∪ W), unchanged, compared on P_x(Y | W) (the baseline in case 2).")
def hand(sname, extra_obs, extra_lat, extra_edges):
    s = STRUCTS[sname]
    return Graph(s["obs"] + extra_obs, dict(s["lat"], **extra_lat),
                 s["edges"] | set(extra_edges)), set(s["X"])
for name, sname, eo, el, ee, Ws in [
        ("base (a): y -> w", "bow", ["y"], {}, [("y", "w")], ["w"]),
        ("w <- c -> y", "bow", ["c", "y"], {}, [("c", "w"), ("c", "y")], ["w"]),
        ("w <- c <- y", "bow", ["c", "y"], {}, [("c", "w"), ("y", "c")], ["w"]),
        ("w <- c <-> y", "bow", ["c", "y"], {"s1": ("c", "y")}, [("c", "w")], ["w"]),
        ("w <-> y", "bow", ["y"], {"s1": ("w", "y")}, [], ["w"]),
        ("w <- c -> d <- y, d ∈ W", "bow", ["c", "d", "y"], {},
         [("c", "w"), ("c", "d"), ("y", "d")], ["w", "d"]),
        ("chain d -> w2 back into H", "bow2", ["c", "d", "y"], {},
         [("c", "w"), ("c", "d"), ("y", "d"), ("d", "w2")], ["w", "w2"]),
        ("re-entry r1 <- e -> r2 <-> y", "tworoots", ["e", "y"], {"s1": ("r2", "y")},
         [("e", "r1"), ("e", "r2")], ["r1", "r2"]),
        ("base (b): a -> y", "three", ["y"], {}, [("a", "y")], ["w"]),
        ("collider a -> q1 <- y, q1 ∈ W", "three", ["q1", "y"], {},
         [("a", "q1"), ("y", "q1")], ["w", "q1"]),
        ("Example C + y -> z", "exC", ["y"], {}, [("y", "z")], ["z"])]:
    G, X = hand(sname, eo, el, ee)
    assert theorem6_hyp(G, X, "y", Ws), name
    show(name, G, X, {"y"}, Ws)


def rebuild(inst):
    sname, edges, lats, Ws = inst
    lat = dict(lats)
    obs = set(STRUCTS[sname]["obs"]) | {"y"} | {v for e in edges for v in e} | \
        {c for cs in lat.values() for c in cs}
    return Graph(sorted(obs - set(lat)), lat, set(edges)), set(STRUCTS[sname]["X"]), set(Ws)


N8 = 100
print()
print(f"== 8. The repaired construction on the random families of section 4 (the first {N8}")
print("tries per structure, same seed) ==")
print("runs: one per W0 found by Brook's lemma and back-door path from it (at most 3);")
print("obs-equal and positive are computed on the full observed law when it has at most 15")
print("bits, otherwise only on the hedge models.")
rng = random.Random(20261127)
for sname in ["bow", "three", "tail", "tworoots", "exC"]:
    st = dict(n=0, read=0, lemU=0, lean=0, heq=0, w0=0, runs=0, full=0, eq=0, pos=0,
              differ=0, carry=0)
    bad = []
    for t in range(4000):
        r = random_instance(rng, sname)
        if t >= N8 or isinstance(r, str):
            continue
        G, X, Ws = rebuild(r[-1])
        if id_fail(G, Ws, X) is None:
            continue
        st["n"] += 1
        st["carry"] += bool(check_carry(G, X, {"y"}, Ws))
        res = check_switch(G, X, {"y"}, Ws)
        st["read"] += res["read W"]
        st["lemU"] += res["lemma U"]
        st["lean"] += bool(res.get("Lean hedge"))
        st["heq"] += bool(res.get("hedge obs-equal")) and bool(res.get("hedge positive"))
        st["w0"] += bool(res.get("W0 found"))
        for (W0, n, ch, eq, pos, d) in res.get("runs", []):
            st["runs"] += 1; st["differ"] += d
            if eq is not None:
                st["full"] += 1; st["eq"] += eq; st["pos"] += pos
            if not d or eq is False or pos is False:
                bad.append((r[-1], W0))
        if not res.get("runs"):
            bad.append((r[-1], None))
    print(f"-- {sname}: {st['n']} instances (case 2), {st['read']} with a read W node, lemma U "
          f"{st['lemU']}; Lean hedge "
          f"{st['lean']}, hedge models equal and positive {st['heq']}, W0 found {st['w0']}; "
          f"{st['runs']} runs: differs {st['differ']}; full law checked in {st['full']}: "
          f"obs-equal {st['eq']}, positive {st['pos']}; carry-over differs {st['carry']}")
    for b in bad[:2]:
        print("   failure:", b)


print()
print("== 9. Case 1: P_x(W) identifiable, P_x(Y ∪ W) not (seed 20261128) ==")
rng = random.Random(20261128)
for sname in ["bow", "three", "tail", "tworoots", "exC"]:
    s = STRUCTS[sname]
    Yt = set(s["Wp"])
    cnt, ok, skip = 0, 0, 0
    for _ in range(300):
        G = struct_graph(s)
        H = [v for v in G.obs if v not in s["X"]]
        Ws = set()
        for i in range(rng.choice([1, 2])):
            w = f"w{i}"
            G.obs.append(w); Ws.add(w)
            opt = rng.choice(["lat", "child", "both", "parent+lat"])
            if opt in ("lat", "both", "parent+lat"):
                G.lat[f"v{i}"] = (w, rng.choice(H))
            if opt in ("child", "both"):
                G.edges.add((rng.choice(H), w))
            if opt == "parent+lat":
                G.edges.add((w, rng.choice(H)))
        hyp = all(not dsep(G, {w}, Yt, set(s["X"]) | (Ws - {w}), cut_in=s["X"], cut_out={w})
                  for w in Ws)
        if not (G.acyclic() and hyp and id_fail(G, Ws, s["X"]) is None
                and id_fail(G, Yt | Ws, s["X"]) is not None):
            skip += 1
            continue
        cnt += 1
        ok += bool(check_carry(G, s["X"], Yt, Ws))
    print(f"-- {sname} (Y = {sorted(Yt)}): {cnt} instances, P_x(Y | W) differs in {ok} "
          f"({skip} tries skipped)")


print()
print("== 10. The graph lemma: P_x(W) not identifiable in G => not in G without the edges")
print("out of W (random graphs, seed 20261129) ==")
rng = random.Random(20261129)
tested, held, lean_ok = 0, 0, 0
for _ in range(30000):
    n = rng.choice([3, 4, 5, 6])
    obs = [f"v{i}" for i in range(n)]
    edges = {(obs[i], obs[j]) for i in range(n) for j in range(i + 1, n) if rng.random() < 0.4}
    lat = {f"u{i}{j}": (obs[i], obs[j]) for i in range(n) for j in range(i + 1, n)
           if rng.random() < 0.3}
    G = Graph(obs, lat, edges)
    roles = [rng.choice("xwo") for _ in obs]
    X = {v for v, r in zip(obs, roles) if r == "x"}
    Ws = {v for v, r in zip(obs, roles) if r == "w"}
    if not X or not Ws:
        continue
    hf = id_fail(G, Ws, X)
    if hf is None:
        continue
    tested += 1
    lean_ok += is_hedge_lean(G, with_lat(G, hf[0]), with_lat(G, hf[1]), X, Ws)
    Gw = cut_out(G, Ws)
    hw = id_fail(Gw, Ws, X)
    held += hw is not None
print(f"{tested} graphs where P_x(W) is not identifiable: the ID failure is a Lean hedge in "
      f"{lean_ok}; P_x(W) is still not identifiable without the edges out of W in {held}")



def rand_graph(rng):
    n = rng.choice([3, 4, 5, 6])
    obs = [f"v{i}" for i in range(n)]
    edges = {(obs[i], obs[j]) for i in range(n) for j in range(i + 1, n) if rng.random() < 0.4}
    lat = {f"u{i}{j}": (obs[i], obs[j]) for i in range(n) for j in range(i + 1, n)
           if rng.random() < 0.3}
    roles = [rng.choice("xwo") for _ in obs]
    return (Graph(obs, lat, edges), {v for v, r in zip(obs, roles) if r == "x"},
            {v for v, r in zip(obs, roles) if r == "w"})


print()
print("== 11. Read nodes of W: Lemma U and the unread switch on random graphs (seed 20261129,")
print("the graphs of section 10), and the whole construction where W has read nodes ==")
rng = random.Random(20261129)
tot = withread = lemU = found = 0
for _ in range(30000):
    G, X, Ws = rand_graph(rng)
    if not X or not Ws:
        continue
    hf = id_fail(G, Ws, X)
    if hf is None:
        continue
    F, Fb = with_lat(G, hf[0]), with_lat(G, hf[1])
    nets, coords = product_models(G, F, Fb, X, Ws)
    readW = roots_reads(G, F, Fb, Ws)
    RO = {v for v in F if v in G.obs and not any((v, w) in G.edges for w in F)}
    S = sorted({v for v in Fb if v in G.obs} - RO - X)
    Cr = [f"a:{v}" for v in S]
    tot += 1
    withread += bool(readW)
    lemU += all(len(L) == 2 ** len(Cr) and set(L.values()) == {Fr(1, 2 ** len(Cr))}
                for N in nets for do in do_values(coords, X) for L in [N.law(Cr, do)[1]])
    allowed = {w: (coords[w] if w not in readW else [f"b:{w}"]) for w in Ws}
    found += bool(brook(nets, coords, Ws, X, allowed))
print(f"{tot} graphs with P_x(W) not identifiable, {withread} with a read node of W: the a of "
      f"the observed non-roots of F' outside X are independent fair bits under every do(x) "
      f"in both models in {lemU}; Brook's lemma finds a switch on unread coordinates in "
      f"{found}")

print("The counterexample of section 10, with y <-> w for every w ∈ W:")
Gc = Graph(["v0", "v1", "v2", "v3", "v4", "v5", "y"],
           {"u03": ("v0", "v3"), "u12": ("v1", "v2"), "u14": ("v1", "v4"),
            "u25": ("v2", "v5"), "u34": ("v3", "v4"), "s1": ("y", "v1"), "s4": ("y", "v4"),
            "s5": ("y", "v5")},
           {("v0", "v5"), ("v1", "v2"), ("v2", "v3"), ("v3", "v5"), ("v4", "v5")})
print("P_x(W) identifiable without the edges out of W:",
      fmt(id_fail(cut_out(Gc, {"v1", "v4", "v5"}), {"v1", "v4", "v5"}, {"v3"}) is None))
show("section 10 graph + y", Gc, {"v3"}, {"y"}, {"v1", "v4", "v5"})

rng = random.Random(20261130)
st = dict(n=0, read=0, w0=0, runs=0, full=0, eq=0, pos=0, differ=0)
bad = []
while st["n"] < 100:
    G, X, Ws = rand_graph(rng)
    if not X or not Ws:
        continue
    G.obs.append("y")
    for w in sorted(Ws):
        opt = rng.choice(["lat", "edge", "via"])
        if opt == "lat":
            G.lat[f"s_{w}"] = ("y", w)
        elif opt == "edge":
            G.edges.add(("y", w))
        else:
            others = [v for v in G.obs if v not in X and v not in Ws and v != "y"]
            if not others:
                G.lat[f"s_{w}"] = ("y", w); continue
            v = rng.choice(others)
            G.lat[f"s_{w}"] = ("y", v); G.lat[f"r_{w}"] = (v, w)
    if not G.acyclic() or not theorem6_hyp(G, X, "y", sorted(Ws)):
        continue
    hf = id_fail(G, Ws, X)
    if hf is None:
        continue
    F, Fb = with_lat(G, hf[0]), with_lat(G, hf[1])
    if not roots_reads(G, F, Fb, Ws):
        continue
    st["n"] += 1
    res = check_switch(G, X, {"y"}, Ws, path_cap=2)
    st["read"] += res["read W"]; st["w0"] += res["W0 found"]
    for (W0, n, ch, eq, pos, d) in res["runs"]:
        st["runs"] += 1; st["differ"] += d
        if eq is not None:
            st["full"] += 1; st["eq"] += eq; st["pos"] += pos
        if not d or eq is False or pos is False:
            bad.append((sorted(X), sorted(Ws), sorted(G.edges), G.lat, W0))
    if not res["runs"]:
        bad.append((sorted(X), sorted(Ws), sorted(G.edges), G.lat, None))
print(f"random graphs with a read node of W and y attached (seed 20261130): {st['n']} "
      f"instances, W0 found {st['w0']}; {st['runs']} runs: differs {st['differ']}; full law "
      f"checked in {st['full']}: obs-equal {st['eq']}, positive {st['pos']}")
for b in bad[:2]:
    print("   failure:", b)

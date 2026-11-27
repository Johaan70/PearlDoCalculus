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

All probabilities are exact fractions, computed by summing over all latent and coin bits.
Run with: python3 verification/idc_checks.py (about five minutes; section 6 is the slow one).
"""
import itertools
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


for name, G, Ws in [("bow + y -> w", Graph(["x", "w", "y"], {"u1": ("x", "w")},
                                           {("x", "w"), ("y", "w")}), ["w"]),
                    ("section 5 graph", G5, ["w", "q1"]),
                    ("Example C + y -> z", Graph(STRUCTS["exC"]["obs"] + ["y"],
                                                 STRUCTS["exC"]["lat"],
                                                 STRUCTS["exC"]["edges"] | {("y", "z")}),
                     ["z"])]:
    n, d = linear_search(G, ["x"], "y", Ws)
    print(f"{name}: {n} observed laws, {d} with two models that differ on P_x(y | W)")

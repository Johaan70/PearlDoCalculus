#!/usr/bin/env python3
"""Exhaustive check of the monotonicity lemma of the IDC check (docs/design-idc.md, step 2).

Movable(M, W', w): w in W' and Y is d-separated from {w} by (X | M) | (W' - {w}) in G
without the edges into X | M and out of w (the side condition of DoCalc.Derives.rule2).

Checked, by brute force (d-separation by enumerating all simple paths of the skeleton):

  (A) owner's form: if w and w' are both movable from (M, W'), then w is movable from
      (M | {w'}, W' - {w'});
  (B) stronger form proved in Lean: if w is movable from (M, W') and w' in W', w' != w,
      then w is movable from (M | {w'}, W' - {w'});
  (C) the statements of step 2: every M reachable from (0, W) by single moves is a subset
      of the set M* computed by rounds (every movable vertex at once, |W| rounds), M* is
      reachable, and no vertex is movable from (M*, W - M*).

Search space: every DAG on n vertices whose edges go from lower to higher index (every
DAG is isomorphic to one of these), and every assignment of the vertices to disjoint
roles. For (A) and (B) the roles are X, Y, M, W', other; for (C) they are X, Y, W,
other. The vertices with role "other" play the latents: they never occur in a set.
n = 1..5 exhaustively; n = 6 and 7 by 100 000 random instances each, fixed seed.
A self test checks d-separation on a chain and a collider, and a negative control
checks that a false variant (dropping w' from the conditioning set without intervening
on it) does fail.

Usage: python3 idc_monotone_check.py [n_full=5] [samples=100000]
"""
import itertools, random, sys
from functools import lru_cache

def parse_args():
    full = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    return full, samples

class Graph:
    def __init__(self, n, edges):
        self.n = n
        self.edges = frozenset(edges)

def cut(edges, into, outof):
    return frozenset((u, v) for (u, v) in edges if v not in into and u not in outof)

@lru_cache(maxsize=None)
def ancestors(n, edges, Z):
    anc = set(Z)
    changed = True
    while changed:
        changed = False
        for (u, v) in edges:
            if v in anc and u not in anc:
                anc.add(u); changed = True
    return frozenset(anc)

@lru_cache(maxsize=None)
def open_path(n, edges, Z, x, y):
    """Return an open simple path from x to y given Z, or None."""
    adj = {v: [] for v in range(n)}
    for (u, v) in edges:
        adj[u].append(v); adj[v].append(u)
    anZ = ancestors(n, edges, Z)
    def is_open(path):
        for i in range(1, len(path) - 1):
            a, b, c = path[i - 1], path[i], path[i + 1]
            collider = (a, b) in edges and (c, b) in edges
            if collider:
                if b not in anZ: return False
            else:
                if b in Z: return False
        return True
    stack = [[x]]
    while stack:
        p = stack.pop()
        last = p[-1]
        if last == y:
            if is_open(p): return tuple(p)
            continue
        for nb in adj[last]:
            if nb not in p:
                stack.append(p + [nb])
    return None

def dsep_set(n, edges, Z, A, B):
    for a in A:
        for b in B:
            if open_path(n, edges, Z, a, b) is not None:
                return False, (a, b, open_path(n, edges, Z, a, b))
    return True, None

def movable(n, edges, X, Y, M, Wp, w):
    if w not in Wp: return False
    g = cut(cut(edges, X | M, frozenset()), frozenset(), frozenset([w]))
    Z = (X | M) | (Wp - {w})
    return dsep_set(n, g, frozenset(Z), Y, frozenset([w]))[0]

def all_dags(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        yield frozenset(p for k, p in enumerate(pairs) if mask >> k & 1)

def check_monotone(n, edges, X, Y, M, Wp, stats):
    for w in Wp:
        mw = movable(n, edges, X, Y, M, Wp, w)
        for w2 in Wp:
            if w2 == w: continue
            after = movable(n, edges, X, Y, M | {w2}, Wp - {w2}, w)
            mw2 = movable(n, edges, X, Y, M, Wp, w2)
            if mw and mw2:
                stats['A'] += 1
                if not after:
                    return ('A', w, w2)
            if mw:
                stats['B'] += 1
                if not after:
                    return ('B', w, w2)
    return None

def rounds(n, edges, X, Y, W):
    M = frozenset()
    for _ in range(len(W)):
        Wp = W - M
        M = M | frozenset(w for w in Wp if movable(n, edges, X, Y, M, Wp, w))
    return M

def check_maximal(n, edges, X, Y, W, stats):
    Mstar = rounds(n, edges, X, Y, W)
    seen = {frozenset()}
    todo = [frozenset()]
    while todo:
        M = todo.pop()
        Wp = W - M
        for w in Wp:
            if movable(n, edges, X, Y, M, Wp, w):
                M2 = M | {w}
                if M2 not in seen:
                    seen.add(M2); todo.append(M2)
    stats['C'] += 1
    if not all(M <= Mstar for M in seen): return 'reachable set not inside M*'
    if Mstar not in seen: return 'M* not reachable'
    if any(movable(n, edges, X, Y, Mstar, W - Mstar, w) for w in W - Mstar):
        return 'a vertex is movable from M*'
    return None

def report(kind, n, edges, roles, detail):
    print('COUNTEREXAMPLE', kind, 'n =', n, 'edges =', sorted(edges), 'roles =', roles, detail)
    sys.exit(1)

def run_instance(n, edges, roles5, roles4, stats):
    if roles5 is not None:
        X = frozenset(v for v in range(n) if roles5[v] == 'X')
        Y = frozenset(v for v in range(n) if roles5[v] == 'Y')
        M = frozenset(v for v in range(n) if roles5[v] == 'M')
        Wp = frozenset(v for v in range(n) if roles5[v] == 'W')
        r = check_monotone(n, edges, X, Y, M, Wp, stats)
        if r: report(r[0], n, edges, roles5, r)
    if roles4 is not None:
        X = frozenset(v for v in range(n) if roles4[v] == 'X')
        Y = frozenset(v for v in range(n) if roles4[v] == 'Y')
        W = frozenset(v for v in range(n) if roles4[v] == 'W')
        r = check_maximal(n, edges, X, Y, W, stats)
        if r: report('C', n, edges, roles4, r)

def self_test():
    """d-separation on the chain 0 -> 1 -> 2 and the collider 0 -> 2 <- 1 -> 3."""
    chain = frozenset([(0, 1), (1, 2)])
    assert open_path(3, chain, frozenset(), 0, 2) is not None
    assert open_path(3, chain, frozenset([1]), 0, 2) is None
    coll = frozenset([(0, 2), (1, 2), (2, 3)])
    assert open_path(4, coll, frozenset(), 0, 1) is None
    assert open_path(4, coll, frozenset([2]), 0, 1) is not None
    assert open_path(4, coll, frozenset([3]), 0, 1) is not None
    print('self test: d-separation on a chain and a collider as expected')

def negative_control(n):
    """A false variant must fail: dropping w' from the conditioning set without
    intervening on it does not keep w movable. Returns the number of failures."""
    fails = 0
    for edges in all_dags(n):
        for roles in itertools.product('XYMWo', repeat=n):
            X = frozenset(v for v in range(n) if roles[v] == 'X')
            Y = frozenset(v for v in range(n) if roles[v] == 'Y')
            M = frozenset(v for v in range(n) if roles[v] == 'M')
            Wp = frozenset(v for v in range(n) if roles[v] == 'W')
            for w in Wp:
                if not movable(n, edges, X, Y, M, Wp, w): continue
                for w2 in Wp - {w}:
                    if not movable(n, edges, X, Y, M, Wp - {w2}, w): fails += 1
    return fails

def main():
    full, samples = parse_args()
    self_test()
    nc = negative_control(4)
    print(f'negative control (n = 4): the false variant fails in {nc} cases, as it should')
    assert nc > 0
    for n in range(1, full + 1):
        stats = {'A': 0, 'B': 0, 'C': 0}
        count = 0
        for edges in all_dags(n):
            for roles in itertools.product('XYMWo', repeat=n):
                run_instance(n, edges, roles, None, stats); count += 1
            for roles in itertools.product('XYWo', repeat=n):
                run_instance(n, edges, None, roles, stats); count += 1
        open_path.cache_clear(); ancestors.cache_clear()
        print(f'n = {n}: exhaustive, {count} instances; (A) {stats["A"]} cases, '
              f'(B) {stats["B"]} cases, (C) {stats["C"]} cases; no counterexample')
        sys.stdout.flush()
    rng = random.Random(20261126)
    for n in (6, 7):
        stats = {'A': 0, 'B': 0, 'C': 0}
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for _ in range(samples):
            p = rng.choice([0.3, 0.5, 0.7])
            edges = frozenset(e for e in pairs if rng.random() < p)
            roles5 = tuple(rng.choice('XYMWWo') for _ in range(n))
            roles4 = tuple(rng.choice('XYWWo') for _ in range(n))
            run_instance(n, edges, roles5, roles4, stats)
            if len(open_path.cache_info()) and open_path.cache_info().currsize > 2000000:
                open_path.cache_clear(); ancestors.cache_clear()
        open_path.cache_clear(); ancestors.cache_clear()
        print(f'n = {n}: {samples} random instances (seed 20261126); (A) {stats["A"]} cases, '
              f'(B) {stats["B"]} cases, (C) {stats["C"]} cases; no counterexample')
        sys.stdout.flush()
    print('ALL CHECKS PASSED')

if __name__ == '__main__':
    main()

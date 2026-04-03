"""
Livelock Characterization via Directed Cycle Homology over Z
=============================================================

ALGEBRA
-------
    H_1(H*, Z) = Z^k,  k = |E| - |V| + c

    Basis: k Z-independent simple cycles B_0,...,B_{k-1}
    (positive cone of Grigor'yan path homology [GLMY 2012])

PROPAGATION ON SIMPLE CYCLES
-----------------------------
By the bounded witness theorem (Lemma 9), the propagation E maps
each simple cycle C of length n to a simple cycle C' of the same
length n, bijectively with a cyclic shift z^s.

The full action of E is:

    For each simple cycle C (in particular each basis cycle B_i):
      E(C) = { (z^s_1, n, decomposition_1),
               (z^s_2, n, decomposition_2), ... }

    where:
      - z^s  = cyclic shift (rotation of the target cycle)
      - n    = length of source and target (always equal)
      - decomposition = Z-linear combination of basis cycles
                        representing the target simple cycle

    When shadows have unique witnesses: each C has exactly one image.
    When shadows have multiple witnesses: multiple images (non-determinism).

NOTE ON rho(E):
    The k x k matrix rho(E) on the homological basis is well-defined
    only when E maps each basis cycle to a SINGLE basis cycle.
    For m >= 4, most simple-cycle-to-simple-cycle mappings produce
    COMPOUND Z-decompositions (97% for Agreement m=4).
    rho(E) is therefore NOT the right object for the general case.
    The full E_rel structure below captures the complete action.

CIRCULATION LAW (on simple cycles):
    Starting from C_0, propagation produces a chain of same-length
    simple cycles with shifts s_i. A livelock on ring size K exists
    iff exists q >= 1: C_{qK} = C_0 and
    |E| = sum_{i=0}^{qK-1} s_i  (mod n).

DEPENDENCIES: livelock_complete.py
"""

import sys, os
for p in ['.', '/mnt/user-data/outputs', os.path.dirname(os.path.abspath(__file__))]:
    if p not in sys.path: sys.path.insert(0, p)

from livelock_complete import (
    fixed_point, find_simple_cycles, enabling_walks, check_self_disabling
)
from collections import defaultdict


# ===================================================================
#  Graph construction
# ===================================================================

def _build_H(L):
    Kf = sorted(L); n = len(Kf)
    H = [[0]*n for _ in range(n)]
    for i, ti in enumerate(Kf):
        for j, tj in enumerate(Kf):
            if tj[1] == ti[2]: H[i][j] = 1
    return H, Kf


def refine_H(H, Kf, L_pred):
    n = len(Kf); ow = {(t[1], t[2]) for t in L_pred}
    Hr = [[0]*n for _ in range(n)]; dead = []
    for i in range(n):
        for j in range(n):
            if not H[i][j]: continue
            s = (Kf[i][0], Kf[j][0])
            if s in ow: Hr[i][j] = 1
            else: dead.append((Kf[i], Kf[j], s))
    return Hr, dead


def connected_components(H, n):
    adj = [set() for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if H[i][j]: adj[i].add(j); adj[j].add(i)
    visited = [False]*n; count = 0
    for s in range(n):
        if visited[s]: continue
        count += 1; stack = [s]
        while stack:
            v = stack.pop()
            if visited[v]: continue
            visited[v] = True
            for u in adj[v]:
                if not visited[u]: stack.append(u)
    return count


def build_edges(H, Kf):
    edges = []; e2i = {}
    for i in range(len(Kf)):
        for j in range(len(Kf)):
            if H[i][j]:
                e = (Kf[i], Kf[j])
                e2i[e] = len(edges)
                edges.append(e)
    return edges, e2i


def cycle_to_zvec(cycle, e2i, m):
    v = [0] * m
    N = len(cycle)
    for k in range(N):
        e = (cycle[k], cycle[(k+1) % N])
        if e in e2i: v[e2i[e]] += 1
    return v


# ===================================================================
#  Z-linear algebra
# ===================================================================

def z_row_reduce(vectors):
    if not vectors: return [], [], 0
    n = len(vectors); m = len(vectors[0])
    mat = [v[:] for v in vectors]
    origin = list(range(n)); pivots = []
    for col in range(m):
        best = -1
        for r in range(len(pivots), n):
            if mat[r][col] != 0:
                if best < 0 or abs(mat[r][col]) < abs(mat[best][col]): best = r
        if best < 0: continue
        pr = len(pivots)
        mat[best], mat[pr] = mat[pr], mat[best]
        origin[best], origin[pr] = origin[pr], origin[best]
        if mat[pr][col] < 0: mat[pr] = [-x for x in mat[pr]]
        changed = True
        while changed:
            changed = False
            for r in range(n):
                if r == pr or mat[r][col] == 0: continue
                q = mat[r][col] // mat[pr][col]
                if q != 0:
                    mat[r] = [mat[r][j] - q * mat[pr][j] for j in range(m)]
                    changed = True
                if mat[r][col] != 0 and abs(mat[r][col]) < abs(mat[pr][col]):
                    mat[r], mat[pr] = mat[pr], mat[r]
                    origin[r], origin[pr] = origin[pr], origin[r]
                    if mat[pr][col] < 0: mat[pr] = [-x for x in mat[pr]]
                    changed = True
        pivots.append(pr)
    return [origin[pr] for pr in pivots], mat, len(pivots)


def z_decompose(target, basis_vecs):
    k = len(basis_vecs); m = len(target)
    if k == 0: return None
    aug = [bv[:] + [1 if i == j else 0 for j in range(k)] for i, bv in enumerate(basis_vecs)]
    aug.append(target[:] + [0]*k)
    nr = k + 1; nc = m + k; pmap = {}
    for col in range(m):
        best = -1
        for r in range(len(pmap), nr):
            if aug[r][col] != 0:
                if best < 0 or abs(aug[r][col]) < abs(aug[best][col]): best = r
        if best < 0: continue
        pr = len(pmap)
        aug[best], aug[pr] = aug[pr], aug[best]
        if aug[pr][col] < 0: aug[pr] = [-x for x in aug[pr]]
        changed = True
        while changed:
            changed = False
            for r in range(nr):
                if r == pr or aug[r][col] == 0: continue
                q = aug[r][col] // aug[pr][col]
                if q != 0:
                    aug[r] = [aug[r][j] - q * aug[pr][j] for j in range(nc)]
                    changed = True
                if aug[r][col] != 0 and abs(aug[r][col]) < abs(aug[pr][col]):
                    aug[r], aug[pr] = aug[pr], aug[r]
                    if aug[pr][col] < 0: aug[pr] = [-x for x in aug[pr]]
                    changed = True
        pmap[col] = pr
    last = aug[nr - 1]
    if any(last[j] != 0 for j in range(m)): return None
    coeffs = [-last[m + i] for i in range(k)]
    check = [0] * m
    for i in range(k):
        for j in range(m): check[j] += coeffs[i] * basis_vecs[i][j]
    return coeffs if check == target else None


def canonical_zero(cycle):
    """Position of canonical zero: transition with minimum (pred, own, written)."""
    N = len(cycle)
    best = 0
    for k in range(1, N):
        if cycle[k] < cycle[best]:
            best = k
    return best


def forward_shift_canonical(source, raw_target):
    """Compute forward shift between source and its constructed forward target.

    By construction, raw_target[k].pred = source[k].written, so raw step k
    of the target corresponds to raw step k of the source.

    The shift is the offset between canonical zeros:
      s = (p_source - p_target) mod n

    When source is at canonical step 0 (raw p_source), target is also at
    raw p_source, which is canonical step (p_source - p_target) mod n = s.
    """
    N = len(source)
    if len(raw_target) != N:
        return None
    p_s = canonical_zero(source)
    p_t = canonical_zero(raw_target)
    return (p_s - p_t) % N


def find_forward_target(source_cycle, L_star):
    """Construct the forward target cycle directly from L*.

    Given source cycle C at P_r, P_{r+1}'s cycle has:
      - pred sequence = C's written sequence
      - H-edge condition: each transition's own = previous written

    After construction, verifies equivariance: E∘H = H∘E at every edge.
    Returns list of valid equivariant target cycles."""
    N = len(source_cycle)
    written_seq = [t[2] for t in source_cycle]

    by_pred_own = defaultdict(list)
    for t in L_star:
        by_pred_own[(t[0], t[1])].append(t)

    # Also build shadow witness lookup for equivariance check
    # E maps edge (t_i, t_j) via shadow (t_i.pred, t_j.pred) → witness (own, written) = (t_i.pred, t_j.pred)
    ow_index = defaultdict(list)
    for t in L_star:
        ow_index[(t[1], t[2])].append(t)

    raw_targets = []

    def build(pos, chain):
        if pos == N:
            if chain[-1][2] == chain[0][1]:  # closure: last.written == first.own
                raw_targets.append(tuple(chain))
            return
        pred_needed = written_seq[pos]
        own_needed = chain[-1][2]  # H-edge: own = prev.written
        for t in by_pred_own.get((pred_needed, own_needed), []):
            if t not in chain:
                chain.append(t)
                build(pos + 1, chain)
                chain.pop()

    # Try each starting transition with pred = written_seq[0]
    for t in L_star:
        if t[0] == written_seq[0]:
            build(1, [t])

    # Verify equivariance: E∘H = H∘E for every edge
    verified = []
    for tgt in raw_targets:
        ok = True
        for k in range(N):
            k1 = (k + 1) % N
            # Source edge: source[k] →_H source[k1]
            # E maps source[k] → tgt[k] and source[k1] → tgt[k1]
            # E∘H: source[k] →_H source[k1] →_E tgt[k1]
            # H∘E: source[k] →_E tgt[k] →_H tgt[k1]
            # Check: tgt[k] →_H tgt[k1] means tgt[k1].own == tgt[k].written
            if tgt[k1][1] != tgt[k][2]:
                ok = False
                break
            # Check: E(source[k]) = tgt[k] means tgt[k].pred == source[k].written
            if tgt[k][0] != source_cycle[k][2]:
                ok = False
                break
            # Check: shadow witness exists in L* for edge (source[k], source[k1])
            shadow = (source_cycle[k][0], source_cycle[k1][0])
            if not ow_index.get(shadow):
                ok = False
                break
        if ok:
            verified.append(tgt)

    if len(raw_targets) != len(verified):
        # Some targets failed equivariance — shouldn't happen if construction is correct
        import sys
        print(f"  WARNING: {len(raw_targets)} raw targets, {len(verified)} passed equivariance",
              file=sys.stderr)

    return verified


def fmt_decomp(ic, k):
    """Format a Z-decomposition as a string."""
    parts = []
    for j in range(k):
        c = ic[j]
        if c == 0: continue
        if c == 1: parts.append(f"B[{j}]")
        elif c == -1: parts.append(f"-B[{j}]")
        else: parts.append(f"{c}*B[{j}]")
    return ' + '.join(parts) if parts else '0'


# ===================================================================
#  Main computation
# ===================================================================

def compute_algebra(L_star,L_o_star=None, verbose=True):
    """Compute the action of E on simple cycles in H_1(H*, Z)."""

    if L_o_star is None: L_o_star = L_star
    H_raw, Kf = _build_H(L_star)
    H, dead = refine_H(H_raw, Kf, L_star)
    edges, e2i = build_edges(H, Kf)
    nE = len(edges); nV = len(Kf)
    nC = connected_components(H, nV)
    k_expected = nE - nV + nC

    if verbose:
        print(f"\n  H*: |V|={nV}, |E|={nE}, components={nC}")
        print(f"  k = |E|-|V|+c = {nE}-{nV}+{nC} = {k_expected}")
        if dead: print(f"  Dead H-edges: {len(dead)}")

    # Shadow analysis
    ow = defaultdict(list)
    for t in L_star: ow[(t[1], t[2])].append(t)
    is_det = all(len(v) == 1 for v in ow.values())
    if verbose:
        print(f"  Shadow deterministic: {is_det}")
        if not is_det:
            for key in sorted(ow):
                if len(ow[key]) > 1:
                    print(f"    ({key[0]},{key[1]}): {len(ow[key])} witnesses")

    # Simple cycles and basis
    simple = find_simple_cycles(H, Kf)
    svecs = [cycle_to_zvec(sc, e2i, nE) for sc in simple]
    if verbose: print(f"  Simple cycles: {len(simple)}")

    idx = sorted(range(len(simple)), key=lambda i: len(simple[i]))
    bo, _, _ = z_row_reduce([svecs[i] for i in idx])
    bidx = [idx[i] for i in bo]
    bcyc = [simple[i] for i in bidx]
    bvec = [svecs[i] for i in bidx]
    k = len(bcyc)

    if verbose:
        tag = "OK" if k == k_expected else f"MISMATCH (expected {k_expected})"
        print(f"  Z-basis: k = {k} {tag}")
        for i, bc in enumerate(bcyc):
            print(f"    B[{i}] (len={len(bc)}): "
                  f"{' -> '.join(f'({t[0]},{t[1]},{t[2]})' for t in bc)} ->")

    # Decompose all simple cycles; build reverse lookup
    scoords = {}
    coord_to_si = {}
    for si, sv in enumerate(svecs):
        c = z_decompose(sv, bvec)
        if c is not None:
            scoords[si] = c
            coord_to_si[tuple(c)] = si
    if verbose:
        print(f"  Decomposition: {len(scoords)}/{len(simple)} "
              f"{'ALL' if len(scoords) == len(simple) else 'INCOMPLETE'}")

    # ── Forward propagation of each basis cycle ──
    # For each B[i], compute what P_{r+1} executes when P_r executes B[i]
    if verbose:
        print(f"\n  Forward propagation E(B[i]):")
        print(f"  B[i] at P_r  --E-->  (z^s, target) at P_{{r+1}}")

    E_rel = {}
    for bi, bc in enumerate(bcyc):
        n_i = len(bc)
        mappings = []

        # Construct all forward targets directly from L*
        fwd_targets = find_forward_target(bc, L_o_star)

        seen = set()
        for ft in fwd_targets:
            # Decompose forward target in basis
            ft_vec = cycle_to_zvec(ft, e2i, nE)
            ft_decomp = z_decompose(ft_vec, bvec)
            if ft_decomp is None: continue
            key = tuple(ft_decomp)
            if key in seen: continue
            seen.add(key)

            # Compute forward shift via canonical zero positions
            fs = forward_shift_canonical(bc, ft)

            mappings.append({
                'coords': ft_decomp,
                'shift': fs,
                'target_cycle': ft,
                'target_len': len(ft),
            })

        E_rel[bi] = mappings

        if verbose:
            print(f"\n  B[{bi}] (n={n_i}):")
            if not mappings:
                print(f"    *** NO FORWARD TARGETS FOUND ***")
            for mp in mappings:
                decomp = fmt_decomp(mp['coords'], k)
                s = mp['shift']
                sh = f"z^{s}" if s is not None else "?"
                print(f"    --E--> ({sh}, n={mp['target_len']}, {decomp})")

    # ── Summary statistics ──
    is_func = all(len(v) == 1 for v in E_rel.values())
    n_total = sum(len(v) for v in E_rel.values())

    if verbose:
        print(f"\n  Summary:")
        print(f"    E deterministic (unique shadow witnesses): {is_det}")
        print(f"    E functional (single image per basis cycle): {is_func}")
        print(f"    Total arrows: {n_total}")

    return {
        'k': k, 'E_rel': E_rel,
        'basis_cycles': bcyc, 'basis_vecs': bvec,
        'simple': simple, 'simple_coords': scoords,
        'is_deterministic': is_det, 'is_functional': is_func,
    }


def test(name, T, T_o=None):
    if T_o is None: T_o = T
    print(f"\n{'='*70}")
    print(f"  {name}")
    print(f"{'='*70}")
    sd, viol = check_self_disabling(T)
    if not sd: print(f"  T Not self-disabling: {viol}"); return
    if T_o != T:
        sd, viol = check_self_disabling(T_o)
        if not sd: print(f"  T_o Not self-disabling: {viol}"); return
    has_ll, k0, ko = fixed_point(T, T_o, verbose=False)
    if not has_ll: print("  FREE"); return
    print(f"  L0* = {sorted(k0)}")
    if T_o != T: print(f"  Lo* = {sorted(ko)}")
    if T_o != T: return compute_algebra(k0, ko), compute_algebra(ko), compute_algebra(ko, k0)
    return compute_algebra(k0)


if __name__ == "__main__":
    m = 4
    test("3-Coloring det (m=3)",
         [(v,w,(w+1)%m) for v in range(m) for w in range(m) if w==v])
    test("Leader (m=3)", [(v,v,(v+1)%m) for v in range(m)])
    test("Simple 2-cycle (m=2)", [(0,1,0),(1,0,1)])
    test("Non-det Sum-Not-2 (m=3)",
         [(m-1-v,v,w) for v in range(m) for w in range(m) if v!=w])
    test("Maximal agreement (m=3)",
         [(v,w,v) for v in range(m) for w in range(m) if v!=w])
    test("Non-det coloring (m=3)",
         [(v,v,w) for v in range(m) for w in range(m) if v!=w])

    test("Non-det w+2 (m=4)",
         [(v,w,(w+2)%m) for v in range(m) for w in range(m) if v==w or w==(v+1)%m])
    offset = 3
    test ("Non-det offset (m=4)",
          [((v + m - offset)%m, v, w) for v in range(m) for w in range(m) if v != w])
    m = 4
    test ("Dijkstra (m=50)",
          [(v,v, (v+1)%m) for v in range(m)],
          [(w, v, w) for v in range(m) for w in range(m) if w != v])

    m = 6
    test("Asymmetric Converse-Dijkstra (m=6)",
         [(w,v,w) for v in range(m) for w in range(m) if v != w],
         [(v,v,(v+1)%m) for v in range(m)])

    print(f"\n{'='*70}\n  DONE\n{'='*70}")

"""
Livelock Detection for Parameterized Self-Disabling Unidirectional Rings
════════════════════════════════════════════════════════════════════════

Complete self-contained implementation:

  1. DECISION ALGORITHM (Theorem 6 of the paper)
     - Shadow-constrained fixed point Φ on transition set T
     - Symmetric (Algorithm 1) and (1,1)-asymmetric (Algorithm 2)
     - O(|T|³) time, independent of ring size K

  2. CIRCULATION LAW
     - Resolves valid (|E|, K) pairs: H^|E| ∩ E^K ≠ ∅

  3. PER-CYCLE STRUCTURAL ANALYSIS
     - Finds all simple cycles in refined H*(L*)
     - Per-cycle shadow computation and enabling walk enumeration
     - Conjunction decomposition (walk → simple cycles)
     - Bipartite permutation: E maps cycles to cycles bijectively via shifts

  4. SELF-DISABLING VALIDATION
     - Rejects invalid protocols upfront

Foundation: Farahat (2012), Farahat (2026 preprint), Klinkhamer & Ebnenasir (2019).
"""

from math import gcd
from functools import reduce
from collections import defaultdict, Counter


# ═══════════════════════════════════════════════════════════════
#  MATRIX OPERATIONS
# ═══════════════════════════════════════════════════════════════

def bmm(A, B):
    """Boolean matrix multiply (square)."""
    n = len(A)
    C = [[0]*n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k]:
                for j in range(n):
                    if B[k][j]: C[i][j] = 1
    return C

def bmm_rect(A, B, ra, ca, cb):
    """Boolean matrix multiply (rectangular): A[ra×ca] * B[ca×cb]."""
    C = [[0]*cb for _ in range(ra)]
    for i in range(ra):
        for k in range(ca):
            if A[i][k]:
                for j in range(cb):
                    if B[k][j]: C[i][j] = 1
    return C

def is_bij(M):
    n = len(M)
    return (all(sum(M[i]) == 1 for i in range(n)) and
            all(sum(M[i][j] for i in range(n)) == 1 for j in range(n)))

def lcm2(a, b): return a * b // gcd(a, b)
def lcm_list(lst): return reduce(lcm2, lst) if lst else 1


# ═══════════════════════════════════════════════════════════════
#  VALIDATION
# ═══════════════════════════════════════════════════════════════

def check_self_disabling(T):
    """
    Self-disabling: for every (v,w,w') in T, no (v,w',_) exists in T.
    Returns (is_valid, first_violation_or_None).
    """
    for v1, w1, wp1 in T:
        for v2, w2, wp2 in T:
            if v2 == v1 and w2 == wp1:
                return False, ((v1,w1,wp1), (v2,w2,wp2))
    return True, None


# ═══════════════════════════════════════════════════════════════
#  CORE GRAPH OPERATIONS: SCC, SHADOWS, FILTER
# ═══════════════════════════════════════════════════════════════

def scc_cycles(T, witness_ow=None):
    """Transitions on directed cycles in H-graph (t_j.own == t_i.written).
    If witness_ow is provided, only keep H-edges whose shadow
    (t_i.pred, t_j.pred) is in witness_ow (edge-aware pruning)."""
    T = list(T); n = len(T)
    if n == 0: return frozenset()
    H = {i: [] for i in range(n)}
    for i, (vi,wi,wpi) in enumerate(T):
        for j, (vj,wj,wpj) in enumerate(T):
            if wj == wpi:
                if witness_ow is None or (vi, vj) in witness_ow:
                    H[i].append(j)
    # Kosaraju's SCC
    visited = [False]*n; order = []
    def dfs1(u):
        stk = [(u,0)]
        while stk:
            v,s = stk.pop()
            if s == 0:
                if visited[v]: continue
                visited[v] = True; stk.append((v,1))
                for w in H[v]:
                    if not visited[w]: stk.append((w,0))
            else: order.append(v)
    for i in range(n):
        if not visited[i]: dfs1(i)
    Hr = {i:[] for i in range(n)}
    for i in range(n):
        for j in H[i]: Hr[j].append(i)
    visited2 = [False]*n; comps = []
    def dfs2(u):
        comp = []; stk = [u]
        while stk:
            v = stk.pop()
            if visited2[v]: continue
            visited2[v] = True; comp.append(v)
            for w in Hr[v]: stk.append(w)
        return comp
    for u in reversed(order):
        if not visited2[u]: comps.append(dfs2(u))
    on_cycle = set()
    for c in comps:
        if len(c) > 1:
            for v in c: on_cycle.add(v)
        elif c and c[0] in H[c[0]]: on_cycle.add(c[0])
    return frozenset(T[i] for i in on_cycle)


def shadows(P, witness_ow=None):
    """Global shadow set: {(t_i.pred, t_j.pred) for every H-edge (t_i→t_j) in P}.
    If witness_ow is provided, only include shadows from witnessed H-edges."""
    return {(vi, vj) for (vi,wi,wpi) in P for (vj,wj,wpj) in P
            if wj == wpi and (witness_ow is None or (vi, vj) in witness_ow)}


def filter_T(T, req):
    """Keep transitions whose (own, written) ∈ req."""
    return frozenset((v,w,wp) for (v,w,wp) in T if (w,wp) in req)


# ═══════════════════════════════════════════════════════════════
#  H AND E MATRIX CONSTRUCTION
# ═══════════════════════════════════════════════════════════════

def build_H_E(kernel_from, kernel_to=None):
    """
    H[i][j] = 1  iff  t_j.own == t_i.written   (pseudolivelock edges)
    E[k][j] = 1  iff  ∃ H-edge (t_i→t_j): t_k.own==t_i.pred ∧ t_k.written==t_j.pred
    Returns: (Kf_from, Kf_to, H, E)
    """
    Kf = sorted(kernel_from)
    Kt = sorted(kernel_to) if kernel_to else Kf
    nf, nt = len(Kf), len(Kt)
    ow_f = defaultdict(list)
    for k, tk in enumerate(Kf):
        ow_f[(tk[1], tk[2])].append(k)
    H = [[0]*nt for _ in range(nt)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if tj[1] == ti[2]: H[i][j] = 1
    E = [[0]*nt for _ in range(nf)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if not H[i][j]: continue
            for k in ow_f.get((ti[0], tj[0]), []):
                E[k][j] = 1
    return Kf, Kt, H, E


def _build_H(L):
    """Quick H adjacency + sorted Kf."""
    Kf = sorted(L); n = len(Kf)
    H = [[0]*n for _ in range(n)]
    for i,ti in enumerate(Kf):
        for j,tj in enumerate(Kf):
            if tj[1] == ti[2]: H[i][j] = 1
    return H, Kf


# ═══════════════════════════════════════════════════════════════
#  FIXED POINT: DECISION ALGORITHM
# ═══════════════════════════════════════════════════════════════

def phi(S, T_full):
    """One Φ iteration with edge-aware H-graph pruning.
    PL_w(Filter(T_full, Shad_w(PL_w(S)))) where _w means witnessed edges only."""
    ow_S = {(t[1], t[2]) for t in S}
    P = scc_cycles(S, witness_ow=ow_S)
    if not P: return frozenset()
    ow_P = {(t[1], t[2]) for t in P}
    sh = shadows(P, witness_ow=ow_P)
    F = filter_T(frozenset(T_full), sh)
    if not F: return frozenset()
    ow_F = {(t[1], t[2]) for t in F}
    return frozenset(scc_cycles(F, witness_ow=ow_F))


def inner_fp(L_init, T_full, verbose=False, label="T"):
    """Deflate from L_init to the greatest fixed point of Φ within T_full."""
    S = frozenset(L_init); k = 0
    while True:
        S2 = phi(S, T_full)
        if S2 == S:
            if verbose: print(f"    [{label}] fixed point at iter {k}: {len(S)} transitions")
            return S
        if verbose: print(f"    [{label}] iter {k}: removed {sorted(S - S2)}")
        S = S2; k += 1


def fixed_point(T_p0, T_other, verbose=True):
    """
    Algorithm 1 (symmetric) / Algorithm 2 ((1,1)-asymmetric).
    Returns (has_livelock, kernel_p0, kernel_other).
    """
    symmetric = (frozenset(T_p0) == frozenset(T_other))

    if symmetric:
        if verbose: print("  [Symmetric] Phi fixed point")
        L = inner_fp(frozenset(T_p0), T_p0, verbose=verbose)
        if not L:
            if verbose: print("  => FREE")
            return False, frozenset(), frozenset()
        if verbose: print(f"  => LIVELOCK: L* = {sorted(L)}")
        return True, L, L

    if verbose: print("  [Asymmetric] Joint fixed point (L_0, L_other)")
    ow_p0 = {(t[1],t[2]) for t in T_p0}
    ow_ot = {(t[1],t[2]) for t in T_other}
    L0 = frozenset(scc_cycles(frozenset(T_p0), witness_ow=ow_ot))
    Lo = frozenset(scc_cycles(frozenset(T_other), witness_ow=ow_ot))
    if not L0 or not Lo:
        if verbose: print("  => FREE (empty initial PL)")
        return False, frozenset(), frozenset()

    for outer in range(1, len(T_p0) + len(T_other) + 2):
        if verbose: print(f"  Outer {outer}: |L0|={len(L0)}, |Lo|={len(Lo)}")
        ow_Lo = {(t[1],t[2]) for t in Lo}
        Lo_new = inner_fp(filter_T(Lo, shadows(L0, witness_ow=ow_Lo)), T_other, verbose=verbose, label="Lo")
        if not Lo_new:
            if verbose: print("  => FREE (L_other emptied)")
            return False, frozenset(), frozenset()
        ow_Lo_new = {(t[1],t[2]) for t in Lo_new}
        L0_new = frozenset(scc_cycles(filter_T(frozenset(T_p0), shadows(Lo_new, witness_ow=ow_Lo_new)), witness_ow=ow_Lo_new))
        if not L0_new:
            if verbose: print("  => FREE (L_0 emptied)")
            return False, frozenset(), frozenset()
        if L0_new == L0 and Lo_new == Lo:
            if verbose: print("  => LIVELOCK: joint fixed point")
            return True, L0_new, Lo_new
        L0, Lo = L0_new, Lo_new


# ═══════════════════════════════════════════════════════════════
#  CIRCULATION LAW
# ═══════════════════════════════════════════════════════════════

def resolve_CL(kern_p0, kern_other, verbose=True):
    """Find valid (|E|, K) pairs satisfying H^|E| ∩ E^K ≠ ∅."""
    if not kern_other: return
    Ko = sorted(kern_other); K0 = sorted(kern_p0)
    no, n0 = len(Ko), len(K0)
    _, _, H, Eo = build_H_E(kern_other, kern_other)
    _, _, _, E0 = build_H_E(kern_p0, kern_other)
    _, _, _, Ex = build_H_E(kern_other, kern_p0)

    sym = (sorted(kern_p0) == sorted(kern_other))
    if verbose:
        print(f"\n  {'─'*50}")
        print(f"  Circulation Law: H^|E| ∩ E^K ≠ ∅")
        print(f"  H bij={is_bij(H)}, E_other bij={is_bij(Eo)}")

    def intersects(A, B):
        return any(A[i][j] and B[i][j] for i in range(len(A)) for j in range(len(A)))

    max_K = min(no*no + 6, 30)
    Ep = [None]
    if sym:
        c = [r[:] for r in Eo]
        for k in range(1, max_K+1):
            Ep.append([r[:] for r in c]); c = bmm(c, Eo)
    else:
        base = bmm_rect(Ex, E0, no, n0, no)
        Ep.append([r[:] for r in base]); Ep.append([r[:] for r in base])
        c = [r[:] for r in base]
        for k in range(3, max_K+1):
            c = bmm_rect(Eo, c, no, no, no); Ep.append([r[:] for r in c])

    valid = []; Hc = [r[:] for r in H]
    for e in range(1, max_K+1):
        for K in range(max(e,2), max_K+1):
            if intersects(Hc, Ep[K]): valid.append((e,K))
        if len(valid) >= 5: break
        Hc = bmm(Hc, H)

    if is_bij(H):
        cycs = _perm_cycles(H, Ko)
        if verbose:
            print(f"  H cycles: {['('+str(len(c))+'-cyc)' for c in cycs]}, "
                  f"order={lcm_list([len(c) for c in cycs])}")

    if verbose and valid:
        print(f"  Valid (|E|,K): {valid[:5]}{'...' if len(valid)>5 else ''}")
        print(f"  Min |E|={valid[0][0]}, min K={valid[0][1]}")
    elif verbose:
        print(f"  No valid (|E|,K) found up to K={max_K}")

    return {'valid': bool(valid), 'pairs': valid}


def _perm_cycles(M, labels):
    """Extract permutation cycles from a bijective matrix."""
    n = len(M)
    succ = {i: next(j for j in range(n) if M[i][j]) for i in range(n)}
    vis = set(); cycs = []
    for s in range(n):
        if s in vis: continue
        c = []; cur = s
        while cur not in vis:
            vis.add(cur); c.append(labels[cur]); cur = succ[cur]
        if c: cycs.append(c)
    return cycs


# ═══════════════════════════════════════════════════════════════
#  SIMPLE CYCLE ENUMERATION
# ═══════════════════════════════════════════════════════════════

def find_simple_cycles(H, Kf):
    """All simple cycles in directed graph H, canonicalized."""
    n = len(Kf); raw = []
    def dfs(s, u, path, pset):
        for v in range(n):
            if not H[u][v]: continue
            if v == s and len(path) >= 2: raw.append(tuple(path))
            elif v > s and v not in pset:
                pset.add(v); path.append(v)
                dfs(s, v, path, pset)
                path.pop(); pset.remove(v)
    for s in range(n): dfs(s, s, [s], {s})
    seen = set(); out = []
    for c in raw:
        canon = min(c[i:]+c[:i] for i in range(len(c)))
        if canon not in seen:
            seen.add(canon); out.append(tuple(Kf[v] for v in c))
    return out


# ═══════════════════════════════════════════════════════════════
#  PER-EDGE H* REFINEMENT
# ═══════════════════════════════════════════════════════════════

def refine_H(H, Kf, L_pred):
    """Remove H-edges whose shadow (pred_i, pred_j) has no witness in L_pred.
    In valid self-disabling protocols this is a no-op (theorem)."""
    n = len(Kf); ow = {(t[1],t[2]) for t in L_pred}
    Hr = [[0]*n for _ in range(n)]; dead = []
    for i in range(n):
        for j in range(n):
            if not H[i][j]: continue
            s = (Kf[i][0], Kf[j][0])
            if s in ow: Hr[i][j] = 1
            else: dead.append((Kf[i], Kf[j], s))
    return Hr, dead


# ═══════════════════════════════════════════════════════════════
#  PER-CYCLE SHADOW + ENABLING WALK ENUMERATION
# ═══════════════════════════════════════════════════════════════

def per_cycle_shadows(cycle):
    """Shadow for each H-edge in a simple cycle."""
    n = len(cycle)
    return [(cycle[k][0], cycle[(k+1)%n][0]) for k in range(n)]


def shadow_witnesses(shadow, T_pred):
    """Transitions in T_pred with own==shadow[0], written==shadow[1]."""
    a, b = shadow
    return [t for t in T_pred if t[1] == a and t[2] == b]


def enabling_walks(cycle_r, L_pred, H_pred, Kf_pred, max_walks=50):
    """
    Enumerate closed walks of length |cycle_r| in H*(L_pred) that enable cycle_r.
    Walk position k must be a shadow witness for H-edge (cycle_r[k], cycle_r[k+1]).
    """
    N = len(cycle_r)
    wits = []
    for k in range(N):
        s = (cycle_r[k][0], cycle_r[(k+1)%N][0])
        wits.append(shadow_witnesses(s, L_pred))
    if any(len(w)==0 for w in wits): return []

    pidx = {t:i for i,t in enumerate(Kf_pred)}
    walks = []

    def dfs(pos, path):
        if len(walks) >= max_walks: return
        if pos == N:
            li, fi = pidx.get(path[-1],-1), pidx.get(path[0],-1)
            if li >= 0 and fi >= 0 and H_pred[li][fi]:
                walks.append(tuple(path))
            return
        for w in wits[pos]:
            pi, wi = pidx.get(path[-1],-1), pidx.get(w,-1)
            if pi >= 0 and wi >= 0 and H_pred[pi][wi]:
                dfs(pos+1, path+[w])

    for w0 in wits[0]: dfs(1, [w0])
    return walks


# ═══════════════════════════════════════════════════════════════
#  CYCLE PROPAGATION MAP
# ═══════════════════════════════════════════════════════════════

def build_propagation_map(L_r, L_pred, verbose=False):
    """
    For each simple cycle in H*(L_r), find its enabling walks in H*(L_pred)
    and identify which predecessor simple cycle each walk corresponds to.

    Returns: (prop_map, cycles_r, cycles_pred)
    """
    H_r_raw, Kf_r = _build_H(L_r)
    H_p_raw, Kf_p = _build_H(L_pred)
    H_r, dead_r = refine_H(H_r_raw, Kf_r, L_pred)
    H_p, dead_p = refine_H(H_p_raw, Kf_p, L_r)

    if verbose and (dead_r or dead_p):
        for ti,tj,s in dead_r:
            print(f"  ⚠ Dead edge in P_r: {ti}->{tj} shadow {s}")
        for ti,tj,s in dead_p:
            print(f"  ⚠ Dead edge in P_pred: {ti}->{tj} shadow {s}")

    cyc_r = find_simple_cycles(H_r, Kf_r)
    cyc_p = find_simple_cycles(H_p, Kf_p)

    # Edge→cycle index lookup for predecessor
    edge2cyc = defaultdict(list)
    for ci, c in enumerate(cyc_p):
        nc = len(c)
        for k in range(nc):
            edge2cyc[(c[k], c[(k+1)%nc])].append(ci)

    prop_map = {}
    for ci, cyc in enumerate(cyc_r):
        walks = enabling_walks(cyc, L_pred, H_p, Kf_p)
        walk_info = []
        for w in walks:
            # Identify which predecessor cycle this walk IS
            N = len(w)
            walk_edges = [(w[k], w[(k+1)%N]) for k in range(N)]
            # Greedy edge-set cover
            remaining = Counter({e:1 for e in walk_edges})
            conj = []
            while sum(remaining.values()) > 0:
                best, best_n = -1, 0
                for pi, pc in enumerate(cyc_p):
                    nc = len(pc)
                    pes = {(pc[k], pc[(k+1)%nc]) for k in range(nc)}
                    n = sum(1 for e in pes if remaining.get(e,0) > 0)
                    if n > best_n: best, best_n = pi, n
                if best < 0: break
                conj.append(best)
                nc = len(cyc_p[best])
                for k in range(nc):
                    e = (cyc_p[best][k], cyc_p[best][(k+1)%nc])
                    if remaining.get(e,0) > 0: remaining[e] -= 1
                    if remaining.get(e,0) == 0 and e in remaining: del remaining[e]
            conj_unique = tuple(sorted(set(conj)))

            # Find cyclic shift if single-cycle conjunction
            shift = None
            if len(conj_unique) == 1:
                pc = cyc_p[conj_unique[0]]
                if len(pc) == N:
                    for s in range(N):
                        if all(w[k] == pc[(k+s)%N] for k in range(N)):
                            shift = s; break

            walk_info.append({
                'walk': w, 'conjunction': conj_unique,
                'shift': shift, 'is_simple': len(w) == len(set(w))
            })

        prop_map[ci] = {'cycle': cyc, 'length': len(cyc), 'walks': walk_info}

    return prop_map, cyc_r, cyc_p


# ═══════════════════════════════════════════════════════════════
#  BIPARTITE PERMUTATION ANALYSIS
# ═══════════════════════════════════════════════════════════════

def permutation_analysis(prop_map, cyc_r, cyc_p, verbose=True):
    """
    Extract the cycle-level permutation σ: C_r[i] ↦ C_pred[j].
    Show that E decomposes into bijective shift-components.
    """
    perm = {}
    for ci, info in prop_map.items():
        if not info['walks']: continue
        # Take the first walk; prefer single-cycle conjunction
        for wd in info['walks']:
            if len(wd['conjunction']) == 1:
                perm[ci] = wd['conjunction'][0]
                break
        else:
            perm[ci] = info['walks'][0]['conjunction']  # tuple

    if verbose:
        print(f"\n  ╔══ CYCLE-LEVEL PERMUTATION σ ══╗")
        all_single = all(isinstance(v, int) for v in perm.values())
        for ci in sorted(perm):
            cj = perm[ci]
            info = prop_map[ci]
            shift = None
            for wd in info['walks']:
                if len(wd['conjunction']) == 1 and wd['conjunction'][0] == cj:
                    shift = wd['shift']; break
            is_simple = all(wd['is_simple'] for wd in info['walks'])
            sh = f"z^{shift}" if shift is not None else "?"
            fp = " (fixed)" if cj == ci else ""
            print(f"    C[{ci}](len={len(cyc_r[ci])}) → C[{cj}](len={len(cyc_p[cj])}) "
                  f"shift={sh} simple={is_simple}{fp}")

        if all_single:
            dom = sorted(perm.keys()); rng = sorted(perm.values())
            bij = (dom == rng)
            print(f"\n  Bijective permutation: {bij}")

            # Permutation cycle decomposition
            vis = set(); orbits = []
            for s in sorted(perm):
                if s in vis: continue
                orb = []; cur = s
                while cur not in vis:
                    vis.add(cur); orb.append(cur); cur = perm[cur]
                orbits.append(orb)

            print(f"  Orbits of σ:")
            for orb in orbits:
                if len(orb) == 1:
                    print(f"    Fixed: C[{orb[0]}](len={len(cyc_r[orb[0]])})")
                else:
                    ch = " → ".join(f"C[{c}]" for c in orb)
                    print(f"    ({len(orb)}-orbit): {ch} → C[{orb[0]}]")

            order = lcm_list([len(o) for o in orbits]) if orbits else 1
            print(f"  Order of σ: {order}")

    return perm


# ═══════════════════════════════════════════════════════════════
#  TOP-LEVEL ANALYSIS
# ═══════════════════════════════════════════════════════════════

def analyze(name, T_p0, T_other=None, expect=None, m=None):
    if T_other is None: T_other = T_p0
    sym = (T_other == T_p0)

    print(f"\n{'═'*60}")
    print(f"  {name}")
    if expect: print(f"  Expected: {expect}")
    print(f"{'═'*60}")

    if not T_p0:
        print("  Empty => NO LIVELOCK"); return False

    all_T = list(T_p0) + list(T_other)
    if m is None: m = max(max(v,w,wp) for v,w,wp in all_T) + 1
    print(f"  m={m}, |T_p0|={len(T_p0)}, |T_other|={len(T_other)}, sym={sym}")

    sd0, v0 = check_self_disabling(T_p0)
    sd1, v1 = check_self_disabling(T_other)
    if not sd0:
        print(f"  ✗ P_0 NOT self-disabling: {v0}"); return False
    if not sd1:
        print(f"  ✗ P_other NOT self-disabling: {v1}"); return False

    has_ll, k0, ko = fixed_point(T_p0, T_other, verbose=True)

    if has_ll:
        print(f"\n  Kernel P0: {sorted(k0)}")
        print(f"  Kernel Po: {sorted(ko)}")
        # NOTE: For algebraic characterization (cycle basis, propagation
        # relation, shifts), use homology_Z.py's compute_algebra(ko).
        # The resolve_CL, build_propagation_map, and permutation_analysis
        # functions below are retained for reference but have assumptions
        # (single permutation, shift only for single-conjunction) that
        # break for non-deterministic shadow maps.

    ok = (has_ll == (expect=="LIVELOCK")) if expect else None
    tag = " ✓" if ok else (" ✗" if ok is False else "")
    print(f"\n  => {'LIVELOCK' if has_ll else 'NO LIVELOCK'}{tag}")
    return has_ll


# ═══════════════════════════════════════════════════════════════
#  TEST SUITE
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    # Dijkstra token ring (asymmetric)
    for m in [3, 4, 5]:
        T0 = [(v, v, (v+1)%m) for v in range(m)]
        To = [(v, w, v) for v in range(m) for w in range(m) if v != w]
        analyze(f"Dijkstra (m={m})", T0, To, "LIVELOCK")

    # Sum-Not-2 deterministic
    m = 3
    analyze("Sum-Not-2 det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m) if (v+w)%m == m-1],
            expect="NO LIVELOCK")

    # Coloring deterministic
    analyze("3-Coloring det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m) if w==v],
            expect="LIVELOCK")

    # Simple 2-cycle
    analyze("Simple 2-cycle (m=2)", [(0,1,0),(1,0,1)], expect="LIVELOCK")

    # Always-write-0
    analyze("Always-write-0 (m=3)",
            [(v,w,0) for v in range(3) for w in range(3) if w!=0],
            expect="NO LIVELOCK")

    # Non-det dead-ends
    analyze("Non-det dead-ends (m=3)",
            [(0,1,0),(0,1,2),(1,0,1),(2,1,2)], expect="LIVELOCK")

    # Maximal agreement
    m = 4
    analyze("Maximal agreement (m=4)",
            [(v, w, v) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    # Non-det coloring
    analyze("Non-det coloring (m=4)",
            [(v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    # Non-det sum-not-2
    m = 3
    analyze("Non-det sum-not-2 (m=3)",
            [(m-1-v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    # Maximal agreement m=3
    analyze("Maximal agreement (m=3)",
            [(v, w, v) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    # Non-det coloring m=3
    analyze("Non-det coloring (m=3)",
            [(v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    print(f"\n{'═'*60}\n  DONE\n{'═'*60}")

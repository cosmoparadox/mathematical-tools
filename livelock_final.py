"""
Livelock Detection — Complete Implementation
Shadow-Constrained Fixed Point + Circulation Law Resolution

For symmetric protocols with optional distinct P_0.

Fixed point iteration:
  1. Compute maximal pseudolivelock (SCC-based) of current set
  2. Compute required shadows for that pseudolivelock
  3. Filter transitions to those matching required shadows (y,z positions)
  4. Repeat until fixed point or empty
  5. Check ring closure back to P_0

Circulation Law (distinct P_0 case):
  At P_other process:
  H^|E| = E0 o Ecross o E_other^{K-2}

  where:
    H      = pseudolivelock matrix on P_other kernel
    E_other = propagation P_other -> P_other (on kernel)
    E0     = propagation P_0 -> P_other (cross kernel)  
    Ecross = propagation P_other -> P_0 (cross kernel)
"""

from math import gcd
from functools import reduce


# ══════════════════════════════════════════════════════
# Boolean matrix operations
# ══════════════════════════════════════════════════════

def bmm(A, B):
    n = len(A)
    C = [[0]*n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k]:
                for j in range(n):
                    if B[k][j]: C[i][j] = 1
    return C

def bpow(M, p):
    n = len(M)
    R = [[1 if i==j else 0 for j in range(n)] for i in range(n)]
    B = [row[:] for row in M]
    while p:
        if p & 1: R = bmm(R, B)
        B = bmm(B, B)
        p >>= 1
    return R

def mat_eq(A, B):
    n = len(A)
    return all(A[i][j] == B[i][j] for i in range(n) for j in range(n))

def is_bij(M):
    n = len(M)
    return (all(sum(M[i]) == 1 for i in range(n)) and
            all(sum(M[i][j] for i in range(n)) == 1 for j in range(n)))

def lcm2(a, b): return a * b // gcd(a, b)
def lcm_list(lst): return reduce(lcm2, lst) if lst else 1


# ══════════════════════════════════════════════════════
# Graph operations
# ══════════════════════════════════════════════════════

def scc_cycles(T):
    """Transitions lying on directed cycles in H-graph (own[j]==written[i])."""
    T = list(T)
    n = len(T)
    if n == 0: return frozenset()
    H = {i: [] for i in range(n)}
    for i, (vi,wi,wpi) in enumerate(T):
        for j, (vj,wj,wpj) in enumerate(T):
            if wj == wpi: H[i].append(j)
    visited = [False]*n; order = []
    def dfs1(u):
        stack = [(u,0)]
        while stack:
            v,s = stack.pop()
            if s == 0:
                if visited[v]: continue
                visited[v] = True; stack.append((v,1))
                for w in H[v]:
                    if not visited[w]: stack.append((w,0))
            else: order.append(v)
    for i in range(n):
        if not visited[i]: dfs1(i)
    Hr = {i:[] for i in range(n)}
    for i in range(n):
        for j in H[i]: Hr[j].append(i)
    visited2 = [False]*n; comps = []
    def dfs2(u):
        comp = []; stack = [u]
        while stack:
            v = stack.pop()
            if visited2[v]: continue
            visited2[v] = True; comp.append(v)
            for w in Hr[v]: stack.append(w)
        return comp
    for u in reversed(order):
        if not visited2[u]: comps.append(dfs2(u))
    on_cycle = set()
    for c in comps:
        if len(c) > 1:
            for v in c: on_cycle.add(v)
        elif c and c[0] in H[c[0]]: on_cycle.add(c[0])
    return frozenset(T[i] for i in on_cycle)

def shadows(P):
    """Required shadow (v_i, v_j) for each H-edge (t_i -> t_j) in P."""
    return {(vi, vj)
            for (vi,wi,wpi) in P
            for (vj,wj,wpj) in P
            if wj == wpi}

def filter_T(T, req):
    """Keep transitions whose (w, wp) matches a required shadow."""
    return frozenset((v,w,wp) for (v,w,wp) in T if (w,wp) in req)


# ══════════════════════════════════════════════════════
# Build matrix representations on a kernel
# ══════════════════════════════════════════════════════

def build_H_E(kernel_from, kernel_to=None):
    """
    H[i][j] = 1  iff  t_j.own == t_i.written   (pseudolivelock step)

    E[k][j] = 1  iff  there exists H-edge (t_i -> t_j) such that t_k.own == t_i.pred
                       AND t_k.written == t_j.pred.  Multiple t_k may qualify
                       (they share the same (own,written) but differ in pred).

    Construction: for each H-edge (t_i -> t_j):
      arc changes pred: t_i.pred -> t_j.pred
      find ALL t_k in kernel_from: t_k.own=t_i.pred, t_k.written=t_j.pred
      set E[k][j] = 1 for each such t_k  (arc-based forward map)

    Result: E = H for protocols where pred==own (coloring-type).
            E = I for protocols where written==pred (agreement-type).
    """
    Kf = sorted(kernel_from)
    Kt = sorted(kernel_to) if kernel_to else Kf
    nf, nt = len(Kf), len(Kt)

    # (own,written) -> list of indices in Kf (may be multiple, differ only in pred)
    from collections import defaultdict
    ow_f = defaultdict(list)
    for k, tk in enumerate(Kf):
        ow_f[(tk[1], tk[2])].append(k)

    # H on Kt (square)
    H = [[0]*nt for _ in range(nt)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if tj[1] == ti[2]: H[i][j] = 1

    # E: forward map Kf -> Kt
    # For each H-edge (t_i -> t_j), ALL transitions t_k in Kf with
    # t_k.own == t_i.pred AND t_k.written == t_j.pred are valid arc predecessors.
    E = [[0]*nt for _ in range(nf)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if not H[i][j]: continue
            for k in ow_f.get((ti[0], tj[0]), []):
                E[k][j] = 1

    return Kf, Kt, H, E


# ══════════════════════════════════════════════════════
# Fixed point computation
# ══════════════════════════════════════════════════════

def phi_symmetric(S, T_full):
    """One application of Phi: PL(Filter(S, Shad(PL(S)))), restricted to T_full."""
    P = scc_cycles(S)
    if not P:
        return frozenset()
    sh = shadows(P)
    return frozenset(scc_cycles(filter_T(frozenset(T_full), sh)))


def inner_fixed_point(L_init, T_full, verbose=False, label="T_other"):
    """
    Compute the symmetric fixed point of Phi on T_full,
    warm-started from L_init (already a subset of T_full).
    L_init must satisfy L_init ⊆ T_full.
    Returns L* = greatest fixed point of Phi within T_full
    reachable by deflating from L_init.
    """
    S = frozenset(L_init)
    k = 0
    while True:
        S2 = phi_symmetric(S, T_full)
        if S2 == S:
            if verbose: print(f"    [{label} inner] fixed point at iter {k}: {len(S)} transitions")
            return S
        if verbose:
            print(f"    [{label} inner] iter {k}: removed {sorted(S - S2)}")
        S = S2
        k += 1


def fixed_point(T_p0, T_other, verbose=True):
    """
    Algorithm 1 (Symmetric): if T_p0 == T_other, returns greatest fixed point of Phi.
    Algorithm 2 (Asymmetric, 1-1): joint fixed-point iteration over (L_0, L_other).

    Joint iteration (Knaster-Tarski on finite lattice):
      Both L_0 and L_other are monotone decreasing.
      Terminate when both stabilize (LIVELOCK) or either empties (FREE).
      Warm-starting the inner fixed point gives O(|T|^3) total.

    Returns (has_livelock, kern_p0, kern_other).
    """
    symmetric = (frozenset(T_p0) == frozenset(T_other))

    if symmetric:
        # ── Algorithm 1: Symmetric ─────────────────────────────────────────
        if verbose: print("  [Symmetric] Running Phi fixed point on T")
        L_star = inner_fixed_point(frozenset(T_p0), T_p0, verbose=verbose, label="T")
        if not L_star:
            if verbose: print("  => FREE (empty fixed point)")
            return False, frozenset(), frozenset()
        if verbose: print(f"  => LIVELOCK: L* = {sorted(L_star)}")
        return True, L_star, L_star

    # ── Algorithm 2: (1,1)-Asymmetric joint fixed-point ────────────────────
    if verbose: print("  [Asymmetric] Joint fixed-point iteration over (L_0, L_other)")

    # Initialise: L_0 = PL(T_0), L_other = PL(T_other)
    L0     = frozenset(scc_cycles(frozenset(T_p0)))
    L_other = frozenset(scc_cycles(frozenset(T_other)))

    if not L0:
        if verbose: print("  P_0: no pseudolivelock => FREE")
        return False, frozenset(), frozenset()
    if not L_other:
        if verbose: print("  T_other: no pseudolivelock => FREE")
        return False, frozenset(), frozenset()

    outer = 0
    while True:
        outer += 1
        if verbose: print(f"  Outer iter {outer}: |L_0|={len(L0)}, |L_other|={len(L_other)}")

        # Step 1: constrain L_other by what L_0 requests (warm-start from current L_other)
        req_fwd = shadows(L0)
        L_other_constrained = frozenset(filter_T(L_other, req_fwd))
        L_other_new = inner_fixed_point(L_other_constrained, T_other,
                                        verbose=verbose, label="L_other")
        if verbose: print(f"    L_other_new = {sorted(L_other_new)}")

        if not L_other_new:
            if verbose: print("  => FREE (L_other emptied)")
            return False, frozenset(), frozenset()

        # Step 2: ring closure — constrain L_0 by what L_other_new requests
        req_back = shadows(L_other_new)
        L0_new = frozenset(scc_cycles(filter_T(frozenset(T_p0), req_back)))
        if verbose: print(f"    L_0_new = {sorted(L0_new)}")

        if not L0_new:
            if verbose: print("  => FREE (L_0 emptied)")
            return False, frozenset(), frozenset()

        # Termination check: joint fixed point
        if L0_new == L0 and L_other_new == L_other:
            if verbose: print(f"  => LIVELOCK: joint fixed point reached")
            return True, L0_new, L_other_new

        L0      = L0_new
        L_other = L_other_new


# ══════════════════════════════════════════════════════
# Circulation Law resolution (per process)
# ══════════════════════════════════════════════════════

def cycle_decomp(M, labels):
    """Extract cycles from a bijective permutation matrix."""
    n = len(M)
    succ = {i: [j for j in range(n) if M[i][j]][0] for i in range(n)}
    visited = set(); cycles = []
    for s in range(n):
        if s not in visited:
            cyc = []; cur = s
            while cur not in visited:
                visited.add(cur); cyc.append(labels[cur]); cur = succ[cur]
            if cyc: cycles.append(cyc)
    return cycles


def resolve_CL(kern_p0, kern_other, verbose=True):
    """
    Resolve Circulation Law to find valid (|E|, K) pairs.

    Physical chain from P_1's perspective going around the ring:
      P_1 -[E_other]-> P_2 -...- P_{K-1} -[Ecross]-> P_0 -[E0]-> P_1
      = E_other^{K-2} then Ecross then E0   (left-to-right composition)

    Circulation Law: H^|E| = chain(K)
    where chain(K) = E_other^{K-2} * Ecross * E0_mat  (matrix multiplication)

    For fully symmetric (kern_p0 == kern_other):
      Ecross = E0_mat = E_other, so chain(K) = E_other^K
      => H^|E| = E^K
    """
    if not kern_other: return

    Ko = sorted(kern_other)
    K0 = sorted(kern_p0)
    no = len(Ko)
    n0 = len(K0)

    _, _, H, E_other = build_H_E(kern_other, kern_other)
    _, _, _, E0_mat  = build_H_E(kern_p0, kern_other)   # K0 -> Ko  (propagation)
    _, _, _, Ecross  = build_H_E(kern_other, kern_p0)   # Ko -> K0  (propagation)

    def bmm_rect(A, B, nA_rows, nA_cols, nB_cols):
        """General matrix multiply A[nA_rows x nA_cols] * B[nA_cols x nB_cols]."""
        C = [[0]*nB_cols for _ in range(nA_rows)]
        for i in range(nA_rows):
            for k in range(nA_cols):
                if A[i][k]:
                    for j in range(nB_cols):
                        if B[k][j]: C[i][j] = 1
        return C

    # For fully symmetric (kern_p0 == kern_other):
    #   E0_mat = E_other, Ecross = E_other
    #   => chain(K) = E_other^{K-2} * E_other * E_other = E_other^K = E^K
    # For asymmetric (distinct P_0):
    #   chain(K) = E_other^{K-2} * Ecross * E0_mat  (one special P_0 step)
    # In both cases we call the K-step propagation E^K for display,
    # where E = E_other for symmetric, and E = chain for asymmetric.

    sym = (sorted(kern_p0) == sorted(kern_other))

    if verbose:
        print(f"\n  {'─'*50}")
        print(f"  Circulation Law: H^|E| ∩ E^K != empty,  0 < |E| <= K")
        if sym:
            print(f"  E^K = E_other^K  (symmetric)")
        else:
            print(f"  E^K = E_other^{{K-2}} * Ecross * E0  (asymmetric)")
        print(f"  {'─'*50}")
        print(f"  H bijective:       {is_bij(H)}")
        print(f"  E_other bijective: {is_bij(E_other)}")

    def intersects(A, B):
        n = len(A)
        return any(A[i][j] and B[i][j] for i in range(n) for j in range(n))

    # Precompute E^K for K = 1..max_K
    max_K = min(no * no + 6, 30)
    max_E = max_K  # |E| <= K so max_E = max_K

    E_powers = [None]   # index 0 unused, E_powers[k] = E^k
    if sym:
        # E^K = E_other^K
        curr = [row[:] for row in E_other]
        for k in range(1, max_K + 1):
            E_powers.append([row[:] for row in curr])
            curr = bmm(curr, E_other)
    else:
        # E^K = E_other^{K-2} * Ecross * E0_mat
        # Precompute iteratively: base = Ecross * E0
        base = bmm_rect(Ecross, E0_mat, no, n0, no)  # K=1 and K=2
        E_powers.append([row[:] for row in base])   # K=1
        E_powers.append([row[:] for row in base])   # K=2
        curr = [row[:] for row in base]
        for k in range(3, max_K + 1):
            curr = bmm_rect(E_other, curr, no, no, no)
            E_powers.append([row[:] for row in curr])

    # Search: 0 < |E| <= K
    valid = []
    H_curr = [row[:] for row in H]
    for e_val in range(1, max_K + 1):
        for K_val in range(max(e_val, 2), max_K + 1):   # K >= max(|E|, 2)
            if intersects(H_curr, E_powers[K_val]):
                valid.append((e_val, K_val))
        if len(valid) >= 5:
            break
        H_curr = bmm(H_curr, H)

    if is_bij(H):
        cycs = cycle_decomp(H, Ko)
        lengths = [len(c) for c in cycs]
        if verbose:
            print(f"\n  H cycle decomposition:")
            for c in cycs:
                print(f"    ({len(c)}-cycle): "
                      + " -> ".join(str(t) for t in c) + " ->")
            print(f"  H order = LCM{lengths} = {lcm_list(lengths)}")

    if valid:
        min_E = valid[0][0]
        min_K = valid[0][1]
        if len(valid) >= 2:
            # Infer period in K (step between consecutive K for same |E|)
            same_E = [K for e,K in valid if e == min_E]
            period_K = (same_E[1] - same_E[0]) if len(same_E) >= 2 else min_K
        else:
            period_K = min_K

        if verbose:
            print(f"\n  Valid (|E|, K) pairs (first {len(valid)}):")
            for e,K in valid:
                print(f"    |E|={e}, K={K}  "
                      f"(|E| mod m = {e % (no if no>0 else 1)}, "
                      f"K mod m = {K % (no if no>0 else 1)})")
            print(f"\n  Minimum |E| = {min_E},  minimum K = {min_K}")
            print(f"  K step = {period_K}")
            print(f"  Pattern: |E| = {min_E} + {lcm_list([c for c in [len(cc) for cc in (cycle_decomp(H,Ko) if is_bij(H) else [[]])]]) if is_bij(H) else '?'}*t,  "
                  f"K = {min_K} + {period_K}*s")

        return {'valid': True, 'min_E': min_E, 'min_K': min_K,
                'period_K': period_K, 'pairs': valid}
    else:
        if verbose:
            print(f"  No valid (|E|, K) found in search range "
                  f"(|E| <= {max_E}, K <= {max_K})")
        return {'valid': False}



# ══════════════════════════════════════════════════════
# Complete analysis
# ══════════════════════════════════════════════════════

def analyze(name, T_p0, T_other=None, expect=None, m=None):
    if T_other is None: T_other = T_p0
    sym = (T_other == T_p0)

    print(f"\n{'═'*60}")
    print(f"  {name}")
    if expect: print(f"  Expected: {expect}")
    print(f"{'═'*60}")

    # Handle empty transition sets gracefully
    if not T_p0 and not T_other:
        print(f"  Empty protocol => NO LIVELOCK")
        print(f"\n  => NO LIVELOCK")
        return False
    if not T_p0:
        if m is None and T_other:
            m = max(max(v,w,wp) for v,w,wp in T_other) + 1
        print(f"  m={m}, P_0=0 (empty) => NO LIVELOCK")
        print(f"\n  => NO LIVELOCK")
        return False
    all_T = list(T_p0) + list(T_other if T_other else [])
    if m is None:
        m = max(max(v,w,wp) for v,w,wp in all_T) + 1
    print(f"  m={m}, P_0={len(T_p0)}, P_other={len(T_other)}, sym={sym}")
    print()

    has_ll, k0, ko = fixed_point(T_p0, T_other, verbose=True)

    if has_ll:
        print(f"\n  P_0 kernel   : {sorted(k0)}")
        print(f"  P_other kernel: {sorted(ko)}")
        resolve_CL(k0, ko, verbose=True)
        if sym:
            structural_analysis(ko, label_r="L*")
        else:
            # Interface 1: P_other -> P_other
            structural_analysis(ko, label_r="L*_others")
            # Interface 2: P_0 -> P_other
            structural_analysis(k0, ko, label_r="L*_0", label_r1="L*_others")
            # Interface 3: P_other -> P_0
            structural_analysis(ko, k0, label_r="L*_others", label_r1="L*_0")

    correct = (has_ll == (expect == "LIVELOCK")) if expect else None
    tag = "✓" if correct else ("✗" if correct is False else "")
    print(f"\n  => {'LIVELOCK' if has_ll else 'NO LIVELOCK'} {tag}")
    return has_ll


# ══════════════════════════════════════════════════════════════════════════════
# STRUCTURAL ANALYSIS: Cycle Basis, E_ij Decomposition, Propagation Law
# ══════════════════════════════════════════════════════════════════════════════

def cycle_to_edge_set(cycle):
    """Represent a cycle as a frozenset of directed edges."""
    n = len(cycle)
    return frozenset((cycle[i], cycle[(i+1)%n]) for i in range(n))

def or_ear_decomposition(H, Kf):
    """
    OR-based ear decomposition: find the minimal set of simple cycles
    whose UNION covers all edges of H* (using set-union, not GF(2) XOR).
    These are the atoms of the transition-set algebra used by E*.
    Returns (ears, complete) where ears is a list of cycle tuples.
    """
    n = len(Kf)
    cycles = []
    def dfs(start, cur, path, path_set):
        for nxt in range(n):
            if not H[cur][nxt]: continue
            if nxt == start and len(path) >= 2:
                cycles.append(tuple(path))
            elif nxt > start and nxt not in path_set:
                path_set.add(nxt); path.append(nxt)
                dfs(start, nxt, path, path_set)
                path.pop(); path_set.remove(nxt)
    for s in range(n):
        dfs(s, s, [s], {s})
    seen = set()
    unique = []
    for c in cycles:
        canon = min(c[i:]+c[:i] for i in range(len(c)))
        if canon not in seen:
            seen.add(canon)
            unique.append(tuple(Kf[v] for v in c))
    unique.sort(key=len)

    all_edges = {(i,j) for i in range(n) for j in range(n) if H[i][j]}
    covered = set()
    ears = []
    for cyc in unique:
        c_idx = tuple(Kf.index(t) for t in cyc)
        c_edges = {(c_idx[k], c_idx[(k+1)%len(c_idx)]) for k in range(len(c_idx))}
        new_edges = c_edges - covered
        if new_edges:
            ears.append(cyc)
            covered |= c_edges
        if covered == all_edges:
            break
    return ears, covered == all_edges


    """Represent a cycle as a frozenset of directed edges."""
    n = len(cycle)
    return frozenset((cycle[i], cycle[(i+1)%n]) for i in range(n))

def compute_cycle_basis(H, Kf):
    """
    Compute a minimum cycle basis for H* using GF(2) Gaussian elimination.
    Cycles sorted by length first (shortest basis).
    Returns (basis, all_simple_cycles).
    """
    from itertools import product as iproduct
    n = len(Kf)

    # Find all simple cycles
    cycles = []
    def dfs(start, cur, path, path_set):
        for nxt in range(n):
            if not H[cur][nxt]: continue
            if nxt == start and len(path) >= 2:
                cycles.append(tuple(path))
            elif nxt > start and nxt not in path_set:
                path_set.add(nxt); path.append(nxt)
                dfs(start, nxt, path, path_set)
                path.pop(); path_set.remove(nxt)
    for s in range(n):
        dfs(s, s, [s], {s})
    seen = set()
    unique = []
    for c in cycles:
        canon = min(c[i:]+c[:i] for i in range(len(c)))
        if canon not in seen:
            seen.add(canon)
            unique.append(tuple(Kf[v] for v in c))

    # GF(2) Gaussian elimination (shortest first)
    sorted_cycles = sorted(unique, key=len)
    basis = []
    basis_vecs = []
    pivot_cols = {}
    for cycle in sorted_cycles:
        vec = cycle_to_edge_set(cycle)
        reduced = vec
        for edge, bidx in pivot_cols.items():
            if edge in reduced:
                reduced = reduced.symmetric_difference(basis_vecs[bidx])
        if reduced:
            basis.append(cycle)
            basis_vecs.append(reduced)
            pivot = min(reduced, key=str)
            pivot_cols[pivot] = len(basis_vecs)-1
    return basis, unique

def get_eij_bijection(C1, C2, E, Kf):
    """
    Return E_ij: C1->C2 as dict {t_k: t_j} if it is a bijection, else None.
    """
    if len(C1) != len(C2): return None
    c1_idx = [Kf.index(t) for t in C1]
    c2_idx = [Kf.index(t) for t in C2]
    edges = [(Kf[ii], Kf[jj]) for ii in c1_idx for jj in c2_idx if E[ii][jj]]
    targets = [tj for _,tj in edges]
    sources = [ti for ti,_ in edges]
    if (len(edges) != len(C1) or len(set(targets)) != len(C1) or
        len(set(sources)) != len(C1) or set(targets) != set(C2)):
        return None
    return dict(edges)

def check_propagation_law_bij(bij, C_i, C_j):
    """
    Check restricted propagation law: E_ij(H_Ci(t)) = H_Cj(E_ij(t))
    for all t in C_i. Returns True if holds.
    """
    Hci = {C_i[k]: C_i[(k+1)%len(C_i)] for k in range(len(C_i))}
    Hcj = {C_j[k]: C_j[(k+1)%len(C_j)] for k in range(len(C_j))}
    return all(bij[Hci[t]] == Hcj[bij[t]] for t in C_i)

def structural_analysis(L_r, L_r1=None, label_r="L*", label_r1=None):
    """
    Full structural analysis:
    1. Cycle basis of H*(L_r)
    2. E_ij decomposition between basis cycles
    3. Propagation law check for each E_ij
    4. Cross-process analysis if L_r1 provided
    """
    if L_r1 is None:
        L_r1 = L_r
    if label_r1 is None:
        label_r1 = label_r

    Kfr, _, Hr, Er = build_H_E(L_r, L_r)
    Kfr1, _, Hr1, Er1 = build_H_E(L_r1, L_r1)

    print(f"\n{'='*60}")
    print(f"Structural analysis: {label_r}")
    print(f"{'='*60}")

    # Cycle basis: GF(2) for dimension, OR ears for E_ij analysis
    gf2_basis, _ = compute_cycle_basis(Hr, Kfr)
    ears_r, complete = or_ear_decomposition(Hr, Kfr)
    nr = len(Kfr)
    n_edges = sum(Hr[i][j] for i in range(nr) for j in range(nr))
    from collections import deque as _dq
    _vis = set(); _nc = 0
    for _s in range(nr):
        if _s in _vis: continue
        _nc += 1; _q = _dq([_s])
        while _q:
            _u = _q.popleft()
            if _u in _vis: continue
            _vis.add(_u)
            for _v in range(nr):
                if Hr[_u][_v] or Hr[_v][_u]: _q.append(_v)
    print(f"|L*| = {nr}, H* edges = {n_edges}, components = {_nc}")
    print(f"GF(2) basis size = {n_edges - nr + _nc}  |  OR ears = {len(ears_r)}  (complete={complete})")
    print(f"OR-based ears (atoms for E_ij analysis):")
    for i,c in enumerate(ears_r):
        chain = " --> ".join(str(t) for t in c) + f" --> {c[0]}"
        print(f"  EAR{i+1}(len={len(c)}): {chain}")

    # E_ij: restrict actual E* to each ear pair (C_i, C_j)
    # Do NOT search for bijections between arbitrary same-length pairs.
    # Instead: for each ear C_i, see where E* sends its transitions,
    # group by target ear, and check equivariance on those restrictions.
    print(f"\nE_ij from actual E* restriction to ear pairs ({label_r} -> {label_r}):")
    bij_count = 0; prop_pass = 0; prop_fail = 0
    for i, Ci in enumerate(ears_r):
        # Find all E*-images of transitions in Ci
        ci_idx = [Kfr.index(t) for t in Ci]
        # Group images by which ear they land in
        ear_images = {}  # j -> {t: t'}
        for ii, t in zip(ci_idx, Ci):
            imgs = [Kfr[jj] for jj in range(nr) if Er[ii][jj]]
            for tj in imgs:
                # Find which ear tj belongs to
                for j, Cj in enumerate(ears_r):
                    if tj in Cj:
                        if j not in ear_images: ear_images[j] = {}
                        if t in ear_images[j]:
                            # multiple images to same ear -- not a bijection
                            ear_images[j][t] = None  # mark as non-bijective
                        else:
                            ear_images[j][t] = tj
        # For each target ear, check if restriction is a bijection and equivariant
        for j, mapping in sorted(ear_images.items()):
            Cj = ears_r[j]
            if None in mapping.values(): continue
            if len(mapping) != len(Ci): continue
            targets = list(mapping.values())
            if len(set(targets)) != len(targets): continue
            if set(targets) != set(Cj): continue
            ok = check_propagation_law_bij(mapping, Ci, Cj)
            if not ok: continue   # not a genuine morphism -- skip
            tag = f"EAR{i+1}->EAR{j+1}" if i != j else f"EAR{i+1}->EAR{i+1} (self)"
            print(f"  {tag}(len={len(Ci)}->{len(Cj)}): prop=✓")
            print(f"    {mapping}")
            bij_count += 1
            prop_pass += 1
    print(f"  [{bij_count} equivariant E_ij morphisms]")

    # Cross-process E_ij if L_r1 != L_r
    if L_r1 != L_r:
        ears_r1, _ = or_ear_decomposition(Hr1, Kfr1)
        print(f"\nCross-process E_ij ({label_r} -> {label_r1}):")
        Kf_src, Kt_tgt, H_cross, E_cross = build_H_E(L_r, L_r1)

        def get_eij_cross(C1, C2, E, Ksrc, Ktgt):
            if len(C1) != len(C2): return None
            try:
                c1_idx = [Ksrc.index(t) for t in C1]
                c2_idx = [Ktgt.index(t) for t in C2]
            except ValueError:
                return None
            edges = [(Ksrc[ii], Ktgt[jj]) for ii in c1_idx for jj in c2_idx if E[ii][jj]]
            targets = [tj for _,tj in edges]
            sources = [ti for ti,_ in edges]
            if (len(edges) != len(C1) or len(set(targets)) != len(C1) or
                len(set(sources)) != len(C1) or set(targets) != set(C2)):
                return None
            return dict(edges)

        bij_count_x = 0; prop_pass_x = 0; prop_fail_x = 0
        for i, Ci in enumerate(ears_r):
            try: ci_idx = [Kf_src.index(t) for t in Ci]
            except ValueError: continue
            ear_images = {}
            for ii, t in zip(ci_idx, Ci):
                imgs = [Kt_tgt[jj] for jj in range(len(Kt_tgt)) if E_cross[ii][jj]]
                for tj in imgs:
                    for j, Cj in enumerate(ears_r1):
                        if tj in Cj:
                            if j not in ear_images: ear_images[j] = {}
                            if t in ear_images[j]:
                                ear_images[j][t] = None
                            else:
                                ear_images[j][t] = tj
            for j, mapping in sorted(ear_images.items()):
                Cj = ears_r1[j]
                if None in mapping.values(): continue
                if len(mapping) != len(Ci): continue
                targets = list(mapping.values())
                if len(set(targets)) != len(targets): continue
                if set(targets) != set(Cj): continue
                ok = check_propagation_law_bij(mapping, Ci, Cj)
                if not ok: continue
                print(f"  Er{i+1}->Er1_{j+1}(len={len(Ci)}->{len(Cj)}): prop=✓")
                print(f"    {mapping}")
                bij_count_x += 1
                prop_pass_x += 1
        print(f"  [{bij_count_x} equivariant E_ij morphisms]")

    return ears_r

# ══════════════════════════════════════════════════════
# Tests
# ══════════════════════════════════════════════════════

if __name__ == "__main__":

    for m in [3, 4, 5, 50]:
        T0  = [(v, v, (v+1)%m) for v in range(m)]
        To  = [(v, w, v) for v in range(m) for w in range(m) if v != w]
        analyze(f"Dijkstra (m={m})", T0, To, "LIVELOCK")

    m = 3
    analyze("Sum-Not-2 det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m)
             if (v+w)%m == m-1],
            expect="NO LIVELOCK")

    analyze("3-Coloring det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m) if w==v],
            expect="LIVELOCK")

    analyze("Simple 2-cycle (m=2)",
            [(0,1,0),(1,0,1)], expect="LIVELOCK")

    analyze("Always-write-0 (m=3)",
            [(v,w,0) for v in range(3) for w in range(3) if w!=0],
            expect="NO LIVELOCK")

    analyze("Non-det dead-ends (m=3)",
            [(0,1,0),(0,1,2),(1,0,1),(2,1,2)], expect="LIVELOCK")

    m = 4
    analyze("AI Proposed Protocol (m=4)",
            [(v, w, (w + 2)%m) for v in range(m) for w in range(m) if w == v or w == (v + 1)%m],
            expect="LIVELOCK")

    m = 4
    analyze("Non Deterministic Coloring (m=4)",
            [(v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    m = 4
    analyze("Agreement (m=4)",
            [(v, w, v) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK")

    print(f"\n{'═'*60}\n  DONE\n{'═'*60}")


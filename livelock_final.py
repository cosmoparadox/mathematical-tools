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

    E[k][j] = 1  iff  there exists H-edge (t_i -> t_j) such that t_k is the
                       unique transition with t_k.own == t_i.pred AND
                       t_k.written == t_j.pred.  (arc-based forward map)

    Construction: for each H-edge (t_i -> t_j):
      arc changes pred: t_i.pred -> t_j.pred
      find unique t_k in kernel_from: t_k.own=t_i.pred, t_k.written=t_j.pred
      set E[k][j] = 1  (t_k in P_{r-1} enables t_j in P_r)

    Result: E = H for protocols where pred==own (coloring-type).
            E = I for protocols where written==pred (agreement-type).
    """
    Kf = sorted(kernel_from)
    Kt = sorted(kernel_to) if kernel_to else Kf
    nf, nt = len(Kf), len(Kt)

    # (own,written) -> index in Kf
    ow_f = {(tk[1], tk[2]): k for k, tk in enumerate(Kf)}

    # H on Kt (square)
    H = [[0]*nt for _ in range(nt)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if tj[1] == ti[2]: H[i][j] = 1

    # E: forward map Kf -> Kt
    E = [[0]*nt for _ in range(nf)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if not H[i][j]: continue
            k = ow_f.get((ti[0], tj[0]))  # unique match
            if k is not None:
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
# Propagation Law check
# ══════════════════════════════════════════════════════

def build_H_local(K):
    """H on kernel K: H[i][j] = 1 iff tj.own == ti.written"""
    n = len(K)
    H = [[0]*n for _ in range(n)]
    for i,ti in enumerate(K):
        for j,tj in enumerate(K):
            if tj[1] == ti[2]: H[i][j] = 1
    return H

def build_E_interface(Kt, Kf):
    """
    Forward E: Kf (P_{r-1}) -> Kt (P_r).
    For each H-edge (ti->tj) in Kt:
      arc: ti.pred -> tj.pred
      unique tk in Kf: tk.own=ti.pred, tk.written=tj.pred
      E[k][j] = 1
    """
    nt = len(Kt); nf = len(Kf)
    H  = build_H_local(Kt)
    ow = {(tk[1],tk[2]):k for k,tk in enumerate(Kf)}
    E  = [[0]*nt for _ in range(nf)]
    for i,ti in enumerate(Kt):
        for j,tj in enumerate(Kt):
            if not H[i][j]: continue
            k = ow.get((ti[0], tj[0]))
            if k is not None:
                E[k][j] = 1
    return E

def check_propagation_law(k0, ko, sym, verbose=True):
    """
    Check H_prev ∘ E = E ∘ H_curr at each interface around the ring.

    Symmetric: one interface (P_other -> P_other).
    Asymmetric: three interfaces:
      1. P_{K-1} (other) -> P_0:      H_other ∘ E_cross = E_cross ∘ H_0
      2. P_0 -> P_1 (other):          H_0     ∘ E_0     = E_0     ∘ H_other
      3. P_r  -> P_{r+1} (other):     H_other ∘ E_other = E_other ∘ H_other
    """
    if verbose:
        print(f"  ──────────────────────────────────────────────────")
        print(f"  Propagation Law: H_prev ∘ E = E ∘ H_curr")
        print(f"  ──────────────────────────────────────────────────")

    K0 = sorted(k0); Ko = sorted(ko)
    H_0     = build_H_local(K0)
    H_other = build_H_local(Ko)

    def equiv_check(H_prev, E, H_curr, label):
        HE = bmm(H_prev, E)
        EH = bmm(E, H_curr)
        ok = (HE == EH)
        if verbose:
            print(f"  {label}: {'✓' if ok else '✗'}")
        return ok

    if sym:
        E_other = build_E_interface(Ko, Ko)
        ok = equiv_check(H_other, E_other, H_other,
                         "P_r->P_{r+1} (H_other ∘ E_other = E_other ∘ H_other)")
        return ok
    else:
        E_cross = build_E_interface(K0, Ko)   # Ko -> K0
        E_0     = build_E_interface(Ko, K0)   # K0 -> Ko
        E_other = build_E_interface(Ko, Ko)   # Ko -> Ko
        ok1 = equiv_check(H_other, E_cross, H_0,
                          "P_{K-1}->P_0   (H_other ∘ E_cross = E_cross ∘ H_0)")
        ok2 = equiv_check(H_0,     E_0,     H_other,
                          "P_0->P_1       (H_0     ∘ E_0     = E_0     ∘ H_other)")
        ok3 = equiv_check(H_other, E_other, H_other,
                          "P_r->P_{r+1}   (H_other ∘ E_other = E_other ∘ H_other)")
        return ok1 and ok2 and ok3

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
        check_propagation_law(k0, ko, sym, verbose=True)

    correct = (has_ll == (expect == "LIVELOCK")) if expect else None
    tag = "✓" if correct else ("✗" if correct is False else "")
    print(f"\n  => {'LIVELOCK' if has_ll else 'NO LIVELOCK'} {tag}")
    return has_ll


# ══════════════════════════════════════════════════════
# Tests
# ══════════════════════════════════════════════════════

if __name__ == "__main__":

    for m in [3, 4, 5]:
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

    print(f"\n{'═'*60}\n  DONE\n{'═'*60}")

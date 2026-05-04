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


def augment_transitive_closure(T, verbose=False):
    """
    For non-self-disabling protocols: augment T with the transitive closure
    of chains under each fixed pred value.

    For each pred value p, transitions (p, o, w) define a directed graph
    on domain values: o → w. If this graph has a cycle, a process can fire
    forever under fixed pred — immediate local livelock.

    Otherwise, for every pair (o_i, o_j) where o_j is reachable from o_i
    in the chain graph, add transition (p, o_i, o_j). This captures
    all possible "bursts" — sequences of firings under fixed pred — as
    single macro-transitions. The augmented set is generally NOT
    self-disabling, but the product graph algorithm works regardless.

    Returns (augmented_T, has_local_livelock, cycle_info).
    """
    from collections import defaultdict

    # Group transitions by pred
    by_pred = defaultdict(list)
    for p, o, w in T:
        by_pred[p].append((o, w))

    augmented = set(T)
    
    for p, edges in by_pred.items():
        # Build adjacency for the chain graph under this pred
        adj = defaultdict(set)
        all_nodes = set()
        for o, w in edges:
            adj[o].add(w)
            all_nodes.add(o)
            all_nodes.add(w)

        # Check for cycles via DFS
        WHITE, GRAY, BLACK = 0, 1, 2
        color = {v: WHITE for v in all_nodes}
        has_cycle = False
        cycle_node = None

        def dfs_cycle(u):
            nonlocal has_cycle, cycle_node
            color[u] = GRAY
            for v in adj[u]:
                if color[v] == GRAY:
                    has_cycle = True
                    cycle_node = v
                    return
                if color[v] == WHITE:
                    dfs_cycle(v)
                    if has_cycle:
                        return
            color[u] = BLACK

        for v in all_nodes:
            if color[v] == WHITE:
                dfs_cycle(v)
                if has_cycle:
                    if verbose:
                        print(f"  Local livelock: pred={p}, cycle at node {cycle_node}")
                    return augmented, True, (p, cycle_node)

        # No cycle — compute transitive closure (all reachable pairs)
        for start in all_nodes:
            # BFS/DFS from start
            reachable = set()
            stack = [start]
            visited = set()
            while stack:
                u = stack.pop()
                if u in visited:
                    continue
                visited.add(u)
                for v in adj[u]:
                    if v not in visited:
                        reachable.add(v)
                        stack.append(v)

            # Add transitions for all reachable values
            for target in reachable:
                if target != start:  # skip self-loops (own = wr)
                    augmented.add((p, start, target))

    augmented = sorted(augmented)
    if verbose:
        added = len(augmented) - len(T)
        print(f"  Transitive closure: {len(T)} → {len(augmented)} transitions "
              f"(+{added} augmented)")

    return augmented, False, None


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

def _scc_on_edges(Ls, edges):
    """Compute SCC using only the given edge set. Return transitions on cycles."""
    n = len(Ls); idx_map = {t: i for i, t in enumerate(Ls)}
    adj = {i: [] for i in range(n)}
    for (ti, tj) in edges:
        i, j = idx_map.get(ti), idx_map.get(tj)
        if i is not None and j is not None:
            adj[i].append(j)
    # Kosaraju's SCC
    visited = [False]*n; order = []
    def dfs1(u):
        stk = [(u,0)]
        while stk:
            v,s = stk.pop()
            if s == 0:
                if visited[v]: continue
                visited[v] = True; stk.append((v,1))
                for w in adj[v]:
                    if not visited[w]: stk.append((w,0))
            else: order.append(v)
    for i in range(n): 
        if not visited[i]: dfs1(i)
    radj = {i:[] for i in range(n)}
    for i in range(n):
        for j in adj[i]: radj[j].append(i)
    visited2 = [False]*n; on_cycle = set()
    for u in reversed(order):
        if visited2[u]: continue
        comp = []; stk = [u]
        while stk:
            v = stk.pop()
            if visited2[v]: continue
            visited2[v] = True; comp.append(v)
            for w in radj[v]: stk.append(w)
        if len(comp) > 1:
            for v in comp: on_cycle.add(v)
        elif comp[0] in adj.get(comp[0], []):
            on_cycle.add(comp[0])
    return frozenset(Ls[i] for i in on_cycle)


def _build_witnessed_edges(L, witness_ow):
    """Build H-edge set keeping only edges whose shadow is in witness_ow."""
    edges = set()
    for ti in L:
        for tj in L:
            if tj[1] == ti[2] and (ti[0], tj[0]) in witness_ow:
                edges.add((ti, tj))
    return edges


def phi(S, T_full):
    """One Φ iteration with explicit edge tracking.
    
    1. Build H(S) with only witnessed edges (shadow ∈ ow(S))
    2. SCC on pruned edge graph → P (transitions on cycles)
    3. Collect witnessed shadow pairs from surviving edges
    4. Filter T_full by these shadow pairs → F
    5. Build H(F) with only witnessed edges (shadow ∈ ow(F))
    6. SCC → result
    """
    if not S: return frozenset()
    Ls = sorted(S)
    ow_S = {(t[1], t[2]) for t in Ls}
    
    # Step 1-2: Build edge-pruned H, compute SCC
    edges = _build_witnessed_edges(Ls, ow_S)
    P = _scc_on_edges(Ls, edges)
    if not P: return frozenset()
    
    # Step 3: Shadow pairs from surviving edges only
    P_set = set(P)
    sh = {(ti[0], tj[0]) for (ti, tj) in edges if ti in P_set and tj in P_set}
    
    # Step 4: Filter T_full
    F = frozenset(t for t in T_full if (t[1], t[2]) in sh)
    if not F: return frozenset()
    
    # Step 5-6: Build edge-pruned H on F, SCC
    Fs = sorted(F)
    ow_F = {(t[1], t[2]) for t in Fs}
    edges_F = _build_witnessed_edges(Fs, ow_F)
    return _scc_on_edges(Fs, edges_F)


def _kosaraju(n, adj):
    """Kosaraju's SCC on graph with n nodes and adjacency list adj.
    Returns set of node indices that lie on non-trivial cycles."""
    visited = [False]*n; order = []
    def dfs1(u):
        stk = [(u, 0)]
        while stk:
            v, s = stk.pop()
            if s: order.append(v); continue
            if visited[v]: continue
            visited[v] = True; stk.append((v, 1))
            for w in adj.get(v, []):
                if not visited[w]: stk.append((w, 0))
    for i in range(n):
        if not visited[i]: dfs1(i)
    radj = defaultdict(list)
    for i in range(n):
        for j in adj.get(i, []): radj[j].append(i)
    visited2 = [False]*n; on_cycle = set()
    for u in reversed(order):
        if visited2[u]: continue
        comp = []; stk = [u]
        while stk:
            v = stk.pop()
            if visited2[v]: continue
            visited2[v] = True; comp.append(v)
            for w in radj[v]: stk.append(w)
        if len(comp) > 1:
            for v in comp: on_cycle.add(v)
        elif comp[0] in adj.get(comp[0], []):
            on_cycle.add(comp[0])
    return on_cycle


def _symmetric_2d_fp(T, verbose=False):
    """Symmetric livelock detection via product transition graph.

    Algorithm:
      1. Build product graph G_×(T) once with four equivariance conditions.
         Node condition: wr(w) = pred(t).
         Arc conditions: own(t2) = wr(t1), own(w2) = wr(w1).
      2. Iterate until stable:
         - SCC: remove arcs not on cycles.
         - Square: S_t = t-components on cycles; remove arcs where w ∉ S_t.
         - Backward closure: for each arc with w-pair (w1,w2), verify
           (w1,w2) appears as a t-pair on some arc on a cycle.

    Returns (L_star, gstar_data) where:
      L_star: frozenset of surviving transitions, or empty if livelock-free.
      gstar_data: (Ls, nodes, arcs) for backtracking, or None.
    """
    Ls = sorted(set(T))
    n = len(Ls)
    if n == 0:
        return frozenset(), None

    # ── Pre-prune: 1D SCC on H-graph ─────────────────────────
    adj1 = defaultdict(list)
    for i, ti in enumerate(Ls):
        for j, tj in enumerate(Ls):
            if tj[1] == ti[2]:
                adj1[i].append(j)
    on1 = _kosaraju(n, adj1)
    Ls = [Ls[i] for i in sorted(on1)]
    n = len(Ls)
    if n == 0:
        return frozenset(), None

    # ── Step 1: Build product graph ONCE ──────────────────────
    # Nodes: (ti, wi) where wr(w) = pred(t)
    nodes = []
    for ti in range(n):
        for wi in range(n):
            if Ls[wi][2] == Ls[ti][0]:
                nodes.append((ti, wi))
    if not nodes:
        return frozenset(), None

    # Arcs: own(t2) = wr(t1), own(w2) = wr(w1)
    all_arcs = set()
    for i, (t1, w1) in enumerate(nodes):
        for j, (t2, w2) in enumerate(nodes):
            if Ls[t2][1] == Ls[t1][2] and Ls[w2][1] == Ls[w1][2]:
                all_arcs.add((i, j))
    if not all_arcs:
        return frozenset(), None

    arcs = set(all_arcs)

    # ── Step 2: Iterate SCC + Square + Backward closure ───────
    for iteration in range(len(all_arcs) + 1):
        prev_arcs = len(arcs)

        # 2.1 SCC: find arcs on cycles
        adj = defaultdict(list)
        live_nodes = set()
        for (i, j) in arcs:
            adj[i].append(j)
            live_nodes.add(i)
            live_nodes.add(j)
        if not live_nodes:
            if verbose:
                print(f"    [T] 2D collapsed to ∅")
            return frozenset(), None

        nlist = sorted(live_nodes)
        nidx = {v: k for k, v in enumerate(nlist)}
        N2 = len(nlist)
        adj2 = defaultdict(list)
        for (i, j) in arcs:
            if i in nidx and j in nidx:
                adj2[nidx[i]].append(nidx[j])

        on_cycle_idx = _kosaraju(N2, adj2)
        on_cycle = {nlist[v] for v in on_cycle_idx}

        if not on_cycle:
            if verbose:
                print(f"    [T] 2D collapsed to ∅")
            return frozenset(), None

        arcs = {(i, j) for (i, j) in arcs
                if i in on_cycle and j in on_cycle}

        # 2.2 Square: S_t = t-components on cycles
        s_t = set()
        for v in on_cycle:
            s_t.add(nodes[v][0])

        arcs = {(i, j) for (i, j) in arcs
                if nodes[i][1] in s_t and nodes[j][1] in s_t}

        # 2.3 Backward closure: for each arc with w-pair (w1,w2),
        #     verify that (w1,w2) appears as a t-pair on some arc
        #     currently on a cycle.
        t_pairs_on_cycle = set()
        for (i, j) in arcs:
            if i in on_cycle and j in on_cycle:
                t_pairs_on_cycle.add((nodes[i][0], nodes[j][0]))

        new_arcs = set()
        for (i, j) in arcs:
            w1 = nodes[i][1]
            w2 = nodes[j][1]
            if (w1, w2) in t_pairs_on_cycle:
                new_arcs.add((i, j))
        arcs = new_arcs

        if not arcs:
            if verbose:
                print(f"    [T] 2D collapsed to ∅")
            return frozenset(), None

        if len(arcs) == prev_arcs:
            # Stable — collect surviving transitions
            final_s_t = set()
            for (i, j) in arcs:
                final_s_t.add(nodes[i][0])
                final_s_t.add(nodes[j][0])
            L_star = frozenset(Ls[i] for i in final_s_t)
            if verbose:
                print(f"    [T] 2D fixed point: {len(L_star)} transitions, "
                      f"{len(arcs)} arcs in G*")
            return L_star, (Ls, nodes, arcs)

        if verbose:
            # Count surviving transitions for progress
            cur_t = set()
            for (i, j) in arcs:
                cur_t.add(nodes[i][0])
            print(f"    [T] 2D iter {iteration}: "
                  f"{prev_arcs} → {len(arcs)} arcs, "
                  f"{len(cur_t)} transitions")

    if verbose:
        print(f"    [T] 2D collapsed to ∅")
    return frozenset(), None


def _find_simple_cycles_gstar(arcs, max_len=20, max_cycles=5000):
    """Find simple cycles in G* (product graph arcs), shortest first."""
    adj = defaultdict(list)
    nodes_set = set()
    for (i, j) in arcs:
        adj[i].append(j)
        nodes_set.add(i)
        nodes_set.add(j)
    max_len = min(max_len, len(nodes_set))
    cycles = []
    # Search by increasing length to find short cycles first
    for target_len in range(2, max_len + 1):
        for start in sorted(nodes_set):
            stack = [(start, [start])]
            while stack:
                if len(cycles) >= max_cycles:
                    return cycles
                v, path = stack.pop()
                if len(path) > target_len:
                    continue
                for nxt in adj[v]:
                    if nxt == start and len(path) == target_len:
                        cycles.append(tuple(path))
                    elif nxt > start and nxt not in path and len(path) < target_len:
                        stack.append((nxt, path + [nxt]))
    return cycles


def _backward_propagate_cycle(nodes, gstar_arcs, cycle_nodes):
    """Find ALL backward cycles in G* whose t-walk matches the given cycle's w-walk.

    Returns a list of tuples of G* node indices forming backward cycles, or [].
    """
    N = len(cycle_nodes)
    w_indices = [nodes[v][1] for v in cycle_nodes]

    adj = defaultdict(list)
    for (i, j) in gstar_arcs:
        adj[i].append(j)

    gstar_nodes = set(i for a in gstar_arcs for i in a)
    pos_candidates = [[] for _ in range(N)]
    for v in gstar_nodes:
        ti = nodes[v][0]
        for k in range(N):
            if ti == w_indices[k]:
                pos_candidates[k].append(v)

    results = []
    max_results = 50  # cap to avoid explosion

    def search(k, path):
        if len(results) >= max_results:
            return
        if k == N:
            if path[0] in adj.get(path[-1], []):
                results.append(tuple(path))
            return
        for v in pos_candidates[k]:
            if k == 0 or v in adj.get(path[-1], []):
                path.append(v)
                search(k + 1, path)
                path.pop()

    search(0, [])
    return results


def _backtrack_verify(Ls, nodes, gstar_arcs, verbose=False):
    """Backtracking verification on G*.

    Builds backward propagation graph between canonical simple cycles.
    Compound backward walks pruned (bijection proposition).

    Returns (has_livelock, graph_info).
    """
    cycles = _find_simple_cycles_gstar(gstar_arcs, max_len=min(20, len(Ls) ** 2))
    if verbose:
        print(f"    [T] Backtracking: {len(cycles)} simple cycles in G*")

    by_length = defaultdict(list)
    for ci, cyc in enumerate(cycles):
        by_length[len(cyc)].append((ci, cyc))

    all_canon_maps = {}       # {N: {canon: (ci, cyc)}}
    all_forward_edges = {}    # {N: {canon: [(target_canon, shift)]}}
    all_compound_pruned = {}
    all_closing_chains = []
    found_livelock = False

    for N in sorted(by_length):
        length_cycles = by_length[N]
        canon_map = {}
        for ci, cyc in length_cycles:
            # Canonicalize by full PG node tuple (not just t-indices)
            # This preserves cycles with same t-walk but different w-walks
            node_key = tuple(cyc)
            rotations = [node_key[r:] + node_key[:r] for r in range(N)]
            canon = min(rotations)
            if canon not in canon_map:
                canon_map[canon] = (ci, cyc)

        all_canon_maps[N] = canon_map
        forward_edges = defaultdict(list)  # canon -> [(target_canon, shift)]
        compound_count = 0

        for canon, (ci, cyc) in canon_map.items():
            all_bw = _backward_propagate_cycle(nodes, gstar_arcs, cyc)
            # Compute canonical rotation offset of source
            src_key = tuple(cyc)
            src_rotations = [src_key[r:] + src_key[:r] for r in range(N)]
            src_canon_rot = src_rotations.index(min(src_rotations))

            for bw in all_bw:
                if len(set(bw)) < len(bw):
                    compound_count += 1
                    continue

                bw_key = tuple(bw)
                bw_rotations = [bw_key[r:] + bw_key[:r] for r in range(N)]
                bw_canon = min(bw_rotations)
                bw_canon_rot = bw_rotations.index(bw_canon)

                # Shift: how much the canonical form rotates
                # Source at canonical rotation src_canon_rot
                # Target at canonical rotation bw_canon_rot
                # The backward walk at position k uses w-component of source[k]
                # so position alignment is inherited. The shift is the
                # difference in canonical rotations.
                shift = (bw_canon_rot - src_canon_rot) % N

                # Avoid duplicate edges
                edge = (bw_canon, shift)
                if edge not in forward_edges[canon]:
                    forward_edges[canon].append(edge)

        all_forward_edges[N] = dict(forward_edges)
        all_compound_pruned[N] = compound_count

        if not forward_edges:
            continue

        # Search for cycles in the forward graph
        targets_only = defaultdict(set)
        for src, edges in forward_edges.items():
            for tgt, _ in edges:
                targets_only[src].add(tgt)

        def find_closing_chain(start, bg=targets_only):
            visited = set()
            stack = [(start, [start])]
            while stack:
                current, path = stack.pop()
                if current in visited:
                    if current == start and len(path) > 1:
                        return path
                    continue
                visited.add(current)
                for nxt in bg.get(current, set()):
                    if nxt == start and len(path) >= 1:
                        return path + [nxt]
                    if nxt not in visited:
                        stack.append((nxt, path + [nxt]))
            return None

        for canon in canon_map:
            chain = find_closing_chain(canon)
            if chain is not None:
                all_closing_chains.append((N, chain))
                if not found_livelock:
                    found_livelock = True
                    ci, cyc = canon_map[canon]
                    if verbose:
                        t_walk = [Ls[nodes[v][0]] for v in cyc]
                        print(f"    [T] Cycle {ci} (N={N}) closes at depth "
                              f"{len(chain)-1} \u2192 LIVELOCK")
                        print(f"         t-walk: {t_walk}")
                        if compound_count > 0:
                            print(f"         ({compound_count} compound walks pruned "
                                  f"by bijection proposition)")
                break  # one closing chain per length suffices

    if not found_livelock and verbose:
        total = sum(len(cm) for cm in all_canon_maps.values())
        print(f"    [T] All {total} canonical cycles fail backward propagation")

    graph_info = {
        'cycles': cycles,
        'canon_maps': all_canon_maps,
        'forward_edges': all_forward_edges,
        'closing_chains': all_closing_chains,
        'compound_pruned': all_compound_pruned,
        'Ls': Ls,
        'nodes': nodes,
    }
    return found_livelock, graph_info


def display_backward_graph(graph_info):
    """Display the forward propagation graph between product graph cycles."""
    canon_maps = graph_info['canon_maps']
    forward_edges = graph_info['forward_edges']
    compound_pruned = graph_info['compound_pruned']
    Ls = graph_info['Ls']
    nodes = graph_info['nodes']

    total_canons = sum(len(cm) for cm in canon_maps.values())
    total_with_fwd = sum(len(fe) for fe in forward_edges.values())
    total_pruned = sum(compound_pruned.values())

    # First: list all simple cycles that close (have forward targets)
    print(f"  SIMPLE CYCLES IN PRODUCT GRAPH (canonical):")
    print()

    for N in sorted(canon_maps):
        cm = canon_maps[N]
        fe = forward_edges.get(N, {})
        if not cm:
            continue

        closing = [canon for canon in cm if canon in fe]
        dead = [canon for canon in cm if canon not in fe]

        print(f"  N={N}: {len(cm)} canonical cycles "
              f"({len(closing)} with forward targets, {len(dead)} dead-ends)")

        for canon, (ci, cyc) in sorted(cm.items(), key=lambda x: x[1][0]):
            t_walk = [Ls[nodes[v][0]] for v in cyc]
            status = "closing" if canon in fe else "dead-end"
            print(f"    c[{ci}] (N={N}): {t_walk}  [{status}]")
        print()

    if total_pruned > 0:
        print(f"  Compound walks pruned (bijection prop.): {total_pruned}")
        print()

    # Then: forward enabling map with shifts
    has_any_edges = any(fe for fe in forward_edges.values())
    if not has_any_edges:
        print(f"  No forward targets found.")
        return

    print(f"  FORWARD ENABLING MAP:")
    print()

    for N in sorted(forward_edges):
        fe = forward_edges[N]
        cm = canon_maps.get(N, {})
        if not fe:
            continue

        for canon in sorted(fe, key=lambda c: cm[c][0] if c in cm else 0):
            if canon not in cm:
                continue
            ci, cyc = cm[canon]
            edges = fe[canon]

            target_strs = []
            for tgt_canon, shift in sorted(edges, key=lambda e: e[1]):
                if tgt_canon == canon:
                    tgt_label = "self"
                elif tgt_canon in cm:
                    tgt_ci, _ = cm[tgt_canon]
                    tgt_label = f"c[{tgt_ci}]"
                else:
                    tgt_label = "(other)"
                target_strs.append(f"{tgt_label} (shift {shift})")

            print(f"    c[{ci}] (N={N}) -> {', '.join(target_strs)}")

    print()


def inner_fp(L_init, T_full, verbose=False, label="T"):
    """Deflate from L_init to the greatest fixed point of Φ within T_full.
    Edge-level phi iteration for the asymmetric case."""
    S = frozenset(L_init); k = 0
    while True:
        S2 = phi(S, T_full)
        if S2 == S:
            if verbose: print(f"    [{label}] fixed point at iter {k}: {len(S)} transitions")
            return S
        if verbose: print(f"    [{label}] iter {k}: {len(S)} → {len(S2)}")
        if not S2: return frozenset()
        S = S2; k += 1


def fixed_point(T_p0, T_other, verbose=True):
    """
    Algorithm 1 (symmetric) / Algorithm 2 ((1,1)-asymmetric).
    Returns (has_livelock, kernel_p0, kernel_other).
    """
    symmetric = (frozenset(T_p0) == frozenset(T_other))

    if symmetric:
        if verbose: print("  [Symmetric] 2D product-graph fixed point")
        L, gstar_data = _symmetric_2d_fp(T_p0, verbose=verbose)
        if not L:
            if verbose: print("  => FREE (G* = ∅)")
            return False, frozenset(), frozenset(), None
        # G* non-empty: verify via backtracking
        Ls, nodes, arcs = gstar_data
        if verbose:
            print("  [Symmetric] G* non-empty — backtracking verification")
        verified, graph_info = _backtrack_verify(Ls, nodes, arcs, verbose=verbose)
        if verified:
            if verbose: print(f"  => LIVELOCK: L* = {sorted(L)}")
            return True, L, L, graph_info
        else:
            if verbose: print("  => INCONCLUSIVE (G* non-empty, no simple cycle closes)")
            return False, L, L, graph_info

    if verbose: print("  [Asymmetric] Joint fixed point (L_0, L_other)")
    # Initial: SCC with edge pruning
    L0 = frozenset(T_p0); Lo = frozenset(T_other)
    ow_0 = {(t[1],t[2]) for t in L0}
    ow_o = {(t[1],t[2]) for t in Lo}
    L0 = _scc_on_edges(sorted(L0), _build_witnessed_edges(sorted(L0), ow_o))
    Lo = _scc_on_edges(sorted(Lo), _build_witnessed_edges(sorted(Lo), ow_o))
    if not L0 or not Lo:
        if verbose: print("  => FREE (empty initial PL)")
        return False, frozenset(), frozenset(), None

    for outer in range(1, len(T_p0) + len(T_other) + 2):
        if verbose: print(f"  Outer {outer}: |L0|={len(L0)}, |Lo|={len(Lo)}")
        # Shadows from L0 edges witnessed by Lo
        ow_Lo = {(t[1],t[2]) for t in Lo}
        edges_L0 = _build_witnessed_edges(sorted(L0), ow_Lo)
        sh_L0 = {(ti[0], tj[0]) for (ti, tj) in edges_L0}
        Lo_init = frozenset(t for t in Lo if (t[1], t[2]) in sh_L0)
        Lo_new = inner_fp(Lo_init, T_other, verbose=verbose, label="Lo")
        if not Lo_new:
            if verbose: print("  => FREE (L_other emptied)")
            return False, frozenset(), frozenset(), None
        # Shadows from Lo edges witnessed by Lo (self)
        ow_Lo_new = {(t[1],t[2]) for t in Lo_new}
        edges_Lo = _build_witnessed_edges(sorted(Lo_new), ow_Lo_new)
        sh_Lo = {(ti[0], tj[0]) for (ti, tj) in edges_Lo}
        L0_init = frozenset(t for t in T_p0 if (t[1], t[2]) in sh_Lo)
        L0_new = _scc_on_edges(sorted(L0_init), 
                               _build_witnessed_edges(sorted(L0_init), ow_Lo_new))
        if not L0_new:
            if verbose: print("  => FREE (L_0 emptied)")
            return False, frozenset(), frozenset(), None
        if L0_new == L0 and Lo_new == Lo:
            if verbose: print("  => LIVELOCK: joint fixed point")
            return True, L0_new, Lo_new
        L0, Lo = L0_new, Lo_new


# ═══════════════════════════════════════════════════════════════
#  2D PRODUCT GRAPH CYCLE ANALYSIS
# ═══════════════════════════════════════════════════════════════

def _build_2d_product_graph(Ls):
    """Build the 2D product graph from a transition set.
    
    Returns:
        Ls: sorted transition list
        surviving: dict (i,j) → set of witness indices
        adj2: adjacency list for 2D nodes (ti, wk) → [(tj, wj), ...]
        nodes2: set of all 2D nodes
    """
    n = len(Ls)
    ow = {(t[1], t[2]) for t in Ls}
    surviving = {}
    for i, ti in enumerate(Ls):
        for j, tj in enumerate(Ls):
            if tj[1] == ti[2]:
                sh = (ti[0], tj[0])
                wits = {k for k in range(n)
                        if Ls[k][1] == sh[0] and Ls[k][2] == sh[1]}
                if wits:
                    surviving[(i, j)] = wits
    adj2 = defaultdict(list)
    nodes2 = set()
    for (ti, tj), ws in surviving.items():
        for wk in ws:
            for (wi, wj) in surviving:
                if wi == wk:
                    nodes2.add((ti, wk))
                    nodes2.add((tj, wj))
                    adj2[(ti, wk)].append((tj, wj))
    return surviving, adj2, nodes2


def analyze_2d_cycles(L_star, max_cycle_len=20, max_cycles=300, verbose=True):
    """Full 2D product-graph cycle analysis.

    Given L* (the surviving transitions from the 2D fixed point):
      1. Enumerate simple cycles in the 2D product graph
      2. Extract t-walk and w-walk from each
      3. Build cycle-to-cycle witness map
      4. Decompose compound w-walks into 1D simple cycles
      5. Find orbits in the cycle map

    Returns dict with keys:
      'transitions': sorted L*
      'cycles_1d': list of 1D simple cycles (as tuples of indices)
      'cycles_2d': list of dicts per 2D cycle with keys:
          'idx', 't_walk', 'w_walk', 'len',
          'w_is_compound', 'w_as_2d_cycle', 'w_1d_decomp'
      'orbits': list of orbit lists (cycle index sequences)
    """
    Ls = sorted(set(L_star))
    n = len(Ls)
    if n == 0:
        return {'transitions': [], 'cycles_1d': [], 'cycles_2d': [], 'orbits': []}

    surviving, adj2, nodes2 = _build_2d_product_graph(Ls)
    ow = {(t[1], t[2]) for t in Ls}

    # ── 1D simple cycles in H* ────────────────────────────────
    adj1 = defaultdict(list)
    for i, ti in enumerate(Ls):
        for j, tj in enumerate(Ls):
            if tj[1] == ti[2] and (ti[0], tj[0]) in ow:
                adj1[i].append(j)

    raw_1d = []
    def find_1d(start, node, path, vis):
        if len(raw_1d) > max_cycles: return
        for nxt in adj1.get(node, []):
            if nxt == start and len(path) > 1:
                raw_1d.append(tuple(path))
            elif nxt not in vis and len(path) < min(n, max_cycle_len):
                vis.add(nxt); path.append(nxt)
                find_1d(start, nxt, path, vis)
                path.pop(); vis.discard(nxt)
    for s in range(n):
        find_1d(s, s, [s], {s})
        if len(raw_1d) > max_cycles: break

    # Canonicalize
    canon_1d = {}
    cycles_1d = []
    for cyc in raw_1d:
        mp = cyc.index(min(cyc))
        c = cyc[mp:] + cyc[:mp]
        if c not in canon_1d:
            canon_1d[c] = len(cycles_1d)
            cycles_1d.append(c)

    # ── 2D simple cycles in product graph ─────────────────────
    nlist = sorted(nodes2)
    nidx = {nd: i for i, nd in enumerate(nlist)}
    N2 = len(nlist)
    adj2_idx = defaultdict(list)
    for nd in nodes2:
        for w in adj2.get(nd, []):
            wi = nidx.get(w)
            if wi is not None:
                adj2_idx[nidx[nd]].append(wi)

    raw_2d = []
    def find_2d(start, node, path, vis):
        if len(raw_2d) > max_cycles: return
        for nxt in adj2_idx.get(node, []):
            if nxt == start and len(path) > 1:
                raw_2d.append(tuple(path))
            elif nxt not in vis and len(path) < max_cycle_len:
                vis.add(nxt); path.append(nxt)
                find_2d(start, nxt, path, vis)
                path.pop(); vis.discard(nxt)
    for s in range(N2):
        find_2d(s, s, [s], {s})
        if len(raw_2d) > max_cycles: break

    canon_2d = {}
    cycles_2d_raw = []
    for cyc in raw_2d:
        mp = cyc.index(min(cyc))
        c = cyc[mp:] + cyc[:mp]
        if c not in canon_2d:
            canon_2d[c] = len(cycles_2d_raw)
            cycles_2d_raw.append(c)

    # ── Analyze each 2D cycle ─────────────────────────────────
    cycles_2d = []
    for ci, cyc in enumerate(cycles_2d_raw):
        pairs = [nlist[v] for v in cyc]
        t_walk = tuple(p[0] for p in pairs)
        w_walk = tuple(p[1] for p in pairs)
        N = len(t_walk)
        is_compound = len(set(w_walk)) < N

        # Match w-walk against 2D cycles' t-walks (up to rotation)
        w_as_2d = None
        for cj, cyc2 in enumerate(cycles_2d_raw):
            t2 = tuple(nlist[v][0] for v in cyc2)
            if len(t2) != N:
                continue
            for rot in range(N):
                if t2[rot:] + t2[:rot] == w_walk:
                    w_as_2d = (cj, rot)
                    break
            if w_as_2d:
                break

        # Decompose w-walk into 1D simple cycles
        w_1d_decomp = []
        for start in range(N):
            for length in range(2, N + 1):
                sub = tuple(w_walk[(start + k) % N] for k in range(length))
                if len(set(sub)) != length:
                    continue
                # Check closure
                if Ls[sub[0]][1] != Ls[sub[-1]][2]:
                    continue
                closed = all(Ls[sub[(k+1) % length]][1] == Ls[sub[k]][2]
                             for k in range(length))
                if not closed:
                    continue
                mp = sub.index(min(sub))
                csub = sub[mp:] + sub[:mp]
                cj = canon_1d.get(csub)
                if cj is not None:
                    w_1d_decomp.append({'cycle_1d': cj, 'start': start, 'len': length})

        cycles_2d.append({
            'idx': ci,
            't_walk': t_walk,
            'w_walk': w_walk,
            'len': N,
            'w_is_compound': is_compound,
            'w_as_2d_cycle': w_as_2d,
            'w_1d_decomp': w_1d_decomp,
        })

    # ── Cycle-to-cycle map and orbits ─────────────────────────
    cycle_map = {}
    for d in cycles_2d:
        if d['w_as_2d_cycle'] is not None:
            cycle_map[d['idx']] = d['w_as_2d_cycle'][0]

    visited = set()
    orbits = []
    for start in range(len(cycles_2d)):
        if start in visited or start not in cycle_map:
            continue
        orbit = [start]
        visited.add(start)
        cur = cycle_map.get(start)
        while cur is not None and cur != start:
            if cur in visited:
                break
            orbit.append(cur)
            visited.add(cur)
            cur = cycle_map.get(cur)
        if cur == start:
            orbits.append(orbit)

    # ── Print results ─────────────────────────────────────────
    if verbose:
        print(f"L* = {Ls} ({n} transitions)")
        print(f"1D simple cycles in H*: {len(cycles_1d)}")
        print(f"2D simple cycles in product graph: {len(cycles_2d)}")

        print(f"\n1D simple cycles:")
        for ci, c in enumerate(cycles_1d):
            print(f"  c1d[{ci}] len {len(c)}: {[Ls[i] for i in c]}")

        print(f"\n2D simple cycles:")
        for d in cycles_2d:
            ci = d['idx']
            tw = [Ls[i] for i in d['t_walk']]
            ww = [Ls[i] for i in d['w_walk']]
            ctype = "COMPOUND" if d['w_is_compound'] else "simple"
            print(f"\n  C2d[{ci}] len {d['len']}:")
            print(f"    t-walk: {list(d['t_walk'])} = {tw}")
            print(f"    w-walk: {list(d['w_walk'])} = {ww}  [{ctype}]")

            if d['w_as_2d_cycle'] is not None:
                cj, rot = d['w_as_2d_cycle']
                print(f"    map: C2d[{ci}] → C2d[{cj}] (shift {rot})")
            else:
                print(f"    map: C2d[{ci}] → compound t-walk")

            if d['w_1d_decomp']:
                seen = set()
                for dd in d['w_1d_decomp']:
                    key = (dd['cycle_1d'], dd['start'])
                    if key not in seen:
                        seen.add(key)
                        print(f"    w contains c1d[{dd['cycle_1d']}] "
                              f"at pos {dd['start']}, len {dd['len']}")

        if orbits:
            print(f"\nCYCLE ORBITS:")
            for orb in orbits:
                chain = ' → '.join(f'C2d[{c}]' for c in orb)
                print(f"  {chain} → C2d[{orb[0]}]  (length {len(orb)} = K)")
                for c in orb:
                    tw = [Ls[i] for i in cycles_2d[c]['t_walk']]
                    print(f"    C2d[{c}]: {tw}")

    return {
        'transitions': Ls,
        'cycles_1d': cycles_1d,
        'cycles_2d': cycles_2d,
        'orbits': orbits,
        'cycle_map': cycle_map,
    }


def trace_witness_chains(L_star, max_depth=10, max_cycles=5000,
                         max_cycle_len=15, verbose=True):
    """Forward enabling map and circulation law for all simple cycles in L*.

    For each simple cycle C in L*:
      1. Construct ALL forward targets: target[k].pred = source[k].wr
      2. Match targets to known simple cycles (or identify as compound)
      3. Forward shift = (canonical_zero(source) - canonical_zero(target)) mod N
      4. Trace chains to find orbits and compute S(K)

    Returns (records, orbits).
    """
    Ls = sorted(set(L_star))
    n = len(Ls)
    if n == 0:
        return [], []

    by_pred_own = defaultdict(list)
    for i, t in enumerate(Ls):
        by_pred_own[(t[0], t[1])].append(i)

    # ── Find simple cycles in 1D H* ──────────────────────────
    adj_h = defaultdict(list)
    for i, ti in enumerate(Ls):
        for j, tj in enumerate(Ls):
            if tj[1] == ti[2]:
                adj_h[i].append(j)

    raw_1d = []
    def find_1d(start, node, path, vis):
        if len(raw_1d) > max_cycles:
            return
        for nxt in adj_h.get(node, []):
            if nxt == start and len(path) > 1:
                raw_1d.append(tuple(path))
            elif nxt not in vis and len(path) < max_cycle_len:
                vis.add(nxt); path.append(nxt)
                find_1d(start, nxt, path, vis)
                path.pop(); vis.discard(nxt)
    for s in range(n):
        find_1d(s, s, [s], {s})
        if len(raw_1d) > max_cycles:
            break

    canon_1d = {}
    cycles_1d = []
    for cyc in raw_1d:
        mp = cyc.index(min(cyc))
        c = cyc[mp:] + cyc[:mp]
        if c not in canon_1d:
            canon_1d[c] = len(cycles_1d)
            cycles_1d.append(c)

    def canonical_zero(walk):
        """Position of lex-min transition (by (pred,own,wr) tuple)."""
        best = 0
        for k in range(1, len(walk)):
            if Ls[walk[k]] < Ls[walk[best]]:
                best = k
        return best

    def canonicalize(walk):
        p = canonical_zero(walk)
        return tuple(walk[p:]) + tuple(walk[:p])

    def walk_type(walk):
        return 'S' if len(set(walk)) == len(walk) else 'C'

    def find_forward_targets(source):
        """Construct all forward target walks.
        target[k].pred = source[k].wr, with H-edge continuity."""
        N = len(source)
        written = [Ls[source[k]][2] for k in range(N)]
        results = []
        def build(k, chain):
            if len(results) > 20:
                return
            if k == N:
                if Ls[chain[-1]][2] == Ls[chain[0]][1]:
                    results.append(tuple(chain))
                return
            pred_needed = written[k]
            if k == 0:
                for own_val in set(Ls[i][1] for i in range(n)):
                    for idx in by_pred_own.get((pred_needed, own_val), []):
                        build(k + 1, [idx])
            else:
                own_needed = Ls[chain[-1]][2]
                for idx in by_pred_own.get((pred_needed, own_needed), []):
                    chain.append(idx)
                    build(k + 1, chain)
                    chain.pop()
        build(0, [])
        return results

    def forward_shift(source, raw_target):
        """shift = (canonical_zero(source) - canonical_zero(target)) mod N.
        For compound targets, pick minimum shift."""
        N = len(source)
        p_s = canonical_zero(source)
        min_t = min(Ls[raw_target[k]] for k in range(N))
        positions = [k for k in range(N) if Ls[raw_target[k]] == min_t]
        shifts = [(p_s - p_t) % N for p_t in positions]
        return min(shifts)

    # ── For each simple cycle, find all forward maps ──────────
    records = []
    for ci, cyc in enumerate(cycles_1d):
        N = len(cyc)
        targets = find_forward_targets(cyc)

        target_map = {}
        for ft in targets:
            canon_ft = canonicalize(ft)
            s = forward_shift(cyc, ft)
            cj = canon_1d.get(canon_ft)
            is_comp = len(set(ft)) < len(ft)
            key = canon_ft
            if key not in target_map or s < target_map[key][1]:
                target_map[key] = (cj, s, is_comp, ft)

        forward_edges = []
        for canon_ft, (cj, s, is_comp, raw_ft) in target_map.items():
            forward_edges.append({
                'target_cycle': cj,
                'target_canon': canon_ft,
                'shift': s,
                'is_compound': is_comp,
                'raw_target': raw_ft,
            })

        records.append({
            'cycle_idx': ci, 'N': N,
            'walk': cyc, 'type': walk_type(cyc),
            'forward_edges': forward_edges,
        })

    # ── Trace chains: for each simple cycle and each forward target,
    #    keep constructing forward targets until closure ─────────
    orbits = []
    seen_orbits = set()

    for ci, rec in enumerate(records):
        original_canon = canonicalize(rec['walk'])
        N = rec['N']

        for edge in rec['forward_edges']:
            chain = [(ci, edge['shift'], edge['target_canon'],
                       'S' if not edge['is_compound'] else 'C')]
            total_shift = edge['shift']
            current_raw = list(edge['raw_target'])

            for depth in range(max_depth):
                # Check if current walk is a rotation of original
                current_canon = canonicalize(current_raw)
                if current_canon == original_canon:
                    key = (ci, total_shift, len(chain))
                    if key not in seen_orbits:
                        seen_orbits.add(key)
                        orbits.append({
                            'start': ci,
                            'chain': list(chain),
                            'period': len(chain),
                            'S_p': total_shift,
                            'N': N,
                        })
                    break

                # Construct forward target of current walk
                next_targets = find_forward_targets(current_raw)
                if not next_targets:
                    break

                ft = next_targets[0]  # pick first valid target
                s = forward_shift(current_raw, ft)
                is_comp = len(set(ft)) < len(ft)
                ft_canon = canonicalize(ft)
                cj = canon_1d.get(ft_canon)
                tp = 'C' if is_comp else 'S'
                label = f"c[{cj}]" if cj is not None else "compound"

                chain.append((label, s, ft_canon, tp))
                total_shift += s
                current_raw = list(ft)

    # ── Verbose output ────────────────────────────────────────
    if verbose:
        active = [r for r in records if r['forward_edges']]
        dead = [r for r in records if not r['forward_edges']]
        print(f"L* = {n} transitions, {len(cycles_1d)} simple cycles in H*")
        print(f"  {len(active)} with forward targets, "
              f"{len(dead)} dead-ends (not in product graph)")
        print()
        print("FORWARD ENABLING MAP:")
        print()
        for rec in active:
            ci = rec['cycle_idx']
            N = rec['N']
            tp = 'simple' if rec['type'] == 'S' else 'compound'
            cyc_trans = [Ls[i] for i in rec['walk']]
            print(f"  c[{ci:>2}] N={N} [{tp}]: {cyc_trans}")
            for edge in rec['forward_edges']:
                cj = edge['target_cycle']
                s = edge['shift']
                etp = 'compound' if edge['is_compound'] else 'simple'
                target_trans = [Ls[i] for i in edge['target_canon']]
                if cj == ci:
                    print(f"       → self  [{etp}] shift={s}")
                else:
                    cj_str = f"c[{cj}]" if cj is not None else "compound"
                    print(f"       → {cj_str} [{etp}] shift={s}: {target_trans}")
            print()

        if orbits:
            print("CLOSING CHAINS & CIRCULATION LAW:")
            print()
            for orb in orbits:
                p = orb['period']
                SP = orb['S_p']
                N = orb['N']
                chain = orb['chain']
                ci_start = orb['start']

                # Build display
                parts = []
                for entry in chain:
                    label, s, canon, tp = entry
                    tp_str = 'simple' if tp == 'S' else 'compound'
                    if isinstance(label, int):
                        parts.append(f"c[{label}]({tp_str},s={s})")
                    else:
                        parts.append(f"{label}({tp_str},s={s})")
                chain_str = ' → '.join(parts)

                shift_str = '+'.join(str(entry[1]) for entry in chain)
                print(f"  {chain_str} → c[{ci_start}]")
                print(f"    period p={p}, S(p)={shift_str}={SP}, N={N}")
                print(f"    e ≡ S(K) mod {N}, 1 ≤ e ≤ K:")

                valid = []
                for km in range(1, 30):
                    Kv = km * p
                    Sv = km * SP
                    for e in range(1, Kv + 1):
                        if e % N == Sv % N:
                            valid.append((Kv, e))
                            break
                    if len(valid) >= 6:
                        break
                if valid:
                    vstr = ', '.join(f'K={k}(e={e})' for k, e in valid)
                    print(f"    {vstr}, ...")
                else:
                    print(f"    no valid K found")
                print()

    return records, orbits



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

def analyze(name, T_p0, T_other=None, expect=None, m=None, trace_cycles=False):
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

    if not sd0 or not sd1:
        if not sd0:
            print(f"  P_0 not self-disabling: {v0}")
            T_p0_aug, local_ll, cycle_info = augment_transitive_closure(T_p0, verbose=True)
            if local_ll:
                print(f"\n  => LIVELOCK (local cycle at pred={cycle_info[0]}) ✓" if expect == "LIVELOCK" else
                      f"\n  => LIVELOCK (local cycle at pred={cycle_info[0]})")
                return True
            T_p0 = T_p0_aug
        if not sd1:
            print(f"  P_other not self-disabling: {v1}")
            T_other_aug, local_ll, cycle_info = augment_transitive_closure(T_other, verbose=True)
            if local_ll:
                print(f"\n  => LIVELOCK (local cycle at pred={cycle_info[0]}) ✓" if expect == "LIVELOCK" else
                      f"\n  => LIVELOCK (local cycle at pred={cycle_info[0]})")
                return True
            T_other = T_other_aug
        # Recompute m after augmentation
        all_T = list(T_p0) + list(T_other)
        m = max(max(v,w,wp) for v,w,wp in all_T) + 1
        sym = (frozenset(T_p0) == frozenset(T_other))
        print(f"  After augmentation: |T_p0|={len(T_p0)}, |T_other|={len(T_other)}, sym={sym}")

    has_ll, k0, ko, graph_info = fixed_point(T_p0, T_other, verbose=True)

    if has_ll:
        print(f"\n  Kernel P0: {sorted(k0)}")
        print(f"  Kernel Po: {sorted(ko)}")

        if trace_cycles and sym and graph_info:
            print(f"\n  {'─'*50}")
            print(f"  CYCLE ANALYSIS (product graph)")
            print(f"  {'─'*50}")
            display_backward_graph(graph_info)

    # Determine status: LIVELOCK, FREE, or INCONCLUSIVE
    if has_ll:
        status = "LIVELOCK"
    elif k0 or ko:
        status = "INCONCLUSIVE"
    else:
        status = "NO LIVELOCK"

    ok = None
    if expect:
        if expect == "LIVELOCK":
            ok = has_ll
        elif expect == "NO LIVELOCK":
            ok = (not has_ll and not k0)
        elif expect == "INCONCLUSIVE":
            ok = (not has_ll and bool(k0))
    tag = " ✓" if ok else (" ✗" if ok is False else "")
    print(f"\n  => {status}{tag}")
    return has_ll


def wang_to_self_disabling(wang_tiles_ke, n_vert=None, n_horiz=None):
    """Convert Wang tiles to a self-disabling protocol via K&E's Lemma 4.8 gadget.

    Wang tiles are (W, N, S, E) in K&E convention.
    W and E use vertical colors (0..n_vert-1).
    N and S use horizontal colors (0..n_horiz-1).

    Returns a sorted list of (pred, own, wr) transitions.
    """
    if n_vert is None:
        n_vert = max(max(t[0], t[3]) for t in wang_tiles_ke) + 1
    if n_horiz is None:
        n_horiz = max(max(t[1], t[2]) for t in wang_tiles_ke) + 1

    DOLLAR = 0
    color_map = {'$': DOLLAR}
    next_id = 1
    for c in range(n_vert):
        color_map[('R', c)] = next_id
        next_id += 1
    for c in range(n_horiz):
        color_map[('U', c)] = next_id
        next_id += 1
    for tile in wang_tiles_ke:
        color_map[('C', tile)] = next_id
        next_id += 1

    T = []
    for w, n, s, e in wang_tiles_ke:
        comp = color_map[('C', (w, n, s, e))]
        T.extend([
            (color_map[('R', w)], color_map[('U', n)], comp),
            (DOLLAR, comp, color_map[('U', s)]),
            (comp, DOLLAR, color_map[('R', e)]),
            (color_map[('U', s)], color_map[('R', e)], DOLLAR),
        ])

    T = sorted(set(T))
    sd, viol = check_self_disabling(T)
    if not sd:
        raise ValueError(f"Gadget produced non-self-disabling protocol: {viol}")
    return T


# ═══════════════════════════════════════════════════════════════
#  TEST SUITE
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import sys
    trace = '--cycles' in sys.argv or '--trace' in sys.argv

    # Dijkstra token ring (asymmetric)
    for m in [3, 4, 5]:
        T0 = [(v, v, (v+1)%m) for v in range(m)]
        To = [(v, w, v) for v in range(m) for w in range(m) if v != w]
        analyze(f"Dijkstra (m={m})", T0, To, "LIVELOCK", trace_cycles=trace)

    # Sum-Not-2 deterministic
    m = 3
    analyze("Sum-Not-2 det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m) if (v+w)%m == m-1],
            expect="NO LIVELOCK", trace_cycles=trace)

    # Coloring deterministic
    analyze("3-Coloring det (m=3)",
            [(v,w,(w+1)%m) for v in range(m) for w in range(m) if w==v],
            expect="LIVELOCK", trace_cycles=trace)

    # Simple 2-cycle
    analyze("Simple 2-cycle (m=2)", [(0,1,0),(1,0,1)],
            expect="LIVELOCK", trace_cycles=trace)

    # Always-write-0
    analyze("Always-write-0 (m=3)",
            [(v,w,0) for v in range(3) for w in range(3) if w!=0],
            expect="NO LIVELOCK", trace_cycles=trace)

    # Non-det dead-ends
    analyze("Non-det dead-ends (m=3)",
            [(0,1,0),(0,1,2),(1,0,1),(2,1,2)],
            expect="LIVELOCK", trace_cycles=trace)

    # Maximal agreement
    m = 4
    analyze("Maximal agreement (m=4)",
            [(v, w, v) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK", trace_cycles=trace)

    # Non-det coloring
    analyze("Non-det coloring (m=4)",
            [(v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK", trace_cycles=trace)

    # Non-det sum-not-2
    m = 3
    analyze("Non-det sum-not-2 (m=3)",
            [(m-1-v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK", trace_cycles=trace)

    # Maximal agreement m=3
    analyze("Maximal agreement (m=3)",
            [(v, w, v) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK", trace_cycles=trace)

    # Non-det coloring m=3
    analyze("Non-det coloring (m=3)",
            [(v, v, w) for v in range(m) for w in range(m) if v != w],
            expect="LIVELOCK", trace_cycles=trace)

    # ── Adversarial / tricky protocols ────────────────────────

    # Trial 56 (seed=777): exposed the Phi operator bug.
    # 13 transitions, all survive edge-aware Phi, but shadow (6,5)
    # has no witness — no transition with own=6, wr=5 exists.
    # Product graph correctly identifies as livelock-free.
    analyze("Trial 56 — Phi bug exposer (m=8)",
            [(0,4,2),(0,7,6),(2,2,7),(2,5,7),(3,6,0),(4,0,2),(4,0,5),
             (5,2,0),(5,6,0),(6,3,4),(6,6,2),(7,0,6),(7,7,3)],
            expect="NO LIVELOCK", trace_cycles=trace)

    # Weird protocol: compound-only witness chains, K_min=3 with e=3.
    # Chain: simple → simple → compound → simple (period 3).
    # All forward shifts = 1, S(3) = 3, e ≡ 3 mod 4.
    # Also livelocks at K=6 with e=2 (different livelock class).
    analyze("Weird protocol — compound witnesses (m=16)",
            [(5,2,3),(8,3,2),(2,7,9),(3,9,12),(2,12,15),(3,15,7),
             (7,5,8),(9,8,5),(12,5,8),(15,8,5)],
            expect="LIVELOCK", trace_cycles=trace)

    # Shifted coloring: pred ≠ own. Self-witnessing with shift 0.
    # All processes fire same step simultaneously.
    analyze("Shifted coloring (m=3)",
            [(1,0,1),(2,1,2),(0,2,0)],
            expect="LIVELOCK", trace_cycles=trace)

    # Gouda-Haddix TB (symmetric): m=8, 32 transitions, rich structure.
    # L* has 14 transitions, multiple livelock classes with various
    # periods and shifts.
    TB = [(0,0,3),(0,1,6),(0,4,6),(0,5,6),(1,0,3),(1,1,6),(1,4,6),(1,5,6),
          (2,2,1),(2,3,4),(2,6,4),(2,7,4),(3,2,1),(3,3,4),(3,6,4),(3,7,4),
          (4,0,2),(4,1,2),(4,4,2),(4,5,2),(5,0,2),(5,1,2),(5,4,2),(5,5,2),
          (6,2,0),(6,3,0),(6,6,0),(6,7,0),(7,2,0),(7,3,0),(7,6,0),(7,7,0)]
    analyze("Gouda-Haddix TB symmetric (m=8)", TB,
            expect="LIVELOCK", trace_cycles=trace)

    # User's example: 6 transitions, livelock-free after label pruning.
    # Demonstrates the 2D (pred,value) shadow/label framework.
    analyze("User example — label pruning (m=5)",
            [(2,0,1),(1,1,2),(3,1,2),(2,2,3),(0,3,0),(4,3,0)],
            expect="NO LIVELOCK", trace_cycles=trace)

    # Random adversarial: heavy pruning (m=7, 31→7)
    analyze("Random s=42 t=2 (m=7, |T|=31->|L*|=7)",
            [(0,0,5),(0,4,1),(0,6,3),(1,3,2),(1,3,4),(1,3,5),(1,6,1),
             (2,4,1),(2,4,3),(2,5,3),(2,6,3),(3,0,1),(3,0,5),(3,3,2),
             (3,3,5),(3,4,6),(4,0,3),(4,1,5),(4,2,6),(4,4,5),(5,1,6),
             (5,2,3),(5,2,6),(5,4,3),(5,5,0),(6,0,2),(6,0,3),(6,4,1),
             (6,4,3),(6,4,5),(6,6,5)],
            expect="LIVELOCK", trace_cycles=trace)

    # Random adversarial: small m, nearly all survive (m=4, 12→11)
    analyze("Random s=42 t=14 (m=4, |T|=12->|L*|=11)",
            [(0,0,1),(0,0,2),(0,0,3),(1,1,0),(1,1,3),(1,2,0),(2,1,2),
             (2,3,0),(3,0,1),(3,0,2),(3,3,1),(3,3,2)],
            expect="LIVELOCK", trace_cycles=trace)

    # Random adversarial: large m (m=8, 40→13)
    analyze("Random s=42 t=16 (m=8, |T|=40->|L*|=13)",
            [(0,0,2),(0,1,4),(0,1,5),(0,3,4),(0,3,5),(0,6,7),(1,0,1),
             (1,0,4),(1,2,1),(1,5,1),(1,5,4),(1,5,6),(1,5,7),(2,1,3),
             (2,1,5),(2,2,3),(2,6,4),(3,1,0),(3,1,5),(3,1,7),(3,2,4),
             (3,2,7),(3,3,0),(3,6,5),(4,1,0),(4,4,2),(4,7,2),(5,1,3),
             (5,1,4),(5,2,3),(5,5,0),(5,6,0),(6,1,4),(6,2,5),(6,2,6),
             (6,7,5),(7,0,1),(7,0,6),(7,4,2),(7,5,3)],
            expect="LIVELOCK", trace_cycles=trace)

    # Random adversarial: minimal L* (m=5, 20→5)
    analyze("Random s=42 t=27 (m=5, |T|=20->|L*|=5)",
            [(0,0,1),(0,0,3),(0,4,3),(1,1,0),(1,1,3),(1,1,4),(1,2,4),
             (2,3,0),(2,3,1),(2,4,0),(2,4,2),(3,1,0),(3,1,4),(3,2,0),
             (3,2,3),(3,2,4),(4,1,4),(4,2,0),(4,3,0),(4,3,4)],
            expect="LIVELOCK", trace_cycles=trace)

    # Random livelock-free: m=7, 32 transitions
    analyze("Random s=42 t=1 FREE (m=7, |T|=32)",
            [(0,0,2),(0,0,4),(0,0,5),(0,3,4),(0,3,5),(1,2,0),(1,2,1),
             (1,2,3),(1,4,0),(1,6,1),(1,6,3),(2,2,1),(2,2,4),(2,2,6),
             (2,3,0),(2,5,6),(3,2,6),(3,4,0),(3,4,5),(4,0,4),(4,1,3),
             (4,5,2),(4,6,3),(4,6,4),(5,0,1),(5,4,1),(5,4,3),(5,5,1),
             (5,5,2),(5,6,2),(6,1,5),(6,4,2)],
            expect="NO LIVELOCK", trace_cycles=trace)

    # Random livelock-free: m=4, 13 transitions (shadow cascade)
    analyze("Random s=777 t=0 FREE (m=4, |T|=13)",
            [(0,1,0),(0,1,2),(0,1,3),(1,1,0),(1,1,2),(1,3,0),(2,1,0),
             (2,2,0),(2,3,0),(3,1,0),(3,1,2),(3,3,0),(3,3,2)],
            expect="NO LIVELOCK", trace_cycles=trace)

    # ── K&E adversarial protocol (from their SE tiling construction) ──
    analyze("K&E adversarial SE tiling (m=15)",
            [(0,5,9),(0,11,3),(3,14,6),(6,2,0),(9,8,6),(1,0,7),(1,3,4),
             (4,6,1),(7,9,10),(10,6,13),(13,0,1),(2,4,5),(2,10,11),
             (5,1,8),(8,7,2),(11,13,14),(14,1,2)],
            expect="LIVELOCK", trace_cycles=trace)

    # ── Kari's aperiodic Wang tiles via K&E's Lemma 4.8 gadget ───────
    # Kari (1996): 14-tile NW-deterministic set that tiles the plane
    # aperiodically. Via K&E's gadget, this becomes a 54-transition
    # self-disabling protocol. Since no periodic tiling exists,
    # no livelock should exist.
    print(f"\n{'═'*60}")
    print(f"  Kari aperiodic tiles via K&E gadget")
    print(f"  Expected: NO LIVELOCK (aperiodic = no periodic tiling)")
    print(f"{'═'*60}")
    T_kari = wang_to_self_disabling([
        # M2 tiles (W,N,S,E) in K&E convention — Kari's Mealy machine M2
        (5,0,1,4), (5,1,2,5), (4,1,1,5), (4,1,2,4),
        # M2/3 tiles — Kari's Mealy machine M2/3 (distinct vertical colors)
        (0,1,0,2), (0,2,1,1), (1,1,0,3), (1,1,1,0), (1,2,1,2),
        (2,1,1,1), (2,2,1,3), (2,2,2,0), (3,1,1,2), (3,2,2,1),
    ], n_vert=6, n_horiz=3)
    analyze("Kari aperiodic (14 tiles → 54 transitions)", T_kari,
            expect="INCONCLUSIVE", trace_cycles=trace)

    print(f"\n{'═'*60}\n  DONE\n{'═'*60}")

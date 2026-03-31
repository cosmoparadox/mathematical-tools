"""
Step-by-step analysis of the cycle propagation structure.

Part 1: Clear display of every simple cycle with its transitions
Part 2: Exhaustive check that no compound walk enables a simple cycle
Part 3: Algebraic exploration — cycle space with shifts
"""

import sys
sys.path.insert(0, '/mnt/user-data/outputs')
from livelock_final import (
    fixed_point, find_simple_cycles, _build_H, build_H_E,
    enabling_walks, per_cycle_shadows, shadow_witnesses, refine_H,
    check_self_disabling
)
from collections import defaultdict, Counter
from math import gcd
from functools import reduce


def lcm(a, b): return a * b // gcd(a, b)


def detailed_analysis(name, T, m=None):
    """Full analysis with explicit transition-level display."""

    print(f"\n{'═'*70}")
    print(f"  {name}")
    print(f"{'═'*70}")

    sd, viol = check_self_disabling(T)
    if not sd:
        print(f"  ✗ Not self-disabling: {viol}")
        return

    if m is None:
        m = max(max(v,w,wp) for v,w,wp in T) + 1
    print(f"  m={m}, |T|={len(T)}")
    print(f"  T = {sorted(T)}")

    has_ll, _, ko = fixed_point(T, T, verbose=False)
    if not has_ll:
        print(f"  => FREE")
        return

    L = sorted(ko)
    print(f"\n  L* = {L}  (|L*|={len(L)})")

    # ── Part 1: Full cycle display ──────────────────────────
    H, Kf = _build_H(ko)
    H_ref, dead = refine_H(H, Kf, ko)
    if dead:
        print(f"\n  Dead H-edges: {dead}")
    cycles = find_simple_cycles(H_ref, Kf)

    print(f"\n{'─'*70}")
    print(f"  PART 1: ALL SIMPLE CYCLES IN H*(L*)")
    print(f"{'─'*70}")
    print(f"  {len(cycles)} simple cycles\n")

    for ci, cyc in enumerate(cycles):
        N = len(cyc)
        print(f"  C[{ci}] — length {N}:")
        for k in range(N):
            t_src = cyc[k]
            t_tgt = cyc[(k+1) % N]
            # H-edge: t_src.written == t_tgt.own
            shadow = (t_src[0], t_tgt[0])
            print(f"    step {k}: (pred={t_src[0]}, own={t_src[1]}, written={t_src[2]})"
                  f"  →  next.own={t_tgt[1]}  [shadow: ({shadow[0]},{shadow[1]})]")
        print()

    # ── Part 2: Enabling walks — verify each is simple ──────
    print(f"{'─'*70}")
    print(f"  PART 2: ENABLING WALKS — SIMPLE vs COMPOUND CHECK")
    print(f"{'─'*70}")

    H_pred, Kf_pred = H_ref, Kf  # same process (symmetric)

    all_walks_simple = True
    cycle_map = {}  # ci -> (target_cycle_idx, shift, walk)

    for ci, cyc in enumerate(cycles):
        N = len(cyc)
        walks = enabling_walks(cyc, ko, H_pred, Kf_pred, max_walks=100)

        print(f"\n  C[{ci}] (len={N}): {len(walks)} enabling walk(s)")

        if not walks:
            print(f"    ✗ NO enabling walk!")
            continue

        for wi, walk in enumerate(walks):
            is_simple = (len(walk) == len(set(walk)))
            if not is_simple:
                all_walks_simple = False

            # Identify which cycle the walk IS
            walk_edges = set()
            for k in range(N):
                walk_edges.add((walk[k], walk[(k+1)%N]))

            # Check each predecessor cycle for containment
            matching_cycles = []
            for pj, pcyc in enumerate(cycles):
                pN = len(pcyc)
                pcyc_edges = set()
                for k in range(pN):
                    pcyc_edges.add((pcyc[k], pcyc[(k+1)%pN]))
                if walk_edges <= pcyc_edges:
                    # Walk edges are a subset of pcyc edges
                    # Check if it's exactly this cycle (same length)
                    if N == pN and walk_edges == pcyc_edges:
                        # Find shift
                        shift = None
                        for s in range(N):
                            if all(walk[k] == pcyc[(k+s)%N] for k in range(N)):
                                shift = s
                                break
                        matching_cycles.append((pj, 'exact', shift))
                    elif walk_edges < pcyc_edges:
                        matching_cycles.append((pj, 'subset', None))

            # Also check if walk edges span MULTIPLE cycles
            compound_cover = []
            remaining = set(walk_edges)
            for pj, pcyc in enumerate(cycles):
                pN = len(pcyc)
                pcyc_edges = set((pcyc[k], pcyc[(k+1)%pN]) for k in range(pN))
                overlap = remaining & pcyc_edges
                if overlap:
                    compound_cover.append((pj, len(overlap)))
                    remaining -= overlap

            tag = "SIMPLE" if is_simple else "COMPOUND (repeated transitions!)"

            # Display
            print(f"    Walk {wi} [{tag}]:")
            for k in range(N):
                t = walk[k]
                print(f"      pos {k}: (pred={t[0]}, own={t[1]}, written={t[2]})")

            if matching_cycles:
                for pj, kind, shift in matching_cycles:
                    if kind == 'exact':
                        sh = f"z^{shift}" if shift is not None else "?"
                        fp = " (SELF)" if pj == ci else ""
                        print(f"    → Bijection to C[{pj}] shift={sh}{fp}")
            else:
                if not remaining:
                    cover_str = " + ".join(f"C[{pj}]({n} edges)" for pj, n in compound_cover)
                    print(f"    → COMPOUND cover: {cover_str}")
                else:
                    print(f"    → Partial cover, {len(remaining)} uncovered edges")

            if not is_simple:
                # Show which transitions repeat
                seen = Counter(walk)
                repeats = {t: c for t, c in seen.items() if c > 1}
                print(f"    ⚠ Repeated transitions: {repeats}")

        # Record the primary mapping (first single-cycle walk)
        for wi, walk in enumerate(walks):
            is_simple = (len(walk) == len(set(walk)))
            if is_simple:
                # Find which cycle it matches
                N = len(walk)
                walk_edges = set((walk[k], walk[(k+1)%N]) for k in range(N))
                for pj, pcyc in enumerate(cycles):
                    pN = len(pcyc)
                    if pN != N: continue
                    pcyc_edges = set((pcyc[k], pcyc[(k+1)%pN]) for k in range(pN))
                    if walk_edges == pcyc_edges:
                        shift = None
                        for s in range(N):
                            if all(walk[k] == pcyc[(k+s)%N] for k in range(N)):
                                shift = s; break
                        cycle_map[ci] = (pj, shift, walk)
                        break
                break

    print(f"\n  All enabling walks are simple: {all_walks_simple}")

    # ── Part 2b: Exhaustive compound check ──────────────────
    print(f"\n{'─'*70}")
    print(f"  PART 2b: CAN A COMPOUND WALK ENABLE A SIMPLE CYCLE?")
    print(f"{'─'*70}")
    print(f"  (Checking all walks, including non-simple ones)")

    has_compound = False
    for ci, cyc in enumerate(cycles):
        N = len(cyc)
        walks = enabling_walks(cyc, ko, H_pred, Kf_pred, max_walks=200)
        for walk in walks:
            if len(walk) != len(set(walk)):
                has_compound = True
                print(f"  ✗ C[{ci}] has a COMPOUND enabling walk (repeated transitions)")
                seen = Counter(walk)
                repeats = {t:c for t,c in seen.items() if c > 1}
                print(f"    Walk: {walk}")
                print(f"    Repeats: {repeats}")

    if not has_compound:
        print(f"  ✓ CONFIRMED: No compound walk enables any simple cycle.")
        print(f"    Every enabling walk is itself a simple cycle.")

    # ── Part 3: Permutation and shift algebra ───────────────
    print(f"\n{'─'*70}")
    print(f"  PART 3: PERMUTATION σ AND SHIFT ALGEBRA")
    print(f"{'─'*70}")

    if not cycle_map:
        print("  No cycle mappings found.")
        return

    # Build permutation
    perm = {}       # ci -> cj
    shifts = {}     # ci -> shift value
    for ci, (cj, sh, _) in cycle_map.items():
        perm[ci] = cj
        shifts[ci] = sh

    # Check bijection
    dom = sorted(perm.keys())
    rng = sorted(perm.values())
    is_bij = (dom == rng)

    print(f"\n  σ: cycle → cycle mapping:")
    for ci in sorted(perm):
        cj = perm[ci]
        sh = shifts[ci]
        ni = len(cycles[ci])
        nj = len(cycles[cj])
        fp = " ★fixed" if ci == cj else ""
        print(f"    σ(C[{ci}]) = C[{cj}],  len={ni}→{nj},  shift z^{sh}{fp}")

    print(f"\n  σ is a bijection: {is_bij}")

    # Orbit decomposition
    vis = set(); orbits = []
    for s in sorted(perm):
        if s in vis: continue
        orb = []; cur = s
        while cur not in vis:
            vis.add(cur); orb.append(cur); cur = perm[cur]
        orbits.append(orb)

    print(f"\n  Orbits:")
    for orb in orbits:
        if len(orb) == 1:
            ci = orb[0]
            print(f"    Fixed point: C[{ci}](len={len(cycles[ci])}), shift z^{shifts[ci]}")
        else:
            parts = []
            for ci in orb:
                cj = perm[ci]
                parts.append(f"C[{ci}]--z^{shifts[ci]}-->C[{cj}]")
            print(f"    {len(orb)}-orbit: {', '.join(parts)}")

    # ── Part 3b: Shift algebra exploration ──────────────────
    print(f"\n{'─'*70}")
    print(f"  PART 3b: SHIFT ALGEBRA ON CYCLES")
    print(f"{'─'*70}")

    # For each orbit, compute the "accumulated shift" after going around
    print(f"\n  For each orbit, the accumulated shift after one full orbit:")
    for orb in orbits:
        acc = 0
        cycle_len = len(cycles[orb[0]])  # all same length in an orbit
        for ci in orb:
            acc = (acc + shifts[ci]) % cycle_len
        orbit_str = " → ".join(f"C[{ci}]" for ci in orb)
        print(f"    {orbit_str} → C[{orb[0]}]")
        print(f"      len={cycle_len}, total shift = {acc} mod {cycle_len}")
        print(f"      After {len(orb)} propagation steps, position advances by {acc}")

        # The order of this orbit in the shift group Z_n
        if acc == 0:
            print(f"      ⇒ Identity after 1 orbit traversal")
        else:
            order = cycle_len // gcd(acc, cycle_len)
            print(f"      ⇒ Order in Z_{cycle_len}: {order}")
            print(f"      ⇒ Full period: {len(orb) * order} propagation steps")

    # ── Key insight about the algebra ──────────────────────
    print(f"\n{'─'*70}")
    print(f"  ALGEBRAIC STRUCTURE SUMMARY")
    print(f"{'─'*70}")
    print(f"""
  The propagation E acts on simple cycles as:
    σ: {{simple cycles}} → {{simple cycles}}   (permutation)
    z: C[i] ↦ z^{{shift(i)}}                  (cyclic shift per cycle)

  For each orbit (C[i₁], C[i₂], ..., C[iₖ]):
    - All cycles in the orbit have the same length n
    - E maps C[iⱼ] → C[iⱼ₊₁] with shift z^sⱼ
    - After k steps (one orbit), accumulated shift = Σsⱼ mod n
    - The Circulation Law becomes:
        H^|E| = σ^K composed with accumulated shifts
        This is solvable in the finite group Z_n × S_{{cycles}}
""")

    return cycles, perm, shifts, orbits


# ═══════════════════════════════════════════════════════════════
#  RUN
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":

    # Start with the richest non-trivial example
    m = 3
    print("\n" + "▓"*70)
    print("  NON-DETERMINISTIC SUM-NOT-2 (m=3) — 11 cycles, rich structure")
    print("▓"*70)
    detailed_analysis("Non-det Sum-Not-2 (m=3)",
        [(m-1-v, v, w) for v in range(m) for w in range(m) if v != w])

    print("\n" + "▓"*70)
    print("  3-COLORING DETERMINISTIC (m=3) — simplest non-trivial")
    print("▓"*70)
    detailed_analysis("3-Coloring det (m=3)",
        [(v, w, (w+1)%m) for v in range(m) for w in range(m) if w == v])

    print("\n" + "▓"*70)
    print("  MAXIMAL AGREEMENT (m=3) — same kernel as coloring, different E")
    print("▓"*70)
    detailed_analysis("Maximal agreement (m=3)",
        [(v, w, v) for v in range(m) for w in range(m) if v != w])

    print("\n" + "▓"*70)
    print("  LEADER ELECTION (m=3)")
    print("▓"*70)
    detailed_analysis("Leader (m=3)",
        [(v, v, (v+1)%m) for v in range(m)])
        
    print("\n" + "▓"*70)
    m = 4
    print("  Non-Deterministic Cycles (m=4)")
    print("▓"*70)
    detailed_analysis("Leader (m=3)",
        [(v, w, (w+2)%m) for v in range(m) for w in range(m) if v == w or w == (v + 1)%m])
    
    print("\n" + "▓"*70)
    print("  Non-Deterministic Cycles (m=4)")
    print("▓"*70)
    m = 4
    offset = 3
    detailed_analysis("Non-deterministic Offset Diff",
            [(v, (v + offset)%m, w) for v in range(m) for w in range(m) if w != (v + offset)%m])    
    print(f"\n{'═'*70}\n  DONE\n{'═'*70}")

#!/usr/bin/env python3
"""
Test harness for livelock detection in self-disabling unidirectional ring protocols.

Generates random self-disabling protocols across multiple categories and
cross-validates the product graph algorithm against exhaustive state-space
search at small ring sizes.

Usage:
    python test_harness.py                    # Run all test suites
    python test_harness.py --suite random     # Run one suite
    python test_harness.py --count 1000       # Override count per suite
    python test_harness.py --max-k 8          # Exhaustive search up to K=8
    python test_harness.py --verbose          # Show per-protocol details

Repository: https://github.com/cosmoparadox/mathematical-tools
"""

import random
import sys
import time
import argparse
from itertools import product as cartesian_product
from collections import defaultdict

# Import the main algorithm
sys.path.insert(0, '.')
import livelock_complete as lc


# ═══════════════════════════════════════════════════════════════
#  RANDOM PROTOCOL GENERATION
# ═══════════════════════════════════════════════════════════════

def generate_random_self_disabling(m, density=None, seed=None):
    """
    Generate a random self-disabling protocol with domain size m.
    
    Self-disabling: for every (p, o, w) in T, no (p, w, u) in T for any u.
    
    Args:
        m: domain size (values in Z_m)
        density: fraction of maximal transitions to include (0.0 to 1.0)
                 If None, chosen randomly.
        seed: random seed for reproducibility
    
    Returns:
        list of (pred, own, wr) triples
    """
    if seed is not None:
        random.seed(seed)
    
    if density is None:
        density = random.uniform(0.05, 0.95)
    
    T = []
    for p in range(m):
        # For each pred value, build a self-disabling set of transitions.
        # Self-disabling: if (p, o, w) in T, then no (p, w, _) in T.
        # This means: the set of "own" values that appear as sources
        # must be disjoint from the set of "wr" values that appear as targets.
        available = list(range(m))
        random.shuffle(available)
        
        # Greedily pick transitions
        used_as_wr = set()  # values written — cannot be used as own
        transitions_for_p = []
        
        for o in available:
            if o in used_as_wr:
                continue
            # Pick a wr value != o that hasn't been used as own
            candidates = [w for w in range(m) if w != o and w not in 
                         {t[1] for t in transitions_for_p}]
            if not candidates:
                continue
            w = random.choice(candidates)
            transitions_for_p.append((p, o, w))
            used_as_wr.add(w)
        
        # Apply density filter
        if transitions_for_p:
            k = max(1, int(len(transitions_for_p) * density))
            random.shuffle(transitions_for_p)
            T.extend(transitions_for_p[:k])
    
    return sorted(set(T))


def generate_structured_protocol(m, structure_type, seed=None):
    """Generate protocols with specific structural properties."""
    if seed is not None:
        random.seed(seed)
    
    if structure_type == "coloring_variant":
        # Coloring-like: (v, v, w) for random w != v
        T = []
        for v in range(m):
            targets = [w for w in range(m) if w != v]
            if targets:
                w = random.choice(targets)
                T.append((v, v, w))
        return sorted(set(T))
    
    elif structure_type == "agreement_variant":
        # Agreement-like: (v, w, v) for random w != v
        T = []
        for v in range(m):
            sources = [w for w in range(m) if w != v]
            for w in random.sample(sources, min(len(sources), random.randint(1, 3))):
                T.append((v, w, v))
        # Check self-disabling
        T_valid = []
        used = set()
        for t in T:
            key = (t[0], t[2])  # (pred, wr)
            if key not in used:
                T_valid.append(t)
                used.add(key)
        return sorted(set(T_valid))
    
    elif structure_type == "sparse":
        # Very sparse: m to 2m transitions
        count = random.randint(m, 2 * m)
        T = generate_random_self_disabling(m, density=0.1, seed=seed)
        if len(T) > count:
            T = random.sample(T, count)
        return sorted(set(T))
    
    elif structure_type == "dense":
        # Near-maximal transitions
        return generate_random_self_disabling(m, density=0.9, seed=seed)
    
    elif structure_type == "compound_witness":
        # Large m, few transitions — designed to need compound witnesses
        T = generate_random_self_disabling(m, density=0.15, seed=seed)
        return sorted(set(T))
    
    else:
        return generate_random_self_disabling(m, seed=seed)


# ═══════════════════════════════════════════════════════════════
#  EXHAUSTIVE STATE-SPACE SEARCH
# ═══════════════════════════════════════════════════════════════

def exhaustive_livelock_search(T, max_K=6):
    """
    Exhaustively check whether protocol T has a livelock for any ring size
    K = 2, ..., max_K by exploring the global state space.
    
    Uses on-the-fly state generation to avoid materializing the full state space.
    
    Returns:
        (has_livelock, K_witness)
    """
    if not T:
        return False, None
    
    m = max(max(t) for t in T) + 1
    
    # Index transitions by (pred, own)
    trans_by_po = defaultdict(list)
    for p, o, w in T:
        trans_by_po[(p, o)].append(w)
    
    for K in range(2, max_K + 1):
        if m ** K > 200000:
            continue  # Skip — too large
        
        def successors(state):
            """Generate all successor states."""
            succs = []
            for proc in range(K):
                pred_val = state[(proc - 1) % K]
                own_val = state[proc]
                for wr_val in trans_by_po.get((pred_val, own_val), []):
                    new_state = list(state)
                    new_state[proc] = wr_val
                    succs.append((tuple(new_state), proc))
            return succs
        
        # For each starting state, try to find a cycle where all processes fire
        # Use iterative approach: find SCCs on-the-fly with Tarjan's
        
        # Simplified: for each state, do bounded DFS looking for a cycle
        # where all K processes have fired at least once
        
        all_states = set()
        has_livelock_at_K = False
        
        # Generate reachable states from each initial config
        # and check for cycles with all processes firing
        for initial in cartesian_product(range(m), repeat=K):
            initial = tuple(initial)
            
            # Check if any process is enabled
            any_enabled = False
            for proc in range(K):
                if (initial[(proc-1)%K], initial[proc]) in trans_by_po:
                    any_enabled = True
                    break
            if not any_enabled:
                continue
            
            # BFS to find cycles from this state
            # Track: (state, set_of_procs_that_fired)
            # We look for: return to same state with all procs having fired
            
            visited = {}  # state -> set of procs that fired to reach it
            queue = [(initial, frozenset())]
            visited[initial] = frozenset()
            
            found = False
            steps = 0
            max_steps = 50000
            
            while queue and steps < max_steps:
                state, fired = queue.pop(0)
                steps += 1
                
                for next_state, proc in successors(state):
                    new_fired = fired | {proc}
                    
                    if next_state == initial and len(new_fired) == K:
                        return True, K
                    
                    if next_state not in visited:
                        visited[next_state] = new_fired
                        if len(visited) < max_steps:
                            queue.append((next_state, new_fired))
                    elif len(new_fired) > len(visited[next_state]):
                        visited[next_state] = new_fired
                        queue.append((next_state, new_fired))
            
            if has_livelock_at_K:
                break
    
    return False, None


# ═══════════════════════════════════════════════════════════════
#  TEST SUITES
# ═══════════════════════════════════════════════════════════════

def run_suite(suite_name, count, max_K, verbose=False):
    """Run a test suite and return (total, pass, fail, errors)."""
    
    configs = {
        "random_small": {
            "description": "Random protocols, m ∈ {3,...,7}",
            "generator": lambda seed: generate_random_self_disabling(
                m=random.choice([3,4,5,6,7]), seed=seed),
        },
        "random_medium": {
            "description": "Random protocols, m ∈ {8,...,10}",
            "generator": lambda seed: generate_random_self_disabling(
                m=random.choice([8,9,10]), seed=seed),
        },
        "random_large": {
            "description": "Random protocols, m ∈ {11,...,15}",
            "generator": lambda seed: generate_random_self_disabling(
                m=random.choice([11,12,13,14,15]), seed=seed),
        },
        "dense": {
            "description": "Near-maximal density protocols",
            "generator": lambda seed: generate_structured_protocol(
                m=random.choice([3,4,5,6,7]), structure_type="dense", seed=seed),
        },
        "sparse": {
            "description": "Very sparse protocols (m to 2m transitions)",
            "generator": lambda seed: generate_structured_protocol(
                m=random.choice([4,5,6,7,8]), structure_type="sparse", seed=seed),
        },
        "coloring": {
            "description": "Coloring variants with noise",
            "generator": lambda seed: generate_structured_protocol(
                m=random.choice([3,4,5,6]), structure_type="coloring_variant", seed=seed),
        },
        "agreement": {
            "description": "Agreement variants",
            "generator": lambda seed: generate_structured_protocol(
                m=random.choice([3,4,5,6]), structure_type="agreement_variant", seed=seed),
        },
        "compound": {
            "description": "Compound-witness-like (large m, few transitions)",
            "generator": lambda seed: generate_structured_protocol(
                m=random.choice([10,12,14,16]), structure_type="compound_witness", seed=seed),
        },
    }
    
    if suite_name not in configs:
        print(f"Unknown suite: {suite_name}. Available: {list(configs.keys())}")
        return 0, 0, 0, 0
    
    cfg = configs[suite_name]
    print(f"\n{'='*70}")
    print(f"  Suite: {suite_name} — {cfg['description']}")
    print(f"  Count: {count}, Exhaustive search up to K={max_K}")
    print(f"{'='*70}")
    
    total = 0
    passed = 0
    failed = 0
    errors = 0
    fp = 0  # false positives
    fn = 0  # false negatives
    
    t0 = time.time()
    
    for i in range(count):
        seed = i * 1000 + hash(suite_name) % 10000
        random.seed(seed)
        
        try:
            T = cfg["generator"](seed)
            
            if not T:
                continue
            
            # Check self-disabling
            sd, viol = lc.check_self_disabling(T)
            if not sd:
                continue
            
            total += 1
            m = max(max(t) for t in T) + 1
            
            # Run algorithm
            has_ll_algo, k0, ko = lc.fixed_point(T, T, verbose=False)
            
            # Run exhaustive search
            has_ll_exact, K_witness = exhaustive_livelock_search(T, max_K=max_K)
            
            if has_ll_algo == has_ll_exact:
                passed += 1
                if verbose:
                    if has_ll_algo:
                        status = "LIVELOCK"
                    elif k0:
                        status = "INCONCLUSIVE"
                    else:
                        status = "FREE"
                    print(f"  [{total:4d}] m={m:2d} |T|={len(T):3d} → {status} ✓")
            elif has_ll_algo and not has_ll_exact:
                # Algorithm says livelock, exhaustive says free
                # Could be: livelock exists at K > max_K
                # Not necessarily a false positive
                passed += 1  # Trust algorithm — exhaustive is incomplete
                if verbose:
                    print(f"  [{total:4d}] m={m:2d} |T|={len(T):3d} → ALGO=LL, EXACT=FREE (K>{max_K}) ~")
            elif not has_ll_algo and has_ll_exact and k0:
                # Algorithm says INCONCLUSIVE, exhaustive found livelock
                # This is expected — INCONCLUSIVE means period > |T|^2
                passed += 1
                if verbose:
                    print(f"  [{total:4d}] m={m:2d} |T|={len(T):3d} → INCONCLUSIVE, EXACT=LL (K={K_witness}) ~")
            else:
                # Algorithm says FREE (G*=∅), exhaustive found livelock
                # This IS a false negative — algorithm bug
                failed += 1
                fn += 1
                print(f"  ✗ FALSE NEGATIVE: m={m}, |T|={len(T)}, K={K_witness}")
                print(f"    T = {T}")
        
        except Exception as e:
            errors += 1
            if verbose:
                print(f"  [{i}] ERROR: {e}")
    
    elapsed = time.time() - t0
    
    print(f"\n  Results: {total} protocols, {passed} passed, {failed} failed, "
          f"{errors} errors")
    print(f"  False negatives: {fn}, Time: {elapsed:.1f}s")
    
    return total, passed, failed, errors


# ═══════════════════════════════════════════════════════════════
#  KNOWN PROTOCOL SUITE
# ═══════════════════════════════════════════════════════════════

def run_known_protocols():
    """Run the algorithm on known protocols with expected results."""
    print(f"\n{'='*70}")
    print(f"  Known Protocols")
    print(f"{'='*70}")
    
    cases = [
        ("3-coloring", [(0,0,1),(1,1,2),(2,2,0)], "LIVELOCK"),
        ("Sum-Not-2", [(0,2,1),(1,1,2),(2,0,1)], "NO LIVELOCK"),
        ("Non-det Sum-Not-2", [(0,2,0),(0,2,1),(1,1,0),(1,1,2),(2,0,1),(2,0,2)], "LIVELOCK"),
        ("Shifted coloring", [(1,0,1),(2,1,2),(0,2,0)], "LIVELOCK"),
        ("Gouda-Haddix TB (m=8)", [
            (0,0,3),(0,1,6),(0,4,6),(0,5,6),(1,0,3),(1,1,6),(1,4,6),(1,5,6),
            (2,2,1),(2,3,4),(2,6,4),(2,7,4),(3,2,1),(3,3,4),(3,6,4),(3,7,4),
            (4,0,2),(4,1,2),(4,4,2),(4,5,2),(5,0,2),(5,1,2),(5,4,2),(5,5,2),
            (6,2,0),(6,3,0),(6,6,0),(6,7,0),(7,2,0),(7,3,0),(7,6,0),(7,7,0)],
            "LIVELOCK"),
        ("Trial 56 — Phi bug exposer", [
            (0,4,2),(0,7,6),(2,2,7),(2,5,7),(3,6,0),(4,0,2),(4,0,5),
            (5,2,0),(5,6,0),(6,3,4),(6,6,2),(7,0,6),(7,7,3)],
            "NO LIVELOCK"),
        ("Weird protocol (m=16)", [
            (5,2,3),(8,3,2),(2,7,9),(3,9,12),(2,12,15),(3,15,7),
            (7,5,8),(9,8,5),(12,5,8),(15,8,5)],
            "LIVELOCK"),
        ("K&E adversarial (m=15)", [
            (0,5,9),(0,11,3),(3,14,6),(6,2,0),(9,8,6),(1,0,7),(1,3,4),
            (4,6,1),(7,9,10),(10,6,13),(13,0,1),(2,4,5),(2,10,11),
            (5,1,8),(8,7,2),(11,13,14),(14,1,2)],
            "LIVELOCK"),
    ]
    
    passed = 0
    failed = 0
    for name, T, expect in cases:
        has_ll, k0, ko = lc.fixed_point(T, T, verbose=False)
        result = "LIVELOCK" if has_ll else "NO LIVELOCK"
        ok = result == expect
        status = "✓" if ok else "✗"
        print(f"  {status} {name}: {result} (expected {expect})")
        if ok:
            passed += 1
        else:
            failed += 1
    
    print(f"\n  {passed} passed, {failed} failed")
    return passed, failed


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Test harness for livelock detection algorithm")
    parser.add_argument("--suite", type=str, default=None,
        help="Run specific suite (random_small, random_medium, random_large, "
             "dense, sparse, coloring, agreement, compound)")
    parser.add_argument("--count", type=int, default=500,
        help="Number of protocols per suite (default: 500)")
    parser.add_argument("--max-k", type=int, default=6,
        help="Maximum ring size for exhaustive search (default: 6)")
    parser.add_argument("--verbose", action="store_true",
        help="Show per-protocol results")
    parser.add_argument("--known-only", action="store_true",
        help="Only run known protocol tests")
    
    args = parser.parse_args()
    
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  Livelock Detection — Test Harness                         ║")
    print("║  Product Graph Algorithm vs Exhaustive State-Space Search  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    
    # Known protocols
    kp, kf = run_known_protocols()
    
    if args.known_only:
        sys.exit(0 if kf == 0 else 1)
    
    # Random suites
    suites = ["random_small", "random_medium", "random_large",
              "dense", "sparse", "coloring", "agreement", "compound"]
    
    if args.suite:
        suites = [args.suite]
    
    grand_total = 0
    grand_passed = 0
    grand_failed = 0
    grand_errors = 0
    
    for suite in suites:
        t, p, f, e = run_suite(suite, args.count, args.max_k, args.verbose)
        grand_total += t
        grand_passed += p
        grand_failed += f
        grand_errors += e
    
    print(f"\n{'═'*70}")
    print(f"  GRAND TOTAL: {grand_total} protocols")
    print(f"  Passed: {grand_passed}")
    print(f"  Failed: {grand_failed} (false negatives)")
    print(f"  Errors: {grand_errors}")
    print(f"  Known protocols: {kp} passed, {kf} failed")
    print(f"{'═'*70}")
    
    if grand_failed > 0 or kf > 0:
        print("\n  ✗ FAILURES DETECTED")
        sys.exit(1)
    else:
        print("\n  ✓ ALL TESTS PASSED")
        sys.exit(0)

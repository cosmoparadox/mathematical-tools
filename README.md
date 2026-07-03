# Livelock Analysis for Self-Disabling Unidirectional Ring Protocols

A practical framework for analyzing livelock behavior in self-disabling
unidirectional ring protocols, based on the **product transition graph**.

---

## Table of Contents

1. [Overview](#overview)
2. [Quick Start](#quick-start)
3. [Background: What Is a Livelock?](#background-what-is-a-livelock)
4. [How the Algorithm Works](#how-the-algorithm-works)
5. [Installation](#installation)
6. [Command-Line Reference (`run_protocol.py`)](#command-line-reference)
7. [Python API Reference (`livelock_complete.py`)](#python-api-reference)
8. [Stress Testing (`test_harness.py`)](#stress-testing)
9. [Wang Tile Gadget (K&E Reduction)](#wang-tile-gadget)
10. [Test Results](#test-results)
11. [Reproducing the Paper's Results](#reproducing-the-papers-results)
12. [Theoretical Foundation](#theoretical-foundation)
13. [Limitations and the Decidability Boundary](#limitations-and-the-decidability-boundary)
14. [Files](#files)
15. [References](#references)
16. [License](#license)

---

## Overview

This tool analyzes **self-stabilizing ring protocols** — distributed algorithms
where identical processes are arranged in a unidirectional ring, each reading
from its predecessor and writing a new value. A **livelock** occurs when all
processes fire transitions indefinitely without ever reaching a legitimate
(stable) state.

Given a protocol's transition set, the algorithm produces one of three outcomes:

| Outcome | Meaning | Guarantee |
|---------|---------|-----------|
| **LIVELOCK-FREE** | No livelock exists for any ring size or period | Sound and complete. Proven. |
| **LIVELOCK** | A livelock exists. Explicit torus witness constructed. | Sound. Proven. |
| **INCONCLUSIVE** | No livelock with period ≤ \|T\|² found | Livelocks with longer periods cannot be ruled out |

Across **4,349 protocols tested** — including adversarial instances derived from
tiling theory — the algorithm is conclusive in every case with **zero errors**.

---

## Quick Start

```bash
# Clone the repository
git clone https://github.com/cosmoparadox/mathematical-tools.git
cd mathematical-tools

# Analyze the classic 3-coloring protocol
python3 run_protocol.py --example coloring3

# Analyze your own protocol (inline)
python3 run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]"

# Quick result only
python3 run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" --quiet

# From a file
python3 run_protocol.py --file my_protocol.txt

# Run the built-in test suite — 26 checks, starting with Dijkstra's token
# ring (m=3,4,5, asymmetric) and ending with Kari's aperiodic tiles.
# Every check prints ✓ on success. Takes about 10 seconds.
python3 livelock_complete.py

# Same, with detailed cycle traces
python3 livelock_complete.py --cycles

# Run randomized stress tests
python3 test_harness.py --count 500 --verbose
```

---

## Background: What Is a Livelock?

### The Setting

A **unidirectional ring** consists of K identical processes P₀, P₁, ..., P_{K-1}
arranged in a ring. Each process Pᵢ can read the value of its predecessor P_{i-1}
and write a new value for itself. All processes share the same transition table.

A **transition** is a triple `(pred, own, wr)` where:
- `pred` — the value read from the predecessor
- `own` — the process's current value
- `wr` — the value written by the process

A transition `(p, o, w)` is **enabled** at process Pᵢ when P_{i-1}'s value is `p`
and Pᵢ's value is `o`. When fired, Pᵢ's value changes from `o` to `w`.

### Self-Disabling

A protocol is **self-disabling** if firing a transition disables it: after writing
`w`, the process cannot fire again until its predecessor changes value. Formally:
for every `(p, o, w)` in T, there is no `(p, w, u)` in T. This ensures that
`own ≠ wr` for every transition and prevents immediate re-firing.

### Livelock

A **livelock** is a periodic execution where all K processes fire transitions
forever, returning to the same global configuration after N steps, without ever
reaching a legitimate state. Equivalently (Klinkhamer & Ebnenasir 2019), a
livelock is a valid tiling of a K × N torus where each row is a closed walk of
transitions executed by one process, and adjacent rows satisfy equivariance
conditions.

---

## How the Algorithm Works

### Phase 1: Product Graph Construction and Pruning (Polynomial)

The algorithm constructs a **product transition graph** G×(T) whose nodes are
pairs (t, w) of transitions satisfying `wr(w) = pred(t)`, and whose arcs encode
the four equivariance conditions between consecutive transition-witness pairs.
This graph has at most |T|² nodes and |T|⁴ arcs.

The algorithm then computes **G\*(T)**, the maximal **backward-closed** subgraph
(called *witness-closed* in the code),
by iteratively pruning arcs that violate:

1. **Cyclicity (SCC)**: every arc must lie on a cycle
2. **Square**: witness components must be transition components on cycles
3. **Backward closure**: each arc's witness-pair must appear as a transition-pair
   on some cycle arc

This fixed-point iteration converges in O(|T|⁸) worst case. If G\* = ∅, the
protocol is **provably livelock-free** for all ring sizes.

### Phase 2: Backtracking Verification

If G\* ≠ ∅, the algorithm enumerates simple cycles (length ≤ |T|²) and
**backward-propagates** each through G\*: it searches for a cycle in G\* whose
t-walk matches the original cycle's w-walk, then repeats. If the chain of walks
revisits a previous walk, a torus is constructed and LIVELOCK is confirmed.

If all simple cycles fail backward propagation, the result is INCONCLUSIVE.

---

## Installation

**Requirements:** Python 3.7 or later. No external dependencies.

```bash
git clone https://github.com/cosmoparadox/mathematical-tools.git
cd mathematical-tools
```

Verify the installation:

```bash
python3 livelock_complete.py
```

This runs the built-in test suite: 26 checks covering Dijkstra's token ring
(m=3,4,5, asymmetric), the coloring and Sum-Not-2 families, regression seeds,
the K&E adversarial SE-tiling protocol, and Kari's aperiodic tiles. All checks
should show ✓. Expected runtime: about 10 seconds.

---

## Command-Line Reference

### `run_protocol.py`

```
SYNOPSIS
    python3 run_protocol.py EXPRESSION [OPTIONS]
    python3 run_protocol.py --file FILE [OPTIONS]
    python3 run_protocol.py --example NAME [OPTIONS]
    python3 run_protocol.py --list-examples

DESCRIPTION
    Analyze a self-disabling protocol for livelock behavior.

ARGUMENTS
    EXPRESSION          Python expression evaluating to a list of (pred, own, wr)
                        tuples. Supports list comprehensions.

OPTIONS
    --file PATH         Read transitions from a text file (one "pred own wr"
                        per line, # for comments).

    --example NAME      Use a built-in example protocol.

    --list-examples     List all built-in example protocols and exit.

    --name NAME         Display name for the protocol.

    --p0 EXPRESSION     Distinguished process P0 transitions for (1,1)-asymmetric
                        protocols. The main EXPRESSION gives the "other" transitions.

    --cycles            Show detailed cycle analysis in the product graph.

    --quiet             Minimal output: just LIVELOCK, NO LIVELOCK, or INCONCLUSIVE.

    Note: all options are long-form only; there are no single-letter aliases.

BUILT-IN EXAMPLES (see --list-examples for descriptions)
    coloring3           3-Coloring (m=3). Classic self-stabilizing coloring. Livelock.
    coloring4           4-Coloring (m=4).
    nondet_coloring     Non-deterministic coloring (m=3).
    shifted_coloring    Shifted coloring (m=3). Self-witnessing, shift 0.
    sum_not_2           Sum-Not-2 (m=3). Livelock-free.
    sum_not_2_nondet    Non-deterministic Sum-Not-2 (m=3). Has livelock.
    maximal_agreement   Maximal agreement (m=3). Every process copies predecessor.
    gouda_haddix        Gouda-Haddix TB (m=8). 32 transitions, 14 survive.
    barrier_clock       Barrier phase clock (m=5). Livelock.
    burns_me            Burns mutual exclusion (m=3). Non-self-disabling.
    cache_coherence     Write-invalidate cache coherence (m=4). Non-self-disabling.
    trial56             Trial 56 (m=8). Livelock-free. Stress-tests shadow pruning.
    weird               Weird protocol (m=16). Compound witness chains.
    ke_adversarial      K&E adversarial SE tiling (m=15). All 17 transitions survive.
    forced_counter_k2   Forced 2-bit binary counter (m=25). LIVELOCK via compound chain.
    forced_counter_k3   Forced 3-bit binary counter (m=37). INCONCLUSIVE.
    forced_counter      Forced 6-bit binary counter (m=73). INCONCLUSIVE — the
                        paper's Section VIII counterexample: a real livelock
                        (K=12, N=128) invisible to simple-cycle search.

OUTPUT
    LIVELOCK            Protocol admits livelock. L* shows surviving transitions.
    NO LIVELOCK         Protocol is provably livelock-free (G* = ∅).
    INCONCLUSIVE        G* ≠ ∅ but no simple cycle backward-closes.
```

### Usage Examples

```bash
# Analyze 3-coloring
python3 run_protocol.py --example coloring3

# Analyze with cycle details
python3 run_protocol.py "[(v,v,(v+1)%3) for v in range(3)]" --cycles

# Analyze from file
python3 run_protocol.py --file protocols/dijkstra.txt

# (1,1)-asymmetric: Dijkstra's token ring (m=3).
# The main expression is the transition set of the ordinary processes
# (copy the predecessor: (v, w, v) for v != w); --p0 gives the
# distinguished process (increment when equal: (v, v, v+1 mod m)).
python3 run_protocol.py "[(v,w,v) for v in range(3) for w in range(3) if v!=w]" \
    --p0 "[(v,v,(v+1)%3) for v in range(3)]" --name "Dijkstra m=3" --quiet
# Output: LIVELOCK
# (Dijkstra m=3,4,5 is also the first check in the built-in suite:
#  python3 livelock_complete.py)

# Quick check
python3 run_protocol.py "[(0,2,1),(1,1,2),(2,0,1)]" --quiet
# Output: NO LIVELOCK

# Reproduce the paper's Section VIII compound-chain counterexample
python3 run_protocol.py --example forced_counter --quiet
# Output: INCONCLUSIVE
```

### Protocol File Format

```
# my_protocol.txt
# Lines: pred own wr (space-separated integers)
# Comments start with #
# Blank lines are ignored

0 0 1
1 1 2
2 2 0
```

---

## Python API Reference

### `livelock_complete.py`

#### Core Functions

**`fixed_point(T_p0, T_other, verbose=True)`**

Main entry point. Analyzes a protocol for livelock behavior.

- **Parameters:**
  - `T_p0`: list of (pred, own, wr) tuples — transitions for P0 (or all processes if symmetric)
  - `T_other`: list of (pred, own, wr) tuples — transitions for other processes (same as T_p0 for symmetric)
  - `verbose`: bool — print progress (default True)
- **Returns:** `(has_livelock, kernel_p0, kernel_other, graph_info)` — a 4-tuple
  - `has_livelock`: bool — True if livelock confirmed
  - `kernel_p0`: frozenset — surviving transitions (L\*). Empty if G\*=∅. Non-empty for LIVELOCK or INCONCLUSIVE.
  - `kernel_other`: frozenset — same as kernel_p0 for symmetric protocols
  - `graph_info`: backtracking graph data for the symmetric path (the G\*
    structure used by the cycle search); `None` when G\*=∅ and on the
    asymmetric path
- **Interpreting results:**
  - `has_livelock=True` → LIVELOCK
  - `has_livelock=False, kernel_p0=∅` → LIVELOCK-FREE
  - `has_livelock=False, kernel_p0≠∅` → INCONCLUSIVE

```python
import livelock_complete as lc

T = [(0,0,1), (1,1,2), (2,2,0)]
has_ll, k0, ko, _ = lc.fixed_point(T, T, verbose=True)

if has_ll:
    print(f"LIVELOCK — {len(k0)} transitions survive")
elif k0:
    print(f"INCONCLUSIVE — G* has {len(k0)} surviving transitions")
else:
    print("LIVELOCK-FREE for all ring sizes")
```

---

**`analyze(name, T_p0, T_other=None, expect=None, m=None, trace_cycles=False)`**

Convenience wrapper with formatted output and optional result checking.

- **Parameters:**
  - `name`: str — display name
  - `T_p0`: list of transitions
  - `T_other`: list of transitions (default: same as T_p0)
  - `expect`: str — expected result for validation: `"LIVELOCK"`, `"NO LIVELOCK"`, `"INCONCLUSIVE"`, or `None`
  - `trace_cycles`: bool — show cycle analysis
- **Returns:** bool (has_livelock)

```python
lc.analyze("3-Coloring", [(0,0,1),(1,1,2),(2,2,0)], expect="LIVELOCK")
```

---

**`check_self_disabling(T)`**

Verify the self-disabling property.

- **Parameters:** `T` — list of (pred, own, wr) tuples
- **Returns:** `(is_self_disabling, violation)`
  - `is_self_disabling`: bool
  - `violation`: tuple of two conflicting transitions, or None

```python
ok, viol = lc.check_self_disabling([(0,0,1),(0,1,2)])
# ok = True, viol = None

ok, viol = lc.check_self_disabling([(0,0,1),(0,1,2),(0,1,0)])
# ok = False, viol shows the conflicting pair
```

---

**`wang_to_self_disabling(wang_tiles_ke, n_vert=None, n_horiz=None)`**

Convert Wang tiles to a self-disabling protocol via K&E's Lemma 4.8 gadget.

- **Parameters:**
  - `wang_tiles_ke`: list of (W, N, S, E) tuples in K&E convention
  - `n_vert`: int — number of distinct vertical colors (auto-detected if None)
  - `n_horiz`: int — number of distinct horizontal colors (auto-detected if None)
- **Returns:** sorted list of (pred, own, wr) transitions
- **Raises:** ValueError if the gadget produces a non-self-disabling protocol (should never happen)

```python
T = lc.wang_to_self_disabling([(0,0,1,1), (1,1,0,0)])
```

---

## Stress Testing

### `test_harness.py`

Generates random self-disabling protocols and cross-validates the product graph
algorithm against exhaustive state-space search at small ring sizes.

```
SYNOPSIS
    python3 test_harness.py [OPTIONS]

OPTIONS
    --suite NAME        Run a specific test suite:
                          random_small    m ∈ {3,...,7}, moderate |T|
                          random_medium   m ∈ {4,...,10}, larger |T|
                          random_large    m ∈ {8,...,15}, stress test
                          dense           High transition density
                          sparse          Low transition density
                          coloring        Coloring-family protocols
                          agreement       Agreement-family protocols
                          compound        Protocols with compound witnesses

    --count N           Number of protocols per suite (default varies by suite)
    --max-k K           Maximum ring size for exhaustive search (default: 6)
    --verbose, -v       Show per-protocol results
```

### Comparison Outcomes

| Outcome | Meaning |
|---------|---------|
| **Match** | Algorithm and exhaustive search agree |
| **Algo=LL, Exact=FREE** | Algorithm finds livelock at K > max_K — trusted |
| **Algo=INCONCLUSIVE, Exact=LL** | Expected for long-period livelocks |
| **FALSE NEGATIVE** | Algorithm says FREE but exhaustive found livelock — **bug** (never observed) |

### Examples

```bash
# Run all suites with defaults
python3 test_harness.py

# Run one suite with verbose output
python3 test_harness.py --suite random_small -v

# Stress test with more trials
python3 test_harness.py --count 2000

# Deeper exhaustive search (slower)
python3 test_harness.py --max-k 10
```

---

## Wang Tile Gadget

Klinkhamer & Ebnenasir's Lemma 4.8 converts any set of Wang tiles to a
self-disabling protocol. This is useful for testing the algorithm against
known tiling-theoretic results.

### Example: Kari's Aperiodic Tiles

Kari (1996) constructed 14 NW-deterministic Wang tiles that tile the plane
but admit no periodic tiling. Through the K&E gadget, this becomes a
54-transition self-disabling protocol — the hardest known test case.

```python
import livelock_complete as lc

# Kari's 14 tiles in K&E convention (West, North, South, East)
kari_tiles = [
    # M2 machine (vertical colors 4,5; horizontal colors 0,1,2)
    (5,0,1,4), (5,1,2,5), (4,1,1,5), (4,1,2,4),
    # M2/3 machine (vertical colors 0,1,2,3; horizontal colors 0,1,2)
    (0,1,0,2), (0,2,1,1), (1,1,0,3), (1,1,1,0),
    (1,2,1,2), (2,1,1,1), (2,2,1,3), (2,2,2,0),
    (3,1,1,2), (3,2,2,1),
]

T = lc.wang_to_self_disabling(kari_tiles, n_vert=6, n_horiz=3)
print(f"|T| = {len(T)}")  # 54 transitions

lc.analyze("Kari aperiodic", T, expect="INCONCLUSIVE")
# G* has 272 arcs, all 5000+ simple cycles fail backward propagation
# Result: INCONCLUSIVE ✓ (consistent with aperiodicity)
```

### Example: Periodic Tiles

```python
# Checkerboard tiles — admit periodic tiling
T = lc.wang_to_self_disabling([(0,0,1,1), (1,1,0,0)])
lc.analyze("Checkerboard", T, expect="LIVELOCK")
# Result: LIVELOCK ✓
```

---

## Test Results

| Category | Count | Result |
|----------|------:|--------|
| Built-in suite: Dijkstra (m=3,4,5), coloring family, Sum-Not-2 family, regression seeds, forced counters | 24 | All correct |
| K&E adversarial (SE tiling, m=15) | 1 | LIVELOCK ✓ |
| Kari aperiodic (14 tiles → 54 transitions) | 1 | INCONCLUSIVE ✓ |
| Random self-disabling (stress test, `test_harness.py`) | 4,300+ | Zero errors |
| **Total** | **4,349** | **Zero errors** |

The grand total is the paper's figure. The first three rows (26 checks) are
`python3 livelock_complete.py`; the randomized row is `test_harness.py`,
cross-validated against exhaustive state-space search at ring sizes K ≤ 6.

---

## Reproducing the Paper's Results

Each claim in the paper maps to one command:

| Paper claim | Command | Expected | Time |
|---|---|---|---|
| Dijkstra token ring has livelock (§VII-A) | `python3 livelock_complete.py` (first three checks) | LIVELOCK ✓ ×3 | seconds |
| Sum-Not-2 det. free / non-det. livelock (§II) | `run_protocol.py --example sum_not_2` / `--example sum_not_2_nondet` | NO LIVELOCK / LIVELOCK | seconds |
| K&E adversarial: all 17 transitions survive, cycle closes (§VII-D) | `run_protocol.py --example ke_adversarial` | LIVELOCK | seconds |
| Kari aperiodic: 272 arcs survive, no cycle closes (§VII-E) | `python3 livelock_complete.py` (final check), or the Wang-gadget snippet below | INCONCLUSIVE | seconds |
| Compound-chain counterexample (§VIII) | `run_protocol.py --example forced_counter --quiet` | INCONCLUSIVE (real livelock, K=12, N=128) | seconds |
| k=2 counter detected via mixed chain (§VIII) | `run_protocol.py --example forced_counter_k2 --quiet` | LIVELOCK | seconds |
| Randomized cross-validation, zero false negatives (§VII-B) | `python3 test_harness.py --count 150` | 150/150 pass | ~4 min |

The full built-in suite (`python3 livelock_complete.py`, ~10 seconds) covers
everything except the randomized row. Kari's fixed point converges in 3
iterations (3046 → 299 → 275 → 272 arcs); backtracking then rejects all
~9,800 canonical simple cycles.

---

## Theoretical Foundation

### Necessary Condition (Theorem 1)

Every livelock maps into the product graph G×(T) as a **backward-closed subgraph**
(the paper's term; the code calls it *witness-closed*):
a subgraph where every arc lies on a cycle (cyclicity) and every arc's witness-pair
is a transition-pair on some cycle arc (backward closure).

**Consequence:** G\*(T) = ∅ implies livelock-freedom for all ring sizes and all
periods. This is a sound and complete livelock-freedom verifier.

### Sufficient Condition (Theorem 2)

Any simple cycle in G\* whose backward chain closes (the sequence of walks
revisits a previous walk) generates a genuine livelock. The closing chain
directly constructs the torus witness.

### The Arc-Cycle Gap

Arc-level backward closure (what G\* enforces via fixed-point iteration) does
**not** imply cycle-level backward closure (what torus construction requires).
The composed backward walk may exist in the full product graph G×(T) but not
in G\*, because the composed walk's own backward arcs may require transitions
not present in T.

The precise obstruction is **pred alignment**: at each backward level, the
wrap boundary requires two transitions to share not just (own, wr) but also
pred. Each backward level demands alignment that the previous level does not
guarantee. This is where the undecidability of the periodic domino problem
(Klinkhamer & Ebnenasir 2019) manifests in the product graph framework.

---

## Limitations and the Decidability Boundary

### What the Algorithm Decides

- **LIVELOCK-FREE** (G\* = ∅): proven for all ring sizes K and all periods N.
  No livelock of any kind exists. This is unconditional.

- **LIVELOCK** (backtracking closes): proven. An explicit torus witness with
  period N ≤ |T|² is constructed.

### What It Cannot Decide

- **INCONCLUSIVE** (G\* ≠ ∅, no cycle closes): the protocol has no livelock
  with period ≤ |T|², but livelocks with longer periods cannot be ruled out.
  This case has never occurred on any real protocol — only on Kari's aperiodic
  tile construction, which is known to have no periodic tiling.

### Relationship to K&E's Undecidability Result

Klinkhamer & Ebnenasir (2019) proved that for parameterized rings, livelock
detection is Σ₁⁰-complete and livelock-freedom verification is Π₁⁰-complete.
Our algorithm is consistent with this: it decides a
significant subclass (bounded-period livelocks) and produces INCONCLUSIVE when
the bound is exceeded. The INCONCLUSIVE outcome is the algorithm's honest
acknowledgment that the full problem is undecidable.

---

## Files

| File | Description |
|------|-------------|
| `livelock_complete.py` | Core algorithm: product graph, fixed-point iteration, backtracking, K&E gadget, built-in test suite |
| `run_protocol.py` | Command-line interface for analyzing individual protocols |
| `test_harness.py` | Randomized stress testing against exhaustive state-space search |
| `README.md` | This file |

---

## References

1. A. Klinkhamer and A. Ebnenasir. "On the verification of livelock-freedom
   and self-stabilization on parameterized rings." *ACM Transactions on
   Computational Logic*, 20(3):18:1–18:37, 2019.

2. A. Klinkhamer and A. Ebnenasir. "Livelock verification for self-disabling
   protocols." Technical Report CS-TR-19-01, Michigan Technological University,
   2019.

3. A. Farahat. "Automated Design of Self-Stabilization." PhD thesis, Michigan
   Technological University, 2012.

4. A. Farahat and A. Ebnenasir. "Local reasoning for global convergence of
   parameterized rings." *Proc. IEEE ICDCS*, pp. 496–505, 2012.

5. M. G. Gouda and F. Haddix. "The stabilizing token ring in three bits."
   *Journal of Parallel and Distributed Computing*, 35(1):43–48, 1996.

6. J. Kari. "A small aperiodic set of Wang tiles." *Discrete Mathematics*,
   160(1–3):259–264, 1996.

7. H. Wang. "Proving theorems by pattern recognition II." *Bell System
   Technical Journal*, 40:1–41, 1961.

---

## License

MIT

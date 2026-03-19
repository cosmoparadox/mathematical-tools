# Livelock Detection in Parameterized Uni-Rings of Self-Disabling Processes

This repository contains the implementation and theoretical foundation for a
polynomial-time algorithm that decides livelock freedom for parameterized
symmetric unidirectional rings of self-disabling processes.

## Main Result

**Theorem.** Livelock existence for a self-disabling protocol T on a
unidirectional ring of K processes (K ≥ 2, K arbitrary) is decidable in
**O(|T|³) time, independent of K**.

A livelock is an infinite execution in which every process fires transitions
indefinitely without any process stabilizing. The decision is independent of
ring size: no enumeration over K values is needed.

## Background

A **self-disabling** protocol is one where every transition (v, w, w') satisfies
w' ≠ w — a process immediately disables itself after firing. This captures a
large class of self-stabilizing distributed protocols including Dijkstra's
token ring, k-coloring, and agreement protocols.

The **parameterized** question asks: does a livelock exist for *some* K ≥ 2?
This is the natural correctness question for protocol designers who want
guarantees that hold regardless of ring size.

## Algorithm

The algorithm is based on the **shadow fixed point** — the greatest fixed point
of a deflationary monotone operator on the finite transition set T:

```
Φ(S) = PL(Filter(S, Shad(PL(S))))
```

where:
- `PL(S)` = transitions lying on directed cycles in the pseudolivelock graph
- `Shad(P)` = shadow pairs `{(t.own, t.written) : t ∈ P}`
- `Filter(S, R)` = transitions in S whose (own, written) pair is in R

Starting from S = T, iterate Φ until stability. The stable set L* is the
**livelock kernel**. A livelock exists if and only if L* ≠ ∅.

**Termination** in at most |T| steps follows from the Knaster-Tarski theorem:
Φ is deflationary and monotone on the finite lattice (2^T, ⊆).

## Quick Start

```python
python3 livelock_final.py
```

Or use the `analyze` function directly:

```python
from livelock_final import analyze

m = 3

# Dijkstra's token ring
T_p0    = [(v, v, (v+1)%m) for v in range(m)]           # P_0: coloring
T_other = [(v, w, v) for v in range(m)                   # P_other: agreement
           for w in range(m) if v != w]

analyze("Dijkstra token ring (m=3)", T_p0, T_other, expect="LIVELOCK")

# k-coloring (symmetric)
T_col = [(v, v, (v+1)%m) for v in range(m)]
analyze("k-Coloring (m=3)", T_col, expect="LIVELOCK")

# Sum-Not-2 (livelock-free)
T_sn2 = [(v, w, (w+1)%m) for v in range(m) for w in range(m)
          if (v+w)%m == m-1]
analyze("Sum-Not-2 det (m=3)", T_sn2, expect="NO LIVELOCK")
```

## Output

For each protocol the algorithm reports:

- Whether a livelock exists
- The livelock kernel L* (transitions participating in the livelock)
- The Circulation Law: valid (|E|, K) pairs — the ring sizes that admit livelocks
- The Propagation Law check: H ∘ E = E ∘ H at every process interface

Example output for Dijkstra's token ring:

```
═══════════════════════════════════════════════════════════
  Dijkstra token ring (m=3)
═══════════════════════════════════════════════════════════
  P_0 kernel   : [(0,0,1), (1,1,2), (2,2,0)]
  P_other kernel: [(0,2,0), (1,0,1), (2,1,2)]
  Minimum |E| = 1,  minimum K = 2,  K step = 1
  Propagation Law: ✓ at all interfaces
  => LIVELOCK
```

## Theoretical Foundation

The algorithm is grounded in the algebraic characterization of livelocks from
Chapter 6 included herein
(`Exact_Algebraic_Characterization_of_Glob.pdf`).

**Propagation Law.** A livelock exists if and only if the livelock kernel L*
and propagation relation E* satisfy the equivariance condition
`H* ∘ E* = E* ∘ H*` at every process interface. This holds automatically
whenever L* ≠ ∅ — it is a consequence of the construction, not an
independent condition to verify.

**Circulation Law.** The valid ring sizes K are characterized by
`H*^|E| ∩ E^K ≠ ∅`. This too follows as a theorem from three algebraic
properties of L*: (P1) H* is an SCC relation, (P2) E* maps L* completely
into L*, (P3) L* is finite. Together these imply that both H*^p and (E^K)^q
have full diagonals, so their intersection is always non-empty.

## Supported Protocol Classes

| Protocol | Symmetric | Result |
|---|---|---|
| Dijkstra token ring | Asymmetric (l=1, q=1) | LIVELOCK for all K≥2 |
| k-Coloring (deterministic) | Symmetric | LIVELOCK for K≡1 (mod m) |
| k-Coloring (non-deterministic) | Symmetric | LIVELOCK for K≥3 |
| Agreement (maximal) | Symmetric | LIVELOCK for all K≥2 |
| Sum-Not-2 (deterministic) | Symmetric | NO LIVELOCK |
| Sum-Not-2 (non-deterministic) | Symmetric | LIVELOCK |
| Agreement-Symmetric | Symmetric | LIVELOCK |
| Alternating protocols (l=0, q=2) | Period-2 | Supported |

## Files

| File | Description |
|---|---|
| `livelock_final.py` | Main algorithm implementation |
| `Exact_Algebraic_Characterization_of_Glob.pdf` | Chapter 6: algebraic framework |
| `CITATION.cff` | Citation information |

## Requirements

Python 3.6+, no external dependencies.

## License

MIT

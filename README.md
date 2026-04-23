# Decidability of Livelock Detection in Self-Disabling Unidirectional Ring Protocols

A polynomial-time algorithm for deciding livelock freedom in parameterized
symmetric unidirectional rings of self-disabling processes, for all ring
sizes simultaneously.

**Repository:** https://github.com/cosmoparadox/mathematical-tools

---

## Table of Contents

- [Overview](#overview)
- [Quick Start](#quick-start)
- [Specifying a Protocol](#specifying-a-protocol)
- [Running the Analyzer](#running-the-analyzer)
- [Built-in Examples](#built-in-examples)
- [Test Harness](#test-harness)
- [File Reference](#file-reference)
- [Understanding the Output](#understanding-the-output)
- [References](#references)

---

## Overview

A **unidirectional ring protocol** consists of K identical processes arranged in a directed cycle. Each process P_i has a state variable v_i in Z_m and can read its own state and its predecessor's state v_{i-1}. A **transition** (p, o, w) means: "if predecessor has value p and I have value o, write w."

A protocol is **self-disabling** if for every (p, o, w) in T, there is no (p, w, u) in T for any u — after firing, the process cannot fire again until its predecessor changes state.

A **livelock** is an infinite execution where processes keep firing without ever reaching a legitimate state. The **parameterized** question: does a livelock exist for *any* ring size K >= 2?

This tool decides the parameterized livelock question in polynomial time by constructing a **product transition graph** and computing its greatest witness-closed subset via monotone fixed-point iteration.

---

## Quick Start

```bash
# Analyze the 3-coloring protocol
python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]"

# Same protocol using list comprehension
python run_protocol.py "[(v,v,(v+1)%3) for v in range(3)]"

# Just get the answer
python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" --quiet

# Full cycle analysis with circulation law
python run_protocol.py --example coloring3 --cycles

# List all built-in examples
python run_protocol.py --list-examples

# Run validation suite
python test_harness.py --known-only
```

---

## Specifying a Protocol

A protocol is a list of **(pred, own, wr)** triples:

| Field | Meaning |
|-------|---------|
| pred | Value read from predecessor process |
| own  | Process's current value (before firing) |
| wr   | Value written by the process (after firing) |

### Inline (Python expression)

Any Python expression evaluating to a list of 3-tuples:

```bash
# Explicit list
python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]"

# List comprehension — 5-coloring
python run_protocol.py "[(v,v,(v+1)%5) for v in range(5)]"

# Non-deterministic — each process can change to any other value
python run_protocol.py "[(v,v,w) for v in range(3) for w in range(3) if v!=w]"

# Agreement — copy predecessor's value
python run_protocol.py "[(v,w,v) for v in range(4) for w in range(4) if v!=w]"
```

### From file

One transition per line, space-separated integers. Lines starting with # are comments.

```
# my_protocol.txt — 3-coloring
0 0 1
1 1 2
2 2 0
```

```bash
python run_protocol.py --file my_protocol.txt
```

### Self-disabling constraint

The tool checks this automatically and reports violations. A protocol violates self-disabling if it contains both (p, o, w) and (p, w, u) for some p, o, w, u.

### (1,1)-Asymmetric protocols

For protocols where one distinguished process P_0 uses different transitions:

```bash
python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" \
    --p0 "[(0,0,2),(1,1,0),(2,2,1)]"
```

---

## Running the Analyzer

```
run_protocol.py [OPTIONS] [PROTOCOL]
```

### Options

| Flag | Description |
|------|-------------|
| PROTOCOL | Python expression for the transition list |
| --name NAME | Display name for the protocol |
| --example NAME | Use a built-in example |
| --file PATH | Read protocol from file |
| --list-examples | List all built-in examples |
| --cycles | Show full cycle analysis (forward map, circulation law) |
| --p0 EXPR | Distinguished process transitions (asymmetric) |
| --quiet | Minimal output: just LIVELOCK or NO LIVELOCK |

---

## Built-in Examples

| Name | m | |T| | Result | Description |
|------|---|-----|--------|-------------|
| coloring3 | 3 | 3 | Livelock | Classic self-stabilizing coloring |
| coloring4 | 4 | 4 | Livelock | 4-value coloring |
| sum_not_2 | 3 | 3 | Free | Classic livelock-free protocol |
| sum_not_2_nondet | 3 | 6 | Livelock | Non-deterministic variant |
| shifted_coloring | 3 | 3 | Livelock | pred != own, self-witnessing |
| gouda_haddix | 8 | 32 | Livelock | 14 survive, multiple classes |
| trial56 | 8 | 13 | Free | Exposes shadow-level false positives |
| weird | 16 | 10 | Livelock | Compound witness chains |
| ke_adversarial | 15 | 17 | Livelock | From K&E SE tiling construction |
| maximal_agreement | 3 | 6 | Livelock | Copy predecessor's value |
| nondet_coloring | 3 | 6 | Livelock | Change to any other value |

```bash
python run_protocol.py --example gouda_haddix --cycles
```

---

## Test Harness

Generates random self-disabling protocols and cross-validates against exhaustive state-space search.

```
test_harness.py [OPTIONS]
```

### Options

| Flag | Description |
|------|-------------|
| --suite NAME | Run one suite (see below) |
| --count N | Protocols per suite (default: 500) |
| --max-k K | Max ring size for exhaustive search (default: 6) |
| --verbose | Show per-protocol results |
| --known-only | Only run known protocol tests |

### Test suites

| Suite | Description |
|-------|-------------|
| random_small | m in {3,...,7}, random density |
| random_medium | m in {8,...,10} |
| random_large | m in {11,...,15} |
| dense | Near-maximal transition sets |
| sparse | m to 2m transitions |
| coloring | Coloring variants with noise |
| agreement | Agreement variants |
| compound | Large m, few transitions |

### Running tests

```bash
# Quick validation
python test_harness.py --known-only

# Medium run (~2 minutes)
python test_harness.py --count 100 --max-k 4

# Full validation (~30 minutes)
python test_harness.py --count 500 --max-k 5

# Single suite, verbose
python test_harness.py --suite random_small --count 200 --verbose
```

---

## File Reference

| File | Description |
|------|-------------|
| livelock_complete.py | Core algorithm. Product graph, fixed-point, cycle analysis, circulation law. |
| run_protocol.py | User-facing CLI. Parses protocols, invokes the algorithm. |
| test_harness.py | Randomized stress testing with exhaustive cross-validation. |
| CITATION.cff | Citation metadata. |

---

## Understanding the Output

### Basic output

```
  m=3, |T_p0|=3, |T_other|=3, sym=True
  [Symmetric] 2D product-graph fixed point
    [T] 2D fixed point: 3 transitions
  => LIVELOCK: L* = [(0, 0, 1), (1, 1, 2), (2, 2, 0)]
```

- **m**: domain size
- **L***: greatest witness-closed subset (surviving transitions)
- **LIVELOCK / NO LIVELOCK**: the decision

### Cycle analysis (with --cycles)

```
FORWARD ENABLING MAP:
  c[0] N=3 [simple]: [(0,0,1),(1,1,2),(2,2,0)]
       -> self [simple] shift=1

CLOSING CHAINS & CIRCULATION LAW:
  c[0](simple,s=1) -> c[0]
    period p=1, S(p)=1, N=3
    e = S(K) mod 3, 1 <= e <= K:
    K=1(e=1), K=2(e=2), K=3(e=3), ...
```

- **c[i]**: simple cycle index in the H-graph
- **N**: cycle length (local period)
- **shift**: rotational offset between a cycle and its forward target
- **period p**: closing chain length
- **e**: number of enabled processes (tokens) at ring size K

---

## Algorithm Summary

1. **Build** the product transition graph: nodes are (t, w) pairs with wr(w) = pred(t); arcs encode four equivariance conditions
2. **Prune** via monotone fixed-point: SCC + backward closure until quiescence
3. **Decide**: livelock exists iff L* is non-empty

---

## References

1. A. Farahat, *Automated Design of Self-Stabilization*, PhD thesis, Michigan Technological University, 2012.
2. A. Farahat and A. Ebnenasir, "Local Reasoning for Global Convergence of Parameterized Rings," IEEE ICDCS, 2012.
3. A. Klinkhamer and A. Ebnenasir, "On the Verification of Livelock-Freedom and Self-Stabilization on Parameterized Rings," ACM Trans. Comput. Logic, 20(3), 2019.

## License

MIT

#!/usr/bin/env python3
"""
run_protocol.py — Livelock detection for self-disabling unidirectional ring protocols.

Analyzes a protocol specified as a list of (pred, own, wr) transitions and
determines whether it admits a livelock for any ring size.

USAGE
─────
  # Inline protocol specification
  python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]"

  # With name
  python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" --name "3-coloring"

  # List comprehension
  python run_protocol.py "[(v,v,(v+1)%3) for v in range(3)]"

  # Non-deterministic protocol
  python run_protocol.py "[(p,o,(o+1)%m) for m in [3] for p in range(m) for o in range(m) if o != p] + [(p,o,(o-1)%m) for m in [3] for p in range(m) for o in range(m) if o != p]"

  # Show full cycle analysis
  python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" --cycles

  # From a named example
  python run_protocol.py --example coloring3

  # List available examples
  python run_protocol.py --list-examples

  # From file
  python run_protocol.py --file my_protocol.txt

  # (1,1)-Asymmetric: distinguished process P0 differs from others
  python run_protocol.py "[(0,0,1),(1,1,2),(2,2,0)]" --p0 "[(0,0,2),(1,1,0),(2,2,1)]"

PROTOCOL FORMAT
───────────────
  A protocol is a list of (pred, own, wr) triples where:
    pred  — the value read from the predecessor process
    own   — the process's current value (before firing)
    wr    — the value written by the process (after firing)

  Self-disabling constraint: for every (p, o, w) in T, no (p, w, u) in T
  for any u. The process cannot fire again until the predecessor changes.

  Transitions can be specified as:
    - Explicit list:  [(0,0,1),(1,1,2),(2,2,0)]
    - Comprehension:  [(v,v,(v+1)%3) for v in range(3)]
    - Any valid Python expression evaluating to a list of 3-tuples

FILE FORMAT
───────────
  One transition per line as "pred own wr" (space-separated integers):
    0 0 1
    1 1 2
    2 2 0

  Lines starting with # are comments. Blank lines are ignored.

OUTPUT
──────
  The algorithm reports:
    - Whether the protocol admits a livelock (LIVELOCK / NO LIVELOCK)
    - The surviving transition set L* (the greatest witness-closed subset)
    - Number of iterations to reach the fixed point

  With --cycles:
    - All simple cycles in the product graph
    - Forward enabling map (which cycle witnesses which)
    - Closing chains and the circulation law
    - Ring sizes K at which livelocks occur

EXAMPLES
────────
  python run_protocol.py --list-examples     # See all built-in examples
  python run_protocol.py --example coloring3 --cycles
  python run_protocol.py --example gouda_haddix --cycles
  python run_protocol.py --example trial56   # Known livelock-free protocol
"""

import sys
import argparse
import ast

sys.path.insert(0, '.')
import livelock_complete as lc


# ═══════════════════════════════════════════════════════════════
#  BUILT-IN EXAMPLES
# ═══════════════════════════════════════════════════════════════

EXAMPLES = {
    "coloring3": {
        "name": "3-Coloring (m=3)",
        "T": [(0,0,1),(1,1,2),(2,2,0)],
        "description": "Classic self-stabilizing coloring. Livelock with shift 1.",
    },
    "coloring4": {
        "name": "4-Coloring (m=4)",
        "T": [(0,0,1),(1,1,2),(2,2,3),(3,3,0)],
        "description": "Coloring on 4 values.",
    },
    "sum_not_2": {
        "name": "Sum-Not-2 (m=3)",
        "T": [(0,2,1),(1,1,2),(2,0,1)],
        "description": "Self-stabilizing Sum-Not-2. Livelock-free.",
    },
    "sum_not_2_nondet": {
        "name": "Non-det Sum-Not-2 (m=3)",
        "T": [(0,2,0),(0,2,1),(1,1,0),(1,1,2),(2,0,1),(2,0,2)],
        "description": "Non-deterministic variant. Has livelock.",
    },
    "shifted_coloring": {
        "name": "Shifted Coloring (m=3)",
        "T": [(1,0,1),(2,1,2),(0,2,0)],
        "description": "pred != own coloring. Self-witnessing, shift 0.",
    },
    "gouda_haddix": {
        "name": "Gouda-Haddix TB (m=8)",
        "T": [(0,0,3),(0,1,6),(0,4,6),(0,5,6),(1,0,3),(1,1,6),(1,4,6),(1,5,6),
              (2,2,1),(2,3,4),(2,6,4),(2,7,4),(3,2,1),(3,3,4),(3,6,4),(3,7,4),
              (4,0,2),(4,1,2),(4,4,2),(4,5,2),(5,0,2),(5,1,2),(5,4,2),(5,5,2),
              (6,2,0),(6,3,0),(6,6,0),(6,7,0),(7,2,0),(7,3,0),(7,6,0),(7,7,0)],
        "description": "32 transitions, 14 survive. Multiple livelock classes.",
    },
    "trial56": {
        "name": "Trial 56 — Phi Bug Exposer (m=8)",
        "T": [(0,4,2),(0,7,6),(2,2,7),(2,5,7),(3,6,0),(4,0,2),(4,0,5),
              (5,2,0),(5,6,0),(6,3,4),(6,6,2),(7,0,6),(7,7,3)],
        "description": "Livelock-free. Exposes shadow-level false positives.",
    },
    "weird": {
        "name": "Weird Protocol — Compound Witnesses (m=16)",
        "T": [(5,2,3),(8,3,2),(2,7,9),(3,9,12),(2,12,15),(3,15,7),
              (7,5,8),(9,8,5),(12,5,8),(15,8,5)],
        "description": "Compound witness chains. Simple H-cycle is dead-end.",
    },
    "ke_adversarial": {
        "name": "K&E Adversarial (m=15)",
        "T": [(0,5,9),(0,11,3),(3,14,6),(6,2,0),(9,8,6),(1,0,7),(1,3,4),
              (4,6,1),(7,9,10),(10,6,13),(13,0,1),(2,4,5),(2,10,11),
              (5,1,8),(8,7,2),(11,13,14),(14,1,2)],
        "description": "From K&E's SE tiling construction. All 17 transitions survive.",
    },
    "maximal_agreement": {
        "name": "Maximal Agreement (m=3)",
        "T": [(v, w, v) for v in range(3) for w in range(3) if v != w],
        "description": "Agreement: every process copies predecessor.",
    },
    "nondet_coloring": {
        "name": "Non-det Coloring (m=3)",
        "T": [(v, v, w) for v in range(3) for w in range(3) if v != w],
        "description": "Non-deterministic coloring: change to any other value.",
    },
}


def list_examples():
    """Print available examples."""
    print("\nAvailable examples:")
    print("─" * 60)
    for key, ex in sorted(EXAMPLES.items()):
        status = "livelock" if key not in ("sum_not_2", "trial56") else "free"
        print(f"  {key:25s}  {ex['name']}")
        print(f"  {'':25s}  {ex['description']}")
        print(f"  {'':25s}  |T|={len(ex['T'])}, {status}")
        print()


def parse_protocol_string(s):
    """Parse a protocol from a Python expression string."""
    try:
        result = eval(s)
        if not isinstance(result, list):
            result = list(result)
        # Validate format
        for item in result:
            if not (isinstance(item, (tuple, list)) and len(item) == 3):
                raise ValueError(f"Expected 3-tuples, got: {item}")
        return [(int(p), int(o), int(w)) for p, o, w in result]
    except Exception as e:
        print(f"Error parsing protocol: {e}", file=sys.stderr)
        print(f"Input was: {s}", file=sys.stderr)
        sys.exit(1)


def parse_protocol_file(filepath):
    """Parse a protocol from a file (one transition per line)."""
    T = []
    with open(filepath) as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split()
            if len(parts) != 3:
                print(f"Error line {lineno}: expected 3 values, got {len(parts)}: {line}",
                      file=sys.stderr)
                sys.exit(1)
            try:
                T.append(tuple(int(x) for x in parts))
            except ValueError:
                print(f"Error line {lineno}: non-integer value: {line}",
                      file=sys.stderr)
                sys.exit(1)
    return T


# ═══════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        description="Livelock detection for self-disabling unidirectional ring protocols.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s "[(0,0,1),(1,1,2),(2,2,0)]"
  %(prog)s "[(v,v,(v+1)%%3) for v in range(3)]" --cycles
  %(prog)s --example coloring3 --cycles
  %(prog)s --list-examples
  %(prog)s --file my_protocol.txt
""")

    # Protocol source (mutually exclusive)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("protocol", nargs="?", type=str, default=None,
        help="Protocol as Python expression: list of (pred, own, wr) triples")
    source.add_argument("--example", type=str, metavar="NAME",
        help="Use a built-in example protocol")
    source.add_argument("--file", type=str, metavar="PATH",
        help="Read protocol from file (one 'pred own wr' per line)")
    source.add_argument("--list-examples", action="store_true",
        help="List available built-in examples")

    # Options
    parser.add_argument("--name", type=str, default=None,
        help="Name for the protocol (for display)")
    parser.add_argument("--cycles", action="store_true",
        help="Show full cycle analysis with forward map and circulation law")
    parser.add_argument("--p0", type=str, default=None,
        help="Distinguished process transitions for (1,1)-asymmetric protocols")
    parser.add_argument("--quiet", action="store_true",
        help="Minimal output: just LIVELOCK or NO LIVELOCK")

    args = parser.parse_args()

    # Handle --list-examples
    if args.list_examples:
        list_examples()
        return

    # Determine protocol source
    T = None
    T_p0 = None
    name = args.name

    if args.example:
        if args.example not in EXAMPLES:
            print(f"Unknown example: {args.example}", file=sys.stderr)
            print(f"Available: {', '.join(sorted(EXAMPLES.keys()))}", file=sys.stderr)
            sys.exit(1)
        ex = EXAMPLES[args.example]
        T = ex["T"]
        if name is None:
            name = ex["name"]
        if not args.quiet:
            print(f"  {ex['description']}")

    elif args.file:
        T = parse_protocol_file(args.file)
        if name is None:
            name = args.file

    elif args.protocol:
        T = parse_protocol_string(args.protocol)
        if name is None:
            name = "User protocol"

    else:
        parser.print_help()
        return

    # Handle asymmetric
    if args.p0:
        T_p0 = parse_protocol_string(args.p0)

    if not T:
        print("Empty protocol — trivially livelock-free.")
        return

    # Remove duplicates and sort
    T = sorted(set(T))
    if T_p0 is not None:
        T_p0 = sorted(set(T_p0))

    if args.quiet:
        # Minimal output
        T_other = T
        T_zero = T_p0 if T_p0 else T
        has_ll, k0, _ = lc.fixed_point(T_zero, T_other, verbose=False)
        if has_ll:
            print("LIVELOCK")
        elif k0:
            print("INCONCLUSIVE")
        else:
            print("NO LIVELOCK")
        return

    # Full analysis
    if T_p0:
        lc.analyze(name, T_p0, T_other=T, trace_cycles=args.cycles)
    else:
        lc.analyze(name, T, trace_cycles=args.cycles)


if __name__ == "__main__":
    main()

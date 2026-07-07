# Errata: Submitted Artifact vs. Current Repository

`artifact.zip` in this repository is the **submission-time snapshot** of the
tool, frozen at paper submission (its SHA1 hash is on record with the
submission). It is preserved unmodified for provenance.

The repository HEAD contains a small number of post-submission corrections.
**No algorithm, protocol definition, theorem-relevant computation, or
experimental result changed.** Both versions produce identical verdicts on
all 26 built-in checks (`python3 livelock_complete.py`) and on the
cross-validation harness (`python3 test_harness.py`).

## Changes since the submitted snapshot

1. **Documentation (README.md).**
   - CLI options are long-form only (`--quiet`, `--example`, `--file`,
     `--name`, `--cycles`); the submitted README also listed short aliases
     (`-q`, `-e`, `-f`, ...) that were never implemented.
   - The Python API entry point `fixed_point(T_p0, T_other)` returns a
     **4-tuple** `(has_livelock, kernel_p0, kernel_other, graph_info)`;
     the submitted README documented a 3-tuple.
   - The built-in example list was refreshed to match
     `run_protocol.py --list-examples`, and a claim-to-command table
     ("Reproducing the Paper's Results") was added.
   - The example invocation for Dijkstra's token ring was corrected to use
     the transition sets of the paper (Section VII.A): ordinary processes
     copy the predecessor, `[(v,w,v) for v!=w]`; the distinguished process
     increments when equal, `[(v,v,(v+1)%m)]`.

2. **One bug fix (run_protocol.py, 2 lines).** The `--p0` command-line path
   crashed with a `ValueError` when either transition set was
   **non-self-disabling** (a stale 3-value unpack of
   `augment_transitive_closure`, which returns 2 values). This affected only
   the CLI wrapper for that case; the analysis code in
   `livelock_complete.py` -- including the asymmetric fixed point exercised
   by the built-in suite (Dijkstra m = 3, 4, 5) -- was never affected.
   Self-disabling asymmetric inputs (e.g., Dijkstra) ran correctly in both
   versions.

## Equivalence check

Both versions were run side by side:

| Check | Submitted `artifact.zip` | Repository HEAD |
|---|---|---|
| Built-in suite (26 checks, incl. Dijkstra m=3,4,5 and Kari) | 26/26 pass, ~6 s | 26/26 pass, ~6 s |
| Kari aperiodic tiles (54 transitions) | 272 arcs survive, 9,830 cycles rejected, INCONCLUSIVE | identical |
| Cross-validation harness (random self-disabling, K <= 6 oracle) | all pass, 0 false negatives | identical |
| `--p0` with non-self-disabling input | crashes (bug above) | returns verdict |

To reproduce any claim of the paper, see "Reproducing the Paper's Results"
in `README.md`; every command works identically on either version except
the single case noted in item 2.

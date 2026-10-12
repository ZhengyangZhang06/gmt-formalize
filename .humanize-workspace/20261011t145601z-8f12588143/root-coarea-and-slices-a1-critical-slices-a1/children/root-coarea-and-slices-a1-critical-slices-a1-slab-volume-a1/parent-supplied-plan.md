# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.critical_slices-a1.slab_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-critical-slices-a1-slab-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.critical_slices-a1`
- Child key: `slab_volume`
- Declaration: `Submission.critSlices_slab_volume_le`
- Exact Lean type: `∀ (m : ℕ) (ν c : Rn m) (r R : ℝ), ‖ν‖ = 1 → volume {w : Rn m | |inner ℝ (w - c) ν| ≤ r ∧ ‖w - c‖ ≤ R} ≤ ENNReal.ofReal (2 * r * (2 * R) ^ (m - 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

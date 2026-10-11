# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.slab_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-slab-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child key: `slab_volume`
- Declaration: `Submission.euclidean_slab_inter_closedBall_volume_le`
- Exact Lean type: `∀ (m : ℕ) (e c : Rn m) (ε R : ℝ), ‖e‖ = 1 → 0 ≤ ε → 0 ≤ R → volume {v : Rn m | ‖v - c‖ ≤ R ∧ |inner ℝ e (v - c)| ≤ ε} ≤ ENNReal.ofReal (2 * ε * (2 * R) ^ (m - 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

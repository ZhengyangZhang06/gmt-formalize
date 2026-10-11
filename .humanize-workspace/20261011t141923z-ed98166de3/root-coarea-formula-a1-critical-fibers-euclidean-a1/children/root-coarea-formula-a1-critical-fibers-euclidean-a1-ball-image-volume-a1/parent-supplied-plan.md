# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_image_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-ball-image-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child key: `ball_image_volume`
- Declaration: `Submission.volume_image_closedBall_le_of_fderiv_not_surjective`
- Exact Lean type: `∀ (n m : ℕ) (G : Rn n → Rn m) (x : Rn n) (r η L : ℝ), 0 ≤ r → (∀ z ∈ closedBall x r, DifferentiableAt ℝ G z) → (∀ z ∈ closedBall x r, ‖fderiv ℝ G z - fderiv ℝ G x‖ ≤ η) → ‖fderiv ℝ G x‖ ≤ L → ¬ Function.Surjective (fderiv ℝ G x) → volume (G '' closedBall x r) ≤ ENNReal.ofReal (2 * (η * r) * (2 * ((L + η) * r)) ^ (m - 1))`

## Sibling prerequisites

- `root.coarea_formula-a1.critical_fibers_euclidean-a1.slab_volume-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

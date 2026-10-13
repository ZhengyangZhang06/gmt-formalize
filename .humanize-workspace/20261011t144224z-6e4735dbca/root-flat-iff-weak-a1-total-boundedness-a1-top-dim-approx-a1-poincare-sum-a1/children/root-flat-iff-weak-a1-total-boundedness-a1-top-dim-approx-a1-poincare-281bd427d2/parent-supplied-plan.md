# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.translation_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-281bd427d2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1`
- Child key: `translation_ball`
- Declaration: `Submission.fiw_tb_tda_ps_translation_ball`
- Exact Lean type: `∀ (n : ℕ) (u : Eucl n → ℝ) (Λ : ℝ≥0∞) (r : ℝ), Measurable u → (∀ h : Eucl n, ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * Λ) → ∫⁻ x, ∫⁻ y in closedBall x r, ENNReal.ofReal |u x - u y| ≤ ENNReal.ofReal r * Λ * volume (closedBall (0 : Eucl n) r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

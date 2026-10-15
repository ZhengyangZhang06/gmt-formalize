# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.pairing_error-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-440ba609fb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `pairing_error`
- Declaration: `Submission.dmcbr_ci_bl_pairing_error_le`
- Exact Lean type: `∀ (P n : ℕ) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n) (A R : ℝ), AEStronglyMeasurable τ ν' → Continuous w → (∀ x, ‖w x‖ ≤ A) → (∀ x, x ∉ closedBall (0 : Euclid P) R → w x = 0) → Integrable (fun x => ζ₀ (w x)) ν' → ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν' ≠ ∞ → |∫ x, τ x (w x) ∂ν' - ∫ x, ζ₀ (w x) ∂ν'| ≤ (ENNReal.ofReal A * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν').toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.pairing_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-9ee77a4bab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `pairing_tendsto`
- Declaration: `Submission.dmcbr_ci_bl_pairing_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (τs : ℕ → Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (w : Euclid P → Covector (Euclid P) n), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → νs k K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(νs k)) atTop (𝓝 (∫ x, f x ∂ν))) → (∀ k, AEStronglyMeasurable (τs k) (νs k)) → (∀ R : ℝ, 0 < R → Tendsto (fun k => ∫⁻ x in closedBall (0 : Euclid P) R, ‖τs k x - ζ₀‖ₑ ∂(νs k)) atTop (𝓝 0)) → Continuous w → HasCompactSupport w → Tendsto (fun k => ∫ x, τs k x (w x) ∂(νs k)) atTop (𝓝 (∫ x, ζ₀ (w x) ∂ν))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.pairing_error-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

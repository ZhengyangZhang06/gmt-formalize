# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.weighted_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-e0a4b06359/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child key: `weighted_field`
- Declaration: `Submission.dmcbr_ci_gp_weighted_field_l1`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μ < ∞ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → StronglyMeasurable (fun x => θ x • ζ x) ∧ ∫⁻ x in M, ‖θ x • ζ x‖ₑ ∂μ < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

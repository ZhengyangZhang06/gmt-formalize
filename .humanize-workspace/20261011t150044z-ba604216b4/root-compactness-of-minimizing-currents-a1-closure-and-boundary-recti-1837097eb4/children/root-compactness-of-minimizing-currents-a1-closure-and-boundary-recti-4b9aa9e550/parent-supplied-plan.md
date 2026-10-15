# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.restriction_limit-a1.cutoff_error-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4b9aa9e550/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.restriction_limit-a1`
- Child key: `cutoff_error`
- Declaration: `Submission.cbr_rlim_cutoff_error_le`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (ω η : TestFormOn U k) (χ f : Euclid P → ℝ) (t ε M : ℝ), Continuous f → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M) → (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x, f x ≤ t - ε → χ x = 1) → (∀ x, t ≤ f x → χ x = 0) → |(∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) - ∫ x, ξ x ((η : DifferentialForm (Euclid P) k) x) ∂μ| ≤ M * (μ (tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t})).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

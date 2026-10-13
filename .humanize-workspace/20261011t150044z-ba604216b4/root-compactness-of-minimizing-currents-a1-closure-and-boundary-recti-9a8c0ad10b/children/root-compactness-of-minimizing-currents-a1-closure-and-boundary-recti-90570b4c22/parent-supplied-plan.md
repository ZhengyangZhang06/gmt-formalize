# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.orient_ae_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-90570b4c22/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1`
- Child key: `orient_ae_eq`
- Declaration: `Submission.cbr_orient_ae_eq_of_setIntegral_eq`
- Exact Lean type: `∀ (P k : ℕ) (B : Set (Euclid P)) (μ₁ μ₂ : Measure (Euclid P)) (ξ₁ ξ₂ : Euclid P → MultiVector P k), IsOpen B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ B → μ₁ K < ∞) → μ₁.restrict B = μ₂.restrict B → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ (E : Set (Euclid P)) (ω : TestFormOn B k), MeasurableSet E → ∫ x in E, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in E, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂) → ∀ᵐ x ∂μ₁, x ∈ B → ξ₁ x = ξ₂ x`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.support_null-a1.local_carrier_null-a1.covector_finite_dimensional-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

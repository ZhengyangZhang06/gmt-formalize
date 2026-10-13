# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1.restrict_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-cc3788be20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1`
- Child key: `restrict_im`
- Declaration: `Submission.cbr_ccisp_restrict_isIntegerMultiplicity`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) → (∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (P q : ℕ) (U : Set (Euclid P)) (X A : GeometricCurrentOn U q) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P q) (E : Set (Euclid P)), IsOpen U → IsIntegerMultiplicity X → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) q, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U q, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) q) x) ∂μ) → MeasurableSet E → (∀ ω : TestFormOn U q, A ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) q) x) ∂μ) → IsIntegerMultiplicity A`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.imrep_data-a1`
- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.imrep_restrict-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

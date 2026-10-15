# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-90bfaf373f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1`
- Child key: `de_giorgi`
- Declaration: `Submission.codim1_rdo_de_giorgi_gauss_green`
- Exact Lean type: `∀ (m : ℕ) (D F : Set (Euclid (m + 1))), 1 ≤ m → IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (B : Set (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), MeasurableSet B ∧ B ⊆ D ∧ CountablyRectifiable m B ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μHE[m] (B ∩ K) ≠ ∞) ∧ Measurable ν ∧ (∀ y ∈ B, ‖ν y‖ = 1) ∧ (∀ᵐ y ∂(μHE[m].restrict B), HasApproximateTangentSpaceAt m B y (Submodule.span ℝ {ν y})ᗮ) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y in B, inner ℝ (φ y) (ν y) ∂μHE[m]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

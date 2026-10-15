# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.gauss_green_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-6409b1b96d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1`
- Child key: `gauss_green_measure`
- Declaration: `Submission.codim1_rdo_dg_gauss_green_measure`
- Exact Lean type: `∀ (m : ℕ) (D F : Set (Euclid (m + 1))), IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y, inner ℝ (φ y) (ν y) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

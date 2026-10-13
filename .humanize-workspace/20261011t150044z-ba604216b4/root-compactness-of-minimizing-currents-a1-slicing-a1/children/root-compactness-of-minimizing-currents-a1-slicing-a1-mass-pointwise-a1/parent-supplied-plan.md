# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.mass_pointwise-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-pointwise-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1`
- Child key: `mass_pointwise`
- Declaration: `Submission.cmcs_slice_mass_pointwise`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.level_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

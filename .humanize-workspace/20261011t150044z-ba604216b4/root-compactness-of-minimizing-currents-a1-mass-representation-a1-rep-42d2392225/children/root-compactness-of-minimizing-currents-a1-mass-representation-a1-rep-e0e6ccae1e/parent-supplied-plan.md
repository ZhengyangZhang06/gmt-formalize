# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1.polar_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-rep-e0e6ccae1e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Child key: `polar_pushforward`
- Declaration: `Submission.cmrc_polar_pushforward`
- Exact Lean type: `∀ (P n d : ℕ) (U : Set (Euclid P)) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (μ₀ : Measure U) (ν : U → EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → Measurable ν → (∀ K : Set U, IsCompact K → IntegrableOn ν K μ₀) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ AEStronglyMeasurable β μ ∧ (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) ∧ (∀ x, covectorEuclideanNorm (β x) ≤ 1) ∧ (∀ᵐ x ∂μ, ξ x (β x) = 1) ∧ ∀ ω : DifferentialForm (Euclid P) n, ∫ x, inner ℝ (c (ω x)) (ν x) ∂μ₀ = ∫ x, ξ x (ω x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

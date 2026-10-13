# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child key: `product_support_density`
- Declaration: `Submission.dimred_cs_product_support_density`
- Exact Lean type: `∀ (P n : ℕ) (L : Submodule ℝ (Euclid P)) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R : IMRep (univ : Set (Euclid P)) n) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)), Module.finrank ℝ L < n → R.Represents S → R₀.Represents S₀ → R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) → (∀ y ∈ Lᗮ, ∃ θ : ℝ, HasMassDensity S₀ y θ) → (∀ t ∈ L, ∀ y ∈ Lᗮ, (t + y ∈ S.support ↔ y ∈ S₀.support)) ∧ ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ θ : ℝ, (HasMassDensity S (t + y) θ ↔ HasMassDensity S₀ y θ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

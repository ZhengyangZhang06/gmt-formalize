# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1.second_variation_nonneg-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-907e409093/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.stability-a1`
- Child key: `second_variation_nonneg`
- Declaration: `Submission.codim1_hcp_stab_second_variation_nonneg`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (E : Set (Euclid P)) (J : ℝ → Euclid P → ℝ) (q : Euclid P → ℝ) (B C t₀ : ℝ), MeasurableSet E → μ E ≠ ∞ → 0 < t₀ → AEStronglyMeasurable q (μ.restrict E) → (∀ x ∈ E, |q x| ≤ B) → (∀ t : ℝ, |t| < t₀ → μ E ≤ ∫⁻ x in E, ENNReal.ofReal (J t x) ∂μ) → (∀ t : ℝ, |t| < t₀ → ∀ x ∈ E, J t x ≤ 1 + t ^ 2 / 2 * q x + C * |t| ^ 3) → 0 ≤ ∫ x in E, q x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

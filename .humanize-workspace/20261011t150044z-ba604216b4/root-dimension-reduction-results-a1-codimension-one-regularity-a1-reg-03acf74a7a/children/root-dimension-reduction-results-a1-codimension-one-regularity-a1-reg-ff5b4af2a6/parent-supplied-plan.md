# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.normal_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ff5b4af2a6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1`
- Child key: `normal_monotonicity`
- Declaration: `Submission.codim1_rdo_dg_hr_ae_translate_monotone`
- Exact Lean type: `∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n)), MeasurableSet F → (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∫ z in F, fderiv ℝ ζ z v ≤ 0) → ∀ t : ℝ, 0 ≤ t → ∀ᵐ z ∂volume, z ∈ F → z + t • v ∈ F`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.translation_identity-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.halfspace_rigidity-a1.nonneg_fundamental_lemma-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

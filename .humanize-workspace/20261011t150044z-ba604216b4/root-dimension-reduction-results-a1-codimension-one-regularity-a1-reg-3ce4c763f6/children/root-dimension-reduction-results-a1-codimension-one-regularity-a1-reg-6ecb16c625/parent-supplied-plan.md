# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1.signed_layer_cake-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-6ecb16c625/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.cutoff_estimates-a1`
- Child key: `signed_layer_cake`
- Declaration: `Submission.codim1_rdo_dg_ce_signed_layer_cake`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (ζ g : X → ℝ) (S B : Set X) (c : ℝ), Measurable ζ → Measurable g → (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) → (∀ x, |g x| ≤ 1) → MeasurableSet S → μ S ≠ ∞ → (∀ x, x ∉ S → ζ x = 0) → (∀ x ∈ B, ζ x = 1) → 0 ≤ c → (∀ t : ℝ, 0 < t → t ≤ 1 → c * (μ {x | t ≤ ζ x}).toReal ≤ ∫ x in {x | t ≤ ζ x}, g x ∂μ) → c * (μ B).toReal ≤ ∫ x, ζ x * g x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

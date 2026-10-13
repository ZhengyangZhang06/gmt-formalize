# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1.local_inverse_c2-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-0b6659d640/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.graph_chart-a1`
- Child key: `local_inverse_c2`
- Declaration: `Submission.codim1_rdo_gc_local_inverse_c2`
- Exact Lean type: `∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 2 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (g : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 2 g O ∧ MapsTo g O V₀ ∧ (∀ y ∈ O, φ (g y) = y) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ g (φ z) = z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

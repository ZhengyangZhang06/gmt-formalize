# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1.c1_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-91f4b972eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1`
- Child key: `c1_inverse`
- Declaration: `Submission.idtp_ccd_scsp_li_c1_inverse`
- Exact Lean type: `∀ (d : ℕ) (Φ : Euclid d → Euclid d) (V : Set (Euclid d)) (v₀ : Euclid d), IsOpen V → v₀ ∈ V → ContDiffOn ℝ 1 Φ V → Injective (fderiv ℝ Φ v₀) → ∃ (V₁ O : Set (Euclid d)) (H : Euclid d → Euclid d), IsOpen V₁ ∧ IsOpen O ∧ v₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Φ v₀ ∈ O ∧ ContDiffOn ℝ 1 H O ∧ H '' O = V₁ ∧ (∀ w ∈ O, Φ (H w) = w) ∧ ∀ w ∈ O, Surjective (fderiv ℝ H w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

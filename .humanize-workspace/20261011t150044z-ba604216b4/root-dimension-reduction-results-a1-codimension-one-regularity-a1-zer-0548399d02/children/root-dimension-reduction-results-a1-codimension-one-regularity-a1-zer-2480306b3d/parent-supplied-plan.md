# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.mollify_l1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-2480306b3d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `mollify_l1`
- Declaration: `Submission.codim1_zsl_pc_mollify_indicator_l1`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid m)) (R η : ℝ), MeasurableSet F → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : Euclid m → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z, δ < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤ ENNReal.ofReal η`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.translate_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.cube_average-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-712a939051/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `cube_average`
- Declaration: `Submission.codim1_zsl_pc_cube_average_bound`
- Exact Lean type: `∀ (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set (Euclid m)) (R C δ : ℝ), MeasurableSet F → 0 ≤ C → 0 < δ → δ * Real.sqrt m ≤ 1 → (∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ ≤ ENNReal.ofReal (K * C * δ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

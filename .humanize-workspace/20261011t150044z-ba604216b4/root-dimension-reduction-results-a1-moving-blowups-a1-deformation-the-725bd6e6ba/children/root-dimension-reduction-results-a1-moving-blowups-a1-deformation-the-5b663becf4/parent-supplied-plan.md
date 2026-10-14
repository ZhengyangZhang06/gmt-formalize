# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1.markov_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-5b663becf4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1`
- Child key: `markov_point`
- Declaration: `Submission.dimred_mbl_dtsd_gr_exists_deriv_le_off_null`
- Exact Lean type: `∀ (F : ℝ → ℝ) (ρ : ℝ) (B : ℝ≥0∞) (N : Set ℝ), Monotone F → 0 < ρ → ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ B → (volume : Measure ℝ) N = 0 → ∃ r ∈ Ioo (ρ / 2) ρ, r ∉ N ∧ ENNReal.ofReal (deriv F r) ≤ ENNReal.ofReal (4 / ρ) * B`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1.lebesgue_deriv-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

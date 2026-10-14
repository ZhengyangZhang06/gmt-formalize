# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.rescaled_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-f08bd35b68/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `rescaled_volume`
- Declaration: `Submission.codim1_rdo_dg_bh_rescaled_volume_lower`
- Exact Lean type: `∀ (m : ℕ) (F : Set (Euclid (m + 1))) (y : Euclid (m + 1)) (c₂ ρ₂ : ℝ), MeasurableSet F → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (F ∩ ball y ρ) ∧ ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (ball y ρ \ F)) → ∀ s r : ℝ, 0 < s → 0 < r → r * s < ρ₂ → ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume ((fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s) ∧ ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume (ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

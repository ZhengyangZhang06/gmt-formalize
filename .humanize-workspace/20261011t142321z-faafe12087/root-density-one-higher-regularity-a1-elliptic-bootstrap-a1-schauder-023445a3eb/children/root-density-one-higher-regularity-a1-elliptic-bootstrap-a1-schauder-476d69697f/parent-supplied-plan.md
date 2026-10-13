# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1.cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-476d69697f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1`
- Child key: `cutoff`
- Declaration: `Submission.dohr_eb_sch_cacc_exists_cutoff`
- Exact Lean type: `∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (y : Rn n) (ρ : ℝ), 0 < ρ → ∃ η : Rn n → ℝ, ContDiff ℝ 1 η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ ball y ρ, η x = 1) ∧ HasCompactSupport η ∧ tsupport η ⊆ ball y (2 * ρ) ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ K / ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

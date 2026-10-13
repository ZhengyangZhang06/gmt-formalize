# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1.localized_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-240154921d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1`
- Child key: `localized_integral`
- Declaration: `Submission.dohr_eb_sch_bu_wel_localized_integral`
- Exact Lean type: `∀ (n : ℕ) (f : Rn n → ℝ) (O T : Set (Rn n)), IsOpen O → IsCompact T → T ⊆ O → ContinuousOn f O → (∀ z, z ∉ T → f z = 0) → Continuous f ∧ Integrable f ∧ ∫ z in O, f z = ∫ z, f z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

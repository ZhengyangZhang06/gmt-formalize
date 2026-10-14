# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1.action_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1-imrep-cu-4cb41f997a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1`
- Child key: `action_bound`
- Declaration: `Submission.rsd_cmr_ic_action_abs_le`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)) (ω : TestFormOn U n) (ε : ℝ), IsCompact K → K ⊆ U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ ε) → |R.action (ω : DifferentialForm (Euclid P) n)| ≤ ε * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_support_eq_measure_support-a1.unit_orientation_nonzero_bounded-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1.open_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1-open-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1`
- Child key: `open_approx`
- Declaration: `Submission.rsd_mw_wlm_exists_open_measure_between`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (W : Set (Euclid P)), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < R.measure W → ∃ V : Set (Euclid P), IsOpen V ∧ V ⊆ W ∧ c < R.measure V ∧ R.measure V < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

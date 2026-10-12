# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1.eval_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1-weight-le-mass-a1-eval-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1`
- Child key: `eval_formula`
- Declaration: `Submission.rsd_mw_wlm_eval_eq_integral_restrict`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ (V : Set (Euclid P)) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ V → T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂(R.measure.restrict V)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

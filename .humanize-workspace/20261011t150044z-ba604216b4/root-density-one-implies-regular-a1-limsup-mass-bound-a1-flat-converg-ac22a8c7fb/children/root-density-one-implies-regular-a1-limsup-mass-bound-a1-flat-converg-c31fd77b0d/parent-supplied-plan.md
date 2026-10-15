# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1.partial_sums-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-c31fd77b0d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- Child key: `partial_sums`
- Declaration: `Submission.dor_lmb_fc_ims_partial_sum_reps`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → ∀ q : ℕ, ∃ R' : IMRep U n, (∀ᵐ x ∂μHE[n], R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x = ∑ r ∈ Finset.range q, (R r).carrier.indicator (fun y => ((R r).mult y : ℝ) • (R r).orient y) x) ∧ R'.measure ≤ ∑ r ∈ Finset.range q, (R r).measure`

## Sibling prerequisites

- `root.regular_set_dense-a1.integer_combination-a1.combination_construction-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1.mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

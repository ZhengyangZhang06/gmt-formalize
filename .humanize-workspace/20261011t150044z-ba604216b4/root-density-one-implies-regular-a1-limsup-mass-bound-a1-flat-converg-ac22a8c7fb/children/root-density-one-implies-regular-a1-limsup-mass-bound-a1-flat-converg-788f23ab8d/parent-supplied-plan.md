# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1.ae_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-788f23ab8d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.im_series-a1`
- Child key: `ae_limit`
- Declaration: `Submission.dor_lmb_fc_ims_ae_limit_imrep`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n) (η : Euclid P → MultiVector P n), IsOpen U → (∀ᵐ x ∂μHE[n], Tendsto (fun q => (R q).carrier.indicator (fun y => ((R q).mult y : ℝ) • (R q).orient y) x) atTop (𝓝 (η x))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ q, (R q).measure K ≤ C) → ∃ R' : IMRep U n, (∀ᵐ x ∂μHE[n], R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x = η x) ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x, η x (ω x) ∂μHE[n]`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.action_dct-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-65ff0119c2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child key: `action_dct`
- Declaration: `Submission.dor_lmbsf_ll_action_mul_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (C : ℝ), (∀ k, Measurable (hs k)) → (∀ k x, |hs k x| ≤ C) → (∀ x, Tendsto (fun k => hs k x) atTop (𝓝 (h x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * hs k x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * h x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]))`

## Sibling prerequisites

- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.imrep_current-a1.action_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

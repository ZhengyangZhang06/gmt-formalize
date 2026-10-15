# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.fix_orient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-a1d5760847/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`
- Child key: `fix_orient`
- Declaration: `Submission.dor_lmb_pc_imrep_orient_fixed_by_retraction`
- Exact Lean type: `∀ (P n d : ℕ) (U N O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 d N → MeasurableSet O → μHE[n] (R.carrier \ N) = 0 → (∀ x ∈ N ∩ O, f x = x) → (∀ x ∈ N ∩ O, ∀ v ∈ tangentSpace N x, fderiv ℝ f x v = v) → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), f x = x ∧ ∀ α : Covector (Euclid P) n, R.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = R.orient x α`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.orient_comp-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

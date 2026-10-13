# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1.fixed_support_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-d688d9da39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`
- Child key: `fixed_support_dense`
- Declaration: `Submission.dor_lmbs_tfa_fixed_support_dense`
- Exact Lean type: `∀ (P n : ℕ) (U K : Set (Euclid P)), IsCompact K → ∃ D : Set (TestFormOn U n), D.Countable ∧ (∀ η ∈ D, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ η ∈ D, (∀ x, dist ((ω : DifferentialForm (Euclid P) n) x) ((η : DifferentialForm (Euclid P) n) x) < ε) ∧ ∀ x, dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) (exteriorDerivative (η : DifferentialForm (Euclid P) n) x) < ε`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1.covector_findim-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

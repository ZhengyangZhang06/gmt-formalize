# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-t-9b84f5afc6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child key: `testform_dense`
- Declaration: `Submission.dor_lmbs_testForm_countable_approx`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ D : Set (TestFormOn U n), D.Countable ∧ ∀ ω : TestFormOn U n, ∃ (K : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), IsCompact K ∧ K ⊆ U ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K ∧ (∀ k, ωs k ∈ D) ∧ (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ K) ∧ TendstoUniformly (fun k x => (ωs k : DifferentialForm (Euclid P) n) x) (ω : DifferentialForm (Euclid P) n) atTop ∧ TendstoUniformly (fun k x => exteriorDerivative (ωs k : DifferentialForm (Euclid P) n) x) (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

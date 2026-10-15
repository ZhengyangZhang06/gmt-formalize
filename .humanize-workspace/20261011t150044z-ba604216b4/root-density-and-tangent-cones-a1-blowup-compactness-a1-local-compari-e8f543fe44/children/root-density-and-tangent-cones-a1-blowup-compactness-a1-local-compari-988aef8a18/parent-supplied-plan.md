# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1.truncate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-988aef8a18/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1`
- Child key: `truncate`
- Declaration: `Submission.dtc_bc_lc_fd_lz_truncate`
- Exact Lean type: `∀ (P n : ℕ) (U E : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → MeasurableSet E → R.Represents T → ∃ (T' : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents T' ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ R'.measure = R.measure.restrict E ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ E → T' ω = T ω) ∧ ∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → T' ω = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

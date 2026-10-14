# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1.testform_restrict_cc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-rep-f608128ac6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Child key: `testform_restrict_cc`
- Declaration: `Submission.cmrc_testForm_restrict_cc`
- Exact Lean type: `∀ (P n d : ℕ) (U : Set (Euclid P)) (f : Covector (Euclid P) n → EuclideanSpace ℝ (Fin d)), Continuous f → f 0 = 0 → ∀ ω : TestFormOn U n, ∃ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), ∀ x : U, g x = f ((ω : DifferentialForm (Euclid P) n) x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.segment_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d9cb35f6b9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child key: `segment_current`
- Declaration: `Submission.cbr_cc_segment_current`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P : ℕ) (a b : Euclid P), ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) 1, IsIntegerMultiplicity S ∧ (∀ g : TestFormOn (univ : Set (Euclid P)) 0, S.boundary g = (g : DifferentialForm (Euclid P) 0) b (fun i => i.elim0) - (g : DifferentialForm (Euclid P) 0) a (fun i => i.elim0)) ∧ S.mass < ∞ ∧ S.support ⊆ segment ℝ a b`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.current_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

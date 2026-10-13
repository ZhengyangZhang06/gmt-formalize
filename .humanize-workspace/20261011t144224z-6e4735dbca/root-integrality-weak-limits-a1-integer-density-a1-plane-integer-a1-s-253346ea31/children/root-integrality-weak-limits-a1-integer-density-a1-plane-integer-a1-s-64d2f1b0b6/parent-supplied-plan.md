# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-64d2f1b0b6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1`
- Child key: `cycle_slice_boundary`
- Declaration: `Submission.ind_pi_ss_cycle_slice_boundary`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ) (t : ℝ) (S : GeometricCurrentOn U m), IsOpen U → T.boundary = 0 → IsSlice T f t S → ∃ A : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ f x < t} A ∧ A.boundary = S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

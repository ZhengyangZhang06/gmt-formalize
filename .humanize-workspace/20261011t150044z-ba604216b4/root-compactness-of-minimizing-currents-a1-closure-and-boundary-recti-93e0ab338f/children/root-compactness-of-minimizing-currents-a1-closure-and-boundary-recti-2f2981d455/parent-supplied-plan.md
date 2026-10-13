# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.halfspace_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2f2981d455/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1`
- Child key: `halfspace_ftc`
- Declaration: `Submission.cbr_cipi_halfspace_partial_integral`
- Exact Lean type: `∀ (d : ℕ) (g : (Fin (d + 1) → ℝ) → ℝ) (t : ℝ), ContDiff ℝ 1 g → HasCompactSupport g → (∀ i : Fin (d + 1), i ≠ 0 → ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single i 1) = 0) ∧ ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single 0 1) = ∫ z' : Fin d → ℝ, g (Fin.cons t z')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

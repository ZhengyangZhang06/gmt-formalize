# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1`
- Child key: `flat_convergence`
- Declaration: `Submission.cmc_flat_convergence`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → IsIntegerMultiplicity T → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + (Ts j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ts T → ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ∃ (R : ℕ → GeometricCurrentOn U (m + 2)) (S : ℕ → GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (R j) ∧ IsIntegerMultiplicity (S j) ∧ T - Ts j - S j = (R j).boundary) ∧ Tendsto (fun j => (R j).massOn W + (S j).massOn W) atTop (𝓝 0)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

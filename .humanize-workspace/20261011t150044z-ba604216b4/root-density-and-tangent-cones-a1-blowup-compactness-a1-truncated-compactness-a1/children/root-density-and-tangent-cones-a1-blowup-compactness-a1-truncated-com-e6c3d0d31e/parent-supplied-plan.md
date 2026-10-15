# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-e6c3d0d31e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1`
- Child key: `closure`
- Declaration: `Submission.dtc_bc_tc_closure`
- Exact Lean type: `∀ (P m : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), m + 1 < P → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, ((Ts j).massOn W + (Ts j).boundary.massOn W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

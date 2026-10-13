# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.orientation_fixed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-b3605f7958/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child key: `orientation_fixed`
- Declaration: `Submission.dtc_bc_lc_orient_fixed`
- Exact Lean type: `∀ (P n : ℕ) (U O : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (f : Euclid P → Euclid P), IsOpen U → IsOpen O → R.Represents T → DifferentiableOn ℝ f O → (∀ y ∈ T.support ∩ O, f y = y) → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), f x = x ∧ ∀ α : Covector (Euclid P) n, R.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = R.orient x α`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

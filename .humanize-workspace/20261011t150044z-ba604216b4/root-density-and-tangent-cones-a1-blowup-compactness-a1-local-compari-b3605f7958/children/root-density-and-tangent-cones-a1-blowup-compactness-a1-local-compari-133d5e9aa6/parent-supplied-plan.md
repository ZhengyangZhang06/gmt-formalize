# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.orientation_fixed-a1.fderiv_fixes_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-133d5e9aa6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.orientation_fixed-a1`
- Child key: `fderiv_fixes_tangent`
- Declaration: `Submission.dtc_bc_lc_fderiv_apply_eq_of_approxTangent`
- Exact Lean type: `∀ (P n : ℕ) (A : Set (Euclid P)) (f : Euclid P → Euclid P) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), HasApproximateTangentSpaceAt n A x Q → DifferentiableAt ℝ f x → f x = x → (∀ y ∈ A, f y = y) → ∀ v ∈ Q, fderiv ℝ f x v = v`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1.blowup_points-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

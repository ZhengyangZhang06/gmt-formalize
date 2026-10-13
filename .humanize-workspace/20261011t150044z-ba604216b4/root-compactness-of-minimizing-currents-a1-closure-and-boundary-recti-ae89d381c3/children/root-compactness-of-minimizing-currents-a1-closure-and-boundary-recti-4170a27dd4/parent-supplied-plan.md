# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1.variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4170a27dd4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`
- Child key: `variation_bound`
- Declaration: `Submission.cbr_ci_pw_l1_boundary_variation_bound`
- Exact Lean type: `∀ (d : ℕ) (U : Set (Euclid (d + 1))) (Y : GeometricCurrentOn U (d + 1)) (u : Euclid (d + 1) → ℝ) (ε : Covector (Euclid (d + 1)) d) (f : Euclid (d + 1) → ℝ) (z : Euclid (d + 1)) (M : ℝ), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ y in U, u y * (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) y (fun i => EuclideanSpace.single i (1 : ℝ))) → Y.boundary.massOn U ≠ ∞ → covectorEuclideanNorm ε ≤ ‖z‖ → (∀ y, exteriorDerivative (fun x => f x • ε) y (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ f y z) → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U → (∀ y, |f y| ≤ M) → |∫ y in U, u y * fderiv ℝ f y z| ≤ (Y.boundary.massOn U).toReal * ‖z‖ * M`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`
- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

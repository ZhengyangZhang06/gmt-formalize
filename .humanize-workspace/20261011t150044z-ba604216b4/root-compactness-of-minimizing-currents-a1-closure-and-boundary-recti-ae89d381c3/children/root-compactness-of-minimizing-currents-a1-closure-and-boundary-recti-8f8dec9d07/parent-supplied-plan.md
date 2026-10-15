# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1.scalar_tests-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-8f8dec9d07/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.l1_constant-a1`
- Child key: `scalar_tests`
- Declaration: `Submission.cbr_ci_pw_l1_scalar_test_tendsto`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Euclid n)) (c : ℝ) (Y : ℕ → GeometricCurrentOn U n) (u : ℕ → Euclid n → ℝ), (∀ (k : ℕ) (ω : TestFormOn U n), Y k ω = ∫ y in U, u k y * (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))) → (∀ ω : TestFormOn U n, Tendsto (fun k => Y k ω) atTop (𝓝 (c * ∫ y, (ω : DifferentialForm (Euclid n) n) y (fun i => EuclideanSpace.single i (1 : ℝ))))) → ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → Tendsto (fun k => ∫ y in U, u k y * b y) atTop (𝓝 (c * ∫ y, b y))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.det_covector-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

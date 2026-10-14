# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1.bounded_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-ae24472ce6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1`
- Child key: `bounded_current`
- Declaration: `Submission.cmc_fc_sc_current_of_coeff_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ) (A : ℝ), (∀ (ω : TestFormOn U n) (c : ℝ), 0 < c → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |L ω| ≤ c * A) → ∃ Y : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, Y ω = L ω`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.uniform_small-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

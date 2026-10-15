# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.radial_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e486a1b156/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1`
- Child key: `radial_homotopy`
- Declaration: `Submission.dimred_cs_sos_cfs_radial_homotopy`
- Exact Lean type: `∀ (P q : ℕ) (β : DifferentialForm (Euclid P) (q + 1)), ContDiff ℝ (⊤ : ℕ∞) β → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => ∫ t in (0 : ℝ)..1, t ^ q • (β (t • x)).curryLeft x) ∧ ∀ x : Euclid P, exteriorDerivative (fun y : Euclid P => ∫ t in (0 : ℝ)..1, t ^ q • (β (t • y)).curryLeft y) x + (∫ t in (0 : ℝ)..1, t ^ (q + 1) • (exteriorDerivative β (t • x)).curryLeft x) = β x`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.param_integral-a1`
- `root.density_and_tangent_cones-a1.cone-a1.euler_cartan-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

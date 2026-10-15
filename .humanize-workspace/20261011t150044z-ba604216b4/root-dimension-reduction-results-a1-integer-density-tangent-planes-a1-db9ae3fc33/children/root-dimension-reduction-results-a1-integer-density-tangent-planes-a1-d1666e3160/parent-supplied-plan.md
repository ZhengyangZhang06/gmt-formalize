# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1.indicator_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d1666e3160/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1`
- Child key: `indicator_extension`
- Declaration: `Submission.idtp_cse_rc_tf_indicator_extension`
- Exact Lean type: `∀ (P : ℕ) (U K : Set (Euclid P)) (h : Euclid P → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ x ∈ U, ContDiffAt ℝ 1 h x) → (∀ y ∈ U, h y ≠ 0 → y ∈ K) → ContDiff ℝ 1 (U.indicator h) ∧ HasCompactSupport (U.indicator h) ∧ (∀ x ∈ U, fderiv ℝ (U.indicator h) x = fderiv ℝ h x) ∧ (∀ x ∉ U, fderiv ℝ (U.indicator h) x = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

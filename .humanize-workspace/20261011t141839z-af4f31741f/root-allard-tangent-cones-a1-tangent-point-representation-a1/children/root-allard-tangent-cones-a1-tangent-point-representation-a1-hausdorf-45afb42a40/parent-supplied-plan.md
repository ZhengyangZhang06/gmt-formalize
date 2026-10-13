# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_point_representation-a1.hausdorff_null_of_weight_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-hausdorf-45afb42a40/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child key: `hausdorff_null_of_weight_null`
- Declaration: `Submission.allard_tc_tpr_hausdorff_null_of_weight_null`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (Z : Set (Euclidean N)) (θ : Euclidean N → ℝ), (∀ K : Set (Euclidean N), IsCompact K → μ K ≠ ∞) → μ Z = 0 → (∀ x ∈ Z, 0 < θ x ∧ HasDensity n μ x (ENNReal.ofReal (θ x))) → μHE[n] Z = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_point_representation-a1.weighted_approx_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1-weighted-38a994edcd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.tangent_point_representation-a1`
- Child key: `weighted_approx_tangent`
- Declaration: `Submission.allard_tc_tpr_weighted_approx_tangent_iff`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (x : Euclidean N) (T : Grassmannian N n), NullMeasurableSet M μHE[n] → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) μHE[n]) → (∀ B : Set (Euclidean N), MeasurableSet B → V.weight B = ∫⁻ y in M ∩ B, ENNReal.ofReal (θ y) ∂μHE[n]) → HasTangentPlane V x T (θ x) → ∀ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane ↔ S = T`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.tangent_point_representation-a1.integral_eq_weighted-a1`
- `root.allard_tangent_cones-a1.tangent_point_representation-a1.blowup_set_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

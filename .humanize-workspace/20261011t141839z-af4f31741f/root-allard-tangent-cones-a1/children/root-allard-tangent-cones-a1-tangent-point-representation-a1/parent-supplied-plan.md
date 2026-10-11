# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_point_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-point-representation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `tangent_point_representation`
- Declaration: `Submission.allard_tc_tangent_point_representation`
- Exact Lean type: `FirstRectifiabilityTheorem → ∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))), (∀ᵐ x ∂C.weight, ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane C x T θ) → ∃ (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf C M θ ∧ (∀ x ∈ M, ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x)) ∧ ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x) ∧ (x, T) ∈ A}, ENNReal.ofReal (θ x) ∂μHE[n]`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.tangent_plane_density-a1`
- `root.allard_tangent_cones-a1.tangent_plane_dilation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

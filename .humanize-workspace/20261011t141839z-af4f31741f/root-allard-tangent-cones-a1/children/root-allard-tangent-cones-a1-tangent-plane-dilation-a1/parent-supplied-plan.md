# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.tangent_plane_dilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-dilation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `tangent_plane_dilation`
- Declaration: `Submission.allard_tc_tangent_plane_dilation`
- Exact Lean type: `∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (s : ℝ) (y : Euclidean N) (T T' : Grassmannian N n) (θ θ' : ℝ), 0 < s → (∀ A : Set (Euclidean N), C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A) → HasTangentPlane C y T θ → HasTangentPlane C (s • y) T' θ' → T' = T ∧ θ' = θ`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.tangent_plane_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

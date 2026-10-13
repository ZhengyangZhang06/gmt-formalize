# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.tangent_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-unique-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `tangent_unique`
- Declaration: `Submission.frt_tangent_plane_unique`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T T' : Grassmannian N n) (θ θ' : ℝ), HasTangentPlane V x T θ → HasTangentPlane V x T' θ' → T' = T ∧ θ' = θ`

## Sibling prerequisites

- `root.first_rectifiability-a1.weight_blowup-a1`
- `root.first_rectifiability-a1.tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

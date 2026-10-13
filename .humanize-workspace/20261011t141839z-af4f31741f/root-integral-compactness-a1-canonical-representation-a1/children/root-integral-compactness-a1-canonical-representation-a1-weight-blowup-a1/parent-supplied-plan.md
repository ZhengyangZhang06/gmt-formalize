# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.canonical_representation-a1.weight_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1-weight-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.canonical_representation-a1`
- Child key: `weight_blowup`
- Declaration: `Submission.intcpt_canon_weight_blowup_tendsto`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → ∀ g : C_c(Euclidean N, ℝ), Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * ∫ z, g (t⁻¹ • (z - x)) ∂V.weight) (𝓝[>] 0) (𝓝 (θ * ∫ y in (T.plane : Set (Euclidean N)), g y ∂μHE[n]))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

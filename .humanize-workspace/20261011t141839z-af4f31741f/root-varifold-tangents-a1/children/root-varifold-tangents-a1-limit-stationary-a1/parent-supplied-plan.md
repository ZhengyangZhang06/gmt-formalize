# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.limit_stationary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-limit-stationary-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1`
- Child key: `limit_stationary`
- Declaration: `Submission.varifold_tangents_limit_stationary`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (C : Varifold N n (univ : Set (Euclidean N))), V.HasLocallyBoundedFirstVariation → x ∈ U → Tendsto (fun ρ : ℝ ↦ ENNReal.ofReal ρ * variationMeasure V (closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → IsVarifoldTangent V x C → C.Stationary`

## Sibling prerequisites

- `root.varifold_tangents-a1.rescaled_divergence_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.rescaled_integral-a1.approx_tangent_similarity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-rescaled-integral-a1-approx-tangent-similarity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.rescaled_integral-a1`
- Child key: `approx_tangent_similarity`
- Declaration: `Submission.intcpt_ri_weightedApproxTangent_similarity_iff`
- Exact Lean type: `∀ (N n : ℕ) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ) (ξ y : Euclidean N) (t : ℝ) (P : Submodule ℝ (Euclidean N)), 0 < t → (Chapter03.HasWeightedApproximateTangentSpaceAt n ((fun w : Euclidean N ↦ ξ + t • w) ⁻¹' M) (fun w : Euclidean N ↦ θ (ξ + t • w)) y P ↔ Chapter03.HasWeightedApproximateTangentSpaceAt n M θ (ξ + t • y) P)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

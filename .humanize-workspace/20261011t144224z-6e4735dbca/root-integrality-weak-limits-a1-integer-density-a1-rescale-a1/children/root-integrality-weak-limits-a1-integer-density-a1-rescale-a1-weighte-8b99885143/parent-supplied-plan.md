# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.weighted_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-weighte-8b99885143/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`
- Child key: `weighted_tangent`
- Declaration: `Submission.ind_rs_weightedTangent_dilation`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x y : Eucl P) (r : ℝ) (Q : Submodule ℝ (Eucl P)), 0 < r → HasWeightedApproximateTangentSpaceAt n M θ y Q → HasWeightedApproximateTangentSpaceAt n ((fun w => r⁻¹ • (w - x)) '' M) (fun z => θ (x + r • z)) (r⁻¹ • (y - x)) Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.pushforward_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-pushforward-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1`
- Child key: `pushforward_measurable`
- Declaration: `Submission.deformation_ipl_tangential_pushforward_aestronglyMeasurable`
- Exact Lean type: `∀ (P Q k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (f : Eucl P → Eucl Q) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsOpen U → IsRectifiableTriple U k M θ ξ → LocallyLipschitzOn U f → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) → AEStronglyMeasurable (fun x => nVectorPushforward k (L x) (ξ x)) ((μHE[k] : Measure (Eucl P)).restrict M)`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`
- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`
- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

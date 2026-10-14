# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.integrand_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-inte-b85bcf5018/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `integrand_bound`
- Declaration: `Submission.deformation_ipl_cc_pushforward_integrand_bound`
- Exact Lean type: `∀ (P Q k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (A : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (β : Eucl P → Covector (Eucl Q) k) (Λ : ℝ), IsOpen U → IsRectifiableTriple U k M θ ξ → AEStronglyMeasurable (fun x => nVectorPushforward k (A x) (ξ x)) ((μHE[k] : Measure (Eucl P)).restrict M) → AEStronglyMeasurable β ((μHE[k] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Tx → ∀ v ∈ Tx, ‖A x v‖ ≤ Λ * ‖v‖) → AEStronglyMeasurable (fun x => θ x * nVectorPushforward k (A x) (ξ x) (β x)) ((μHE[k] : Measure (Eucl P)).restrict M) ∧ ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), |θ x * nVectorPushforward k (A x) (ξ x) (β x)| ≤ Λ ^ k * ‖β x‖ * θ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

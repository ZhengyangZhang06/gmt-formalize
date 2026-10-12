# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_iff_variational-a1.first_variation_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-stationary-iff-variational-a1-first-variation-continuity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_iff_variational-a1`
- Child key: `first_variation_continuity`
- Declaration: `Submission.tendsto_integral_tangentialDiv_of_tendstoUniformly_fderiv`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (K : Set (Ambient n ℓ)) (X : Ambient n ℓ → Ambient n ℓ) (Y : ℕ → Ambient n ℓ → Ambient n ℓ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsCompact K → ContDiff ℝ 1 X → tsupport X ⊆ K → (∀ k, ContDiff ℝ 1 (Y k) ∧ tsupport (Y k) ⊆ K) → TendstoUniformly (fun k ↦ fderiv ℝ (Y k)) (fderiv ℝ X) atTop → Tendsto (fun k ↦ ∫ x, V.tangentialDiv (Y k) x ∂V.weight) atTop (𝓝 (∫ x, V.tangentialDiv X x ∂V.weight))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

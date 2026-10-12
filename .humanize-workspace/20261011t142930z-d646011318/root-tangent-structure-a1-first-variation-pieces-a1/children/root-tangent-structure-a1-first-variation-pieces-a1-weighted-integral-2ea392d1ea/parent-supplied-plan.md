# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.first_variation_pieces-a1.weighted_integral_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-first-variation-pieces-a1-weighted-integral-2ea392d1ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.first_variation_pieces-a1`
- Child key: `weighted_integral_derivative`
- Declaration: `Submission.ts_fv_hasDerivAt_of_weighted_jacobian`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (K : Set (Ambient n ℓ)) (m : ℝ → ℝ≥0∞) (J J' : ℝ → Ambient n ℓ → ℝ) (g : Ambient n ℓ → ℝ) (δ B : ℝ), 0 < δ → IsCompact K → (∀ t ∈ Ioo (-δ) δ, m t = ∫⁻ x in a.M ∩ K, ENNReal.ofReal (a.θ x * J t x) ∂μHE[n]) → (∀ t ∈ Ioo (-δ) δ, AEStronglyMeasurable (J t) ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M)) → AEStronglyMeasurable g ((μHE[n] : Measure (Ambient n ℓ)).restrict a.M) → (∀ x ∉ K, g x = 0) → (∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, x ∈ K → J' 0 x = g x ∧ ∀ t ∈ Ioo (-δ) δ, 0 ≤ J t x ∧ J t x ≤ B ∧ HasDerivAt (fun s ↦ J s x) (J' t x) t ∧ |J' t x| ≤ B) → HasDerivAt (fun t ↦ (m t).toReal) (∫ x, g x ∂(mk a).weight) 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

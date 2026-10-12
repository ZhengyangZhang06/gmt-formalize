# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_weighted_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1`
- Child key: `piece_weighted_blowup`
- Declaration: `Submission.ts_piece_weighted_blowup_ae`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n → (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧ (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧ ContinuousOn (fderiv ℝ F) C ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → ∀ᵐ x ∂(μHE[n] : Measure (Ambient n ℓ)).restrict a.M, ∀ w ∈ C, F w = x → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * ∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n]))`

## Sibling prerequisites

- `root.tangent_structure-a1.piece_density_blowup-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

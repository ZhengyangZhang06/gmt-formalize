# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_density_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1`
- Child key: `piece_density_blowup`
- Declaration: `Submission.ts_piece_density_blowup`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ), 0 < n → (IsCompact C ∧ (∃ K : NNReal, LipschitzWith K F) ∧ (∀ w ∈ C, DifferentiableAt ℝ F w ∧ Function.Injective (fderiv ℝ F w)) ∧ ContinuousOn (fderiv ℝ F) C ∧ ∃ c : ℝ, 0 < c ∧ ∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → (∃ Γ : ℝ, ∀ x ∈ F '' C, ∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (F '' C ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) ∧ ∀ w ∈ C, Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in F '' C, f (t⁻¹ • (y - F w)) ∂μHE[n]) (𝓝[>] 0) (𝓝 (∫ y in (LinearMap.range (fderiv ℝ F w).toLinearMap : Set (Ambient n ℓ)), f y ∂μHE[n]))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

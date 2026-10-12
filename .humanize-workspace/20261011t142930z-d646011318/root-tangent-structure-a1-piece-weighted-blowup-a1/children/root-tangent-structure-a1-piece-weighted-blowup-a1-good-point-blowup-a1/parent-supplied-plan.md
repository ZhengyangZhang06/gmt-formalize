# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_weighted_blowup-a1.good_point_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-weighted-blowup-a1-good-point-blowup-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_weighted_blowup-a1`
- Child key: `good_point_blowup`
- Declaration: `Submission.ts_pwb_blowup_at_good_point`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : RectifiablePair n ℓ) (N K : Set (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (Γ L : ℝ), MeasurableSet N → (μHE[n] : Measure (Ambient n ℓ)) N ≠ ⊤ → IsCompact K → K ⊆ a.M ∩ N → x ∈ K → ContinuousWithinAt a.θ K x → (∀ ρ : ℝ, 0 < ρ → (μHE[n] : Measure (Ambient n ℓ)) (N ∩ closedBall x ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → Tendsto (fun r : ℝ ↦ (mk a).weight.real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ((μHE[n] : Measure (Ambient n ℓ)).restrict N).real (Kᶜ ∩ closedBall x r) / r ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y in N, f (t⁻¹ • (y - x)) ∂μHE[n]) (𝓝[>] 0) (𝓝 L) → Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ y, f (t⁻¹ • (y - x)) ∂(mk a).weight) (𝓝[>] 0) (𝓝 (a.θ x * L))`

## Sibling prerequisites

- `root.tangent_structure-a1.piece_weighted_blowup-a1.pair_weight_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.c1_chart_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-chart-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child key: `c1_chart_cover`
- Declaration: `Submission.tae_rectifiable_c1_chart_cover`
- Exact Lean type: `∀ {n ℓ : ℕ} (M : Set (Amb n ℓ)), 1 ≤ n → Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N₀ : Set (Amb n ℓ)) (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (ρ : ℕ → ℝ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∀ v ∈ ball (c k) (ρ k), Function.Injective (fderiv ℝ (G k) v)) ∧ (∀ k, ∃ κ : ℝ, 0 < κ ∧ ∀ v ∈ ball (c k) (ρ k), ∀ w ∈ ball (c k) (ρ k), κ * ‖v - w‖ ≤ ‖G k v - G k w‖) ∧ M ⊆ N₀ ∪ ⋃ k, G k '' ball (c k) (ρ k)`

## Sibling prerequisites

- `root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

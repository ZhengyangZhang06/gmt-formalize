# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollifier_seq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollifier-seq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`
- Child key: `mollifier_seq`
- Declaration: `Submission.deGiorgiSobInd_mollifier_seq`
- Exact Lean type: `∀ (N : ℕ) (r : ℝ), 0 < r → ∃ ρ : ℕ → Rn N → ℝ, (∀ j, ContDiff ℝ 1 (ρ j)) ∧ (∀ j, HasCompactSupport (ρ j)) ∧ (∀ j y, 0 ≤ ρ j y) ∧ (∀ j, ∫ y, ρ j y = 1) ∧ (∀ j, tsupport (ρ j) ⊆ Metric.closedBall (0 : Rn N) (r / ((j : ℝ) + 1))) ∧ ∀ G : Set (Rn N), NullMeasurableSet G volume → (∀ j, ∃ L : ℝ≥0, LipschitzWith L (fun y ↦ ∫ z in G, ρ j (y - z))) ∧ (∀ j y, 0 ≤ (∫ z in G, ρ j (y - z)) ∧ (∫ z in G, ρ j (y - z)) ≤ 1) ∧ (∀ᵐ y ∂(volume : Measure (Rn N)), Tendsto (fun j ↦ ∫ z in G, ρ j (y - z)) atTop (𝓝 (G.indicator (fun _ ↦ (1 : ℝ)) y))) ∧ ∀ h : Rn N → ℝ, Integrable h → Tendsto (fun j ↦ ∫ y, (∫ z in G, ρ j (y - z)) * h y) atTop (𝓝 (∫ y in G, h y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

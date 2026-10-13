# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_eq_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-measure-eq-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `measure_eq_density`
- Declaration: `Submission.deGiorgiRH_measure_eq_of_density`
- Exact Lean type: `∀ (n N : ℕ) (μ σ : Measure (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ K : Set (Rn N), IsCompact K → σ K < ∞) → μ ≪ σ → (∀ᵐ x ∂σ, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1))) ∧ Tendsto (fun ρ : ℝ ↦ σ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))) → μ = σ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

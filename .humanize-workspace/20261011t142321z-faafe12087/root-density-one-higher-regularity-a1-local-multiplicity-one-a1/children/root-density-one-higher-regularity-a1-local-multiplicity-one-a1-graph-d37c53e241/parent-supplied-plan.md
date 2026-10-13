# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.graph_support_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-graph-d37c53e241/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `graph_support_density`
- Declaration: `Submission.dohr_lmo_graph_support_density`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ x ∈ ball (0 : Rn n) R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ ρ : ℝ, ρ < R → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball ξ ρ) < ⊤) ∧ ∀ y ∈ S ∩ ball ξ R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

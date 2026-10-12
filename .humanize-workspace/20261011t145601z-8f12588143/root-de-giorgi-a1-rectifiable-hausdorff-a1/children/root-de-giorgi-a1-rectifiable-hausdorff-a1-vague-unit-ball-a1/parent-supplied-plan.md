# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.vague_unit_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-vague-unit-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `vague_unit_ball`
- Declaration: `Submission.deGiorgiRH_closedBall_tendsto_of_vague_plane`
- Exact Lean type: `∀ (n N : ℕ) (ν : ℝ → Measure (Rn N)) (P : Submodule ℝ (Rn N)), finrank ℝ P = n → (∀ᶠ r in 𝓝[>] (0 : ℝ), ν r (Metric.closedBall 0 2) < ∞) → (∀ f : C_c(Rn N, ℝ), Tendsto (fun r : ℝ ↦ ∫ y, f y ∂(ν r)) (𝓝[>] 0) (𝓝 (∫ y in (P : Set (Rn N)), f y ∂μHE[n]))) → Tendsto (fun r : ℝ ↦ ν r (Metric.closedBall 0 1)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))`

## Sibling prerequisites

- `root.de_giorgi-a1.rectifiable_hausdorff-a1.plane_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.hausdorff_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-hausdorff-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `hausdorff_density`
- Declaration: `Submission.deGiorgiRH_hausdorff_density_of_approxTangent`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)) (x : Rn N) (P : Submodule ℝ (Rn N)), (∃ δ : ℝ, 0 < δ ∧ μHE[n] (M ∩ Metric.closedBall x δ) < ∞) → HasApproximateTangentSpaceAt n M x P → Tendsto (fun ρ : ℝ ↦ μHE[n] (M ∩ Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))`

## Sibling prerequisites

- `root.de_giorgi-a1.rectifiable_hausdorff-a1.vague_unit_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.hausdorff_le_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-hausdorff-le-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `hausdorff_le_measure`
- Declaration: `Submission.deGiorgiRH_hausdorff_le_of_density`
- Exact Lean type: `∀ (n N : ℕ) (μ : Measure (Rn N)) (A : Set (Rn N)), (∀ K : Set (Rn N), IsCompact K → μ K < ∞) → (∀ x ∈ A, Tendsto (fun ρ : ℝ ↦ μ (Metric.closedBall x ρ) / ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 (volume (Metric.ball (0 : Rn n) 1)))) → μHE[n] A ≤ μ A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

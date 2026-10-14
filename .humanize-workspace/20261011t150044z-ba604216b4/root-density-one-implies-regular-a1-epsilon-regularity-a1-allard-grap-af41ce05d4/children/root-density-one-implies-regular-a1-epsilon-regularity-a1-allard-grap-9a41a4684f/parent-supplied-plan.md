# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1.l2_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9a41a4684f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- Child key: `l2_subseq`
- Declaration: `Submission.dorag_ha_rb_l2_subseq`
- Exact Lean type: `∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ), (∀ j, MemLp (f j) 2 μ) → (∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x, (f j x - f k x) ^ 2 ∂μ ≤ η) → ∃ (φ : ℕ → ℕ) (W : α → ℝ), StrictMono φ ∧ MemLp W 2 μ ∧ Tendsto (fun j => ∫ x, (f (φ j) x - W x) ^ 2 ∂μ) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.chart_pieces-a1.lipschitz_open_charts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-chart-pieces-a1-lipschitz-open-charts-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.chart_pieces-a1`
- Child key: `lipschitz_open_charts`
- Declaration: `Submission.submanifold_cover_lipschitz_open_charts`
- Exact Lean type: `∀ (n N m : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn m), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ i, IsC1Submanifold n (S i)) → M ⊆ N₀ ∪ ⋃ i, S i → ∃ (D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N), (∀ α, IsOpen (D α)) ∧ (∀ α, ContDiffOn ℝ 1 (ψ α) (D α)) ∧ (∀ α, InjOn (ψ α) (D α)) ∧ (∀ α, ∃ K, LipschitzOnWith K (ψ α) (D α)) ∧ (∀ α, ∀ u ∈ D α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ (∀ α, ∃ K, LipschitzOnWith K (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

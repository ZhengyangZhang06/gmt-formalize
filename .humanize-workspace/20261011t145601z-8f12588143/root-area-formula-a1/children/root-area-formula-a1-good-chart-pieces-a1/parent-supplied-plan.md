# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.area_formula-a1.good_chart_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-area-formula-a1-good-chart-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.area_formula-a1`
- Child key: `good_chart_pieces`
- Declaration: `Submission.areaFormula_good_chart_pieces`
- Exact Lean type: `∀ (n N p : ℕ) (M U N₀ : Set (Rn N)) (S : ℕ → Set (Rn N)) (f : Rn N → Rn p), IsOpen U → M ⊆ U → LocallyLipschitzOn U f → (∀ j, IsC1Submanifold n (S j)) → M ⊆ N₀ ∪ ⋃ j, S j → ∃ (V D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn N) (K C : ℕ → ℝ≥0), (∀ α, IsOpen (V α) ∧ ContDiffOn ℝ 1 (ψ α) (V α) ∧ (∀ u ∈ V α, Function.Injective (fderiv ℝ (ψ α) u)) ∧ IsCompact (D α) ∧ D α ⊆ V α ∧ LipschitzOnWith (K α) (ψ α) (D α) ∧ (∀ u ∈ D α, ∀ v ∈ D α, dist u v ≤ (C α : ℝ) * dist (ψ α u) (ψ α v)) ∧ LipschitzOnWith (K α) (f ∘ ψ α) (D α)) ∧ M ⊆ N₀ ∪ ⋃ α, ψ α '' D α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

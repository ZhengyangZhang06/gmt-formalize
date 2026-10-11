# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.chart_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-chart-pieces-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `chart_pieces`
- Declaration: `Submission.rectifiable_c1_chart_pieces`
- Exact Lean type: `SubmanifoldCoverCharacterization → (∀ (n p : ℕ) (f : Rn n → Rn p) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Rn n → Rn p, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) → ∀ (n ℓ m : ℕ) (M U : Set (Rn (n + ℓ))) (f : Rn (n + ℓ) → Rn m), CountablyRectifiable n M → IsOpen U → M ⊆ U → LocallyLipschitzOn U f → ∃ (D : ℕ → Set (Rn n)) (ψ : ℕ → Rn n → Rn (n + ℓ)) (G : ℕ → Rn n → Rn m) (E : ℕ → Set (Rn n)), (∀ j, IsOpen (D j)) ∧ (∀ j, ContDiffOn ℝ 1 (ψ j) (D j)) ∧ (∀ j, InjOn (ψ j) (D j)) ∧ (∀ j, ∃ K, LipschitzOnWith K (ψ j) (D j)) ∧ (∀ j, ∀ u ∈ D j, Function.Injective (fderiv ℝ (ψ j) u)) ∧ (∀ j, ContDiff ℝ 1 (G j)) ∧ (∀ j, MeasurableSet (E j)) ∧ (∀ j, E j ⊆ D j) ∧ (∀ j, ∀ u ∈ E j, f (ψ j u) = G j u ∧ HasFDerivAt (f ∘ ψ j) (fderiv ℝ (G j) u) u) ∧ μHE[n] (M \ ⋃ j, ψ j '' E j) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

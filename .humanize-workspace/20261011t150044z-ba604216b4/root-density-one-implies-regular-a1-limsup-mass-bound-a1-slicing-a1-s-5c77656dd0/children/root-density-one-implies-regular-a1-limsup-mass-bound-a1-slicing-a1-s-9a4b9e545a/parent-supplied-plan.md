# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-9a4b9e545a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `chart_cover`
- Declaration: `Submission.dor_lmbsf_cp_submanifold_chart_cover`
- Exact Lean type: `∀ (P m : ℕ) (U M N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), IsOpen U → M ⊆ U → (∀ l, IsEmbeddedSubmanifold 1 m (N l)) → M ⊆ N₀ ∪ ⋃ l, N l → ∃ (V : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P), (∀ s, IsOpen (V s) ∧ ContDiffOn ℝ 1 (ψ s) (V s) ∧ InjOn (ψ s) (V s) ∧ (∀ y ∈ V s, Injective (fderiv ℝ (ψ s) y)) ∧ ψ s '' V s ⊆ U) ∧ M ⊆ N₀ ∪ ⋃ s, ψ s '' V s`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.diagonal_blowup-a1.dense_family_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1-dense-family-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child key: `dense_family_tendsto`
- Declaration: `Submission.intcpt_diag_dense_family_tendsto`
- Exact Lean type: `∀ (N n : ℕ) (O : Set (Euclidean N)) (g : ℕ → C_c(Euclidean N × Grassmannian N n, ℝ)) (μ ν : ℕ → Measure (Euclidean N × Grassmannian N n)) (C : ℝ≥0∞), MeasurableSet O → C ≠ ∞ → (∀ m, tsupport (g m) ⊆ O ×ˢ (univ : Set (Grassmannian N n))) → (∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ O ×ˢ (univ : Set (Grassmannian N n)) → ∀ η : ℝ, 0 < η → ∃ m, ∀ z, |f z - g m z| ≤ η) → (∀ᶠ k in atTop, μ k (O ×ˢ (univ : Set (Grassmannian N n))) ≤ C) → (∀ᶠ k in atTop, ν k (O ×ˢ (univ : Set (Grassmannian N n))) ≤ C) → (∀ m, Tendsto (fun k ↦ ∫ z, g m z ∂(μ k) - ∫ z, g m z ∂(ν k)) atTop (𝓝 0)) → ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ O ×ˢ (univ : Set (Grassmannian N n)) → Tendsto (fun k ↦ ∫ z, f z ∂(μ k) - ∫ z, f z ∂(ν k)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

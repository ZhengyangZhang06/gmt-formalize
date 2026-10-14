# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1.uniformize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9899c799b9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1`
- Child key: `uniformize`
- Declaration: `Submission.cbrr_ud_uniformize_eventually`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (F : Set (Euclid P)) (T : ℝ → Set (Euclid P)), MeasurableSet F → μ F ≠ ∞ → (∀ ρ : ℝ, 0 < ρ → IsClosed (T ρ)) → (∀ x ∈ F, ∀ᶠ ρ in 𝓝[>] (0 : ℝ), x ∈ T ρ) → ∀ η : ℝ≥0∞, η ≠ 0 → ∃ (E : Set (Euclid P)) (δ : ℝ), E ⊆ F ∧ 0 < δ ∧ μ (F \ E) < η ∧ ∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → x ∈ T ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

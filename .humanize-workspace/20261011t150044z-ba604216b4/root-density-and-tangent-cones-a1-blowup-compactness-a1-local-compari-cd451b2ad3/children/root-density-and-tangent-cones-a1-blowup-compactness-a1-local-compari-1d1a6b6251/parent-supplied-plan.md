# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1.scale_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-1d1a6b6251/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1`
- Child key: `scale_limit`
- Declaration: `Submission.dtc_bc_lc_sl_eil_limit`
- Exact Lean type: `∀ (P : ℕ) (d : ℝ) (S : ℝ → Set (Euclid P)) (ψ : ℕ → ℝ → ℝ≥0∞) (δ ε : ℕ → ℝ≥0∞) (B : ℝ≥0∞), (∀ k, Measurable (ψ k)) → Tendsto δ atTop (𝓝 0) → Tendsto ε atTop (𝓝 0) → (∀ k t, (⨅ (c : ℕ → Set (Euclid P)) (_ : S t ⊆ ⋃ i, c i) (_ : ∀ i, Metric.ediam (c i) ≤ δ k), ∑' i, ⨆ _ : (c i).Nonempty, Metric.ediam (c i) ^ d) ≤ ψ k t) → (∀ k, ∫⁻ t, ψ k t ≤ B + ε k) → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t, μH[d] (S t) ≤ φ t) ∧ ∫⁻ t, φ t ≤ B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

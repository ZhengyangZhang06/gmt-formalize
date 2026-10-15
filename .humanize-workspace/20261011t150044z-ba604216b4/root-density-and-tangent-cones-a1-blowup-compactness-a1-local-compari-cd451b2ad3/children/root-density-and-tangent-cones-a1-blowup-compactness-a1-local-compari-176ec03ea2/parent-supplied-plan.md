# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1.single_scale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-176ec03ea2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.eilenberg-a1`
- Child key: `single_scale`
- Declaration: `Submission.dtc_bc_lc_sl_eil_scale`
- Exact Lean type: `∀ (P d : ℕ) (A : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (δ ε : ℝ≥0∞), LipschitzWith L f → 0 < δ → 0 < ε → μH[((d + 1 : ℕ) : ℝ)] A ≠ ∞ → ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧ (∀ t : ℝ, (⨅ (c : ℕ → Set (Euclid P)) (_ : A ∩ f ⁻¹' {t} ⊆ ⋃ i, c i) (_ : ∀ i, Metric.ediam (c i) ≤ δ), ∑' i, ⨆ _ : (c i).Nonempty, Metric.ediam (c i) ^ (d : ℝ)) ≤ ψ t) ∧ ∫⁻ t, ψ t ≤ (L : ℝ≥0∞) * (μH[((d + 1 : ℕ) : ℝ)] A + ε)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

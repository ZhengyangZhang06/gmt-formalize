# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1.ae_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-95199f8c16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Child key: `ae_finite`
- Declaration: `Submission.dtc_bc_tc_cl_sl_ae_liminf_lt_top`
- Exact Lean type: `(∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop) → ∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (Z : ℕ → ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ k : ℕ, ⨆ i, μs i (ball (0 : Euclid P) ((k : ℝ) + 1)) < ∞) → (∀ (i k : ℕ) (t : ℝ), Z i k t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs i (ball (0 : Euclid P) ((k : ℝ) + 1) ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∀ᵐ t ∂(volume : Measure ℝ), ∀ k : ℕ, liminf (fun i => Z i k t) atTop < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_has_fderiv_at-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-07cd9b6e07/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Child key: `chart_has_fderiv_at`
- Declaration: `Submission.slicing_im_ll_twl_chart_hasFDerivAt`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (h : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → LipschitzWith L h → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict A), ∀ w ∈ Ω, Φ w = x → ∀ u ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)), HasFDerivAt (h ∘ Φ) ((innerSL ℝ (G (Φ w))).comp (fderiv ℝ Φ w)) w`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1.uniform_limit_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-radial-homogeneity-a1-dilation-mollify-cc-a-7a922443d4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.radial_homogeneity-a1.dilation_mollify_cc-a1`
- Child key: `uniform_limit_integral`
- Declaration: `Submission.varifold_tangents_rh_mc_tendsto_integral_of_uniform`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (K : Set (Euclidean N)) (F : ℕ → Euclidean N → ℝ) (G : Euclidean N → ℝ), IsFiniteMeasureOnCompacts μ → IsCompact K → (∀ k, Integrable (F k) μ) → Integrable G μ → (∀ k, ∀ y ∉ K, F k y = G y) → (∀ ε > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ y, |F k y - G y| ≤ ε) → Tendsto (fun k => ∫ y, F k y ∂μ) atTop (𝓝 (∫ y, G y ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-37749b6fd4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1`
- Child key: `smooth_tendsto`
- Declaration: `Submission.slicing_im_ll_gws_smooth_tendsto`
- Exact Lean type: `∀ (n : ℕ) (Ω : Set (Eucl n)) (C : ℝ≥0) (u : Eucl n → ℝ) (ug : ℕ → Eucl n → ℝ), IsOpen Ω → LipschitzOnWith C u Ω → (∀ k, LipschitzOnWith C (ug k) Ω) → TendstoUniformlyOn ug u atTop Ω → ∀ b : Eucl n → Eucl n, ContDiff ℝ 1 b → HasCompactSupport b → tsupport b ⊆ Ω → Tendsto (fun k => ∫ w in Ω, fderiv ℝ (ug k) w (b w)) atTop (𝓝 (∫ w in Ω, fderiv ℝ u w (b w)))`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.lipschitz_ibp-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

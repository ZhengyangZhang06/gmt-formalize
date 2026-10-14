# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_mass_bounds-a1.continuous_form_conv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-continuous-form-conv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_mass_bounds-a1`
- Child key: `continuous_form_conv`
- Declaration: `Submission.cmb_tendsto_integral_of_weaklyConvergesOn`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (S : ℕ → GeometricCurrentOn U n) (S₀ : GeometricCurrentOn U n), (∀ W, CompactlyContainedOpen W U → (⨆ q, (S q).massOn W) < ∞) → WeaklyConvergesOn S S₀ → ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U → ∀ (μ : ℕ → Measure (Eucl P)) (v : ℕ → Eucl P → NVector (Eucl P) n) (μ₀ : Measure (Eucl P)) (v₀ : Eucl P → NVector (Eucl P) n), (∀ q, IsMeasureRepresentation (S q) (μ q) (v q)) → IsMeasureRepresentation S₀ μ₀ v₀ → Tendsto (fun q => ∫ x, v q x (ω x) ∂(μ q)) atTop (𝓝 (∫ x, v₀ x (ω x) ∂μ₀))`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mollify-a1`
- `root.compactness_mass_bounds-a1.repr_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

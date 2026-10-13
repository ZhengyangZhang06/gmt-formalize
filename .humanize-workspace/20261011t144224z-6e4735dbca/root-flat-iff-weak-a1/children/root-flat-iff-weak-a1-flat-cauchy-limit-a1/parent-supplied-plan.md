# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.flat_cauchy_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-flat-cauchy-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1`
- Child key: `flat_cauchy_limit`
- Declaration: `Submission.fiw_flat_cauchy_limit`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U n) (T : GeometricCurrentOn U n), (∀ ε : ℝ≥0∞, 0 < ε → ∀ J : Set ℕ, J.Infinite → ∃ J' ⊆ J, J'.Infinite ∧ ∀ i ∈ J', ∀ j ∈ J', ∃ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω, Tj i ω - Tj j ω = R.boundary ω + S ω) ∧ R.mass + S.mass < ε) → WeaklyConvergesOn Tj T → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ℓ : ℕ, ∃ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω, Tj (φ ℓ) ω - T ω = R.boundary ω + S ω) ∧ R.mass + S.mass ≤ 2 * 2⁻¹ ^ ℓ`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

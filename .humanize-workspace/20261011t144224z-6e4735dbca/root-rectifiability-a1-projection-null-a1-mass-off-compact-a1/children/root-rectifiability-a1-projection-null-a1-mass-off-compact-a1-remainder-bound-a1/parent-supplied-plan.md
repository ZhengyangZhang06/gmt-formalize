# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.remainder_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-remainder-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`
- Child key: `remainder_bound`
- Declaration: `Submission.rpn_moc_abs_apply_le_mul_measure_diff`
- Exact Lean type: `∀ (P n : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U n) (μ : Measure (Eucl P)) (ξ : Eucl P → NVector (Eucl P) n), IsMeasureRepresentation T μ ξ → IsOpen W → IsCompact K → μ (W \ K) ≠ ∞ → ∀ (θ : Covector (Eucl P) n) (h : Eucl P → ℝ) (c c' : ℝ), (∀ x, |h x| ≤ c) → (∀ x, x ∉ W → h x = 0) → (∀ x ∈ K, h x = 0) → (∀ᵐ x ∂μ, |ξ x θ| ≤ c') → ∀ φ : TestFormOn U n, (∀ x, (φ : DifferentialForm (Eucl P) n) x = h x • θ) → |T φ| ≤ c * c' * (μ (W \ K)).toReal`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

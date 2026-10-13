# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.top_form_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-top-for-a0faf9bbe3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`
- Child key: `top_form_estimate`
- Declaration: `Submission.rpn_moc_abs_apply_top_form_le`
- Exact Lean type: `∀ (P m : ℕ) (U W K : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P)) (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ ξ → IsOpen W → W ⊆ U → IsCompact K → μ (W \ K) ≠ ∞ → ∀ (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ) (c c' : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W → (∀ x, |f x| ≤ c) → (∀ᵐ x ∂μ, |ξ x (wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L))| ≤ c') → (∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1), (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) • wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) → |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))) → (∀ δ : ℝ, 0 < δ → ∃ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ L '' K, b y = 1) ∧ ((volume : Measure (Eucl (m + 1))) (tsupport b)).toReal ≤ δ) → ∀ ζ : TestFormOn U (m + 1), (∀ x, (ζ : DifferentialForm (Eucl P) (m + 1)) x = f x • wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) → |T ζ| ≤ c * c' * (μ (W \ K)).toReal`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.scalar_test_form-a1`
- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.remainder_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

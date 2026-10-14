# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.im_combine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-im-combine-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1`
- Child key: `im_combine`
- Declaration: `Submission.fiw_ims_combine`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[n] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M₁, 0 < θ₁ x) → (∀ x ∈ M₂, 0 < θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[n] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x Q) → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ), (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) → (∀ r, ∀ x ∈ M r, ∃ k : ℕ, θ r x = k) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) → ∃ (M' : Set (Eucl P)) (θ' : Eucl P → ℝ) (ξ' : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M' θ' ξ' ∧ (∀ x ∈ M', ∃ k : ℕ, θ' x = k) ∧ ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω) (tauAction n M' θ' ξ' ω)`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.orientation_sign-a1`
- `root.flat_iff_weak-a1.im_series-a1.overlap_finite-a1`
- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

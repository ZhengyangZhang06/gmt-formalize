# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.overlap_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-overlap-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1`
- Child key: `overlap_finite`
- Declaration: `Submission.fiw_ims_overlap_finite`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (c : ℕ → ℤ), (∀ r, M r ⊆ U) → (∀ r, NullMeasurableSet (M r) (μHE[n] : Measure (Eucl P))) → (∀ r, ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn (θ r) (M r ∩ K) (μHE[n] : Measure (Eucl P))) → (∀ r, ∀ x ∈ M r, 1 ≤ θ r x) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (∫⁻ x in K, ∑' r, ((c r).natAbs : ℝ≥0∞) * (M r).indicator (fun y => ENNReal.ofReal (θ r y)) x ∂(μHE[n] : Measure (Eucl P))) < ∞) ∧ ∀ᵐ x ∂(μHE[n] : Measure (Eucl P)), {r | c r ≠ 0 ∧ x ∈ M r}.Finite`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1`
- Child key: `tsum_tau`
- Declaration: `Submission.fiw_ims_tsum_tau`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (M : ℕ → Set (Eucl P)) (θ : ℕ → Eucl P → ℝ) (ξ : ℕ → Eucl P → NVector (Eucl P) n) (c : ℕ → ℤ), (∀ r, IsRectifiableTriple U n (M r) (θ r) (ξ r)) → (∀ W, CompactlyContainedOpen W U → (∑' r, ((c r).natAbs : ℝ≥0∞) * ∫⁻ x in M r ∩ W, ENNReal.ofReal (θ r x) ∂(μHE[n] : Measure (Eucl P))) < ∞) → ∀ ω : TestFormOn U n, HasSum (fun r => (c r : ℝ) * tauAction n (M r) (θ r) (ξ r) ω) (∫ x, ∑' r, (M r).indicator (fun y => (c r : ℝ) * (θ r y * ξ r y ((ω : DifferentialForm (Eucl P) n) y))) x ∂(μHE[n] : Measure (Eucl P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

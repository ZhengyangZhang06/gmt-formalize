# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.term_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-term-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`
- Child key: `term_bound`
- Declaration: `Submission.fiw_ims_tt_term_bound`
- Exact Lean type: `∀ (P n : ℕ) (U W M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (ω : Eucl P → Covector (Eucl P) n) (B : ℝ), IsRectifiableTriple U n M θ ξ → CompactlyContainedOpen W U → Continuous ω → tsupport ω ⊆ W → (∀ x, ‖ω x‖ ≤ B) → AEStronglyMeasurable (M.indicator fun x => θ x * ξ x (ω x)) (μHE[n] : Measure (Eucl P)) ∧ ∫⁻ x, ‖M.indicator (fun y => θ y * ξ y (ω y)) x‖ₑ ∂(μHE[n] : Measure (Eucl P)) ≤ ENNReal.ofReal B * ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

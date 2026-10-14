# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.int_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-74f5e736d3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `int_density`
- Declaration: `Submission.dtc_bc_lc_pfi_integer_density_of_summable`
- Exact Lean type: `∀ (P n : ℕ) (f : ℕ → Euclid P → ℤ), (∀ j, Measurable (f j)) → ∑' j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → ∃ m : Euclid P → ℝ, Measurable m ∧ (∀ y, ∃ z : ℤ, m y = z) ∧ (∀ y, ENNReal.ofReal |m y| ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞)) ∧ ∀ᵐ y ∂μHE[n], Summable (fun j => (f j y : ℝ)) ∧ m y = ∑' j, (f j y : ℝ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

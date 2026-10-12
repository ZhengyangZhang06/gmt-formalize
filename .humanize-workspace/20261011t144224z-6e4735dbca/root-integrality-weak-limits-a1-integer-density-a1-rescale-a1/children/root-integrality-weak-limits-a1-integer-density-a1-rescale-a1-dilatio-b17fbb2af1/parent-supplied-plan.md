# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.dilation_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-dilatio-b17fbb2af1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`
- Child key: `dilation_measure`
- Declaration: `Submission.ind_rs_dilation_measurePreserving`
- Exact Lean type: `∀ (P n : ℕ) (x : Eucl P) (r : ℝ), 0 < r → MeasurableEmbedding (fun y : Eucl P => r⁻¹ • (y - x)) ∧ MeasurePreserving (fun y : Eucl P => r⁻¹ • (y - x)) (ENNReal.ofReal ((r ^ n)⁻¹) • (μHE[n] : Measure (Eucl P))) (μHE[n] : Measure (Eucl P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

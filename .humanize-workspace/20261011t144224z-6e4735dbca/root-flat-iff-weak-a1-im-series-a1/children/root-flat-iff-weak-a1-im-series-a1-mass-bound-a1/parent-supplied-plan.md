# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1`
- Child key: `mass_bound`
- Declaration: `Submission.fiw_ims_mass_bound`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (X : GeometricCurrentOn U k) (V : Set (Eucl P)) (η : TestFormOn U k) (C : ℝ), 0 < C → tsupport (η : DifferentialForm (Eucl P) k) ⊆ V → (∀ x, covectorEuclideanNorm ((η : DifferentialForm (Eucl P) k) x) ≤ C) → ENNReal.ofReal |X η| ≤ X.massOn V * ENNReal.ofReal C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.mass_restriction-a1.mass_measure_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1-mass-measure-facts-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.mass_restriction-a1`
- Child key: `mass_measure_facts`
- Declaration: `Submission.dmr_massMeasure_support_finite`
- Exact Lean type: `∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)), IsMassMeasure X μ → μ X.supportᶜ = 0 ∧ (X.mass < ∞ → IsFiniteMeasure μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

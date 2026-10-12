# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.globalize-a1.unit_top_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-globalize-a1-unit-top-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.globalize-a1`
- Child key: `unit_top_form`
- Declaration: `Submission.constancy_exists_topTestForm_integral_eq_one`
- Exact Lean type: `∀ (m : ℕ) (U W : Set (Eucl (m + 1))), IsOpen W → W.Nonempty → W ⊆ U → ∃ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) ⊆ W ∧ ∫ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume = 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

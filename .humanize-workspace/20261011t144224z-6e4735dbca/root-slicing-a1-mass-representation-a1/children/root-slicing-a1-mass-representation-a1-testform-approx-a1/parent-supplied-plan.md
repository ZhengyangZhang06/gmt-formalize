# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.testform_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-testform-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1`
- Child key: `testform_approx`
- Declaration: `Submission.smr_exists_testForm_uniform_approx`
- Exact Lean type: `∀ (P k : ℕ) (U V : Set (Eucl P)) (φ : Eucl P → Covector (Eucl P) k), IsOpen V → V ⊆ U → Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V → ∀ ε : ℝ, 0 < ε → ∃ η : TestFormOn U k, tsupport (η : DifferentialForm (Eucl P) k) ⊆ V ∧ ∀ x, covectorEuclideanNorm (φ x - (η : DifferentialForm (Eucl P) k) x) ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

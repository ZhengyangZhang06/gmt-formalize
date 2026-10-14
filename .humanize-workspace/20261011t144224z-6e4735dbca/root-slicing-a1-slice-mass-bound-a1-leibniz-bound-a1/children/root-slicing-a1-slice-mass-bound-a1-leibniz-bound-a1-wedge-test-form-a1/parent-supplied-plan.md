# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.wedge_test_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-wedge-test-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`
- Child key: `wedge_test_form`
- Declaration: `Submission.slicing_mb_lb_wedge_testForm`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U m) (α : Eucl P → (Eucl P →L[ℝ] ℝ)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α → ∃ η : TestFormOn U (m + 1), ∀ x, (η : DifferentialForm (Eucl P) (m + 1)) x = ContinuousAlternatingMap.alternatizeUncurryFin ((α x).smulRight ((ω : DifferentialForm (Eucl P) m) x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

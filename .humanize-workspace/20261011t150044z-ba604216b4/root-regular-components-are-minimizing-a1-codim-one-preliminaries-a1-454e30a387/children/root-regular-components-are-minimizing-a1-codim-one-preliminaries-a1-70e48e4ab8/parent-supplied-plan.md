# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.isolated_point_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-codim-one-preliminaries-a1-70e48e4ab8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Child key: `isolated_point_integral`
- Declaration: `Submission.regcomp_cop_zdr_setIntegral_eq_indicator`
- Exact Lean type: `∀ (P : ℕ) (C K : Set (Euclid P)) (x : Euclid P) (F : Euclid P → ℝ), MeasurableSet K → (∀ z, z ∉ K → F z = 0) → C ∩ K ⊆ {x} → ∫ z in C, F z ∂μHE[0] = C.indicator F x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

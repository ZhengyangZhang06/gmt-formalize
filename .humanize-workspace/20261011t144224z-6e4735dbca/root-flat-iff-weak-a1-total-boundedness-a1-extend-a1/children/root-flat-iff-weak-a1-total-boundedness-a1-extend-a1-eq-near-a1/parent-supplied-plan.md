# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.eq_near-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-eq-near-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child key: `eq_near`
- Declaration: `Submission.fiw_tb_ext_apply_eq_of_eqOn`
- Exact Lean type: `∀ (P q : ℕ) (V K N : Set (Eucl P)) (Z : GeometricCurrentOn V q), IsOpen N → K ⊆ N → (∀ ω : TestFormOn V q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → ∀ ω η : TestFormOn V q, (∀ x ∈ N, (η : DifferentialForm (Eucl P) q) x = (ω : DifferentialForm (Eucl P) q) x) → Z η = Z ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

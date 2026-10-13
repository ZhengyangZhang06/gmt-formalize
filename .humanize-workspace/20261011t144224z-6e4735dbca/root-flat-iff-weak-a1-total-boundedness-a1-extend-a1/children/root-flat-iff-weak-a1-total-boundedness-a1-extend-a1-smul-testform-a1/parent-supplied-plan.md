# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-smul-testform-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child key: `smul_testform`
- Declaration: `Submission.fiw_tb_ext_smul_testForm`
- Exact Lean type: `∀ (P q : ℕ) (V W : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ W → ∃ L : TestFormOn V q →ₗ[ℝ] TestFormOn W q, ∀ (ω : TestFormOn V q) (x : Eucl P), (L ω : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

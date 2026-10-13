# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-cutoff-current-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child key: `cutoff_current`
- Declaration: `Submission.fiw_tb_ext_cutoff_current`
- Exact Lean type: `∀ (P q : ℕ) (U : Set (Eucl P)) (χ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → tsupport χ ⊆ U → (∀ x, |χ x| ≤ 1) → ∀ X : GeometricCurrentOn U q, X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) q, ∀ (ω : TestFormOn (univ : Set (Eucl P)) q) (η : TestFormOn U q), (∀ x, (η : DifferentialForm (Eucl P) q) x = χ x • (ω : DifferentialForm (Eucl P) q) x) → Y ω = X η`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.norm_smul-a1`
- `root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1`
- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.converges_small-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

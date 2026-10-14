# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.mass_le_restrict-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-mass-le-restrict-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Child key: `mass_le_restrict`
- Declaration: `Submission.fiw_tb_ext_mass_le_restrictDomain`
- Exact Lean type: `∀ (P q : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ Z : GeometricCurrentOn (univ : Set (Eucl P)) q, (∀ ω : TestFormOn (univ : Set (Eucl P)) q, Disjoint (tsupport (ω : DifferentialForm (Eucl P) q)) K → Z ω = 0) → Z.mass ≤ (Z.restrictDomain (subset_univ U)).mass`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.eq_near-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.norm_smul-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

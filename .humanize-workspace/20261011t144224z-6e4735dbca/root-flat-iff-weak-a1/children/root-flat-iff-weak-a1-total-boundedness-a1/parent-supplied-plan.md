# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1`
- Child key: `total_boundedness`
- Declaration: `Submission.fiw_total_boundedness`
- Exact Lean type: `DeformationTheorem → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P)), IsCompact K → K ⊆ U → ∀ (B : ℝ≥0∞), B ≠ ∞ → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, IsIntegerMultiplicity (Tj j).boundary) → (∀ j, (Tj j).support ⊆ K) → (∀ j, (Tj j).mass + (Tj j).boundary.mass ≤ B) → ∀ ε : ℝ≥0∞, 0 < ε → ∀ J : Set ℕ, J.Infinite → ∃ J' ⊆ J, J'.Infinite ∧ ∀ i ∈ J', ∀ j ∈ J', ∃ (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ (∀ ω, Tj i ω - Tj j ω = R.boundary ω + S ω) ∧ R.mass + S.mass < ε`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_lincomb-a1`
- `root.flat_iff_weak-a1.im_mass_formula-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.extend-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `extend`
- Declaration: `Submission.fiw_tb_extend_to_univ`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P m : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ X : GeometricCurrentOn U (m + 1), X.support ⊆ K → X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (IsIntegerMultiplicity X.boundary → IsIntegerMultiplicity Y.boundary)`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.vanish_off_support-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.support_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

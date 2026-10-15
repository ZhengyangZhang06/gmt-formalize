# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.cauchy_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-flat-convergenc-2638604134/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1`
- Child key: `cauchy_subseq`
- Declaration: `Submission.dimred_mbl_fc_cauchy_subseq`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) → ∀ (P m : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U (m + 1)), IsOpen U → (∀ η : ℝ≥0∞, 0 < η → ∃ 𝒬 : Set (GeometricCurrentOn U (m + 1)), 𝒬.Finite ∧ ∀ j, ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X j - Q - S = R.boundary ∧ R.mass + S.mass ≤ η) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, ∃ (R : GeometricCurrentOn U (m + 2)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧ X (φ (r + 1)) - X (φ r) - S = R.boundary ∧ R.mass + S.mass ≤ (2⁻¹ : ℝ≥0∞) ^ r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1`
- Child key: `localization`
- Declaration: `Submission.br_local_finite_mass_extension`
- Exact Lean type: `SlicingTheorem → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) → ∀ x₀ ∈ U, ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∃ X : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), IsIntegerMultiplicity X ∧ X.mass < ∞ ∧ X.boundary.mass < ∞ ∧ ∀ η : TestFormOn U (m + 1), tsupport (η : DifferentialForm (Eucl P) (m + 1)) ⊆ ball x₀ r → X (testFormOnInclusion (subset_univ U) (m + 1) η) = T η`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

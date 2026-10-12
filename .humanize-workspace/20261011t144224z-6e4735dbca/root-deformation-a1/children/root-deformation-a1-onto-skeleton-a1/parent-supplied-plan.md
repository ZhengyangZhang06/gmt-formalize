# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `onto_skeleton`
- Declaration: `Submission.deformation_onto_skeleton`
- Exact Lean type: `SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), T.mass + T.boundary.mass < ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)) (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2)) (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), (∀ ω, T ω - Q ω = R.boundary ω + S ω) ∧ Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F ∧ (∀ (F : LatticeFaceIndex (m + 1) (m + 1 + ℓ)) (y : Eucl (m + 1 + ℓ)) (r : ℝ), ball y r ∩ (⋃ G : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 G) ⊆ latticeFace 1 F → ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) ⊆ ball y r → (∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0) → Q ω = 0) ∧ Q.mass ≤ C * T.mass ∧ Q.boundary.mass ≤ C * T.boundary.mass ∧ R.mass ≤ C * T.mass ∧ S.mass ≤ C * T.boundary.mass ∧ Q.support ∪ R.support ⊆ cthickening (Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ)) T.support ∧ Q.boundary.support ∪ S.support ⊆ cthickening (Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ)) T.boundary.support ∧ (IsIntegerMultiplicity T → IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R) ∧ (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)`

## Sibling prerequisites

- `root.deformation-a1.retraction-a1`
- `root.deformation-a1.good_center-a1`
- `root.deformation-a1.mass_restriction-a1`
- `root.deformation-a1.im_completeness-a1`
- `root.deformation-a1.im_pushforward_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

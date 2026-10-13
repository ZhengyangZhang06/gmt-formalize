# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.skeleton_polyhedral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-skeleton-polyhedral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `skeleton_polyhedral`
- Declaration: `Submission.deformation_skeleton_polyhedral`
- Exact Lean type: `∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ Q : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), Q.mass + Q.boundary.mass < ∞ → Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F → (∀ (F : LatticeFaceIndex (m + 1) (m + 1 + ℓ)) (y : Eucl (m + 1 + ℓ)) (r : ℝ), ball y r ∩ (⋃ G : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 G) ⊆ latticeFace 1 F → ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) ⊆ ball y r → (∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0) → Q ω = 0) → ∃ (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ) (P S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), IsLatticeChain 1 β P ∧ (∀ ω, Q ω - P ω = S ω) ∧ P.mass ≤ C * Q.mass ∧ P.boundary.mass ≤ C * Q.boundary.mass ∧ S.mass ≤ C * Q.boundary.mass ∧ P.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.support ∧ P.boundary.support ∪ S.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.boundary.support ∧ (IsIntegerMultiplicity Q → (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity P)`

## Sibling prerequisites

- `root.deformation-a1.mass_restriction-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

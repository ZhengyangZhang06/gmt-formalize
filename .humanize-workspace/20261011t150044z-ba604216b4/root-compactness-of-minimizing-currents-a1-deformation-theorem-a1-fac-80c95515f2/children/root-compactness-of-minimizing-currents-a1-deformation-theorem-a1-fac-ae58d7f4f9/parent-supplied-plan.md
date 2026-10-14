# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.coordinate_plane_orientation_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-ae58d7f4f9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Child key: `coordinate_plane_orientation_sign`
- Declaration: `Submission.cmcdtfrsd_coordinate_plane_orientation_sign`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

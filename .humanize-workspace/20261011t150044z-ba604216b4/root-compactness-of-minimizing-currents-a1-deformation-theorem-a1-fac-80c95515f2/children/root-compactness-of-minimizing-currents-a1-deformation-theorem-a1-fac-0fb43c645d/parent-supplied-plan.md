# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.face_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-0fb43c645d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Child key: `face_density`
- Declaration: `Submission.cmcdtfrsd_face_density`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.coordinate_plane_orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1.orientation_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-836d202eb4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Child key: `orientation_sign`
- Declaration: `Submission.cmcdt_lpi_pr_orientation_sign`
- Exact Lean type: `∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (ζ : Euclid n → MultiVector N n), MeasurableSet A → (∀ u ∈ A, Injective (fderiv ℝ G u)) → AEStronglyMeasurable ζ (volume.restrict A) → (∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ζ u) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))))) → ∃ s : Euclid n → ℤ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict A), ∀ α : Covector (Euclid N) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1)))) * ζ u α = (s u : ℝ) * α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

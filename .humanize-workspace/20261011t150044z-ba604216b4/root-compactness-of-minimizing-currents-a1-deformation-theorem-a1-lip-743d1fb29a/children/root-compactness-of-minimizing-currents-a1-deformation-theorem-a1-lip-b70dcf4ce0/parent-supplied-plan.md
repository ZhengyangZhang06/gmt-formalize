# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.piece_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-b70dcf4ce0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Child key: `piece_orientation`
- Declaration: `Submission.cmcdt_lpi_pc_piece_orientation`
- Exact Lean type: `∀ (P n : ℕ) (L : NNReal) (κ : ℝ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), LipschitzWith L H → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧ (∀ u ∈ B, IsUnitOrientationOf (η (H u)) (LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)) ∧ ∀ α : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a 1)) (fderiv ℝ H u (EuclideanSpace.single b 1)))) * η (H u) α = α (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) ∧ ∀ᵐ y ∂(μHE[n].restrict (H '' B)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (H '' B) y Q ∧ IsUnitOrientationOf (η y) Q`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.measurable_inverse-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

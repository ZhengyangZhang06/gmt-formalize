# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1.piece_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-5d9982b5d0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Child key: `piece_orientation`
- Declaration: `Submission.cmcdt_lpi_pr_piece_orientation_ae`
- Exact Lean type: `(∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (N n : ℕ) (M : Set (Euclid N)) (ξ : Euclid N → MultiVector N n) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), MeasurableSet M → (∀ K : Set (Euclid N), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → AEStronglyMeasurable ξ (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid N), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ξ x) Q) → LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ M → AEStronglyMeasurable (fun u => ξ (G u)) (volume.restrict A) ∧ ∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ξ (G u)) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_pullback-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

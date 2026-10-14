# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.single_piece_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-41f7d7ef42/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Child key: `single_piece_current`
- Declaration: `Submission.cmcdt_lpi_pc_piece_current`
- Exact Lean type: `(∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → ∀ (P n : ℕ) (L : NNReal) (κ : ℝ) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → IntegrableOn (fun u => (g u : ℝ)) B → (∀ u ∈ B, g u ≠ 0) → ∃ Φ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity Φ ∧ Φ.mass ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, Φ ω = ∫ u in B, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.measurable_inverse-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.piece_multiplicity-a1`
- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.piece_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

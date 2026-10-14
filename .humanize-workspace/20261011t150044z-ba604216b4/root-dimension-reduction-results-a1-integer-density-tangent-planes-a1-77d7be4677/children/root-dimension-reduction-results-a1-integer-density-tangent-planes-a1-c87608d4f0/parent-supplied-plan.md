# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.signed_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c87608d4f0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `signed_density`
- Declaration: `Submission.idtp_pc_signed_density`
- Exact Lean type: `∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P), IsOpen V → Orthonormal ℝ τ → IsIntegerMultiplicity S → S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → ∃ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) ∧ (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) ∧ (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → S.massOn W = ∫⁻ x in W ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.planar_orientation_sign-a1`
- `root.dimension_reduction_results-a1.im_mass_measure-a1`
- `root.minimizing_implies_stationary-a1.support_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

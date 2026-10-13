# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1.oriented_mass_lower-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-74933f09f6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- Child key: `oriented_mass_lower`
- Declaration: `Submission.codim1_oriented_rep_lintegral_le_massOn`
- Exact Lean type: `∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), V ⊆ U → Measurable θ' → (∀ x, 0 ≤ θ' x) → AEStronglyMeasurable ξ' (μHE[k].restrict M') → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≠ ∞ → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≤ T.massOn W`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.lusin_covector-a1`
- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

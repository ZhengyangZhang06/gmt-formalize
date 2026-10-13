# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child key: `area_comparison`
- Declaration: `Submission.codim1_minimizing_piece_area_comparison`
- Exact Lean type: `∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (V M : Set (Euclid P)) (ξ : Euclid P → MultiVector P m), 1 ≤ m → IsMinimizingIn C univ → BoundaryVanishes C → IsOpen V → M ⊆ V → IsEmbeddedSubmanifold 1 m M → IsOrientation m M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → μHE[m] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ V → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → (∀ W : Set (Euclid P), IsOpen W → W ⊆ V → μHE[m] (M ∩ W) ≠ ∞ → μHE[m] (M ∩ W) ≤ C.massOn W) → ∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ V → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ μHE[m] ((fun x => x + t • Z x) '' (M ∩ tsupport Z))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.unit_orientation_duality-a1`
- `root.minimizing_implies_stationary-a1.chart_tangent_space-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

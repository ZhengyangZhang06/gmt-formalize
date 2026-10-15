# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.planar_support_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-15cbdbde67/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child key: `planar_support_mass`
- Declaration: `Submission.idtp_ccd_planar_support_mass`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (Q : Submodule ℝ (Euclid P)) (p : Euclid P) (r : ℝ) (k : ℕ), 1 ≤ n → IsOpen U → IsIntegerMultiplicity T → BoundaryVanishes T → Module.finrank ℝ Q = n → p ∈ Q → 0 < r → ball p r ⊆ U → T.support ∩ ball p r ⊆ (Q : Set (Euclid P)) → HasMassDensity T p k → ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball p r → T.massOn W = (k : ℝ≥0∞) * μHE[n] (W ∩ (Q : Set (Euclid P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

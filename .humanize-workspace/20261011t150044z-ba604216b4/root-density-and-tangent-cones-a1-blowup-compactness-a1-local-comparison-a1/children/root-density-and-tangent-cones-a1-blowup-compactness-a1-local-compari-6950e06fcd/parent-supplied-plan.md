# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.retraction_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6950e06fcd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child key: `retraction_comparison`
- Declaration: `Submission.dtc_bc_lc_retraction_comparison`
- Exact Lean type: `∀ (P m : ℕ) (U A : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (π : Euclid P → Euclid P) (G L : ℝ), IsOpen U → IsMinimizingIn S A → S.support ⊆ A → 0 < G → closedBall (0 : Euclid P) G ⊆ U → 0 ≤ L → ContDiffOn ℝ 1 π (ball 0 (2 * G)) → MapsTo π (ball 0 (2 * G)) A → (∀ y ∈ A ∩ ball 0 (2 * G), π y = y) → (∀ y ∈ ball 0 (2 * G), ‖π y‖ ≤ 2 * ‖y‖) → (∀ y ∈ ball 0 (2 * G), ∀ z ∈ ball 0 (2 * G), ‖π y - π z‖ ≤ L * ‖y - z‖) → IsIntegerMultiplicity Y → Y.boundary = 0 → IsCompact Y.support → Y.support ⊆ ball 0 (G / 2) → S.massOn (ball 0 G) ≤ ENNReal.ofReal (L ^ (m + 1)) * (S - (0 - Y.restrictDomain (subset_univ U))).massOn (ball 0 G)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.orientation_fixed-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.measure_subadditive-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.cone_exclusion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-7d2d7402f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child key: `cone_exclusion`
- Declaration: `Submission.codim1_rdo_dg_rc_cone_exclusion`
- Exact Lean type: `∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (K : Set (Euclid (m + 1))) (δ ε : ℝ), (∀ y, ‖ν y‖ = 1) → 0 ≤ ε → (1 + 16 ^ m) * ε < 1 → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) → ∀ x ∈ K, ∀ x' ∈ K, ∀ v : Euclid (m + 1), ‖ν x - v‖ ≤ 1 / 16 → ‖x' - x‖ < δ / 2 → |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

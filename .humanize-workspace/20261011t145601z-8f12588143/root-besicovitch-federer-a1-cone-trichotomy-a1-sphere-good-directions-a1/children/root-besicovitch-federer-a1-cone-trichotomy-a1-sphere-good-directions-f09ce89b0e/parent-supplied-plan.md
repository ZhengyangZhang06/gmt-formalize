# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1.double_cone_outer_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-sphere-good-directions-f09ce89b0e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`
- Child key: `double_cone_outer_measure`
- Declaration: `Submission.bf_sphereGood_doubleCone_outerMeasure`
- Exact Lean type: `∀ (N n : ℕ) (H : Submodule ℝ (Rn N)) (A : Set (Rn N)) (δ : ℝ), 0 < δ → ∀ a : Rn N, ∃ m : OuterMeasure (Rn N), m {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0} = 0 ∧ ∀ θ ∈ H, ‖θ‖ = 1 → ((∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) ∧ ((∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ ENNReal.ofReal (K * t ^ n) < m ({ζ | ζ ∈ H ∧ ‖ζ‖ = 1} ∩ Metric.ball θ t)) → ∀ K : ℝ, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ ∃ r : ℝ, 0 < r ∧ r < δ ∧ ENNReal.ofReal (K * (r * s) ^ n) ≤ μHE[n] (A ∩ ({x | ‖H.starProjection (x - a) - inner ℝ (H.starProjection (x - a)) θ • θ‖ < s * ‖H.starProjection (x - a)‖} ∩ Metric.ball a r)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

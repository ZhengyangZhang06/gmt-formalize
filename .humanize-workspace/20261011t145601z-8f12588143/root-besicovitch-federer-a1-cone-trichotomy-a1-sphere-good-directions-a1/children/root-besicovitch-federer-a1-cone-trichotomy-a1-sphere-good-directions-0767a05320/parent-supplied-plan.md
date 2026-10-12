# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1.density_dichotomy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-sphere-good-directions-0767a05320/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`
- Child key: `density_dichotomy`
- Declaration: `Submission.bf_sphereGood_densityDichotomy`
- Exact Lean type: `∀ (N n : ℕ) (σ : Measure (Rn N)), IsFiniteMeasure σ → ∀ (S : Set (Rn N)) (c₁ C₁ : ℝ), 0 < c₁ → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 2 → ENNReal.ofReal (c₁ * ρ ^ n) ≤ σ (Metric.ball ζ ρ)) → (∀ ζ ∈ S, ∀ ρ : ℝ, 0 < ρ → σ (Metric.ball ζ ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ n)) → ∀ (m : OuterMeasure (Rn N)) (F : Set (Rn N)), MeasurableSet F → F ⊆ S → m F = 0 → σ {θ | θ ∈ F ∧ ¬ (∀ c : ℝ, 0 < c → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → m (S ∩ Metric.ball θ t) ≤ ENNReal.ofReal (c * t ^ n)) ∧ ¬ (∀ K : ℝ, ∀ η : ℝ, 0 < η → ∃ t : ℝ, 0 < t ∧ t < η ∧ ENNReal.ofReal (K * t ^ n) < m (S ∩ Metric.ball θ t))} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

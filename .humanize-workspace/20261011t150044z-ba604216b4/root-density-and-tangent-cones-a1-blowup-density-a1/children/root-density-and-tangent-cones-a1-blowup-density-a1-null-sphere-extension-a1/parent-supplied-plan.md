# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_density-a1.null_sphere_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-density-a1-null-sphere-extension-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_density-a1`
- Child key: `null_sphere_extension`
- Declaration: `Submission.dtc_measure_ball_eq_of_null_sphere`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (c : ℝ≥0∞), c ≠ ∞ → (∀ r : ℝ, 0 < r → μ (ball 0 r) ≠ ∞) → (∀ ρ : ℝ, 0 < ρ → μ (sphere 0 ρ) = 0 → μ (ball 0 ρ) = c * ENNReal.ofReal (ρ ^ n)) → ∀ ρ : ℝ, 0 < ρ → μ (ball 0 ρ) = c * ENNReal.ofReal (ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

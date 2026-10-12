# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.deformation_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-deformation-regularity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1`
- Child key: `deformation_regularity`
- Declaration: `Submission.deformation_velocity_acceleration_regularity`
- Exact Lean type: `(∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsAdmissibleDeformation 2 U K φ → ContDiff ℝ 1 (initialVelocity φ) ∧ ∀ x ∉ K, initialVelocity φ x = 0) ∧ ∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), IsAdmissibleDeformation 3 U K φ → ContDiff ℝ 2 (initialVelocity φ) ∧ ContDiff ℝ 1 (initialAcceleration φ) ∧ ∀ x ∉ K, initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

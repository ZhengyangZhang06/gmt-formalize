# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1.axis_free_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-sphere-good-directions-f0f649fa00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_good_directions-a1`
- Child key: `axis_free_measurable`
- Declaration: `Submission.bf_sphereGood_axisFree_measurableSet`
- Exact Lean type: `∀ (N : ℕ) (H : Submodule ℝ (Rn N)) (A : Set (Rn N)), IsCompact A → ∀ (δ : ℝ) (a : Rn N), MeasurableSet {θ : Rn N | θ ∈ H ∧ ‖θ‖ = 1 ∧ ¬ ∃ b ∈ A, b ≠ a ∧ dist b a < δ ∧ H.starProjection (b - a) - inner ℝ (H.starProjection (b - a)) θ • θ = 0}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1.lipschitz_near_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-retract-a333c9ec7d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_retraction-a1`
- Child key: `lipschitz_near_point`
- Declaration: `Submission.dtc_bc_lr_lipschitz_near_point`
- Exact Lean type: `∀ (P : ℕ) (f : Euclid P → Euclid P) (x : Euclid P) (δ c : ℝ), 0 < δ → ContDiffOn ℝ 1 f (ball x δ) → ‖fderiv ℝ f x‖ ≤ c → ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖f y - f z‖ ≤ (c + η) * ‖y - z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

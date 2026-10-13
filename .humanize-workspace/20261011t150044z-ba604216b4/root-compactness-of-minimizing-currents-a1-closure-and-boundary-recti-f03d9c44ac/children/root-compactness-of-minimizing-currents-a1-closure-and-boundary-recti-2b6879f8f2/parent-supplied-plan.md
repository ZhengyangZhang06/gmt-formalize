# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_to_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2b6879f8f2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1`
- Child key: `uniform_to_rectifiable`
- Declaration: `Submission.cbrr_rectifiable_of_uniform_density`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (E : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (a b δ : ℝ), 0 < a → b * 16 ^ n < a → 0 < δ → (∀ x ∈ E, Module.finrank ℝ (Q x) = n) → (∀ y ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (a * ρ ^ n) ≤ μ (closedBall y ρ)) → (∀ x ∈ E, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ ENNReal.ofReal (b * ρ ^ n)) → CountablyRectifiable n E`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.plane_net-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_claim-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.lipschitz_cover-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

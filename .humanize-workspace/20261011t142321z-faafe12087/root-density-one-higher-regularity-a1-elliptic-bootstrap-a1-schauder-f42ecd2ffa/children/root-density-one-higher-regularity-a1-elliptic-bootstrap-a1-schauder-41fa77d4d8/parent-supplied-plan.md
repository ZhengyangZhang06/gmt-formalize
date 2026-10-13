# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.absorption-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-41fa77d4d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child key: `absorption`
- Declaration: `Submission.dohr_eb_sch_ube_absorption`
- Exact Lean type: `∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖g x‖ ≤ 1024 * M + 64 * A) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖g x - g y‖ ≤ (1024 * M + 64 * A) * ‖x - y‖ ^ α`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_improvement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

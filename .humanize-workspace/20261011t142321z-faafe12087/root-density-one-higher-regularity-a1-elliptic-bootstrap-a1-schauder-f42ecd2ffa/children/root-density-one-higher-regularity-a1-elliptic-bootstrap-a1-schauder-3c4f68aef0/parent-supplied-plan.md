# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.rescaled_structure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-3c4f68aef0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child key: `rescaled_structure`
- Declaration: `Submission.dohr_eb_sch_ube_rescaled_structure`
- Exact Lean type: `∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (y₀ : Rn n) (ρ α lam M : ℝ), 0 < ρ → ‖y₀‖ + ρ ≤ 1 → 0 ≤ α → 0 ≤ M → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → (∀ z ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a (y₀ + ρ • z) P P) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q| ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |(ρ • Φ (y₀ + ρ • z)) P - (ρ • Φ (y₀ + ρ • z')) P| ≤ M * ‖z - z'‖ ^ α * ‖P‖) ∧ ∀ z ∈ ball (0 : Rn n) 1, ‖w (y₀ + ρ • z)‖ ≤ M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1.holder_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-5b41592233/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.unit_ball_estimate-a1`
- Child key: `holder_rescale`
- Declaration: `Submission.dohr_eb_sch_ube_holder_rescale`
- Exact Lean type: `∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (y : Rn n) (ρ r α c : ℝ), 0 < ρ → ((∀ z ∈ ball (0 : Rn n) r, ∀ z' ∈ ball (0 : Rn n) r, ‖ρ • g (y + ρ • z) - ρ • g (y + ρ • z')‖ ≤ c * ‖z - z'‖ ^ α) ↔ ∀ x ∈ ball y (ρ * r), ∀ x' ∈ ball y (ρ * r), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ c * ‖x - x'‖ ^ α)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

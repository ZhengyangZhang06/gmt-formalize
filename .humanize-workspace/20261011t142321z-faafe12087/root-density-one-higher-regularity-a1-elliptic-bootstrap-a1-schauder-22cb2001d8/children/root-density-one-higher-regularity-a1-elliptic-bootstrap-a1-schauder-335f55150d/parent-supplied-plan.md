# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-335f55150d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1`
- Child key: `weak_eq_limit`
- Declaration: `Submission.dohr_eb_sch_bu_weak_eq_limit`
- Exact Lean type: `∀ (n ℓ : ℕ) (α : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)) (R c d : ℕ → ℝ), 0 ≤ α → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → Continuous V → (∀ r : ℝ, TendstoUniformlyOn U V atTop (closedBall (0 : Rn n) r)) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ContinuousOn (U k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - A P Q| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (U k z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (V z) (fderiv ℝ ζ z) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

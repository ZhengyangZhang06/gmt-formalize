# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.blowup_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-8be7c308f8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1`
- Child key: `blowup_limit`
- Declaration: `Submission.dohr_eb_sch_bu_blowup_limit`
- Exact Lean type: `∀ (n ℓ : ℕ) (α lam M K : ℝ) (W : ℕ → Rn n → Rn ℓ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : ℕ → Rn n) (R c d : ℕ → ℝ), 0 < α → 0 ≤ K → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → (∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k))) → (∀ k, W k 0 = 0) → (∀ k, fderiv ℝ (W k) 0 = 0) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k), ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ ah k 0 P P) → (∀ k, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - ah k 0 P Q| ≤ c k * ‖z‖ ^ α * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → (∀ k, ‖e k‖ ≤ 1) → (∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1) → ∃ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W' : Rn n → Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) ∧ (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ ContDiff ℝ 1 W' ∧ (∀ z z' : Rn n, ‖fderiv ℝ W' z - fderiv ℝ W' z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (fderiv ℝ W' z) (fderiv ℝ ζ z) = 0) ∧ fderiv ℝ W' 0 = 0 ∧ ∃ e₀ : Rn n, ‖fderiv ℝ W' e₀‖ = 1`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.holder_diag_subseq-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.c1_limit-a1`
- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.blowup_estimate-a1.weak_eq_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

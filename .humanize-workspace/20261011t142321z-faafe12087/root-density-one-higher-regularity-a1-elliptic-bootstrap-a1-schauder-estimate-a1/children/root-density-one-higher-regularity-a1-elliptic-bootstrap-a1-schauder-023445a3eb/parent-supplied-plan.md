# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.caccioppoli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-023445a3eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1`
- Child key: `caccioppoli`
- Declaration: `Submission.dohr_eb_sch_caccioppoli_const_coeff`
- Exact Lean type: `∀ (n ℓ : ℕ) (lam Lam : ℝ), 0 < lam → ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (y : Rn n) (ρ : ℝ) (c : Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → 0 < ρ → ContDiffOn ℝ 1 V (ball y (2 * ρ)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball y (2 * ρ) → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

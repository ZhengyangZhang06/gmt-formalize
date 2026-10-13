# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1.mollify-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-schauder-75a198a31d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.schauder_estimate-a1.liouville-a1`
- Child key: `mollify`
- Declaration: `Submission.dohr_eb_sch_liou_mollify`
- Exact Lean type: `∀ (n ℓ : ℕ) (α K ε : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W : Rn n → Rn ℓ), 0 < α → 0 ≤ K → 0 < ε → ContDiff ℝ 1 W → (∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ x) = 0) → ∃ V : Rn n → Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x y : Rn n, ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ K * ‖x - y‖ ^ α) ∧ (∀ x : Rn n, ‖fderiv ℝ V x - fderiv ℝ W x‖ ≤ K * ε ^ α) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.averaged_hessian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-0516ed15cc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `averaged_hessian`
- Declaration: `Submission.dohr_eb_elc2_averaged_hessian`
- Exact Lean type: `∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (lam ε MB LB H α : ℝ) (S : Set (Rn n)) (P₀ P₁ : Rn n → Rn n →L[ℝ] Rn ℓ), ContDiff ℝ 2 Ψ → 0 ≤ LB → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q : Rn n →L[ℝ] Rn ℓ, lam * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ Ψ) P Q Q) → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q'| ≤ MB * ‖Q‖ * ‖Q'‖) → (∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ‖P'‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q' - fderiv ℝ (fderiv ℝ Ψ) P' Q Q'| ≤ LB * ‖P - P'‖ * ‖Q‖ * ‖Q'‖) → (∀ x ∈ S, ‖P₀ x‖ ≤ ε) → (∀ x ∈ S, ‖P₁ x‖ ≤ ε) → (∀ x ∈ S, ∀ y ∈ S, ‖P₀ x - P₀ y‖ ≤ H * ‖x - y‖ ^ α) → (∀ x ∈ S, ∀ y ∈ S, ‖P₁ x - P₁ y‖ ≤ H * ‖x - y‖ ^ α) → ∃ a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P Q : Rn n →L[ℝ] Rn ℓ), a x P Q = ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (P₀ x + t • (P₁ x - P₀ x)) P Q) ∧ (∀ x ∈ S, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) ∧ (∀ x ∈ S, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ MB * ‖P‖ * ‖Q‖) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ LB * H * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

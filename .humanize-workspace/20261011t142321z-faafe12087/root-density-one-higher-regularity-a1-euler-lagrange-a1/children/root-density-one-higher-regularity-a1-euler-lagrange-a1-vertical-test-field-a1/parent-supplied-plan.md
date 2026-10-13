# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1.vertical_test_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1-vertical-test-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child key: `vertical_test_field`
- Declaration: `Submission.dohr_vel_vertical_test_field`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (s r : ℝ) (u φ : Rn n → Rn ℓ), 0 < s → ContinuousOn u (ball 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖graphPoint x (u x)‖ < s) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∃ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ ball ξ s ∧ (∀ x : Rn n, X (ξ + Q.symm (graphPoint x (u x))) = Q.symm (graphPoint 0 (φ x))) ∧ ∀ (x v : Rn n) (w : Rn ℓ), fderiv ℝ X (ξ + Q.symm (graphPoint x (u x))) (Q.symm (graphPoint v w)) = Q.symm (graphPoint 0 (fderiv ℝ φ x v))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

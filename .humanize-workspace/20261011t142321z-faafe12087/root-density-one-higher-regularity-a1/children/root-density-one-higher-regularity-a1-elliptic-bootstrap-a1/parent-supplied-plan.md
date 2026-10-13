# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `elliptic_bootstrap`
- Declaration: `Submission.dohr_elliptic_bootstrap`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : ℕ) (α β : ℝ), 0 < α → α < 1 → α ≤ β → β ≤ 1 → ∀ (r : ℝ) (u : Rn n → Rn ℓ) (F : Amb n ℓ → Amb n ℓ) (O : Set (Amb n ℓ)), 0 < r → IsOpen O → IsLocallyHolderCkα q α F O → (∀ x ∈ ball (0 : Rn n) r, graphPoint x (u x) ∈ O) → ContDiffOn ℝ 1 u (ball 0 r) → fderiv ℝ u 0 = 0 → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) r, ∀ y ∈ ball (0 : Rn n) r, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K * ‖x - y‖ ^ β) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∫ x in ball (0 : Rn n) r, fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in ball (0 : Rn n) r, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * inner ℝ (graphPoint 0 (φ x)) (F (graphPoint x (u x)))) → ∃ r' > 0, r' ≤ r ∧ IsHolderCkα (q + 2) α u (ball 0 r')`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

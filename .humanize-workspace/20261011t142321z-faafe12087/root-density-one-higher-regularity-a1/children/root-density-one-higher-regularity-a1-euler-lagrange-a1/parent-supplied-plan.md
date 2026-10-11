# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `euler_lagrange`
- Declaration: `Submission.dohr_vertical_euler_lagrange`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), V.HasGeneralizedMeanCurvature H → IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) → ∀ (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U) ∧ ∃ r > 0, r ≤ R ∧ (∀ x ∈ ball (0 : Rn n) r, graphPoint x (u x) ∈ (fun y => Q (y - ξ)) '' U) ∧ ∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∫ x in ball (0 : Rn n) r, fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in ball (0 : Rn n) r, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x)))))`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

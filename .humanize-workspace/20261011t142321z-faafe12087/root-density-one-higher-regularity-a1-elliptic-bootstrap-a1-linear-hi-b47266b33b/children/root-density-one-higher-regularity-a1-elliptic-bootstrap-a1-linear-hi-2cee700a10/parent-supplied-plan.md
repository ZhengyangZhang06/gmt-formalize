# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_weak_equation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-2cee700a10/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1`
- Child key: `dq_weak_equation`
- Declaration: `Submission.dohr_eb_lhr_dq_weak_equation`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R d : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → d ≠ 0 → |d| < R → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → ContDiffOn ℝ 1 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball xb (2 * R) → ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x) = ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

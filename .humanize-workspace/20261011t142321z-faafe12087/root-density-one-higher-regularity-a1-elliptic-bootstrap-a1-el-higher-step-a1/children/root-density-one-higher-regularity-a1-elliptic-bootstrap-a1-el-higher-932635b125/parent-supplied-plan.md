# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1.differentiated_el-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-higher-932635b125/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_higher_step-a1`
- Child key: `differentiated_el`
- Declaration: `Submission.dohr_eb_ehs_differentiated_el`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u g : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ContinuousOn g U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ (e : Rn n) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x) (fderiv ℝ (fun z => fderiv ℝ u z e) x) (fderiv ℝ ζ x) = ∫ x in U, inner ℝ (g x) (fderiv ℝ ζ x e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

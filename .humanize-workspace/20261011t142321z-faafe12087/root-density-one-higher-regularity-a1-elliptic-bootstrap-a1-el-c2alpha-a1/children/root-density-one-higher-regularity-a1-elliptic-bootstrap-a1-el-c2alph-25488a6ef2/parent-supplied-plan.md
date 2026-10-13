# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.dq_weak_equation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-25488a6ef2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `dq_weak_equation`
- Declaration: `Submission.dohr_eb_elc2_dq_weak_equation`
- Exact Lean type: `∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U V : Set (Rn n)) (u g : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), ContDiff ℝ 2 Ψ → IsOpen U → IsOpen V → ContDiffOn ℝ 1 u U → ContinuousOn g U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ V → ∫ x in V, (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) = ∫ x in V, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.shift_ibp-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

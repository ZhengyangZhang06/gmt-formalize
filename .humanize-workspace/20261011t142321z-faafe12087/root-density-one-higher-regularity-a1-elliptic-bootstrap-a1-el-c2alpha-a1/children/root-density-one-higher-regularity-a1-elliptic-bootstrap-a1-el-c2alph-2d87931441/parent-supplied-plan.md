# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.shift_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-2d87931441/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `shift_ibp`
- Declaration: `Submission.dohr_eb_elc2_shift_ibp`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (g ζ : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), IsOpen U → ContinuousOn g U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ x ∈ tsupport ζ, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = d * ∫ x, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

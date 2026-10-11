# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.halfspace_flux-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-halfspace-flux-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1`
- Child key: `halfspace_flux`
- Declaration: `Submission.deGiorgiTM_halfSpace_integral_fderiv`
- Exact Lean type: `∀ (n : ℕ) (e : Rn (n + 1)) (φ : Rn (n + 1) → ℝ), ‖e‖ = 1 → ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ y in {y : Rn (n + 1) | 0 < inner ℝ y e}, fderiv ℝ φ y e = -∫ y in ((Submodule.span ℝ {e})ᗮ : Set (Rn (n + 1))), φ y ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

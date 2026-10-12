# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.tangent_ae-a1.c1_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1-c1-approximation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child key: `c1_approximation`
- Declaration: `Submission.tae_lipschitz_c1_approximation`
- Exact Lean type: `∀ {n : ℕ} (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume ({x | f x ≠ g x} ∪ {x | fderiv ℝ f x ≠ fderiv ℝ g x}) < ENNReal.ofReal ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

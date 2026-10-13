# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.interpolation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-differenc-eea526b72c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child key: `interpolation`
- Declaration: `Submission.dohr_eb_dql_interpolation_fderiv_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (h : Rn n → Rn ℓ) (x : Rn n) (r t α L S : ℝ), 0 < t → t ≤ r → 0 < α → 0 ≤ L → (∀ y ∈ closedBall x (2 * r), DifferentiableAt ℝ h y) → (∀ y ∈ closedBall x (2 * r), ∀ y' ∈ closedBall x (2 * r), ‖fderiv ℝ h y - fderiv ℝ h y'‖ ≤ L * ‖y - y'‖ ^ α) → (∀ y ∈ closedBall x (2 * r), ‖h y‖ ≤ S) → ∀ y ∈ closedBall x r, ‖fderiv ℝ h y‖ ≤ 2 * S / t + L * t ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1.bilinear_basis_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-ff53a35ecd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.coeff_uniform_bounds-a1`
- Child key: `bilinear_basis_bound`
- Declaration: `Submission.dohr_eb_lhr_cub_bilinear_basis_bound`
- Exact Lean type: `∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (E : Fin N → L) (c : ℝ), 0 ≤ c ∧ (∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t)|) * ‖P‖ * ‖Q‖) ∧ ∀ (B B' : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q - B' P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t) - B' (E r) (E t)|) * ‖P‖ * ‖Q‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

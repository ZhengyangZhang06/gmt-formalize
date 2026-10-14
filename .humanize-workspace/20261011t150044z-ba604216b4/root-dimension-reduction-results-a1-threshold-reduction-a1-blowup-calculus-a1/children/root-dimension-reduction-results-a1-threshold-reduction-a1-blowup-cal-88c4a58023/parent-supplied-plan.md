# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_calculus-a1.pullback_composition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cal-88c4a58023/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_calculus-a1`
- Child key: `pullback_composition`
- Declaration: `Submission.dimred_tr_bc_dilation_pullback_comp`
- Exact Lean type: `∀ (P n : ℕ) (x y : Euclid P) (lam mu : ℝ), lam ≠ 0 → ∀ ω : DifferentialForm (Euclid P) n, affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) (affinePullbackForm (dilationCLM P mu) (-(mu⁻¹ • y)) ω) = affinePullbackForm (dilationCLM P (lam * mu)) (-((lam * mu)⁻¹ • (x + lam • y))) ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

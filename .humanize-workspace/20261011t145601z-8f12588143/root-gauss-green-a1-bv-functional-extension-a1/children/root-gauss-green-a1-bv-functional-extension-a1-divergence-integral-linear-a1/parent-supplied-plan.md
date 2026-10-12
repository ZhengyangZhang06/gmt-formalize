# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.bv_functional_extension-a1.divergence_integral_linear-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-bv-functional-extension-a1-divergence-integral-linear-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.bv_functional_extension-a1`
- Child key: `divergence_integral_linear`
- Declaration: `Submission.gaussGreenRep_setIntegral_divergence_linear`
- Exact Lean type: `∀ (N : ℕ) (S : Set (Rn N)), (∀ g h : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → ContDiff ℝ 1 h → HasCompactSupport h → ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence (g + h) x = (∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence g x) + ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence h x) ∧ ∀ (c : ℝ) (g : Rn N → Rn N), ContDiff ℝ 1 g → ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence (c • g) x = c * ∫ x in S, Poincare.SimonGMT.Chapter02.euclideanDivergence g x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

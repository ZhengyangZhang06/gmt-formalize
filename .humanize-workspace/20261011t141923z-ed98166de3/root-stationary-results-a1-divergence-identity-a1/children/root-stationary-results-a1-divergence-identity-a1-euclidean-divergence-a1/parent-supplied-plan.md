# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.divergence_identity-a1.euclidean_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1-euclidean-divergence-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.divergence_identity-a1`
- Child key: `euclidean_divergence`
- Declaration: `Submission.euclidean_setIntegral_trace_fderiv_eq_zero`
- Exact Lean type: `∀ (n : ℕ) (V Q : Set (Rn n)) (w : Rn n → Rn n), IsOpen V → IsCompact Q → Q ⊆ V → ContDiffOn ℝ 1 w V → (∀ x ∈ V, x ∉ Q → w x = 0) → ∫ x in V, LinearMap.trace ℝ (Rn n) (fderiv ℝ w x).toLinearMap = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

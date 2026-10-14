# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.pushforward_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pushforward-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Child key: `pushforward_formula`
- Declaration: `Submission.iwl_sp_lipschitzPushforward_apply_eq`
- Exact Lean type: `∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)) (X : GeometricCurrentOn U n) (S : GeometricCurrentOn V n) (f : Eucl P → Eucl Q), Differentiable ℝ f → IsLipschitzPushforward X f S → ∀ (ω : TestFormOn V n) (η : TestFormOn U n), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) n) x = ((ω : DifferentialForm (Eucl Q) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

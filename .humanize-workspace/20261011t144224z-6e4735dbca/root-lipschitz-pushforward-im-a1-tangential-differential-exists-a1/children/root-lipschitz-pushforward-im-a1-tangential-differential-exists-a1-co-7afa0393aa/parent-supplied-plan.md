# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.continuous_left_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-co-7afa0393aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child key: `continuous_left_inverse`
- Declaration: `Submission.lpf_tde_continuous_left_inverse`
- Exact Lean type: `∀ (n P : ℕ), ∃ Λ : (Eucl n →L[ℝ] Eucl P) → (Eucl P →L[ℝ] Eucl n), ContinuousOn Λ {A : Eucl n →L[ℝ] Eucl P | Function.Injective A} ∧ ∀ A : Eucl n →L[ℝ] Eucl P, Function.Injective A → (Λ A).comp A = ContinuousLinearMap.id ℝ (Eucl n) ∧ ∀ v : Eucl P, ‖A (Λ A v)‖ ≤ ‖v‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

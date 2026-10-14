# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.support_null_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1-support-2d52519b95/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`
- Child key: `support_null_reduction`
- Declaration: `Submission.lpf_rsn_null_diff_support_of_local_null`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (μ : Measure (Eucl P)), M ⊆ U → (∀ W : Set (Eucl P), IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μ (M ∩ W) = 0) → μ (M \ T.support) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

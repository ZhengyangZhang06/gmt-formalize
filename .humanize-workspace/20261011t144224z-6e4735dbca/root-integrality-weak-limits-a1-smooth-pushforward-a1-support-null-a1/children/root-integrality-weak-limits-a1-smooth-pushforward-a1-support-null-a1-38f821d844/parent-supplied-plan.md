# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.local_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-38f821d844/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`
- Child key: `local_null`
- Declaration: `Submission.iwl_sp_sn_local_null`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → (μHE[n] : Measure (Eucl P)) (M ∩ W) = 0`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.covector_basis-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.signed_simple_bound-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.weighted_fundamental_lemma-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

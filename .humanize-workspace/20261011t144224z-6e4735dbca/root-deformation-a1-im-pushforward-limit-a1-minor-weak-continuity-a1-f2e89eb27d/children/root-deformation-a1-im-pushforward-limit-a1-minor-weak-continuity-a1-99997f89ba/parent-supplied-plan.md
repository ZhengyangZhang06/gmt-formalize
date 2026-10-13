# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.cofactor_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-99997f89ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Child key: `cofactor_leibniz`
- Declaration: `Submission.deformation_ipl_mwc_pi_cofactor_leibniz`
- Exact Lean type: `∀ (r : ℕ) (N : Fin r → Fin (r + 1) → ℝ) (q : Fin (r + 1)), (-1 : ℝ) ^ (q : ℕ) * Matrix.det (Matrix.of fun t s : Fin r => N t (q.succAbove s)) = ∑ σ : Equiv.Perm (Fin (r + 1)), (if σ 0 = q then ((Equiv.Perm.sign σ : ℤ) : ℝ) else 0) * ∏ t : Fin r, N t (σ t.succ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

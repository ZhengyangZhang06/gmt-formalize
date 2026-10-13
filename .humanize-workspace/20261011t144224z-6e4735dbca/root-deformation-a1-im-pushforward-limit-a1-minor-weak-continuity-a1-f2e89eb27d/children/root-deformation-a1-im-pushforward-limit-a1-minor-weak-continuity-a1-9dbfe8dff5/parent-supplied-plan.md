# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.swap_cancel-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-9dbfe8dff5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Child key: `swap_cancel`
- Declaration: `Submission.deformation_ipl_mwc_pi_swap_cancel`
- Exact Lean type: `∀ (r : ℕ) (H : Fin r → Fin (r + 1) → Fin (r + 1) → ℝ) (N : Fin r → Fin (r + 1) → ℝ), (∀ u i j, H u i j = H u j i) → ∑ σ : Equiv.Perm (Fin (r + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∑ u : Fin r, H u (σ 0) (σ u.succ) * ∏ t ∈ Finset.univ.erase u, N t (σ t.succ) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

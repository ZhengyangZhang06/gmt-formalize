# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1.fderiv_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-ebb928a3a8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.pushforward_current-a1`
- Child key: `fderiv_bound`
- Declaration: `Submission.dpf_pfc_fderiv_norm_le_of_eq_id_off_compact`
- Exact Lean type: `∀ (P : ℕ) (K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsCompact K → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ Λ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

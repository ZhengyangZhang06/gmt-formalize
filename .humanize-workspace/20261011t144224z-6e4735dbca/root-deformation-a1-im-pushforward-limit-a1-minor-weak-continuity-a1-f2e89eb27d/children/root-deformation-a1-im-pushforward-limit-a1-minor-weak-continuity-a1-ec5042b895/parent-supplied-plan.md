# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.fderiv_sum_prod-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-ec5042b895/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`
- Child key: `fderiv_sum_prod`
- Declaration: `Submission.deformation_ipl_mwc_pi_fderiv_sum_prod`
- Exact Lean type: `∀ (k r : ℕ) (ι : Type) [Fintype ι] (a : ι → ℝ) (g : ι → Fin r → Eucl k → ℝ) (w v : Eucl k), (∀ i t, DifferentiableAt ℝ (g i t) w) → fderiv ℝ (fun x : Eucl k => ∑ i, a i * ∏ t, g i t x) w v = ∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ∈ Finset.univ.erase u, g i t w`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

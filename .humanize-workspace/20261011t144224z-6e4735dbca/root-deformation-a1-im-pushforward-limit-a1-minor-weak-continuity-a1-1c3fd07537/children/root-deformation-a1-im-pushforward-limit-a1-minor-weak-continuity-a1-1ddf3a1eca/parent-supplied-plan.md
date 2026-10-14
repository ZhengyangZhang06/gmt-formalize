# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.ae_fderiv_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1ddf3a1eca/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`
- Child key: `ae_fderiv_extension`
- Declaration: `Submission.deformation_ipl_mwc_mil_ae_fderiv_eq_proj`
- Exact Lean type: `∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : Eucl k → Eucl Q) (c : Fin Q) (g : Eucl k → ℝ), IsOpen Ω → LipschitzOnWith C v Ω → EqOn g (fun w => EuclideanSpace.proj c (v w)) Ω → ∀ᵐ w ∂(volume : Measure (Eucl k)), w ∈ Ω → ∀ x : Eucl k, fderiv ℝ g w x = EuclideanSpace.proj c (fderiv ℝ v w x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

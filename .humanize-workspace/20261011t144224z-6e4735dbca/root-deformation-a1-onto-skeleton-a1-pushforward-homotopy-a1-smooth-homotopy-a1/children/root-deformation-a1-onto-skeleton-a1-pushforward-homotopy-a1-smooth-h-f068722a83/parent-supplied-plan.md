# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.extderiv_compatible-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-f068722a83/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`
- Child key: `extderiv_compatible`
- Declaration: `Submission.dph_sh_extDeriv_compatible`
- Exact Lean type: `∀ (P Q j : ℕ) (G : Eucl P → Eucl Q) (ω : DifferentialForm (Eucl Q) j) (θ : DifferentialForm (Eucl P) j) (N : Set (Eucl P)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → IsOpen N → (∀ x ∈ N, θ x = (ω (G x)).compContinuousLinearMap (fderiv ℝ G x)) → ∀ x ∈ N, exteriorDerivative θ x = ((exteriorDerivative ω) (G x)).compContinuousLinearMap (fderiv ℝ G x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.weak_smooth-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-632d04a7e5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child key: `weak_smooth`
- Declaration: `Submission.dor_lmbsf_pwl_fderiv_weak_smooth`
- Exact Lean type: `∀ (d : ℕ) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ) (Ψ : Euclid d → Euclid d), (∀ k, LipschitzWith K (us k)) → TendstoUniformly us u atTop → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) atTop (𝓝 (∫ y, fderiv ℝ u y (Ψ y)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

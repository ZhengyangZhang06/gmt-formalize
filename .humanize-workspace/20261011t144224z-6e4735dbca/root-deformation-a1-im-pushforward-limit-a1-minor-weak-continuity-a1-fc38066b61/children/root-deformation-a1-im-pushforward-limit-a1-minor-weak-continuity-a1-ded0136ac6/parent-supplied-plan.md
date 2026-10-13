# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1.scalar_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-ded0136ac6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1`
- Child key: `scalar_dense`
- Declaration: `Submission.deformation_ipl_mwc_td_scalar_smooth_dense`
- Exact Lean type: `∀ (k : ℕ) (Ω : Set (Eucl k)) (η : Eucl k → ℝ), IsOpen Ω → IntegrableOn η Ω (volume : Measure (Eucl k)) → ∀ ε : ℝ, 0 < ε → ∃ φ : Eucl k → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧ ∫ w in Ω, |η w - φ w| ∂(volume : Measure (Eucl k)) < ε`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_dense-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

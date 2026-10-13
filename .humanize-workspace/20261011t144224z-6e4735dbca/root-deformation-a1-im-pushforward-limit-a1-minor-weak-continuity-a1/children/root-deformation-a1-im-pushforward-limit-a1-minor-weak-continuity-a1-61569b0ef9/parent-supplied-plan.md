# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.lipschitz_smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-61569b0ef9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `lipschitz_smooth_approx`
- Declaration: `Submission.deformation_ipl_mwc_lipschitz_smooth_approx`
- Exact Lean type: `∀ (k : ℕ) (L : ℝ≥0) (g : Eucl k → ℝ), LipschitzWith L g → ∃ G : ℕ → Eucl k → ℝ, (∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G m)) ∧ (∀ m, LipschitzWith L (G m)) ∧ TendstoUniformly G g atTop ∧ ∀ᵐ w ∂(volume : Measure (Eucl k)), Tendsto (fun m => fderiv ℝ (G m) w) atTop (𝓝 (fderiv ℝ g w))`

## Sibling prerequisites

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1`
- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_fderiv-a1`
- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_close-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

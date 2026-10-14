# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.lipschitz_smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1ad00fd161/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child key: `lipschitz_smooth_approx`
- Declaration: `Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx`
- Exact Lean type: `∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.mollify_fderiv-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.lipschitz_smoothing-a1.mollify_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

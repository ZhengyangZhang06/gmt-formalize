# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-fc38066b61/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `test_density`
- Declaration: `Submission.deformation_ipl_mwc_test_density`
- Exact Lean type: `∀ (k : ℕ) (Ω : Set (Eucl k)) (B : ℝ) (f : ℕ → Eucl k → ℝ) (f₀ : Eucl k → ℝ), IsOpen Ω → (∀ j, AEStronglyMeasurable (f j) ((volume : Measure (Eucl k)).restrict Ω)) → AEStronglyMeasurable f₀ ((volume : Measure (Eucl k)).restrict Ω) → (∀ j, ∀ w ∈ Ω, |f j w| ≤ B) → (∀ w ∈ Ω, |f₀ w| ≤ B) → (∀ φ : Eucl k → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω → Tendsto (fun j => ∫ w in Ω, φ w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, φ w * f₀ w ∂(volume : Measure (Eucl k))))) → ∀ η : Eucl k → ℝ, IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * f j w ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * f₀ w ∂(volume : Measure (Eucl k))))`

## Sibling prerequisites

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

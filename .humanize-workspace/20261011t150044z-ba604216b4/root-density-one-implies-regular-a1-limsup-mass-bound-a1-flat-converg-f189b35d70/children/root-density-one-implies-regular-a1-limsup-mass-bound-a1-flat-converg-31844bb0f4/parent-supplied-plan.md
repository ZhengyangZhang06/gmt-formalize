# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1.weak_star_l1_upgrade-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-31844bb0f4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1`
- Child key: `weak_star_l1_upgrade`
- Declaration: `Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade`
- Exact Lean type: `∀ (k : ℕ) (C : ℝ) (Fs : ℕ → Euclid k → ℝ) (F : Euclid k → ℝ), (∀ j, AEStronglyMeasurable (Fs j) (volume : Measure (Euclid k))) → AEStronglyMeasurable F (volume : Measure (Euclid k)) → (∀ j x, |Fs j x| ≤ C) → (∀ x, |F x| ≤ C) → (∀ ψ : Euclid k → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → Tendsto (fun j => ∫ x, ψ x * Fs j x) atTop (𝓝 (∫ x, ψ x * F x))) → ∀ φ : Euclid k → ℝ, Integrable φ → Tendsto (fun j => ∫ x, φ x * Fs j x) atTop (𝓝 (∫ x, φ x * F x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

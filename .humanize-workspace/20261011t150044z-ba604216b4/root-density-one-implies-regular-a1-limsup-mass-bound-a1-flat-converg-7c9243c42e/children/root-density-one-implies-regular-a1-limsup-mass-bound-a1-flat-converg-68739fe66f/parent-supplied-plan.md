# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.smooth_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-68739fe66f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `smooth_homotopy`
- Declaration: `Submission.dor_lmb_fcdp_smooth_homotopy`
- Exact Lean type: `(∀ (N N' m : ℕ) (Φ : Euclid N → Euclid N') (α : DifferentialForm (Euclid N') m), ContDiff ℝ (⊤ : ℕ∞) Φ → IsSmoothForm α → IsSmoothForm (fun x => (α (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x))) ∧ ∀ (P k : ℕ) (F G : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1, ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧ ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) - (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) = exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1, ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x + ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

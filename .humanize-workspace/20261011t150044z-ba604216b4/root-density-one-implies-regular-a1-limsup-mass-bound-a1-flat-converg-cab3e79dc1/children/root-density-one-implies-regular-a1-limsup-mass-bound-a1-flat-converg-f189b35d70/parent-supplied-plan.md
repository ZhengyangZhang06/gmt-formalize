# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.jacobian_weak_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f189b35d70/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child key: `jacobian_weak_continuity`
- Declaration: `Submission.dor_lmb_fcd_jacobian_weak_continuity`
- Exact Lean type: `∀ (k N' : ℕ) (A : Set (Euclid k)) (w : Euclid k → ℝ) (L : NNReal) (Hs : ℕ → Euclid k → Euclid N') (H : Euclid k → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k), MeasurableSet A → IntegrableOn w A → (∀ j, LipschitzWith L (Hs j)) → LipschitzWith L H → TendstoUniformly Hs H atTop → Tendsto (fun j => ∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (Hs j u) (fun i => fderiv ℝ (Hs j) u (EuclideanSpace.single i (1 : ℝ)))) atTop (𝓝 (∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (H u) (fun i => fderiv ℝ H u (EuclideanSpace.single i (1 : ℝ)))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

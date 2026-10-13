# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-722770cb6e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `minor_weak_star`
- Declaration: `Submission.deformation_ipl_mwc_minor_weak_star`
- Exact Lean type: `∀ (k Q : ℕ) (Ω : Set (Eucl k)) (C : ℝ≥0) (v : ℕ → Eucl k → Eucl Q) (v₀ : Eucl k → Eucl Q), IsOpen Ω → (∀ j, LipschitzOnWith C (v j) Ω) → LipschitzOnWith C v₀ Ω → TendstoUniformlyOn v v₀ atTop Ω → ∀ (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k) (η : Eucl k → ℝ), IntegrableOn η Ω (volume : Measure (Eucl k)) → Tendsto (fun j => ∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (v j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, η w * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ v₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))`

## Sibling prerequisites

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1`
- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.coeff_minor_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-bff0c8b488/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`
- Child key: `coeff_minor_continuity`
- Declaration: `Submission.deformation_ipl_mwc_coeff_minor_continuity`
- Exact Lean type: `∀ (k Q : ℕ) (Ω : Set (Eucl k)) (ψ : Eucl k → ℝ) (g : Eucl Q → ℝ) (C : ℝ≥0) (u : ℕ → Eucl k → Eucl Q) (u₀ : Eucl k → Eucl Q) (r : ℕ) (a : Fin r → Fin Q) (b : Fin r → Fin k), IsOpen Ω → IntegrableOn ψ Ω (volume : Measure (Eucl k)) → Continuous g → HasCompactSupport g → (∀ j, LipschitzOnWith C (u j) Ω) → LipschitzOnWith C u₀ Ω → TendstoUniformlyOn u u₀ atTop Ω → Tendsto (fun j => ∫ w in Ω, ψ w * g (u j w) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ (u j) w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))) atTop (𝓝 (∫ w in Ω, ψ w * g (u₀ w) * Matrix.det (Matrix.of fun t s : Fin r => EuclideanSpace.proj (a t) (fderiv ℝ u₀ w (EuclideanSpace.single (b s) 1))) ∂(volume : Measure (Eucl k))))`

## Sibling prerequisites

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

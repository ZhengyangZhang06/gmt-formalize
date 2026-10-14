# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.pullback_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-d2560752b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child key: `pullback_continuity`
- Declaration: `Submission.cmcdt_lpi_pullback_weak_continuity`
- Exact Lean type: `∀ (m N' : ℕ) (L : NNReal) (H : ℕ → Euclid m → Euclid N') (H₀ : Euclid m → Euclid N') (w : Euclid m → ℝ) (ω : DifferentialForm (Euclid N') m), (∀ j, LipschitzWith L (H j)) → LipschitzWith L H₀ → TendstoUniformly H H₀ atTop → Integrable w → Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ u, w u * ω (H j u) (fun a => fderiv ℝ (H j) u (EuclideanSpace.single a 1))) atTop (𝓝 (∫ u, w u * ω (H₀ u) (fun a => fderiv ℝ H₀ u (EuclideanSpace.single a 1))))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.minor_continuity-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

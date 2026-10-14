# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.minor_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-6f0c593de0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child key: `minor_continuity`
- Declaration: `Submission.cmcdt_lpi_minor_weak_continuity`
- Exact Lean type: `∀ (m p r : ℕ) (L : NNReal) (v : ℕ → Euclid m → Euclid p) (v₀ : Euclid m → Euclid p) (a : Fin r → Fin p) (b : Fin r → Fin m) (c : Euclid m → ℝ), (∀ j, LipschitzWith L (v j)) → LipschitzWith L v₀ → TendstoUniformly v v₀ atTop → Integrable c → Tendsto (fun j => ∫ u, c u * Matrix.det (Matrix.of fun s t => fderiv ℝ (v j) u (EuclideanSpace.single (b t) 1) (a s))) atTop (𝓝 (∫ u, c u * Matrix.det (Matrix.of fun s t => fderiv ℝ v₀ u (EuclideanSpace.single (b t) 1) (a s))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

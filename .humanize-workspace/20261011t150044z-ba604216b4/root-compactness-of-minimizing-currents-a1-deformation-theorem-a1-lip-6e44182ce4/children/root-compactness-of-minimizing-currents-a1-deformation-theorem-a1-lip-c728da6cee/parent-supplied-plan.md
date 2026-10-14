# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1.pullback_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-c728da6cee/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Child key: `pullback_integrable`
- Declaration: `Submission.cmcdt_lpi_cyl_pullback_integrable`
- Exact Lean type: `∀ (Q n : ℕ) (L : NNReal) (H : Euclid n → Euclid Q) (S : Set (Euclid n)) (g : Euclid n → ℝ) (ω : TestFormOn (univ : Set (Euclid Q)) n), LipschitzWith L H → IntegrableOn g S → IntegrableOn (fun z => g z * (ω : DifferentialForm (Euclid Q) n) (H z) (fun a => fderiv ℝ H z (EuclideanSpace.single a 1))) S`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

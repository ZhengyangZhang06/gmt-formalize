# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1`
- Child key: `tangent_measure`
- Declaration: `Submission.deGiorgi_tangent_measure`
- Exact Lean type: `∀ (n : ℕ) (U E : Set (Rn (n + 1))) (μ : Measure (Rn (n + 1))) (ν : Rn (n + 1) → Rn (n + 1)), IsOpen U → NullMeasurableSet E volume → IsGaussGreenPair U E μ ν → ∀ x ∈ reducedBoundary U μ ν, HasApproxTangentPlaneWithMultiplicity n μ x ((Submodule.span ℝ {reducedNormal μ ν x})ᗮ) 1`

## Sibling prerequisites

- `root.de_giorgi-a1.blowup_identity-a1`
- `root.de_giorgi-a1.density_estimates-a1`
- `root.de_giorgi-a1.blowup_halfspace-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

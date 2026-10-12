# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1.restricted_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1-restricted-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child key: `restricted_density`
- Declaration: `Submission.varifold_tangents_dlb_restricted_hasDensity`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t R : ℝ) (c θ : ℝ≥0∞) (W : Varifold N n (ball (0 : Euclidean N) R)) (y : Euclidean N), 0 < t → c ≠ ∞ → W.measure = c • (rescaledMeasure V x t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) → y ∈ ball (0 : Euclidean N) R → HasDensity n V.weight (x + t • y) θ → HasDensity n W.weight y (c * θ)`

## Sibling prerequisites

- `root.varifold_tangents-a1.density_lower_bound-a1.density_scaling-a1`
- `root.varifold_tangents-a1.density_lower_bound-a1.rescaled_mass_formula-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

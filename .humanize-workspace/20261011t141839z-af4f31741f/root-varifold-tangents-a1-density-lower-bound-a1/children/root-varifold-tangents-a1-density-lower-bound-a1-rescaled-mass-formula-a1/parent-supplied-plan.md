# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.density_lower_bound-a1.rescaled_mass_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-density-lower-bound-a1-rescaled-mass-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.density_lower_bound-a1`
- Child key: `rescaled_mass_formula`
- Declaration: `Submission.varifold_tangents_dlb_rescaledMeasure_prod_univ`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (t : ℝ), (∀ A : Set (Euclidean N), MeasurableSet A → rescaledMeasure V x t (A ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight {z | t⁻¹ • (z - x) ∈ A}) ∧ (0 < t → ∀ (y : Euclidean N) (ρ : ℝ), rescaledMeasure V x t (closedBall y ρ ×ˢ (univ : Set (Grassmannian N n))) = ENNReal.ofReal (t⁻¹ ^ n) * V.weight (closedBall (x + t • y) (t * ρ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

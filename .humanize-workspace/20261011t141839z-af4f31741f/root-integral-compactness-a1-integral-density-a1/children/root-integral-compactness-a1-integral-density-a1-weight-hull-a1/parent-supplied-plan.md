# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.integral_density-a1.weight_hull-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-integral-density-a1-weight-hull-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.integral_density-a1`
- Child key: `weight_hull`
- Declaration: `Submission.intcpt_id_weight_hull`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf V M θ → ∃ T : Set (Euclidean N), MeasurableSet T ∧ {x | x ∈ M ∧ ∃ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane} ⊆ T ∧ V.weight = (((μHE[n] : Measure (Euclidean N)).restrict M).withDensity fun x ↦ ENNReal.ofReal (θ x)).restrict T ∧ ∀ B : Set (Euclidean N), MeasurableSet B → V.weight B = ∫⁻ x in {x | x ∈ M ∧ ∃ S : Grassmannian N n, Chapter03.HasWeightedApproximateTangentSpaceAt n M θ x S.plane} ∩ B, ENNReal.ofReal (θ x) ∂μHE[n]`

## Sibling prerequisites

- `root.integral_compactness-a1.integral_density-a1.restrict_sigma_finite-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

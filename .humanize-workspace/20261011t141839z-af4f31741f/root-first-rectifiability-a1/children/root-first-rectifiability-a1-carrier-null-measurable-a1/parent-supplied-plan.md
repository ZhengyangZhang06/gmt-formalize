# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.carrier_null_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-carrier-null-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `carrier_null_measurable`
- Declaration: `Submission.frt_carrier_nullMeasurable`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), M ⊆ U → V.weight Mᶜ = 0 → (∀ x ∈ M, 0 < θ x ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) → NullMeasurableSet M μHE[n]`

## Sibling prerequisites

- `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.carrier_dilation_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1-carrier-dil-5e0eeb9237/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child key: `carrier_dilation_null`
- Declaration: `Submission.allard_tc_cri_carrier_dilation_null`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), NullMeasurableSet M (μHE[n] : Measure (Euclidean N)) → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Euclidean N), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Euclidean N))) → (∀ B : Set (Euclidean N), MeasurableSet B → μ B = ∫⁻ x in M ∩ B, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Euclidean N))) → (∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → μ (s • A) = ENNReal.ofReal s ^ n * μ A) → ∀ s : ℝ, 0 < s → (μHE[n] : Measure (Euclidean N)) {w : Euclidean N | w ∈ M ∧ s • w ∉ M} = 0 ∧ (μHE[n] : Measure (Euclidean N)) {w : Euclidean N | s • w ∈ M ∧ w ∉ M} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.weight_eq_theta_hausdorff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-eq-theta-hausdorff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `weight_eq_theta_hausdorff`
- Declaration: `Submission.frt_weight_eq_multiplicity_hausdorff`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), M ⊆ U → V.weight Mᶜ = 0 → (∀ x ∈ M, 0 < θ x ∧ HasDensity n V.weight x (ENNReal.ofReal (θ x))) → (∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ M ⊆ ⋃ c ∈ C, c.2) → (∀ K : Set (Euclidean N), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) μHE[n]) ∧ ∀ B : Set (Euclidean N), NullMeasurableSet B V.weight → V.weight B = ∫⁻ x in B ∩ M, ENNReal.ofReal (θ x) ∂μHE[n]`

## Sibling prerequisites

- `root.first_rectifiability-a1.density_one_flat_covers-a1`
- `root.first_rectifiability-a1.weight_null_of_hausdorff_null-a1`
- `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1`
- `root.first_rectifiability-a1.carrier_null_measurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

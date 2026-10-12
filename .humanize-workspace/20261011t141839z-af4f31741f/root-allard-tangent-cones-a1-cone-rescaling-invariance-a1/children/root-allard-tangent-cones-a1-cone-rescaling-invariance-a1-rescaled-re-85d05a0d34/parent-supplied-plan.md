# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.rescaled_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1-rescaled-re-85d05a0d34/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child key: `rescaled_representation`
- Declaration: `Submission.allard_tc_cri_rescaled_representation`
- Exact Lean type: `∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (M : Set (Euclidean N)) (P : Euclidean N → Grassmannian N n → Prop) (g : Euclidean N → ℝ≥0∞), (∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n, P x T ∧ (x, T) ∈ A}, g x ∂(μHE[n] : Measure (Euclidean N))) → ∀ s : ℝ, 0 < s → ∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → rescaledMeasure C 0 s A = ∫⁻ w in {w : Euclidean N | s • w ∈ M ∧ ∃ T : Grassmannian N n, P (s • w) T ∧ (w, T) ∈ A}, g (s • w) ∂(μHE[n] : Measure (Euclidean N))`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.hausdorff_dilation_lintegral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

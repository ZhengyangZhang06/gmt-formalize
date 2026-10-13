# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.cone_rescaling_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1`
- Child key: `cone_rescaling_invariance`
- Declaration: `Submission.allard_tc_cone_rescaling_invariance`
- Exact Lean type: `∀ (N n : ℕ) (C : Varifold N n (univ : Set (Euclidean N))) (M : Set (Euclidean N)) (θ : Euclidean N → ℝ), IsVarifoldOf C M θ → (∀ x ∈ M, ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x)) → (∀ A : Set (Euclidean N × Grassmannian N n), MeasurableSet A → C.measure A = ∫⁻ x in {x | x ∈ M ∧ ∃ T : Grassmannian N n, HasTangentPlane C x T (θ x) ∧ (x, T) ∈ A}, ENNReal.ofReal (θ x) ∂μHE[n]) → (∀ (s : ℝ) (A : Set (Euclidean N)), 0 < s → C.weight (s • A) = ENNReal.ofReal s ^ n * C.weight A) → ∀ s : ℝ, 0 < s → rescaledMeasure C 0 s = C.measure`

## Sibling prerequisites

- `root.allard_tangent_cones-a1.tangent_plane_dilation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

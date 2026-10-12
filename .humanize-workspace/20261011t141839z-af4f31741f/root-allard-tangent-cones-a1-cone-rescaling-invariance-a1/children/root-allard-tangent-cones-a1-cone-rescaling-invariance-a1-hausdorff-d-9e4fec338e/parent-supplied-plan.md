# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.cone_rescaling_invariance-a1.hausdorff_dilation_lintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-cone-rescaling-invariance-a1-hausdorff-d-9e4fec338e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.cone_rescaling_invariance-a1`
- Child key: `hausdorff_dilation_lintegral`
- Declaration: `Submission.allard_tc_cri_hausdorff_dilation_lintegral`
- Exact Lean type: `∀ (N n : ℕ) (s : ℝ) (D : Set (Euclidean N)) (f : Euclidean N → ℝ≥0∞), 0 < s → ∫⁻ x in D, f x ∂(μHE[n] : Measure (Euclidean N)) = ENNReal.ofReal s ^ n * ∫⁻ w in {w : Euclidean N | s • w ∈ D}, f (s • w) ∂(μHE[n] : Measure (Euclidean N))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

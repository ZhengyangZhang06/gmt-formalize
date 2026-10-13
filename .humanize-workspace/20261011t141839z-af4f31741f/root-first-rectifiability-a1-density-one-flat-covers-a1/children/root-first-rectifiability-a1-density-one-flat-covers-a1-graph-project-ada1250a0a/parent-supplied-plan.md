# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.density_one_flat_covers-a1.graph_projection_compare-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-density-one-flat-covers-a1-graph-project-ada1250a0a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1.density_one_flat_covers-a1`
- Child key: `graph_projection_compare`
- Declaration: `Submission.frt_lipschitz_graph_hausdorff_compare`
- Exact Lean type: `∀ (N n : ℕ) (P : Grassmannian N n) (L : ℝ) (S : Set (Euclidean N)), 0 ≤ L → (∀ y ∈ S, ∀ z ∈ S, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) → (∀ x ∈ S, ∀ r : ℝ, (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) (r / Real.sqrt (1 + L ^ 2))) ≤ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ∧ (μHE[n] : Measure (Euclidean N)) (S ∩ closedBall x r) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) ((Grassmannian.project P '' S) ∩ closedBall (Grassmannian.project P x) r)) ∧ ∀ Y : Set (Euclidean N), (μHE[n] : Measure (Euclidean N)) (S ∩ Grassmannian.project P ⁻¹' Y) ≤ ENNReal.ofReal (Real.sqrt (1 + L ^ 2)) ^ n * (μHE[n] : Measure (Euclidean N)) Y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

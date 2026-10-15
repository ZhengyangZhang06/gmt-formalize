# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1`
- Child key: `graph_cycle_regular`
- Declaration: `Submission.dor_graph_supported_cycle_regular`
- Exact Lean type: `∀ (n k : ℕ) (U : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s h : ℝ), 0 < n → IsOpen U → R.Represents T → BoundaryVanishes T → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → 0 < h → ContDiffOn ℝ 1 u (ball 0 s) → u 0 = 0 → {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → R.measure.support ∩ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} = (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s → z ∈ T.support → z ∈ regularSet T`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

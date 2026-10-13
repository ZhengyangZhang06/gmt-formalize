# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-27e8b1c734/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `graph_area`
- Declaration: `Submission.dorag_tes_lipschitz_graph_area_bounds`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (A : Set (Euclid n)) (h : Euclid (n + k) → ℝ≥0∞), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → MeasurableSet A → Measurable h → (∫⁻ v in A, h (ξ + ι v + ι' (f v)) ≤ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n]) ∧ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n] ≤ ∫⁻ v in A, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * h (ξ + ι v + ι' (f v))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

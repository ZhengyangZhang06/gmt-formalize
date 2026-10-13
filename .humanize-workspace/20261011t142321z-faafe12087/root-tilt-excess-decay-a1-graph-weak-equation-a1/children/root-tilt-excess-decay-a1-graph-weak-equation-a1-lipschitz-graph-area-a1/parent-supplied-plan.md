# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.lipschitz_graph_area-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-lipschitz-graph-area-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `lipschitz_graph_area`
- Declaration: `Submission.gwe_lipschitz_graph_area_formula`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ g : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ)) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) * g (q (graphPoint x (f x)))`

## Sibling prerequisites

- `root.lipschitz_approximation-a1.graph_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.varifold_graph_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child key: `varifold_graph_transfer`
- Declaration: `Submission.gwe_varifold_graph_transfer`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), LipschitzOnWith 1 f (closedBall 0 R) → ∃ W : Rn n → ℝ, Measurable W ∧ (∀ x, 0 ≤ W x) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, φ y ∂V.weight = ∫⁻ x in A, ENNReal.ofReal (W x) * φ (q (graphPoint x (f x)))) ∧ (∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ φ : Amb n ℓ → ℝ, Measurable φ → ∫ y in q '' graphOver f A, φ y ∂V.weight = ∫ x in A, W x * φ (q (graphPoint x (f x)))) ∧ (∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ ball 0 R → W x = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ))))) * V.carrier.indicator V.mult (q (graphPoint x (f x)))) ∧ ∀ Z : Set (Amb n ℓ), V.weight Z = 0 → ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ closedBall 0 R → q (graphPoint x (f x)) ∈ Z → W x = 0`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_jacobian_bounds-a1`
- `root.tilt_excess_decay-a1.graph_weak_equation-a1.lipschitz_graph_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

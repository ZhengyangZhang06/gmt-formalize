# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.euler_lagrange-a1.graph_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1-graph-area-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child key: `graph_area_formula`
- Declaration: `Submission.dohr_vel_graph_area_formula`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (D : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen D → ContDiffOn ℝ 1 u D → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ D → (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))))`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.euler_lagrange-a1.linear_graph_area-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

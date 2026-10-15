# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_constancy-a1.weak_derivs-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-ef56e3263a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_constancy-a1`
- Child key: `weak_derivs`
- Declaration: `Submission.dtc_bc_cz_tc_weak_derivs`
- Exact Lean type: `∀ (m : ℕ) (V B : Set (Euclid (m + 1))) (X : GeometricCurrentOn V (m + 1)) (G : Euclid (m + 1) → ℝ), B ⊆ V → (∀ β : TestFormOn V m, tsupport (β : DifferentialForm (Euclid (m + 1)) m) ⊆ B → X.boundary β = 0) → (∀ ω : TestFormOn V (m + 1), X ω = ∫ y, G y * (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) y ⇑(EuclideanSpace.basisFun (Fin (m + 1)) ℝ)) → ∀ a : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ B → ∀ j : Fin (m + 1), ∫ v in B, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.orient_interior-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-3900f4c29c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `orient_interior`
- Declaration: `Submission.dtc_bc_lc_sl_ll_orient_interior`
- Exact Lean type: `∀ (P n : ℕ) (ξ : MultiVector P (n + 1)) (α : Covector (Euclid P) n), (∀ β : Euclid P →L[ℝ] ℝ, ξ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α)) = β (∑ i : Fin P, ξ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Euclid P)).smulRight α)) • (EuclideanSpace.single i (1 : ℝ) : Euclid P))) ∧ ∀ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf ξ Q → (∑ i : Fin P, ξ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ) : Euclid P)).smulRight α)) • (EuclideanSpace.single i (1 : ℝ) : Euclid P)) ∈ Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

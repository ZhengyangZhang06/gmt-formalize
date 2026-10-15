# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.orient_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-570dee57ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `orient_algebra`
- Declaration: `Submission.dtc_bc_lc_pfi_unitOrientation_algebra`
- Exact Lean type: `∀ (P n : ℕ), (∀ (ξ ξ' : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → IsUnitOrientationOf ξ' T → ξ' = ξ ∨ ξ' = -ξ) ∧ (∀ (ξ : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → ∀ β : Covector (Euclid P) n, |ξ β| ≤ ‖β‖) ∧ (∀ A : Euclid n →L[ℝ] Euclid P, Injective A → 0 < Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) ∧ IsUnitOrientationOf ((Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))))⁻¹ • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun k : Fin n => A (EuclideanSpace.single k 1))) (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P))) ∧ ∀ A : Euclid n →L[ℝ] Euclid P, ¬ Injective A → ∀ β : Covector (Euclid P) n, β (fun k : Fin n => A (EuclideanSpace.single k 1)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

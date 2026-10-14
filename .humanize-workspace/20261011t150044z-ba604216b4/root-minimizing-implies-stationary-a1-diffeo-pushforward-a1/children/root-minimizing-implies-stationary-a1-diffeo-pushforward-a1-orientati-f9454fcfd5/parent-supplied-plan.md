# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-f9454fcfd5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child key: `orientation_pushforward`
- Declaration: `Submission.dpf_unitOrientation_map_gramNormalized`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n) (L : Euclid P →L[ℝ] Euclid P) (J : ℝ), IsUnitOrientationOf ξ Q → Injective L → J = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j)))) → 0 < J ∧ J ≤ ‖L‖ ^ n ∧ IsUnitOrientationOf (J⁻¹ • ξ.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM L)) (Submodule.map (L : Euclid P →ₗ[ℝ] Euclid P) Q)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

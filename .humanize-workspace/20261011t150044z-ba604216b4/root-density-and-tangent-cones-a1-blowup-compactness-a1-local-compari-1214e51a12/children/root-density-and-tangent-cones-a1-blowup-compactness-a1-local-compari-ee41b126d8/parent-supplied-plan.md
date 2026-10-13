# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1.unit_orient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-ee41b126d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.slice_family-a1`
- Child key: `unit_orient`
- Declaration: `Submission.dtc_bc_lc_sl_sf_unit_orient`
- Exact Lean type: `(∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∀ α : Covector (Euclid P) n, |ξ α| ≤ ‖α‖) ∧ ∀ (P n : ℕ) (ξ : MultiVector P (n + 1)) (Q : Submodule ℝ (Euclid P)) (v : Euclid P) (ζ : MultiVector P n), IsUnitOrientationOf ξ Q → v ∈ Q → v ≠ 0 → (∀ α : Covector (Euclid P) n, ζ α = ξ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (‖v‖⁻¹ • v)).smulRight α))) → IsUnitOrientationOf ζ (Q ⊓ (ℝ ∙ v)ᗮ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

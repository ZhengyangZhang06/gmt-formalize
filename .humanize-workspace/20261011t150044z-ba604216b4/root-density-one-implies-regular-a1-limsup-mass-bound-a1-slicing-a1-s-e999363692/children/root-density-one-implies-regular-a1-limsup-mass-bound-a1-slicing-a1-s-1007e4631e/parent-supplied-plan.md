# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-1007e4631e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `wedge_orientation`
- Declaration: `Submission.dor_lmbsf_interior_product_orientation`
- Exact Lean type: `∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (ζ' : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), IsUnitOrientationOf ζ Q → ν ∈ Q → ‖ν‖ = 1 → (∀ α : Covector (Euclid P) n, ζ' α = ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α))) → IsUnitOrientationOf ζ' (Q ⊓ (ℝ ∙ ν)ᗮ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

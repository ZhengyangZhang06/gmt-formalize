# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.wedge_vector-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-5a530448f8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child key: `wedge_vector`
- Declaration: `Submission.dor_lmbsf_ll_wedge_representing_vector`
- Exact Lean type: `∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (α : Covector (Euclid P) n), (∀ β : Euclid P →L[ℝ] ℝ, ζ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α)) = β (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ))) ∧ ∀ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf ζ Q → (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ)) ∈ Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

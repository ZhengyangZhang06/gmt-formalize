# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.slice_orientation_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-fea55503c2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child key: `slice_orientation_field`
- Declaration: `Submission.dor_lmbsf_si_slice_orientation_field`
- Exact Lean type: `∀ (P n : ℕ) (ζ : Euclid P → MultiVector P (n + 1)) (g : Euclid P → Euclid P), StronglyMeasurable ζ → Measurable g → ∃ ζ' : Euclid P → MultiVector P n, StronglyMeasurable ζ' ∧ (∀ x (α : Covector (Euclid P) n), ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (‖g x‖⁻¹ • g x)).smulRight α))) ∧ (∀ x (α : Covector (Euclid P) n), ‖g x‖ * ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))) ∧ ∀ x (α : Covector (Euclid P) n), |ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))| ≤ ((n : ℝ) + 1) * ‖ζ x‖ * ‖g x‖ * ‖α‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

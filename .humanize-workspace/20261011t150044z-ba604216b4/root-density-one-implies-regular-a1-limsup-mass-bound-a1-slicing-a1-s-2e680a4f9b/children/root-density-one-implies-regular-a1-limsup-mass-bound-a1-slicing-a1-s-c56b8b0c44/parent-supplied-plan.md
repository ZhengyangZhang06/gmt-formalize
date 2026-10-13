# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.tangent_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-c56b8b0c44/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child key: `tangent_field`
- Declaration: `Submission.dor_lmbsf_ll_tangent_wedge_field`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U (n + 1)) (ω : DifferentialForm (Euclid P) n) (B : ℝ), Continuous ω → (∀ x, ‖ω x‖ ≤ B) → ∃ (W : Euclid P → Euclid P) (c' : ℝ), Measurable W ∧ (∀ x, ω x = 0 → W x = 0) ∧ (∀ x, ‖W x‖ ≤ c') ∧ ∀ᵐ x ∂(μHE[n + 1].restrict R.carrier), W x ∈ approxTangentPlane (n + 1) R.carrier x ∧ ∀ β : Euclid P →L[ℝ] ℝ, R.orient x (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight (ω x))) = β (W x)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.orient_approx_tangent_plane-a1`
- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_norm_bound-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.wedge_vector-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

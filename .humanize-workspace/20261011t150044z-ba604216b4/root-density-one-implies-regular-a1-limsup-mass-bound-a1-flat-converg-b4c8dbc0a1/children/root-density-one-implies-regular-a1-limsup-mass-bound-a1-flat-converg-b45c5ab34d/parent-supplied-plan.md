# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1.cube_chain_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-b45c5ab34d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation_top-a1`
- Child key: `cube_chain_im`
- Declaration: `Submission.dor_lmb_fc_dtop_cube_chain_im`
- Exact Lean type: `∀ (m : ℕ) (ρ : ℝ) (s : Finset (Fin (m + 1) → ℤ)) (β : (Fin (m + 1) → ℤ) → ℤ) (X : GeometricCurrentOn (univ : Set (Euclid (m + 1))) (m + 1)), 0 < ρ → (∀ ω : TestFormOn (univ : Set (Euclid (m + 1))) (m + 1), X ω = ∑ z ∈ s, (β z : ℝ) * ∫ x in {x : Euclid (m + 1) | ∀ i : Fin (m + 1), ρ * z i ≤ x i ∧ x i ≤ ρ * (z i + 1)}, (ω : DifferentialForm (Euclid (m + 1)) (m + 1)) x (fun k => EuclideanSpace.single k (1 : ℝ)) ∂μHE[m + 1]) → IsIntegerMultiplicity X`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

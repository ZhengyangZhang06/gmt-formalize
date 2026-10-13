# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.competitor_mass-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-co-4ad1f13c76/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1`
- Child key: `competitor_mass`
- Declaration: `Submission.dor_lmb_pc_competitor_massOn_le`
- Exact Lean type: `∀ (P n : ℕ) (U G O : Set (Euclid P)) (RZ RX RY : IMRep U n) (Y S : GeometricCurrentOn U n) (f : Euclid P → Euclid P) (Λ : ℝ), IsOpen U → IsOpen G → CompactlyContained G U → IsOpen O → G ⊆ O → ContDiffOn ℝ 1 f O → 0 ≤ Λ → (∀ x ∈ G, ‖fderiv ℝ f x‖ ≤ Λ) → RY.Represents Y → (∀ ω : TestFormOn U n, Y ω = RZ.action (ω : DifferentialForm (Euclid P) n) + RX.action (ω : DifferentialForm (Euclid P) n)) → (∀ᵐ x ∂(μHE[n].restrict (RZ.carrier ∩ G)), f x = x ∧ ∀ α : Covector (Euclid P) n, RZ.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = RZ.orient x α) → μHE[n] (RX.carrier \ G) = 0 → (∀ ω : TestFormOn U n, S ω = RZ.action (ω : DifferentialForm (Euclid P) n) + ∫ x in RX.carrier, (RX.mult x : ℝ) * RX.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → S.massOn G ≤ ENNReal.ofReal (Λ ^ n) * RY.measure G`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.projected_comparison-a1.orient_comp-a1`
- `root.regular_set_dense-a1.integer_combination-a1.combination_construction-a1`
- `root.regular_set_dense-a1.integer_combination-a1.combination_action-a1`
- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.vector_density_ae_eq-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

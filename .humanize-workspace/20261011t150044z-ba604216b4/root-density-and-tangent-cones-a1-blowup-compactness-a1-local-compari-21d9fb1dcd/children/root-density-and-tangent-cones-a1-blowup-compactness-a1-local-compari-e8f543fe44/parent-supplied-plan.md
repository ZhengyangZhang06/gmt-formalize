# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.localize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-e8f543fe44/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1`
- Child key: `localize`
- Declaration: `Submission.dtc_bc_lc_fd_localize`
- Exact Lean type: `∀ (P m : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (W : Set (Euclid P)), Bornology.IsBounded W → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ V : Set (Euclid P), IsOpen V → Bornology.IsBounded V → ⨆ j, ((Ts j).massOn V + (Ts j).boundary.massOn V) < ∞) → ∃ (K : Set (Euclid P)) (φ : ℕ → ℕ) (Λ : NNReal) (Ts' : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K ∧ StrictMono φ ∧ (∀ j, IsIntegerMultiplicity (Ts' j)) ∧ (∀ j, (Ts' j).support ⊆ K) ∧ (∀ j, (Ts' j).mass ≤ Λ ∧ (Ts' j).boundary.mass ≤ Λ) ∧ ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ W → Ts' j ω = Ts (φ j) ω`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.im_calculus-a1`
- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`
- `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1`
- `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_of_vanishing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

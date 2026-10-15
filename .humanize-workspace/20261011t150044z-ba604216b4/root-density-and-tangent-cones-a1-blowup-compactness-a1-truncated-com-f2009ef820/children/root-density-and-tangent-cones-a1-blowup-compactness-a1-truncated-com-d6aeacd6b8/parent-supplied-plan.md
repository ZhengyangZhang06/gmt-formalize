# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1.local_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-d6aeacd6b8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1`
- Child key: `local_bound`
- Declaration: `Submission.dtc_bc_tc_wc_local_bound`
- Exact Lean type: `∀ (P n : ℕ) (Ts : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ W : Set (Euclid P), IsOpen W → Bornology.IsBounded W → ⨆ j, (Ts j).massOn W < ∞) → ∀ K : Set (Euclid P), IsCompact K → ∃ c : ℝ, 0 ≤ c ∧ ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |Ts j ω| ≤ c * s`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`
- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1.norm_props-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1.limit_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-6d1b215581/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.weak_compactness-a1`
- Child key: `limit_current`
- Declaration: `Submission.dtc_bc_tc_wc_limit_current`
- Exact Lean type: `∀ (P n : ℕ) (S : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ K : Set (Euclid P), IsCompact K → ∃ c : ℝ, 0 ≤ c ∧ ∀ (i : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |S i ω| ≤ c * s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ L : ℝ, Tendsto (fun i => S i ω) atTop (𝓝 L)) → ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, WeaklyConvergesOn S C`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.restrict_current-a1.order_zero_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

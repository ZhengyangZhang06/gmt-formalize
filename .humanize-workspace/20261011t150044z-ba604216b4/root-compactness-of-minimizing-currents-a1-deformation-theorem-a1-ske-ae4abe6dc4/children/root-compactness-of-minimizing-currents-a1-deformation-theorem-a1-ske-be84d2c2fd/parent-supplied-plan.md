# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1.mass_eval-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-be84d2c2fd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.telescoping_deformation-a1`
- Child key: `mass_eval`
- Declaration: `Submission.cmcsdtd_mass_controls_eval`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), (Tendsto (fun j => (X j).mass) atTop (𝓝 0) → ∀ ω : TestFormOn U n, Tendsto (fun j => X j ω) atTop (𝓝 0)) ∧ (∑' j, (X j).mass < ∞ → (∀ ω : TestFormOn U n, Summable (fun j => X j ω)) ∧ ∀ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun j => X j ω) (Y ω)) → Y.mass ≤ ∑' j, (X j).mass)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.series_current-a1.coeff_bound-a1`
- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.eval_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

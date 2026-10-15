# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.tangent_complement_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-81790968d5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child key: `tangent_complement_density`
- Declaration: `Submission.dtc_bc_lc_sl_co_tangent_complement_density`
- Exact Lean type: `∀ (P N : ℕ) (A M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), MeasurableSet A → A ⊆ M → 0 < s → μHE[N] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt N M x Q → HasApproximateTangentSpaceAt N A x Q → Tendsto (fun r : ℝ => μHE[N] ((M \ A) ∩ ball x r) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.regular_set_dense-a1.density_eq_multiplicity-a1.unweighted_density_one-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

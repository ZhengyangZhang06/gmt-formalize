# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.jac_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-6ef28deb49/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1`
- Child key: `jac_algebra`
- Declaration: `Submission.dimred_mbl_pfi_gram_jacobian_algebra`
- Exact Lean type: `∀ (P n : ℕ) (A : Euclid n →L[ℝ] Euclid P), (∀ L : Euclid P →L[ℝ] Euclid P, Real.sqrt (((L ∘L A).adjoint ∘L (L ∘L A)).det) ≤ ‖L‖ ^ n * Real.sqrt ((A.adjoint ∘L A).det)) ∧ (∀ α : Covector (Euclid P) n, |α (fun j => A (EuclideanSpace.single j (1 : ℝ)))| ≤ Real.sqrt ((A.adjoint ∘L A).det) * ‖α‖) ∧ (Injective A → ∀ ξ : MultiVector P n, IsUnitOrientationOf ξ (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)) → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ α : Covector (Euclid P) n, Real.sqrt ((A.adjoint ∘L A).det) * ξ α = s * α (fun j => A (EuclideanSpace.single j (1 : ℝ))))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.injective_unit_orientation-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

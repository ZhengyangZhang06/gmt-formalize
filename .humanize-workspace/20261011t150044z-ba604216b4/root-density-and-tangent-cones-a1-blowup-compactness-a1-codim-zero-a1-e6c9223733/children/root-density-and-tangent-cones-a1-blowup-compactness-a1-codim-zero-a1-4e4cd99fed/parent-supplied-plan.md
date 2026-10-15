# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1.det_covector-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-4e4cd99fed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1`
- Child key: `det_covector`
- Declaration: `Submission.dtc_bc_cz_top_density_det_covector`
- Exact Lean type: `∀ n : ℕ, ∃ ε : Covector (Euclid n) n, ε ⇑(EuclideanSpace.basisFun (Fin n) ℝ) = 1 ∧ (∀ (α : Covector (Euclid n) n) (v : Fin n → Euclid n), α v = ε v * α ⇑(EuclideanSpace.basisFun (Fin n) ℝ)) ∧ ∀ τ : Fin n → Euclid n, Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = ⊤ → ε τ = 1 ∨ ε τ = -1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

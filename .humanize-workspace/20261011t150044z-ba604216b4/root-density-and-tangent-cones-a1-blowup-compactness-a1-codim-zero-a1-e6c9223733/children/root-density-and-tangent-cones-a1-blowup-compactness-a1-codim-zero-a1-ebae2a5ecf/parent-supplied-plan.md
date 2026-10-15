# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1.orient_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-ebae2a5ecf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1`
- Child key: `orient_sign`
- Declaration: `Submission.dtc_bc_cz_top_density_orient_sign`
- Exact Lean type: `∀ (n : ℕ) (V : Set (Euclid n)) (R : IMRep V n), ∃ σ : Euclid n → ℝ, Measurable σ ∧ ∀ᵐ y ∂(μHE[n].restrict R.carrier), (σ y = 1 ∨ σ y = -1) ∧ ∀ α : Covector (Euclid n) n, R.orient y α = σ y * α ⇑(EuclideanSpace.basisFun (Fin n) ℝ)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1.det_covector-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

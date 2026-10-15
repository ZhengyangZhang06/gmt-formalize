# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1.cylinder-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-e261229700/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.pushforward_calculus-a1`
- Child key: `cylinder`
- Declaration: `Submission.dor_lmb_fcdp_cylinder`
- Exact Lean type: `∀ (P k : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable k M → μHE[k] M ≠ ∞ → ∃ C : Set (Euclid (P + 1)), MeasurableSet C ∧ C ⊆ (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M) ∧ CountablyRectifiable (k + 1) C ∧ μHE[k + 1].restrict C = ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict M)).map (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) ∧ ∀ᵐ y ∂(μHE[k + 1].restrict C), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k M (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P) Q → HasApproximateTangentSpaceAt (k + 1) C y (Submodule.span ℝ (insert (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) ((fun v : Euclid P => (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Q : Set (Euclid P)))))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1.gram_area-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_pieces-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

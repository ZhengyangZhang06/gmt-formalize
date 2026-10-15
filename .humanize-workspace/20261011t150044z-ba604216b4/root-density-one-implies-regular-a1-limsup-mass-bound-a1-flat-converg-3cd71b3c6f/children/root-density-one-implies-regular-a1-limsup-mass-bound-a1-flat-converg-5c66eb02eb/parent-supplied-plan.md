# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1.piece_orientation_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-5c66eb02eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.im_pushforward-a1`
- Child key: `piece_orientation_sign`
- Declaration: `Submission.dor_lmb_fcd_imp_piece_orientation_sign`
- Exact Lean type: `∀ (N k : ℕ) (R : IMRep (univ : Set (Euclid N)) k) (G : Euclid k → Euclid N) (B : Set (Euclid k)) (L : NNReal) (κ : ℝ), μHE[k] R.carrier ≠ ∞ → LipschitzWith L G → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ B, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' B ⊆ R.carrier → ∃ s : Euclid k → ℝ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict B), ∀ α : Covector (Euclid N) k, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin k => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ G u (EuclideanSpace.single b (1 : ℝ))))) * R.orient (G u) α = s u * α (fun a => fderiv ℝ G u (EuclideanSpace.single a (1 : ℝ)))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.wedge_orientation-a1`
- `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

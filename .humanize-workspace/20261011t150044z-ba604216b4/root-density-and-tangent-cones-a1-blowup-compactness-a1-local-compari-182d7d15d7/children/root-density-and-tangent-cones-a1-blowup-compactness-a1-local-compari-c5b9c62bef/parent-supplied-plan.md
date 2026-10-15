# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.piece_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-c5b9c62bef/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1`
- Child key: `piece_orientation`
- Declaration: `Submission.dtc_bc_lc_pfi_piece_orientation_sign`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (κ : ℝ), IsOpen U → LipschitzWith L G → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∀ᵐ a ∂(volume.restrict A), ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ β : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ G a (EuclideanSpace.single k 1)) (fderiv ℝ G a (EuclideanSpace.single l 1)))) * R.orient (G a) β = σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1))`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.change_of_variables-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.pf_integer-a1.orient_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

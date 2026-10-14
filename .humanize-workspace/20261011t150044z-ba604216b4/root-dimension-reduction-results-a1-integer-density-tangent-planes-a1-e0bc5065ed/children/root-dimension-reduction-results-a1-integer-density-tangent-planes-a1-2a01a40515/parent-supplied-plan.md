# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1.flat_point_persists-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-2a01a40515/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1`
- Child key: `flat_point_persists`
- Declaration: `Submission.idtp_fons_cr_nusc_flat_point_persists`
- Exact Lean type: `∀ (P n : ℕ) (β : ℝ) (S Dset : Set (Euclid P)) (Ss Ds : ℕ → Set (Euclid P)), 0 < β → (∀ K : Set (Euclid P), IsCompact K → K ⊆ Dset → ∀ᶠ k in atTop, K ⊆ Ds k) → (∀ (sub : ℕ → ℕ) (z : ℕ → Euclid P) (x : Euclid P), StrictMono sub → (∀ k, z k ∈ Ss (sub k)) → Tendsto z atTop (𝓝 x) → x ∈ Dset → x ∈ S) → ∀ w : Euclid P, (∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s) → ∀ (σ : ℕ → ℕ) (v : ℕ → Euclid P), StrictMono σ → Tendsto v atTop (𝓝 w) → ∀ᶠ i in atTop, ∃ ρ : ℝ, 0 < ρ ∧ ball (v i) ρ ⊆ Ds (σ i) ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ Ss (σ i), y ∈ ball (v i) ρ → ‖(y - v i) - Q.starProjection (y - v i)‖ ≤ s`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1.flat_eventually-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

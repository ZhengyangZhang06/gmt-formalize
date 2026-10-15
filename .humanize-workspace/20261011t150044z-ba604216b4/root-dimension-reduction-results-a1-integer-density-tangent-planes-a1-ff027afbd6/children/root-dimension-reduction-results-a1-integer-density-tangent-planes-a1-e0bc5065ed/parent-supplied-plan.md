# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e0bc5065ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `nonflat_usc`
- Declaration: `Submission.idtp_fons_cr_nonflat_usc`
- Exact Lean type: `∀ (P n : ℕ) (β : ℝ) (S Dset : Set (Euclid P)) (Ss Ds : ℕ → Set (Euclid P)), 0 < β → closedBall (0 : Euclid P) 1 ⊆ Dset → (∀ k, ball (0 : Euclid P) 1 ⊆ Ds k) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ Dset → ∀ᶠ k in atTop, K ⊆ Ds k) → (∀ (sub : ℕ → ℕ) (z : ℕ → Euclid P) (x : Euclid P), StrictMono sub → (∀ k, z k ∈ Ss (sub k)) → Tendsto z atTop (𝓝 x) → x ∈ Dset → x ∈ S) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ (((Ss k ∩ Ds k) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Ds k ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ Ss k, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ (Ds k)ᶜ) ⊆ {x | ∃ z ∈ ((S ∩ Dset) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ Dsetᶜ, dist x z < ε}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

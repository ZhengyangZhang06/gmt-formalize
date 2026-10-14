# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1.nonflat_affine_preimage-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a620325f4a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.class_reduction-a1`
- Child key: `nonflat_affine_preimage`
- Declaration: `Submission.idtp_fons_cr_nonflat_affine_preimage`
- Exact Lean type: `∀ (P n : ℕ) (β : ℝ) (S Dset : Set (Euclid P)) (y₀ : Euclid P) (lam : ℝ), 0 < lam → ((((fun x => y₀ + lam • x) ⁻¹' S) ∩ ((fun x => y₀ + lam • x) ⁻¹' Dset)) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ ((fun x => y₀ + lam • x) ⁻¹' Dset) ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ ((fun x => y₀ + lam • x) ⁻¹' S), y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ ((fun x => y₀ + lam • x) ⁻¹' Dset)ᶜ = (fun x => y₀ + lam • x) ⁻¹' (((S ∩ Dset) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ Dsetᶜ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

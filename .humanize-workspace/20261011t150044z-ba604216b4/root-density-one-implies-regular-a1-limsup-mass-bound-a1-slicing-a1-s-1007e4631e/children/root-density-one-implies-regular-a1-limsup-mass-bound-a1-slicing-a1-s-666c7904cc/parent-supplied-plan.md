# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1.adapted_frame-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-666c7904cc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1`
- Child key: `adapted_frame`
- Declaration: `Submission.dor_lmbsf_io_adapted_frame`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), Module.finrank ℝ Q = n + 1 → ν ∈ Q → ‖ν‖ = 1 → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Q ⊓ (ℝ ∙ ν)ᗮ ∧ Orthonormal ℝ (Fin.cons ν σ : Fin (n + 1) → Euclid P) ∧ (∀ i, σ i ∈ Q) ∧ ∀ i, inner ℝ ν (σ i) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

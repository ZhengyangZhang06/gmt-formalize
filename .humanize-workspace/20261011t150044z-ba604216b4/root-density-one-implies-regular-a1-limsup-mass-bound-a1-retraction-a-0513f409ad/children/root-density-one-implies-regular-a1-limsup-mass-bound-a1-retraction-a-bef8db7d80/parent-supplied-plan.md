# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1.local_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-bef8db7d80/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1`
- Child key: `local_inverse`
- Declaration: `Submission.dor_lmb_ret_nc_local_inverse`
- Exact Lean type: `∀ (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (Φ : X → Y) (U : Set X) (z₀ : X) (Λ : X ≃L[ℝ] Y), IsOpen U → z₀ ∈ U → ContDiffOn ℝ 1 Φ U → HasFDerivAt Φ (Λ : X →L[ℝ] Y) z₀ → ∃ ρ : ℝ, 0 < ρ ∧ ball z₀ ρ ⊆ U ∧ ∃ G : Y → X, (∀ z ∈ ball z₀ ρ, G (Φ z) = z) ∧ ∀ W : Set X, W ⊆ ball z₀ ρ → IsOpen W → IsOpen (Φ '' W) ∧ ContDiffOn ℝ 1 G (Φ '' W)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

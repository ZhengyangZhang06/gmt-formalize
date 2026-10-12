# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.blowup_density-a1.plane_cutoff_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-blowup-density-a1-plane-cutoff-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.blowup_density-a1`
- Child key: `plane_cutoff_approx`
- Declaration: `Submission.ts_unit_ball_plane_cutoff_approx`
- Exact Lean type: `∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)), Module.finrank ℝ P = n → (∀ a : ℝ, a < omega n → ∃ g : C_c(Ambient n ℓ, ℝ), (∀ y : Ambient n ℓ, g y ≤ 1) ∧ (∀ y : Ambient n ℓ, 1 < ‖y‖ → g y ≤ 0) ∧ a < ∫ y in (P : Set (Ambient n ℓ)), g y ∂μHE[n]) ∧ (∀ b : ℝ, omega n < b → ∃ h : C_c(Ambient n ℓ, ℝ), (∀ y : Ambient n ℓ, 0 ≤ h y) ∧ (∀ y : Ambient n ℓ, ‖y‖ ≤ 1 → 1 ≤ h y) ∧ ∫ y in (P : Set (Ambient n ℓ)), h y ∂μHE[n] < b)`

## Sibling prerequisites

- `root.tangent_structure-a1.blowup_density-a1.plane_ball_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

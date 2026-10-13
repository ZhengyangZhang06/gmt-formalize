# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.nearest_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-898e4c7b39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1`
- Child key: `nearest_point`
- Declaration: `Submission.dor_lmb_ret_nearest_point`
- Exact Lean type: `∀ (P d : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen V → IsOpen W → ContDiffOn ℝ 2 ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v₀ ∈ V → ∃ (r δ : ℝ) (g : Euclid P → Euclid d), 0 < r ∧ 0 < δ ∧ closedBall v₀ δ ⊆ V ∧ ContDiffOn ℝ 1 g (ball (ψ v₀) r) ∧ MapsTo g (ball (ψ v₀) r) (ball v₀ δ) ∧ (∀ x ∈ ball (ψ v₀) r, ∀ z ∈ N, ‖x - ψ (g x)‖ ≤ ‖x - z‖) ∧ (∀ x ∈ ball (ψ v₀) r, (fderiv ℝ ψ (g x)).range.starProjection (x - ψ (g x)) = 0) ∧ ∀ x ∈ N ∩ ball (ψ v₀) r, ψ (g x) = x`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.chart_localization-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

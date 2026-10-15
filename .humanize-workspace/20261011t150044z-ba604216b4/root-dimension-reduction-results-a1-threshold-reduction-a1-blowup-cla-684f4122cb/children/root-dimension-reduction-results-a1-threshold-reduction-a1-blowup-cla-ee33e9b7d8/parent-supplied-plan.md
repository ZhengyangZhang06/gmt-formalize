# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1.uniform_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-ee33e9b7d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`
- Child key: `uniform_mass_bound`
- Declaration: `Submission.dimred_tr_bc_ct_uniform_mass_bound`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (z : Euclid P) (r Λ : ℝ), 0 < r → 0 ≤ Λ → (∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ closedBall z (2 * r) → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → T.massOn (ball z (2 * r)) ≠ ∞ → ∃ δ Γ : ℝ, 0 < δ ∧ ∀ b ∈ closedBall z r, ∀ x' ∈ ball b δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.abstract_dimension_reduction-a1.finite_of_dim_zero-a1.secant_rescaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-finite-of-dim-zero-a1-secant-rescaling-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.abstract_dimension_reduction-a1.finite_of_dim_zero-a1`
- Child key: `secant_rescaling`
- Declaration: `Submission.adr_secant_rescaling_of_infinite`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)) (σ : ℝ), σ < 1 → (S ∩ ball (0 : Euclid P) σ).Infinite → ∃ (x : Euclid P) (lams : ℕ → ℝ) (zs : ℕ → Euclid P) (z : Euclid P), ‖x‖ < 1 ∧ (∀ k, 0 < lams k) ∧ StrictAnti lams ∧ Tendsto lams atTop (𝓝 0) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ (∀ k, x + lams k • zs k ∈ S) ∧ (∀ k, ‖zs k‖ = 1 / 2) ∧ Tendsto zs atTop (𝓝 z) ∧ ‖z‖ = 1 / 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

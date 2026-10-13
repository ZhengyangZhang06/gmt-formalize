# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.ode_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-ode-lower-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1`
- Child key: `ode_lower_bound`
- Declaration: `Submission.deGiorgiDens_lower_bound_of_deriv`
- Exact Lean type: `∀ (n : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → MonotoneOn V (Ioo 0 ρ₁) → (∀ ρ ∈ Ioo 0 ρ₁, 0 < V ρ) → (∀ᵐ ρ ∂(volume : Measure ℝ), ρ ∈ Ioo 0 ρ₁ → ∃ d : ℝ, HasDerivAt V d ρ ∧ V ρ ^ ((n : ℝ) / (n + 1)) ≤ K * d) → ∀ ρ ∈ Ioo 0 ρ₁, (ρ / ((n + 1) * K)) ^ (n + 1) ≤ V ρ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

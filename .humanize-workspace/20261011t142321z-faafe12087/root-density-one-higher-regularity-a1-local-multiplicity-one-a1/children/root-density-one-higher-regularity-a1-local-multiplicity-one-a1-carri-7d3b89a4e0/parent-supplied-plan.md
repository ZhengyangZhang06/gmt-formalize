# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.carrier_graph_symmdiff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-carri-7d3b89a4e0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `carrier_graph_symmdiff`
- Declaration: `Submission.dohr_lmo_carrier_graph_symmDiff`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (M S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R s : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), s ≤ R → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (M ∩ ball ξ s) (S ∩ ball ξ s)) = 0 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' M) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

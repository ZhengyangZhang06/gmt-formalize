# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1.fderiv_setintegral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mollified-c34f9b4b00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mollified_fderiv_le-a1`
- Child key: `fderiv_setintegral`
- Declaration: `Submission.deGiorgiSobIndMFL_fderiv_setIntegral_apply`
- Exact Lean type: `∀ (N : ℕ) (G : Set (Rn N)) (ρ : Rn N → ℝ), NullMeasurableSet G volume → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x w : Rn N, fderiv ℝ (fun x ↦ ∫ z in G, ρ (x - z)) x w = ∫ z in G, fderiv ℝ ρ (x - z) w`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

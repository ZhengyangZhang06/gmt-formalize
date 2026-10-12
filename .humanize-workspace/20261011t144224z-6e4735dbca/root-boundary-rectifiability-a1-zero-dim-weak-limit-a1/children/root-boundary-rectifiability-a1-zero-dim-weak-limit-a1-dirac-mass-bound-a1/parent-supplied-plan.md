# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-dirac-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`
- Child key: `dirac_mass_bound`
- Declaration: `Submission.br_zd_dirac_massOn_ge`
- Exact Lean type: `∀ (P : ℕ) (U W N : Set (Eucl P)) (Y : GeometricCurrentOn U 0) (c : Eucl P → ℤ), IsOpen W → W ⊆ U → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → (N ∩ K).Finite) → (∀ ω : TestFormOn U 0, Y ω = ∑ᶠ x ∈ N, (c x : ℝ) * (ω : DifferentialForm (Eucl P) 0) x ![]) → ∀ S : Finset (Eucl P), (↑S : Set (Eucl P)) ⊆ N ∩ W → ENNReal.ofReal (∑ x ∈ S, |(c x : ℝ)|) ≤ Y.massOn W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

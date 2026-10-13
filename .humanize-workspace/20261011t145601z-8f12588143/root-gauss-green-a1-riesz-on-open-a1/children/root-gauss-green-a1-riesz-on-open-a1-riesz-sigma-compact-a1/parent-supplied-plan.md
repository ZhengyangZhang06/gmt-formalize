# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.riesz_on_open-a1.riesz_sigma_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-riesz-on-open-a1-riesz-sigma-compact-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.riesz_on_open-a1`
- Child key: `riesz_sigma_compact`
- Declaration: `Submission.gaussGreenRep_riesz_sigmaCompact_borel`
- Exact Lean type: `∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (N : ℕ) (L : C_c(X, Rn N) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ C : ℝ, ∀ f : C_c(X, Rn N), (∀ x, ‖f x‖ ≤ 1) → tsupport f ⊆ K → L f ≤ C) → ∃ (μ : Measure X) (ν : X → Rn N), (∀ K : Set X, IsCompact K → μ K < ∞) ∧ StronglyMeasurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ f : C_c(X, Rn N), L f = ∫ x, inner ℝ (f x) (ν x) ∂μ`

## Sibling prerequisites

- `root.gauss_green-a1.riesz_on_open-a1.caratheodory_borel_version-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

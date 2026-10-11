# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.riesz_on_open-a1.pushforward_from_subset-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-riesz-on-open-a1-pushforward-from-subset-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.riesz_on_open-a1`
- Child key: `pushforward_from_subset`
- Declaration: `Submission.gaussGreenRep_riesz_pushforward_subtype`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (μ₀ : Measure U) (ν₀ : U → Rn N), MeasurableSet U → (∀ K : Set U, IsCompact K → μ₀ K < ∞) → AEStronglyMeasurable ν₀ μ₀ → (∀ᵐ y ∂μ₀, ‖ν₀ y‖ = 1) → ∃ (μ : Measure (Rn N)) (ν : Rn N → Rn N), μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ g : Rn N → Rn N, ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ y, inner ℝ (g ↑y) (ν₀ y) ∂μ₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

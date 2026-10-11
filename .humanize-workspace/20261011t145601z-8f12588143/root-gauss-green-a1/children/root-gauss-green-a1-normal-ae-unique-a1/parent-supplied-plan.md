# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.normal_ae_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-normal-ae-unique-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `normal_ae_unique`
- Declaration: `Submission.gaussGreenRep_normal_ae_eq_of_pairing`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (μ : Measure (Rn N)) (ν ν' : Rn N → Rn N), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ν μ → AEStronglyMeasurable ν' μ → (∀ᵐ x ∂μ, ‖ν x‖ ≤ 1) → (∀ᵐ x ∂μ, ‖ν' x‖ ≤ 1) → (∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ x, inner ℝ (g x) (ν' x) ∂μ) → ν =ᵐ[μ] ν'`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

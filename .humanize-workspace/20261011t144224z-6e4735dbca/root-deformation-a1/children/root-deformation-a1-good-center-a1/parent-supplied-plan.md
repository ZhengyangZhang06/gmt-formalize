# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `good_center`
- Declaration: `Submission.deformation_good_center`
- Exact Lean type: `∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ μ₁ μ₂ : Measure (Eucl (m + 1 + ℓ)), IsFiniteMeasure μ₁ → IsFiniteMeasure μ₂ → ∃ a : Eucl (m + 1 + ℓ), ∑ i, (a i - 1 / 2) ^ 2 < 1 / 16 ∧ ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → μ₁ {x | infDist x La < σ} ≤ c * ENNReal.ofReal (σ ^ (m + 2)) * μ₁ univ ∧ μ₂ {x | infDist x La < σ} ≤ c * ENNReal.ofReal (σ ^ (m + 2)) * μ₂ univ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

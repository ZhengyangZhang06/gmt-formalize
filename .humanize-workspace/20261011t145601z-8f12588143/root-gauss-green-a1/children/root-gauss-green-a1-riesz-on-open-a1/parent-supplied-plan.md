# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.riesz_on_open-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-riesz-on-open-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `riesz_on_open`
- Declaration: `Submission.gaussGreenRep_riesz_on_open`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)) (Λ : (Rn N → Rn N) → ℝ), IsOpen U → (∀ g h : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Continuous h → HasCompactSupport h → tsupport h ⊆ U → Λ (g + h) = Λ g + Λ h) → (∀ (c : ℝ) (g : Rn N → Rn N), Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (c • g) = c * Λ g) → (∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ g : Rn N → Rn N, Continuous g → tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → Λ g ≤ C) → ∃ (μ : Measure (Rn N)) (ν : Rn N → Rn N), μ Uᶜ = 0 ∧ (∀ K : Set (Rn N), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ν μ ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧ ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ g = ∫ x, inner ℝ (g x) (ν x) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

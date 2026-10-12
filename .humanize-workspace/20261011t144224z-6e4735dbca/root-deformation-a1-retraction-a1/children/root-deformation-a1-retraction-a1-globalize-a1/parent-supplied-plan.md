# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.retraction-a1.globalize-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-globalize-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.retraction-a1`
- Child key: `globalize`
- Declaration: `Submission.deformation_retraction_globalize`
- Exact Lean type: `∀ (N : ℕ) (c₁ : ℝ), 0 ≤ c₁ → ∃ c : ℝ≥0, ∀ (L : Set (Eucl N)) (ψ : Eucl N → Eucl N), (∀ (z : Fin N → ℤ) (x : Eucl N), x ∉ L → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, (z i : ℝ) ≤ ψ x i ∧ ψ x i ≤ z i + 1) → (∀ (z : Fin N → ℤ) (x : Eucl N), x ∉ L → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl N, x' ∉ L → (∀ i, (z i : ℝ) ≤ x' i ∧ x' i ≤ z i + 1) → dist x' x < δ → dist (ψ x') (ψ x) ≤ (c₁ / infDist x L + ε) * dist x' x) → ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 → LipschitzOnWith (c / Real.toNNReal σ) ψ {x | σ ≤ infDist x L}`

## Sibling prerequisites

- `root.deformation-a1.retraction-a1.dini_segment-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.variation_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-variation-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `variation_formula`
- Declaration: `Submission.gaussGreenRep_measure_eq_iSup_pairing`
- Exact Lean type: `∀ (N : ℕ) (O : Set (Rn N)) (μ : Measure (Rn N)) (ν : Rn N → Rn N), IsOpen O → (∀ K : Set (Rn N), IsCompact K → K ⊆ O → μ K < ∞) → AEStronglyMeasurable ν μ → (∀ᵐ x ∂μ, ‖ν x‖ = 1) → μ O = ⨆ (g : Rn N → Rn N) (_ : Continuous g) (_ : HasCompactSupport g) (_ : tsupport g ⊆ O) (_ : ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (∫ x, inner ℝ (g x) (ν x) ∂μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

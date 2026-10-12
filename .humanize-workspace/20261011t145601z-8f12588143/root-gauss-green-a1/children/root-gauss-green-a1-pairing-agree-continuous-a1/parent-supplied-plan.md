# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.pairing_agree_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-pairing-agree-continuous-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `pairing_agree_continuous`
- Declaration: `Submission.gaussGreenRep_pairing_eq_continuous`
- Exact Lean type: `∀ (N : ℕ) (U E : Set (Rn N)) (μ μ' : Measure (Rn N)) (ν ν' : Rn N → Rn N), IsOpen U → IsGaussGreenPair U E μ ν → IsGaussGreenPair U E μ' ν' → ∀ g : Rn N → Rn N, Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, inner ℝ (g x) (ν x) ∂μ = ∫ x, inner ℝ (g x) (ν' x) ∂μ'`

## Sibling prerequisites

- `root.gauss_green-a1.c1_uniform_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

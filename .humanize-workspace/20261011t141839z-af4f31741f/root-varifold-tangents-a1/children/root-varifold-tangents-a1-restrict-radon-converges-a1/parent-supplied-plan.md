# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.restrict_radon_converges-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-restrict-radon-converges-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1`
- Child key: `restrict_radon_converges`
- Declaration: `Submission.varifold_tangents_restricted_radon_converges`
- Exact Lean type: `∀ (N n : ℕ) (Ω : Set (Euclidean N)) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (Ws : ℕ → Varifold N n Ω) (W : Varifold N n Ω) (c : ℝ≥0∞), VagueConverges μs μ → c ≠ ∞ → (∀ i, (Ws i).measure = c • (μs i).restrict (Ω ×ˢ (univ : Set (Grassmannian N n)))) → W.measure = c • μ.restrict (Ω ×ˢ (univ : Set (Grassmannian N n))) → Varifold.RadonConverges Ws W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

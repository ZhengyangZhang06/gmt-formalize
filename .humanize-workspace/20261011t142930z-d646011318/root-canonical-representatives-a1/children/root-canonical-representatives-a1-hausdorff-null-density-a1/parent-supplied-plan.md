# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_representatives-a1.hausdorff_null_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1-hausdorff-null-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_representatives-a1`
- Child key: `hausdorff_null_density`
- Declaration: `Submission.hausdorff_null_of_measure_null_density_ge`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (A : Set (Ambient n ℓ)) (t : ℝ), 0 < n → IsFiniteMeasureOnCompacts μ → 0 < t → μ A = 0 → (∀ x ∈ A, ∃ s : ℝ, t ≤ s ∧ Tendsto (fun ρ ↦ μ.real (closedBall x ρ) / (omega n * ρ ^ n)) (𝓝[>] 0) (𝓝 s)) → (μHE[n] : Measure (Ambient n ℓ)) A = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

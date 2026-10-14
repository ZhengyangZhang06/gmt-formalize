# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.local_comparison-a1.lipschitz_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-lipsch-80245fc994/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child key: `lipschitz_cutoff`
- Declaration: `Submission.lcmp_exists_lipschitz_cutoff`
- Exact Lean type: `∀ (P : ℕ) (U K : Set (Euclid P)) (ε : ℝ), IsOpen U → IsCompact K → K ⊆ U → 0 < ε → ∃ (ψ : Euclid P → ℝ) (L : NNReal), LipschitzWith L ψ ∧ (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧ (∀ x ∈ K, ψ x = 1) ∧ {x | 0 < ψ x} ⊆ thickening ε K ∧ CompactlyContained {x | 0 < ψ x} U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

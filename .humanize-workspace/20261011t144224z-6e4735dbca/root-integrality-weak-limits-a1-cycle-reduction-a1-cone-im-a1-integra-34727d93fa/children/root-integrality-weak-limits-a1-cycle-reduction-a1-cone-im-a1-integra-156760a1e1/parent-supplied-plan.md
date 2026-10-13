# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.finite_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-156760a1e1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child key: `finite_measure`
- Declaration: `Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (K : Set (Eucl P)), IsRectifiableTriple U n M θ ξ → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → IsCompact K → K ⊆ U → (μHE[n] : Measure (Eucl P)) (M ∩ K) < ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

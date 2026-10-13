# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1-9cae75a529/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child key: `integrand_bound`
- Declaration: `Submission.iwl_cr_ro_integrand_iteratedFDeriv_le`
- Exact Lean type: `∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

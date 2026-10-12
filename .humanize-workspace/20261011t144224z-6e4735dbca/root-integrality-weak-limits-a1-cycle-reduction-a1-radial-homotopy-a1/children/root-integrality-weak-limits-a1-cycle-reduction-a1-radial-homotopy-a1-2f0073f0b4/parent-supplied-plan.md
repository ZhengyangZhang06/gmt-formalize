# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.degree_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-2f0073f0b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- Child key: `degree_zero`
- Declaration: `Submission.iwl_cr_rh_degree_zero`
- Exact Lean type: `∀ (P : ℕ) (φ χ : DifferentialForm (Eucl P) 0), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ (x : Eucl P) (v : Fin 0 → Eucl P), χ x v = ∫ t in (0 : ℝ)..1, t ^ 0 * extDeriv φ (t • x) (Fin.cons x v)) → ∀ x, χ x = φ x - φ 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.radial_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-803e557495/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- Child key: `radial_ftc`
- Declaration: `Submission.iwl_cr_rh_radial_ftc`
- Exact Lean type: `∀ (P n m : ℕ) (φ : DifferentialForm (Eucl P) n), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (x : Eucl P) (u : Fin n → Eucl P), ∫ t in (0 : ℝ)..1, (t ^ (m + 1) * fderiv ℝ φ (t • x) x u + ((m : ℝ) + 1) * t ^ m * φ (t • x) u) = φ x u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

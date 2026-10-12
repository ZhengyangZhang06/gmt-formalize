# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.integrand_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-b30921add2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- Child key: `integrand_identity`
- Declaration: `Submission.iwl_cr_rh_integrand_identity`
- Exact Lean type: `∀ (P k : ℕ) (L : Eucl P →L[ℝ] Covector (Eucl P) (k + 1)) (α : Covector (Eucl P) (k + 1)) (x : Eucl P) (u : Fin (k + 1) → Eucl P) (t : ℝ), t ^ (k + 1) * ContinuousAlternatingMap.alternatizeUncurryFin L (Fin.cons x u) + ∑ j : Fin (k + 1), (-1 : ℝ) ^ (j : ℕ) * (t ^ k * (t * L (u j) (Fin.cons x (Fin.removeNth j u)) + α (Fin.cons (u j) (Fin.removeNth j u)))) = t ^ (k + 1) * L x u + ((k : ℝ) + 1) * t ^ k * α u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

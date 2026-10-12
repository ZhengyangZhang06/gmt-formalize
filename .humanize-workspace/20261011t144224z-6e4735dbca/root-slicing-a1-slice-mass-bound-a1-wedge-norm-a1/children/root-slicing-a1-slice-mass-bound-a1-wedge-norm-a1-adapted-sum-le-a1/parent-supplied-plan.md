# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_sum_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-adapted-sum-le-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`
- Child key: `adapted_sum_le`
- Declaration: `Submission.slicing_mb_wn_adapted_sum_le`
- Exact Lean type: `∀ (P m : ℕ) (α : Eucl P →L[ℝ] ℝ) (γ : Covector (Eucl P) m) (u : Fin P → Eucl P) (c : ℝ), (∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then c else 0) → (∑ I : Fin (m + 1) → Fin P, if StrictMono I then (ContinuousAlternatingMap.alternatizeUncurryFin (α.smulRight γ) (fun i => u (I i))) ^ 2 else 0) ≤ c ^ 2 * ∑ I : Fin m → Fin P, if StrictMono I then (γ (fun i => u (I i))) ^ 2 else 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

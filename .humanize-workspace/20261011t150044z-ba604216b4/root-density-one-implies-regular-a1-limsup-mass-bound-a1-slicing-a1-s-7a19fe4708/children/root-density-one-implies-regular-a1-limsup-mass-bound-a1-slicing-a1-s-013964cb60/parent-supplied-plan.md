# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1.ae_forall_compact-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-013964cb60/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Child key: `ae_forall_compact`
- Declaration: `Submission.dor_lmbsf_si_ae_forall_compact`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (F : ℝ → Set (Euclid P) → ℝ≥0∞), IsOpen U → (∀ t, Monotone (F t)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∀ᵐ t, F t K ≠ ∞) → ∀ᵐ t, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → F t K ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

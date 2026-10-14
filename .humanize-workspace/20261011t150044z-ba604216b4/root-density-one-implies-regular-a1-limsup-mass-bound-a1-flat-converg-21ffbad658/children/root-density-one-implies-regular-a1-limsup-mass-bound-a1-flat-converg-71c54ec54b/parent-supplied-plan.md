# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1.cube_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-71c54ec54b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1`
- Child key: `cube_selection`
- Declaration: `Submission.dor_lmb_fcd_gc_cube_selection`
- Exact Lean type: `∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1.immersion_injective-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-7ed7fc33b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- Child key: `immersion_injective`
- Declaration: `Submission.dor_lmbsf_c1c_immersion_local_injOn`
- Exact Lean type: `∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Set.InjOn G (Metric.closedBall x r) ∧ ∀ z ∈ Metric.closedBall x r, Function.Injective (fderiv ℝ G z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

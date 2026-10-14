# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1.c1_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-156708e486/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1`
- Child key: `c1_extension`
- Declaration: `Submission.dor_lmbsf_cit_c1_local_extension`
- Exact Lean type: `∀ (P k : ℕ) (W : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen W → ContDiffOn ℝ 1 χ W → y ∈ W → ∃ (g : Euclid k → Euclid P) (ε : ℝ), 0 < ε ∧ ball y ε ⊆ W ∧ ContDiff ℝ 1 g ∧ EqOn g χ (ball y ε)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

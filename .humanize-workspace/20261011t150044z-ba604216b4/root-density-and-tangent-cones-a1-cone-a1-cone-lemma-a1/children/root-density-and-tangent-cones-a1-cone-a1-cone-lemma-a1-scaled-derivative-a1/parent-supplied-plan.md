# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.scaled_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1-scaled-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child key: `scaled_derivative`
- Declaration: `Submission.dtc_cwv_scaled_action_hasDerivAt`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (t : ℝ), 0 < t → HasDerivAt (fun s : ℝ => R.action (fun y => (s ^ n) • (ω : DifferentialForm (Euclid P) n) (s • y))) (R.action (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) + (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y)) t`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.orientation_norm_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

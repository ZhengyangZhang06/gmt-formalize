# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.slice_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-f3a94ebf1a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `slice_deriv`
- Declaration: `Submission.dimred_cs_sos_mt_cs_slice_hasDerivAt`
- Exact Lean type: `∀ (P q n' : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid P)) q) (RY : IMRep (univ : Set (Euclid P)) q) (Φ : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) q) (ω : TestFormOn (univ : Set (Euclid P)) n') (s v : Euclid P) (τ : ℝ), RY.Represents Y → HasDerivAt (fun σ : ℝ => currentEval Y (fun y => Φ ((ω : DifferentialForm (Euclid P) n') (s + σ • v + y)))) (currentEval Y (fun y => fderiv ℝ (fun z => Φ ((ω : DifferentialForm (Euclid P) n') z)) (s + τ • v + y) v)) τ`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.fderiv_test_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

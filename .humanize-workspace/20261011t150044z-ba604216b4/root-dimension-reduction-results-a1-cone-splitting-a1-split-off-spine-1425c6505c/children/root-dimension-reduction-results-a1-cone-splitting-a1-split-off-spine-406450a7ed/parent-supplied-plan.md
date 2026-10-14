# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1.translate_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-406450a7ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1`
- Child key: `translate_imrep`
- Declaration: `Submission.dimred_cs_sos_mt_fc_translate_imrep`
- Exact Lean type: `∀ (P n : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid P)) n) (RA : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), RA.Represents A → ∃ (Av : GeometricCurrentOn (univ : Set (Euclid P)) n) (Rv : IMRep (univ : Set (Euclid P)) n), Rv.Represents Av ∧ (∀ φ : DifferentialForm (Euclid P) n, currentEval Av φ = currentEval A (fun y => φ (y + v))) ∧ ∀ C : Set (Euclid P), MeasurableSet C → Rv.measure C = RA.measure ((fun y => y + v) ⁻¹' C)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

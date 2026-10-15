# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1.box_face-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-658e44fabc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1`
- Child key: `box_face`
- Declaration: `Submission.dimred_cs_sos_mt_fc_box_face`
- Exact Lean type: `∀ (P k m' n' : ℕ) (f : Fin k → Euclid P) (h : n' = k + m') (w : Euclid P) (Y : GeometricCurrentOn (univ : Set (Euclid P)) m') (RY : IMRep (univ : Set (Euclid P)) m') (r : ℝ), 0 < m' → Orthonormal ℝ f → w ∈ (Submodule.span ℝ (Set.range f))ᗮ → RY.Represents Y → RY.measure ((Submodule.span ℝ (Set.range f))ᗮ : Set (Euclid P))ᶜ = 0 → 0 < r → ∃ B : GeometricCurrentOn (univ : Set (Euclid P)) n', IsIntegerMultiplicity B ∧ B.mass = ENNReal.ofReal ((2 * r) ^ k) * RY.measure univ ∧ ∀ flat : Covector (Euclid P) n' → Covector (Euclid P) m', (∀ (α : Covector (Euclid P) n') (v : Fin m' → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n', B ω = ∫ s in {s | s ∈ Submodule.span ℝ (Set.range f) ∧ ∀ c, |inner ℝ (f c) s| ≤ r}, currentEval Y (fun y => flat ((ω : DifferentialForm (Euclid P) n') (s + w + y))) ∂μHE[k]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1.translate_imrep-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

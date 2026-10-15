# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.slice_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-bd4f539c89/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `slice_identity`
- Declaration: `Submission.dimred_cs_sos_mt_cs_slice_identity`
- Exact Lean type: `∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) n') (t : Euclid P), Y.boundary = X → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → currentEval Y (fun y => flatD (exteriorDerivative (ω : DifferentialForm (Euclid P) n') (t + y))) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) * currentEval Y (fun y => fderiv ℝ (fun z => flatF a ((ω : DifferentialForm (Euclid P) n') z)) (t + y) (g a)) + (-1 : ℝ) ^ (j + 1) * currentEval X (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.fderiv_test_form-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.flat_extderiv_split-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.translate_boundary-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

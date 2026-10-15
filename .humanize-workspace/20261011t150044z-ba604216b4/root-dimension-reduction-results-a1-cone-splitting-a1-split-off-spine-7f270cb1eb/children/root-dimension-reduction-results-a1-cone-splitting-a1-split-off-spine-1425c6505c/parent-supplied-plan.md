# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.face_currents-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-1425c6505c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `face_currents`
- Declaration: `Submission.dimred_cs_sos_mt_face_currents`
- Exact Lean type: `∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h₂ : n' = j + (m + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (RY : IMRep (univ : Set (Euclid P)) (m + 1)) (r : ℝ), Orthonormal ℝ g → RY.Represents Y → RY.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → 0 < r → ∃ E' : GeometricCurrentOn (univ : Set (Euclid P)) n', IsIntegerMultiplicity E' ∧ E'.mass ≤ ENNReal.ofReal (2 * ((j : ℝ) + 1) * (2 * r) ^ j) * RY.measure univ ∧ ∀ flatF : Fin (j + 1) → Covector (Euclid P) n' → Covector (Euclid P) (m + 1), (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n', E' ω = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) * ((∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, currentEval Y (fun y => flatF a ((ω : DifferentialForm (Euclid P) n') (s + r • g a + y))) ∂μHE[j]) - ∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, currentEval Y (fun y => flatF a ((ω : DifferentialForm (Euclid P) n') (s - r • g a + y))) ∂μHE[j])`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1`
- `root.compactness_of_minimizing_currents-a1.local_comparison-a1.mass_triangle-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.frame_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

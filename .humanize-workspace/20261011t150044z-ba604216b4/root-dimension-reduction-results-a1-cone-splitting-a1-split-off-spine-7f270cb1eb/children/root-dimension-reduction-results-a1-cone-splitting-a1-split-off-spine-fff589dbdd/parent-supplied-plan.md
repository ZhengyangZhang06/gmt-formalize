# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.slice_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-fff589dbdd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `slice_integrable`
- Declaration: `Submission.dimred_cs_sos_mt_slice_integrable`
- Exact Lean type: `∀ (P k j n' : ℕ) (g : Fin k → Euclid P) (T : GeometricCurrentOn (univ : Set (Euclid P)) j) (RT : IMRep (univ : Set (Euclid P)) j) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) j) (ω : TestFormOn (univ : Set (Euclid P)) n'), Orthonormal ℝ g → RT.Represents T → Continuous (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) ∧ (∀ E : Set (Euclid P), MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → Bornology.IsBounded E → IntegrableOn (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) E μHE[k]) ∧ (RT.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → ∀ E : Set (Euclid P), MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → IntegrableOn (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) E μHE[k])`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.interior_product-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.frame_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

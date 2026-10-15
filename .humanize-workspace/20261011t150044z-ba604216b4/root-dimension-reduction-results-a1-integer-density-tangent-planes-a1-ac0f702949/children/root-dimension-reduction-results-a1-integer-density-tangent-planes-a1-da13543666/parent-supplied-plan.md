# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1.product_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-da13543666/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.split_off_spine-a1`
- Child key: `product_current`
- Declaration: `Submission.idtp_fons_cs_sos_product_current`
- Exact Lean type: `∀ (P k m' n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m') (E : Set (Euclid P)) (A : GeometricCurrentOn (univ : Set (Euclid P)) m') (RA : IMRep (univ : Set (Euclid P)) m'), 0 < m' → Orthonormal ℝ g → MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → RA.Represents A → RA.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → ∃ (B : GeometricCurrentOn (univ : Set (Euclid P)) n') (RB : IMRep (univ : Set (Euclid P)) n'), RB.Represents B ∧ (∀ C : Set (Euclid P), MeasurableSet C → RB.measure C = ∫⁻ t in E, RA.measure ((fun y => t + y) ⁻¹' C) ∂μHE[k]) ∧ ∀ flat : Covector (Euclid P) n' → Covector (Euclid P) m', (∀ (α : Covector (Euclid P) n') (v : Fin m' → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n', B ω = ∫ t in E, currentEval A (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) ∂μHE[k]`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`
- `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

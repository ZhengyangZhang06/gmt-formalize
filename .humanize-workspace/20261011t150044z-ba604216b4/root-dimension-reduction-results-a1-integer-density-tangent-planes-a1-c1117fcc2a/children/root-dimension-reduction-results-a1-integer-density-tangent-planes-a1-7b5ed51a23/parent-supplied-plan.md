# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1.imrep_formulas-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b5ed51a23/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.polygonal_current-a1`
- Child key: `imrep_formulas`
- Declaration: `Submission.idtp_fons_odc_pc_imrep_formulas`
- Exact Lean type: `∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, MeasurableSet (I k)) → ∀ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) → (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) → (∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

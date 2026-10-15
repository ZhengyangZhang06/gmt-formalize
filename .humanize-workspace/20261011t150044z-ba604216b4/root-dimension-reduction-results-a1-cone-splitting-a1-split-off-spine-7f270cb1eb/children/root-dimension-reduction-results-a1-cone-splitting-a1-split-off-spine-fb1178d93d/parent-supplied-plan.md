# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.interior_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-fb1178d93d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `interior_product`
- Declaration: `Submission.dimred_cs_sos_mt_interior_product`
- Exact Lean type: `∀ P : ℕ, (∀ (k m n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m), ∃ flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m, ∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) ∧ ∀ (a b : ℕ) (flat : Covector (Euclid P) a →L[ℝ] Covector (Euclid P) b) (ω : DifferentialForm (Euclid P) a) (t : Euclid P), IsTestForm ω → IsTestForm (fun y => flat (ω (t + y))) ∧ tsupport (fun y => flat (ω (t + y))) ⊆ (fun y => t + y) ⁻¹' tsupport ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

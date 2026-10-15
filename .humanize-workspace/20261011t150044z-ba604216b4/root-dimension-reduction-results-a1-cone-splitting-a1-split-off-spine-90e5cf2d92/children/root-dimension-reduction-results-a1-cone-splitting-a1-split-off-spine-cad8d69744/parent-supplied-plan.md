# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.flat_extderiv_split-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-cad8d69744/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `flat_extderiv_split`
- Declaration: `Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split`
- Exact Lean type: `∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : DifferentialForm (Euclid P) n') (x : Euclid P), DifferentiableAt ℝ ω x → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → flatD (exteriorDerivative ω x) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) • fderiv ℝ (fun z => flatF a (ω z)) x (g a) + (-1 : ℝ) ^ (j + 1) • exteriorDerivative (fun z => flat (ω z)) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

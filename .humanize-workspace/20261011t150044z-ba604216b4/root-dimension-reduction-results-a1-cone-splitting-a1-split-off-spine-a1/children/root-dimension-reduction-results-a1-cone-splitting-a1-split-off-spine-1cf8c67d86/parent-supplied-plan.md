# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.boundary_cone_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-1cf8c67d86/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1`
- Child key: `boundary_cone_transfer`
- Declaration: `Submission.dimred_cs_sos_boundary_cone_transfer`
- Exact Lean type: `∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (f : Fin (Module.finrank ℝ L) → Euclid P) (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (hd : Module.finrank ℝ L < n), 0 < Module.finrank ℝ L → Orthonormal ℝ f → (∀ i, f i ∈ L) → R₀.Represents S₀ → R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) (n - Module.finrank ℝ L), (∀ (α : Covector (Euclid P) n) (v : Fin (n - Module.finrank ℝ L) → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[Module.finrank ℝ L]) → (BoundaryVanishes S → BoundaryVanishes S₀) ∧ (IsConeCurrent S → IsConeCurrent S₀)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

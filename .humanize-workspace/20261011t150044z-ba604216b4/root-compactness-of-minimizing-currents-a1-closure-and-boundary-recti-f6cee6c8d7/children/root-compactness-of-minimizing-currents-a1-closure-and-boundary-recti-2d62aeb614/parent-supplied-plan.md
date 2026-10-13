# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.orient_union-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2d62aeb614/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1`
- Child key: `orient_union`
- Declaration: `Submission.cbrg_ae_orient_iUnion`
- Exact Lean type: `(∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W N : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, MeasurableSet (N i)) → (∀ i, N i ⊆ (R i).carrier) → (⋃ i, N i) ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[k] ((⋃ i, N i) ∩ K) ≠ ∞) → (∀ i, ∀ᵐ y ∂(μHE[k].restrict (N i)), ξ y = (R i).orient y) → ∀ᵐ x ∂(μHE[k].restrict (⋃ i, N i)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ i, N i) x Q ∧ IsUnitOrientationOf (ξ x) Q`

## Sibling prerequisites

- `root.regular_set_dense-a1.density_eq_multiplicity-a1.imrep_local_finiteness-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

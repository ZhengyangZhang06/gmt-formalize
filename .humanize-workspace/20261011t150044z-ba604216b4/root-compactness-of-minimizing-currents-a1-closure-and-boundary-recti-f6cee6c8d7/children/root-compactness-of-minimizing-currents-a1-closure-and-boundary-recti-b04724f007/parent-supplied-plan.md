# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.glue_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b04724f007/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1`
- Child key: `glue_pieces`
- Declaration: `Submission.cbrg_imRep_glue_disjoint`
- Exact Lean type: `(∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W A : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, W i ⊆ U) → (∀ i, MeasurableSet (A i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → μ (⋃ i, A i)ᶜ = 0 → (∀ i, μ.restrict (A i) = (R i).measure.restrict (A i)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y) → ∃ R' : IMRep U k, R'.carrier = ⋃ i, (R i).carrier ∩ A i ∧ R'.orient = ξ ∧ R'.measure = μ`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.orient_union-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

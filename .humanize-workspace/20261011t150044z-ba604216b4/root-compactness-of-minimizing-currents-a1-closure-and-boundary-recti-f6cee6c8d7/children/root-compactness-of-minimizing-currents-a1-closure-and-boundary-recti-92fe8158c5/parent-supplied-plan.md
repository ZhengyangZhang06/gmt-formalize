# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1.cover_refine-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-92fe8158c5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1`
- Child key: `cover_refine`
- Declaration: `Submission.cbrg_exists_countable_disjoint_refinement`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (p : Set (Euclid P) → Prop), (∀ x ∈ U, ∃ W : Set (Euclid P), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ p W) → ∃ (ι : Type) (_ : Countable ι) (W A : ι → Set (Euclid P)), (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ U) ∧ (∀ i, p (W i)) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i, A i ⊆ W i) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ⋃ i, A i = U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1.chart_partition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f1b36565bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.area_formula-a1`
- Child key: `chart_partition`
- Declaration: `Submission.codim1_hcp_af_chart_partition`
- Exact Lean type: `∀ (P m : ℕ) (M E : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → MeasurableSet E → E ⊆ M → ∃ (Es : ℕ → Set (Euclid P)) (Vs : ℕ → Set (Euclid m)) (Ws : ℕ → Set (Euclid P)) (ψs : ℕ → Euclid m → Euclid P), (∀ k, MeasurableSet (Es k)) ∧ Pairwise (fun i j => Disjoint (Es i) (Es j)) ∧ (⋃ k, Es k) = E ∧ ∀ k, IsOpen (Vs k) ∧ IsOpen (Ws k) ∧ ContDiffOn ℝ 1 (ψs k) (Vs k) ∧ InjOn (ψs k) (Vs k) ∧ ψs k '' Vs k = Ws k ∩ M ∧ (∀ K ⊆ Ws k, IsCompact K → IsCompact (Vs k ∩ ψs k ⁻¹' K)) ∧ (∀ z ∈ Vs k, Injective (fderiv ℝ (ψs k) z)) ∧ Es k ⊆ Ws k ∩ M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

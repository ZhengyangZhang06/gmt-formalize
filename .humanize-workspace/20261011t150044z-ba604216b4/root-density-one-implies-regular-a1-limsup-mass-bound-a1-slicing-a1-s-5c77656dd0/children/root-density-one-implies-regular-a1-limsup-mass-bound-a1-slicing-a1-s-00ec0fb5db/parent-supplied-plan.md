# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.disjoint_refinement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-00ec0fb5db/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `disjoint_refinement`
- Declaration: `Submission.dor_lmbsf_cp_disjoint_refinement`
- Exact Lean type: `∀ (m P : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (C : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P) (Good : ℕ → Euclid m → Prop), MeasurableSet M → (∀ j, IsCompact (C j) ∧ ContinuousOn (ψ j) (C j)) → μ (M \ ⋃ j, ψ j '' C j) = 0 → (∀ j, ∀ᵐ x ∂(μ.restrict (M ∩ ψ j '' C j)), ∀ y ∈ C j, ψ j y = x → Good j y) → ∃ Y : ℕ → Set (Euclid m), (∀ j, MeasurableSet (Y j) ∧ Y j ⊆ C j ∧ ψ j '' Y j ⊆ M ∧ ∀ y ∈ Y j, Good j y) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μ (M \ ⋃ j, ψ j '' Y j) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

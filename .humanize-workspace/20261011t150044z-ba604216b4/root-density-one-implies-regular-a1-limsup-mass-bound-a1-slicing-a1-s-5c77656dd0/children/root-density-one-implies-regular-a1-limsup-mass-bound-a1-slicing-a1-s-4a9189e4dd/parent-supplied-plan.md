# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.measurable_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-4a9189e4dd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `measurable_glue`
- Declaration: `Submission.dor_lmbsf_cp_measurable_glue`
- Exact Lean type: `∀ (m P : ℕ) (Y : ℕ → Set (Euclid m)) (ψ Φ : ℕ → Euclid m → Euclid P), (∀ j, MeasurableSet (Y j) ∧ ContinuousOn (ψ j) (Y j) ∧ InjOn (ψ j) (Y j) ∧ ContinuousOn (Φ j) (Y j)) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → ∃ g : Euclid P → Euclid P, Measurable g ∧ (∀ j, ∀ y ∈ Y j, g (ψ j y) = Φ j y) ∧ ∀ x, (∀ j, x ∉ ψ j '' Y j) → g x = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

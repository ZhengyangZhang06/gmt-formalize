# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1.disjointify-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-0d31e1595b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_pieces-a1`
- Child key: `disjointify`
- Declaration: `Submission.dtc_bc_lc_sl_cp_disjointify`
- Exact Lean type: `∀ (P N : ℕ) (ψ : ℕ → Euclid N → Euclid P) (Y : ℕ → Set (Euclid N)), (∀ j, Continuous (ψ j)) → (∀ j, MeasurableSet (Y j)) → (∀ j, InjOn (ψ j) (Y j)) → ∃ Y' : ℕ → Set (Euclid N), (∀ j, MeasurableSet (Y' j) ∧ Y' j ⊆ Y j) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y' i) (ψ j '' Y' j)) ∧ ⋃ j, ψ j '' Y' j = ⋃ j, ψ j '' Y j`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

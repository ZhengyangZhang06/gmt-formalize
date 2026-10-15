# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.lipschitz_localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-f9cefd17ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child key: `lipschitz_localization`
- Declaration: `Submission.idtp_caf_lipschitz_localization`
- Exact Lean type: `∀ (P n : ℕ) (Z : Set (Euclid P)) (F : Euclid P → Euclid n), IsOpen Z → ContDiffOn ℝ 1 F Z → ∃ (V Zs : ℕ → Set (Euclid P)) (G : ℕ → Euclid P → Euclid n), (∀ l, IsOpen (V l)) ∧ (∀ l, V l ⊆ Z) ∧ (∀ l, MeasurableSet (Zs l)) ∧ (∀ l, Zs l ⊆ V l) ∧ Pairwise (fun l l' => Disjoint (Zs l) (Zs l')) ∧ (⋃ l, Zs l) = Z ∧ (∀ l, ∃ K : NNReal, LipschitzWith K (G l)) ∧ ∀ l, EqOn F (G l) (V l)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

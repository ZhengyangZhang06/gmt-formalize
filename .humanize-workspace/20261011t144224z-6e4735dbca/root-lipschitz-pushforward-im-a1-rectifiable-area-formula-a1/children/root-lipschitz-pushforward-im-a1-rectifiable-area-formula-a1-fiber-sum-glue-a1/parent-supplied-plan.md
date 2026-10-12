# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.fiber_sum_glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-fiber-sum-glue-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child key: `fiber_sum_glue`
- Declaration: `Submission.lpf_raf_fiber_sum_glue`
- Exact Lean type: `∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (f : X → Y) (h F : X → ℝ≥0∞) (A Z : Set X) (B : ℕ → Set X), (∀ m, B m ⊆ A) → Pairwise (Function.onFun Disjoint B) → (∀ m, NullMeasurableSet (B m) μ) → (A ⊆ Z ∪ ⋃ m, B m) → μ Z = 0 → ν (f '' Z) = 0 → (∀ m, AEMeasurable (fun y => ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x) ν ∧ ∫⁻ x in B m, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ B m ∧ f x = y}, h x ∂ν) → AEMeasurable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, h x) ν ∧ ∫⁻ x in A, F x ∂μ = ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, h x ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

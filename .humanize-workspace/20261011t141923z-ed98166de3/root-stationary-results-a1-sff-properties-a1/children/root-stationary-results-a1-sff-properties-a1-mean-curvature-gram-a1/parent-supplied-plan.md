# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.sff_properties-a1.mean_curvature_gram-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-properties-a1-mean-curvature-gram-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.sff_properties-a1`
- Child key: `mean_curvature_gram`
- Declaration: `Submission.mean_curvature_eq_normalPart_gram_trace`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)) (y : Rn N) (A : Rn n →L[ℝ] Rn N) (S : Rn n →L[ℝ] Rn n →L[ℝ] Rn N), Function.Injective A → tangentSpace M y = LinearMap.range A.toLinearMap → (∀ a b : Rn n, secondFundamentalForm M y (A a) (A b) = normalPart M y (S a b)) → meanCurvature M y = normalPart M y (∑ k : Fin n, ∑ l : Fin n, inner ℝ (EuclideanSpace.single k (1 : ℝ)) (Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) (EuclideanSpace.single l (1 : ℝ))) • S (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single l (1 : ℝ)))`

## Sibling prerequisites

- `root.stationary_results-a1.sff_properties-a1.gram_unit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

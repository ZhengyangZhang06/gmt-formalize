# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.diagonal_blowup-a1.blowup_variation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1-blowup-variation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child key: `blowup_variation_bound`
- Declaration: `Submission.intcpt_diag_blowup_variation_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (ξ : Euclidean N) (t R : ℝ), V.HasLocallyBoundedFirstVariation → 0 < t → 0 < R → (∀ y ∈ ball (0 : Euclidean N) R, ξ + t • y ∈ U) → ∃ W : Varifold N n (ball (0 : Euclidean N) R), W.measure = (rescaledMeasure V ξ t).restrict (ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) ∧ W.HasLocallyBoundedFirstVariation ∧ variationMeasure W (ball (0 : Euclidean N) R) ≤ ENNReal.ofReal (t⁻¹ ^ n * t) * variationMeasure V (closedBall ξ (t * R))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

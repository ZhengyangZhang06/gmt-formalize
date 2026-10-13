# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.diagonal_blowup-a1.rescaled_radon_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1-rescaled-radon-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child key: `rescaled_radon_tendsto`
- Declaration: `Submission.intcpt_diag_rescaled_radon_tendsto`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U) (ξ : Euclidean N) (t : ℝ) (F : C_c(Euclidean N × Grassmannian N n, ℝ)), Varifold.RadonConverges Vi V → 0 < t → (∀ z ∈ tsupport F, ξ + t • z.1 ∈ U) → Tendsto (fun i ↦ ∫ z, F z ∂(rescaledMeasure (Vi i) ξ t)) atTop (𝓝 (∫ z, F z ∂(rescaledMeasure V ξ t)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

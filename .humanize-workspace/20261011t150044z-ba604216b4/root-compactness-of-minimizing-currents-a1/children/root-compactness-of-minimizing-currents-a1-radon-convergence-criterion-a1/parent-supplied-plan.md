# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-radon-convergence-criterion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1`
- Child key: `radon_convergence_criterion`
- Declaration: `Submission.cmc_tendsto_integral_of_limsup_liminf`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs j G) atTop) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

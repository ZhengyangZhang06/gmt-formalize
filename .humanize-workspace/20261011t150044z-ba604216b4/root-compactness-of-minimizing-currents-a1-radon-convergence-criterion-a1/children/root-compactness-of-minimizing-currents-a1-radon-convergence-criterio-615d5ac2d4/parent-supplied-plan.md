# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1.superlevel_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-radon-convergence-criterio-615d5ac2d4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1`
- Child key: `superlevel_convergence`
- Declaration: `Submission.cmc_rcc_ae_tendsto_measure_superlevel`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs j G) atTop) → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun j => μs j {x | t < g x}) atTop (𝓝 (μ {x | t < g x}))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

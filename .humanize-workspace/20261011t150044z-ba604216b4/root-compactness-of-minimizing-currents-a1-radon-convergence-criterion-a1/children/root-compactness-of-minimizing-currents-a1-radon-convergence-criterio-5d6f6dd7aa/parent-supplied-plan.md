# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1.layer_cake_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-radon-convergence-criterio-5d6f6dd7aa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.radon_convergence_criterion-a1`
- Child key: `layer_cake_convergence`
- Declaration: `Submission.cmc_rcc_tendsto_integral_of_ae_tendsto_superlevel`
- Exact Lean type: `∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)) (g : Euclid P → ℝ), Continuous g → HasCompactSupport g → (∀ x, 0 ≤ g x) → μ (tsupport g) < ∞ → limsup (fun j => μs j (tsupport g)) atTop < ∞ → (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun j => μs j {x | t < g x}) atTop (𝓝 (μ {x | t < g x}))) → Tendsto (fun j => ∫ x, g x ∂(μs j)) atTop (𝓝 (∫ x, g x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

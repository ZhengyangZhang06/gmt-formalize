# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.critical_slices-a1.near_degenerate_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-critical-slices-a1-near-degenerate-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.critical_slices-a1`
- Child key: `near_degenerate_image`
- Declaration: `Submission.critSlices_image_volume_le_of_fderiv_near`
- Exact Lean type: `∀ (n m : ℕ) (G : Rn n → Rn m) (S : Set (Rn n)) (P : Rn n →L[ℝ] Rn m) (u₀ : Rn n) (d ε Λ : ℝ), Convex ℝ S → u₀ ∈ S → (∀ v ∈ S, DifferentiableAt ℝ G v) → (∀ v ∈ S, ‖fderiv ℝ G v - P‖ ≤ ε) → (∀ v ∈ S, ‖v - u₀‖ ≤ d) → ¬ Function.Surjective P → ‖P‖ ≤ Λ → volume (G '' S) ≤ ENNReal.ofReal (2 * (ε * d) * (2 * ((Λ + ε) * d)) ^ (m - 1))`

## Sibling prerequisites

- `root.coarea_and_slices-a1.critical_slices-a1.slab_volume-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

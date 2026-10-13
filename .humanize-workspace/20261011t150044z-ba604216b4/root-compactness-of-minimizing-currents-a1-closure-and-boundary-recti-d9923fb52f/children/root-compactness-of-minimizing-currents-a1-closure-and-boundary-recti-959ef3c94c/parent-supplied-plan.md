# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.portmanteau-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-959ef3c94c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1`
- Child key: `portmanteau`
- Declaration: `Submission.cbr_vague_portmanteau`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => νs j K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => νs j G) atTop)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

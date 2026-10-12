# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.rotated_coords-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-rotated-coords-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1`
- Child key: `rotated_coords`
- Declaration: `Submission.arp_rotatedPlane_graphPoint_coords`
- Exact Lean type: `∀ (n ℓ : ℕ), (∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (a, b)) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ ∀ (q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (a : Rn n) (b : Rn ℓ), infDist (q₀ (graphPoint a b)) (rotatedPlane q₀ : Set (Amb n ℓ)) = ‖b‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

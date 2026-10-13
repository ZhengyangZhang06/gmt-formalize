# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.proj_fderiv_zero-a1.gram_fderiv_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-plane-algebra-a1-graph-proj-smooth-a1-5d45a2143d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.graph_plane_algebra-a1.graph_proj_smooth-a1.proj_fderiv_zero-a1`
- Child key: `gram_fderiv_zero`
- Declaration: `Submission.allard52_gfz_gram_fderiv_zero`
- Exact Lean type: `∀ (n ℓ : ℕ) (ι : Rn n →L[ℝ] Amb n ℓ) (κ : Rn ℓ →L[ℝ] Amb n ℓ) (τ : (Rn n →L[ℝ] Amb n ℓ) →L[ℝ] (Amb n ℓ →L[ℝ] Rn n)), (∀ (L : Rn n →L[ℝ] Amb n ℓ) (w : Amb n ℓ) (v : Rn n), inner ℝ (τ L w) v = inner ℝ w (L v)) → (∀ v u : Rn n, inner ℝ (ι v) (ι u) = inner ℝ v u) → (∀ (v : Rn n) (z : Rn ℓ), inner ℝ (ι v) (κ z) = 0) → ∀ H : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun A : Rn n →L[ℝ] Rn ℓ => (ι + κ ∘L A) ∘L Ring.inverse (τ (ι + κ ∘L A) ∘L (ι + κ ∘L A)) ∘L τ (ι + κ ∘L A)) 0 H = ι ∘L τ (κ ∘L H) + κ ∘L H ∘L τ ι`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

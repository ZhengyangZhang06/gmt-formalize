# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_density_blowup-a1.rescaled_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1-rescaled-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Child key: `rescaled_limit`
- Declaration: `Submission.ts_pdb_density_point_rescaled_limit`
- Exact Lean type: `∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (J : EuclideanSpace ℝ (Fin n) → ℝ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] Ambient n ℓ) (w : EuclideanSpace ℝ (Fin n)) (c : ℝ), IsCompact C → Continuous F → ContinuousOn J C → w ∈ C → HasFDerivAt F A w → Function.Injective A → 0 < c → (∀ v ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → ∀ f : C_c(Ambient n ℓ, ℝ), Tendsto (fun t : ℝ ↦ (t ^ n)⁻¹ * ∫ v in C, J v * f (t⁻¹ • (F v - F w))) (𝓝[>] 0) (𝓝 (J w * ∫ u, f (A u)))`

## Sibling prerequisites

- `root.tangent_structure-a1.piece_density_blowup-a1.density_complement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

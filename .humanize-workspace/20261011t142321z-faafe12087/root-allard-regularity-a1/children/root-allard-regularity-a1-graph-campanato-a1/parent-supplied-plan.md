# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_campanato-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `graph_campanato`
- Declaration: `Submission.allard52_graph_campanato`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ L δ₃ C : ℝ, 0 < L ∧ L ≤ 1 / 4 ∧ 0 < δ₃ ∧ 0 ≤ C ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₃ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), 0 < R → R ≤ δ * ρ → f 0 = 0 → LipschitzOnWith (Real.toNNReal L) f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → ∀ (S : Amb n ℓ → Submodule ℝ (Amb n ℓ)) (A : ℝ), 0 ≤ A → (∀ ζ ∈ V.support ∩ closedBall 0 (R / 2), Module.finrank ℝ (S ζ) = n ∧ ∀ s : ℝ, 0 < s → s ≤ R / 2 → V.tiltExcess ζ s (S ζ) ≤ A * (s / R) ^ (2 * (1 - n / p))) → ContDiffOn ℝ 1 f (ball 0 (R / 16)) ∧ (∀ x ∈ ball (0 : Rn n) (R / 16), ∀ y ∈ ball (0 : Rn n) (R / 16), hsNorm (fderiv ℝ f x - fderiv ℝ f y) ≤ C * Real.sqrt A * (‖x - y‖ / R) ^ (1 - n / p)) ∧ ∀ z ∈ ball (0 : Rn n) (R / 16), (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f z v))).map q.toLinearEquiv.toLinearMap = S (q (graphPoint z (f z)))`

## Sibling prerequisites

- `root.allard_regularity-a1.tangent_ae-a1`
- `root.allard_regularity-a1.graph_plane_algebra-a1`
- `root.allard_regularity-a1.graph_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

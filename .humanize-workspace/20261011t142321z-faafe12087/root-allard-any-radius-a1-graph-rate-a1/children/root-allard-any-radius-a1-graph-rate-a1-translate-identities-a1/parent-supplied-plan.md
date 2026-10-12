# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.translate_identities-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-translate-identities-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1`
- Child key: `translate_identities`
- Declaration: `Submission.any_radius_gr_translate_identities`
- Exact Lean type: `∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ζ : Amb n ℓ), V'.weight = V.weight.map (fun x => x - ζ) → (∀ x, V'.mult x = V.mult (ζ + x)) → (∀ x, V'.tangentProj x = V.tangentProj (ζ + x)) → (∀ s : ℝ, V'.weight (closedBall 0 s) = V.weight (closedBall ζ s)) ∧ (∀ (s : ℝ) (T : Submodule ℝ (Amb n ℓ)), V'.tiltExcess 0 s T = V.tiltExcess ζ s T) ∧ (∀ (H : Amb n ℓ → Amb n ℓ) (p s : ℝ), V'.scaledLpNorm (fun x => H (ζ + x)) p 0 s = V.scaledLpNorm H p ζ s) ∧ ((∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ᵐ x ∂V'.weight, 1 ≤ V'.mult x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

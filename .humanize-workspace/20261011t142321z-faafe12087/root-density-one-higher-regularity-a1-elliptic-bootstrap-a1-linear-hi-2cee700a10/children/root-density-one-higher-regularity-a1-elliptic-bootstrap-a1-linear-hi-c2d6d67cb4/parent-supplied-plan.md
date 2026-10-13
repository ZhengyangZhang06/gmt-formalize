# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_weak_equation-a1.linear_family_continuity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-c2d6d67cb4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_weak_equation-a1`
- Child key: `linear_family_continuity`
- Declaration: `Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => Φ (s x) (B x)) x₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

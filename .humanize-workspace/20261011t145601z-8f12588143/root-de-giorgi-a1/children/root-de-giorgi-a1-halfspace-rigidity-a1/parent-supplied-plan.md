# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.halfspace_rigidity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-halfspace-rigidity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1`
- Child key: `halfspace_rigidity`
- Declaration: `Submission.deGiorgi_halfSpace_rigidity`
- Exact Lean type: `∀ (N : ℕ) (G : Set (Rn N)) (e : Rn N), NullMeasurableSet G volume → ‖e‖ = 1 → (∀ (ζ : Rn N → ℝ) (v : Rn N), ContDiff ℝ 1 ζ → HasCompactSupport ζ → inner ℝ v e = 0 → ∫ y in G, fderiv ℝ ζ y v = 0) → (∀ ζ : Rn N → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → ∫ y in G, fderiv ℝ ζ y e ≤ 0) → (∀ R : ℝ, 0 < R → 0 < volume (G ∩ Metric.ball 0 R) ∧ 0 < volume (Metric.ball 0 R \ G)) → volume (symmDiff G {y | 0 < inner ℝ y e}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

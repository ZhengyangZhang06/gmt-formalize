# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.bilipschitz_diffeo-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-686bf23105/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child key: `bilipschitz_diffeo`
- Declaration: `Submission.dpf_c1_compact_perturbation_bilipschitz`
- Exact Lean type: `∀ (P : ℕ) (U K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → (∀ x, x ∉ K → φ x = x) → ∃ Λ : NNReal, LipschitzWith Λ φ ∧ AntilipschitzWith Λ φ ∧ φ ⁻¹' U = U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

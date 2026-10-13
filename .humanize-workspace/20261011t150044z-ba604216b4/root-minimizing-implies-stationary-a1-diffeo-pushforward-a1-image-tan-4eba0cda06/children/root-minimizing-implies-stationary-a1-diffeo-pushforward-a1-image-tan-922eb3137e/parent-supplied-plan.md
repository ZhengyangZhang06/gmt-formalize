# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1.image_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-922eb3137e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Child key: `image_regularity`
- Declaration: `Submission.dpf_itt_bilipschitz_image_locfin`
- Exact Lean type: `∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ Λ' : NNReal), MeasurableSet M → M ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → LipschitzWith Λ φ → AntilipschitzWith Λ' φ → φ ⁻¹' U = U → MeasurableSet (φ '' M) ∧ φ '' M ⊆ U ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (φ '' M ∩ C) ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

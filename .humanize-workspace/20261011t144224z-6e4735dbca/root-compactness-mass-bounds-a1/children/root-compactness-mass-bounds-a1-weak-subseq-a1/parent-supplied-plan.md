# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_mass_bounds-a1.weak_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-weak-subseq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_mass_bounds-a1`
- Child key: `weak_subseq`
- Declaration: `Submission.cmb_exists_weakly_convergent_subseq`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U n, (∀ W, CompactlyContainedOpen W U → (⨆ q, (T q).massOn W) < ∞) → ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U n), StrictMono φ ∧ WeaklyConvergesOn (fun q => T (φ q)) T₀`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.exhaustion-a1`
- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.compactness_mass_bounds-a1.testform_separable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

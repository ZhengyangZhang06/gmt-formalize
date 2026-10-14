# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-localization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1`
- Child key: `localization`
- Declaration: `Submission.fiw_localization`
- Exact Lean type: `SlicingTheorem → BoundaryRectifiability → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → ∀ W, CompactlyContainedOpen W U → ∃ (ψ : ℕ → ℕ) (K : Set (Eucl P)) (B : ℝ≥0∞) (T' : GeometricCurrentOn U (m + 1)) (T'j : ℕ → GeometricCurrentOn U (m + 1)), StrictMono ψ ∧ IsCompact K ∧ K ⊆ U ∧ B ≠ ∞ ∧ (∀ j, IsIntegerMultiplicity (T'j j)) ∧ (∀ j, IsIntegerMultiplicity (T'j j).boundary) ∧ (∀ j, (T'j j).support ⊆ K) ∧ (∀ j, (T'j j).mass + (T'j j).boundary.mass ≤ B) ∧ WeaklyConvergesOn T'j T' ∧ ∀ (j : ℕ) (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R → IsIntegerMultiplicity S → (∀ ω, T'j j ω - T' ω = R.boundary ω + S ω) → flatDistance W (Tj (ψ j)) T ≤ S.massOn W + R.massOn W`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_lincomb-a1`
- `root.flat_iff_weak-a1.im_mass_formula-a1`
- `root.flat_iff_weak-a1.tangent_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

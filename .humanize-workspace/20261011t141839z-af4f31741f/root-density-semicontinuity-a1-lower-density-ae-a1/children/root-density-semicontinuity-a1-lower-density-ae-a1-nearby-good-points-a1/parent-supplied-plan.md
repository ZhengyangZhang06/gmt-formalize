# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.lower_density_ae-a1.nearby_good_points-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-lower-density-ae-a1-nearby-good-points-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.lower_density_ae-a1`
- Child key: `nearby_good_points`
- Declaration: `Submission.exists_nearby_points_off_bad_sets`
- Exact Lean type: `∀ (N : ℕ) (W : Set (Euclidean N)) (Bad : ℕ → Set (Euclidean N)) (x : Euclidean N), IsOpen W → x ∈ W → (∀ i : ℕ, x ∉ interior (⋂ ℓ : ℕ, ⋂ (_ : i ≤ ℓ), Bad ℓ)) → ∃ (q : ℕ → ℕ) (y : ℕ → Euclidean N), Tendsto q atTop atTop ∧ Tendsto y atTop (𝓝 x) ∧ ∀ i, y i ∈ W ∧ y i ∉ Bad (q i)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

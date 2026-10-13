# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_mass_bound-a1.slab_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-mass-bound-a1-slab-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_mass_bound-a1`
- Child key: `slab_cover`
- Declaration: `Submission.bf_coneMass_slab_cover`
- Exact Lean type: `∀ (N : ℕ) (P : Rn N →L[ℝ] Rn N) (s R : ℝ) (S : Set (Rn N)) (x : Rn N), 0 < s → (∃ y ∈ S, ‖P (y - x)‖ < s / 4 * ‖y - x‖) → (∀ y ∈ S, ‖y - x‖ ≤ R) → ∃ h : ℝ, 0 < h ∧ h ≤ R ∧ ∃ x' ∈ S, S ∩ {z | ‖P (z - x)‖ < s * h / 4} ⊆ insert x ({y | ‖P (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x (3 * h) ∪ {y | ‖P (y - x')‖ < s * ‖y - x'‖} ∩ Metric.ball x' (3 * h))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

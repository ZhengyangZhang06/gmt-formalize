# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.set_convergence_integral-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-set-convergence-integral-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1`
- Child key: `set_convergence_integral`
- Declaration: `Submission.deGiorgiTM_tendsto_setIntegral_of_symmDiff`
- Exact Lean type: `∀ (N : ℕ) (A : ℝ → Set (Rn N)) (H : Set (Rn N)) (g : Rn N → ℝ), (∀ᶠ r in 𝓝[>] (0 : ℝ), NullMeasurableSet (A r) volume) → NullMeasurableSet H volume → Continuous g → HasCompactSupport g → Tendsto (fun r : ℝ ↦ volume (tsupport g ∩ symmDiff (A r) H)) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ ↦ ∫ y in A r, g y) (𝓝[>] 0) (𝓝 (∫ y in H, g y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

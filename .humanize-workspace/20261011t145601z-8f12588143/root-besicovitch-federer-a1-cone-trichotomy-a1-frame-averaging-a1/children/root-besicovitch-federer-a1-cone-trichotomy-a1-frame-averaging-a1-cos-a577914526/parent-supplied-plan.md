# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.coset_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-cos-a577914526/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `coset_fubini`
- Declaration: `Submission.bf_haar_null_of_cosetFibres_null`
- Exact Lean type: `∀ (N : ℕ) (θ θ' : Measure (Rn N →L[ℝ] Rn N)), IsFiniteMeasure θ → IsProbabilityMeasure θ' → (∀ᵐ k ∂θ', Measure.map (fun g ↦ g * k) θ = θ) → ∀ B : Set (Rn N →L[ℝ] Rn N), MeasurableSet B → (∀ᵐ h ∂θ, θ' {g | h * g ∈ B} = 0) → θ B = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

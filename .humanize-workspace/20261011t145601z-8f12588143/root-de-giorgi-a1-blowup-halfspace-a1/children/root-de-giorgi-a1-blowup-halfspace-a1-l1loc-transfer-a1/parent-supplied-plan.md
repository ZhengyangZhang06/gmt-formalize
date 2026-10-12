# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.blowup_halfspace-a1.l1loc_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1-l1loc-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `l1loc_transfer`
- Declaration: `Submission.deGiorgiHS_L1loc_limit_transfer`
- Exact Lean type: `∀ (N : ℕ) (F : ℕ → Set (Rn N)) (G : Set (Rn N)), (∀ k, NullMeasurableSet (F k) volume) → NullMeasurableSet G volume → (∀ K : Set (Rn N), IsCompact K → Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0)) → (∀ f : Rn N → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k ↦ ∫ y in F k, f y) atTop (𝓝 (∫ y in G, f y))) ∧ ∀ B : Set (Rn N), Bornology.IsBounded B → Tendsto (fun k ↦ volume (F k ∩ B)) atTop (𝓝 (volume (G ∩ B))) ∧ Tendsto (fun k ↦ volume (B \ F k)) atTop (𝓝 (volume (B \ G)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

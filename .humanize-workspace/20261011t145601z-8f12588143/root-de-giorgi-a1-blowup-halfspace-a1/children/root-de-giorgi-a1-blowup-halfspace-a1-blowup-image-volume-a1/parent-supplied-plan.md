# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.blowup_halfspace-a1.blowup_image_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1-blowup-image-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `blowup_image_volume`
- Declaration: `Submission.deGiorgiHS_blowUpMap_image_volume`
- Exact Lean type: `∀ (N : ℕ) (x : Rn N) (r : ℝ) (A : Set (Rn N)), (NullMeasurableSet A volume → NullMeasurableSet (blowUpMap x r '' A) volume) ∧ (0 < r → volume (blowUpMap x r '' A) = ENNReal.ofReal ((r ^ N)⁻¹) * volume A ∧ ∀ R : ℝ, blowUpMap x r '' A ∩ Metric.ball 0 R = blowUpMap x r '' (A ∩ Metric.ball x (r * R)) ∧ Metric.ball 0 R \ blowUpMap x r '' A = blowUpMap x r '' (Metric.ball x (r * R) \ A))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

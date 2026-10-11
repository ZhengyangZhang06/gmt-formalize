# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.harmonic_affine_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-harmonic-affine-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `harmonic_affine_approx`
- Declaration: `Submission.ted_harmonic_affine_approx`
- Exact Lean type: `HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δε : ℝ, 0 < δε ∧ ∀ (r E h : ℝ) (f : Rn n → Rn ℓ) (L : ℝ≥0), 0 < r → 0 < E → 0 ≤ h → LipschitzOnWith L f (closedBall 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖f x‖ ≤ h) → ∫ x in ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ E * r ^ n → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 r → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) r, inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ δε * Real.sqrt E * M * r ^ n) → ∃ (a : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ C * Real.sqrt E ∧ ‖a‖ ≤ C * (h + r * Real.sqrt (ε * E)) ∧ ∀ e : ℝ, 0 < e → e ≤ 1 / 4 → ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.

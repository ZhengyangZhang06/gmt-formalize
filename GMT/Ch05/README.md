# Chapter 5 — The Allard Regularity Theorem (Simon, printed pp. 103–130)

Frozen contract: `GMT/Ch05/Contract.lean` (namespace `GMT.Ch05`); `Submission.lean` is a byte copy.
Final statement: `GMT.Ch05.main_theorem`, the conjunction of the 12 Props below.

Book conventions used throughout (Simon, Notation p. ix): `B_ρ(y)` = **closed** ball
(`Metric.closedBall`), `B̆_ρ(y)` = open ball (`Metric.ball`); `ω_n = π^{n/2}/Γ(n/2+1)`;
`|A|` for matrices/linear maps is the Hilbert–Schmidt norm `(Σ A_ij²)^{1/2}` (also `|Du|`);
`Hⁿ` = Mathlib `μHE[n]` (normalized so `Hⁿ = Lⁿ` on `n`-planes, like Simon's).
Every Prop assumes `1 ≤ n` (the book's `n`-dimensional setting); `ℓ` is arbitrary.
The chapter's standing assumption `p > n` (stated in the chapter introduction and needed for 2.4) is
an explicit hypothesis of every result of §§2, 4, 5 that involves `p`.

## Statement map

| # | Book item (page) | Lean name | Meaning | Existing SimonGMT |
|---|---|---|---|---|
| 1 | Lemma 2.1 (p. 107) | `TiltExcessHeightEstimate` | `E(ξ,ρ/2,T) ≤ Cρ⁻ⁿ∫_{B_ρ(ξ)}(dist(x−ξ,T)/ρ)²dμ + Cρ^{2−n}∫_{B_ρ(ξ)}|H|²dμ`, `C = C(n)` | new |
| 2 | Lemma 2.5 (p. 108) | `AffineApproximationLemma` | affine approximation at all `ξ ∈ spt V ∩ B_{δρ}(0)`, `σ ∈ (0,2δρ]` (corrected, see below) | new |
| 3 | Lemma 2.6 (p. 110) | `LipschitzApproximationLemma` | Lipschitz graph approximation with measure-of-bad-set ≤ `CL⁻²·tilt` | new |
| 4 | Corollary 2.7 (p. 113) | `LipschitzGraphCorollary` | small tilt at all points/scales ⇒ `spt V` *is* a Lipschitz graph in `B_{σ₀/4}` | new |
| 5 | Lemma 3.1 (p. 114) | `HarmonicApproximationLemma` | almost-weakly-harmonic `W^{1,2}` functions are `L²`-close to harmonic ones | new |
| 6 | Theorem 4.5 (p. 116) | `TiltExcessDecayTheorem` | `E_*(ξ,ησ,S) ≤ η^{2(1−n/p)}E_*(ξ,σ,T)` | new |
| 7 | **Theorem 5.2** (p. 121) | `AllardRegularityTheorem` | Allard regularity with `C^{1,1−n/p}` estimate `≤ Cδ^{1/(2n+2)}` | new |
| 8 | Remark 5.3 (p. 122) / §6 title | `AllardRegularityAnyRadius` | same conclusion on `B_{γρ}` for **every** `γ ∈ (0,1)` | new |
| 9 | Theorem 6.1 (p. 124) | `ConicalApproximationTheorem` | conical approximation in the annulus `B₁ \ B_λ` | new |
| 10 | Theorem 7.1, 1st assertion (p. 127) | `DensityOneRegularity` | `Θⁿ(μ_V,ξ)=1` ⇒ `M` is a `C^{1,1−n/p}` graph near `ξ` (up to `Hⁿ`-null sets) | new |
| 11 | Theorem 7.1, 2nd assertion (p. 127) | `DensityOneHigherRegularity` | integer `θ`, `H = h ∈ C^{q,α}` ⇒ `u ∈ C^{q+2,α}`, `Θ ≡ 1` on `spt V` near `ξ` | new |
| 12 | Corollary 7.3 (p. 128) | `RegularSetOpenDense` | integer `θ`, `H ∈ Lᵖ_loc`, `p>n` ⇒ `reg V` relatively open and dense in `spt V` | new |

No item of this chapter is proved in `Poincare.SimonGMT`.  Infrastructure the prover may adapt:
`Chapter03.HasWeightedApproximateTangentSpaceAt.unique` (Chapter03/Rectifiable.lean, uniqueness of
`T_xV`); the `Lᵖ` monotonicity formula and density/u.s.c. results of Ch. 4 §4
(`Chapter04/LpMeanCurvature.lean`, `Chapter04/LpDensity.lean`, e.g.
`Chapter04.RectifiableVarifold.HasGeneralizedMeanCurvatureIn.tendsto_normalizedBallMass_of_memLp`)
— these are proved for the strengthened `Chapter04.RectifiableVarifold` (tangent field stored as
data) and need a bridge via Ch. 3, 1.9; five-times covering (`Chapter01.exists_fiveTimesCovering`,
Chapter01/DensityCovering.lean); real-valued McShane Lipschitz extension
(`Chapter02.lipschitz_extension_real_optimal`, Chapter02/Lipschitz.lean); the §1
harmonic-comparison energy estimate (`Chapter05.harmonicComparison_energy_le_sixthPower`,
Chapter05/HarmonicEnergy.lean; §1 itself is motivational and not part of this contract).
(All names are under `Poincare.SimonGMT`.)

### Hypotheses of each Prop
1. `U` open, `V` has generalized mean curvature `H` in `U`, `ρ > 0`, `B_ρ(ξ) ⊆ U`, `dim T = n`. No
   `θ ≥ 1`. Quantifiers `∀ n, ∃ C, ∀ ℓ …` (book: `C = C(n)`). The `|H|²` integral is in `[0,∞]`.
2. `p > n`; `∃ C(n,ℓ,p) > 0`; `δ ∈ (0,1/4]`, hypotheses 2.3 (`AllardHypotheses H p δ ρ`);
   `ξ ∈ spt V ∩ B_{δρ}(0)`, `σ ∈ (0,2δρ]`; conclusion `∃ T`, `dim T = n`.
3. `p > n`; `∃ β ∈ (0,1/4], C` (dep. on `n,ℓ,p`); `∀ L ∈ (0,1]`, `K ≥ 0`; `δ ∈ (0,(βL)^{2n+2}]`, 2.3;
   `σ₀ = δρ`; any linear isometry `q` such that `T₀ = q(ℝⁿ×{0})` satisfies
   `dist(x,T₀) ≤ Kδ^{1/(2n+2)}σ₀` on `spt V ∩ B_{2σ₀}(0)`.  Conclusion: `f` on `Bⁿ_{σ₀/2}(0)`,
   `Lip f ≤ L`, `sup|f| ≤ Kδ^{1/(2n+2)}σ₀`, `μ_V(B_{σ₀/2}∩(spt V\q(graph f))) +
   Hⁿ(B_{σ₀/2}∩(q(graph f)\spt V)) ≤ CL⁻²∫_{B_{σ₀}(0)}|p_{T_xM}−p_{T₀}|²dμ_V`.
4. As 3, plus `σ⁻ⁿ∫_{B_σ(ξ)}|p_{T_xM}−p_{T₀}|²dμ_V ≤ β²L²` for all `ξ ∈ spt V ∩ B_{σ₀/2}(0)`,
   `σ ∈ (0,σ₀/2]`.  Conclusion: `spt V ∩ B_{σ₀/4}(0) = q(graph f) ∩ B_{σ₀/4}(0)`, `Lip f ≤ L`,
   `sup|f| ≤ Kδ^{1/(2n+2)}σ₀`.
5. `ε > 0`, `∃ δ(n,ε) > 0`; `f ∈ W^{1,2}(B̆₁(0))` with weak gradient `g` (`IsW12WithGradient`),
   `∫|g|² ≤ 1`, `|∫ g·∇ζ| ≤ δ·M` whenever `|∇ζ| ≤ M` (`ζ ∈ C^∞_c(B̆₁)`).  Conclusion: `u` harmonic
   on `B̆₁(0)` (`InnerProductSpace.HarmonicOnNhd`), `∫|∇u|² ≤ 1`, `∫(u−f)² ≤ ε`.
6. `p > n`; `∃ η, δ₀ ∈ (0,1/4]`; `δ ∈ (0,δ₀]`, 2.3, `σ ∈ (0,δρ/2]`, `ξ ∈ spt V ∩ B_{δρ}(0)`, `dim T = n`.
7. `p > n`; `∃ δ₀, γ ∈ (0,1)` and `C` (all dep. only on `n,ℓ,p`, quantified before `U, V, H, δ, ρ`);
   `δ ∈ (0,δ₀]` and 5.1 (= 2.3).  Conclusion `AllardConclusion`: `∃ q` linear isometry, `u` `C¹` on
   the closed ball `Bⁿ_{γρ}(0)` with `u(0)=0`, `Du(0)=0`,
   `spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`,
   `ρ⁻¹sup|u| + sup|Du| + ρ^{1−n/p}sup_{x≠y}|x−y|^{−(1−n/p)}|Du(x)−Du(y)| ≤ Cδ^{1/(2n+2)}`
   (sums of suprema evaluated in `[0,∞]`, so finiteness — i.e. `u ∈ C^{1,1−n/p}` — is part of the
   conclusion).  `u(0)=0` is not printed but is automatic from `0 ∈ spt V`.
8. `p > n`, `∀ γ ∈ (0,1)`, `∃ δ₀ ∈ (0,1)` and `C` (dep. on `γ,n,ℓ,p`); rest as 7.
9. `Λ > 0`, `∃ C(n,ℓ,Λ)`; `λ,θ,δ ∈ (0,1/4)`, `|ξ| = 1−θ`, `U ⊇ B₁(0)` open, generalized mean curvature
   `H` (`L¹_loc` built in), the pinching/curvature hypothesis for every `r ∈ [λ,1]`, `μ(B₁(0)) ≤ Λ`;
   conclusion for all `ρ ∈ (0,θ]`, `τ ∈ [2λ,1]`.
10. `U` open, generalized mean curvature `H`, `H ∈ Lᵖ_loc(μ_V)` with `p > n`, `θ ≥ 1 μ_V`-a.e.,
    `ξ ∈ U`, `Θⁿ(μ_V,ξ) = 1`.  Conclusion: `ρ > 0`, linear isometry `Q`, open `W ∋ 0`,
    `u ∈ C^{1,1−n/p}(W;ℝ^ℓ)` (`IsHolderCkα 1`), `u(0)=0`, `Du(0)=0`,
    `Hⁿ((Q(M−ξ) ∩ B̆_ρ(0)) Δ graph_W u) = 0`.
11. As 10 but with `θ` positive-integer-valued `μ_V`-a.e., `H = h μ_V`-a.e., `h` locally
    `C^{q,α}` in `U`, `α ∈ (0,1)` (then `H ∈ L^∞_loc` and `θ ≥ 1` automatically).  Conclusion adds
    `u ∈ C^{q+2,α}(W)` and `Θⁿ(μ_V,x) = 1` for `x ∈ B̆_ρ(ξ) ∩ spt V`.
12. `U` open, generalized mean curvature `H ∈ Lᵖ_loc`, `p > n`, `θ` positive-integer-valued
    `μ_V`-a.e. on `spt V`.  Conclusion: `reg V = O ∩ spt V` for an open `O`, and
    `spt V = closure(reg V) ∩ U`.

## Errata / interpretation decisions
* **2.5 (‡), first inequality.** Printed: `C⁻¹(σ⁻ⁿ∫_{B_{σ/2}}|p_{T_xM}−p_T|²)^{1/2} ≤ σ⁻¹ sup dist`.
  The proof says it "follows directly from Remark 2.2", but 2.2 carries the extra term
  `C(σ^{p−n}∫_{B_σ}|H|ᵖ)^{2/p}`.  We add `(σ^{p−n}∫_{B_σ(ξ)}|H|ᵖdμ_V)^{1/p}` to the right side, i.e.
  we state exactly what the cited argument gives.  (Everything the book later uses from 2.5 —
  tilt `≤ Cδ^{1/(n+1)}` and height `≤ Cδ^{1/(2n+2)}σ` — still follows, since that term is `≤ δ`.)
* **2.6 sup bound.** Printed `sup|f| ≤ Cδ^{1/(2n+2)}` lacks the scale factor; corrected to
  `… · σ₀` (as in 2.7 and in proof step (7)).
* **2.6/2.7 normalization.** The book assumes w.l.o.g. `T(2σ₀,0) = ℝⁿ×{0}`.  We do not rotate the
  varifold; instead we quantify over linear isometries `q` and use `T₀ = q(ℝⁿ×{0})`, graphs
  `q(graph f)`.  We also replace "`T(2σ₀,0)` from Lemma 2.5" by its only property used in the proof
  — a height bound `dist ≤ Kδ^{1/(2n+2)}σ₀` on `spt V ∩ B_{2σ₀}(0)` — for an arbitrary `K ≥ 0`
  (2.5's plane has `K = 2C₂.₅`); `β, C` stay independent of `K` and the sup bound becomes
  `Kδ^{1/(2n+2)}σ₀`.  Specializing `K` recovers the printed statements.
* **Tilt excess normalization.** Simon 4.1 defines `E(ξ,σ,T) = σ⁻ⁿ∫_{B_σ(ξ)}|p_{T_xM}−p_T|²dμ_V`
  with the Hilbert–Schmidt norm and **no** factor `1/2` (the `1/2` appears only in the proof of
  2.1, in `σ = ½|p_{T_xM}−p_{ℝⁿ}|²`).  `E_*` is `max{E, δ⁻¹(σ^{p−n}∫|H|ᵖ)^{2/p}}` exactly as printed.
* **5.2.** Printed conclusion has `Du(0)=0`; we also record `u(0)=0` (automatic).  `δ > 0` per the
  standing convention `δ ∈ (0,1/2)` of §2.
* **5.3.** The improvement is only announced (§6 contains 6.1 but no proof of it).  We allow the
  constant `C` to depend on `γ` (the weaker reading of "the conclusion of the above theorem").
* **7.1.** Printed target `ℝ^k` is `ℝ^ℓ`.  In the second assertion, printed "`Θⁿ ≡ 1` on `B̆_ρ(ξ)`"
  must be restricted to `spt μ_V` (off the support `Θ = 0`), as the third assertion does.  The third
  assertion (stationary in a `C^{q+3}` submanifold `N`) is omitted: as printed `N` is
  `(n+ℓ)`-dimensional in `ℝ^{n+ℓ}` (so open, and the claim reduces to the second assertion with
  `h = 0`); the intended `ℝ^{n+L}` version needs the second fundamental form of `N` (Ch. 4, 2.7).
* **7.1 "up to `Hⁿ`-null sets"** is formalized as `Hⁿ` of the symmetric difference being `0`.
* **Omitted:** §1 (motivating smooth computation 1.1–1.5), 2.2, 2.4, 3.2–3.4, 4.2–4.4, 4.6, 6.2,
  7.4 (remarks/standard estimates used only inside proofs).

## New definitions and why they are faithful
* `Amb n ℓ = EuclideanSpace ℝ (Fin (n+ℓ))`, `Rn m`; `graphPoint x y = (x,y)` via `Fin.append`;
  `graphOver u D = {(x,u(x)) : x ∈ D}`; `horizontalPlane = ℝⁿ×{0}` (span of the first `n` basis
  vectors); `rotatedPlane q = q(ℝⁿ×{0})`.
* `unitBallVolume n = π^{n/2}/Γ(n/2+1)` — Simon's `ω_n` verbatim.
* `hsNormSq A = Σᵢ|Aeᵢ|²`, `hsNorm` — the inner-product norm of footnote 2 p. 115 / Notation p. ix.
* `IsC1Submanifold m S` — Simon Ch. 2 §4 definition (1:1 `C¹` proper parametrizations of maximal rank).
* `RectifiableVarifold n ℓ U` — **only primitive data**: carrier `M ⊆ U` (`Hⁿ`-null-measurable,
  countably `n`-rectifiable via the clean `Chapter03.CountablyRectifiable`) and multiplicity `θ`
  (positive on `M`, `Hⁿ`-measurable, `∫_{M∩K}θ dHⁿ < ∞` for compact `K ⊆ U`).  No tangent field is
  stored (unlike the excluded `Chapter04.RectifiableVarifold`).
* `weight = (Hⁿ⌞M).withDensity θ` (Ch. 4, 1.1); `support = U ∩ spt μ_V` (Ch. 4, 1.4; `spt V ⊆ U`,
  needed for "relatively closed in `U`" in 7.2/7.3).
* `tangentProj x` = orthogonal projection onto the approximate tangent space of `M` w.r.t. `θ`
  (Ch. 3, 1.7, via the clean `Chapter03.HasWeightedApproximateTangentSpaceAt`, which matches 1.7
  literally) **where it exists**, `0` otherwise — exactly Ch. 4, 1.3 ("whenever this exists").
  Uniqueness on `M` is SimonGMT `HasWeightedApproximateTangentSpaceAt.unique`; `μ_V`-a.e. existence
  (and hence a.e.-measurability) is Ch. 3, 1.9, left as a theorem.
* `divM X = trace(DX ∘ p_{T_xM}) = Σ e^{ij}D_iX^j` (Ch. 2, 4.18 / Ch. 4, 2.3).
* `HasGeneralizedMeanCurvature H` — Ch. 4, 3.14: `∫div_M X dμ_V = −∫X·H dμ_V` for all
  `X ∈ C¹_c(U;ℝ^{n+ℓ})`, plus `H ∈ L¹_loc(μ_V)` on `U` (equivalent to the right side existing for all
  such `X`).  `LocallyLp`, `HasDensity` (`Θⁿ(μ_V,x)` with closed balls).
* `tiltExcess` (4.1), `scaledLpNorm` (`(σ^{p−n}∫_{B_σ}|H|ᵖ)^{1/p}` in `[0,∞]`), `tiltExcessStar`
  (`E_*`, p. 116), `heightSup` (sup in 2.5, in `[0,∞]`).
* `AllardHypotheses` = 2.3 = 5.1 verbatim (with `ρ > 0` and the generalized-mean-curvature
  hypothesis); mass and `Lᵖ` conditions are in `[0,∞]`, so an infinite integral cannot satisfy them
  by a junk value.
* `regularSet` — Definition 7.2 (open ball `B̆_ρ(ξ)`).
* `scaledC1AlphaNorm`, `AllardConclusion` — the 5.2 conclusion; derivative within the closed ball,
  HS norms, suprema in `[0,∞]`.
* `IsHolderCkα j α u W` (`C^j` on `W`, derivatives up to order `j` bounded, `j`-th derivative globally
  `α`-Hölder on `W`) and `IsLocallyHolderCkα` (Hölder on compacts of `U`) — the qualitative Hölder
  classes of 7.1.  `IsW12WithGradient` — `W^{1,2}(Ω)` per Notation p. ix (weak gradient tested with
  `C^∞_c(Ω)`).

## Points of uncertainty (for reviewers)
* 5.2 as printed asserts the rate `Cδ^{1/(2n+2)}` with `γ` independent of `δ`; the printed proof
  reaches radius `γρ = δρ/4` "with `δ = δ(n,ℓ,p)` fixed", so the rate at fixed `γ` needs an argument
  beyond the text (it is the standard statement, Simon LGMT 24.2, and we keep it verbatim).
* 5.3 and 7.1(ii) go beyond what is proved in the chapter (5.3 announced only; 7.1(ii) cites Schauder
  theory).  They are included because they are stated results of the chapter.
* The literal printed first inequality of 2.5 (without the `H` term) is false: corrugated graphs
  with ε ≪ σ have tilt ≈ (a/ε)² against height ≈ a/σ for every `T`; the `H`-term is necessary.

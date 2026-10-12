import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Poincare.SimonGMT.Chapter04.WeightedBlowUp

/-!
# Simon, *Introduction to GMT*, Chapter 5: The Allard Regularity Theorem (pp. 103–130)

Frozen problem statement.  Conventions (Simon's "Notation", p. ix):
* `B_ρ(y)` is the **closed** ball (`Metric.closedBall`), `B̆_ρ(y)` the open ball (`Metric.ball`);
* `ℝ^{n+ℓ}` is `EuclideanSpace ℝ (Fin (n + ℓ))`, whose first `n` coordinates span `ℝⁿ × {0}`;
* `Hⁿ` is Mathlib's `μHE[n]` (normalized so that `Hⁿ = Lⁿ` on `n`-planes, as in Simon);
* `ω_n = π^{n/2}/Γ(n/2+1)`;
* `|A|` for a linear map is the inner-product (Hilbert–Schmidt) norm `(Σ_{ij} A_{ij}²)^{1/2}`
  (Simon p. ix and footnote 2 on p. 115).
* All results are stated for `n ≥ 1` (the book's `n`-dimensional setting) and arbitrary `ℓ`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GMT.Ch05

/-- Ambient space `ℝ^{n+ℓ}`. -/
abbrev Amb (n ℓ : ℕ) := EuclideanSpace ℝ (Fin (n + ℓ))

/-- Euclidean space `ℝᵐ`. -/
abbrev Rn (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- `ω_n = π^{n/2} / Γ(n/2 + 1)` (Simon, Notation p. ix): the volume of the unit ball of `ℝⁿ`. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1)

/-- Squared Hilbert–Schmidt ("inner product") norm `|A|² = Σ_i |A eᵢ|² = Σ_{i,j} A_{ji}²`
(Simon, Notation p. ix; Ch. 5 footnote 2 p. 115 and Remark 4.4). -/
noncomputable def hsNormSq {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  ∑ i : Fin m, ‖A (EuclideanSpace.single i 1)‖ ^ 2

/-- Hilbert–Schmidt norm `|A| = (Σ_{i,j} A_{ji}²)^{1/2}`; for `A = Du` this is Simon's `|Du|`. -/
noncomputable def hsNorm {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : ℝ :=
  Real.sqrt (hsNormSq A)

/-- The point `(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}` (first `n` coordinates `x`, last `ℓ` coordinates `y`). -/
noncomputable def graphPoint {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ) : Amb n ℓ :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

/-- `graph u = {(x, u(x)) : x ∈ D} ⊆ ℝ^{n+ℓ}` for `u : D ⊆ ℝⁿ → ℝ^ℓ`. -/
noncomputable def graphOver {n ℓ : ℕ} (u : Rn n → Rn ℓ) (D : Set (Rn n)) : Set (Amb n ℓ) :=
  (fun x => graphPoint x (u x)) '' D

/-- The coordinate plane `ℝⁿ × {0} ⊆ ℝ^{n+ℓ}`. -/
noncomputable def horizontalPlane (n ℓ : ℕ) : Submodule ℝ (Amb n ℓ) :=
  Submodule.span ℝ (Set.range fun i : Fin n => EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ))

/-- The rotated plane `q(ℝⁿ × {0})` for a linear isometry `q` of `ℝ^{n+ℓ}`. -/
noncomputable def rotatedPlane {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) : Submodule ℝ (Amb n ℓ) :=
  (horizontalPlane n ℓ).map q.toLinearEquiv.toLinearMap

/-- Simon Ch. 2 §4 (p. 55), definition preceding 4.1, with `r = 1`: `S ⊆ ℝ^N` is an
`m`-dimensional `C¹` submanifold if each `y ∈ S` has open `V ⊆ ℝᵐ`, `W ∋ y` and a 1:1 `C¹` map
`φ : V → W` with `φ(V) = W ∩ S`, `φ` proper (`K ⊆ W` compact ⇒ `φ⁻¹(K)` compact in `V`) and
`Dφ(x)` of rank `m` (injective) for all `x ∈ V`. -/
def IsC1Submanifold (m : ℕ) {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ y ∈ S, ∃ (V : Set (Rn m)) (W : Set (EuclideanSpace ℝ (Fin N)))
    (φ : Rn m → EuclideanSpace ℝ (Fin N)),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 φ V ∧ InjOn φ V ∧ φ '' V = W ∩ S ∧
    (∀ K, IsCompact K → K ⊆ W → IsCompact (V ∩ φ ⁻¹' K)) ∧
    ∀ x ∈ V, Function.Injective (fderiv ℝ φ x)

/-- `u ∈ C^{k,α}(W)` for open `W`: `u` is `C^k` on `W`, all derivatives of order `≤ k` are bounded on
`W`, and the `k`-th derivative is `α`-Hölder on `W` (finite global seminorm).  Used for the
qualitative Hölder classes of Theorem 7.1 (any fixed norm on multilinear maps gives the same class). -/
def IsHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (u : Rn m → Rn k) (W : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j u W ∧
  (∃ B : ℝ, ∀ i ≤ j, ∀ x ∈ W, ‖iteratedFDeriv ℝ i u x‖ ≤ B) ∧
  ∃ K : ℝ, ∀ x ∈ W, ∀ y ∈ W,
    ‖iteratedFDeriv ℝ j u x - iteratedFDeriv ℝ j u y‖ ≤ K * ‖x - y‖ ^ α

/-- `h` is `C^{k,α}` in the open set `U` (locally): `C^k` on `U`, and the `k`-th derivative is
`α`-Hölder on each compact subset of `U` (Simon 7.1, "a `C^{q,α}` function in `U`"). -/
def IsLocallyHolderCkα {m k : ℕ} (j : ℕ) (α : ℝ) (h : Rn m → Rn k) (U : Set (Rn m)) : Prop :=
  ContDiffOn ℝ j h U ∧
  ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α

/-- A rectifiable `n`-varifold `V = v(M, θ)` in the open set `U ⊆ ℝ^{n+ℓ}`
(Simon Ch. 4, introduction p. 85, and 3.14): only the primitive data `M ⊆ U` and `θ`, with
* `M` countably `n`-rectifiable (Ch. 3, 1.1; SimonGMT `Chapter03.CountablyRectifiable`) and
  `Hⁿ`-measurable;
* `θ` positive on `M`, `Hⁿ`-measurable, and locally `Hⁿ`-integrable on `M` in `U`.
No tangent-plane data is stored: tangent planes are *defined* below (`tangentProj`) as approximate
tangent spaces where they exist (their a.e. existence is Ch. 3, 1.9, a theorem). -/
structure RectifiableVarifold (n ℓ : ℕ) (U : Set (Amb n ℓ)) where
  /-- The carrier `M`. -/
  carrier : Set (Amb n ℓ)
  /-- The multiplicity function `θ` (its values off `M` are irrelevant). -/
  mult : Amb n ℓ → ℝ
  carrier_subset : carrier ⊆ U
  nullMeasurableSet_carrier : NullMeasurableSet carrier (μHE[n] : Measure (Amb n ℓ))
  countablyRectifiable : Poincare.SimonGMT.Chapter03.CountablyRectifiable n carrier
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  aemeasurable_mult : AEMeasurable mult ((μHE[n] : Measure (Amb n ℓ)).restrict carrier)
  integrableOn_mult : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U →
    IntegrableOn mult (carrier ∩ K) (μHE[n] : Measure (Amb n ℓ))

namespace RectifiableVarifold

variable {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)

/-- Simon Ch. 4, 1.1: the weight measure `μ_V = Hⁿ ⌞ θ` (with `θ = 0` off `M`). -/
noncomputable def weight : Measure (Amb n ℓ) :=
  ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
    (fun x => ENNReal.ofReal (V.mult x))

/-- Simon Ch. 4, 1.4: `spt V = spt μ_V`, taken inside the open set `U` where `V` lives. -/
def support : Set (Amb n ℓ) := U ∩ V.weight.support

open Classical in
/-- Orthogonal projection `p_{T_x M}` onto the tangent space `T_x V` (Simon Ch. 4, 1.3): the
approximate tangent space of `M` with respect to `θ` (Ch. 3, 1.7/1.9; SimonGMT
`Chapter03.HasWeightedApproximateTangentSpaceAt`) **where it exists**, and `0` elsewhere.  It is
unique on `M` (where `θ > 0`) and exists `μ_V`-a.e. by Ch. 3, 1.9 — a theorem, not an assumption. -/
noncomputable def tangentProj (x : Amb n ℓ) : Amb n ℓ →L[ℝ] Amb n ℓ :=
  if h : ∃ P : Submodule ℝ (Amb n ℓ),
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult x P
  then (Classical.choose h).starProjection else 0

/-- Tangential divergence `div_M X (x) = Σ_{i,j} e^{ij}(x) D_i X^j(x) = trace(DX(x) ∘ p_{T_x M})`
(Simon Ch. 2, 4.18; Ch. 4, 2.3). -/
noncomputable def divM (X : Amb n ℓ → Amb n ℓ) (x : Amb n ℓ) : ℝ :=
  LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap)

/-- Simon Ch. 4, Definition 3.14: `V` has generalized mean curvature `H` in `U` if
`∫ div_M X dμ_V = -∫ X · H dμ_V` for all `X ∈ C¹_c(U; ℝ^{n+ℓ})`; the implicit requirement that the
right side exist for every such `X` is the local `μ_V`-integrability of `H` on `U`. -/
def HasGeneralizedMeanCurvature (H : Amb n ℓ → Amb n ℓ) : Prop :=
  LocallyIntegrableOn H U V.weight ∧
  ∀ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    ∫ x, V.divM X x ∂V.weight = -∫ x, inner ℝ (X x) (H x) ∂V.weight

/-- `H` is locally in `Lᵖ(μ_V)` in `U`: `∫_K |H|ᵖ dμ_V < ∞` for every compact `K ⊆ U`. -/
def LocallyLp (H : Amb n ℓ → Amb n ℓ) (p : ℝ) : Prop :=
  ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ U → ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight < ∞

/-- `Θⁿ(μ_V, x) = t`: `μ_V(B_r(x)) / (ω_n rⁿ) → t` as `r ↓ 0` (Simon Ch. 1 §3; Ch. 4). -/
def HasDensity (x : Amb n ℓ) (t : ℝ) : Prop :=
  Tendsto (fun r : ℝ => V.weight (closedBall x r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal t))

/-- Simon Ch. 5, 4.1 (p. 115): tilt-excess
`E(ξ, σ, T) = σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_T|² dμ_V` (Hilbert–Schmidt norm, **no** factor `1/2`;
`B_σ(ξ)` closed).  Defined by the book only when `B_σ(ξ) ⊆ U`. -/
noncomputable def tiltExcess (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  (σ ^ n)⁻¹ * ∫ x in closedBall ξ σ, hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight

/-- `(σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}` as an extended real (no junk value when infinite). -/
noncomputable def scaledLpNorm (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (σ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (σ ^ (p - n)) * ∫⁻ x in closedBall ξ σ, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)

/-- Simon Ch. 5, p. 116 (before 4.5):
`E_*(ξ, σ, T) = max{E(ξ, σ, T), δ⁻¹ (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{2/p}}`, `δ` as in 2.3. -/
noncomputable def tiltExcessStar (H : Amb n ℓ → Amb n ℓ) (p δ : ℝ) (ξ : Amb n ℓ) (σ : ℝ)
    (T : Submodule ℝ (Amb n ℓ)) : ℝ :=
  max (V.tiltExcess ξ σ T) (δ⁻¹ * (V.scaledLpNorm H p ξ σ).toReal ^ 2)

/-- `sup {dist(x − ξ, T) : x ∈ spt V ∩ B_σ(ξ)}` (Simon 2.5), as an extended real. -/
noncomputable def heightSup (ξ : Amb n ℓ) (σ : ℝ) (T : Submodule ℝ (Amb n ℓ)) : ℝ≥0∞ :=
  ⨆ x ∈ V.support ∩ closedBall ξ σ, ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ)))

/-- The standing hypotheses 2.3 = 5.1 of Simon Ch. 5 (pp. 108, 121), for `V` with generalized
mean curvature `H` in `U`:
`θ ≥ 1 μ_V-a.e.`, `0 ∈ spt V`, `B_ρ(0) ⊆ U`, `ω_n⁻¹ ρ⁻ⁿ μ_V(B_ρ(0)) ≤ 1 + δ`,
`(ρ^{p−n} ∫_{B_ρ(0)} |H|ᵖ dμ_V)^{1/p} ≤ δ` (and `ρ > 0`). -/
def AllardHypotheses (H : Amb n ℓ → Amb n ℓ) (p δ ρ : ℝ) : Prop :=
  0 < ρ ∧ V.HasGeneralizedMeanCurvature H ∧ (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) ∧
  (0 : Amb n ℓ) ∈ V.support ∧ closedBall (0 : Amb n ℓ) ρ ⊆ U ∧
  V.weight (closedBall 0 ρ) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) ∧
  V.scaledLpNorm H p 0 ρ ≤ ENNReal.ofReal δ

/-- Simon Ch. 5, 7.2 (p. 128): `ξ ∈ spt V` is a regular point if `B̆_ρ(ξ) ∩ spt V` is an
`n`-dimensional `C¹` submanifold of `ℝ^{n+ℓ}` for some `ρ > 0`; `reg V` is the set of regular points
(and `sing V = spt V \ reg V`). -/
def regularSet : Set (Amb n ℓ) :=
  {ξ | ξ ∈ V.support ∧ ∃ ρ > 0, IsC1Submanifold n (ball ξ ρ ∩ V.support)}

end RectifiableVarifold

open RectifiableVarifold

/-- `ρ⁻¹ sup_B |u| + sup_B |Du| + ρ^α sup_{x ≠ y ∈ B} |x − y|^{−α} |Du(x) − Du(y)|` on a set `B`
(the quantity estimated in Simon 5.2), with `Du` the derivative within `B` and `|·|` the
Hilbert–Schmidt norm; as an extended real, so suprema never take junk values. -/
noncomputable def scaledC1AlphaNorm {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B : Set (Rn n)) (α ρ : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal ρ⁻¹ * (⨆ x ∈ B, ‖u x‖ₑ) +
  (⨆ x ∈ B, ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x))) +
  ENNReal.ofReal (ρ ^ α) * ⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
    ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)

/-- The conclusion of Simon 5.2 for radius `γρ` and constant `C`: there are a linear isometry `q`
of `ℝ^{n+ℓ}` and `u ∈ C^{1,1−n/p}(B_{γρ}(0); ℝ^ℓ)` (closed ball) with `u(0) = 0`, `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)`, and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} [Du]_{1−n/p} ≤ C δ^{1/(2n+2)}`. -/
def AllardConclusion {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (p δ ρ γ C : ℝ) : Prop :=
  ∃ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (closedBall 0 (γ * ρ)) ∧ u 0 = 0 ∧
    fderivWithin ℝ u (closedBall 0 (γ * ρ)) 0 = 0 ∧
    V.support ∩ closedBall 0 (γ * ρ) =
      q '' graphOver u (closedBall 0 (γ * ρ)) ∩ closedBall 0 (γ * ρ) ∧
    scaledC1AlphaNorm u (closedBall 0 (γ * ρ)) (1 - n / p) ρ ≤
      ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- `W^{1,2}(Ω)` with weak gradient `g` (Simon, Notation p. ix): `f, g ∈ L²(Ω)` and
`∫_Ω f ∇ζ = −∫_Ω ζ g` for every `ζ ∈ C^∞_c(Ω)`. -/
def IsW12WithGradient {n : ℕ} (f : Rn n → ℝ) (g : Rn n → Rn n) (Ω : Set (Rn n)) : Prop :=
  MemLp f 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
  ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω →
    ∫ x in Ω, f x • gradient ζ x = -∫ x in Ω, ζ x • g x

/-! ## Headline results -/

/-- **Simon Ch. 5, Lemma 2.1 (p. 107).**  Let `V = v(M, θ)` have generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}` (no lower bound on `θ` is needed).  If `B_ρ(ξ) ⊆ U`, then for every
`n`-dimensional subspace `T`,
`E(ξ, ρ/2, T) ≤ C ρ⁻ⁿ ∫_{B_ρ(ξ)} (dist(x − ξ, T)/ρ)² dμ_V + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ_V`,
with `C = C(n)` (independent of `ℓ`).  The `|H|²` term is an extended-real integral (it may be
infinite, in which case the inequality is trivial). -/
def TiltExcessHeightEstimate : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
  ∀ (ξ : Amb n ℓ) (ρ : ℝ), 0 < ρ → closedBall ξ ρ ⊆ U →
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
    ENNReal.ofReal (V.tiltExcess ξ (ρ / 2) T) ≤
      ENNReal.ofReal (C * (ρ ^ n)⁻¹ *
        ∫ x in closedBall ξ ρ, (infDist (x - ξ) (T : Set (Amb n ℓ)) / ρ) ^ 2 ∂V.weight) +
      ENNReal.ofReal (C * ρ ^ ((2 : ℝ) - n)) * ∫⁻ x in closedBall ξ ρ, ‖H x‖ₑ ^ 2 ∂V.weight

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)**, `p > n` (standing assumption of
the chapter).  There is `C = C(n, ℓ, p) > 0` such that if `δ ∈ (0, 1/4]` and 2.3 holds, then for each
`ξ ∈ spt V ∩ B_{δρ}(0)` and `σ ∈ (0, 2δρ]` there is an `n`-dimensional subspace `T` with
`C⁻¹ (σ⁻ⁿ ∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² dμ_V)^{1/2}
   ≤ σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} + (σ^{p−n} ∫_{B_σ(ξ)} |H|ᵖ dμ_V)^{1/p}`
and `σ⁻¹ sup{dist(x, ξ + T) : x ∈ spt V ∩ B_σ(ξ)} ≤ C δ^{1/(2n+2)}`.

*Correction:* the printed first inequality of (‡) omits the mean-curvature term
`(σ^{p−n}∫|H|ᵖ)^{1/p}`; the book derives it "directly from Remark 2.2", which contains exactly this
term, so we state the inequality that the cited argument proves.  (Since this term is `≤ δ`, it
still gives the tilt bound `σ⁻ⁿ∫_{B_{σ/2}(ξ)}|p_{T_xM} − p_T|² ≤ C δ^{1/(n+1)}` used later.) -/
def AffineApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ 1 / 4 → V.AllardHypotheses H p δ ρ →
  ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ →
  ∃ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n ∧
    ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ *
        ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
      ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T + V.scaledLpNorm H p ξ σ ∧
    ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T ≤ ENNReal.ofReal (C * δ ^ (1 / (2 * (n : ℝ) + 2)))

/-- **Simon Ch. 5, Lemma 2.6 (Lipschitz Approximation Lemma, p. 110)**, `p > n`.  There are
`β = β(n, ℓ, p) ∈ (0, 1/4]` and `C = C(n, ℓ, p)` such that: let `L ∈ (0, 1]`,
`δ ∈ (0, (βL)^{2n+2}]`, 2.3 hold, `σ₀ = δρ`, and let `T₀ = q(ℝⁿ × {0})` (`q` a linear isometry) be a
plane with `dist(x, T₀) ≤ K δ^{1/(2n+2)} σ₀` for `x ∈ spt V ∩ B_{2σ₀}(0)`.  Then there is
`f : Bⁿ_{σ₀/2}(0) → ℝ^ℓ` with `Lip f ≤ L`, `sup |f| ≤ K δ^{1/(2n+2)} σ₀` and
`μ_V(B_{σ₀/2}(0) ∩ (spt V \ q(graph f))) + Hⁿ(B_{σ₀/2}(0) ∩ (q(graph f) \ spt V))
   ≤ C L⁻² ∫_{B_{σ₀}(0)} |p_{T_x M} − p_{T₀}|² dμ_V`.

The book takes (w.l.o.g., after a rotation) `T₀ = T(2σ₀, 0) = ℝⁿ × {0}` from Lemma 2.5, which
satisfies the height hypothesis with `K = 2C₂.₅`; we state the rotation explicitly and allow any
such plane. The statement remains true for every `K` with `β, C` independent of `K`: if the tilt of
`T₀` on `B_{σ₀}` exceeds `c²L²` the estimate holds with `f = 0`; otherwise `T₀` is `CL`-close to
`T(2σ₀, 0)` and the book's construction applies relative to `T₀`.
*Correction:* printed `sup|f| ≤ Cδ^{1/(2n+2)}` lacks the scale factor `σ₀` (cf. 2.7 and proof (7)). -/
def LipschitzApproximationLemma : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β C : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 2)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 2),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.weight (closedBall 0 (δ * ρ / 2) ∩
        (V.support \ q '' graphOver f (closedBall 0 (δ * ρ / 2)))) +
      (μHE[n] : Measure (Amb n ℓ)) (closedBall 0 (δ * ρ / 2) ∩
        (q '' graphOver f (closedBall 0 (δ * ρ / 2)) \ V.support)) ≤
      ENNReal.ofReal (C * (L ^ 2)⁻¹ * ∫ x in closedBall 0 (δ * ρ),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight)

/-- **Simon Ch. 5, Corollary 2.7 (p. 113)**, `p > n`.  With the notation and assumptions of
Lemma 2.6 (as formalized in `LipschitzApproximationLemma`), `β = β(n, ℓ, p)` can be chosen so that
`sup_{ξ ∈ spt V ∩ B_{σ₀/2}(0), σ ∈ (0, σ₀/2]} σ⁻ⁿ ∫_{B_σ(ξ)} |p_{T_x M} − p_{T₀}|² dμ_V ≤ β² L²`
implies `spt V ∩ B_{σ₀/4}(0) = q(graph f) ∩ B_{σ₀/4}(0)` for some `f : Bⁿ_{σ₀/4}(0) → ℝ^ℓ` with
`Lip f ≤ L` and `sup |f| ≤ K δ^{1/(2n+2)} σ₀` (book: `C δ^{1/(2n+2)} σ₀`). -/
def LipschitzGraphCorollary : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧
  ∀ L K : ℝ, 0 < L → L ≤ 1 → 0 ≤ K →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
  ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ,
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) →
    (∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ / 2), ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 →
      V.tiltExcess ξ σ (rotatedPlane q) ≤ β ^ 2 * L ^ 2) →
  ∃ f : Rn n → Rn ℓ, LipschitzOnWith (Real.toNNReal L) f (closedBall 0 (δ * ρ / 4)) ∧
    (∀ x ∈ closedBall (0 : Rn n) (δ * ρ / 4),
      ‖f x‖ ≤ K * δ ^ (1 / (2 * (n : ℝ) + 2)) * (δ * ρ)) ∧
    V.support ∩ closedBall 0 (δ * ρ / 4) =
      q '' graphOver f (closedBall 0 (δ * ρ / 4)) ∩ closedBall 0 (δ * ρ / 4)

/-- **Simon Ch. 5, Lemma 3.1 (Harmonic approximation, p. 114).**  Given `ε > 0` there is
`δ = δ(n, ε) > 0` such that if `f ∈ W^{1,2}(B)`, `B = B̆₁(0)` the open unit ball of `ℝⁿ`, satisfies
`∫_B |∇f|² ≤ 1` and `|∫_B ∇f · ∇ζ dLⁿ| ≤ δ sup |∇ζ|` for every `ζ ∈ C^∞_c(B)`, then there is a
harmonic function `u` on `B` with `∫_B |∇u|² ≤ 1` and `∫_B (u − f)² ≤ ε`.
(`sup|∇ζ| ≤ M` is expressed by quantifying over all bounds `M`; the energy integrals of `u` and
`u − f` are extended-real integrals.) -/
def HarmonicApproximationLemma : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) →
    ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 →
    (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 →
      ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x)| ≤ δ * M) →
    ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - f x‖ₑ ^ 2 ≤ ENNReal.ofReal ε

/-- **Simon Ch. 5, Theorem 4.5 (Tilt-excess Decay Theorem, p. 116)**, `p > n`.  There are
`η, δ₀ ∈ (0, 1/4]` depending only on `n, ℓ, p` such that if 2.3 holds for some `δ ∈ (0, δ₀]`, if
`σ ∈ (0, δρ/2]`, `ξ ∈ spt μ_V ∩ B_{δρ}(0)`, and `T` is any `n`-dimensional subspace, then
`E_*(ξ, ησ, S) ≤ η^{2(1−n/p)} E_*(ξ, σ, T)` for some `n`-dimensional subspace `S`. -/
def TiltExcessDecayTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ η δ₀ : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 4 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
  ∀ σ : ℝ, 0 < σ → σ ≤ δ * ρ / 2 → ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ),
  ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n →
  ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧
    V.tiltExcessStar H p δ ξ (η * σ) S ≤ η ^ (2 * (1 - n / p)) * V.tiltExcessStar H p δ ξ σ T

/-- **Simon Ch. 5, Theorem 5.2 (Allard Regularity Theorem, p. 121).**  If `p > n` is arbitrary,
then there are `δ₀ = δ₀(n, ℓ, p)`, `γ = γ(n, ℓ, p) ∈ (0, 1)` and `C = C(n, ℓ, p)` such that the
hypotheses 5.1 (`AllardHypotheses`) with `δ ≤ δ₀` imply the existence of a linear isometry `q` of
`ℝ^{n+ℓ}` and `u = (u¹, …, u^ℓ) ∈ C^{1,1−n/p}(Bⁿ_{γρ}(0); ℝ^ℓ)` with `Du(0) = 0`,
`spt V ∩ B_{γρ}(0) = q(graph u) ∩ B_{γρ}(0)` and
`ρ⁻¹ sup|u| + sup|Du| + ρ^{1−n/p} sup_{x ≠ y ∈ Bⁿ_{γρ}(0)} |x − y|^{−(1−n/p)} |Du(x) − Du(y)|
   ≤ C δ^{1/(2n+2)}`
(balls closed; see `AllardConclusion`, which also records `u(0) = 0`, automatic since `0 ∈ spt V`).
`δ > 0` is the book's standing convention for 2.3. -/
def AllardRegularityTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p →
  ∃ δ₀ γ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ 0 < γ ∧ γ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Remark 5.3 (p. 122) — the extension of Allard's theorem announced for §6.**
For every `γ ∈ (0, 1)` there is `δ₀ = δ₀(γ, n, ℓ, p) ∈ (0, 1)` such that the hypotheses 5.1 with
`δ ≤ δ₀` imply the conclusion of Theorem 5.2 on `B_{γρ}(0)`.  The constant `C` of the estimate is
allowed to depend on `γ` as well (the remark does not specify it; this is the weaker reading). -/
def AllardRegularityAnyRadius : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ γ : ℝ, 0 < γ → γ < 1 →
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ →
    AllardConclusion V p δ ρ γ C

/-- **Simon Ch. 5, Theorem 6.1 (Conical approximation, p. 124).**  Suppose `Λ > 0`,
`λ, θ, δ ∈ (0, 1/4)`, `ξ ∈ ∂B_{1−θ}(0)`, `V = v(M, θ_V)` has generalized mean curvature
`H ∈ L¹_loc(μ)` in an open `U ⊇ B₁(0)`, `μ = μ_V`,
`|μ(B₁(0))/ω_n − μ(B_λ(0))/(ω_n λⁿ)| + sup_{r ∈ [λ,1]} r^{1−n} ∫_{B_r(0)} |H| dμ ≤ δ`
and `μ(B₁(0)) ≤ Λ`.  Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`
`μ(B_{(1−δ^{1/4})ρ}(ξ)) − Cδ^{1/4}|log λ| ≤ τ⁻ⁿ μ(B_{τρ}(τξ)) ≤ μ(B_{(1+δ^{1/4})ρ}(ξ)) + Cδ^{1/4}|log λ|`
with `C = C(n, ℓ, Λ)`.  (The supremum condition is written pointwise in `r`; the conclusion is in
`[0, ∞]`, where `a − c ≤ b` is written `a ≤ b + c`.) -/
def ConicalApproximationTheorem : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ Λ : ℝ, 0 < Λ → ∃ C : ℝ,
  ∀ (lam θ δ : ℝ), 0 < lam → lam < 1 / 4 → 0 < θ → θ < 1 / 4 → 0 < δ → δ < 1 / 4 →
  ∀ ξ : Amb n ℓ, ‖ξ‖ = 1 - θ →
  ∀ (U : Set (Amb n ℓ)), IsOpen U → closedBall 0 1 ⊆ U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H →
    (∀ r ∈ Icc lam 1,
      |(V.weight (closedBall 0 1)).toReal / unitBallVolume n -
          (V.weight (closedBall 0 lam)).toReal / (unitBallVolume n * lam ^ n)| +
        r ^ (1 - (n : ℝ)) * ∫ x in closedBall (0 : Amb n ℓ) r, ‖H x‖ ∂V.weight ≤ δ) →
    V.weight (closedBall 0 1) ≤ ENNReal.ofReal Λ →
  ∀ ρ ∈ Ioc 0 θ, ∀ τ ∈ Icc (2 * lam) 1,
    V.weight (closedBall ξ ((1 - δ ^ (1 / 4 : ℝ)) * ρ)) ≤
        ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|) ∧
      ENNReal.ofReal (τ ^ n)⁻¹ * V.weight (closedBall (τ • ξ) (τ * ρ)) ≤
        V.weight (closedBall ξ ((1 + δ ^ (1 / 4 : ℝ)) * ρ)) +
          ENNReal.ofReal (C * δ ^ (1 / 4 : ℝ) * |Real.log lam|)

/-- **Simon Ch. 5, Theorem 7.1, first assertion (p. 127).**  If `V = v(M, θ)` has generalized mean
curvature `H` in the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`,
`θ ≥ 1 μ_V`-a.e. in `U`, and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then there are `ρ > 0` and an orthogonal
`Q` of `ℝ^{n+ℓ}` such that, up to a set of `Hⁿ`-measure zero, `Q ∘ τ(M) ∩ B̆_ρ(0) = graph u`
(`τ(x) = x − ξ`), where `u : W → ℝ^ℓ`, `W ∋ 0` open in `ℝⁿ`, is `C^{1,1−n/p}(W; ℝ^ℓ)` with
`u(0) = 0`, `Du(0) = 0`.  (*Erratum:* printed target `ℝ^k` means `ℝ^ℓ`.) -/
def DensityOneRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα 1 (1 - n / p) u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0

/-- **Simon Ch. 5, Theorem 7.1, second assertion (p. 127).**  In the situation of the first
assertion, if moreover `θ` is positive integer-valued `μ_V`-a.e. in `U` and `H = h` on `spt V`
(`μ_V`-a.e.) for some `h ∈ C^{q,α}` in `U` (`q ∈ {0,1,2,…}`, `α ∈ (0,1)`), then for sufficiently
small `ρ > 0` the function `u` is `C^{q+2,α}(W)` and `Θⁿ(μ_V, x) = 1` on `B̆_ρ(ξ) ∩ spt V`.
(The hypotheses `H ∈ Lᵖ_loc`, `θ ≥ 1` of the first assertion are implied here.
*Erratum:* printed "`Θⁿ(μ_V, x) ≡ 1` on `B̆_ρ(ξ)`" must be restricted to `spt μ_V`, as in the third
assertion.  The third assertion (stationarity in a `C^{q+3}` submanifold `N`) is not included: as
printed, `N` is `(n+ℓ)`-dimensional in `ℝ^{n+ℓ}`, hence open, and it reduces to this one with
`h = 0`.) -/
def DensityOneHigherRegularity : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), 0 < α → α < 1 →
    V.HasGeneralizedMeanCurvature H →
    (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) →
  ∀ ξ ∈ U, V.HasDensity ξ 1 →
  ∃ ρ > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (W : Set (Rn n)) (u : Rn n → Rn ℓ),
    IsOpen W ∧ (0 : Rn n) ∈ W ∧ IsHolderCkα (q + 2) α u W ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧
    (μHE[n] : Measure (Amb n ℓ))
      (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u W)) = 0 ∧
    ∀ x ∈ ball ξ ρ ∩ V.support, V.HasDensity x 1

/-- **Simon Ch. 5, Corollary 7.3 (p. 128).**  If `V = v(M, θ)` has generalized mean curvature `H` in
the open set `U ⊆ ℝ^{n+ℓ}`, `H` is locally in `Lᵖ(μ_V)` for some `p > n`, and `θ` is positive
integer-valued `μ_V`-a.e. in `spt V`, then `reg V` is a relatively open dense subset of `spt V`:
it is open in `spt V`, and `spt V` is the closure, taken in `U`, of `reg V` (equivalently,
`sing V` is nowhere dense in `spt V`). -/
def RegularSetOpenDense : Prop :=
  ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U →
  ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p →
    V.HasGeneralizedMeanCurvature H → V.LocallyLp H p →
    (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) →
    (∃ O : Set (Amb n ℓ), IsOpen O ∧ V.regularSet = O ∩ V.support) ∧
      V.support = closure V.regularSet ∩ U

namespace Submission

set_option maxHeartbeats 2000000 in
/-- **Simon Ch. 5, proof of Theorem 5.2 (p. 123): comparing `μ_V` with the Lipschitz graph.**
The book passes from (7) and (9) to (10)–(11) by integrating over the graph of (9) instead of
over `spt V`; this inequality is what that passage uses.  Take `δ₂ = δ_P(n, p)` from
`allard52_density_bounds` (independent of `ℓ`).  If 2.3 holds with `δ ≤ δ₂` and
`spt V ∩ B_R(0) = q(graph f) ∩ B_R(0)` for a `1`-Lipschitz `f` with `f(0) = 0`, `R ≤ δρ`, then
`∫_A Φ(F(x), p_{q(graph Df(x))}) dLⁿ ≤ ∫_{F(A)} Φ(w, p_{T_wV}) dμ_V` for `A ⊆ B̆ⁿ_{R/2}(0)`, where
`F(x) = q(x, f(x))`.  Extending `f` to a Lipschitz `G` on `ℝⁿ`, the area formula (SimonGMT)
writes `μ_V` near the origin as the push-forward of `θ(F) J_F Lⁿ`; the lower density bound shows
that a.e. point of the graph lies in the carrier; blowing up at Lebesgue points of `θ(F) J_F`
identifies `T_{F(x)}V = q(graph Df(x))`; finally `J_F ≥ 1` and `θ ≥ 1` give
`Lⁿ⌞A ≤ J_F Lⁿ⌞A = F^*(Hⁿ⌞F(A))` and `Hⁿ⌞F(A) ≤ μ_V⌞F(A)`. -/
theorem allard52_graph_comparison : ∀ (n : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₂ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), 0 < R → R ≤ δ * ρ → f 0 = 0 → LipschitzOnWith 1 f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → ∀ Φ : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) → ℝ≥0∞, Measurable (Function.uncurry Φ) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ ball 0 (R / 2) → ∫⁻ x in A, Φ (q (graphPoint x (f x))) ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection ≤ ∫⁻ y in q '' graphOver f A, Φ y (V.tangentProj y) ∂V.weight := by
  intro n hn p hp
  obtain ⟨δP, CP, hδP0, hδP8, hCP0, hCPδP, hDB⟩ := Submission.allard52_density_bounds n hn p hp
  refine ⟨δP, hδP0, ?_⟩
  intro ℓ U hU V H δ ρ hδ0 hδle hAH q f R hR0 hRle hf0 hLip hgraph Φ hΦ A hAm hAsub
  have hAH' := hAH
  obtain ⟨hρ0, -, hθ1, -, hBρU, hmass, -⟩ := hAH'
  have hδ8 : δ ≤ 1 / 8 := hδle.trans hδP8
  have hRρ : R ≤ ρ / 8 := by nlinarith
  have hCPδ : CP * δ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hδle hCP0.le) hCPδP
  have hfr : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  -- Step 1: the linear algebra of `graphPoint`.
  have gp_norm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
    simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_add : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' := by
    intro x x' y y'
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_smul : ∀ (c : ℝ) (x : Rn n) (y : Rn ℓ), graphPoint (c • x) (c • y) = c • graphPoint x y := by
    intro c x y
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x - x') (y - y') = graphPoint x y - graphPoint x' y' := by
    intro x x' y y'
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  have gp_zero : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [graphPoint, Fin.append_left, Fin.append_right]
  obtain ⟨Lc, hLc⟩ : ∃ Lc : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ, ∀ z, Lc z = graphPoint z.1 z.2 :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun z => graphPoint z.1 z.2
        map_add' := fun z z' => gp_add z.1 z'.1 z.2 z'.2
        map_smul' := fun c z => gp_smul c z.1 z.2 }, fun z => rfl⟩
  -- Step 2: a global Lipschitz extension `G` of `f` and the graph map `F`.
  obtain ⟨G, hGLip, hGeq⟩ := hLip.extend_finite_dimension
  obtain ⟨F, hFdef⟩ : ∃ F : Rn n → Amb n ℓ, F = fun x => q (graphPoint x (G x)) := ⟨_, rfl⟩
  have hF_apply : ∀ x, F x = q (graphPoint x (G x)) := fun x => by rw [hFdef]
  have hG0 : G 0 = 0 := by rw [← hGeq (mem_closedBall_self hR0.le), hf0]
  have hF0 : F 0 = 0 := by rw [hF_apply, hG0, gp_zero, map_zero]
  have hF_sub : ∀ x x', F x - F x' = q (graphPoint (x - x') (G x - G x')) := by
    intro x x'
    rw [hF_apply, hF_apply, ← map_sub, gp_sub]
  have hF_dist_sq : ∀ x x', ‖F x - F x'‖ ^ 2 = ‖x - x'‖ ^ 2 + ‖G x - G x'‖ ^ 2 := by
    intro x x'
    rw [hF_sub, LinearIsometryEquiv.norm_map, gp_norm]
  have hF_ge : ∀ x x', ‖x - x'‖ ≤ ‖F x - F x'‖ := by
    intro x x'
    have h := hF_dist_sq x x'
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖G x - G x'‖])
  have hG_le : ∀ x x', ‖G x - G x'‖ ≤ (lipschitzExtensionConstant (Rn ℓ) * 1 : ℝ≥0) * ‖x - x'‖ := by
    intro x x'
    simpa [dist_eq_norm] using hGLip.dist_le_mul x x'
  have hF_le : ∀ x x', ‖F x - F x'‖ ≤ ((1 + lipschitzExtensionConstant (Rn ℓ) * 1 : ℝ≥0) : ℝ) * ‖x - x'‖ := by
    intro x x'
    have h := hF_dist_sq x x'
    have h2 := hG_le x x'
    have h3 : ‖F x - F x'‖ ≤ ‖x - x'‖ + ‖G x - G x'‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
      nlinarith [norm_nonneg (x - x'), norm_nonneg (G x - G x')]
    push_cast at h2 ⊢
    nlinarith [norm_nonneg (x - x')]
  have hFLip : LipschitzWith (1 + lipschitzExtensionConstant (Rn ℓ) * 1) F :=
    LipschitzWith.of_dist_le_mul fun x x' => by
      simpa [dist_eq_norm] using hF_le x x'
  have hFcont : Continuous F := hFLip.continuous
  have hFmeas : Measurable F := hFcont.measurable
  have hFinj : Function.Injective F := by
    intro x x' h
    have := hF_ge x x'
    rw [h, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hF_on : ∀ x ∈ closedBall (0 : Rn n) R, F x = q (graphPoint x (f x)) := by
    intro x hx
    rw [hF_apply, ← hGeq hx]
  have hF_norm_sq_le : ∀ x ∈ closedBall (0 : Rn n) R, ‖F x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    intro x hx
    have h := hF_dist_sq x 0
    rw [hF0, sub_zero, sub_zero, hG0, sub_zero, ← hGeq hx] at h
    have h2 : ‖f x‖ ≤ ‖x‖ := by
      have := hLip.dist_le_mul x hx 0 (mem_closedBall_self hR0.le)
      simpa [dist_eq_norm, hf0] using this
    nlinarith [norm_nonneg (f x), norm_nonneg x]
  have hFA : q '' graphOver f A = F '' A := by
    rw [graphOver, image_image]
    refine image_congr fun x hx => ?_
    refine (hF_on x ?_).symm
    have := hAsub hx
    rw [mem_ball, dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]; linarith
  have hFimg_meas : ∀ S : Set (Rn n), MeasurableSet S → MeasurableSet (F '' S) := fun S hS =>
    hS.image_of_continuousOn_injOn hFcont.continuousOn hFinj.injOn
  -- points of `spt V` near the origin lie on the graph
  have hsupp_range : ∀ w ∈ V.support, ‖w‖ ≤ R → w ∈ range F := by
    intro w hw hwR
    have hw' : w ∈ V.support ∩ closedBall 0 R := ⟨hw, by rw [mem_closedBall, dist_zero_right]; exact hwR⟩
    rw [hgraph] at hw'
    obtain ⟨⟨z, ⟨x, hx, rfl⟩, rfl⟩, -⟩ := hw'
    exact ⟨x, hF_on x hx⟩
  have hF_supp : ∀ x ∈ closedBall (0 : Rn n) R, ‖F x‖ ≤ R → F x ∈ V.support := by
    intro x hx hFx
    have : F x ∈ q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R :=
      ⟨⟨graphPoint x (f x), ⟨x, hx, rfl⟩, (hF_on x hx).symm⟩, by
        rw [mem_closedBall, dist_zero_right]; exact hFx⟩
    rw [← hgraph] at this
    exact this.1
  -- Step 3: a measurable piece `M₂` of the carrier on which `θ` agrees with a measurable `θ'`.
  obtain ⟨M₁, hM₁sub, hM₁meas, hM₁ae⟩ := V.nullMeasurableSet_carrier.exists_measurable_subset_ae_eq
  obtain ⟨θ', hθ'meas, hθθ'⟩ : ∃ θ' : Amb n ℓ → ℝ, Measurable θ' ∧
      V.mult =ᵐ[(μHE[n] : Measure (Amb n ℓ)).restrict V.carrier] θ' :=
    ⟨V.aemeasurable_mult.mk V.mult, V.aemeasurable_mult.measurable_mk, V.aemeasurable_mult.ae_eq_mk⟩
  obtain ⟨M₂, hM₂def⟩ : ∃ M₂ : Set (Amb n ℓ), M₂ = M₁ \ toMeasurable
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier) {x | V.mult x ≠ θ' x} := ⟨_, rfl⟩
  have hM₂meas : MeasurableSet M₂ := by
    rw [hM₂def]; exact hM₁meas.diff (measurableSet_toMeasurable _ _)
  have hM₂sub : M₂ ⊆ V.carrier := by
    rw [hM₂def]; exact sdiff_subset.trans hM₁sub
  have hM₂θ : ∀ x ∈ M₂, V.mult x = θ' x := by
    intro x hx
    rw [hM₂def] at hx
    by_contra h
    exact hx.2 (subset_toMeasurable _ _ h)
  have hM₂pos : ∀ x ∈ M₂, 0 < θ' x := fun x hx => hM₂θ x hx ▸ V.mult_pos x (hM₂sub hx)
  have hM₂null : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ M₂) = 0 := by
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (V.carrier \ M₁) = 0 := (ae_eq_set.mp hM₁ae).2
    have h2 : (μHE[n] : Measure (Amb n ℓ)) (toMeasurable ((μHE[n] : Measure (Amb n ℓ)).restrict
        V.carrier) {x | V.mult x ≠ θ' x} ∩ V.carrier) = 0 := by
      rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]
      exact ae_iff.mp hθθ'
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
    rw [hM₂def] at hx
    by_cases hx1 : x ∈ M₁
    · exact Or.inr ⟨not_not.mp fun h => hx.2 ⟨hx1, h⟩, hx.1⟩
    · exact Or.inl ⟨hx.1, hx1⟩
  have hrestr : (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier =
      (μHE[n] : Measure (Amb n ℓ)).restrict M₂ := by
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨hM₂null, ?_⟩)
    rw [sdiff_eq_empty.mpr hM₂sub, measure_empty]
  -- the weight in terms of `M₂` and `θ'`
  have hWGT : ∀ B, MeasurableSet B →
      V.weight B = ∫⁻ w in B ∩ M₂, ENNReal.ofReal (θ' w) ∂μHE[n] := by
    intro B hB
    rw [RectifiableVarifold.weight, withDensity_apply _ hB, hrestr, Measure.restrict_restrict hB]
    exact setLIntegral_congr_fun (hB.inter hM₂meas) (fun w hw => by rw [hM₂θ w hw.2])
  -- `μ_V`-null measurable sets meet `M₂` in `Hⁿ`-null sets
  have hLnull : ∀ S, MeasurableSet S → V.weight S = 0 →
      (μHE[n] : Measure (Amb n ℓ)) (S ∩ M₂) = 0 := by
    intro S hS h0
    rw [hWGT S hS, lintegral_eq_zero_iff hθ'meas.ennreal_ofReal] at h0
    have hfalse : ∀ᵐ w ∂(μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ M₂), False := by
      filter_upwards [h0, ae_restrict_mem (hS.inter hM₂meas)] with w hw hwS
      have := hM₂pos w hwS.2
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hw
      linarith
    rw [← Measure.restrict_eq_zero, ← ae_eq_bot]
    exact Filter.eventually_false_iff_eq_bot.mp hfalse
  -- the carrier outside `spt V` is `Hⁿ`-null
  have hsuppc_meas : MeasurableSet (V.weight.supportᶜ) :=
    (Measure.isClosed_support (μ := V.weight)).isOpen_compl.measurableSet
  have hC1 : (μHE[n] : Measure (Amb n ℓ)) (V.weight.supportᶜ ∩ M₂) = 0 :=
    hLnull _ hsuppc_meas Measure.measure_compl_support
  -- the measurable density on the parameter domain
  obtain ⟨g₀, hg₀def⟩ : ∃ g₀ : Rn n → ℝ≥0∞, g₀ = fun x =>
      ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
        M₂.indicator (fun w => ENNReal.ofReal (θ' w)) (F x) := ⟨_, rfl⟩
  have hg₀meas : Measurable g₀ := by
    rw [hg₀def]
    exact (Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F).ennreal_ofReal.mul
      ((Measurable.indicator hθ'meas.ennreal_ofReal hM₂meas).comp hFmeas)
  have hrange_meas : MeasurableSet (range F) := by
    rw [← image_univ]; exact hFimg_meas _ MeasurableSet.univ
  -- the area formula along the graph
  have hArea : ∀ (S : Set (Rn n)), MeasurableSet S → ∀ g : Amb n ℓ → ℝ≥0∞,
      ∫⁻ y in F '' S, g y ∂μHE[n] =
        ∫⁻ x in S, ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) * g (F x) := by
    intro S hS g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hFLip hS
      hFinj.injOn g
    rwa [hfr] at h
  -- Step 4: near the origin, `μ_V` is the pushforward of `g₀ Lⁿ` under `F`.
  have hREP : ∀ B, MeasurableSet B → B ⊆ ball 0 R → V.weight B = ∫⁻ x in F ⁻¹' B, g₀ x := by
    intro B hB hBR
    rw [hWGT B hB, ← lintegral_inter_add_sdiff _ (B ∩ M₂) hrange_meas]
    have hnull : (μHE[n] : Measure (Amb n ℓ)) ((B ∩ M₂) \ range F) = 0 := by
      refine measure_mono_null ?_ hC1
      intro w hw
      refine ⟨fun hws => hw.2 ?_, hw.1.2⟩
      have hwB := hBR hw.1.1
      rw [mem_ball, dist_zero_right] at hwB
      exact hsupp_range w ⟨V.carrier_subset (hM₂sub hw.1.2), hws⟩ hwB.le
    rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    have hset : B ∩ M₂ ∩ range F = M₂ ∩ F '' (F ⁻¹' B) := by
      rw [image_preimage_eq_inter_range]
      ext w; simp only [mem_inter_iff]; tauto
    rw [hset, ← setLIntegral_indicator hM₂meas, hArea _ (hFmeas hB), hg₀def]

  -- Step 5: the derivative of `F` and the graph planes.
  obtain ⟨DF, hDF, hFderiv⟩ : ∃ DF : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ),
      (∀ B v, DF B v = q (graphPoint v (B v))) ∧
      ∀ x, DifferentiableAt ℝ G x → HasFDerivAt F (DF (fderiv ℝ G x)) x := by
    refine ⟨fun B => (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      (Lc.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod B)), fun B v => by simp [hLc], ?_⟩
    intro x hx
    have h1 : HasFDerivAt (fun x => (x, G x))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ G x)) x :=
      (hasFDerivAt_id x).prodMk hx.hasFDerivAt
    have h2 := (Lc.hasFDerivAt).comp x h1
    have h3 := (q.toContinuousLinearEquiv.hasFDerivAt).comp x h2
    convert h3 using 1
    ext x'
    simp [hF_apply, hLc]
  have hDF_norm : ∀ B v, ‖v‖ ≤ ‖DF B v‖ := by
    intro B v
    rw [hDF, LinearIsometryEquiv.norm_map]
    have := gp_norm v (B v)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖B v‖])
  have hDF_inj : ∀ B, Function.Injective (DF B) := by
    intro B v v' h
    have := hDF_norm B (v - v')
    rw [map_sub, h, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hDF_range : ∀ B, LinearMap.range (DF B : Rn n →ₗ[ℝ] Amb n ℓ) =
      (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v))).map
        q.toLinearEquiv.toLinearMap := by
    intro B
    have hspan : Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (B v)) =
        LinearMap.range ((Lc.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod B) :
          Rn n →L[ℝ] Amb n ℓ) : Rn n →ₗ[ℝ] Amb n ℓ) := by
      rw [← Submodule.span_eq (LinearMap.range _), LinearMap.coe_range]
      congr 1
      ext w
      simp [hLc]
    rw [hspan, ← LinearMap.range_comp]
    congr 1
    ext v
    simp [hDF, hLc]
  have hDF_finrank : ∀ B, Module.finrank ℝ (LinearMap.range (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) = n := by
    intro B
    rw [LinearMap.finrank_range_of_inj (hDF_inj B), hfr]
  have hvol_ball_pos : 0 < (volume : Measure (Rn n)) (closedBall 0 1) :=
    measure_closedBall_pos _ _ one_pos
  have hvol_ball_fin : (volume : Measure (Rn n)) (closedBall 0 1) ≠ ∞ :=
    measure_closedBall_lt_top.ne
  have hball : (μHE[n] : Measure (Rn n)) (closedBall 0 1) = (volume : Measure (Rn n)) (closedBall 0 1) := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
    rw [hfr] at h
    rw [h]
  have hDF_normDet : ∀ B, 1 ≤ LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro B
    have himg := LinearMap.euclideanHausdorffMeasure_image (DF B : Rn n →ₗ[ℝ] Amb n ℓ)
      (closedBall (0 : Rn n) 1)
    rw [hfr, hball] at himg
    have hgLip : LipschitzOnWith 1 (Function.invFun (DF B)) (range (DF B)) := by
      refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
      obtain ⟨v, rfl⟩ := hw
      obtain ⟨v', rfl⟩ := hw'
      rw [Function.leftInverse_invFun (hDF_inj B) v, Function.leftInverse_invFun (hDF_inj B) v',
        dist_eq_norm, dist_eq_norm, ← map_sub]
      simpa using hDF_norm B (v - v')
    have hle : (μHE[n] : Measure (Rn n)) (closedBall 0 1) ≤
        (μHE[n] : Measure (Amb n ℓ)) (DF B '' closedBall 0 1) := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hgLip.mono (image_subset_range (DF B) (closedBall 0 1)))
      have hli : ∀ v, Function.invFun (DF B) (DF B v) = v := Function.leftInverse_invFun (hDF_inj B)
      rw [image_image] at h
      simpa only [hli, image_id', ENNReal.coe_one, one_pow, one_mul] using h
    have himg' : (μHE[n] : Measure (Amb n ℓ)) (DF B '' closedBall 0 1) =
        ENNReal.ofReal (LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) *
          (volume : Measure (Rn n)) (closedBall 0 1) := himg
    rw [himg', hball] at hle
    have h1 : 1 ≤ ENNReal.ofReal (LinearMap.normDet (DF B : Rn n →ₗ[ℝ] Amb n ℓ)) := by
      exact (ENNReal.mul_le_mul_iff_left hvol_ball_pos.ne' hvol_ball_fin).mp (by rwa [one_mul])
    exact ENNReal.one_le_ofReal.mp h1
  have hJ_eq : ∀ x, DifferentiableAt ℝ G x → Poincare.SimonGMT.Chapter02.areaJacobianAt F x =
      LinearMap.normDet (DF (fderiv ℝ G x) : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro x hx
    rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, (hFderiv x hx).fderiv]
  have hJ1 : ∀ x, DifferentiableAt ℝ G x → 1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt F x := by
    intro x hx
    rw [hJ_eq x hx]
    exact hDF_normDet _
  have hGdiff : ∀ᵐ x ∂(volume : Measure (Rn n)), DifferentiableAt ℝ G x :=
    hGLip.ae_differentiableAt
  -- on the open ball `f` and `G` have the same derivative
  have hfG_fderiv : ∀ x : Rn n, ‖x‖ < R → fderiv ℝ f x = fderiv ℝ G x := by
    intro x hx
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : Rn n) R by
      rwa [mem_ball, dist_zero_right])] with x' hx'
    exact hGeq (ball_subset_closedBall hx')

  -- Step 6: an integrable version `g₁` of the density, and its Lebesgue points.
  have hFimg_ball : ∀ x : Rn n, ‖x‖ < 2 * R / 3 → ‖F x‖ < R := by
    intro x hx
    have hx' : x ∈ closedBall (0 : Rn n) R := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have h := hF_norm_sq_le x hx'
    have hx2 : ‖x‖ * ‖x‖ < (2 * R / 3) * (2 * R / 3) := mul_self_lt_mul_self (norm_nonneg x) hx
    nlinarith [norm_nonneg (F x), norm_nonneg x]
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : Rn n → ℝ,
      g₁ = (ball (0 : Rn n) (2 * R / 3)).indicator (fun x => (g₀ x).toReal) := ⟨_, rfl⟩
  have hg₀fin : ∀ x, g₀ x ≠ ∞ := by
    intro x
    rw [hg₀def]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    by_cases h : F x ∈ M₂
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  have hFball_sub : ∀ S : Set (Rn n), S ⊆ ball 0 (2 * R / 3) → F '' S ⊆ ball 0 R := by
    rintro S hS _ ⟨x, hx, rfl⟩
    have := hS hx
    rw [mem_ball, dist_zero_right] at this ⊢
    exact hFimg_ball x this
  have hg₀_lint : ∫⁻ x in ball (0 : Rn n) (2 * R / 3), g₀ x < ∞ := by
    have hS := hFimg_meas _ (measurableSet_ball : MeasurableSet (ball (0 : Rn n) (2 * R / 3)))
    have hsub := hFball_sub _ subset_rfl
    have h := hREP _ hS hsub
    rw [hFinj.preimage_image] at h
    rw [← h]
    calc V.weight (F '' ball 0 (2 * R / 3)) ≤ V.weight (closedBall 0 ρ) :=
          measure_mono (hsub.trans (ball_subset_closedBall.trans
            (closedBall_subset_closedBall (by linarith))))
      _ ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * ρ ^ n)) := hmass
      _ < ∞ := ENNReal.ofReal_lt_top
  have hg₁int : Integrable g₁ := by
    rw [hg₁def, integrable_indicator_iff measurableSet_ball]
    exact integrable_toReal_of_lintegral_ne_top hg₀meas.aemeasurable hg₀_lint.ne
  have hg₁nonneg : ∀ x, 0 ≤ g₁ x := by
    intro x
    rw [hg₁def]
    exact indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x
  have hg₀_g₁ : ∀ S : Set (Rn n), MeasurableSet S → S ⊆ ball 0 (2 * R / 3) →
      ∫⁻ x in S, g₀ x = ENNReal.ofReal (∫ x in S, g₁ x) := by
    intro S hS hSsub
    rw [ofReal_integral_eq_lintegral_ofReal hg₁int.integrableOn (ae_of_all _ hg₁nonneg)]
    refine setLIntegral_congr_fun hS (fun y hy => ?_)
    rw [hg₁def, indicator_of_mem (hSsub hy), ENNReal.ofReal_toReal (hg₀fin y)]
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (μ := (volume : Measure (Rn n))) hg₁int.locallyIntegrable 1
  -- Step 7: volumes of balls and the lower density bound (P.ii).
  have hωpos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hvol_ball : ∀ (x : Rn n) (s : ℝ), 0 ≤ s →
      (volume : Measure (Rn n)) (closedBall x s) = ENNReal.ofReal (unitBallVolume n * s ^ n) := by
    intro x s hs
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [EuclideanSpace.volume_closedBall, Fintype.card_fin, unitBallVolume,
      ← ENNReal.ofReal_pow hs, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.pi ^ (1 / 2 : ℝ)) n,
      ← Real.rpow_mul Real.pi_pos.le, show (1 / 2 : ℝ) * n = n / 2 by ring]
    ring
  have hlow : ∀ y ∈ V.support, ‖y‖ ≤ R → ∀ s, 0 < s → s ≤ ρ / 2 →
      ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall y s) := by
    intro y hy hyR s hs hsρ
    have hy3 : ‖y‖ ≤ 3 * δ * ρ := by nlinarith
    obtain ⟨-, h⟩ := hDB ℓ U hU V H δ ρ hδ0 hδle hAH y hy3 s hs hsρ
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (h hy).1
    have : 0 < unitBallVolume n * s ^ n := mul_pos hωpos (pow_pos hs n)
    nlinarith
  -- Step 8: `F(x) ∈ M₂` for a.e. `x` in `Bⁿ_{R/2}(0)` (the carrier fills the graph).
  have hE : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 → F x ∈ M₂ := by
    filter_upwards [hLeb] with x hx hxR
    by_contra hxM
    have hxB : x ∈ ball (0 : Rn n) (2 * R / 3) := by
      rw [mem_ball, dist_zero_right]; linarith
    have hg₁x : g₁ x = 0 := by
      rw [hg₁def, indicator_of_mem hxB, hg₀def]
      simp [indicator_of_notMem hxM]
    have hlim : Tendsto (fun s : ℝ => ⨍ y in closedBall x s, ‖g₁ y - g₁ x‖)
        (𝓝[>] 0) (𝓝 0) := by
      refine hx (fun _ => x) (fun s => s) tendsto_id ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
      exact mem_closedBall_self (by linarith)
    have hFxR : ‖F x‖ < R := hFimg_ball x (by linarith)
    have hFx_supp : F x ∈ V.support :=
      hF_supp x (by rw [mem_closedBall, dist_zero_right]; linarith) hFxR.le
    set s₀ := min (R - ‖F x‖) (2 * R / 3 - ‖x‖) with hs₀
    have hs₀pos : 0 < s₀ := lt_min (by linarith) (by linarith)
    obtain ⟨s, hs_avg, hs_mem⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (Ioo_mem_nhdsGT hs₀pos)).exists
    have hs0 : 0 < s := hs_mem.1
    have hs1 : s < R - ‖F x‖ := lt_of_lt_of_le hs_mem.2 (min_le_left _ _)
    have hs2 : s < 2 * R / 3 - ‖x‖ := lt_of_lt_of_le hs_mem.2 (min_le_right _ _)
    -- upper bound for the mass of `B_s(F x)`
    have hball_sub : closedBall (F x) s ⊆ ball 0 R := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_zero_right]
      calc ‖w‖ = ‖(w - F x) + F x‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - F x‖ + ‖F x‖ := norm_add_le _ _
        _ < R := by linarith
    have hpre_sub : F ⁻¹' closedBall (F x) s ⊆ closedBall x s := by
      intro x' hx'
      rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx'
      rw [mem_closedBall, dist_eq_norm]
      exact (hF_ge x' x).trans hx'
    have hballx_sub : closedBall x s ⊆ ball (0 : Rn n) (2 * R / 3) := by
      intro x' hx'
      rw [mem_closedBall, dist_eq_norm] at hx'
      rw [mem_ball, dist_zero_right]
      calc ‖x'‖ = ‖(x' - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x' - x‖ + ‖x‖ := norm_add_le _ _
        _ < 2 * R / 3 := by linarith
    have hup : V.weight (closedBall (F x) s) ≤ ENNReal.ofReal (∫ y in closedBall x s, g₁ y) := by
      rw [hREP _ measurableSet_closedBall hball_sub,
        ← hg₀_g₁ _ measurableSet_closedBall hballx_sub]
      exact lintegral_mono_set hpre_sub
    have hlo := hlow (F x) hFx_supp hFxR.le s hs0 (by linarith [norm_nonneg (F x)])
    -- the average bound
    have hvol := hvol_ball x s hs0.le
    have hpos : 0 < unitBallVolume n * s ^ n := mul_pos hωpos (pow_pos hs0 n)
    have havg : ⨍ y in closedBall x s, ‖g₁ y - g₁ x‖ =
        (unitBallVolume n * s ^ n)⁻¹ * ∫ y in closedBall x s, g₁ y := by
      rw [setAverage_eq, measureReal_def, hvol, ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [hg₁x, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hg₁nonneg y)]
    rw [havg] at hs_avg
    have hint_lt : ∫ y in closedBall x s, g₁ y < unitBallVolume n * s ^ n / 2 := by
      have := (inv_mul_lt_iff₀ hpos).mp hs_avg
      linarith
    have := hlo.trans hup
    rw [ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg measurableSet_closedBall
      (fun y _ => hg₁nonneg y))] at this
    linarith

  -- Step 9: `θ ≥ 1` along the graph, a.e.
  have hθge : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 → F x ∈ M₂ → 1 ≤ θ' (F x) := by
    obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Set (Amb n ℓ), S₁ = {w | w ∈ M₂ ∧ θ' w < 1} ∩ ball 0 R := ⟨_, rfl⟩
    have hS₁meas : MeasurableSet S₁ := by
      rw [hS₁]
      exact (hM₂meas.inter (measurableSet_lt hθ'meas measurable_const)).inter measurableSet_ball
    have hS₁null : V.weight S₁ = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hθ1)
      intro w hw
      rw [hS₁] at hw
      simp only [Set.mem_ofPred_eq, not_le]
      rw [hM₂θ w hw.1.1]
      exact hw.1.2
    have h := hREP S₁ hS₁meas (by rw [hS₁]; exact inter_subset_right)
    rw [hS₁null, eq_comm, lintegral_eq_zero_iff hg₀meas, Filter.EventuallyEq,
      ae_restrict_iff' (hFmeas hS₁meas)] at h
    filter_upwards [h, hGdiff] with x hx hxd hxR hxM
    by_contra hlt
    push Not at hlt
    have hmem : x ∈ F ⁻¹' S₁ := by
      rw [mem_preimage, hS₁]
      exact ⟨⟨hxM, hlt⟩, by rw [mem_ball, dist_zero_right]; exact hFimg_ball x (by linarith)⟩
    have h0 := hx hmem
    rw [hg₀def] at h0
    simp only [Pi.zero_apply, indicator_of_mem hxM, mul_eq_zero, ENNReal.ofReal_eq_zero] at h0
    rcases h0 with h0 | h0
    · linarith [hJ1 x hxd]
    · linarith [hM₂pos (F x) hxM]
  -- integrals against the weight
  have hint_weight : ∀ h : Amb n ℓ → ℝ,
      ∫ w, h w ∂V.weight = ∫ w in V.carrier, h w * V.mult w ∂μHE[n] := by
    intro h
    rw [RectifiableVarifold.weight, integral_withDensity_eq_integral_toReal_smul₀
      V.aemeasurable_mult.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem₀ V.nullMeasurableSet_carrier] with w hw
    rw [ENNReal.toReal_ofReal (V.mult_pos w hw).le, smul_eq_mul, mul_comm]
  -- the local representation as an identity of measures
  have hμν : V.weight.restrict (ball 0 R) =
      (Measure.map F ((volume : Measure (Rn n)).withDensity g₀)).restrict (ball 0 R) := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS,
      Measure.map_apply hFmeas (hS.inter measurableSet_ball),
      withDensity_apply _ (hFmeas (hS.inter measurableSet_ball)),
      hREP _ (hS.inter measurableSet_ball) inter_subset_right]
  -- change of variables `x' = x + r v` on `ℝⁿ`
  have hcov : ∀ (k : Rn n → ℝ) (x : Rn n) (r : ℝ), 0 < r →
      ∫ v, k (x + r • v) = (r⁻¹) ^ n * ∫ x', k x' := by
    intro k x r hr
    have h1 := Measure.integral_comp_smul (volume : Measure (Rn n)) (fun u => k (x + u)) r
    rw [hfr] at h1
    rw [h1, integral_add_left_eq_self, abs_of_pos (inv_pos.mpr (pow_pos hr n)), inv_pow,
      smul_eq_mul]
  -- Step 10: the approximate tangent planes along the graph.
  have hTan : ∀ᵐ x ∂(volume : Measure (Rn n)), ‖x‖ < R / 2 →
      V.tangentProj (F x) =
        (LinearMap.range (DF (fderiv ℝ G x) : Rn n →ₗ[ℝ] Amb n ℓ)).starProjection := by
    filter_upwards [hLeb, hGdiff, hE] with x hxLeb hxd hxE hxR
    have hxM := hxE hxR
    obtain ⟨B, hB⟩ : ∃ B, B = fderiv ℝ G x := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D, D = DF B := ⟨_, rfl⟩
    rw [← hB, ← hD]
    have hDer : HasFDerivAt F D x := by rw [hD, hB]; exact hFderiv x hxd
    have hFxR : ‖F x‖ < 5 * R / 6 := by
      have hx' : x ∈ closedBall (0 : Rn n) R := by
        rw [mem_closedBall, dist_zero_right]; linarith
      have h := hF_norm_sq_le x hx'
      have hx2 : ‖x‖ * ‖x‖ < (R / 2) * (R / 2) := mul_self_lt_mul_self (norm_nonneg x) hxR
      nlinarith [norm_nonneg (F x)]
    have hg₁x : g₁ x = LinearMap.normDet (D : Rn n →ₗ[ℝ] Amb n ℓ) * V.mult (F x) := by
      rw [hg₁def, indicator_of_mem (show x ∈ ball (0 : Rn n) (2 * R / 3) by
        rw [mem_ball, dist_zero_right]; linarith), hg₀def]
      simp only [indicator_of_mem hxM]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F x),
        ENNReal.toReal_ofReal (hM₂pos (F x) hxM).le, hJ_eq x hxd, hM₂θ (F x) hxM, ← hB, ← hD]
    have hHW : Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier
        V.mult (F x) (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ)) := by
      refine ⟨hD ▸ hDF_finrank B, fun φ => ?_⟩
      -- the support radius and a bound of the test function
      obtain ⟨Rφ, hRφ1, hRφ⟩ : ∃ Rφ : ℝ, 1 ≤ Rφ ∧ ∀ z : Amb n ℓ, Rφ < ‖z‖ → φ z = 0 := by
        obtain ⟨C, hC⟩ := (φ.hasCompactSupport.isCompact.isBounded).subset_closedBall 0
        refine ⟨max C 1, le_max_right _ _, fun z hz => image_eq_zero_of_notMem_tsupport fun hzt => ?_⟩
        have := hC hzt
        rw [mem_closedBall, dist_zero_right] at this
        linarith [le_max_left C 1]
      obtain ⟨Cφ, hCφ⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.continuous
      -- (a) the weighted blow-up as a rescaled integral against the weight
      have h6a : ∀ r : ℝ, 0 < r →
          ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F x) r '' V.carrier,
            φ z * V.mult (F x + r • z) ∂μHE[n] =
          (r⁻¹) ^ n * ∫ w, φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) ∂V.weight := by
        intro r hr
        have hi := (Poincare.SimonGMT.Chapter04.blowUpHomeomorph (F x) hr).symm.measurableEmbedding.integral_map
          (μ := (μHE[n] : Measure (Amb n ℓ)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r '' V.carrier))
          (fun w => φ (Poincare.SimonGMT.Chapter04.blowUpHomeomorph (F x) hr w) * V.mult w)
        rw [Poincare.SimonGMT.Chapter04.map_inverse_blowUp_carrier (F x) hr V.carrier,
          integral_smul_measure, ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_pos.mpr hr).le,
          smul_eq_mul] at hi
        have hbl : ∀ z, Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x + r • z) = z := by
          intro z
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr.ne']
        simp only [Poincare.SimonGMT.Chapter04.blowUpHomeomorph_symm_apply,
          Poincare.SimonGMT.Chapter04.blowUpHomeomorph_apply, hbl] at hi
        rw [hint_weight]
        exact hi.symm
      -- (b) localisation: near `F x` the weight is the pushforward of `g₀ Lⁿ`
      have hcontψ : ∀ r : ℝ, Continuous (fun w : Amb n ℓ =>
          φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w)) := by
        intro r
        unfold Poincare.SimonGMT.Chapter03.blowUpMap
        fun_prop
      have h6b : ∀ r : ℝ, 0 < r → r * Rφ < R / 6 →
          ∫ w, φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) ∂V.weight =
          ∫ x', g₁ x' * φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x')) := by
        intro r hr hrR
        have hsupp : ∀ w, r * Rφ < ‖w - F x‖ →
            φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) = 0 := by
          intro w hw
          apply hRφ
          rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
            Real.norm_of_nonneg (inv_pos.mpr hr).le, lt_inv_mul_iff₀ hr]
          exact hw
        have hout : ∀ w ∉ ball (0 : Amb n ℓ) R,
            φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r w) = 0 := by
          intro w hw
          apply hsupp
          rw [mem_ball, dist_zero_right, not_lt] at hw
          have := norm_sub_norm_le w (F x)
          linarith
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, hμν,
          setIntegral_eq_integral_of_forall_compl_eq_zero hout,
          integral_map hFmeas.aemeasurable (hcontψ r).aestronglyMeasurable,
          integral_withDensity_eq_integral_toReal_smul₀ hg₀meas.aemeasurable
            (ae_of_all _ fun x' => (hg₀fin x').lt_top)]
        refine integral_congr_ae (ae_of_all _ fun x' => ?_)
        simp only [smul_eq_mul]
        by_cases hφ : φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x')) = 0
        · rw [hφ, mul_zero, mul_zero]
        · congr 1
          have h1 : ‖F x' - F x‖ ≤ r * Rφ := by
            by_contra h
            exact hφ (hsupp _ (not_le.mp h))
          have h2 := (hF_ge x' x).trans h1
          have h3 : x' ∈ ball (0 : Rn n) (2 * R / 3) := by
            rw [mem_ball, dist_zero_right]
            calc ‖x'‖ = ‖x + (x' - x)‖ := by rw [add_sub_cancel]
              _ ≤ ‖x‖ + ‖x' - x‖ := norm_add_le _ _
              _ < 2 * R / 3 := by linarith
          rw [hg₁def, indicator_of_mem h3]
      -- (d) the blow-up limit on the parameter domain
      have hsuppQ : ∀ r : ℝ, 0 < r → ∀ v : Rn n, Rφ < ‖v‖ →
          φ (r⁻¹ • (F (x + r • v) - F x)) = 0 := by
        intro r hr v hv
        apply hRφ
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le, lt_inv_mul_iff₀ hr]
        have := hF_ge (x + r • v) x
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at this
        calc r * Rφ < r * ‖v‖ := mul_lt_mul_of_pos_left hv hr
          _ ≤ _ := this
      have hnotmem : ∀ v : Rn n, v ∉ closedBall (0 : Rn n) Rφ → Rφ < ‖v‖ := by
        intro v hv
        rwa [mem_closedBall, dist_zero_right, not_le] at hv
      have hcontQ : ∀ r : ℝ, Continuous (fun v : Rn n => φ (r⁻¹ • (F (x + r • v) - F x))) := by
        intro r
        have hφc := φ.continuous
        fun_prop
      have hintQ : ∀ r : ℝ, 0 < r → Integrable (fun v : Rn n => φ (r⁻¹ • (F (x + r • v) - F x))) := by
        intro r hr
        exact (hcontQ r).integrable_of_hasCompactSupport (HasCompactSupport.intro
          (isCompact_closedBall (0 : Rn n) Rφ) (fun v hv => hsuppQ r hr v (hnotmem v hv)))
      have hintg : ∀ r : ℝ, 0 < r → Integrable (fun v : Rn n => g₁ (x + r • v)) := by
        intro r hr
        exact (hg₁int.comp_add_left x).comp_smul hr.ne'
      have hT2 : Tendsto (fun r : ℝ => ∫ v, φ (r⁻¹ • (F (x + r • v) - F x))) (𝓝[>] 0)
          (𝓝 (∫ v, φ (D v))) := by
        refine tendsto_integral_filter_of_dominated_convergence
          ((closedBall (0 : Rn n) Rφ).indicator (fun _ => Cφ)) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun r => (hcontQ r).aestronglyMeasurable
        · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
          refine ae_of_all _ fun v => ?_
          by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
          · rw [indicator_of_mem hv]
            exact hCφ _
          · rw [indicator_of_notMem hv, hsuppQ r hr v (hnotmem v hv), norm_zero]
        · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
            measurableSet_closedBall
        · refine ae_of_all _ fun v => ?_
          have hpath : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
          have hD0 : HasFDerivAt F D (x + (0 : ℝ) • v) := by simpa using hDer
          have hcomp := (hD0.comp_hasDerivAt (0 : ℝ) hpath).tendsto_slope_zero_right
          simp only [zero_add, zero_smul, add_zero, Function.comp_def] at hcomp
          exact (φ.continuous.tendsto _).comp hcomp
      have hLebx : Tendsto (fun r : ℝ => ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖)
          (𝓝[>] 0) (𝓝 0) := by
        refine hxLeb (fun _ => x) (fun r => Rφ * r) ?_ ?_
        · refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have : Tendsto (fun r : ℝ => Rφ * r) (𝓝 0) (𝓝 (Rφ * 0)) :=
              (continuous_const.mul continuous_id).tendsto 0
            rw [mul_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
            exact mul_pos (by linarith) hr
        · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
          have : 0 ≤ Rφ * r := mul_nonneg (by linarith) hr.le
          exact mem_closedBall_self (by linarith)
      have hT1 : Tendsto (fun r : ℝ => (∫ v, g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x))) -
          g₁ x * ∫ v, φ (r⁻¹ • (F (x + r • v) - F x))) (𝓝[>] 0) (𝓝 0) := by
        have hlim : Tendsto (fun r : ℝ => Cφ * (unitBallVolume n * Rφ ^ n) *
            ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖) (𝓝[>] 0) (𝓝 0) := by
          have h := hLebx.const_mul (Cφ * (unitBallVolume n * Rφ ^ n))
          rwa [mul_zero] at h
        refine squeeze_zero_norm' ?_ hlim
        filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        have hi1 : Integrable (fun v : Rn n => g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x))) :=
          (hintg r hr).mul_bdd (hcontQ r).aestronglyMeasurable (ae_of_all _ fun v => hCφ _)
        have hi2 : Integrable (fun v : Rn n => g₁ x * φ (r⁻¹ • (F (x + r • v) - F x))) :=
          (hintQ r hr).const_mul _
        rw [← integral_const_mul, ← integral_sub hi1 hi2]
        have hmem : ∀ v : Rn n, (x + r • v ∈ closedBall x (Rφ * r)) ↔ v ∈ closedBall (0 : Rn n) Rφ := by
          intro v
          rw [mem_closedBall, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hr.le, dist_zero_right, mul_comm Rφ r]
          exact ⟨fun h => le_of_mul_le_mul_left h hr, fun h => mul_le_mul_of_nonneg_left h hr.le⟩
        have hind : ∀ v : Rn n, (closedBall (0 : Rn n) Rφ).indicator
            (fun v => ‖g₁ (x + r • v) - g₁ x‖) v =
            (closedBall x (Rφ * r)).indicator (fun y => ‖g₁ y - g₁ x‖) (x + r • v) := by
          intro v
          by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
          · rw [indicator_of_mem hv, indicator_of_mem ((hmem v).mpr hv)]
          · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv ((hmem v).mp h))]
        have hbound_int : Integrable (fun v : Rn n => Cφ * (closedBall (0 : Rn n) Rφ).indicator
            (fun v => ‖g₁ (x + r • v) - g₁ x‖) v) := by
          refine Integrable.const_mul ?_ _
          refine IntegrableOn.integrable_indicator ?_ measurableSet_closedBall
          exact ((hintg r hr).integrableOn.sub (integrableOn_const measure_closedBall_lt_top.ne)).norm
        have hpos : 0 < unitBallVolume n * (Rφ * r) ^ n :=
          mul_pos hωpos (pow_pos (mul_pos (by linarith) hr) n)
        have havg : ∫ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ =
            unitBallVolume n * (Rφ * r) ^ n * ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ := by
          rw [setAverage_eq, measureReal_def, hvol_ball x _ (by positivity),
            ENNReal.toReal_ofReal hpos.le, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        calc ‖∫ v, (g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x)) -
              g₁ x * φ (r⁻¹ • (F (x + r • v) - F x)))‖
            ≤ ∫ v, Cφ * (closedBall (0 : Rn n) Rφ).indicator
                (fun v => ‖g₁ (x + r • v) - g₁ x‖) v := by
              refine norm_integral_le_of_norm_le hbound_int (ae_of_all _ fun v => ?_)
              rw [← sub_mul, norm_mul]
              by_cases hv : v ∈ closedBall (0 : Rn n) Rφ
              · rw [indicator_of_mem hv, mul_comm]
                exact mul_le_mul_of_nonneg_right (hCφ _) (norm_nonneg _)
              · rw [indicator_of_notMem hv, hsuppQ r hr v (hnotmem v hv), norm_zero, mul_zero,
                  mul_zero]
          _ = Cφ * (unitBallVolume n * Rφ ^ n) * ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖ := by
              rw [integral_const_mul, funext hind,
                hcov (fun y => (closedBall x (Rφ * r)).indicator (fun y => ‖g₁ y - g₁ x‖) y) x r hr,
                integral_indicator measurableSet_closedBall, havg, mul_pow, inv_pow]
              have hrn : (r ^ n)⁻¹ * r ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero n hr.ne')
              calc Cφ * ((r ^ n)⁻¹ * (unitBallVolume n * (Rφ ^ n * r ^ n) *
                    ⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖))
                  = Cφ * (unitBallVolume n * Rφ ^ n) *
                      (⨍ y in closedBall x (Rφ * r), ‖g₁ y - g₁ x‖) * ((r ^ n)⁻¹ * r ^ n) := by ring
                _ = _ := by rw [hrn, mul_one]
      have h6d : Tendsto (fun r : ℝ => ∫ v, g₁ (x + r • v) * φ (r⁻¹ • (F (x + r • v) - F x)))
          (𝓝[>] 0) (𝓝 (g₁ x * ∫ v, φ (D v))) := by
        have h := hT1.add (hT2.const_mul (g₁ x))
        rw [zero_add] at h
        exact h.congr' (Eventually.of_forall fun r => sub_add_cancel _ _)
      -- (e) the limit is `θ(F x)` times the plane integral
      have h6e : g₁ x * ∫ v, φ (D v) = V.mult (F x) *
          ∫ z in (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)), φ z ∂μHE[n] := by
        have hmeasP : (μHE[n] : Measure (Amb n ℓ)).restrict
            (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) =
            ENNReal.ofReal (LinearMap.normDet (D : Rn n →ₗ[ℝ] Amb n ℓ)) •
              Measure.map D (volume : Measure (Rn n)) := by
          ext S hS
          rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply D.continuous.measurable hS,
            smul_eq_mul]
          have h1 : S ∩ (LinearMap.range (D : Rn n →ₗ[ℝ] Amb n ℓ) : Set (Amb n ℓ)) =
              (D : Rn n →ₗ[ℝ] Amb n ℓ) '' ((D : Rn n →ₗ[ℝ] Amb n ℓ) ⁻¹' S) := by
            rw [image_preimage_eq_inter_range, LinearMap.coe_range]
          rw [h1]
          have h2 := LinearMap.euclideanHausdorffMeasure_image (D : Rn n →ₗ[ℝ] Amb n ℓ)
            ((D : Rn n →ₗ[ℝ] Amb n ℓ) ⁻¹' S)
          have h3 := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Rn n)
          rw [hfr] at h2 h3
          rw [h3] at h2
          exact h2
        rw [hmeasP, integral_smul_measure,
          integral_map D.continuous.aemeasurable (map_continuous φ).aestronglyMeasurable,
          ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _), hg₁x, smul_eq_mul]
        ring
      rw [← h6e]
      refine h6d.congr' ?_
      have hr₀ : 0 < R / (6 * Rφ) := div_pos hR0 (by linarith)
      filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
      have hrR : r * Rφ < R / 6 := by
        have h := hr.2
        rw [lt_div_iff₀ (by linarith)] at h
        linarith
      rw [h6a r hr.1, h6b r hr.1 hrR]
      exact hcov (fun x' => g₁ x' * φ (Poincare.SimonGMT.Chapter03.blowUpMap (F x) r (F x'))) x r hr.1
    have hθx : V.mult (F x) ≠ 0 := (V.mult_pos _ (hM₂sub hxM)).ne'
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (F x) P := ⟨_, hHW⟩
    have hch := Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique hθx
      (Classical.choose_spec hex) hHW
    unfold RectifiableVarifold.tangentProj
    rw [dite_eq_left hex]
    simp only [hch]

  -- Step 11: the comparison `Lⁿ⌞A ≤ (Jacobian) ≤ Hⁿ⌞F(A) ≤ μ_V⌞F(A)`.
  have hA_ball : ∀ x ∈ A, ‖x‖ < R / 2 := by
    intro x hx
    have := hAsub hx
    rwa [mem_ball, dist_zero_right] at this
  have hFA_sub : F '' A ⊆ ball 0 R :=
    hFball_sub A (fun x hx => by
      rw [mem_ball, dist_zero_right]; linarith [hA_ball x hx])
  have hmeas_le : (μHE[n] : Measure (Amb n ℓ)).restrict (F '' A) ≤ V.weight.restrict (F '' A) := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS, inter_comm,
      ← image_inter_preimage]
    have hT : MeasurableSet (A ∩ F ⁻¹' S) := hAm.inter (hFmeas hS)
    rw [hREP _ (hFimg_meas _ hT) ((image_mono inter_subset_left).trans hFA_sub),
      hFinj.preimage_image]
    have h := hArea _ hT (fun _ => 1)
    rw [setLIntegral_one] at h
    rw [h]
    refine lintegral_mono_ae ((ae_restrict_iff' hT).mpr ?_)
    filter_upwards [hE, hθge] with x hxE hxθ hxT
    have hxR := hA_ball x hxT.1
    have hxM := hxE hxR
    rw [hg₀def, mul_one]
    simp only [indicator_of_mem hxM]
    exact le_mul_of_one_le_right zero_le (ENNReal.one_le_ofReal.mpr (hxθ hxR hxM))
  have hgood : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∈ A →
      Φ (q (graphPoint x (f x)))
        ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
          q.toLinearEquiv.toLinearMap).starProjection ≤
      ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
        Φ (F x) (V.tangentProj (F x)) := by
    filter_upwards [hTan, hGdiff] with x hxT hxd hxA
    have hxR := hA_ball x hxA
    have hproj : ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
        q.toLinearEquiv.toLinearMap).starProjection = V.tangentProj (F x) := by
      rw [hxT hxR, hfG_fderiv x (by linarith)]
      simp only [hDF_range]
    rw [hproj, ← hF_on x (by rw [mem_closedBall, dist_zero_right]; linarith)]
    exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr (hJ1 x hxd))
  calc ∫⁻ x in A, Φ (q (graphPoint x (f x)))
        ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map
          q.toLinearEquiv.toLinearMap).starProjection
      ≤ ∫⁻ x in A, ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt F x) *
          Φ (F x) (V.tangentProj (F x)) :=
        lintegral_mono_ae ((ae_restrict_iff' hAm).mpr hgood)
    _ = ∫⁻ y in F '' A, Φ y (V.tangentProj y) ∂μHE[n] :=
        (hArea A hAm (fun y => Φ y (V.tangentProj y))).symm
    _ ≤ ∫⁻ y in F '' A, Φ y (V.tangentProj y) ∂V.weight := lintegral_mono' hmeas_le le_rfl
    _ = ∫⁻ y in q '' graphOver f A, Φ y (V.tangentProj y) ∂V.weight := by rw [hFA]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

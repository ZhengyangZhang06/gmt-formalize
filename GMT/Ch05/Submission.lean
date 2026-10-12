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
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

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

/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Poincaré inequality, segment step: for a `C¹`
function `φ` on `ℝⁿ` and `x, y ∈ ℝⁿ`,
`|φ(x) - φ(y)|² ≤ |x - y|² ∫_{[0,1]} |∇φ((1 - t) y + t x)|² dt` in `[0, ∞]`.  Along the segment
`γ(t) = (1 - t) y + t x` the chain rule and the fundamental theorem of calculus give
`φ(x) - φ(y) = ∫₀¹ Dφ(γ(t))(x - y) dt`; then `|Dφ(z) v| ≤ |v| |∇φ(z)|` (the gradient is the
Riesz representative of `Dφ(z)`), and Cauchy–Schwarz on the unit interval (`L¹ ≤ L²` for a
probability measure) bounds the square of `∫₀¹ |∇φ(γ(t))| dt`. -/
theorem poincare_c1_segment_sq_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ x y : Rn n, ‖φ x - φ y‖ₑ ^ 2 ≤ ‖x - y‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
  intro n φ hφ x y
  set γ : ℝ → Rn n := fun t => (1 - t) • y + t • x with hγ
  -- 1. the segment and the chain rule
  have hγd : ∀ t, HasDerivAt γ (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) • y) (-y) t := by
      simpa using ((hasDerivAt_id t).const_sub 1).smul_const y
    have h2 : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    convert h1.add h2 using 1
    abel
  have hud : ∀ t, HasDerivAt (fun t => φ (γ t)) (fderiv ℝ φ (γ t) (x - y)) t := fun t =>
    ((hφ.differentiable one_ne_zero (γ t)).hasFDerivAt).comp_hasDerivAt t (hγd t)
  have hγc : Continuous γ := by fun_prop
  have hderc : Continuous (fun t => fderiv ℝ φ (γ t) (x - y)) :=
    ((hφ.continuous_fderiv one_ne_zero).comp hγc).clm_apply continuous_const
  -- 2. fundamental theorem of calculus
  have hFTC : ∫ t in (0:ℝ)..1, fderiv ℝ φ (γ t) (x - y) = φ x - φ y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hud t)
      (hderc.intervalIntegrable 0 1)]
    simp [γ]
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  -- 3. pointwise Cauchy–Schwarz: |Dφ(z) v| ≤ |v| |∇φ(z)|
  have hpt : ∀ t, ‖fderiv ℝ φ (γ t) (x - y)‖ₑ ≤ ‖x - y‖ₑ * ‖gradient φ (γ t)‖ₑ := by
    intro t
    have : ‖fderiv ℝ φ (γ t) (x - y)‖ ≤ ‖x - y‖ * ‖gradient φ (γ t)‖ := by
      calc ‖fderiv ℝ φ (γ t) (x - y)‖ ≤ ‖fderiv ℝ φ (γ t)‖ * ‖x - y‖ := (fderiv ℝ φ (γ t)).le_opNorm _
        _ = ‖x - y‖ * ‖gradient φ (γ t)‖ := by
          rw [gradient, LinearIsometryEquiv.norm_map, mul_comm]
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal this
  have hle : ‖φ x - φ y‖ₑ ≤ ‖x - y‖ₑ * ∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ := by
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0:ℝ) 1, fderiv ℝ φ (γ t) (x - y)‖ₑ
        ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ φ (γ t) (x - y)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, ‖x - y‖ₑ * ‖gradient φ (γ t)‖ₑ := lintegral_mono fun t => hpt t
      _ = ‖x - y‖ₑ * ∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ :=
          lintegral_const_mul' _ _ enorm_ne_top
  -- 4. Cauchy–Schwarz on (0,1] (a probability space): (∫ a)^2 ≤ ∫ a^2
  have hCS : (∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ) ^ 2 ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ ^ 2 := by
    set μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1) with hμ
    have hμ1 : μ univ = 1 := by
      rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
    have : IsFiniteMeasure μ := ⟨by rw [hμ1]; exact ENNReal.one_lt_top⟩
    have hh : AEStronglyMeasurable (fun t => gradient φ (γ t)) μ := (hgc.comp hγc).aestronglyMeasurable
    have key := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := μ) one_le_two hh
    rw [eLpNorm_one_eq_lintegral_enorm hh,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hh] at key
    have e1 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
    rw [e1, hμ1, ENNReal.one_rpow, mul_one] at key
    have e2 : ∀ t, ‖gradient φ (γ t)‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖gradient φ (γ t)‖ₑ ^ 2 := fun t => by
      simp
    simp_rw [e2] at key
    calc (∫⁻ t, ‖gradient φ (γ t)‖ₑ ∂μ) ^ 2
        ≤ ((∫⁻ t, ‖gradient φ (γ t)‖ₑ ^ 2 ∂μ) ^ (1 / (2 : ℝ≥0∞).toReal)) ^ 2 := by gcongr
      _ = ∫⁻ t, ‖gradient φ (γ t)‖ₑ ^ 2 ∂μ := by
        rw [← ENNReal.rpow_mul_natCast]
        norm_num
  -- 5. combine
  calc ‖φ x - φ y‖ₑ ^ 2 ≤ (‖x - y‖ₑ * ∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ) ^ 2 := by gcongr
    _ = ‖x - y‖ₑ ^ 2 * (∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ) ^ 2 := mul_pow _ _ _
    _ ≤ ‖x - y‖ₑ ^ 2 * ∫⁻ t in Ioc (0:ℝ) 1, ‖gradient φ (γ t)‖ₑ ^ 2 := by gcongr
    _ ≤ ‖x - y‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        gcongr
        exact Ioc_subset_Icc_self
/-- **Convex-combination averaging bound on a ball** (the change-of-variables step in the proof of
the Poincaré inequality on convex domains, Gilbarg–Trudinger Lemma 7.16; Evans §5.8.1).  For a
measurable `h ≥ 0`, `r > 0` and `t ∈ [0, 1]`,
`∫_{B_r} ∫_{B_r} h((1 - t) y + t x) dy dx ≤ 2ⁿ |B_r| ∫_{B_r} h`.

Since `B_r` is convex, `(1 - t) y + t x ∈ B_r`.  One of the two variables has coefficient
`s ≥ 1/2`; substituting `z = c + s •` (that variable) (Jacobian `sⁿ`, `Measure.map_addHaar_smul`
and translation invariance) bounds the integral in that variable by `s⁻ⁿ ∫_{B_r} h ≤ 2ⁿ ∫_{B_r} h`,
and integrating this constant over the other variable (after Tonelli when `t ≥ 1/2`) gives the
claim. -/
theorem poincare_ball_convex_combination_bound : ∀ (n : ℕ) (h : Rn n → ℝ≥0∞), Measurable h → ∀ r t : ℝ, 0 < r → 0 ≤ t → t ≤ 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, h ((1 - t) • y + t • x) ≤ (2 : ℝ≥0∞) ^ n * volume (ball (0 : Rn n) r) * ∫⁻ z in ball (0 : Rn n) r, h z := by
  intro n h hh r t hr ht0 ht1
  set B := ball (0 : Rn n) r with hB
  -- 1. affine change of variables: ∫ F(c + s x) dx = |s|^{-n} ∫ F
  have affine : ∀ (F : Rn n → ℝ≥0∞), Measurable F → ∀ (c : Rn n) {s : ℝ}, s ≠ 0 →
      ∫⁻ x, F (c + s • x) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
    intro F hF c s hs
    have hm : Measurable (fun z : Rn n => F (c + z)) := hF.comp (measurable_const_add c)
    have hmap := lintegral_map (μ := (volume : Measure (Rn n))) hm
      (measurable_const_smul s : Measurable fun x : Rn n => s • x)
    rw [← hmap, Measure.map_addHaar_smul volume hs, lintegral_smul_measure,
      lintegral_add_left_eq_self (μ := (volume : Measure (Rn n))) F c, smul_eq_mul,
      finrank_euclideanSpace_fin]
  -- 2. convexity of the ball
  have hmem : ∀ x ∈ B, ∀ y ∈ B, (1 - t) • y + t • x ∈ B := fun x hx y hy =>
    convex_ball (0 : Rn n) r hy hx (by linarith) ht0 (by ring)
  -- 3. one-variable bound when the coefficient of the integration variable is ≥ 1/2
  have key : ∀ (c : Rn n) (s : ℝ), 1 / 2 ≤ s → (∀ x ∈ B, c + s • x ∈ B) →
      ∫⁻ x in B, h (c + s • x) ≤ (2 : ℝ≥0∞) ^ n * ∫⁻ z in B, h z := by
    intro c s hs hcs
    have hs' : 0 < s := by linarith
    calc ∫⁻ x in B, h (c + s • x) = ∫⁻ x in B, B.indicator h (c + s • x) := by
          refine setLIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
          rw [indicator_of_mem (hcs x hx)]
      _ ≤ ∫⁻ x, B.indicator h (c + s • x) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, B.indicator h z :=
          affine _ (hh.indicator measurableSet_ball) c hs'.ne'
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in B, h z := by
          rw [lintegral_indicator measurableSet_ball]
      _ ≤ (2 : ℝ≥0∞) ^ n * ∫⁻ z in B, h z := by
          gcongr
          have h1 : |(s ^ n)⁻¹| ≤ (2 : ℝ) ^ n := by
            rw [abs_of_pos (by positivity), ← inv_pow]
            exact pow_le_pow_left₀ (by positivity) (inv_le_of_inv_le₀ (by norm_num) (by linarith)) n
          calc ENNReal.ofReal |(s ^ n)⁻¹| ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := ENNReal.ofReal_le_ofReal h1
            _ = (2 : ℝ≥0∞) ^ n := by rw [ENNReal.ofReal_pow (by norm_num)]; simp
  have hH : Measurable (fun p : Rn n × Rn n => h ((1 - t) • p.2 + t • p.1)) :=
    hh.comp (by fun_prop : Continuous fun p : Rn n × Rn n => (1 - t) • p.2 + t • p.1).measurable
  rcases le_or_gt (1 / 2 : ℝ) t with ht | ht
  · -- 4. t ≥ 1/2: Tonelli, then substitute in x
    rw [lintegral_lintegral_swap hH.aemeasurable]
    calc ∫⁻ y in B, ∫⁻ x in B, h ((1 - t) • y + t • x)
        ≤ ∫⁻ y in B, (2 : ℝ≥0∞) ^ n * ∫⁻ z in B, h z := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          exact key ((1 - t) • y) t ht (fun x hx => hmem x hx y hy)
      _ = (2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, h z := by
          rw [setLIntegral_const]; ring
  · -- 5. t < 1/2: substitute in y directly
    calc ∫⁻ x in B, ∫⁻ y in B, h ((1 - t) • y + t • x)
        ≤ ∫⁻ x in B, (2 : ℝ≥0∞) ^ n * ∫⁻ z in B, h z := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          have e : ∀ y : Rn n, (1 - t) • y + t • x = t • x + (1 - t) • y := fun y => add_comm _ _
          simp_rw [e]
          exact key (t • x) (1 - t) (by linarith) (fun y hy => by rw [← e]; exact hmem x hx y hy)
      _ = (2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, h z := by
          rw [setLIntegral_const]; ring

/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Poincaré inequality, smooth estimate: for a `C¹`
function `φ` on `ℝⁿ` and `0 < r ≤ 1`,
`∫_{B_r} ∫_{B_r} |φ(x) - φ(y)|² dy dx ≤ 2ⁿ⁺² |B_1| ∫_{B_r} |∇φ|²` in `[0, ∞]`.  For
`x, y ∈ B_r` we have `|x - y| < 2r ≤ 2`, so the segment bound gives
`|φ(x) - φ(y)|² ≤ 4 ∫_{[0,1]} |∇φ((1 - t) y + t x)|² dt`; integrating over `B_r × B_r`, moving the
`t`-integral outside (Tonelli) and applying the convex-combination bound
`∫_{B_r} ∫_{B_r} |∇φ((1 - t) y + t x)|² dy dx ≤ 2ⁿ |B_r| ∫_{B_r} |∇φ|²` for each `t ∈ [0, 1]`
gives the claim, since `|[0, 1]| = 1` and `|B_r| ≤ |B_1|`. -/
theorem poincare_c1_ball_double_integral_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ r : ℝ, 0 < r → r ≤ 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖φ x - φ y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖gradient φ x‖ₑ ^ 2 := by
  intro n φ hφ r hr0 hr1
  set B := ball (0 : Rn n) r with hB
  -- 1. regularity: `∇φ` is continuous, so the integrands are measurable
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hgm : Measurable (fun z => ‖gradient φ z‖ₑ ^ 2) := hgc.measurable.enorm.pow_const 2
  have hG1 : Measurable (fun p : (Rn n × Rn n) × ℝ => ‖gradient φ ((1 - p.2) • p.1.2 + p.2 • p.1.1)‖ₑ ^ 2) :=
    hgm.comp (by fun_prop : Continuous (fun p : (Rn n × Rn n) × ℝ => (1 - p.2) • p.1.2 + p.2 • p.1.1)).measurable
  have hG2 : Measurable (fun p : (Rn n × ℝ) × Rn n => ‖gradient φ ((1 - p.1.2) • p.2 + p.1.2 • p.1.1)‖ₑ ^ 2) :=
    hgm.comp (by fun_prop : Continuous (fun p : (Rn n × ℝ) × Rn n => (1 - p.1.2) • p.2 + p.1.2 • p.1.1)).measurable
  -- 2. pointwise bound on `B × B`, from the segment bound and `|x - y| ≤ 2`
  have step1 : ∀ x ∈ B, ∀ y ∈ B, ‖φ x - φ y‖ₑ ^ 2 ≤
      4 * ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
    intro x hx y hy
    refine (poincare_c1_segment_sq_bound n φ hφ x y).trans ?_
    gcongr
    have hxy : ‖x - y‖ ≤ 2 := by
      have := norm_sub_le x y
      rw [hB, mem_ball, dist_zero_right] at hx hy
      linarith
    have : ‖x - y‖ₑ ≤ 2 := by
      rw [← ofReal_norm]
      calc ENNReal.ofReal ‖x - y‖ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hxy
        _ = 2 := by simp
    calc ‖x - y‖ₑ ^ 2 ≤ 2 ^ 2 := by gcongr
      _ = 4 := by norm_num
  calc ∫⁻ x in B, ∫⁻ y in B, ‖φ x - φ y‖ₑ ^ 2
      ≤ ∫⁻ x in B, ∫⁻ y in B, 4 * ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        exact setLIntegral_mono' measurableSet_ball fun y hy => step1 x hx y hy
    -- 3. pull out the constant `4`
    _ = 4 * ∫⁻ x in B, ∫⁻ y in B, ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        rw [← lintegral_const_mul' _ _ (by norm_num)]
        congr 1; ext x
        rw [← lintegral_const_mul' _ _ (by norm_num)]
    -- 4. Tonelli: move the `t`-integral outside
    _ = 4 * ∫⁻ t in Icc (0:ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
        congr 1
        have inner : ∀ x, ∫⁻ y in B, ∫⁻ t in Icc (0:ℝ) 1, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2
            = ∫⁻ t in Icc (0:ℝ) 1, ∫⁻ y in B, ‖gradient φ ((1 - t) • y + t • x)‖ₑ ^ 2 := by
          intro x
          refine lintegral_lintegral_swap ?_
          exact (hG1.comp (measurable_const.prodMk measurable_fst |>.prodMk measurable_snd)).aemeasurable
        simp_rw [inner]
        refine lintegral_lintegral_swap ?_
        exact (hG2.lintegral_prod_right').aemeasurable
    -- 5. the convex-combination bound for each `t ∈ [0, 1]`, and `|[0, 1]| = 1`
    _ ≤ 4 * ∫⁻ t in Icc (0:ℝ) 1, (2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2 := by
        gcongr 4 * ?_
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        exact poincare_ball_convex_combination_bound n _ hgm r t hr0 ht.1 ht.2
    _ = 4 * ((2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2) := by
        rw [setLIntegral_const, Real.volume_Icc]; simp
    -- 6. `4 · 2ⁿ = 2ⁿ⁺²` and `|B_r| ≤ |B_1|`
    _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in B, ‖gradient φ x‖ₑ ^ 2 := by
        have hvol : volume B ≤ volume (ball (0 : Rn n) 1) := measure_mono (ball_subset_ball hr1)
        calc 4 * ((2 : ℝ≥0∞) ^ n * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2)
            = (2 : ℝ≥0∞) ^ (n + 2) * volume B * ∫⁻ z in B, ‖gradient φ z‖ₑ ^ 2 := by
              rw [pow_add]; ring
          _ ≤ _ := by gcongr
/-- **Double-integral Poincaré bound for `L²` limits of `C¹` functions on `B_r`** (the passage to
the limit in the Poincaré inequality on balls behind Simon Ch. 5, Lemma 3.1; cf. Gilbarg–Trudinger,
Lemma 7.16 and (7.45), Evans §5.8.1).  Let `0 < r ≤ 1`, let `f`, `g` be a.e.-strongly measurable on
`B_r = B̆_r(0)`, and let `φⱼ ∈ C¹` with `φⱼ → f` and `∇φⱼ → g` in `L²(B_r)`.  Then
`∫_{B_r} ∫_{B_r} |f(x) − f(y)|² dy dx ≤ 2^{n+2} |B̆₁(0)| ∫_{B_r} |g|²` (in `[0, ∞]`).

Pass to a subsequence `φ_{ns i} → f` a.e. on `B_r`, apply Fatou's lemma in `y` and then in `x`,
bound each `φ_{ns i}` by the `C¹` estimate `poincare_c1_ball_double_integral_bound`, and use
Minkowski `‖∇φ_{ns i}‖₂ ≤ ‖g‖₂ + ‖∇φ_{ns i} − g‖₂`, whose last term tends to `0`. -/
theorem poincare_approx_ball_double_integral_bound : ∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n) (φ : ℕ → Rn n → ℝ) (r : ℝ), 0 < r → r ≤ 1 → AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) → AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) r)) → (∀ j, ContDiff ℝ 1 (φ j)) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) * ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2 := by
  intro n f g φ r hr0 hr1 hf hg hφ h1 h2
  set B := ball (0 : Rn n) r with hB
  set μ : Measure (Rn n) := volume.restrict B with hμ
  set C : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) with hC
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne
  -- `L²` bookkeeping: `eLpNorm u 2 μ = (∫⁻ ‖u‖ₑ ^ 2 dμ) ^ (1/2)` for a.e.-strongly measurable `u`.
  have eL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    intro E _ u hu
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hu]
    simp
  have eL2sq : ∀ {E : Type} [NormedAddCommGroup E] {u : Rn n → E}, AEStronglyMeasurable u μ →
      eLpNorm u 2 μ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ := by
    intro E _ u hu
    rw [eL2 hu, ← ENNReal.rpow_mul_natCast]
    norm_num
  have tL2 : ∀ {E : Type} [NormedAddCommGroup E] {u : ℕ → Rn n → E},
      (∀ j, AEStronglyMeasurable (u j) μ) → Tendsto (fun j => ∫⁻ x, ‖u j x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) →
      Tendsto (fun j => eLpNorm (u j) 2 μ) atTop (𝓝 0) := by
    intro E _ u hu h
    simp_rw [eL2 (hu _)]
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  -- Step 0: replace `f` by a strongly measurable representative `f'`; nothing changes.
  have hff' := hf.ae_eq_mk
  have hfm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set f' := hf.mk f
  have hdbl : ∫⁻ x in B, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 =
      ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 := by
    have hin : ∀ x, ∫⁻ y in B, ‖f x - f y‖ₑ ^ 2 = ∫⁻ y in B, ‖f x - f' y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (hff'.mono fun y hy => by simp [hy])
    simp_rw [hin]
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp [hx])
  rw [hdbl]
  have h1' : Tendsto (fun j => ∫⁻ x in B, ‖φ j x - f' x‖ₑ ^ 2) atTop (𝓝 0) := by
    refine h1.congr fun j => ?_
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp only [hx])
  -- Step 1: `φⱼ` and `∇φⱼ = (toDual)⁻¹ ∘ Dφⱼ` are continuous.
  have hφc : ∀ j, Continuous (φ j) := fun j => (hφ j).continuous
  have hgc : ∀ j, Continuous (gradient (φ j)) := fun j =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp ((hφ j).continuous_fderiv one_ne_zero)
  -- Step 2: `φⱼ → f'` in `L²(μ)`, hence in measure, so a subsequence converges `μ`-a.e.
  have hconv : Tendsto (fun j => eLpNorm (φ j - f') 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hφc j).aestronglyMeasurable.sub hfm.aestronglyMeasurable) h1'
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hconv).exists_seq_tendsto_ae
  -- Steps 3–4: Fatou's lemma, first in `y` (for `μ`-a.e. `x`) and then in `x`.
  have hsqc : Continuous (fun p : ℝ × ℝ => ‖p.1 - p.2‖ₑ ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp (continuous_fst.sub continuous_snd))
  have hFatou : ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
      liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
    have hpt : ∀ᵐ x ∂μ, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2 ≤
        liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
      filter_upwards [hae] with x hx
      calc ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
          = ∫⁻ y in B, liminf (fun i => ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae] with y hy
            exact (((hsqc.tendsto _).comp (hx.prodMk_nhds hy)).liminf_eq).symm
        _ ≤ liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
            lintegral_liminf_le fun i =>
              ((measurable_const.sub (hφc _).measurable).enorm.pow_const 2)
    calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
        ≤ ∫⁻ x in B, liminf (fun i => ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_mono_ae hpt
      _ ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop :=
          lintegral_liminf_le fun i =>
            ((((hφc _).measurable.comp measurable_fst).sub
              ((hφc _).measurable.comp measurable_snd)).enorm.pow_const 2).lintegral_prod_right'
  -- Step 5: the `C¹` estimate for `φ_{ns i}` and Minkowski's inequality in `L²(μ)`.
  have hbound : ∀ i, ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2 ≤
      C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2 := by
    intro i
    refine (Submission.poincare_c1_ball_double_integral_bound n (φ (ns i)) (hφ _) r hr0
      hr1).trans ?_
    gcongr
    rw [← eL2sq (hgc _).aestronglyMeasurable]
    gcongr
    calc eLpNorm (gradient (φ (ns i))) 2 μ
        = eLpNorm (g + (gradient (φ (ns i)) - g)) 2 μ := by rw [add_sub_cancel]
      _ ≤ _ := eLpNorm_add_le one_le_two
  -- Step 6: `‖∇φ_{ns i} − g‖₂ → 0`, so the bounds tend to `C ‖g‖₂²` (`C < ∞`).
  have hε : Tendsto (fun j => eLpNorm (gradient (φ j) - g) 2 μ) atTop (𝓝 0) :=
    tL2 (fun j => (hgc j).aestronglyMeasurable.sub hg) h2
  have hlim : Tendsto (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2)
      atTop (𝓝 (C * (eLpNorm g 2 μ + 0) ^ 2)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hCtop)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp
      (tendsto_const_nhds.add (hε.comp hns.tendsto_atTop))
  -- Step 7: conclusion.
  calc ∫⁻ x in B, ∫⁻ y in B, ‖f' x - f' y‖ₑ ^ 2
      ≤ liminf (fun i => ∫⁻ x in B, ∫⁻ y in B, ‖φ (ns i) x - φ (ns i) y‖ₑ ^ 2) atTop := hFatou
    _ ≤ liminf (fun i => C * (eLpNorm g 2 μ + eLpNorm (gradient (φ (ns i)) - g) 2 μ) ^ 2) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = C * (eLpNorm g 2 μ + 0) ^ 2 := hlim.liminf_eq
    _ = C * ∫⁻ x in B, ‖g x‖ₑ ^ 2 := by rw [add_zero, eL2sq hg]
/-- **Exhaustion of the unit ball for the double integral** (step `r → 1` of the `W^{1,2}`
Poincaré inequality on `B̆₁(0)`; Gilbarg–Trudinger, Lemma 7.16).  If `f` is a.e.-strongly
measurable on `B̆₁(0)` and `∫_{B̆_r}∫_{B̆_r} |f(x) - f(y)|² dy dx ≤ K` for every `r ∈ (0,1)`, then
the same bound holds on `B̆₁(0)`.  The balls `B̆_{r_m}`, `r_m = 1 - 1/(m+2)`, increase to `B̆₁(0)`;
for a strongly measurable representative of `f` the union formula for directed unions and
monotone convergence reduce the double integral over `B̆₁(0)` to the diagonal radii. -/
theorem poincare_ball_double_integral_exhaustion : ∀ (n : ℕ) (f : Rn n → ℝ) (K : ℝ≥0∞), AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) 1)) → (∀ r : ℝ, 0 < r → r < 1 → ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤ K) → ∫⁻ x in ball (0 : Rn n) 1, ∫⁻ y in ball (0 : Rn n) 1, ‖f x - f y‖ₑ ^ 2 ≤ K := by
  intro n f K hf hK
  -- double integrals over `s` only depend on the a.e.-class of `f` on `s`
  have dbl : ∀ {s : Set (Rn n)} {f₁ f₂ : Rn n → ℝ}, f₁ =ᵐ[volume.restrict s] f₂ →
      ∫⁻ x in s, ∫⁻ y in s, ‖f₁ x - f₁ y‖ₑ ^ 2 = ∫⁻ x in s, ∫⁻ y in s, ‖f₂ x - f₂ y‖ₑ ^ 2 := by
    intro s f₁ f₂ h
    have h1 : ∀ x, ∫⁻ y in s, ‖f₁ x - f₁ y‖ₑ ^ 2 = ∫⁻ y in s, ‖f₁ x - f₂ y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (h.mono fun y hy => by simp [hy])
    simp_rw [h1]
    exact lintegral_congr_ae (h.mono fun x hx => by simp [hx])
  have hff' := hf.ae_eq_mk
  have hm : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set f' := hf.mk f
  -- radii `r m = 1 - 1/(m+2)` increase to `1`
  let r : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2)
  have hr0 : ∀ m, 0 < r m := fun m => by
    have : (1 : ℝ) / ((m : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    simp only [r]; linarith
  have hr1 : ∀ m, r m < 1 := fun m => by
    have : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
    simp only [r]; linarith
  have hrmono : Monotone r := by
    intro a b hab
    simp only [r]
    have hab' : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hab 2
    have : (1 : ℝ) / ((b : ℝ) + 2) ≤ 1 / ((a : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) hab'
    linarith
  set B : ℕ → Set (Rn n) := fun m => ball 0 (r m) with hBdef
  have hBmono : Monotone B := fun a b hab => ball_subset_ball (hrmono hab)
  have hBdir : Directed (· ⊆ ·) B := hBmono.directed_le
  have hU : ⋃ m, B m = ball (0 : Rn n) 1 := by
    ext x
    simp only [mem_iUnion, mem_ball, dist_zero_right, B]
    constructor
    · rintro ⟨m, hm⟩; exact hm.trans (hr1 m)
    · intro hx
      have h1 : 0 < 1 - ‖x‖ := by linarith
      obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - ‖x‖))
      refine ⟨m, ?_⟩
      simp only [r]
      have : 1 / ((m : ℝ) + 2) < 1 - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ h1] at hm
        nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      linarith
  -- the hypothesis transfers to the representative `f'`
  have hK' : ∀ m, ∫⁻ x in B m, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2 ≤ K := fun m => by
    rw [← dbl (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (hr1 m).le) hff')]
    exact hK _ (hr0 m) (hr1 m)
  rw [dbl hff', ← hU]
  have hF : Measurable (fun p : Rn n × Rn n => ‖f' p.1 - f' p.2‖ₑ ^ 2) :=
    ((hm.measurable.comp measurable_fst).sub (hm.measurable.comp measurable_snd)).enorm.pow_const 2
  -- inner integrals: union formula along the directed family `B`
  have hG : ∀ x, ∫⁻ y in ⋃ m, B m, ‖f' x - f' y‖ₑ ^ 2 = ⨆ m, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2 :=
    fun x => setLIntegral_iUnion_of_directed _ hBdir
  simp_rw [hG]
  -- outer integral: union formula, then monotone convergence
  rw [setLIntegral_iUnion_of_directed _ hBdir]
  refine iSup_le fun k => ?_
  rw [lintegral_iSup (fun m => hF.lintegral_prod_right')
    (fun a b hab x => lintegral_mono_set (hBmono hab))]
  refine iSup_le fun m => ?_
  -- diagonal comparison at the radius `r (max k m)`
  calc ∫⁻ x in B k, ∫⁻ y in B m, ‖f' x - f' y‖ₑ ^ 2
      ≤ ∫⁻ x in B (max k m), ∫⁻ y in B (max k m), ‖f' x - f' y‖ₑ ^ 2 := by
        refine (lintegral_mono_set (hBmono (le_max_left k m))).trans ?_
        exact lintegral_mono fun x => lintegral_mono_set (hBmono (le_max_right k m))
    _ ≤ K := hK' _
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Poincaré inequality, mean-deviation step: for a
measurable `s ⊆ ℝⁿ` of finite measure and `f ∈ L²(s)`,
`∫_s |f - ⨍_s f|² ≤ |s|⁻¹ ∫_s ∫_s |f(x) - f(y)|² dy dx` in `[0, ∞]`.  If `|s| = 0` the left side
vanishes.  Otherwise `f(x) - ⨍_s f = |s|⁻¹ ∫_s (f(x) - f(y)) dy`, and Cauchy–Schwarz on `s`
(`L¹ ≤ L²` for the finite measure `volume.restrict s`) gives
`|f(x) - ⨍_s f|² ≤ |s|⁻¹ ∫_s |f(x) - f(y)|² dy` for every `x`; integrate over `x ∈ s`. -/
theorem poincare_set_mean_deviation_sq_bound : ∀ (n : ℕ) (s : Set (Rn n)) (f : Rn n → ℝ), MeasurableSet s → volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫⁻ x in s, ‖f x - ⨍ y in s, f y‖ₑ ^ 2 ≤ (volume s)⁻¹ * ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 := by
  intro n s f hs hfin hf
  -- 1. null set: the left side vanishes
  by_cases h0 : volume s = 0
  · have : volume.restrict s = 0 := Measure.restrict_eq_zero.mpr h0
    simp [this]
  -- 2. pass to a strongly measurable representative (no side changes)
  have hfa := hf.aestronglyMeasurable
  have hff' : f =ᵐ[volume.restrict s] hfa.mk f := hfa.ae_eq_mk
  have hf'L2 : MemLp (hfa.mk f) 2 (volume.restrict s) := (memLp_congr_ae hff').mp hf
  have hdbl : ∫⁻ x in s, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 =
      ∫⁻ x in s, ∫⁻ y in s, ‖hfa.mk f x - hfa.mk f y‖ₑ ^ 2 := by
    have h1 : ∀ x, ∫⁻ y in s, ‖f x - f y‖ₑ ^ 2 = ∫⁻ y in s, ‖f x - hfa.mk f y‖ₑ ^ 2 := fun x =>
      lintegral_congr_ae (hff'.mono fun y hy => by simp [hy])
    simp_rw [h1]
    exact lintegral_congr_ae (hff'.mono fun x hx => by simp [hx])
  rw [hdbl]
  have havg : ⨍ y in s, f y = ⨍ y in s, hfa.mk f y := by
    rw [setAverage_eq, setAverage_eq, integral_congr_ae hff']
  rw [havg]
  set f' := hfa.mk f
  set c := ⨍ y in s, f' y with hc
  rw [lintegral_congr_ae (g := fun x => ‖f' x - c‖ₑ ^ 2) (hff'.mono fun x hx => by simp only [hx])]
  have : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0)]
  apply lintegral_mono
  intro x
  -- 3. f(x) - λ = |s|⁻¹ ∫_s (f(x) - f(y)) dy
  have hint : Integrable f' (volume.restrict s) := hf'L2.integrable one_le_two
  have hkey : f' x - c = (volume.real s)⁻¹ * ∫ y in s, (f' x - f' y) := by
    have hu : (volume.restrict s).real univ = volume.real s := by simp [Measure.real]
    have hreal : volume.real s ≠ 0 := by
      simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, hfin]
    rw [integral_sub (integrable_const _) hint, integral_const, hu, hc, setAverage_eq]
    simp only [smul_eq_mul]
    field_simp
  -- 4. Cauchy–Schwarz on s: (∫_s |u|)^2 ≤ |s| ∫_s |u|^2
  have hCS : (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 ≤ volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
    have hh : AEStronglyMeasurable (fun y => f' x - f' y) (volume.restrict s) :=
      aestronglyMeasurable_const.sub hint.aestronglyMeasurable
    have key := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (μ := volume.restrict s) one_le_two hh
    rw [eLpNorm_one_eq_lintegral_enorm hh,
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hh] at key
    have e1 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
    rw [e1, Measure.restrict_apply_univ] at key
    have e2 : ∀ y, ‖f' x - f' y‖ₑ ^ (2 : ℝ≥0∞).toReal = ‖f' x - f' y‖ₑ ^ 2 := fun y => by simp
    simp_rw [e2] at key
    calc (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2
        ≤ ((∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2) ^ (1 / (2 : ℝ≥0∞).toReal) *
            volume s ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast]
        norm_num
        rw [mul_comm]
  -- 5. pointwise bound and conclusion
  have hnorm : ‖f' x - c‖ₑ ≤ (volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ := by
    rw [hkey, enorm_mul]
    gcongr
    · rw [Measure.real, Real.enorm_eq_ofReal (inv_nonneg.mpr ENNReal.toReal_nonneg),
        ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 hfin), ENNReal.ofReal_toReal hfin]
    · exact enorm_integral_le_lintegral_enorm _
  calc ‖f' x - c‖ₑ ^ 2 ≤ ((volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 := by gcongr
    _ = (volume s)⁻¹ ^ 2 * (∫⁻ y in s, ‖f' x - f' y‖ₑ) ^ 2 := by rw [mul_pow]
    _ ≤ (volume s)⁻¹ ^ 2 * (volume s * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2) := by gcongr
    _ = (volume s)⁻¹ * ∫⁻ y in s, ‖f' x - f' y‖ₑ ^ 2 := by
      rw [pow_two, ← mul_assoc, mul_assoc _ _ (volume s), ENNReal.inv_mul_cancel h0 hfin, mul_one]
/-- **`L²` contraction of mollification** (Young's inequality with exponents `(1, 2; 2)`;
Gilbarg–Trudinger §7.2, Evans Appendix C).  Convolution with a continuous probability kernel
`ρ ≥ 0`, `∫ ρ = 1`, does not increase the `L²` energy: `∫⁻ ‖ρ ⋆ H‖ₑ² ≤ ∫⁻ ‖H‖ₑ²`.

With the weight `a = ofReal ∘ ρ` (mass one), `‖∫ ρ(z) H(x - z) dz‖ₑ ≤ ∫⁻ a(z) ‖H(x - z)‖ₑ dz`, and
Hölder's inequality for `a^{1/2}` and `a^{1/2} ‖H(x - ·)‖ₑ` bounds the square of the right side by
`∫⁻ a(z) ‖H(x - z)‖ₑ² dz`.  Integrating in `x`, Tonelli and the translation invariance of Lebesgue
measure turn the double integral into `(∫⁻ a) ∫⁻ ‖H‖ₑ² = ∫⁻ ‖H‖ₑ²`. -/
theorem mollifier_l2_contraction : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (ρ : Rn n → ℝ) (H : Rn n → E), Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → AEStronglyMeasurable H volume → ∫⁻ x, ‖∫ z, ρ z • H (x - z)‖ₑ ^ 2 ≤ ∫⁻ x, ‖H x‖ₑ ^ 2 := by
  intro n E _ _ _ ρ H hρc hρ0 hρ1 hH
  -- Step 1: `ρ` is integrable, so the weight `a = ofReal ∘ ρ` has mass one.
  have hρi : Integrable ρ := integrable_of_integral_eq_one hρ1
  have hmass : ∫⁻ z, ENNReal.ofReal (ρ z) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1,
      ENNReal.ofReal_one]
  -- Step 2: measurability of the weight and of `‖H‖ₑ`.
  have ha : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) volume :=
    (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
  have hh : AEMeasurable (fun y => ‖H y‖ₑ) volume := hH.enorm
  -- Steps 3–5: `‖∫ ρ(z) H(x - z) dz‖ₑ² ≤ ∫⁻ a(z) ‖H(x - z)‖ₑ² dz` for every `x`.
  have hpt : ∀ x, ‖∫ z, ρ z • H (x - z)‖ₑ ^ 2 ≤
      ∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2 := by
    intro x
    have h1 : ‖∫ z, ρ z • H (x - z)‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      congr 1; funext z
      rw [enorm_smul, Real.enorm_of_nonneg (hρ0 z)]
    have hg : AEMeasurable (fun z => ‖H (x - z)‖ₑ) volume :=
      hh.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
    -- Hölder with `p = q = 2` for `a^{1/2}` and `a^{1/2} ‖H(x - ·)‖ₑ`, then `∫⁻ a = 1`.
    have key := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      (f := fun z => ENNReal.ofReal (ρ z) ^ (1 / 2 : ℝ))
      (g := fun z => ENNReal.ofReal (ρ z) ^ (1 / 2 : ℝ) * ‖H (x - z)‖ₑ)
      (ha.pow_const _) ((ha.pow_const _).mul hg)
    have e1 : ∀ t s : ℝ≥0∞, t ^ (1 / 2 : ℝ) * (t ^ (1 / 2 : ℝ) * s) = t * s := by
      intro t s
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have e2 : ∀ t : ℝ≥0∞, (t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = t := by
      intro t
      rw [← ENNReal.rpow_mul]; norm_num
    have e3 : ∀ t s : ℝ≥0∞, (t ^ (1 / 2 : ℝ) * s) ^ (2 : ℝ) = t * s ^ 2 := by
      intro t s
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
    simp only [Pi.mul_apply, e1, e2, e3, hmass, ENNReal.one_rpow, one_mul] at key
    calc ‖∫ z, ρ z • H (x - z)‖ₑ ^ 2 ≤ (∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ) ^ 2 := by
          gcongr
      _ ≤ ((∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2 := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  -- Step 7: Tonelli and translation invariance of Lebesgue measure.
  have hprod : AEMeasurable
      (Function.uncurry fun x z => ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2)
      ((volume : Measure (Rn n)).prod volume) := by
    have h1 : AEMeasurable (fun p : Rn n × Rn n => ENNReal.ofReal (ρ p.2))
        ((volume : Measure (Rn n)).prod volume) := ha.comp_snd
    have h2 : AEMeasurable (fun p : Rn n × Rn n => ‖H (p.1 - p.2)‖ₑ ^ 2)
        ((volume : Measure (Rn n)).prod volume) :=
      (hh.pow_const 2).comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
    exact h1.mul h2
  have hz : ∀ z, ∫⁻ x, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2 =
      ENNReal.ofReal (ρ z) * ∫⁻ y, ‖H y‖ₑ ^ 2 := fun z => by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (fun y => ‖H y‖ₑ ^ 2) z]
  -- Steps 6 and 8: integrate the pointwise bound and use `∫⁻ a = 1`.
  calc ∫⁻ x, ‖∫ z, ρ z • H (x - z)‖ₑ ^ 2
      ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2 := lintegral_mono hpt
    _ = ∫⁻ z, ∫⁻ x, ENNReal.ofReal (ρ z) * ‖H (x - z)‖ₑ ^ 2 := lintegral_lintegral_swap hprod
    _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ∫⁻ y, ‖H y‖ₑ ^ 2 := lintegral_congr hz
    _ = ∫⁻ y, ‖H y‖ₑ ^ 2 := by rw [lintegral_mul_const'' _ ha, hmass, one_mul]

/-- **Mollifiers are an approximate identity in `L²`** (Gilbarg–Trudinger §7.2, Evans Appendix C).
If `ρ j ≥ 0` are continuous with `∫ ρ j = 1` and `ρ j = 0` outside `ball 0 (ε j)` with `ε j → 0`,
then `∫⁻ ‖ρ j ⋆ H - H‖ₑ² → 0` for every `H ∈ L¹ ∩ L²`.

For continuous compactly supported `Φ`, uniform continuity bounds `‖ρ j ⋆ Φ - Φ‖` uniformly and
the difference vanishes off a fixed ball, so `∫⁻ ‖ρ j ⋆ Φ - Φ‖ₑ² → 0`.  Such `Φ` are dense in `L²`
(simple functions, inner/outer regularity of Lebesgue measure and Urysohn's lemma), and splitting
`ρ j ⋆ H - H = ρ j ⋆ (H - Φ) + (ρ j ⋆ Φ - Φ) + (Φ - H)`, the first term is controlled by the
`L²` contraction `mollifier_l2_contraction`. -/
theorem mollifier_l2_tendsto : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (H : Rn n → E), Integrable H → MemLp H 2 volume → ∀ (ρ : ℕ → Rn n → ℝ) (ε : ℕ → ℝ), (∀ j, Continuous (ρ j)) → (∀ j z, 0 ≤ ρ j z) → (∀ j, ∫ z, ρ j z = 1) → (∀ j z, ε j ≤ ‖z‖ → ρ j z = 0) → Tendsto ε atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖(∫ z, ρ j z • H (x - z)) - H x‖ₑ ^ 2) atTop (𝓝 0) := by
  intro n E _ _ _ H hHi hH2 ρ ε hρc hρ0 hρ1 hρs hε
  -- Step 1: `ρ j` vanishes off `ball 0 (ε j)`, so it is continuous with compact support and the
  -- mollification `x ↦ ∫ ρ j z • u (x - z)` of a locally integrable `u` is continuous.
  have hρsupp : ∀ j r, ε j ≤ r → Function.support (ρ j) ⊆ ball (0 : Rn n) r := by
    intro j r hr z hz
    rw [mem_ball_zero_iff]
    by_contra h
    exact hz (hρs j z (hr.trans (not_lt.1 h)))
  have hρcs : ∀ j, HasCompactSupport (ρ j) := fun j =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (ε j)) fun z hz =>
      hρs j z (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)
  have hMc : ∀ j (u : Rn n → E), LocallyIntegrable u volume →
      Continuous (fun x => ∫ z, ρ j z • u (x - z)) := fun j u hu =>
    (hρcs j).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρc j) hu
  -- Step 2: `(a + b)² ≤ 2 (a² + b²)` in `ℝ≥0∞`.
  have sq2 : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    intro a b
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) one_le_two
    norm_num [ENNReal.rpow_two] at h
    exact h
  -- Step 3: for continuous compactly supported `Φ`, `∫⁻ ‖ρ j ⋆ Φ - Φ‖ₑ² → 0`.
  have hCc : ∀ Φ : Rn n → E, Continuous Φ → HasCompactSupport Φ → ∀ δ : ℝ≥0∞, δ ≠ 0 →
      ∀ᶠ j in atTop, ∫⁻ x, ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 ≤ δ := by
    intro Φ hΦc hΦcs δ hδ
    obtain ⟨R, hR⟩ := hΦcs.isCompact.isBounded.subset_closedBall (0 : Rn n)
    have hΦ0 : ∀ y : Rn n, R < ‖y‖ → Φ y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => not_le.2 hy (mem_closedBall_zero_iff.1 (hR h))
    obtain ⟨θ, θpos, hθ⟩ := ENNReal.exists_nnreal_pos_mul_lt
      (measure_closedBall_lt_top (μ := (volume : Measure (Rn n))) (x := 0) (r := R + 1)).ne hδ
    set η : ℝ := Real.sqrt θ with hη
    have ηpos : 0 < η := Real.sqrt_pos.2 (by exact_mod_cast θpos)
    obtain ⟨r, rpos, hr⟩ :=
      Metric.uniformContinuous_iff.1 (hΦcs.uniformContinuous_of_continuous hΦc) η ηpos
    filter_upwards [hε.eventually_lt_const (lt_min rpos one_pos)] with j hj
    have hpt : ∀ x, ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 ≤
        (closedBall (0 : Rn n) (R + 1)).indicator (fun _ => (θ : ℝ≥0∞)) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : Rn n) (R + 1)
      · rw [indicator_of_mem hx]
        have h1 := dist_convolution_le (μ := volume) (f := ρ j) (g := Φ) (x₀ := x) (z₀ := Φ x)
          ηpos.le (hρsupp j r (hj.le.trans (min_le_left _ _))) (hρ0 j) (hρ1 j)
          hΦc.aestronglyMeasurable fun y hy => (hr (mem_ball.1 hy)).le
        rw [convolution_lsmul, dist_eq_norm] at h1
        calc ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 ≤ ENNReal.ofReal η ^ 2 := by
              gcongr
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal h1
          _ = (θ : ℝ≥0∞) := by
              rw [← ENNReal.ofReal_pow ηpos.le, hη, Real.sq_sqrt θ.coe_nonneg,
                ENNReal.ofReal_coe_nnreal]
      · rw [indicator_of_notMem hx]
        rw [mem_closedBall_zero_iff, not_le] at hx
        have h1 := dist_convolution_le (μ := volume) (f := ρ j) (g := Φ) (x₀ := x) (z₀ := 0)
          le_rfl (hρsupp j 1 (hj.le.trans (min_le_right _ _))) (hρ0 j) (hρ1 j)
          hΦc.aestronglyMeasurable fun y hy => by
            have h2 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
            rw [← dist_eq_norm, dist_comm] at h2
            rw [hΦ0 y (by linarith [mem_ball.1 hy]), dist_self]
        rw [convolution_lsmul, dist_le_zero] at h1
        rw [h1, hΦ0 x (by linarith), sub_zero, enorm_zero]
        simp
    calc ∫⁻ x, ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2
        ≤ ∫⁻ x, (closedBall (0 : Rn n) (R + 1)).indicator (fun _ => (θ : ℝ≥0∞)) x :=
          lintegral_mono hpt
      _ = θ * volume (closedBall (0 : Rn n) (R + 1)) :=
          lintegral_indicator_const measurableSet_closedBall _
      _ ≤ δ := hθ.le
  -- Step 4: continuous compactly supported functions are dense in `L²`.
  have hdense : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ Φ : Rn n → E,
      eLpNorm (H - Φ) 2 volume ≤ δ ∧ (Continuous Φ ∧ HasCompactSupport Φ) := by
    intro δ hδ
    refine hH2.induction_dense (by norm_num) (fun g => Continuous g ∧ HasCompactSupport g)
      ?_ ?_ hδ
    · intro c S hS hSμ η hη
      obtain ⟨θ, θpos, hθ⟩ := exists_eLpNorm_indicator_le (μ := (volume : Measure (Rn n)))
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) c hη
      have hθ2 : (θ : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.div_pos (by exact_mod_cast θpos.ne')
        (by norm_num)).ne'
      obtain ⟨K, hKS, hKc, hSK⟩ := hS.exists_isCompact_sdiff_lt hSμ.ne hθ2
      obtain ⟨U, hSU, hUo, -, hUS⟩ := hS.exists_isOpen_sdiff_lt hSμ.ne hθ2
      obtain ⟨f, hf1, hf0, hfcs, hf01⟩ := exists_continuous_one_zero_of_isCompact hKc
        hUo.isClosed_compl (disjoint_compl_right_iff_subset.2 (hKS.trans hSU))
      have hfc : Continuous fun x => f x • c := f.continuous.smul continuous_const
      refine ⟨fun x => f x • c, ?_, hfc, hfcs.smul_right (f' := fun _ => c)⟩
      have hmeas : AEStronglyMeasurable ((fun x => f x • c) - S.indicator fun _ => c) volume :=
        hfc.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hS)
      refine (eLpNorm_mono hmeas (g := (U \ K).indicator fun _ => c) fun x => ?_).trans
        (hθ _ ?_ (hUo.measurableSet.diff hKc.measurableSet).nullMeasurableSet)
      · have hf01' : ‖f x‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 x).1, (hf01 x).2]
        have hf01'' : ‖f x - 1‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hf01 x).1, (hf01 x).2]
        rw [Pi.sub_apply]
        by_cases hxK : x ∈ K
        · rw [hf1 hxK, indicator_of_mem (hKS hxK)]
          simp
        by_cases hxU : x ∈ U
        · rw [indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
          by_cases hxS : x ∈ S
          · have h3 : f x • c - c = (f x - 1) • c := by rw [sub_smul, one_smul]
            rw [indicator_of_mem hxS, h3, norm_smul]
            exact mul_le_of_le_one_left (norm_nonneg _) hf01''
          · rw [indicator_of_notMem hxS, sub_zero, norm_smul]
            exact mul_le_of_le_one_left (norm_nonneg _) hf01'
        · rw [hf0 hxU, indicator_of_notMem fun h => hxU (hSU h)]
          simp
      · calc volume (U \ K) ≤ volume ((U \ S) ∪ (S \ K)) := by
              refine measure_mono fun x hx => ?_
              by_cases hxS : x ∈ S
              · exact Or.inr ⟨hxS, hx.2⟩
              · exact Or.inl ⟨hx.1, hxS⟩
          _ ≤ volume (U \ S) + volume (S \ K) := measure_union_le _ _
          _ ≤ θ / 2 + θ / 2 := add_le_add hUS.le hSK.le
          _ = θ := ENNReal.add_halves _
    · rintro f g ⟨hfc, hfcs⟩ ⟨hgc, hgcs⟩
      exact ⟨hfc.add hgc, hfcs.add hgcs⟩
  -- Step 5: split `ρ j ⋆ H - H` and conclude.
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set δ := e / 10
  have hδ : δ ≠ 0 := (ENNReal.div_pos he.ne' (by norm_num)).ne'
  obtain ⟨Φ, hHΦ, hΦc, hΦcs⟩ := hdense (min δ 1) (lt_min (pos_iff_ne_zero.2 hδ) one_pos).ne'
  have hΦi : Integrable Φ volume := hΦc.integrable_of_hasCompactSupport hΦcs
  have hHΦi : Integrable (H - Φ) volume := hHi.sub hΦi
  have hC : ∫⁻ x, ‖(H - Φ) x‖ₑ ^ 2 ≤ δ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hHΦi.aestronglyMeasurable] at hHΦ
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hHΦ
    calc ∫⁻ x, ‖(H - Φ) x‖ₑ ^ 2 = ((∫⁻ x, ‖(H - Φ) x‖ₑ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (min δ 1) ^ 2 := by gcongr
      _ ≤ min δ 1 := pow_le_of_le_one (by positivity) (min_le_right _ _) two_ne_zero
      _ ≤ δ := min_le_left _ _
  filter_upwards [hCc Φ hΦc hΦcs δ hδ] with j hj
  have hA := mollifier_l2_contraction n E (ρ j) (H - Φ) (hρc j) (hρ0 j) (hρ1 j)
    hHΦi.aestronglyMeasurable
  have hlin : ∀ x, (∫ z, ρ j z • H (x - z)) =
      (∫ z, ρ j z • (H - Φ) (x - z)) + ∫ z, ρ j z • Φ (x - z) := by
    intro x
    have h := ((hρcs j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρc j)
      hHΦi.locallyIntegrable x).distrib_add
      ((hρcs j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρc j)
        hΦi.locallyIntegrable x)
    rw [sub_add_cancel] at h
    simpa only [convolution_lsmul] using h
  have hpt : ∀ x, ‖(∫ z, ρ j z • H (x - z)) - H x‖ₑ ^ 2 ≤
      2 * ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
        4 * ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 + 4 * ‖(H - Φ) x‖ₑ ^ 2 := by
    intro x
    have heq : (∫ z, ρ j z • H (x - z)) - H x = (∫ z, ρ j z • (H - Φ) (x - z)) +
        (((∫ z, ρ j z • Φ (x - z)) - Φ x) + -(H - Φ) x) := by
      rw [hlin x, Pi.sub_apply]; abel
    rw [heq]
    calc ‖(∫ z, ρ j z • (H - Φ) (x - z)) +
          (((∫ z, ρ j z • Φ (x - z)) - Φ x) + -(H - Φ) x)‖ₑ ^ 2
        ≤ (‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ +
          (‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ + ‖(H - Φ) x‖ₑ)) ^ 2 := by
          gcongr
          refine (enorm_add_le _ _).trans ?_
          gcongr
          exact (enorm_add_le _ _).trans_eq (by rw [enorm_neg])
      _ ≤ 2 * (‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
          (‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ + ‖(H - Φ) x‖ₑ) ^ 2) := sq2 _ _
      _ ≤ 2 * (‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
          2 * (‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 + ‖(H - Φ) x‖ₑ ^ 2)) := by
          gcongr; exact sq2 _ _
      _ = 2 * ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
          4 * ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 + 4 * ‖(H - Φ) x‖ₑ ^ 2 := by ring
  have hmA : AEMeasurable (fun x => 2 * ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2) volume :=
    (((hMc j _ hHΦi.locallyIntegrable).enorm.measurable.pow_const 2).const_mul 2).aemeasurable
  have hmB : AEMeasurable (fun x => 4 * ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2) volume :=
    ((((hMc j _ hΦi.locallyIntegrable).sub hΦc).enorm.measurable.pow_const 2).const_mul
      4).aemeasurable
  calc ∫⁻ x, ‖(∫ z, ρ j z • H (x - z)) - H x‖ₑ ^ 2
      ≤ ∫⁻ x, (2 * ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
        4 * ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2 + 4 * ‖(H - Φ) x‖ₑ ^ 2) := lintegral_mono hpt
    _ = 2 * (∫⁻ x, ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2) +
        4 * (∫⁻ x, ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2) + 4 * ∫⁻ x, ‖(H - Φ) x‖ₑ ^ 2 := by
      have hmAB : AEMeasurable (fun x => 2 * ‖∫ z, ρ j z • (H - Φ) (x - z)‖ₑ ^ 2 +
          4 * ‖(∫ z, ρ j z • Φ (x - z)) - Φ x‖ₑ ^ 2) volume := hmA.add hmB
      rw [lintegral_add_left' hmAB, lintegral_add_left' hmA,
        lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * δ + 4 * δ + 4 * δ := by gcongr; exact hA.trans hC
    _ = 10 * δ := by ring
    _ = e := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
/-- **Mollified `W^{1,2}` functions on the unit ball** (Evans, *PDE*, §5.3.1; Gilbarg–Trudinger,
§7.3).  Let `f ∈ W^{1,2}(B)` with weak gradient `g`, `B = B̆₁(0)`, and let `ρ` be `C^∞` with
`ρ(z) = 0` for `‖z‖ ≥ ε`.  For the zero extensions `F = 1_B f`, `G = 1_B g`, the mollification
`Φ(x) = ∫ ρ(z) F(x - z) dz` is `C^∞`, and `∇Φ(x) = ∫ ρ(z) G(x - z) dz` whenever `‖x‖ < 1 - ε`.

`ρ` is supported in `B_ε(0)` and `F` is integrable (`L²` on a ball of finite measure), so
`Φ = F ⋆ ρ` is smooth with `DΦ(x) v = ∫ F(t) Dρ(x - t) v dt`, i.e. `∇Φ(x) = ∫ F(t) ∇ρ(x - t) dt`.
For `‖x‖ < 1 - ε` the reflected kernel `ζ(y) = ρ(x - y)` is a test function in `B` with
`∇ζ(y) = -∇ρ(x - y)`, so the weak identity gives `∫_B f(y) ∇ρ(x - y) dy = ∫_B ρ(x - y) g(y) dy`,
which is `∫ ρ(z) G(x - z) dz` after the substitution `z = x - y`. -/
theorem w12_ball_mollification_gradient : ∀ (n : ℕ) (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ (ρ : Rn n → ℝ) (ε : ℝ), ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, ε ≤ ‖z‖ → ρ z = 0) → ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) ∧ ∀ x : Rn n, ‖x‖ < 1 - ε → gradient (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) x = ∫ z, ρ z • (ball (0 : Rn n) 1).indicator g (x - z) := by
  intro n f g hW ρ ε hρ hρ0
  obtain ⟨hf2, hg2, hweak⟩ := hW
  -- Step 1: `tsupport ρ ⊆ B_ε(0)`, so `ρ` is a compactly supported `C^∞` (in particular `C¹`)
  -- kernel.
  have hts : tsupport ρ ⊆ closedBall 0 ε := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact (Function.mem_support.1 hz) (hρ0 z (not_le.1 h).le)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Rn n) ε)
      (subset_closure.trans hts)
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  -- Step 2: `F = 1_B f` is integrable, since `f ∈ L²(B)` and `B` has finite measure.
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hFi : Integrable ((ball (0 : Rn n) 1).indicator f) volume :=
    (integrable_indicator_iff measurableSet_ball).2 (hf2.integrable one_le_two)
  -- Step 3: `Φ = F ⋆ ρ` (kernel on the right) is `C^∞`.
  have hΦ : (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) =
      convolution ((ball (0 : Rn n) 1).indicator f) ρ (ContinuousLinearMap.lsmul ℝ ℝ).flip
        volume := by
    rw [convolution_flip]; rfl
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hΦ]
    exact hρc.contDiff_convolution_right _ hFi.locallyIntegrable hρ
  -- Step 4: `∇Φ(x) = ∫ F(t) ∇ρ(x - t) dt`, by testing `DΦ(x) = ∫ F(t) Dρ(x - t) dt` against each
  -- `v` and commuting `⟪v, ·⟫` with the (integrable) vector integral.
  have hgrad : ∀ p v, fderiv ℝ ρ p v = inner ℝ (gradient ρ p) v := fun p v => by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hgc : Continuous (gradient ρ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hρ1.continuous_fderiv one_ne_zero)
  have hgcs : HasCompactSupport (gradient ρ) :=
    (hρc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (Rn n)).symm) (map_zero _)
  have hint : Integrable (fun t => (ball (0 : Rn n) 1).indicator f t • gradient ρ (x - t)) volume :=
    hgcs.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hFi.locallyIntegrable hgc x
  have hD := hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ).flip
    hFi.locallyIntegrable hρ1 x
  have key : gradient (fun x => ∫ z, ρ z • (ball (0 : Rn n) 1).indicator f (x - z)) x =
      ∫ t, (ball (0 : Rn n) 1).indicator f t • gradient ρ (x - t) := by
    rw [hΦ]
    refine HasGradientAt.gradient ?_
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hD using 1
    ext v
    rw [convolution_precompR_apply _ hFi.locallyIntegrable (hρc.fderiv ℝ)
      (hρ1.continuous_fderiv one_ne_zero) x v, InnerProductSpace.toDual_apply_apply,
      real_inner_comm, ← innerSL_apply_apply ℝ, ← ContinuousLinearMap.integral_comp_comm _ hint,
      convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [innerSL_apply_apply, real_inner_smul_right, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, hgrad, real_inner_comm v]
    ring
  rw [key]
  -- Step 5: for `‖x‖ < 1 - ε`, `ζ(y) = ρ(x - y)` is a `C^∞` test function with
  -- `tsupport ζ ⊆ B_ε(x) ⊆ B` and `∇ζ(y) = -∇ρ(x - y)`.
  have hζ : ContDiff ℝ (⊤ : ℕ∞) (fun y => ρ (x - y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hζc : HasCompactSupport (fun y => ρ (x - y)) := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hζs : tsupport (fun y => ρ (x - y)) ⊆ ball 0 1 := by
    refine (tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id)).trans
      fun y hy => ?_
    have h1 : x - y ∈ tsupport ρ := hy
    have h2 : ‖x - y‖ ≤ ε := mem_closedBall_zero_iff.1 (hts h1)
    rw [mem_ball_zero_iff]
    calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
      _ < 1 := by linarith
  have hζg : ∀ y, gradient (fun y => ρ (x - y)) y = -gradient ρ (x - y) := fun y => by
    have hd : fderiv ℝ (fun y => ρ (x - y)) y = -(fderiv ℝ ρ (x - y)) := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_neg,
        ContinuousLinearMap.comp_id] using
        ((hρ1.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
          ((hasFDerivAt_id y).const_sub x)).fderiv
    rw [gradient, hd, map_neg, gradient]
  -- Step 6: the weak identity for `ζ`: `∫_B f(y) ∇ρ(x - y) dy = ∫_B ρ(x - y) g(y) dy`.
  have hw := hweak (fun y => ρ (x - y)) hζ hζc hζs
  simp only [hζg, smul_neg, integral_neg, neg_inj] at hw
  -- Step 7: pass to the zero extensions and substitute `z = x - y`.
  calc ∫ t, (ball (0 : Rn n) 1).indicator f t • gradient ρ (x - t)
      = ∫ y in ball (0 : Rn n) 1, f y • gradient ρ (x - y) := by
        rw [← integral_indicator measurableSet_ball]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        rw [indicator_smul_apply_left]
    _ = ∫ y in ball (0 : Rn n) 1, ρ (x - y) • g y := hw
    _ = ∫ y, ρ (x - y) • (ball (0 : Rn n) 1).indicator g y := by
        rw [← integral_indicator measurableSet_ball]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        rw [indicator_smul_apply]
    _ = ∫ z, ρ z • (ball (0 : Rn n) 1).indicator g (x - z) := by
        rw [← integral_sub_left_eq_self
          (fun z => ρ z • (ball (0 : Rn n) 1).indicator g (x - z)) volume x]
        simp only [sub_sub_cancel]
/-- Interior smooth approximation of `W^{1,2}(B)`, `B = B̆₁(0)` (Friedrichs mollification; Evans,
*PDE*, §5.3.1; Gilbarg–Trudinger §§7.2–7.3), used in the proof of Simon Ch. 5, Lemma 3.1 (p. 114):
for `0 < r < 1` there are `C^∞` functions `φ_j` with `φ_j → f` and `∇φ_j → g` in `L²(B_r)`.
With `F = 1_B f`, `G = 1_B g`, `ε_j = (1 - r)/(j + 2)` and `ρ_j` the normalized bump supported in
`B_{ε_j}`, take `φ_j = ρ_j * F`.  It is smooth with `∇φ_j = ρ_j * G` on `B_{1-ε_j} ⊇ B_r`, and
`F = f`, `G = g` on `B_r`, so the two errors on `B_r` are at most `∫_{ℝⁿ} |ρ_j * H - H|²` for
`H = F, G`, which tends to `0`. -/
theorem w12_ball_smooth_approximation : ∀ n : ℕ, 1 ≤ n → ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ r : ℝ, 0 < r → r < 1 → ∃ φ : ℕ → Rn n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) ∧ Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖φ j x - f x‖ₑ ^ 2) atTop (𝓝 0) ∧ Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r, ‖gradient (φ j) x - g x‖ₑ ^ 2) atTop (𝓝 0) := by
  intro n _ f g hfg r hr hr1
  -- Step 1: the zero extensions `F = 1_B f` and `G = 1_B g` lie in `L¹(ℝⁿ)` and `L²(ℝⁿ)`.
  have hB : MeasurableSet (ball (0 : Rn n) 1) := measurableSet_ball
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hF2 : MemLp ((ball (0 : Rn n) 1).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hB.nullMeasurableSet).2 hfg.1
  have hG2 : MemLp ((ball (0 : Rn n) 1).indicator g) 2 volume :=
    (memLp_indicator_iff_restrict hB.nullMeasurableSet).2 hfg.2.1
  have hF1 : Integrable ((ball (0 : Rn n) 1).indicator f) :=
    (integrable_indicator_iff hB).2 (hfg.1.integrable one_le_two)
  have hG1 : Integrable ((ball (0 : Rn n) 1).indicator g) :=
    (integrable_indicator_iff hB).2 (hfg.2.1.integrable one_le_two)
  -- Step 2: radii `ε_j = (1 - r)/(j + 2) ∈ (0, 1 - r)` with `ε_j → 0`, and normalized bumps
  -- `ρ_j ≥ 0` with `∫ ρ_j = 1` and `ρ_j = 0` off `B_{ε_j}`.
  obtain ⟨ε, hεpos, hεlt, hεlim⟩ : ∃ ε : ℕ → ℝ,
      (∀ j, 0 < ε j) ∧ (∀ j, ε j < 1 - r) ∧ Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun j => (1 - r) / ((j : ℝ) + 2), fun j => div_pos (sub_pos.2 hr1) (by positivity),
      fun j => div_lt_self (sub_pos.2 hr1) ?_, ?_⟩
    · have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      linarith
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨ρ, hρsmooth, hρcont, hρnonneg, hρint, hρsupp⟩ : ∃ ρ : ℕ → Rn n → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ρ j)) ∧ (∀ j, Continuous (ρ j)) ∧ (∀ j z, 0 ≤ ρ j z) ∧
        (∀ j, ∫ z, ρ j z = 1) ∧ ∀ j z, ε j ≤ ‖z‖ → ρ j z = 0 := by
    let b : ℕ → ContDiffBump (0 : Rn n) := fun j =>
      ⟨ε j / 2, ε j, half_pos (hεpos j), half_lt_self (hεpos j)⟩
    refine ⟨fun j => (b j).normed volume, fun j => (b j).contDiff_normed,
      fun j => (b j).continuous_normed, fun j z => (b j).nonneg_normed z,
      fun j => (b j).integral_normed, fun j z hz => ?_⟩
    have hz' : z ∉ Function.support ((b j).normed volume) := by
      rw [(b j).support_normed_eq, mem_ball_zero_iff, not_lt]
      exact hz
    exact Function.notMem_support.1 hz'
  -- Step 3: `φ_j = ρ_j * F` is smooth, and `∇φ_j = ρ_j * G` on `B_{1 - ε_j}`.
  have hmol := fun j : ℕ => Submission.w12_ball_mollification_gradient n f g hfg (ρ j) (ε j)
    (hρsmooth j) (hρsupp j)
  refine ⟨fun j x => ∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z),
    fun j => (hmol j).1, ?_, ?_⟩
  · -- Step 4: `F = f` on `B_r ⊆ B`, so the error is at most `∫_{ℝⁿ} |ρ_j * F - F|² → 0`.
    have hlim := Submission.mollifier_l2_tendsto n ℝ ((ball (0 : Rn n) 1).indicator f) hF1 hF2
      ρ ε hρcont hρnonneg hρint hρsupp hεlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun j => ?_
    have hpt : ∀ x ∈ ball (0 : Rn n) r,
        ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) - f x‖ₑ ^ 2 =
          ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) -
            (ball (0 : Rn n) 1).indicator f x‖ₑ ^ 2 := by
      intro x hx
      rw [indicator_of_mem (ball_subset_ball hr1.le hx)]
    calc ∫⁻ x in ball (0 : Rn n) r,
          ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) - f x‖ₑ ^ 2
        = ∫⁻ x in ball (0 : Rn n) r,
          ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) -
            (ball (0 : Rn n) 1).indicator f x‖ₑ ^ 2 := setLIntegral_congr_fun measurableSet_ball hpt
      _ ≤ ∫⁻ x, ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) -
            (ball (0 : Rn n) 1).indicator f x‖ₑ ^ 2 := setLIntegral_le_lintegral _ _
  · -- Step 5: on `B_r` we have `‖x‖ < 1 - ε_j`, so `∇φ_j = ρ_j * G` there, and `G = g`; the error
    -- is at most `∫_{ℝⁿ} |ρ_j * G - G|² → 0`.
    have hlim := Submission.mollifier_l2_tendsto n (Rn n) ((ball (0 : Rn n) 1).indicator g) hG1
      hG2 ρ ε hρcont hρnonneg hρint hρsupp hεlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun j => ?_
    have hpt : ∀ x ∈ ball (0 : Rn n) r,
        ‖gradient (fun x => ∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) x - g x‖ₑ ^ 2 =
          ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator g (x - z)) -
            (ball (0 : Rn n) 1).indicator g x‖ₑ ^ 2 := by
      intro x hx
      have hx' : ‖x‖ < 1 - ε j := by
        have := mem_ball_zero_iff.1 hx
        linarith [hεlt j]
      rw [(hmol j).2 x hx', indicator_of_mem (ball_subset_ball hr1.le hx)]
    calc ∫⁻ x in ball (0 : Rn n) r,
          ‖gradient (fun x => ∫ z, ρ j z • (ball (0 : Rn n) 1).indicator f (x - z)) x - g x‖ₑ ^ 2
        = ∫⁻ x in ball (0 : Rn n) r,
          ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator g (x - z)) -
            (ball (0 : Rn n) 1).indicator g x‖ₑ ^ 2 := setLIntegral_congr_fun measurableSet_ball hpt
      _ ≤ ∫⁻ x, ‖(∫ z, ρ j z • (ball (0 : Rn n) 1).indicator g (x - z)) -
            (ball (0 : Rn n) 1).indicator g x‖ₑ ^ 2 := setLIntegral_le_lintegral _ _

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

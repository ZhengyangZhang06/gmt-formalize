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
/-- **Dilation formula for lower integrals on `ℝⁿ`** (used in the boundary-layer estimate for the
Rellich compactness step in the proof of Simon Ch. 5, Lemma 3.1, p. 114).  For `t > 0`, every
`F : ℝⁿ → [0, ∞]` and every set `E ⊆ ℝⁿ` (neither assumed measurable),
`∫_E F(t x) dx = t^{-n} ∫_{tE} F(y) dy`, where `tE = {y : t⁻¹ y ∈ E}`.
Proof: `T x = t x` is a measurable equivalence with `T⁻¹(tE) = E`, and `T_# Lⁿ = t^{-n} Lⁿ`
(`Measure.map_addHaar_smul`, `finrank ℝ ℝⁿ = n`).  Change of variables along the measurable
embedding `T` needs no measurability of `F` or `E`. -/
theorem ble_sac_lintegral_comp_smul : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (E : Set (Rn n)) (t : ℝ), 0 < t → ∫⁻ x in E, F (t • x) = ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y := by
  intro n F E t ht
  -- `T x = t • x` as a measurable equivalence of `ℝⁿ`.
  let e : Rn n ≃ᵐ Rn n := (Homeomorph.smul (Units.mk0 t ht.ne')).toMeasurableEquiv
  have he : ∀ x, e x = t • x := fun x => rfl
  -- `T⁻¹(tE) = E`, since `t⁻¹ • (t • x) = x`.
  have hpre : e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E) = E := by
    ext x
    simp only [mem_preimage, he, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  -- `T_# Lⁿ = t^{-n} Lⁿ`.
  have hmap : Measure.map e volume = ENNReal.ofReal ((t ^ n)⁻¹) • (volume : Measure (Rn n)) := by
    have := Measure.map_addHaar_smul (volume : Measure (Rn n)) ht.ne'
    rw [finrank_euclideanSpace_fin] at this
    rw [show (e : Rn n → Rn n) = fun x => t • x from funext he, this]
    congr 2
    rw [abs_of_pos (by positivity)]
  -- Change variables along the measurable embedding `T`, then pull out the scalar.
  calc ∫⁻ x in E, F (t • x) = ∫⁻ x in e ⁻¹' ((fun y => t⁻¹ • y) ⁻¹' E), F (e x) := by
        rw [hpre]; simp only [he]
    _ = ∫⁻ y in (fun y => t⁻¹ • y) ⁻¹' E, F y ∂(Measure.map e volume) := by
        rw [e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map]
    _ = _ := by rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
/-- **Pointwise ray inequality for `C¹` functions** (inequality (2.2) of the smooth annulus
estimate in the boundary-layer estimate for the Rellich compactness step in the proof of Simon
Ch. 5, Lemma 3.1, p. 114).  For `φ ∈ C¹(ℝⁿ)`, `|x| ≤ 1` and `τ ≤ 1`,
`(1 - τ) |φ(x)|² ≤ 2 ∫_τ^1 |φ(t x)|² dt + 2 (1 - τ)² ∫_τ^1 |∇φ(σ x)|² dσ`.
Proof: for `t ∈ [τ, 1]`, the fundamental theorem of calculus along the ray gives
`φ(x) - φ(t x) = ∫_t^1 ⟨∇φ(σ x), x⟩ dσ`, so `|x| ≤ 1` and Cauchy–Schwarz on `[τ, 1]` give
`|φ(x) - φ(t x)|² ≤ (1 - τ) ∫_τ^1 |∇φ(σ x)|² dσ`.  Then `(a + b)² ≤ 2a² + 2b²`, and integrate
over `t ∈ [τ, 1]`, a set of length `1 - τ`. -/
theorem ble_sac_ray_sq_bound : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (x : Rn n), ‖x‖ ≤ 1 → ∀ τ : ℝ, τ ≤ 1 → ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 ≤ 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) + 2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
  intro n φ hφ x hx τ hτ
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- `d/dσ φ(σ x) = ⟨∇φ(σ x), x⟩`.
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => φ (σ • x)) (inner ℝ (gradient φ (σ • x)) x) σ := by
    intro σ
    have h1 : HasFDerivAt φ (fderiv ℝ φ (σ • x)) (σ • x) := (hdiff (σ • x)).hasFDerivAt
    have h2 : HasDerivAt (fun σ : ℝ => σ • x) x σ := by
      simpa using (hasDerivAt_id σ).smul_const x
    have h3 := h1.comp_hasDerivAt σ h2
    rw [inner_gradient_left]
    exact h3
  have hray : Continuous (fun σ : ℝ => σ • x) := continuous_id.smul continuous_const
  have hcont_inner : Continuous (fun σ : ℝ => inner ℝ (gradient φ (σ • x)) x) :=
    (hgc.comp hray).inner continuous_const
  set G : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 with hG_def
  set m : ℝ≥0∞ := ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ with hm_def
  -- Cauchy–Schwarz on `[τ, 1]`: `m² ≤ (1 - τ) G`.
  have hcs : m ^ 2 ≤ ENNReal.ofReal (1 - τ) * G := by
    have hmeas : AEMeasurable (fun σ : ℝ => ‖gradient φ (σ • x)‖ₑ) (volume.restrict (Icc τ 1)) :=
      (hgc.comp hray).enorm.aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc τ 1))
      Real.HolderConjugate.two_two (aemeasurable_const (b := (1 : ℝ≥0∞))) hmeas
    simp only [Pi.mul_apply, one_mul, setLIntegral_const, Real.volume_Icc,
      ENNReal.rpow_two, one_pow] at h
    calc m ^ 2 ≤ ((ENNReal.ofReal (1 - τ)) ^ (1 / 2 : ℝ) * G ^ (1 / 2 : ℝ)) ^ 2 := by
          gcongr
      _ = ENNReal.ofReal (1 - τ) * G := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
  -- `(p + q)² ≤ 2p² + 2q²` in `[0, ∞]`.
  have hsq : ∀ p q : ℝ≥0∞, (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
    intro p q
    rcases eq_or_ne p ⊤ with hp | hp
    · simp [hp]
    rcases eq_or_ne q ⊤ with hq | hq
    · simp [hq]
    lift p to ℝ≥0 using hp
    lift q to ℝ≥0 using hq
    have h := add_sq_le (a := p) (b := q)
    rw [mul_add] at h
    exact_mod_cast h
  -- Pointwise inequality (2.1) for `t ∈ [τ, 1]`.
  have hpt : ∀ t ∈ Icc τ 1, ‖φ x‖ₑ ^ 2 ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G) := by
    intro t ht
    have hftc : ∫ σ in t..1, inner ℝ (gradient φ (σ • x)) x = φ x - φ (t • x) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
        (hcont_inner.intervalIntegrable t 1)]
      simp
    have hb : ‖φ x - φ (t • x)‖ₑ ≤ m := by
      rw [← hftc, intervalIntegral.integral_of_le ht.2]
      calc ‖∫ σ in Ioc t 1, inner ℝ (gradient φ (σ • x)) x‖ₑ
            ≤ ∫⁻ σ in Ioc t 1, ‖inner ℝ (gradient φ (σ • x)) x‖ₑ :=
              enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ σ in Ioc t 1, ‖gradient φ (σ • x)‖ₑ := by
            apply lintegral_mono
            intro σ
            rw [enorm_le_iff_norm_le]
            calc ‖inner ℝ (gradient φ (σ • x)) x‖ ≤ ‖gradient φ (σ • x)‖ * ‖x‖ :=
                  norm_inner_le_norm _ _
              _ ≤ ‖gradient φ (σ • x)‖ * 1 := by gcongr
              _ = _ := mul_one _
        _ ≤ m := lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1 le_rfl))
    have htri : ‖φ x‖ₑ ≤ ‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ := by
      calc ‖φ x‖ₑ = ‖φ (t • x) + (φ x - φ (t • x))‖ₑ := by ring_nf
        _ ≤ _ := enorm_add_le _ _
    calc ‖φ x‖ₑ ^ 2 ≤ (‖φ (t • x)‖ₑ + ‖φ x - φ (t • x)‖ₑ) ^ 2 := by gcongr
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * ‖φ x - φ (t • x)‖ₑ ^ 2 := hsq _ _
      _ ≤ 2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * m ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  -- Integrate (2.1) over `t ∈ [τ, 1]`.
  calc ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 = ∫⁻ t in Icc τ 1, ‖φ x‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
    _ ≤ ∫⁻ t in Icc τ 1, (2 * ‖φ (t • x)‖ₑ ^ 2 + 2 * (ENNReal.ofReal (1 - τ) * G)) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = 2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
          2 * (ENNReal.ofReal (1 - τ) * G) * ENNReal.ofReal (1 - τ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp),
          setLIntegral_const, Real.volume_Icc]
    _ = _ := by
        rw [ENNReal.ofReal_pow (by linarith)]
        ring
/-- **Averaged dilation over an annulus** (function term and kernel bound of the boundary-layer
estimate in the proof of Simon Ch. 5, Lemma 3.1, p. 114).  For measurable `F : ℝⁿ → [0, ∞]`,
`1/2 ≤ r < 1`, `s > 0`, `τ ≥ 1/2` and the annulus `A = B̆_s(0) \ B̆_{rs}(0)`,
`∫_{[τ,1]} ∫_A F(t x) dx dt ≤ 2^{n+1} (1 - r) ∫_{B̆_s(0)} F(y) dy`.
Proof: the dilation formula turns the inner integral into `∫ F(y) K(y, t) dy` with
`K(y, t) = t^{-n} 1_S(y, t)`, `S = {(y, t) : r s t ≤ |y| < s t}`; by Tonelli the left side is
`∫ F(y) k(y) dy` with `k(y) = ∫_{[τ,1]} K(y, t) dt`, and `k ≤ 2^{n+1} (1 - r) 1_{B̆_s(0)}`, since
`k` vanishes off `B̆_s(0)`, `t^{-n} ≤ 2^n`, and `K(y, ·)` is supported in
`(|y|/s, |y|/(r s)]`, an interval of length at most `2 (1 - r)`. -/
theorem ble_sac_annulus_dilation_avg_le : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞), Measurable F → ∀ r s τ : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → 1 / 2 ≤ τ → ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) ≤ ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, F y := by
  intro n F hF r s τ hr1 hr2 hs hτ
  have hr0 : 0 < r := by linarith
  -- Step 1: the kernel set `S` and the measurable weight `K(y, t) = t^{-n} 1_S(y, t)`.
  set S : Set (Rn n × ℝ) := {p | r * s * p.2 ≤ ‖p.1‖ ∧ ‖p.1‖ < s * p.2} with hS_def
  have hSm : MeasurableSet S := by
    have h1 : Measurable fun p : Rn n × ℝ => r * s * p.2 := measurable_const.mul measurable_snd
    have h2 : Measurable fun p : Rn n × ℝ => ‖p.1‖ := measurable_fst.norm
    have h3 : Measurable fun p : Rn n × ℝ => s * p.2 := measurable_const.mul measurable_snd
    exact (measurableSet_le h1 h2).inter (measurableSet_lt h2 h3)
  set K : Rn n × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((p.2 ^ n)⁻¹) * S.indicator 1 p with hK_def
  have hKm : Measurable K :=
    (ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const n).inv)).mul
      (measurable_one.indicator hSm)
  -- Step 2: for fixed `t ∈ [τ, 1]`, the dilation formula gives `∫_A F(t x) dx = ∫ F(y) K(y, t) dy`,
  -- because `t⁻¹ y ∈ A ↔ (y, t) ∈ S`.
  have step1 : ∀ t ∈ Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x) =
      ∫⁻ y, F y * K (y, t) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [Submission.ble_sac_lintegral_comp_smul n F _ t ht0]
    have hpre : (fun y => t⁻¹ • y) ⁻¹' (ball (0 : Rn n) s \ ball 0 (r * s)) =
        {y | (y, t) ∈ S} := by
      ext y
      simp only [mem_preimage, Set.mem_sdiff, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos ht0, not_lt, Set.mem_ofPred_eq, hS_def]
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · rw [le_inv_mul_iff₀ ht0] at h2; linarith
        · rw [inv_mul_lt_iff₀ ht0] at h1; linarith
      · rintro ⟨h1, h2⟩
        constructor
        · rw [inv_mul_lt_iff₀ ht0]; linarith
        · rw [le_inv_mul_iff₀ ht0]; linarith
    have hSt : MeasurableSet {y : Rn n | (y, t) ∈ S} := measurable_prodMk_right hSm
    rw [hpre, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hSt]
    congr 1
    funext y
    by_cases hy : (y, t) ∈ S
    · rw [indicator_of_mem (show y ∈ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_mem hy, Pi.one_apply, mul_one]
      ring
    · rw [indicator_of_notMem (show y ∉ {y : Rn n | (y, t) ∈ S} from hy)]
      simp only [hK_def, indicator_of_notMem hy, mul_zero]
  -- Step 4: the kernel bound `k(y) = ∫_{[τ,1]} K(y, t) dt ≤ 2^{n+1} (1 - r) 1_{B̆_s(0)}(y)`.
  have kernel : ∀ y : Rn n, ∫⁻ t in Icc τ 1, K (y, t) ≤
      (ball (0 : Rn n) s).indicator (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y := by
    intro y
    by_cases hy : y ∈ ball (0 : Rn n) s
    · rw [indicator_of_mem hy]
      rw [mem_ball_zero_iff] at hy
      -- For `|y| < s`: `K(y, t) ≤ 2^n 1_{(|y|/s, |y|/(r s)]}(t)` for `t ∈ [τ, 1]`.
      have hbound : ∀ t ∈ Icc τ 1, K (y, t) ≤
          (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t := by
        intro t ht
        have ht0 : 0 < t := by linarith [ht.1]
        by_cases hS : (y, t) ∈ S
        · have hmem : t ∈ Ioc (‖y‖ / s) (‖y‖ / (r * s)) := by
            constructor
            · rw [div_lt_iff₀ hs]; linarith [hS.2]
            · rw [le_div_iff₀ (by positivity)]; linarith [hS.1]
          rw [indicator_of_mem hmem]
          simp only [hK_def, indicator_of_mem hS, Pi.one_apply, mul_one]
          apply ENNReal.ofReal_le_ofReal
          rw [← inv_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [inv_le_comm₀ ht0 (by norm_num)]
          linarith [ht.1]
        · simp [hK_def, indicator_of_notMem hS]
      -- The support interval has length `|y| (1 - r) / (r s) ≤ 2 (1 - r)`.
      have hlen : ‖y‖ / (r * s) - ‖y‖ / s ≤ 2 * (1 - r) := by
        rw [show ‖y‖ / (r * s) - ‖y‖ / s = ‖y‖ * (1 - r) / (r * s) by field_simp]
        rw [div_le_iff₀ (by positivity)]
        have h1 : ‖y‖ * (1 - r) ≤ s * (1 - r) := mul_le_mul_of_nonneg_right hy.le (by linarith)
        have h2 : s * (1 - r) ≤ 2 * (1 - r) * (r * s) := by
          nlinarith [mul_nonneg (mul_nonneg hs.le (by linarith : (0:ℝ) ≤ 1 - r))
            (by linarith : (0:ℝ) ≤ 2 * r - 1)]
        linarith
      calc ∫⁻ t in Icc τ 1, K (y, t)
            ≤ ∫⁻ t in Icc τ 1, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator
                (fun _ => ENNReal.ofReal (2 ^ n)) t := setLIntegral_mono' measurableSet_Icc hbound
        _ ≤ ∫⁻ t, (Ioc (‖y‖ / s) (‖y‖ / (r * s))).indicator (fun _ => ENNReal.ofReal (2 ^ n)) t :=
            setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (‖y‖ / (r * s) - ‖y‖ / s) := by
            rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
        _ ≤ ENNReal.ofReal (2 ^ n) * ENNReal.ofReal (2 * (1 - r)) := by
            gcongr
        _ = ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    · -- For `|y| ≥ s`: `s t ≤ s ≤ |y|`, so `(y, t) ∉ S` and `k(y) = 0`.
      rw [indicator_of_notMem hy]
      have hz : ∀ t ∈ Icc τ 1, K (y, t) = 0 := by
        intro t ht
        have hS : (y, t) ∉ S := by
          rintro ⟨_, h2⟩
          rw [mem_ball_zero_iff, not_lt] at hy
          nlinarith [ht.2]
        simp only [hK_def, indicator_of_notMem hS, mul_zero]
      rw [setLIntegral_congr_fun measurableSet_Icc hz, lintegral_zero]
  -- Steps 3 and 5: Tonelli, then integrate the kernel bound against `F`.
  have hmeas : AEMeasurable (Function.uncurry fun (t : ℝ) (y : Rn n) => F y * K (y, t))
      ((volume.restrict (Icc τ 1)).prod volume) :=
    ((hF.comp measurable_snd).mul (hKm.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
  calc ∫⁻ t in Icc τ 1, ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), F (t • x)
        = ∫⁻ t in Icc τ 1, ∫⁻ y, F y * K (y, t) := setLIntegral_congr_fun measurableSet_Icc step1
    _ = ∫⁻ y, ∫⁻ t in Icc τ 1, F y * K (y, t) := lintegral_lintegral_swap hmeas
    _ = ∫⁻ y, F y * ∫⁻ t in Icc τ 1, K (y, t) := by
        congr 1
        funext y
        exact lintegral_const_mul _ (hKm.comp measurable_prodMk_left)
    _ ≤ ∫⁻ y, F y * (ball (0 : Rn n) s).indicator
          (fun _ => ENNReal.ofReal (2 ^ (n + 1) * (1 - r))) y :=
        lintegral_mono (fun y => by gcongr; exact kernel y)
    _ = ∫⁻ y in ball (0 : Rn n) s, F y * ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1
        funext y
        by_cases hy : y ∈ ball (0 : Rn n) s
        · simp [indicator_of_mem hy]
        · simp [indicator_of_notMem hy]
    _ = _ := by rw [lintegral_mul_const _ hF, mul_comm]
/-- **Smooth annulus estimate** (the smooth step of the boundary-layer estimate for `W^{1,2}` on
balls).  Let `n ≥ 1`, `φ ∈ C¹(ℝⁿ)`, `1/2 ≤ r < 1`, `0 < s ≤ 1`, `a := √(1 - r)` and
`A := B̆_s(0) \ B̆_{rs}(0)`.  Then `∫_A |φ|² ≤ 2^{n+3} a (∫_{B̆_s(0)} |φ|² + ∫_{B̆_s(0)} |∇φ|²)`
(lintegrals of squared extended norms).  With `τ := 1 - a/2 ∈ [1/2, 1)`, integrate the ray
inequality `ble_sac_ray_sq_bound` over `A` and swap the order of integration (Tonelli).  The
dilation formula `ble_sac_lintegral_comp_smul`, with `σA ⊆ B̆_s(0)` and `σ⁻ⁿ ≤ 2ⁿ` for
`σ ∈ [τ, 1]`, bounds the gradient term by `2ⁿ (1 - τ) ∫_{B̆_s(0)} |∇φ|²`; the kernel bound
`ble_sac_annulus_dilation_avg_le` bounds the function term by `2^{n+1} (1 - r) ∫_{B̆_s(0)} |φ|²`.
Dividing by `1 - τ = a/2` and using `1 - r = a²`, `a ≤ 1` gives the constant `2^{n+3} a`. -/
theorem ble_smooth_annulus_estimate : ∀ n : ℕ, 1 ≤ n → ∀ (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ r s : ℝ, 1 / 2 ≤ r → r < 1 → 0 < s → s ≤ 1 → ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (2 ^ (n + 3) * Real.sqrt (1 - r)) * ((∫⁻ x in ball (0 : Rn n) s, ‖φ x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) s, ‖gradient φ x‖ₑ ^ 2) := by
  intro n _ φ hφ r s hr1 hr2 hs0 hs1
  -- Step 0: `a := √(1 - r) ∈ (0, 1]` with `a² = 1 - r`, and `τ := 1 - a/2 ∈ [1/2, 1]`.
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = Real.sqrt (1 - r) := ⟨_, rfl⟩
  rw [← ha_def]
  have ha0 : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.2 (by linarith)
  have ha1 : a ≤ 1 := by
    rw [ha_def]
    calc Real.sqrt (1 - r) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have ha2 : a ^ 2 = 1 - r := by rw [ha_def]; exact Real.sq_sqrt (by linarith)
  obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ, τ = 1 - a / 2 := ⟨_, rfl⟩
  have hτ1 : τ ≤ 1 := by rw [hτ_def]; linarith
  have hτ2 : 1 / 2 ≤ τ := by rw [hτ_def]; linarith
  have h1τ : 1 - τ = a / 2 := by rw [hτ_def]; ring
  set A := ball (0 : Rn n) s \ ball 0 (r * s)
  have hA : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hA1 : ∀ x ∈ A, ‖x‖ ≤ 1 := fun x hx => by
    have h := mem_ball_zero_iff.1 hx.1
    linarith
  -- `φ` and `∇φ = (toDual ℝ ℝⁿ)⁻¹ ∘ Dφ` are continuous; measurability for Tonelli.
  have hφc : Continuous φ := hφ.continuous
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hFm : Measurable (fun y : Rn n => ‖φ y‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp hφc.enorm).measurable
  have hH1 : Measurable (fun p : Rn n × ℝ => ‖φ (p.2 • p.1)‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp
      (hφc.comp (continuous_snd.smul continuous_fst)).enorm).measurable
  have hH2 : Measurable (fun p : Rn n × ℝ => ‖gradient φ (p.2 • p.1)‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp
      (hgc.comp (continuous_snd.smul continuous_fst)).enorm).measurable
  have hP : Measurable (fun x : Rn n => ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) :=
    hH1.lintegral_prod_right'
  have hQ : Measurable (fun x : Rn n => ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2) :=
    hH2.lintegral_prod_right'
  -- Step 3: integrate the ray inequality over `A` (where `‖x‖ < s ≤ 1`), then swap integrals.
  have h3 : ENNReal.ofReal (1 - τ) * ∫⁻ x in A, ‖φ x‖ₑ ^ 2 ≤
      2 * (∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2) +
        2 * ENNReal.ofReal ((1 - τ) ^ 2) *
          ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
    have hs1 : ∫⁻ x in A, ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2 =
        ∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2 :=
      lintegral_lintegral_swap hH1.aemeasurable
    have hs2 : ∫⁻ x in A, ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 =
        ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 :=
      lintegral_lintegral_swap hH2.aemeasurable
    calc ENNReal.ofReal (1 - τ) * ∫⁻ x in A, ‖φ x‖ₑ ^ 2
          = ∫⁻ x in A, ENNReal.ofReal (1 - τ) * ‖φ x‖ₑ ^ 2 :=
            (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ x in A, (2 * (∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
            2 * ENNReal.ofReal ((1 - τ) ^ 2) * ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2) :=
            setLIntegral_mono' hA fun x hx =>
              Submission.ble_sac_ray_sq_bound n φ hφ x (hA1 x hx) τ hτ1
      _ = 2 * (∫⁻ x in A, ∫⁻ t in Icc τ 1, ‖φ (t • x)‖ₑ ^ 2) +
            2 * ENNReal.ofReal ((1 - τ) ^ 2) *
              ∫⁻ x in A, ∫⁻ σ in Icc τ 1, ‖gradient φ (σ • x)‖ₑ ^ 2 := by
          rw [lintegral_add_left (hP.const_mul 2), lintegral_const_mul _ hP,
            lintegral_const_mul _ hQ]
      _ = _ := by rw [hs1, hs2]
  -- Step 4: gradient term.  For `σ ∈ [τ, 1]`, `∫_A |∇φ(σx)|² dx ≤ 2ⁿ ∫_{B̆_s(0)} |∇φ|²` by the
  -- dilation formula, `σ⁻ⁿ ≤ 2ⁿ` and `σA ⊆ B̆_s(0)`; then integrate over `σ ∈ [τ, 1]`.
  have h4 : ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ n * (1 - τ)) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 := by
    have hJ : ∀ σ ∈ Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 ^ n) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 := by
      intro σ hσ
      have hσ0 : 0 < σ := by linarith [hσ.1]
      rw [Submission.ble_sac_lintegral_comp_smul n (fun y => ‖gradient φ y‖ₑ ^ 2) A σ hσ0]
      gcongr ?_ * ?_
      · apply ENNReal.ofReal_le_ofReal
        rw [← inv_pow]
        apply pow_le_pow_left₀ (by positivity)
        rw [inv_le_comm₀ hσ0 (by norm_num)]
        linarith [hσ.1]
      · apply lintegral_mono_set
        intro y hy
        rw [Set.mem_preimage] at hy
        have h1 := mem_ball_zero_iff.1 hy.1
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hσ0] at h1
        rw [mem_ball_zero_iff]
        calc ‖y‖ = σ * (σ⁻¹ * ‖y‖) := by rw [← mul_assoc, mul_inv_cancel₀ hσ0.ne', one_mul]
          _ < σ * s := by gcongr
          _ ≤ s := by nlinarith [hσ.2]
    calc ∫⁻ σ in Icc τ 1, ∫⁻ x in A, ‖gradient φ (σ • x)‖ₑ ^ 2
          ≤ ∫⁻ σ in Icc τ 1,
              ENNReal.ofReal (2 ^ n) * ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2 :=
            setLIntegral_mono measurable_const hJ
      _ = _ := by
          rw [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_mul (by positivity)]
          ring
  -- Step 5: function term, by the kernel bound.
  have h5 : ∫⁻ t in Icc τ 1, ∫⁻ x in A, ‖φ (t • x)‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 ^ (n + 1) * (1 - r)) * ∫⁻ y in ball (0 : Rn n) s, ‖φ y‖ₑ ^ 2 :=
    Submission.ble_sac_annulus_dilation_avg_le n (fun y => ‖φ y‖ₑ ^ 2) hFm r s τ hr1 hr2 hs0 hτ2
  -- Step 6: combine, cancel the finite nonzero factor `1 - τ = a/2`, and compare coefficients
  -- using `1 - r = a²` and `a ≤ 1`.
  set X := ∫⁻ x in A, ‖φ x‖ₑ ^ 2
  set P := ∫⁻ y in ball (0 : Rn n) s, ‖φ y‖ₑ ^ 2
  set G := ∫⁻ y in ball (0 : Rn n) s, ‖gradient φ y‖ₑ ^ 2
  have key : ENNReal.ofReal (a / 2) * X ≤
      2 * (ENNReal.ofReal (2 ^ (n + 1) * a ^ 2) * P) +
        2 * ENNReal.ofReal ((a / 2) ^ 2) * (ENNReal.ofReal (2 ^ n * (a / 2)) * G) := by
    rw [← h1τ, ha2]
    refine h3.trans ?_
    gcongr
  have hb0 : ENNReal.ofReal (a / 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  refine (ENNReal.mul_le_mul_iff_right hb0 ENNReal.ofReal_ne_top).1 (key.trans ?_)
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  have e1 : (2 : ℝ≥0∞) * (ENNReal.ofReal (2 ^ (n + 1) * a ^ 2) * P) =
      ENNReal.ofReal (2 * (2 ^ (n + 1) * a ^ 2)) * P := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← h2, mul_assoc]
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((a / 2) ^ 2) * (ENNReal.ofReal (2 ^ n * (a / 2)) * G) =
      ENNReal.ofReal (2 * (a / 2) ^ 2 * (2 ^ n * (a / 2))) * G := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (a / 2) ^ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← h2]
    ring
  have e3 : ENNReal.ofReal (a / 2) * (ENNReal.ofReal (2 ^ (n + 3) * a) * (P + G)) =
      ENNReal.ofReal (a / 2 * (2 ^ (n + 3) * a)) * P +
        ENNReal.ofReal (a / 2 * (2 ^ (n + 3) * a)) * G := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a / 2)]
    ring
  rw [e1, e2, e3]
  -- `2 · 2^{n+1} a² = (a/2) · 2^{n+3} a` and `2 (a/2)² · 2ⁿ (a/2) = 2ⁿ a² (a/4) ≤ 2ⁿ a² · 4`.
  have c1 : 2 * (2 ^ (n + 1) * a ^ 2) ≤ a / 2 * (2 ^ (n + 3) * a) := le_of_eq (by ring)
  have c2 : 2 * (a / 2) ^ 2 * (2 ^ n * (a / 2)) ≤ a / 2 * (2 ^ (n + 3) * a) := by
    have k1 : 2 * (a / 2) ^ 2 * (2 ^ n * (a / 2)) = 2 ^ n * a ^ 2 * (a / 4) := by ring
    have k2 : a / 2 * (2 ^ (n + 3) * a) = 2 ^ n * a ^ 2 * 4 := by ring
    rw [k1, k2]
    have h0 : (0 : ℝ) ≤ 2 ^ n * a ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 4 - a / 4)]
  exact add_le_add (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal c1) (by positivity))
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal c2) (by positivity))
/-- Convergence of squared `L²` norms under `L²` convergence (the step "by Minkowski the `L²` norms
converge" in the proof of the boundary-layer estimate).  If `f ∈ L²(μ)`, the `φ_j` are `μ`-a.e.
strongly measurable and `∫ |φ_j − f|² dμ → 0`, then `∫ |φ_j|² dμ → ∫ |f|² dμ` in `[0, ∞]`.
Proof: with `N(h) = eLpNorm h 2 μ`, `∫ |h|² dμ = N(h)²` for a.e. strongly measurable `h`, so
`N(φ_j − f) → 0` (`x ↦ x^{1/2}` is continuous on `[0, ∞]`).  Minkowski gives
`N(f) − N(φ_j − f) ≤ N(φ_j) ≤ N(f) + N(φ_j − f)`, and both bounds tend to `N(f) < ∞`; hence
`N(φ_j) → N(f)`, and squaring is continuous on `[0, ∞]`. -/
theorem ble_lintegral_sq_tendsto_of_l2_tendsto : ∀ {α : Type} [MeasurableSpace α] {E : Type} [NormedAddCommGroup E] (μ : Measure α) (f : α → E) (φ : ℕ → α → E), MemLp f 2 μ → (∀ j, AEStronglyMeasurable (φ j) μ) → Tendsto (fun j => ∫⁻ x, ‖φ j x - f x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖φ j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)) := by
  intro α _ E _ μ f φ hf hφ hlim
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  -- Step 1: `∫⁻ ‖h‖ₑ ^ 2 = (eLpNorm h 2 μ) ^ 2` for a.e. strongly measurable `h`.
  have hsq : ∀ h : α → E, AEStronglyMeasurable h μ →
      ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ = eLpNorm h 2 μ ^ 2 := by
    intro h hh
    have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hh
    simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at this
    exact this.symm
  -- Notation: `a j` is the error norm, `b j` the approximant norm, `c < ∞` the limit norm.
  set a : ℕ → ℝ≥0∞ := fun j => eLpNorm (φ j - f) 2 μ
  set b : ℕ → ℝ≥0∞ := fun j => eLpNorm (φ j) 2 μ with hb
  set c : ℝ≥0∞ := eLpNorm f 2 μ with hc
  have hc_top : c ≠ ∞ := hf.eLpNorm_lt_top.ne
  -- Step 2: `a j → 0`, as the square root of `a j ^ 2 = ∫⁻ ‖φ j - f‖ₑ ^ 2 → 0`.
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h2 : Tendsto (fun j => a j ^ 2) atTop (𝓝 0) :=
      hlim.congr fun j => hsq _ ((hφ j).sub hfm)
    have h3 : Tendsto (fun j => (a j ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h2
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr fun j => ?_
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  -- Step 3: Minkowski, `b j ≤ c + a j` and `c ≤ b j + a j`.
  have hup : ∀ j, b j ≤ c + a j := by
    intro j
    have : φ j = f + (φ j - f) := by abel
    calc b j = eLpNorm (f + (φ j - f)) 2 μ := by rw [hb]; dsimp only; rw [← this]
      _ ≤ eLpNorm f 2 μ + eLpNorm (φ j - f) 2 μ := eLpNorm_add_le (by norm_num)
  have hlow : ∀ j, c ≤ b j + a j := by
    intro j
    have : f = φ j - (φ j - f) := by abel
    calc c = eLpNorm (φ j - (φ j - f)) 2 μ := by rw [hc]; rw [← this]
      _ ≤ eLpNorm (φ j) 2 μ + eLpNorm (φ j - f) 2 μ := eLpNorm_sub_le (by norm_num)
  -- Step 4: squeeze `c - a j ≤ b j ≤ c + a j`; both bounds tend to `c` because `c ≠ ∞`.
  have hbc : Tendsto b atTop (𝓝 c) := by
    have hU : Tendsto (fun j => c + a j) atTop (𝓝 (c + 0)) := tendsto_const_nhds.add ha0
    have hL : Tendsto (fun j => c - a j) atTop (𝓝 (c - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds ha0 (Or.inl hc_top)
    rw [add_zero] at hU
    rw [tsub_zero] at hL
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hL hU
      (fun j => tsub_le_iff_right.2 (hlow j)) hup
  -- Step 5: square the limit and convert back to lintegrals by Step 1.
  have := ENNReal.Tendsto.pow (n := 2) hbc
  rw [hsq f hfm]
  exact this.congr fun j => (hsq _ (hφ j)).symm
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
/-- **Translating a ball into a larger ball does not increase a lintegral** (translation
invariance of Lebesgue measure; Evans, *PDE*, §5.8.2 Theorem 3(i), Gilbarg–Trudinger §7.11).
If `r + ‖w‖ ≤ s`, then `x - w ∈ B̆_s(0)` for every `x ∈ B̆_r(0)`, so for an arbitrary
`F : ℝⁿ → [0, ∞]` (no measurability needed) `∫⁻_{B̆_r(0)} F(x - w) dx ≤ ∫⁻_{B̆_s(0)} F`.

Both set lintegrals are lintegrals of indicators (open balls are measurable), the integrands
compare pointwise as `1_{B̆_r}(x) F(x - w) ≤ (1_{B̆_s} F)(x - w)`, and the change of variables
`x ↦ x - w`, valid for every `[0, ∞]`-valued function, removes the translation. -/
theorem lintegral_ball_comp_sub_le : ∀ (n : ℕ) (F : Rn n → ℝ≥0∞) (r s : ℝ) (w : Rn n), r + ‖w‖ ≤ s → ∫⁻ x in ball (0 : Rn n) r, F (x - w) ≤ ∫⁻ x in ball (0 : Rn n) s, F x := by
  intro n F r s w hrs
  -- Steps 1–2: `x ∈ B̆_r(0)` gives `‖x - w‖ ≤ ‖x‖ + ‖w‖ < r + ‖w‖ ≤ s`, hence the pointwise bound.
  have hpt : ∀ x, (ball (0 : Rn n) r).indicator (fun y => F (y - w)) x ≤
      (ball (0 : Rn n) s).indicator F (x - w) := by
    intro x
    by_cases hx : x ∈ ball (0 : Rn n) r
    · have hxw : x - w ∈ ball (0 : Rn n) s :=
        mem_ball_zero_iff.2 ((norm_sub_le x w).trans_lt (by linarith [mem_ball_zero_iff.1 hx]))
      rw [indicator_of_mem hx, indicator_of_mem hxw]
    · rw [indicator_of_notMem hx]
      exact zero_le
  -- Steps 3–6: indicator form, monotonicity, and translation invariance of Lebesgue measure.
  calc ∫⁻ x in ball (0 : Rn n) r, F (x - w)
      = ∫⁻ x, (ball (0 : Rn n) r).indicator (fun y => F (y - w)) x :=
        (lintegral_indicator measurableSet_ball _).symm
    _ ≤ ∫⁻ x, (ball (0 : Rn n) s).indicator F (x - w) := lintegral_mono hpt
    _ = ∫⁻ x, (ball (0 : Rn n) s).indicator F x :=
        lintegral_sub_right_eq_self ((ball (0 : Rn n) s).indicator F) w
    _ = ∫⁻ x in ball (0 : Rn n) s, F x := lintegral_indicator measurableSet_ball F
/-- Crude `L²` bound for translation differences on balls, used for the translation estimate in
the proof of Simon Ch. 5, Lemma 3.1 (p. 114): if `r + ‖z‖ ≤ s` and `h` is a.e. strongly measurable
on `B_s`, then `∫_{B_r} |h(x - z) - h(x)|² ≤ 4 ∫_{B_s} |h|²`.  Pointwise
`|h(x - z) - h(x)|² ≤ 2 |h(x - z)|² + 2 |h(x)|²`; the translated term is bounded by
`lintegral_ball_comp_sub_le` and the untranslated one by `B_r ⊆ B_s`. -/
theorem lintegral_ball_translation_difference_le : ∀ (n : ℕ) (h : Rn n → ℝ) (r s : ℝ) (z : Rn n), r + ‖z‖ ≤ s → AEStronglyMeasurable h (volume.restrict (ball (0 : Rn n) s)) → ∫⁻ x in ball (0 : Rn n) r, ‖h (x - z) - h x‖ₑ ^ 2 ≤ 4 * ∫⁻ x in ball (0 : Rn n) s, ‖h x‖ₑ ^ 2 := by
  intro n h r s z hrs hh
  -- `B_r ⊆ B_s`, so the untranslated summand is a.e. measurable on `B_r`.
  have hsub : ball (0 : Rn n) r ⊆ ball 0 s :=
    ball_subset_ball ((le_add_of_nonneg_right (norm_nonneg z)).trans hrs)
  have hmeas : AEMeasurable (fun x => 2 * ‖h x‖ₑ ^ 2) (volume.restrict (ball (0 : Rn n) r)) :=
    ((hh.mono_measure (Measure.restrict_mono hsub le_rfl)).enorm.pow_const 2).const_mul 2
  -- `(a + b)² ≤ 2a² + 2b²` in `ℝ≥0∞` (the power-mean inequality for `p = 2`).
  have hsq : ∀ a b : ℝ≥0∞, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
    norm_num at h2
    simpa [mul_add] using h2
  calc ∫⁻ x in ball (0 : Rn n) r, ‖h (x - z) - h x‖ₑ ^ 2
      ≤ ∫⁻ x in ball (0 : Rn n) r, (2 * ‖h (x - z)‖ₑ ^ 2 + 2 * ‖h x‖ₑ ^ 2) :=
        lintegral_mono fun x => (pow_le_pow_left' enorm_sub_le 2).trans (hsq _ _)
    _ = 2 * (∫⁻ x in ball (0 : Rn n) r, ‖h (x - z)‖ₑ ^ 2) +
          2 * ∫⁻ x in ball (0 : Rn n) r, ‖h x‖ₑ ^ 2 := by
        rw [lintegral_add_right' _ hmeas, lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * (∫⁻ x in ball (0 : Rn n) s, ‖h x‖ₑ ^ 2) +
          2 * ∫⁻ x in ball (0 : Rn n) s, ‖h x‖ₑ ^ 2 :=
        add_le_add
          (mul_le_mul_right
            (Submission.lintegral_ball_comp_sub_le n (fun y => ‖h y‖ₑ ^ 2) r s z hrs) 2)
          (mul_le_mul_right (lintegral_mono_set hsub) 2)
    _ = 4 * ∫⁻ x in ball (0 : Rn n) s, ‖h x‖ₑ ^ 2 := by ring

/-- **Translation estimate for `C¹` functions** (Evans, *PDE*, §5.8.2 Theorem 3(i);
Gilbarg–Trudinger §7.11): for `φ ∈ C¹(ℝⁿ)`, `r ∈ ℝ` and `z ∈ ℝⁿ`,
`∫⁻_{B̆_r(0)} |φ(x - z) - φ(x)|² dx ≤ |z|² ∫⁻_{B̆_{r+|z|}(0)} |∇φ|²` in `[0, ∞]`.

The segment bound `poincare_c1_segment_sq_bound` at the pair `(x - z, x)` gives
`|φ(x - z) - φ(x)|² ≤ |z|² ∫⁻_{[0,1]} |∇φ(x - t z)|² dt` for every `x`.  Integrate over `B̆_r(0)`
and swap the integrals (Tonelli; the integrand is continuous in `(x, t)`).  For `t ∈ [0, 1]`,
`|t z| ≤ |z|`, so `lintegral_ball_comp_sub_le` bounds each inner integral by
`∫⁻_{B̆_{r+|z|}(0)} |∇φ|²`, and `[0, 1]` has measure one. -/
theorem contDiff_one_ball_translation_estimate : ∀ (n : ℕ) (φ : Rn n → ℝ), ContDiff ℝ 1 φ → ∀ (r : ℝ) (z : Rn n), ∫⁻ x in ball (0 : Rn n) r, ‖φ (x - z) - φ x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖gradient φ x‖ₑ ^ 2 := by
  intro n φ hφ r z
  -- Step 0: `∇φ = toDual⁻¹ ∘ Dφ` is continuous, so the Tonelli integrand is Borel measurable.
  have hgc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hmeas : Measurable (fun p : Rn n × ℝ => ‖gradient φ (p.1 - p.2 • z)‖ₑ ^ 2) :=
    ((hgc.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).measurable.enorm).pow_const 2
  -- Steps 1–4: the segment bound at the pair `(x - z, x)`, whose segment is `t ↦ x - t z`.
  have hpt : ∀ x : Rn n, ‖φ (x - z) - φ x‖ₑ ^ 2 ≤
      ‖z‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ (x - t • z)‖ₑ ^ 2 := by
    intro x
    have e1 : x - z - x = -z := by abel
    have e2 : ∀ t : ℝ, (1 - t) • x + t • (x - z) = x - t • z := fun t => by module
    calc ‖φ (x - z) - φ x‖ₑ ^ 2
        ≤ ‖x - z - x‖ₑ ^ 2 *
            ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ ((1 - t) • x + t • (x - z))‖ₑ ^ 2 :=
          poincare_c1_segment_sq_bound n φ hφ (x - z) x
      _ = ‖z‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ (x - t • z)‖ₑ ^ 2 := by
          simp only [e1, e2, enorm_neg]
  -- Steps 5–8: integrate over `B̆_r(0)`, swap the integrals, translate by `t z`, and use
  -- `|[0, 1]| = 1` and `‖z‖ₑ² = ofReal ‖z‖²`.
  calc ∫⁻ x in ball (0 : Rn n) r, ‖φ (x - z) - φ x‖ₑ ^ 2
      ≤ ∫⁻ x in ball (0 : Rn n) r,
          ‖z‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ (x - t • z)‖ₑ ^ 2 :=
        lintegral_mono hpt
    _ = ‖z‖ₑ ^ 2 * ∫⁻ x in ball (0 : Rn n) r,
          ∫⁻ t in Icc (0 : ℝ) 1, ‖gradient φ (x - t • z)‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)
    _ = ‖z‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1,
          ∫⁻ x in ball (0 : Rn n) r, ‖gradient φ (x - t • z)‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ ≤ ‖z‖ₑ ^ 2 * ∫⁻ t in Icc (0 : ℝ) 1,
          ∫⁻ y in ball (0 : Rn n) (r + ‖z‖), ‖gradient φ y‖ₑ ^ 2 := by
        refine mul_le_mul_right (setLIntegral_mono measurable_const fun t ht => ?_) _
        refine lintegral_ball_comp_sub_le n (fun y => ‖gradient φ y‖ₑ ^ 2) r (r + ‖z‖) (t • z) ?_
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        have : t * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
        linarith
    _ = ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖gradient φ x‖ₑ ^ 2 := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
/-- **`L²` approximation preserves a quadratic energy bound** (Minkowski's inequality in `L²`; the
limit step `j → ∞` in the proof of the translation estimate, Evans §5.8.2 Thm 3(i),
Gilbarg–Trudinger §7.11).  If `aⱼ → a₀` in `L²(μ)`, `bⱼ → b₀` in `L²(ν)` and
`∫⁻ ‖aⱼ‖ₑ² dμ ≤ c ∫⁻ ‖bⱼ‖ₑ² dν` for every `j` with `c < ∞`, then `∫⁻ ‖a₀‖ₑ² dμ ≤ c ∫⁻ ‖b₀‖ₑ² dν`.

With `N = eLpNorm · 2` and `γ = c^{1/2}`, Minkowski gives
`N(a₀) ≤ N(a₀ - aⱼ) + γ (N(bⱼ - b₀) + N(b₀))` for every `j`; the error terms tend to `0`, so
`N(a₀) ≤ γ N(b₀)`, and squaring gives the claim (infinite integrals included). -/
theorem lintegral_sq_le_of_l2_approximation : ∀ {α E F : Type} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (μ ν : Measure α) (c : ℝ≥0∞) (a : ℕ → α → E) (a₀ : α → E) (b : ℕ → α → F) (b₀ : α → F), c ≠ ∞ → (∀ j, AEStronglyMeasurable (a j) μ) → AEStronglyMeasurable a₀ μ → (∀ j, AEStronglyMeasurable (b j) ν) → AEStronglyMeasurable b₀ ν → Tendsto (fun j => ∫⁻ x, ‖a j x - a₀ x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖b j x - b₀ x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) → (∀ j, ∫⁻ x, ‖a j x‖ₑ ^ 2 ∂μ ≤ c * ∫⁻ x, ‖b j x‖ₑ ^ 2 ∂ν) → ∫⁻ x, ‖a₀ x‖ₑ ^ 2 ∂μ ≤ c * ∫⁻ x, ‖b₀ x‖ₑ ^ 2 ∂ν := by
  intro α E F _ _ _ μ ν c a a₀ b b₀ hc ha ha₀ hb hb₀ hA hB hab
  -- Step 1: `N(u) = eLpNorm u 2 m` has `N(u) ^ 2 = ∫⁻ ‖u‖ₑ ^ 2 dm` and
  -- `N(u) = (∫⁻ ‖u‖ₑ ^ 2 dm) ^ (1/2)` (`eLpNorm` is `∞` off a.e.-strongly measurable functions).
  have hsq : ∀ {G : Type} [NormedAddCommGroup G] {m : Measure α} {u : α → G},
      AEStronglyMeasurable u m → eLpNorm u 2 m ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂m := by
    intro G _ m u hu
    simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hu
  have hroot : ∀ {G : Type} [NormedAddCommGroup G] {m : Measure α} {u : α → G},
      AEStronglyMeasurable u m → eLpNorm u 2 m = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂m) ^ (1 / 2 : ℝ) := by
    intro G _ m u hu
    rw [← hsq hu, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  -- Step 2: `γ = c ^ (1/2)` is finite and `γ ^ 2 = c`.
  obtain ⟨γ, hγ, hγ2⟩ : ∃ γ : ℝ≥0∞, γ ≠ ∞ ∧ γ ^ 2 = c := by
    refine ⟨c ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc, ?_⟩
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  -- Steps 3–7: for every `j`, `N(a₀) ≤ N(a₀ - aⱼ) + γ (N(bⱼ - b₀) + N(b₀))`.
  have hbound : ∀ j, eLpNorm a₀ 2 μ ≤
      eLpNorm (a₀ - a j) 2 μ + γ * (eLpNorm (b j - b₀) 2 ν + eLpNorm b₀ 2 ν) := by
    intro j
    have h4 : eLpNorm a₀ 2 μ ≤ eLpNorm (a₀ - a j) 2 μ + eLpNorm (a j) 2 μ := by
      simpa using eLpNorm_add_le (f := a₀ - a j) (g := a j) (μ := μ) one_le_two
    -- `N(aⱼ)² ≤ c N(bⱼ)² = (γ N(bⱼ))²`, and squaring is order-reflecting on `[0, ∞]`.
    have h5 : eLpNorm (a j) 2 μ ≤ γ * eLpNorm (b j) 2 ν := by
      rw [← ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
        mul_pow, hsq (ha j), hsq (hb j), hγ2]
      exact hab j
    have h6 : eLpNorm (b j) 2 ν ≤ eLpNorm (b j - b₀) 2 ν + eLpNorm b₀ 2 ν := by
      simpa using eLpNorm_add_le (f := b j - b₀) (g := b₀) (μ := ν) one_le_two
    calc eLpNorm a₀ 2 μ ≤ eLpNorm (a₀ - a j) 2 μ + eLpNorm (a j) 2 μ := h4
      _ ≤ eLpNorm (a₀ - a j) 2 μ + γ * eLpNorm (b j) 2 ν := by gcongr
      _ ≤ eLpNorm (a₀ - a j) 2 μ + γ * (eLpNorm (b j - b₀) 2 ν + eLpNorm b₀ 2 ν) := by gcongr
  -- Step 8: the error terms tend to `0`, since `t ↦ t ^ (1/2)` is continuous with `0 ^ (1/2) = 0`.
  have hroot0 : ∀ {f : ℕ → ℝ≥0∞}, Tendsto f atTop (𝓝 0) →
      Tendsto (fun j => f j ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    intro f hf
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using
      ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hf
  have hA' : Tendsto (fun j => eLpNorm (a₀ - a j) 2 μ) atTop (𝓝 0) :=
    (hroot0 hA).congr fun j =>
      ((eLpNorm_sub_comm a₀ (a j) 2 μ).trans (hroot ((ha j).sub ha₀))).symm
  have hB' : Tendsto (fun j => eLpNorm (b j - b₀) 2 ν) atTop (𝓝 0) :=
    (hroot0 hB).congr fun j => (hroot ((hb j).sub hb₀)).symm
  -- Step 9: pass to the limit (`γ < ∞`, so `t ↦ γ t` is continuous).
  have hlim : Tendsto (fun j => eLpNorm (a₀ - a j) 2 μ +
      γ * (eLpNorm (b j - b₀) 2 ν + eLpNorm b₀ 2 ν)) atTop (𝓝 (γ * eLpNorm b₀ 2 ν)) := by
    simpa using hA'.add (ENNReal.Tendsto.const_mul (hB'.add tendsto_const_nhds) (Or.inr hγ))
  have h9 : eLpNorm a₀ 2 μ ≤ γ * eLpNorm b₀ 2 ν := ge_of_tendsto' hlim hbound
  -- Step 10: square.
  calc ∫⁻ x, ‖a₀ x‖ₑ ^ 2 ∂μ = eLpNorm a₀ 2 μ ^ 2 := (hsq ha₀).symm
    _ ≤ (γ * eLpNorm b₀ 2 ν) ^ 2 := by gcongr
    _ = c * ∫⁻ x, ‖b₀ x‖ₑ ^ 2 ∂ν := by rw [mul_pow, hγ2, hsq hb₀]
/-- **Translates of a.e.-strongly measurable functions on balls.**  If `r + ‖z‖ ≤ s` and `h` is
a.e.-strongly measurable for Lebesgue measure on `B̆_s(0)`, then so is `x ↦ h(x - z)` on `B̆_r(0)`.

The translation `τ(x) = x - z` preserves Lebesgue measure, hence also maps Lebesgue measure on
`τ⁻¹(B̆_s(0))` to Lebesgue measure on `B̆_s(0)`; a.e.-strong measurability pulls back along such a
map, and `B̆_r(0) ⊆ τ⁻¹(B̆_s(0))` because `‖x - z‖ ≤ ‖x‖ + ‖z‖ < r + ‖z‖ ≤ s`. -/
theorem aestronglyMeasurable_ball_comp_sub : ∀ (n : ℕ) (h : Rn n → ℝ) (r s : ℝ) (z : Rn n), r + ‖z‖ ≤ s → AEStronglyMeasurable h (volume.restrict (ball (0 : Rn n) s)) → AEStronglyMeasurable (fun x => h (x - z)) (volume.restrict (ball (0 : Rn n) r)) := by
  intro n h r s z hrs hh
  -- Steps 1–2: `τ` is measure preserving, also from the restriction to `τ⁻¹(B̆_s(0))`
  -- to the restriction to `B̆_s(0)`.
  have hmp : MeasurePreserving (fun x : Rn n => x - z)
      (volume.restrict ((fun x : Rn n => x - z) ⁻¹' ball 0 s)) (volume.restrict (ball 0 s)) :=
    (measurePreserving_sub_right volume z).restrict_preimage measurableSet_ball
  -- Step 3: compose a strongly measurable representative of `h` with `τ`.
  have hcomp : AEStronglyMeasurable (fun x => h (x - z))
      (volume.restrict ((fun x : Rn n => x - z) ⁻¹' ball 0 s)) :=
    hh.comp_measurePreserving hmp
  -- Step 4: `B̆_r(0) ⊆ τ⁻¹(B̆_s(0))`.
  have hsub : ball (0 : Rn n) r ⊆ (fun x : Rn n => x - z) ⁻¹' ball 0 s := by
    intro x hx
    rw [mem_preimage, mem_ball_zero_iff]
    exact (norm_sub_le x z).trans_lt (by linarith [mem_ball_zero_iff.1 hx])
  -- Step 5: pass to the smaller measure.
  exact hcomp.mono_measure (Measure.restrict_mono hsub le_rfl)
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
/-- **Poincaré inequality on the unit ball** (Simon Ch. 5, fact (P) in the proof of Lemma 3.1,
p. 114; Gilbarg–Trudinger (7.45)).  If `n ≥ 1` and `f ∈ W^{1,2}(B)` has weak gradient `g`, where
`B = B̆₁(0)`, then `∫_B |f − λ|² ≤ 2^{n+2} ∫_B |g|²` with `λ = ⨍_B f`.  For `0 < r < 1`, smooth
approximation on `B_r` and the segment estimate give
`∫_{B_r}∫_{B_r} |f(x) − f(y)|² ≤ 2^{n+2} |B| ∫_{B_r} |g|²`.  Letting `r ↑ 1` and using
`∫_B |f − λ|² ≤ |B|⁻¹ ∫_B∫_B |f(x) − f(y)|²` then gives the claim. -/
theorem w12_ball_poincare_inequality : ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∫⁻ x in ball (0 : Rn n) 1, ‖f x - ⨍ y in ball (0 : Rn n) 1, f y‖ₑ ^ 2 ≤ ENNReal.ofReal C * ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 := by
  intro n hn
  refine ⟨2 ^ (n + 2), by positivity, fun f g hfg => ?_⟩
  have hf : MemLp f 2 (volume.restrict (ball (0 : Rn n) 1)) := hfg.1
  have hg : MemLp g 2 (volume.restrict (ball (0 : Rn n) 1)) := hfg.2.1
  -- Steps 1–2: for `0 < r < 1`, approximate `f` on `B_r` by smooth `φ_j` and pass to the limit;
  -- the energy on `B_r` is at most the energy on `B`.
  have hBr : ∀ r : ℝ, 0 < r → r < 1 →
      ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2 ≤
        (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) *
          ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 := by
    intro r hr0 hr1
    obtain ⟨φ, hφ, h1, h2⟩ := Submission.w12_ball_smooth_approximation n hn f g hfg r hr0 hr1
    have hsub : ball (0 : Rn n) r ⊆ ball 0 1 := ball_subset_ball hr1.le
    calc ∫⁻ x in ball (0 : Rn n) r, ∫⁻ y in ball (0 : Rn n) r, ‖f x - f y‖ₑ ^ 2
        ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) *
            ∫⁻ x in ball (0 : Rn n) r, ‖g x‖ₑ ^ 2 :=
          Submission.poincare_approx_ball_double_integral_bound n f g φ r hr0 hr1.le
            (hf.aestronglyMeasurable.mono_set hsub) (hg.aestronglyMeasurable.mono_set hsub)
            (fun j => (hφ j).of_le (by exact_mod_cast le_top)) h1 h2
      _ ≤ (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) *
            ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 := by
          gcongr
  -- Step 3: let `r ↑ 1`.
  have hB := Submission.poincare_ball_double_integral_exhaustion n f _ hf.aestronglyMeasurable hBr
  -- Step 4: the mean.  Since `0 < |B| < ∞`, `|B|⁻¹ · 2^{n+2} |B| = 2^{n+2}`.
  have h0 : volume (ball (0 : Rn n) 1) ≠ 0 := (measure_ball_pos volume (0 : Rn n) one_pos).ne'
  have htop : volume (ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ x in ball (0 : Rn n) 1, ‖f x - ⨍ y in ball (0 : Rn n) 1, f y‖ₑ ^ 2
      ≤ (volume (ball (0 : Rn n) 1))⁻¹ *
          ∫⁻ x in ball (0 : Rn n) 1, ∫⁻ y in ball (0 : Rn n) 1, ‖f x - f y‖ₑ ^ 2 :=
        Submission.poincare_set_mean_deviation_sq_bound n _ f measurableSet_ball htop hf
    _ ≤ (volume (ball (0 : Rn n) 1))⁻¹ * ((2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Rn n) 1) *
          ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (n + 2)) * ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 := by
        rw [mul_comm ((2 : ℝ≥0∞) ^ (n + 2)), ← mul_assoc, ← mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, one_mul, ENNReal.ofReal_pow zero_le_two,
          ENNReal.ofReal_ofNat]
/-- **Boundary-layer `L²` estimate for `W^{1,2}(B)`**, `B = B̆₁(0)` (a trace-type estimate along
rays from the origin; the boundary control of Rellich's theorem, cf. Evans §5.7,
Gilbarg–Trudinger §7.10): if `f ∈ W^{1,2}(B)` has weak gradient `g` and `0 < r < 1`, then
`∫_{B \ B̆_r(0)} |f|² ≤ 2^{n+3} √(1 − r) (∫_B |f|² + ∫_B |g|²)`.

For `r < 1/2` the constant is at least `1`.  For `r ≥ 1/2` and `0 < s < 1`, smooth `φ_j` with
`φ_j → f` and `∇φ_j → g` in `L²(B̆_s(0))` satisfy the annulus estimate on `B̆_s \ B̆_{rs}`; their
squared `L²` norms converge, so the estimate passes to `f`.  Finally `B̆_s \ B̆_r ⊆ B̆_s \ B̆_{rs}`,
and the sets `B̆_s \ B̆_r` increase to `B \ B̆_r` as `s ↑ 1`. -/
theorem w12_ball_boundary_layer_estimate : ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ r : ℝ, 0 < r → r < 1 → ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖f x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * Real.sqrt (1 - r)) * ((∫⁻ x in ball (0 : Rn n) 1, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2) := by
  intro n hn
  refine ⟨2 ^ (n + 3), by positivity, ?_⟩
  intro f g hW r hr0 hr1
  have hf2 : MemLp f 2 (volume.restrict (ball (0 : Rn n) 1)) := hW.1
  have hg2 : MemLp g 2 (volume.restrict (ball (0 : Rn n) 1)) := hW.2.1
  rcases lt_or_ge r (1 / 2) with hr | hr
  · -- Step 1: for `r < 1/2`, `√(1 − r) ≥ 1/2` and `2^{n+3} ≥ 8`, so the constant is `≥ 1`.
    have h1 : (1 / 2 : ℝ) ≤ Real.sqrt (1 - r) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      linarith
    have h2 : (8 : ℝ) ≤ 2 ^ (n + 3) :=
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hK : 1 ≤ ENNReal.ofReal (2 ^ (n + 3) * Real.sqrt (1 - r)) := by
      rw [ENNReal.one_le_ofReal]
      linarith [mul_le_mul h2 h1 (by norm_num) (by positivity)]
    calc ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖f x‖ₑ ^ 2
        ≤ ∫⁻ x in ball (0 : Rn n) 1, ‖f x‖ₑ ^ 2 := lintegral_mono_set sdiff_subset
      _ ≤ (∫⁻ x in ball (0 : Rn n) 1, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 :=
        le_self_add
      _ ≤ _ := le_mul_of_one_le_left zero_le hK
  -- Step 3: for `0 < s < 1`, the annulus estimate for the smooth approximants on `B̆_s(0)`
  -- passes to `f` in the limit.
  have hannulus : ∀ s : ℝ, 0 < s → s < 1 →
      ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖f x‖ₑ ^ 2 ≤
        ENNReal.ofReal (2 ^ (n + 3) * Real.sqrt (1 - r)) *
          ((∫⁻ x in ball (0 : Rn n) 1, ‖f x‖ₑ ^ 2) + ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2) := by
    intro s hs0 hs1
    obtain ⟨φ, hφ, hφf, hφg⟩ := Submission.w12_ball_smooth_approximation n hn f g hW s hs0 hs1
    have hB : ball (0 : Rn n) s ⊆ ball 0 1 := ball_subset_ball hs1.le
    have hA : ball (0 : Rn n) s \ ball 0 (r * s) ⊆ ball 0 s := sdiff_subset
    -- The approximants are `C¹`; they and their gradients are continuous.
    have hφ1 : ∀ j, ContDiff ℝ 1 (φ j) := fun j => (hφ j).of_le (by exact_mod_cast le_top)
    have hφc : ∀ j, Continuous (φ j) := fun j => (hφ j).continuous
    have hgc : ∀ j, Continuous (gradient (φ j)) := fun j =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp
        ((hφ1 j).continuous_fderiv one_ne_zero)
    -- Convergence of the squared `L²` norms on `B̆_s \ B̆_{rs}` and on `B̆_s`.
    have hlimA : Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖φ j x‖ₑ ^ 2)
        atTop (𝓝 (∫⁻ x in ball (0 : Rn n) s \ ball 0 (r * s), ‖f x‖ₑ ^ 2)) :=
      Submission.ble_lintegral_sq_tendsto_of_l2_tendsto _ f φ
        (hf2.mono_measure (Measure.restrict_mono (hA.trans hB) le_rfl))
        (fun j => (hφc j).aestronglyMeasurable)
        (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφf
          (fun _ => zero_le) (fun _ => lintegral_mono_set hA))
    have hlimf : Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) s, ‖φ j x‖ₑ ^ 2)
        atTop (𝓝 (∫⁻ x in ball (0 : Rn n) s, ‖f x‖ₑ ^ 2)) :=
      Submission.ble_lintegral_sq_tendsto_of_l2_tendsto _ f φ
        (hf2.mono_measure (Measure.restrict_mono hB le_rfl))
        (fun j => (hφc j).aestronglyMeasurable) hφf
    have hlimg : Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) s, ‖gradient (φ j) x‖ₑ ^ 2)
        atTop (𝓝 (∫⁻ x in ball (0 : Rn n) s, ‖g x‖ₑ ^ 2)) :=
      Submission.ble_lintegral_sq_tendsto_of_l2_tendsto _ g (fun j => gradient (φ j))
        (hg2.mono_measure (Measure.restrict_mono hB le_rfl))
        (fun j => (hgc j).aestronglyMeasurable) hφg
    -- Step 2 (the smooth annulus estimate) for each `φ_j`, and the limit `j → ∞`.
    have hlim := le_of_tendsto_of_tendsto' hlimA
      (ENNReal.Tendsto.const_mul (hlimf.add hlimg) (Or.inr ENNReal.ofReal_ne_top))
      fun j => Submission.ble_smooth_annulus_estimate n hn (φ j) (hφ1 j) r s hr hr1 hs0 hs1.le
    -- Enlarge `B̆_s(0)` to `B`.
    refine hlim.trans ?_
    gcongr
  -- Step 4: `B̆_s \ B̆_r ⊆ B̆_s \ B̆_{rs}`, and `B̆_s \ B̆_r` increases to `B \ B̆_r` along radii
  -- `s_m ↑ 1`.
  obtain ⟨s, hs_mono, hs_mem, hs_lim⟩ := exists_seq_strictMono_tendsto' (zero_lt_one' ℝ)
  have hU : ball (0 : Rn n) 1 \ ball 0 r = ⋃ m, ball (0 : Rn n) (s m) \ ball 0 r := by
    rw [← iUnion_sdiff]
    congr 1
    ext x
    simp only [mem_ball, dist_zero_right, mem_iUnion]
    exact ⟨fun hx => (hs_lim.eventually (lt_mem_nhds hx)).exists,
      fun ⟨m, hm⟩ => hm.trans (hs_mem m).2⟩
  have hd : Directed (· ⊆ ·) fun m => ball (0 : Rn n) (s m) \ ball 0 r :=
    Monotone.directed_le fun i j hij =>
      sdiff_subset_sdiff_left (ball_subset_ball (hs_mono.monotone hij))
  rw [hU, setLIntegral_iUnion_of_directed _ hd]
  refine iSup_le fun m => ?_
  have hsub : ball (0 : Rn n) (s m) \ ball 0 r ⊆ ball 0 (s m) \ ball 0 (r * s m) :=
    sdiff_subset_sdiff_right (ball_subset_ball (mul_le_of_le_one_right hr0.le (hs_mem m).2.le))
  exact (lintegral_mono_set hsub).trans (hannulus (s m) (hs_mem m).1 (hs_mem m).2)
/-- Translation (difference-quotient) estimate for `W^{1,2}(B)` (Evans, *PDE*, §5.8.2, Theorem 3(i);
Gilbarg–Trudinger §7.11), used for Rellich compactness in the proof of Simon Ch. 5, Lemma 3.1
(p. 114): if `0 < r` and `‖z‖ < 1 - r`, then `∫_{B_r} |f(x - z) - f(x)|² ≤ |z|² ∫_B |g|²`.
With `s = r + ‖z‖ ∈ (0, 1)`, take smooth `φ_j` with `φ_j → f` and `∇φ_j → g` in `L²(B_s)`.  The
`C¹` estimate gives `∫_{B_r} |φ_j(x - z) - φ_j(x)|² ≤ |z|² ∫_{B_s} |∇φ_j|²`; the translation
differences of `φ_j` converge to those of `f` in `L²(B_r)`, with error at most
`4 ∫_{B_s} |φ_j - f|²`, so the estimate passes to the limit, and `B_s ⊆ B`. -/
theorem w12_ball_translation_estimate : ∀ n : ℕ, 1 ≤ n → ∀ (f : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient f g (ball 0 1) → ∀ (r : ℝ) (z : Rn n), 0 < r → ‖z‖ < 1 - r → ∫⁻ x in ball (0 : Rn n) r, ‖f (x - z) - f x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 := by
  intro n hn f g hfg r z hr hz
  -- Step 0: `B_r ⊆ B_s ⊆ B` for `s = r + ‖z‖ ∈ (0, 1)`; `f`, `g`, `f(· - z)` are measurable there.
  have hs0 : 0 < r + ‖z‖ := add_pos_of_pos_of_nonneg hr (norm_nonneg z)
  have hs1 : r + ‖z‖ < 1 := by linarith
  have hBs : ball (0 : Rn n) (r + ‖z‖) ⊆ ball 0 1 := ball_subset_ball hs1.le
  have hBr : ball (0 : Rn n) r ⊆ ball 0 (r + ‖z‖) :=
    ball_subset_ball (le_add_of_nonneg_right (norm_nonneg z))
  have hfs : AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) (r + ‖z‖))) :=
    hfg.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono hBs le_rfl)
  have hgs : AEStronglyMeasurable g (volume.restrict (ball (0 : Rn n) (r + ‖z‖))) :=
    hfg.2.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono hBs le_rfl)
  have hfr : AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) r)) :=
    hfs.mono_measure (Measure.restrict_mono hBr le_rfl)
  have hfzr : AEStronglyMeasurable (fun x => f (x - z)) (volume.restrict (ball (0 : Rn n) r)) :=
    Submission.aestronglyMeasurable_ball_comp_sub n f r (r + ‖z‖) z le_rfl hfs
  -- Step 1: smooth `φ_j` with `φ_j → f` and `∇φ_j → g` in `L²(B_s)`.
  obtain ⟨φ, hφ, hφf, hφg⟩ :=
    Submission.w12_ball_smooth_approximation n hn f g hfg (r + ‖z‖) hs0 hs1
  have hφ1 : ∀ j, ContDiff ℝ 1 (φ j) := fun j => (hφ j).of_le (by exact_mod_cast le_top)
  have hφc : ∀ j, Continuous (φ j) := fun j => (hφ j).continuous
  have hgradc : ∀ j, Continuous (gradient (φ j)) := fun j =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp
      ((hφ1 j).continuous_fderiv one_ne_zero)
  -- Step 2: the `C¹` estimate for each `φ_j`.
  have hsmooth : ∀ j, ∫⁻ x in ball (0 : Rn n) r, ‖φ j (x - z) - φ j x‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖gradient (φ j) x‖ₑ ^ 2 :=
    fun j => Submission.contDiff_one_ball_translation_estimate n (φ j) (hφ1 j) r z
  -- Step 3: the translation differences of `φ_j` converge to those of `f` in `L²(B_r)`.
  have hdiff : ∀ j, ∫⁻ x in ball (0 : Rn n) r,
      ‖(φ j (x - z) - φ j x) - (f (x - z) - f x)‖ₑ ^ 2 ≤
        4 * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖φ j x - f x‖ₑ ^ 2 := by
    intro j
    calc ∫⁻ x in ball (0 : Rn n) r, ‖(φ j (x - z) - φ j x) - (f (x - z) - f x)‖ₑ ^ 2
        = ∫⁻ x in ball (0 : Rn n) r, ‖(φ j (x - z) - f (x - z)) - (φ j x - f x)‖ₑ ^ 2 :=
          lintegral_congr fun x => by rw [sub_sub_sub_comm]
      _ ≤ 4 * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖φ j x - f x‖ₑ ^ 2 :=
          Submission.lintegral_ball_translation_difference_le n (fun x => φ j x - f x) r
            (r + ‖z‖) z le_rfl ((hφc j).aestronglyMeasurable.sub hfs)
  have hconv : Tendsto (fun j => ∫⁻ x in ball (0 : Rn n) r,
      ‖(φ j (x - z) - φ j x) - (f (x - z) - f x)‖ₑ ^ 2) atTop (𝓝 0) := by
    have h4 := ENNReal.Tendsto.const_mul (a := 4) hφf (Or.inr (by norm_num))
    rw [mul_zero] at h4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun _ => zero_le) hdiff
  -- Step 4: pass to the limit in `L²(B_r)` and `L²(B_s)`, then enlarge `B_s` to `B`.
  calc ∫⁻ x in ball (0 : Rn n) r, ‖f (x - z) - f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) (r + ‖z‖), ‖g x‖ₑ ^ 2 :=
        Submission.lintegral_sq_le_of_l2_approximation (volume.restrict (ball (0 : Rn n) r))
          (volume.restrict (ball (0 : Rn n) (r + ‖z‖))) (ENNReal.ofReal (‖z‖ ^ 2))
          (fun j x => φ j (x - z) - φ j x) (fun x => f (x - z) - f x)
          (fun j => gradient (φ j)) g ENNReal.ofReal_ne_top
          (fun j => (((hφc j).comp (continuous_sub_right z)).sub (hφc j)).aestronglyMeasurable)
          (hfzr.sub hfr) (fun j => (hgradc j).aestronglyMeasurable) hgs hconv hφg hsmooth
    _ ≤ ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 :=
        mul_le_mul_right (lintegral_mono_set hBs) _
/-- **Rellich compactness on the unit ball** (Simon Ch. 5, fact (R) in the proof of Lemma 3.1;
Gilbarg–Trudinger, Thm. 7.26).  If `f k ∈ W^{1,2}(B̆₁(0))` with weak gradients `g k` and
`∫_B |f k|² ≤ A`, `∫_B |g k|² ≤ A` for all `k`, then a subsequence `f (φ k)` converges in
`L²(B̆₁(0))` to some `w ∈ L²(B̆₁(0))`.

Proof (parent-supplied natural proof, steps 0–6): pass to measurable representatives; mollify at
the scales `ε_m = 1/(m+2)` with the normalized tent kernel `max (ε - ‖z‖) 0 / I`.  By
`w12_ball_translation_estimate` the interior mollification error on `B̆_r(0)` is `≤ ε² A`.  For
fixed `m` the mollified functions are uniformly bounded and equi-Lipschitz, so a finite `δ`-net of
`B₁(0)` and Bolzano–Weierstrass in `ℝ^net` give, for every tolerance, a subsequence that is
uniformly Cauchy up to that tolerance; a diagonal argument over all pairs (scale, tolerance) gives
one subsequence `φ`.  `w12_ball_boundary_layer_estimate` controls the annulus
`B̆₁(0) \ B̆_r(0)`, so `f (φ k)` is Cauchy in `L²(B̆₁(0))`, and completeness of `L²` gives `w`. -/
theorem w12_ball_rellich_compactness : ∀ n : ℕ, 1 ≤ n → ∀ (A : ℝ) (f : ℕ → Rn n → ℝ) (g : ℕ → Rn n → Rn n), (∀ k, IsW12WithGradient (f k) (g k) (ball 0 1)) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖f k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖g k x‖ₑ ^ 2 ≤ ENNReal.ofReal A) → ∃ (φ : ℕ → ℕ) (w : Rn n → ℝ), StrictMono φ ∧ MemLp w 2 (volume.restrict (ball (0 : Rn n) 1)) ∧ Tendsto (fun k => ∫⁻ x in ball (0 : Rn n) 1, ‖f (φ k) x - w x‖ₑ ^ 2) atTop (𝓝 0) := by
  intro n hn
  -- Step 1 (and 3): a normalized tent kernel `ρ` supported in `B_ε(0)`, and uniform sup and
  -- Lipschitz bounds for `x ↦ ∫_B ρ (x - y) u y` in terms of `∫_B |u|²`.
  have hmol : ∀ ε : ℝ, 0 < ε → ∃ (ρ : Rn n → ℝ) (C : ℝ), Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      (∀ z, ε < ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 ∧ ∀ (a : ℝ) (u : Rn n → ℝ),
      MemLp u 2 (volume.restrict (ball (0 : Rn n) 1)) →
      ∫⁻ y in ball (0 : Rn n) 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal a → ∀ x x' : Rn n,
      |∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y| ≤ C * Real.sqrt a ∧
      |(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - ∫ y in ball (0 : Rn n) 1, ρ (x' - y) * u y| ≤
        C * Real.sqrt a * ‖x - x'‖ := by
    intro ε hε
    -- the tent `τ z = max (ε - ‖z‖) 0` and its integral `I > 0`
    let τ : Rn n → ℝ := fun z => max (ε - ‖z‖) 0
    have hτc : Continuous τ := (continuous_const.sub continuous_norm).max continuous_const
    have hτnn : ∀ z, 0 ≤ τ z := fun z => le_max_right _ _
    have hτ0 : ∀ z, ε < ‖z‖ → τ z = 0 := fun z hz => max_eq_right (by linarith)
    have hτint : Integrable τ := hτc.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall 0 ε) fun z hz =>
        hτ0 z (by rwa [mem_closedBall_zero_iff, not_le] at hz))
    have hIpos : 0 < ∫ z, τ z := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hτnn z) hτint]
      refine lt_of_lt_of_le (measure_ball_pos volume (0 : Rn n) hε) (measure_mono fun z hz => ?_)
      rw [mem_ball_zero_iff] at hz
      exact (lt_max_of_lt_left (sub_pos.mpr hz)).ne'
    set I : ℝ := ∫ z, τ z with hI
    let ρ : Rn n → ℝ := fun z => τ z / I
    have hρc : Continuous ρ := hτc.div_const I
    have hM : ∀ z, |ρ z| ≤ ε / I := fun z => by
      show |τ z / I| ≤ ε / I
      rw [abs_of_nonneg (div_nonneg (hτnn z) hIpos.le)]
      exact div_le_div_of_nonneg_right (max_le (by linarith [norm_nonneg z]) hε.le) hIpos.le
    have hL : ∀ p q, |ρ p - ρ q| ≤ 1 / I * ‖p - q‖ := fun p q => by
      show |τ p / I - τ q / I| ≤ 1 / I * ‖p - q‖
      have h1 : |τ p - τ q| ≤ ‖p - q‖ := (abs_max_sub_max_le_abs _ _ _).trans (by
        rw [show ε - ‖p‖ - (ε - ‖q‖) = ‖q‖ - ‖p‖ by ring, abs_sub_comm]
        exact abs_norm_sub_norm_le p q)
      rw [← sub_div, abs_div, abs_of_pos hIpos, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right h1 hIpos.le
    set B : Set (Rn n) := ball (0 : Rn n) 1 with hB
    set V : ℝ := (volume B).toReal with hV
    have hBfin : volume B ≠ ⊤ := measure_ball_lt_top.ne
    have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin
    -- L¹ bound via Hölder (eLpNorm comparison)
    have hL1 : ∀ (a : ℝ) (u : Rn n → ℝ), MemLp u 2 (volume.restrict B) →
        ∫⁻ y in B, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal a →
        ∫ y in B, |u y| ≤ Real.sqrt V * Real.sqrt a := by
      intro a u hu ha
      have hum : AEStronglyMeasurable u (volume.restrict B) := hu.aestronglyMeasurable
      have key1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
        (μ := volume.restrict B) (by norm_num) hum
      rw [eLpNorm_one_eq_lintegral_enorm hum,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hum,
        Measure.restrict_apply_univ] at key1
      have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
      simp only [h2, ENNReal.toReal_one, ENNReal.rpow_two] at key1
      have key2 : ∫⁻ y in B, ‖u y‖ₑ ≤
          ENNReal.ofReal a ^ (1 / 2 : ℝ) * volume B ^ (1 / 2 : ℝ) := by
        refine key1.trans ?_
        have e : (1 / 1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
        rw [e]
        gcongr
      have hT : ∫ y in B, |u y| = (∫⁻ y in B, ‖u y‖ₑ).toReal := by
        simp_rw [← Real.norm_eq_abs]
        exact integral_norm_eq_lintegral_enorm hum
      rw [hT]
      have hfin : ENNReal.ofReal a ^ (1 / 2 : ℝ) * volume B ^ (1 / 2 : ℝ) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin
      refine (ENNReal.toReal_mono hfin key2).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← hV, mul_comm]
      congr 1
      rcases le_total 0 a with h | h
      · rw [ENNReal.toReal_ofReal h]
      · rw [ENNReal.ofReal_of_nonpos h, Real.sqrt_eq_zero_of_nonpos h]
        simp
    have hML : 0 ≤ max (ε / I) (1 / I) := le_max_of_le_right (by positivity)
    refine ⟨ρ, max (ε / I) (1 / I) * Real.sqrt V, hρc, fun z => div_nonneg (hτnn z) hIpos.le,
      fun z hz => by simp only [ρ, hτ0 z hz, zero_div], ?_, ?_⟩
    · show ∫ z, τ z / I = 1
      rw [integral_div, div_self hIpos.ne']
    intro a u hu ha x x'
    have hui : Integrable u (volume.restrict B) := hu.integrable (by norm_num)
    have hT := hL1 a u hu ha
    have hTnn : 0 ≤ ∫ y in B, |u y| := integral_nonneg (fun _ => abs_nonneg _)
    have hcomp : ∀ x0 : Rn n, Continuous (fun y => ρ (x0 - y)) :=
      fun x0 => hρc.comp (continuous_const.sub continuous_id)
    have hint : ∀ x0 : Rn n, Integrable (fun y => ρ (x0 - y) * u y) (volume.restrict B) :=
      fun x0 => hui.bdd_mul (c := ε / I) (hcomp x0).aestronglyMeasurable
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM (x0 - y))
    have hbound : ∀ K : ℝ, ∫ y in B, K * |u y| = K * ∫ y in B, |u y| :=
      fun K => integral_const_mul K _
    constructor
    · have h1 : ‖∫ y in B, ρ (x - y) * u y‖ ≤ ∫ y in B, ε / I * |u y| :=
        norm_integral_le_of_norm_le (hui.abs.const_mul (ε / I)) (Eventually.of_forall fun y => by
          rw [norm_mul, Real.norm_eq_abs (u y), Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hM (x - y)) (abs_nonneg _))
      rw [hbound, Real.norm_eq_abs] at h1
      calc |∫ y in B, ρ (x - y) * u y| ≤ ε / I * ∫ y in B, |u y| := h1
        _ ≤ max (ε / I) (1 / I) * ∫ y in B, |u y| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hTnn
        _ ≤ max (ε / I) (1 / I) * (Real.sqrt V * Real.sqrt a) := mul_le_mul_of_nonneg_left hT hML
        _ = max (ε / I) (1 / I) * Real.sqrt V * Real.sqrt a := by ring
    · rw [← integral_sub (hint x) (hint x')]
      have h1 : ‖∫ y in B, (ρ (x - y) * u y - ρ (x' - y) * u y)‖ ≤
          ∫ y in B, (1 / I * ‖x - x'‖) * |u y| :=
        norm_integral_le_of_norm_le (hui.abs.const_mul _) (Eventually.of_forall fun y => by
          rw [← sub_mul, norm_mul, Real.norm_eq_abs (u y), Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := hL (x - y) (x' - y)
          rwa [sub_sub_sub_cancel_right] at this)
      rw [hbound, Real.norm_eq_abs] at h1
      have hxx : 0 ≤ ‖x - x'‖ := norm_nonneg _
      calc |∫ y in B, (ρ (x - y) * u y - ρ (x' - y) * u y)|
          ≤ 1 / I * ‖x - x'‖ * ∫ y in B, |u y| := h1
        _ ≤ max (ε / I) (1 / I) * ‖x - x'‖ * ∫ y in B, |u y| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hxx) hTnn
        _ ≤ max (ε / I) (1 / I) * ‖x - x'‖ * (Real.sqrt V * Real.sqrt a) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg hML hxx)
        _ = max (ε / I) (1 / I) * Real.sqrt V * Real.sqrt a * ‖x - x'‖ := by ring
  -- Step 2: the interior mollification error, by Jensen for the probability density `ρ`,
  -- Tonelli, and a translation estimate.
  have hmolerr : ∀ (ρ u : Rn n → ℝ) (ε r : ℝ) (E : ℝ≥0∞), Continuous ρ → (∀ z, 0 ≤ ρ z) →
      (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → Measurable u → 0 < r → ε < 1 - r →
      (∀ z : Rn n, ‖z‖ < 1 - r →
        ∫⁻ x in ball (0 : Rn n) r, ‖u (x - z) - u x‖ₑ ^ 2 ≤ ENNReal.ofReal (‖z‖ ^ 2) * E) →
      ∫⁻ x in ball (0 : Rn n) r, ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2 ≤
        ENNReal.ofReal (ε ^ 2) * E := by
    clear hmol
    intro ρ u ε r E hρc hρ0 hρsupp hρ1 hu hr hεr htrans
    -- preliminaries on ρ
    have hρint : Integrable ρ := by
      by_contra h
      rw [integral_undef h] at hρ1
      exact zero_ne_one hρ1
    have hρlint : ∫⁻ z, ENNReal.ofReal (ρ z) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hρint (Filter.Eventually.of_forall hρ0), hρ1,
        ENNReal.ofReal_one]
    have hsupp : ∀ z, ρ z ≠ 0 → ‖z‖ ≤ ε := by
      intro z hz
      by_contra h
      exact hz (hρsupp z (lt_of_not_ge h))
    have hρm : Measurable fun z => ENNReal.ofReal (ρ z) := hρc.measurable.ennreal_ofReal
    -- change of variables `y = x - z`
    have hconv : ∀ x ∈ ball (0 : Rn n) r,
        (∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) = ∫ z, ρ z * u (x - z) := by
      intro x hx
      rw [← integral_indicator measurableSet_ball,
        ← integral_sub_left_eq_self ((ball (0 : Rn n) 1).indicator (fun y => ρ (x - y) * u y))
          (volume : Measure (Rn n)) x]
      congr 1
      ext z
      by_cases hz : ρ z = 0
      · rw [hz, zero_mul]
        by_cases hm : x - z ∈ ball (0 : Rn n) 1
        · rw [indicator_of_mem hm, sub_sub_cancel, hz, zero_mul]
        · rw [indicator_of_notMem hm]
      · have hzε := hsupp z hz
        have hm : x - z ∈ ball (0 : Rn n) 1 := by
          rw [mem_ball_zero_iff] at hx ⊢
          calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le x z
            _ < r + (1 - r) := by linarith
            _ = 1 := by ring
        rw [indicator_of_mem hm, sub_sub_cancel]
    -- pointwise Cauchy–Schwarz
    have hpt : ∀ x ∈ ball (0 : Rn n) r,
        ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2 ≤
          ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 := by
      intro x hx
      rw [hconv x hx]
      set J := ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 with hJdef
      by_cases hJ : J = ⊤
      · rw [hJ]; exact le_top
      have hDm : Measurable fun z => u (x - z) - u x :=
        (hu.comp (measurable_const.sub measurable_id)).sub measurable_const
      have hHol : ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ≤ J ^ (1 / 2 : ℝ) := by
        have := ENNReal.lintegral_mul_norm_pow_le (μ := volume)
          (f := fun z => ENNReal.ofReal (ρ z))
          (g := fun z => ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2)
          hρm.aemeasurable (hρm.mul (hDm.enorm.pow_const 2)).aemeasurable
          (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
        rw [hρlint, ENNReal.one_rpow, one_mul] at this
        refine le_trans (le_of_eq ?_) this
        congr 1
        ext z
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num
      have hfin : ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ < ⊤ :=
        lt_of_le_of_lt hHol (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ)
      have hnorm : ∀ z, ‖ρ z * (u (x - z) - u x)‖ₑ =
          ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ := by
        intro z
        rw [enorm_mul, Real.enorm_of_nonneg (hρ0 z)]
      have hint : Integrable (fun z => ρ z * (u (x - z) - u x)) := by
        refine ⟨(hρc.measurable.mul hDm).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simp_rw [hnorm]
        exact hfin
      have hint2 : Integrable (fun z => ρ z * u (x - z)) := by
        refine (hint.add (hρint.mul_const (u x))).congr (Filter.Eventually.of_forall fun z => ?_)
        simp only [Pi.add_apply]
        ring
      have heq : (∫ z, ρ z * u (x - z)) - u x = ∫ z, ρ z * (u (x - z) - u x) := by
        have h1 : ∫ z, ρ z * u x = u x := by rw [integral_mul_const, hρ1, one_mul]
        simp_rw [mul_sub]
        rw [integral_sub hint2 (hρint.mul_const (u x)), h1]
      rw [heq]
      calc ‖∫ z, ρ z * (u (x - z) - u x)‖ₑ ^ 2
          ≤ (∫⁻ z, ‖ρ z * (u (x - z) - u x)‖ₑ) ^ 2 := by
            gcongr
            exact enorm_integral_le_lintegral_enorm _
        _ = (∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ) ^ 2 := by simp_rw [hnorm]
        _ ≤ (J ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
        _ = J := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            norm_num
    -- integrate over `B̆_r(0)` and use Tonelli
    have hjm : Measurable (Function.uncurry fun (x z : Rn n) =>
        ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2) := by
      have h1 : Measurable fun p : Rn n × Rn n => ENNReal.ofReal (ρ p.2) :=
        (hρc.measurable.comp measurable_snd).ennreal_ofReal
      have h2 : Measurable fun p : Rn n × Rn n => ‖u (p.1 - p.2) - u p.1‖ₑ ^ 2 :=
        ((hu.comp (measurable_fst.sub measurable_snd)).sub (hu.comp measurable_fst)).enorm.pow_const 2
      exact h1.mul h2
    calc ∫⁻ x in ball (0 : Rn n) r, ‖(∫ y in ball (0 : Rn n) 1, ρ (x - y) * u y) - u x‖ₑ ^ 2
        ≤ ∫⁻ x in ball (0 : Rn n) r, ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ∫⁻ z, ∫⁻ x in ball (0 : Rn n) r, ENNReal.ofReal (ρ z) * ‖u (x - z) - u x‖ₑ ^ 2 :=
          lintegral_lintegral_swap hjm.aemeasurable
      _ = ∫⁻ z, ENNReal.ofReal (ρ z) * ∫⁻ x in ball (0 : Rn n) r, ‖u (x - z) - u x‖ₑ ^ 2 := by
          congr 1
          ext z
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∫⁻ z, ENNReal.ofReal (ρ z) * (ENNReal.ofReal (ε ^ 2) * E) := by
          apply lintegral_mono
          intro z
          dsimp only
          by_cases hz : ρ z = 0
          · rw [hz, ENNReal.ofReal_zero, zero_mul, zero_mul]
          · have hzε := hsupp z hz
            gcongr
            calc _ ≤ ENNReal.ofReal (‖z‖ ^ 2) * E := htrans z (by linarith)
              _ ≤ _ := by gcongr
      _ = (∫⁻ z, ENNReal.ofReal (ρ z)) * (ENNReal.ofReal (ε ^ 2) * E) :=
          lintegral_mul_const _ hρm
      _ = ENNReal.ofReal (ε ^ 2) * E := by rw [hρlint, one_mul]
  -- Step 4a: for uniformly bounded, equi-Lipschitz functions on a compact set `K` and a tolerance
  -- `η > 0`, every subsequence has a further subsequence that is eventually `η`-close uniformly
  -- on `K` (a finite `δ`-net of `K` and Bolzano–Weierstrass in `ℝ^net`).
  have hAA : ∀ (K : Set (Rn n)) (h : ℕ → Rn n → ℝ) (M L : ℝ), IsCompact K →
      (∀ k, ∀ x ∈ K, |h k x| ≤ M) → (∀ k, ∀ x ∈ K, ∀ y ∈ K, |h k x - h k y| ≤ L * dist x y) →
      ∀ η : ℝ, 0 < η → ∀ ψ : ℕ → ℕ, ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∀ x ∈ K, |h (ψ (σ k)) x - h (ψ (σ l)) x| ≤ η := by
    clear hmol hmolerr
    intro K h M L hK hM hL η hη ψ
    set L' : ℝ := max L 0 with hL'
    have hL'0 : 0 ≤ L' := le_max_right _ _
    set δ : ℝ := η / (3 * (L' + 1)) with hδ
    have hδ0 : 0 < δ := by positivity
    have hδη : 3 * (L' + 1) * δ = η := by
      rw [hδ, mul_comm]
      exact div_mul_cancel₀ η (by positivity)
    obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK hδ0
    have : Fintype t := htfin.fintype
    let v : ℕ → (t → ℝ) := fun k y => h (ψ k) y
    have hvmem : ∀ k, v k ∈ Set.pi univ fun _ : t => Icc (-M) M := fun k y _ =>
      abs_le.mp (hM (ψ k) y (htK y.2))
    obtain ⟨a, -, σ, hσ, hlim⟩ :=
      (isCompact_univ_pi fun _ : t => isCompact_Icc (a := -M) (b := M)).tendsto_subseq hvmem
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq δ hδ0
    refine ⟨σ, hσ, N, fun k l hk hl x hx => ?_⟩
    obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hcover hx)
    have hxy' : dist x y ≤ δ := (mem_ball.mp hxy).le
    have h1 : |h (ψ (σ k)) y - h (ψ (σ l)) y| ≤ δ := by
      have := (dist_le_pi_dist (v (σ k)) (v (σ l)) ⟨y, hyt⟩).trans (hN k hk l hl).le
      rwa [Real.dist_eq] at this
    have hLip : ∀ j, |h j x - h j y| ≤ L' * δ := fun j =>
      (hL j x hx y (htK hyt)).trans (mul_le_mul (le_max_left _ _) hxy' dist_nonneg hL'0)
    have h2 := hLip (ψ (σ k))
    have h3 := hLip (ψ (σ l))
    rw [abs_sub_comm] at h3
    calc |h (ψ (σ k)) x - h (ψ (σ l)) x|
        ≤ |h (ψ (σ k)) x - h (ψ (σ k)) y| + |h (ψ (σ k)) y - h (ψ (σ l)) y| +
            |h (ψ (σ l)) y - h (ψ (σ l)) x| := by
          have e1 := abs_sub_le (h (ψ (σ k)) x) (h (ψ (σ k)) y) (h (ψ (σ l)) x)
          have e2 := abs_sub_le (h (ψ (σ k)) y) (h (ψ (σ l)) y) (h (ψ (σ l)) x)
          linarith
      _ ≤ L' * δ + δ + L' * δ := by linarith
      _ ≤ η := by linarith [mul_nonneg hL'0 hδ0.le]
  -- Step 4b: the diagonal argument for countably many eventually-pairwise properties that can
  -- each be achieved along a further subsequence of any subsequence.
  have hdiag : ∀ R : ℕ → ℕ → ℕ → Prop, (∀ (j : ℕ) (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l → R j (ψ (σ k)) (ψ (σ l))) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l → R j (φ k) (φ l) := by
    clear hmol hmolerr hAA
    intro R hR
    choose s hs_mono hs_cauchy using hR
    -- `Σ_0 = id`, `Σ_{m+1} = Σ_m ∘ s m Σ_m`, in the subtype of strictly increasing maps
    obtain ⟨Sig, hSigS⟩ : ∃ Sig : ℕ → {ψ : ℕ → ℕ // StrictMono ψ},
        ∀ m, (Sig (m + 1)).1 = (Sig m).1 ∘ s m (Sig m).1 (Sig m).2 :=
      ⟨fun m => Nat.rec (motive := fun _ => {ψ : ℕ → ℕ // StrictMono ψ}) ⟨id, strictMono_id⟩
        (fun m Ψ => ⟨Ψ.1 ∘ s m Ψ.1 Ψ.2, Ψ.2.comp (hs_mono m Ψ.1 Ψ.2)⟩) m, fun _ => rfl⟩
    -- nesting: for `m ≤ k`, the value of `Σ_k` at `i` is a value of `Σ_m` at some `j ≥ i`
    have nest : ∀ m k, m ≤ k → ∀ i, ∃ j, i ≤ j ∧ (Sig k).1 i = (Sig m).1 j := by
      intro m k hmk
      induction k, hmk using Nat.le_induction with
      | base => exact fun i => ⟨i, le_rfl, rfl⟩
      | succ k _ ih =>
        intro i
        obtain ⟨j, hij, hj⟩ := ih (s k (Sig k).1 (Sig k).2 i)
        exact ⟨j, (hs_mono k _ _).le_apply.trans hij, by rw [hSigS]; exact hj⟩
    -- the diagonal map `φ k = Σ_k k`
    refine ⟨fun k => (Sig k).1 k, strictMono_nat_of_lt_succ fun k => ?_, fun m => ?_⟩
    · show (Sig k).1 k < (Sig (k + 1)).1 (k + 1)
      rw [hSigS]
      exact (Sig k).2 ((Nat.lt_succ_self k).trans_le (hs_mono k _ _).le_apply)
    · obtain ⟨N, hN⟩ := hs_cauchy m (Sig m).1 (Sig m).2
      refine ⟨max N (m + 1), fun k l hk hl => ?_⟩
      obtain ⟨a, hka, ha⟩ := nest (m + 1) k ((le_max_right _ _).trans hk) k
      obtain ⟨b, hlb, hb⟩ := nest (m + 1) l ((le_max_right _ _).trans hl) l
      show R m ((Sig k).1 k) ((Sig l).1 l)
      rw [ha, hb, hSigS]
      exact hN a b ((le_max_left _ _).trans (hk.trans hka)) ((le_max_left _ _).trans (hl.trans hlb))
  -- Step 5 (criterion): uniform smallness on the annulus plus uniform interior approximation by
  -- functions that are uniformly Cauchy gives the Cauchy property in `L²(B̆₁(0))`.
  have hcrit : ∀ u : ℕ → Rn n → ℝ,
      (∀ k, AEStronglyMeasurable (u k) (volume.restrict (ball (0 : Rn n) 1))) →
      (∀ η : ℝ, 0 < η → ∃ (r : ℝ) (v : ℕ → Rn n → ℝ), 0 < r ∧ r < 1 ∧
        (∀ k, AEStronglyMeasurable (v k) (volume.restrict (ball (0 : Rn n) r))) ∧
        (∀ k, ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x‖ₑ ^ 2 ≤ ENNReal.ofReal η) ∧
        (∀ k, ∫⁻ x in ball (0 : Rn n) r, ‖u k x - v k x‖ₑ ^ 2 ≤ ENNReal.ofReal η) ∧
        ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
          ∀ x ∈ ball (0 : Rn n) r, |v k x - v l x| ≤ θ) →
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2 ≤ ENNReal.ofReal η := by
    clear hmol hmolerr hAA hdiag
    intro u hu H η hη
    obtain ⟨r, v, hr0, hr1, hv, ha, hb, hc⟩ := H (η / 20) (by positivity)
    have hVfin : volume (ball (0 : Rn n) 1) ≠ ∞ := measure_ball_lt_top.ne
    set V : ℝ≥0∞ := volume (ball (0 : Rn n) 1) with hV
    have hVnn : 0 ≤ V.toReal := ENNReal.toReal_nonneg
    set θ : ℝ := Real.sqrt (η / (6 * (V.toReal + 1))) with hθdef
    have hθpos : 0 < θ := Real.sqrt_pos.mpr (by positivity)
    have hθsq : θ ^ 2 = η / (6 * (V.toReal + 1)) := Real.sq_sqrt (by positivity)
    set e : ℝ≥0∞ := ENNReal.ofReal (η / 20) with he
    obtain ⟨N, hN⟩ := hc θ hθpos
    refine ⟨N, fun k l hk hl => ?_⟩
    have hsq : ∀ s : ℝ, ‖s‖ₑ ^ 2 = ENNReal.ofReal (s ^ 2) := by
      intro s
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg s), sq_abs]
    have hpt2 : ∀ s t : ℝ, ‖s - t‖ₑ ^ 2 ≤ 2 * ‖s‖ₑ ^ 2 + 2 * ‖t‖ₑ ^ 2 := by
      intro s t
      rw [hsq, hsq, hsq]
      have key : (s - t) ^ 2 ≤ 2 * s ^ 2 + 2 * t ^ 2 := by linarith [sq_nonneg (s + t)]
      calc ENNReal.ofReal ((s - t) ^ 2) ≤ ENNReal.ofReal (2 * s ^ 2 + 2 * t ^ 2) :=
            ENNReal.ofReal_le_ofReal key
        _ = 2 * ENNReal.ofReal (s ^ 2) + 2 * ENNReal.ofReal (t ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            simp
    have hpt3 : ∀ a b c d : ℝ, |c - d| ≤ θ →
        ‖a - b‖ₑ ^ 2 ≤ 3 * ‖a - c‖ₑ ^ 2 + 3 * ‖b - d‖ₑ ^ 2 + ENNReal.ofReal (3 * θ ^ 2) := by
      intro a b c d hcd
      rw [hsq, hsq, hsq]
      have hY : (c - d) ^ 2 ≤ θ ^ 2 := sq_le_sq' (abs_le.mp hcd).1 (abs_le.mp hcd).2
      have key : (a - b) ^ 2 ≤ 3 * (a - c) ^ 2 + 3 * (b - d) ^ 2 + 3 * θ ^ 2 := by
        linarith [sq_nonneg ((a - c) - (c - d)), sq_nonneg ((c - d) - (d - b)),
          sq_nonneg ((a - c) - (d - b))]
      calc ENNReal.ofReal ((a - b) ^ 2)
          ≤ ENNReal.ofReal (3 * (a - c) ^ 2 + 3 * (b - d) ^ 2 + 3 * θ ^ 2) :=
            ENNReal.ofReal_le_ofReal key
        _ = 3 * ENNReal.ofReal ((a - c) ^ 2) + 3 * ENNReal.ofReal ((b - d) ^ 2)
              + ENNReal.ofReal (3 * θ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3) (q := (a - c) ^ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3) (q := (b - d) ^ 2)]
            simp
    have hBr : ball (0 : Rn n) r ⊆ ball (0 : Rn n) 1 := ball_subset_ball hr1.le
    -- splitting `B = B_r ∪ (B \ B_r)`
    have hsplit : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2 ≤
        (∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2) +
          ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2 := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2
          = ∫⁻ x in ball (0 : Rn n) r ∪ (ball (0 : Rn n) 1 \ ball 0 r),
              ‖u k x - u l x‖ₑ ^ 2 := by
            rw [Set.union_sdiff_cancel hBr]
        _ ≤ _ := lintegral_union_le _ _ _
    -- the annulus
    have hbd : ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2 ≤ 2 * e + 2 * e := by
      have hmk : AEMeasurable (fun x => 2 * ‖u k x‖ₑ ^ 2)
          (volume.restrict (ball (0 : Rn n) 1 \ ball 0 r)) :=
        ((((hu k).mono_set sdiff_subset).enorm).pow_const 2).const_mul 2
      calc ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x - u l x‖ₑ ^ 2
          ≤ ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, (2 * ‖u k x‖ₑ ^ 2 + 2 * ‖u l x‖ₑ ^ 2) :=
            lintegral_mono fun x => hpt2 _ _
        _ = 2 * (∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u k x‖ₑ ^ 2) +
              2 * ∫⁻ x in ball (0 : Rn n) 1 \ ball 0 r, ‖u l x‖ₑ ^ 2 := by
            rw [lintegral_add_left' hmk, lintegral_const_mul' _ _ (by norm_num),
              lintegral_const_mul' _ _ (by norm_num)]
        _ ≤ 2 * e + 2 * e := by
            gcongr
            · exact ha k
            · exact ha l
    -- the interior
    have hint : ∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2 ≤
        3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V := by
      have hmk : AEMeasurable (fun x => 3 * ‖u k x - v k x‖ₑ ^ 2)
          (volume.restrict (ball (0 : Rn n) r)) :=
        (((((hu k).mono_set hBr).sub (hv k)).enorm).pow_const 2).const_mul 3
      calc ∫⁻ x in ball (0 : Rn n) r, ‖u k x - u l x‖ₑ ^ 2
          ≤ ∫⁻ x in ball (0 : Rn n) r,
              (3 * ‖u k x - v k x‖ₑ ^ 2 + 3 * ‖u l x - v l x‖ₑ ^ 2
                + ENNReal.ofReal (3 * θ ^ 2)) :=
            setLIntegral_mono' measurableSet_ball fun x hx => hpt3 _ _ _ _ (hN k l hk hl x hx)
        _ = 3 * (∫⁻ x in ball (0 : Rn n) r, ‖u k x - v k x‖ₑ ^ 2) +
              3 * (∫⁻ x in ball (0 : Rn n) r, ‖u l x - v l x‖ₑ ^ 2) +
              ENNReal.ofReal (3 * θ ^ 2) * volume (ball (0 : Rn n) r) := by
            rw [lintegral_add_right' _ aemeasurable_const, lintegral_add_left' hmk,
              lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
              setLIntegral_const]
        _ ≤ 3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V := by
            gcongr
            · exact hb k
            · exact hb l
            · exact measure_mono hBr
    have hθV : ENNReal.ofReal (3 * θ ^ 2) * V ≤ 10 * e := by
      rw [← ENNReal.ofReal_toReal hVfin, ← ENNReal.ofReal_mul (by positivity), he,
        show (10 : ℝ≥0∞) = ENNReal.ofReal 10 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [hθsq]
      have hq : 0 ≤ η / (6 * (V.toReal + 1)) := by positivity
      have hq1 : η / (6 * (V.toReal + 1)) * (V.toReal + 1) = η / 6 := by
        rw [← div_div, div_mul_cancel₀ _ (by positivity)]
      linarith
    have he20 : ENNReal.ofReal η = 20 * e := by
      rw [he, show (20 : ℝ≥0∞) = ENNReal.ofReal 20 by simp, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    calc ∫⁻ x in ball (0 : Rn n) 1, ‖u k x - u l x‖ₑ ^ 2
        ≤ _ := hsplit
      _ ≤ (3 * e + 3 * e + ENNReal.ofReal (3 * θ ^ 2) * V) + (2 * e + 2 * e) :=
          add_le_add hint hbd
      _ ≤ (3 * e + 3 * e + 10 * e) + (2 * e + 2 * e) := by gcongr
      _ = 20 * e := by ring
      _ = ENNReal.ofReal η := he20.symm
  -- Step 6 (completeness): a sequence that is Cauchy in `L²(μ)` has a limit in `L²(μ)`.
  have hcomplete : ∀ (μ : Measure (Rn n)) (u : ℕ → Rn n → ℝ), (∀ k, MemLp (u k) 2 μ) →
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
        ∫⁻ x, ‖u k x - u l x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal η) →
      ∃ w : Rn n → ℝ, MemLp w 2 μ ∧ Tendsto (fun k => ∫⁻ x, ‖u k x - w x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
    clear hmol hmolerr hAA hdiag hcrit
    intro μ u hu hC
    -- the norm identity `‖v‖₂ ^ 2 = ∫⁻ ‖v‖ₑ ^ 2` (for a.e.-strongly measurable `v`)
    have key : ∀ v : Rn n → ℝ, AEStronglyMeasurable v μ →
        ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ = eLpNorm v 2 μ ^ 2 := by
      intro v hv
      have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (μ := μ) two_ne_zero hv
      simpa using h.symm
    have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    -- the classes `G k` of `u k` in `L²(μ)` form a Cauchy sequence
    let G : ℕ → Lp ℝ 2 μ := fun k => (hu k).toLp (u k)
    have hG : CauchySeq G := by
      rw [EMetric.cauchySeq_iff]
      intro ε hε
      obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      have hr : 0 < r := ENNReal.ofReal_pos.1 hr1
      obtain ⟨N, hN⟩ := hC (r ^ 2) (by positivity)
      refine ⟨N, fun k hk l hl => ?_⟩
      calc edist (G k) (G l) = eLpNorm (u k - u l) 2 μ := Lp.edist_toLp_toLp _ _ _ _
        _ ≤ ENNReal.ofReal r := by
          rw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
            ← key _ ((hu k).aestronglyMeasurable.sub (hu l).aestronglyMeasurable),
            ← ENNReal.ofReal_pow hr0]
          exact hN k l hk hl
        _ < ε := hr2
    -- completeness of `L²(μ)` (Riesz–Fischer)
    obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete hG
    refine ⟨W, Lp.memLp W, ?_⟩
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hW
    have h2 : ∀ k, eLpNorm (⇑(G k) - ⇑W) 2 μ = eLpNorm (u k - ⇑W) 2 μ := fun k =>
      eLpNorm_congr_ae ((hu k).coeFn_toLp.sub EventuallyEq.rfl)
    have h3 : ∀ k, ∫⁻ x, ‖u k x - W x‖ₑ ^ 2 ∂μ = eLpNorm (u k - ⇑W) 2 μ ^ 2 := fun k =>
      key _ ((hu k).aestronglyMeasurable.sub (Lp.memLp W).aestronglyMeasurable)
    have h4 := ENNReal.Tendsto.pow (n := 2) hW
    simp only [h2, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h4
    simpa only [h3] using h4
  -- Assembly.
  intro A f g hW hf hg
  -- Step 0: measurable representatives `F k` of `f k` on the unit ball.
  let F : ℕ → Rn n → ℝ := fun k => (hW k).1.aestronglyMeasurable.mk (f k)
  have hFmeas : ∀ k, Measurable (F k) := fun k =>
    (hW k).1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFae : ∀ k, f k =ᵐ[volume.restrict (ball (0 : Rn n) 1)] F k := fun k =>
    (hW k).1.aestronglyMeasurable.ae_eq_mk
  have hWF : ∀ k, IsW12WithGradient (F k) (g k) (ball 0 1) := by
    intro k
    obtain ⟨h1, h2, h3⟩ := hW k
    refine ⟨h1.ae_eq (hFae k), h2, ?_⟩
    intro ζ hζ hζc hζB
    rw [← h3 ζ hζ hζc hζB]
    refine integral_congr_ae ?_
    filter_upwards [hFae k] with x hx
    rw [hx]
  have hFbd : ∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ^ 2 ≤ ENNReal.ofReal A := by
    intro k
    calc ∫⁻ x in ball (0 : Rn n) 1, ‖F k x‖ₑ ^ 2 = ∫⁻ x in ball (0 : Rn n) 1, ‖f k x‖ₑ ^ 2 := by
          refine lintegral_congr_ae ?_
          filter_upwards [hFae k] with x hx
          rw [hx]
      _ ≤ _ := hf k
  -- The sibling estimates R1 (boundary layer) and R2 (translation).
  obtain ⟨C1, hC1, hR1⟩ := Submission.w12_ball_boundary_layer_estimate n hn
  have hR2 := Submission.w12_ball_translation_estimate n hn
  -- Mollifiers at the scales `ε_m = 1/(m+2)` and the mollified functions `H m k`.
  choose ρ C hρc hρnn hρsupp hρint hρbd using fun m : ℕ => hmol (1 / ((m : ℝ) + 2)) (by positivity)
  let H : ℕ → ℕ → Rn n → ℝ := fun m k x => ∫ y in ball (0 : Rn n) 1, ρ m (x - y) * F k y
  have hHbd : ∀ m k x x', |H m k x| ≤ C m * Real.sqrt A ∧
      |H m k x - H m k x'| ≤ C m * Real.sqrt A * ‖x - x'‖ := fun m k x x' =>
    hρbd m A (F k) (hWF k).1 (hFbd k) x x'
  have hHcont : ∀ m k, Continuous (H m k) := by
    intro m k
    refine (LipschitzWith.of_dist_le' (K := C m * Real.sqrt A) fun x x' => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    exact (hHbd m k x x').2
  -- Step 4: one subsequence `φ` along which every `H m` is uniformly Cauchy on `B₁(0)`
  -- (diagonal argument over the pairs `(m, i) = Nat.unpair j`, tolerance `1/(i+1)`).
  obtain ⟨φ, hφmono, hφ⟩ := hdiag
    (fun j p q => ∀ x ∈ closedBall (0 : Rn n) 1,
      |H (Nat.unpair j).1 p x - H (Nat.unpair j).1 q x| ≤ 1 / (((Nat.unpair j).2 : ℝ) + 1))
    (fun j ψ _ => hAA (closedBall 0 1) (H (Nat.unpair j).1) (C (Nat.unpair j).1 * Real.sqrt A)
      (C (Nat.unpair j).1 * Real.sqrt A) (isCompact_closedBall 0 1)
      (fun k x _ => (hHbd _ k x x).1)
      (fun k x _ y _ => by rw [dist_eq_norm]; exact (hHbd _ k x y).2)
      _ (by positivity) ψ)
  have hφ' : ∀ (m : ℕ) (θ : ℝ), 0 < θ → ∃ N : ℕ, ∀ k l, N ≤ k → N ≤ l →
      ∀ x ∈ closedBall (0 : Rn n) 1, |H m (φ k) x - H m (φ l) x| ≤ θ := by
    intro m θ hθ
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hθ
    obtain ⟨N, hN⟩ := hφ (Nat.pair m i)
    refine ⟨N, fun k l hk hl x hx => ?_⟩
    have h := hN k l hk hl x hx
    simp only [Nat.unpair_pair] at h
    exact h.trans hi.le
  -- Step 5: the Cauchy criterion, applied to `u k = F (φ k)`.
  have hcauchy := hcrit (fun k => F (φ k)) (fun k => (hFmeas (φ k)).aestronglyMeasurable) (by
    intro η hη
    obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = max A 0 := ⟨_, rfl⟩
    have hA'0 : 0 ≤ A' := by rw [hA']; exact le_max_right A 0
    have hAA' : ENNReal.ofReal A ≤ ENNReal.ofReal A' := by
      rw [hA']; exact ENNReal.ofReal_le_ofReal (le_max_left A 0)
    -- the radius `r = 1 - t`
    have hden : 0 < 2 * C1 * A' + 1 := by positivity
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (1 / 2) ((η / (2 * C1 * A' + 1)) ^ 2) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
    have ht1 : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
    have htsq : Real.sqrt t ≤ η / (2 * C1 * A' + 1) := by
      rw [Real.sqrt_le_left (by positivity), ht]
      exact min_le_right _ _
    -- the scale `ε_m`
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (lt_min ht0 (by positivity : 0 < η / (A' + 1)))
    have hεm : 1 / ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hεt : 1 / ((m : ℝ) + 2) < t := lt_of_le_of_lt hεm (lt_of_lt_of_le hm (min_le_left _ _))
    have hεη : 1 / ((m : ℝ) + 2) < η / (A' + 1) :=
      lt_of_le_of_lt hεm (lt_of_lt_of_le hm (min_le_right _ _))
    have hε0 : 0 < 1 / ((m : ℝ) + 2) := by positivity
    have hε1 : 1 / ((m : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hεA : (1 / ((m : ℝ) + 2)) ^ 2 * A' ≤ η := by
      have h1 : (1 / ((m : ℝ) + 2)) ^ 2 ≤ 1 / ((m : ℝ) + 2) := by
        rw [sq]; exact mul_le_of_le_one_left hε0.le hε1
      have h2 : 1 / ((m : ℝ) + 2) * A' ≤ η / (A' + 1) * A' :=
        mul_le_mul_of_nonneg_right hεη.le hA'0
      have h3 : η / (A' + 1) * A' ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (by linarith) hη.le
      calc (1 / ((m : ℝ) + 2)) ^ 2 * A' ≤ 1 / ((m : ℝ) + 2) * A' :=
            mul_le_mul_of_nonneg_right h1 hA'0
        _ ≤ η := h2.trans h3
    refine ⟨1 - t, fun k => H m (φ k), by linarith, by linarith,
      fun k => (hHcont m (φ k)).aestronglyMeasurable, ?_, ?_, ?_⟩
    · -- (a) the annulus, from R1
      intro k
      have h := hR1 (F (φ k)) (g (φ k)) (hWF (φ k)) (1 - t) (by linarith) (by linarith)
      rw [sub_sub_cancel] at h
      refine h.trans ?_
      calc ENNReal.ofReal (C1 * Real.sqrt t) * ((∫⁻ x in ball (0 : Rn n) 1, ‖F (φ k) x‖ₑ ^ 2) +
            ∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2)
          ≤ ENNReal.ofReal (C1 * Real.sqrt t) * (ENNReal.ofReal A' + ENNReal.ofReal A') := by
            gcongr
            · exact (hFbd (φ k)).trans hAA'
            · exact (hg (φ k)).trans hAA'
        _ = ENNReal.ofReal (C1 * Real.sqrt t * (A' + A')) := by
            rw [← ENNReal.ofReal_add hA'0 hA'0, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal η := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : C1 * Real.sqrt t * (A' + A') ≤
                C1 * (η / (2 * C1 * A' + 1)) * (A' + A') := by
              gcongr
            have h2 : C1 * (η / (2 * C1 * A' + 1)) * (A' + A') ≤ η := by
              rw [mul_comm C1, mul_assoc, div_mul_eq_mul_div, div_le_iff₀ hden]
              exact mul_le_mul_of_nonneg_left (by linarith) hη.le
            exact h1.trans h2
    · -- (b) the interior mollification error, from Step 2 and R2
      intro k
      have h := hmolerr (ρ m) (F (φ k)) (1 / ((m : ℝ) + 2)) (1 - t)
        (∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2) (hρc m) (hρnn m) (hρsupp m) (hρint m)
        (hFmeas (φ k)) (by linarith) (by linarith)
        (fun z hz => hR2 (F (φ k)) (g (φ k)) (hWF (φ k)) (1 - t) z (by linarith) hz)
      calc ∫⁻ x in ball (0 : Rn n) (1 - t), ‖F (φ k) x - H m (φ k) x‖ₑ ^ 2
          = ∫⁻ x in ball (0 : Rn n) (1 - t), ‖H m (φ k) x - F (φ k) x‖ₑ ^ 2 :=
            lintegral_congr fun x => by rw [enorm_sub_rev]
        _ ≤ ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2) *
              ∫⁻ x in ball (0 : Rn n) 1, ‖g (φ k) x‖ₑ ^ 2 := h
        _ ≤ ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2) * ENNReal.ofReal A' := by
            gcongr; exact (hg (φ k)).trans hAA'
        _ = ENNReal.ofReal ((1 / ((m : ℝ) + 2)) ^ 2 * A') := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hεA
    · -- (c) the uniform Cauchy property of the mollified subsequence, from Step 4
      intro θ hθ
      obtain ⟨N, hN⟩ := hφ' m θ hθ
      exact ⟨N, fun k l hk hl x hx => hN k l hk hl x
        (ball_subset_closedBall (ball_subset_ball (by linarith) hx))⟩)
  -- Step 6: completeness of `L²(B̆₁(0))`, and back from `F` to `f`.
  obtain ⟨w, hw, hlim⟩ := hcomplete (volume.restrict (ball (0 : Rn n) 1)) (fun k => F (φ k))
    (fun k => (hWF (φ k)).1) hcauchy
  refine ⟨φ, w, hφmono, hw, Tendsto.congr (fun k => ?_) hlim⟩
  refine lintegral_congr_ae ?_
  filter_upwards [hFae (φ k)] with x hx
  rw [hx]
/-- **Weak compactness in `L²(B; ℝⁿ)`** (Simon Ch. 5, proof of Lemma 3.1, p. 114: `∇f_{k'} → ∇w`
weakly in `L²` with `∫_B |∇w|² ≤ 1`).  If `∫_B |G_k|² ≤ 1` for every `k`, then a subsequence
`G_{φ(k)}` converges weakly in `L²(B; ℝⁿ)` to some `g` with `∫_B |g|² ≤ 1`.

`L²(B; ℝⁿ)` is made a real Hilbert space with `⟪u, v⟫ = ∫_B ⟨u, v⟩`, as in Mathlib's `L2Space`
(not among the frozen imports).  A diagonal subsequence makes `⟪G_{φ(k)}, G_j⟫` converge for every
`j`; the uniform bound extends this to the closed span `K` of the `G_j`, and the orthogonal
projection onto `K` to all of `L²`.  The limit functional has norm `≤ 1`; `g` is its Riesz
representative. -/
theorem l2_ball_weak_subsequence : ∀ (n : ℕ) (G : ℕ → Rn n → Rn n), (∀ k, MemLp (G k) 2 (volume.restrict (ball (0 : Rn n) 1))) → (∀ k, ∫⁻ x in ball (0 : Rn n) 1, ‖G k x‖ₑ ^ 2 ≤ 1) → ∃ (φ : ℕ → ℕ) (g : Rn n → Rn n), StrictMono φ ∧ MemLp g 2 (volume.restrict (ball (0 : Rn n) 1)) ∧ ∫⁻ x in ball (0 : Rn n) 1, ‖g x‖ₑ ^ 2 ≤ 1 ∧ ∀ h : Rn n → Rn n, MemLp h 2 (volume.restrict (ball (0 : Rn n) 1)) → Tendsto (fun k => ∫ x in ball (0 : Rn n) 1, inner ℝ (G (φ k) x) (h x)) atTop (𝓝 (∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (h x))) := by
  -- Step 1: a bounded sequence in a real Hilbert space has a weakly convergent subsequence
  -- whose limit lies in the same closed ball.
  have weak : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (u : ℕ → H), (∀ k, ‖u k‖ ≤ 1) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ γ : H, ‖γ‖ ≤ 1 ∧
        ∀ v, Tendsto (fun k => inner ℝ (u (φ k)) v) atTop (𝓝 (inner ℝ γ v)) := by
    intro H _ _ _ u hu
    have hbd : ∀ k v, |inner ℝ (u k) v| ≤ ‖v‖ := fun k v =>
      (abs_real_inner_le_norm _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hu k))
    -- Diagonal extraction: `⟪u (φ k), u j⟫` converges for every `j` (Tychonoff).
    have hmem : ∀ k, (fun j => inner ℝ (u k) (u j)) ∈ Set.pi univ fun _ : ℕ => Icc (-1 : ℝ) 1 :=
      fun k j _ => abs_le.mp ((hbd k (u j)).trans (hu j))
    obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_univ_pi fun _ => isCompact_Icc).tendsto_subseq hmem
    have hconv₀ : ∀ j, Tendsto (fun k => inner ℝ (u (φ k)) (u j)) atTop (𝓝 (a j)) :=
      fun j => tendsto_pi_nhds.mp hlim j
    -- Convergence against the span of the sequence.
    have hspan : ∀ v ∈ Submodule.span ℝ (Set.range u),
        ∃ l, Tendsto (fun k => inner ℝ (u (φ k)) v) atTop (𝓝 l) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact ⟨a j, hconv₀ j⟩
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨l₁, h₁⟩ := hx
        obtain ⟨l₂, h₂⟩ := hy
        exact ⟨l₁ + l₂, by simpa only [inner_add_right] using h₁.add h₂⟩
      | smul c x _ hx =>
        obtain ⟨l, h⟩ := hx
        exact ⟨c * l, by simpa only [real_inner_smul_right] using h.const_mul c⟩
    -- Convergence against its closure, by the uniform bound `‖u k‖ ≤ 1`.
    set K := (Submodule.span ℝ (Set.range u)).topologicalClosure with hK
    have hclos : ∀ v ∈ K, ∃ l, Tendsto (fun k => inner ℝ (u (φ k)) v) atTop (𝓝 l) := by
      intro v hv
      rw [← SetLike.mem_coe, hK, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hv
      apply cauchySeq_tendsto_of_complete
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨w, hw, hvw⟩ := hv (ε / 3) (by positivity)
      obtain ⟨l, hl⟩ := hspan w hw
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hl.cauchySeq (ε / 3) (by positivity)
      refine ⟨N, fun k hk => ?_⟩
      have e₁ := hbd (φ k) (v - w)
      have e₂ := hbd (φ N) (v - w)
      have e₃ := hN k hk
      rw [Real.dist_eq] at e₃ ⊢
      rw [dist_eq_norm] at hvw
      rw [inner_sub_right] at e₁ e₂
      have := abs_le.mp e₁
      have := abs_le.mp e₂
      have := abs_lt.mp e₃
      rw [abs_lt]
      constructor <;> linarith
    -- Convergence against every vector, via the orthogonal projection onto `K`.
    have hall : ∀ v : H, ∃ l, Tendsto (fun k => inner ℝ (u (φ k)) v) atTop (𝓝 l) := by
      intro v
      obtain ⟨l, hl⟩ := hclos (K.starProjection v) (K.starProjection_apply_mem v)
      refine ⟨l, hl.congr fun k => ?_⟩
      have hmemK : u (φ k) ∈ K :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ k, rfl⟩)
      have h0 :=
        Submodule.inner_right_of_mem_orthogonal hmemK (K.sub_starProjection_mem_orthogonal v)
      rw [inner_sub_right] at h0
      linarith
    -- The limit functional and its Riesz representative.
    choose L hL using hall
    have Ladd : ∀ v w, L (v + w) = L v + L w := fun v w =>
      tendsto_nhds_unique (hL (v + w)) (by simpa only [inner_add_right] using (hL v).add (hL w))
    have Lsmul : ∀ (c : ℝ) v, L (c • v) = c * L v := fun c v => tendsto_nhds_unique (hL (c • v))
      (by simpa only [real_inner_smul_right] using (hL v).const_mul c)
    have Lbound : ∀ v, ‖L v‖ ≤ 1 * ‖v‖ := fun v => by
      rw [one_mul, Real.norm_eq_abs]
      exact le_of_tendsto (hL v).abs (Eventually.of_forall fun k => hbd (φ k) v)
    let Lc : StrongDual ℝ H := LinearMap.mkContinuous
      { toFun := L, map_add' := Ladd, map_smul' := fun c v => by simpa using Lsmul c v } 1 Lbound
    refine ⟨φ, hφ, (InnerProductSpace.toDual ℝ H).symm Lc, ?_, fun v => ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact LinearMap.mkContinuous_norm_le _ zero_le_one _
    · rw [InnerProductSpace.toDual_symm_apply]
      exact hL v
  -- Step 2: the Hilbert space `L²(B; ℝⁿ)`.
  intro n G hG hGb
  set μ : Measure (Rn n) := volume.restrict (ball (0 : Rn n) 1)
  have hsq : ∀ f : Rn n → Rn n, AEStronglyMeasurable f μ →
      eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := fun f hf => by
    simpa [ENNReal.rpow_two] using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf
  have hint : ∀ f g : Lp (Rn n) 2 μ, Integrable (fun x => inner ℝ (f x) (g x)) μ := by
    intro f g
    refine (((Lp.memLp f).integrable_norm_pow two_ne_zero).add
      ((Lp.memLp g).integrable_norm_pow two_ne_zero)).mono'
      (continuous_inner.comp_aestronglyMeasurable₂ (Lp.aestronglyMeasurable f)
        (Lp.aestronglyMeasurable g)) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply]
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [norm_nonneg (f x), norm_nonneg (g x), sq_nonneg (‖f x‖ - ‖g x‖)]
  have hnorm : ∀ f : Lp (Rn n) 2 μ, ‖f‖ ^ 2 = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := fun f => by
    rw [Lp.norm_def, ← ENNReal.toReal_pow, hsq _ (Lp.aestronglyMeasurable f)]
  have hnorm' : ∀ f : Lp (Rn n) 2 μ, ‖f‖ ^ 2 = ∫ x, inner ℝ (f x) (f x) ∂μ := fun f => by
    simp_rw [real_inner_self_eq_norm_sq]
    rw [hnorm, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      ((Lp.aestronglyMeasurable f).norm.pow 2)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  let _ : Inner ℝ (Lp (Rn n) 2 μ) := ⟨fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ⟩
  let _ : InnerProductSpace ℝ (Lp (Rn n) 2 μ) :=
    { norm_sq_eq_re_inner := fun f => by rw [RCLike.re_to_real]; exact hnorm' f
      conj_inner_symm := fun f g => by
        rw [conj_trivial]
        exact integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
      add_left := fun f f' g => by
        change ∫ x, inner ℝ ((f + f') x) (g x) ∂μ =
          ∫ x, inner ℝ (f x) (g x) ∂μ + ∫ x, inner ℝ (f' x) (g x) ∂μ
        rw [← integral_add (hint f g) (hint f' g)]
        refine integral_congr_ae ((Lp.coeFn_add f f').mono fun x hx => ?_)
        simp only [hx, Pi.add_apply, inner_add_left]
      smul_left := fun f g r => by
        change ∫ x, inner ℝ ((r • f) x) (g x) ∂μ =
          (starRingEnd ℝ) r * ∫ x, inner ℝ (f x) (g x) ∂μ
        rw [conj_trivial, ← integral_const_mul]
        refine integral_congr_ae ((Lp.coeFn_smul r f).mono fun x hx => ?_)
        simp only [hx, Pi.smul_apply, real_inner_smul_left] }
  -- Step 3: apply Step 1 to the classes of the `G k` and return to functions.
  have hGn : ∀ k, ‖(hG k).toLp (G k)‖ ≤ 1 := fun k => by
    have h1 : ‖(hG k).toLp (G k)‖ ^ 2 ≤ 1 := by
      rw [hnorm, lintegral_congr_ae ((hG k).coeFn_toLp.mono fun x hx => by rw [hx])]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hGb k)
    nlinarith [norm_nonneg ((hG k).toLp (G k))]
  obtain ⟨φ, hφ, γ, hγ, hconv⟩ := weak (Lp (Rn n) 2 μ) (fun k => (hG k).toLp (G k)) hGn
  refine ⟨φ, γ, hφ, Lp.memLp γ, ?_, fun h hh => ?_⟩
  · have h1 : eLpNorm γ 2 μ ≤ 1 := by
      rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top γ), ← Lp.norm_def]
      exact ENNReal.ofReal_le_one.mpr hγ
    rw [← hsq _ (Lp.aestronglyMeasurable γ)]
    exact pow_le_one₀ (by positivity) h1
  · have key : ∀ f : Lp (Rn n) 2 μ, inner ℝ f (hh.toLp h) = ∫ x, inner ℝ (f x) (h x) ∂μ :=
      fun f => integral_congr_ae (hh.coeFn_toLp.mono fun x hx => by simp only [hx])
    have h2 := hconv (hh.toLp h)
    rw [key] at h2
    refine h2.congr fun k => ?_
    rw [key]
    exact integral_congr_ae ((hG (φ k)).coeFn_toLp.mono fun x hx => by simp only [hx])
/-- **Weak harmonicity in Laplacian form** (step 1 of the proof of Weyl's lemma).  If
`w ∈ W^{1,2}(B)`, `B = B̆₁(0)`, has weak gradient `g` with `∫_B ⟨g, ∇ζ⟩ = 0` for every
`ζ ∈ C^∞_c(B)`, then `∫_B w Δζ = 0` for every such `ζ`.
Proof: each partial derivative `ζᵢ = Dζ(·)[eᵢ]` is again a test function, and pairing the
weak-gradient identity for `ζᵢ` with `eᵢ` gives `∫_B w D²ζ[eᵢ, eᵢ] = -∫_B ζᵢ ⟨g, eᵢ⟩`.  Summing
over `i`, with `Δζ = Σᵢ D²ζ[eᵢ, eᵢ]` and `⟨g, ∇ζ⟩ = Σᵢ ζᵢ ⟨g, eᵢ⟩`, gives
`∫_B w Δζ = -∫_B ⟨g, ∇ζ⟩ = 0`. -/
theorem w12_ball_weak_laplacian_eq_zero : ∀ n : ℕ, 1 ≤ n → ∀ (w : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient w g (ball 0 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x) = 0) → ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0 := by
  intro n _ w g hw hharm ζ hζ hζc hζB
  obtain ⟨hwL, hgL, hweak⟩ := hw
  -- `w` and `g` are integrable on the ball, which has finite measure.
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hwi : Integrable w (volume.restrict (ball (0 : Rn n) 1)) := hwL.integrable one_le_two
  have hgi : Integrable g (volume.restrict (ball (0 : Rn n) 1)) := hgL.integrable one_le_two
  -- Their products with continuous compactly supported (hence bounded) functions are integrable.
  have hint_w : ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
      Integrable (fun x => w x * φ x) (volume.restrict (ball (0 : Rn n) 1)) := by
    intro φ hφ hφc
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
    exact hwi.mul_bdd hφ.aestronglyMeasurable (Eventually.of_forall hC)
  have hint_g : ∀ (φ : Rn n → ℝ) (c : Rn n), Continuous φ → HasCompactSupport φ →
      Integrable (fun x => φ x * inner ℝ (g x) c) (volume.restrict (ball (0 : Rn n) 1)) := by
    intro φ c hφ hφc
    obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
    have hgc : Integrable (fun x => inner ℝ (g x) c) (volume.restrict (ball (0 : Rn n) 1)) := by
      have := (innerSL ℝ c).integrable_comp hgi
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [real_inner_comm]
    exact hgc.bdd_mul hφ.aestronglyMeasurable (Eventually.of_forall hC)
  -- The partial derivatives `ζᵢ = Dζ(·)[eᵢ]` are test functions.
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hDζ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ζ) := (contDiff_infty_iff_fderiv.1 hζ).2
  set ζ' : Fin n → Rn n → ℝ := fun i x => fderiv ℝ ζ x (b i) with hζ'
  have hζ's : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ζ' i) := fun i => hDζ.clm_apply contDiff_const
  have hζ'c : ∀ i, HasCompactSupport (ζ' i) := fun i => hζc.fderiv_apply ℝ (b i)
  have hζ'B : ∀ i, tsupport (ζ' i) ⊆ ball 0 1 := fun i =>
    (tsupport_fderiv_apply_subset ℝ (b i)).trans hζB
  -- The `i`-th coordinate of the weak-gradient identity for `ζᵢ`:
  -- `∫_B w Dζᵢ[eᵢ] = -∫_B ζᵢ ⟨g, eᵢ⟩`.
  have hcoord : ∀ i, ∫ x in ball (0 : Rn n) 1, w x * fderiv ℝ (ζ' i) x (b i) =
      -∫ x in ball (0 : Rn n) 1, ζ' i x * inner ℝ (g x) (b i) := by
    intro i
    have h := hweak (ζ' i) (hζ's i) (hζ'c i) (hζ'B i)
    have hgrad : Continuous (gradient (ζ' i)) :=
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp
        ((hζ's i).continuous_fderiv (by simp))
    have hgradc : HasCompactSupport (gradient (ζ' i)) := by
      refine (hζ'c i).mono' fun x hx => ?_
      by_contra h'
      exact hx (by rw [gradient, fderiv_of_notMem_tsupport ℝ h', map_zero])
    have hA : Integrable (fun x => w x • gradient (ζ' i) x)
        (volume.restrict (ball (0 : Rn n) 1)) := by
      obtain ⟨C, hC⟩ := hgrad.bounded_above_of_compact_support hgradc
      exact hwi.smul_bdd C hgrad.aestronglyMeasurable (Eventually.of_forall hC)
    have hB : Integrable (fun x => ζ' i x • g x) (volume.restrict (ball (0 : Rn n) 1)) := by
      obtain ⟨C, hC⟩ := (hζ's i).continuous.bounded_above_of_compact_support (hζ'c i)
      exact hgi.bdd_smul C (hζ's i).continuous.aestronglyMeasurable (Eventually.of_forall hC)
    have h1 := (innerSL ℝ (b i)).integral_comp_comm hA
    have h2 := (innerSL ℝ (b i)).integral_comp_comm hB
    calc ∫ x in ball (0 : Rn n) 1, w x * fderiv ℝ (ζ' i) x (b i)
        = ∫ x in ball (0 : Rn n) 1, innerSL ℝ (b i) (w x • gradient (ζ' i) x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp
      _ = innerSL ℝ (b i) (∫ x in ball (0 : Rn n) 1, w x • gradient (ζ' i) x) := h1
      _ = innerSL ℝ (b i) (-∫ x in ball (0 : Rn n) 1, ζ' i x • g x) := by rw [h]
      _ = -innerSL ℝ (b i) (∫ x in ball (0 : Rn n) 1, ζ' i x • g x) := map_neg _ _
      _ = -∫ x in ball (0 : Rn n) 1, innerSL ℝ (b i) (ζ' i x • g x) := by rw [h2]
      _ = -∫ x in ball (0 : Rn n) 1, ζ' i x * inner ℝ (g x) (b i) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp [real_inner_comm]
  -- `Dζᵢ(x)[eᵢ] = D²ζ(x)[eᵢ, eᵢ]`.
  have hD2 : ∀ i x, fderiv ℝ (ζ' i) x (b i) = fderiv ℝ (fderiv ℝ ζ) x (b i) (b i) := by
    intro i x
    have hd : DifferentiableAt ℝ (fderiv ℝ ζ) x := (hDζ.differentiable (by simp)) x
    rw [hζ', fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  -- `Δζ = Σᵢ D²ζ[eᵢ, eᵢ]` and `⟨g, ∇ζ⟩ = Σᵢ ζᵢ ⟨g, eᵢ⟩`.
  have hlap : ∀ x, Laplacian.laplacian ζ x = ∑ i, fderiv ℝ (fderiv ℝ ζ) x (b i) (b i) := by
    intro x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ζ b]
    simp [iteratedFDeriv_two_apply]
  have hpars : ∀ x, inner ℝ (g x) (gradient ζ x) = ∑ i, ζ' i x * inner ℝ (g x) (b i) := by
    intro x
    rw [← b.sum_inner_mul_inner (g x) (gradient ζ x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_gradient_right]
    simp [hζ', mul_comm]
  -- Summing over `i`: `∫_B w Δζ = -∫_B ⟨g, ∇ζ⟩ = 0`.
  have hcont2 : ∀ i, Continuous (fun x => fderiv ℝ (ζ' i) x (b i)) := fun i =>
    ((hζ's i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcomp2 : ∀ i, HasCompactSupport (fun x => fderiv ℝ (ζ' i) x (b i)) := fun i =>
    (hζ'c i).fderiv_apply ℝ (b i)
  calc ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x
      = ∫ x in ball (0 : Rn n) 1, ∑ i, w x * fderiv ℝ (ζ' i) x (b i) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hlap, Finset.mul_sum, hD2]
    _ = ∑ i, ∫ x in ball (0 : Rn n) 1, w x * fderiv ℝ (ζ' i) x (b i) :=
        integral_finsetSum _ (fun i _ => hint_w _ (hcont2 i) (hcomp2 i))
    _ = ∑ i, -∫ x in ball (0 : Rn n) 1, ζ' i x * inner ℝ (g x) (b i) :=
        Finset.sum_congr rfl fun i _ => hcoord i
    _ = -∫ x in ball (0 : Rn n) 1, ∑ i, ζ' i x * inner ℝ (g x) (b i) := by
        rw [integral_finsetSum _ (fun i _ => hint_g _ _ (hζ's i).continuous (hζ'c i)),
          Finset.sum_neg_distrib]
    _ = -∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x) := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (hpars x).symm
    _ = 0 := by rw [hharm ζ hζ hζc hζB, neg_zero]
/-- **Mollifications of a weakly harmonic function are harmonic** (step 2 of the proof of
Weyl's lemma, used for Simon Ch. 5, Lemma 3.1).  Let `w` be integrable on `B = B̆₁(0)` with
`∫_B w Δζ = 0` for every `ζ ∈ C^∞_c(B)`, and let `κ` be `C^∞` with `κ(z) = 0` whenever `|z| ≥ ε`.
Then `v(x) = ∫_B κ(x - y) w(y) dy` is `C^∞` on `ℝⁿ` and `Δv = 0` on `B̆_{1-ε}(0)`.

With `W = 1_B w`, `v = W ⋆ κ` is the convolution of an integrable function with a smooth
compactly supported kernel, so `v` is smooth and its derivatives fall on the kernel; summing over
an orthonormal basis gives `Δv(x) = ∫_B Δκ(x - t) w(t) dt`.  For `|x| < 1 - ε`,
`ζ(y) = κ(x - y)` is a test function with `tsupport ζ ⊆ B̄_ε(x) ⊆ B` and `Δζ(y) = Δκ(x - y)`, so
`Δv(x) = ∫_B w Δζ = 0`. -/
theorem ball_convolution_contDiff_laplacian_eq_zero : ∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0) → ∀ (κ : Rn n → ℝ) (ε : ℝ), ContDiff ℝ (⊤ : ℕ∞) κ → (∀ z : Rn n, ε ≤ ‖z‖ → κ z = 0) → ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) ∧ ∀ x ∈ ball (0 : Rn n) (1 - ε), Laplacian.laplacian (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) x = 0 := by
  intro n _hn w hw hharm κ ε hκ hκε
  -- Step 1: `W = 1_B w` is integrable and `v = W ⋆ κ` (convolution with `L = lsmul`).
  set W : Rn n → ℝ := (ball (0 : Rn n) 1).indicator w with hWdef
  have hWloc : LocallyIntegrable W :=
    ((integrable_indicator_iff measurableSet_ball).2 hw).locallyIntegrable
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hv : (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) =
      convolution (𝕜 := ℝ) W κ L volume := by
    funext x
    rw [convolution_def, ← integral_indicator measurableSet_ball]
    congr 1
    funext t
    by_cases ht : t ∈ ball (0 : Rn n) 1
    · simp [hWdef, hLdef, Set.indicator_of_mem ht, mul_comm]
    · simp [hWdef, hLdef, Set.indicator_of_notMem ht]
  -- Step 2: `κ = 0` off `B̄_ε(0)`, so `κ`, `Dκ` and `D²κ` are smooth with compact support.
  have hκc : HasCompactSupport κ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) ε) (fun z hz => hκε z ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hκ1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ κ) := (contDiff_infty_iff_fderiv.1 hκ).2
  have hκ2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ κ)) := (contDiff_infty_iff_fderiv.1 hκ1).2
  have hκ1c : HasCompactSupport (fderiv ℝ κ) := hκc.fderiv ℝ
  have hκ2c : HasCompactSupport (fderiv ℝ (fderiv ℝ κ)) := hκ1c.fderiv ℝ
  have hκ2cont : Continuous (fderiv ℝ (fderiv ℝ κ)) := hκ2.continuous
  -- Step 3: `v = W ⋆ κ` is smooth.
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact hκc.contDiff_convolution_right L hWloc hκ
  -- Steps 4–5: derivatives fall on the kernel, `D²v(x)[e, e] = ∫ W(t) D²κ(x - t)[e, e] dt`.
  have hD2 : fderiv ℝ (fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume)) =
      convolution (𝕜 := ℝ) W (fderiv ℝ (fderiv ℝ κ)) ((L.precompR (Rn n)).precompR (Rn n))
        volume := by
    have hD1 : fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume) =
        convolution (𝕜 := ℝ) W (fderiv ℝ κ) (L.precompR (Rn n)) volume := by
      funext x
      exact (hκc.hasFDerivAt_convolution_right L hWloc (hκ.of_le (mod_cast le_top)) x).fderiv
    rw [hD1]
    funext x
    exact (hκ1c.hasFDerivAt_convolution_right (L.precompR (Rn n)) hWloc
      (hκ1.of_le (mod_cast le_top)) x).fderiv
  have hD2v : ∀ x e : Rn n, fderiv ℝ (fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume)) x e e =
      ∫ t, W t * fderiv ℝ (fderiv ℝ κ) (x - t) e e := by
    intro x e
    rw [hD2, convolution_precompR_apply (L.precompR (Rn n)) hWloc hκ2c hκ2cont x e,
      convolution_precompR_apply L hWloc (hκ1c.fderiv_apply ℝ e)
        (hκ2cont.clm_apply continuous_const) x e, convolution_def]
    simp [hLdef]
  -- Each `t ↦ W(t) D²κ(x - t)[e, e]` is integrable: `D²κ(·)[e, e]` is continuous with compact
  -- support.
  have hint : ∀ x e : Rn n, Integrable (fun t => W t * fderiv ℝ (fderiv ℝ κ) (x - t) e e) := by
    intro x e
    have hc : HasCompactSupport (fun a => fderiv ℝ (fderiv ℝ κ) a e e) :=
      (hκ1c.fderiv_apply ℝ e).comp_left (g := fun T : Rn n →L[ℝ] ℝ => T e) (by simp)
    exact hc.convolutionExists_right L hWloc
      ((hκ2cont.clm_apply continuous_const).clm_apply continuous_const) x
  -- Step 6: `Δf(x) = ∑ᵢ D²f(x)[bᵢ, bᵢ]` for the standard orthonormal basis `b`.
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hlap : ∀ (f : Rn n → ℝ) (x : Rn n),
      Laplacian.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
    intro f x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    simp [iteratedFDeriv_two_apply]
  -- Step 7: for `|x| < 1 - ε`, `ζ(y) = κ(x - y)` is a test function with `tsupport ζ ⊆ B`.
  intro x hx
  set ζ : Rn n → ℝ := fun y => κ (x - y) with hζdef
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := hκ.comp (contDiff_const.sub contDiff_id)
  have hζsupp : Function.support ζ ⊆ closedBall x ε := by
    intro y hy
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra h
    exact hy (hκε _ (not_le.1 h).le)
  have hζc : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall x ε)
      (fun y hy => by_contra (fun h => hy (hζsupp h)))
  have hζB : tsupport ζ ⊆ ball 0 1 := by
    refine (closure_minimal hζsupp isClosed_closedBall).trans (closedBall_subset_ball' ?_)
    rw [mem_ball] at hx
    linarith
  -- Step 8: `Δζ(t) = Δκ(x - t)`, writing `ζ = κ(x + ·) ∘ (-id)`.
  have hκx : ContDiff ℝ (⊤ : ℕ∞) (fun z => κ (x + z)) := hκ.comp (contDiff_const.add contDiff_id)
  have hcomp : ζ = (fun z => κ (x + z)) ∘ (-(ContinuousLinearMap.id ℝ (Rn n))) := by
    funext y
    simp [hζdef, sub_eq_add_neg]
  have hlapζ : ∀ t,
      Laplacian.laplacian ζ t = ∑ i, fderiv ℝ (fderiv ℝ κ) (x - t) (b i) (b i) := by
    intro t
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ζ b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (i := 2) _ hκx t
        (WithTop.coe_le_coe.2 le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left,
      iteratedFDeriv_two_apply]
    simp [sub_eq_add_neg]
  -- Steps 6 and 9: `Δv(x) = ∑ᵢ ∫ W(t) D²κ(x - t)[bᵢ, bᵢ] dt = ∫_B w(t) Δζ(t) dt = 0`.
  rw [hv, hlap]
  simp_rw [hD2v]
  rw [← integral_finsetSum _ (fun i _ => hint x (b i)), ← hharm ζ hζ hζc hζB,
    ← integral_indicator measurableSet_ball]
  congr 1
  funext t
  by_cases ht : t ∈ ball (0 : Rn n) 1
  · rw [Set.indicator_of_mem ht, hlapζ t, Finset.mul_sum]
    simp [hWdef, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    simp [hWdef, Set.indicator_of_notMem ht]
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Weyl's lemma for the weak limit `w`: the mean-value
kernel.  With `E(σ) = expNegInvGlue (1 − σ)` (`C^∞`, `≥ 0`, `0` for `σ ≥ 1`, `> 0` for `σ < 1`),
`ρ(z) = c E(|z|²)` with `c = (∫ E(|z|²) dz)⁻¹` is `C^∞`, even, zero for `|z| ≥ 1` and of mass `1`;
`Ψ(z) = (c/2) P(|z|²)` with `P(σ) = ∫_1^σ E` is `C^∞` (`P' = E` by FTC), zero for `|z| ≥ 1`, and
`DΨ(z)[v] = (c/2) E(|z|²) 2⟨z, v⟩ = ρ(z)⟨z, v⟩` by the chain rule. -/
theorem mvk_exists_kernel_potential : ∀ n : ℕ, ∃ ρ Ψ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) ∧ (∀ z : Rn n, ρ (-z) = ρ z) ∧ ∫ z, ρ z = 1 ∧ ∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v := by
  intro n
  -- The profile `E(σ) = expNegInvGlue (1 - σ)`: `C^∞`, `≥ 0`, `0` for `σ ≥ 1`, `> 0` for `σ < 1`.
  set E : ℝ → ℝ := fun σ => expNegInvGlue (1 - σ)
  have hE_smooth : ContDiff ℝ (⊤ : ℕ∞) E :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hE_cont : Continuous E := hE_smooth.continuous
  have hE_nonneg : ∀ σ, 0 ≤ E σ := fun σ => expNegInvGlue.nonneg _
  have hE_zero : ∀ σ, 1 ≤ σ → E σ = 0 := fun σ hσ =>
    expNegInvGlue.zero_of_nonpos (by linarith)
  have hE_pos : ∀ σ, σ < 1 → 0 < E σ := fun σ hσ =>
    expNegInvGlue.pos_of_pos (by linarith)
  -- The unnormalized kernel `ρ₀(z) = E(‖z‖²)`: `C^∞`, zero for `‖z‖ ≥ 1`, of positive mass.
  set ρ₀ : Rn n → ℝ := fun z => E (‖z‖ ^ 2) with hρ₀_def
  have hρ₀_smooth : ContDiff ℝ (⊤ : ℕ∞) ρ₀ := hE_smooth.comp (contDiff_norm_sq ℝ)
  have hρ₀_zero : ∀ z : Rn n, 1 ≤ ‖z‖ → ρ₀ z = 0 := fun z hz =>
    hE_zero _ (one_le_pow₀ hz)
  have hρ₀_supp : HasCompactSupport ρ₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) 1) fun z hz =>
      hρ₀_zero z (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)
  have hρ₀_int : Integrable ρ₀ := hρ₀_smooth.continuous.integrable_of_hasCompactSupport hρ₀_supp
  have hI₀_pos : 0 < ∫ z, ρ₀ z := by
    rw [integral_pos_iff_support_of_nonneg (fun z => hE_nonneg _) hρ₀_int]
    refine (measure_ball_pos volume (0 : Rn n) one_pos).trans_le (measure_mono fun z hz => ?_)
    rw [mem_ball_zero_iff] at hz
    exact (hE_pos _ (pow_lt_one₀ (norm_nonneg z) hz two_ne_zero)).ne'
  set c : ℝ := (∫ z, ρ₀ z)⁻¹ with hc_def
  -- The primitive `P(σ) = ∫_1^σ E`: `P' = E` (FTC), so `P` is `C^∞`; `P = 0` on `[1, ∞)`.
  set P : ℝ → ℝ := fun σ => ∫ s in (1 : ℝ)..σ, E s with hP_def
  have hP_deriv : ∀ σ, HasDerivAt P (E σ) σ := fun σ =>
    (hE_cont.integral_hasStrictDerivAt 1 σ).hasDerivAt
  have hP_smooth : ContDiff ℝ (⊤ : ℕ∞) P :=
    contDiff_infty_iff_deriv.2 ⟨fun σ => (hP_deriv σ).differentiableAt,
      (funext fun σ => (hP_deriv σ).deriv : deriv P = E) ▸ hE_smooth⟩
  have hP_zero : ∀ σ, 1 ≤ σ → P σ = 0 := fun σ hσ => by
    simp only [hP_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_le hσ] at hs
      exact hE_zero s hs.1
  -- `ρ = c ρ₀` and `Ψ(z) = (c/2) P(‖z‖²)`.
  refine ⟨fun z => c * ρ₀ z, fun z => c / 2 * P (‖z‖ ^ 2), contDiff_const.mul hρ₀_smooth,
    contDiff_const.mul (hP_smooth.comp (contDiff_norm_sq ℝ)), fun z hz => ?_, fun z hz => ?_,
    fun z => ?_, ?_, fun z v => ?_⟩
  · show c * ρ₀ z = 0
    rw [hρ₀_zero z hz, mul_zero]
  · show c / 2 * P (‖z‖ ^ 2) = 0
    rw [hP_zero _ (one_le_pow₀ hz), mul_zero]
  · simp only [hρ₀_def, norm_neg]
  · rw [integral_const_mul, hc_def, inv_mul_cancel₀ hI₀_pos.ne']
  · -- Chain rule: `DΨ(z)[v] = (c/2) E(‖z‖²) 2⟨z, v⟩ = ρ(z) ⟨z, v⟩`.
    have h : HasFDerivAt (fun z : Rn n => c / 2 * P (‖z‖ ^ 2))
        ((c / 2) • (E (‖z‖ ^ 2) • (2 • innerSL ℝ z))) z :=
      ((hP_deriv _).comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul _
    rw [h.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, hρ₀_def]
    push_cast
    ring
/-- Fundamental theorem of calculus along rays, averaged against a kernel (used for the mean value
kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): for continuous `ρ` vanishing where
`‖z‖ ≥ 1`, `h ∈ C¹` and `t ≥ 0`,
`∫ ρ(z) h(x₀ + t z) dz = (∫ ρ) h(x₀) + ∫₀ᵗ ∫ ρ(z) Dh(x₀ + σ z)[z] dz dσ`.  Raywise FTC, then
Fubini for the continuous integrand, which vanishes off `[0, t] × B₁(0)`. -/
theorem mvk_integral_ray_fubini : ∀ (n : ℕ) (ρ h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 ≤ t → Continuous ρ → (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) → ContDiff ℝ 1 h → ∫ z, ρ z * h (x₀ + t • z) = (∫ z, ρ z) * h x₀ + ∫ σ in (0 : ℝ)..t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z := by
  intro n ρ h x₀ t ht hρ hρ0 hh
  -- `ρ` vanishes off the compact closed unit ball, so it has compact support.
  have hρs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) 1) fun z hz => hρ0 z ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hDh : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  -- Products of `ρ` with continuous functions are integrable.
  have hint : ∀ g : Rn n → ℝ, Continuous g → Integrable fun z => ρ z * g z := fun g hg =>
    (hρ.mul hg).integrable_of_hasCompactSupport hρs.mul_right
  -- FTC along the ray `σ ↦ x₀ + σ • z`, multiplied by the constant `ρ z`.
  have hftc : ∀ z : Rn n, ∫ σ in (0 : ℝ)..t, ρ z * fderiv ℝ h (x₀ + σ • z) z =
      ρ z * h (x₀ + t • z) - ρ z * h x₀ := by
    intro z
    have hderiv : ∀ σ : ℝ,
        HasDerivAt (fun σ : ℝ => h (x₀ + σ • z)) (fderiv ℝ h (x₀ + σ • z) z) σ := by
      intro σ
      have hray : HasDerivAt (fun σ : ℝ => x₀ + σ • z) z σ := by
        simpa using ((hasDerivAt_id σ).smul_const z).const_add x₀
      exact (hhd (x₀ + σ • z)).hasFDerivAt.comp_hasDerivAt σ hray
    have hcont : Continuous fun σ : ℝ => fderiv ℝ h (x₀ + σ • z) z := by fun_prop
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
        (hcont.intervalIntegrable _ _), zero_smul, add_zero, mul_sub]
  -- The integrand is integrable on `(0, t] × ℝⁿ`: it is continuous and vanishes off the compact
  -- set `[0, t] × B₁(0)`.
  have hF : Integrable
      (Function.uncurry fun (σ : ℝ) (z : Rn n) => ρ z * fderiv ℝ h (x₀ + σ • z) z)
      ((volume.restrict (uIoc (0 : ℝ) t)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hK : IntegrableOn
        (Function.uncurry fun (σ : ℝ) (z : Rn n) => ρ z * fderiv ℝ h (x₀ + σ • z) z)
        (Icc (0 : ℝ) t ×ˢ closedBall (0 : Rn n) 1) (volume.prod volume) :=
      (Continuous.continuousOn (by fun_prop)).integrableOn_compact
        (isCompact_Icc.prod (isCompact_closedBall _ _))
    refine hK.of_forall_sdiff_eq_zero (measurableSet_uIoc.prod MeasurableSet.univ) ?_
    rintro ⟨σ, z⟩ ⟨⟨hσ, -⟩, hnot⟩
    rw [uIoc_of_le ht] at hσ
    have hz : z ∉ closedBall (0 : Rn n) 1 := fun hz => hnot ⟨Ioc_subset_Icc_self hσ, hz⟩
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    simp [hρ0 z hz.le]
  -- Fubini, then integrate the raywise identity over `z`.
  rw [MeasureTheory.intervalIntegral_integral_swap hF]
  simp_rw [hftc]
  rw [integral_sub (hint (fun z => h (x₀ + t • z)) (by fun_prop))
    (hint (fun _ => h x₀) continuous_const), integral_mul_const]
  ring
/-- Green's first identity on `ℝⁿ` against a compactly supported `C¹` function (used for the mean
value kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): if `H` is `C²`, `Ψ` is `C¹` with
compact support and `w = ∇Ψ`, then `∫ DH(z)[w(z)] dz = -∫ ΔH(z) Ψ(z) dz`.  Each coordinate
integration by parts reduces to `∫ DG(z)[v] dz = 0` for a compactly supported `C¹` function `G`,
which holds because `t ↦ ∫ G(z + t v) dz` is constant by translation invariance. -/
theorem mvk_integral_fderiv_grad_eq_neg_laplacian : ∀ (n : ℕ) (H Ψ : Rn n → ℝ) (w : Rn n → Rn n), ContDiff ℝ 2 H → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → (∀ z v : Rn n, fderiv ℝ Ψ z v = inner ℝ (w z) v) → ∫ z, fderiv ℝ H z (w z) = -∫ z, Laplacian.laplacian H z * Ψ z := by
  intro n H Ψ w hH hΨ hΨc hw
  -- For a compactly supported `C¹` function `G` and a direction `v`, `∫ DG(z)[v] dz = 0`:
  -- `t ↦ ∫ G(z + t v) dz` is constant by translation invariance, and its derivative at `0` is
  -- `∫ DG(z)[v] dz` by differentiation under the integral sign.
  have key : ∀ G : Rn n → ℝ, ContDiff ℝ 1 G → HasCompactSupport G → ∀ v : Rn n,
      ∫ z, fderiv ℝ G z v = 0 := by
    intro G hG hGc v
    have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hG' : Continuous fun y => fderiv ℝ G y v :=
      (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨C, hC⟩ := hG'.bounded_above_of_compact_support (hGc.fderiv_apply ℝ v)
    obtain ⟨R, -, hR⟩ := (hGc.fderiv_apply ℝ v).exists_pos_le_norm
    -- For `|t| < 1`, `|DG(z + t v)[v]|` is bounded by `C` times the indicator of `B_{R + |v|}(0)`.
    have hbound : Integrable ((closedBall (0 : Rn n) (R + ‖v‖)).indicator fun _ => C) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    have hb : ∀ z : Rn n, ∀ t ∈ ball (0 : ℝ) 1,
        ‖fderiv ℝ G (z + t • v) v‖ ≤ (closedBall (0 : Rn n) (R + ‖v‖)).indicator (fun _ => C) z := by
      intro z t ht
      by_cases hz : z ∈ closedBall (0 : Rn n) (R + ‖v‖)
      · rw [indicator_of_mem hz]
        exact hC _
      · rw [mem_closedBall, dist_zero_right, not_le] at hz
        rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
        have h1 : ‖t • v‖ ≤ ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.le
        have h2 : ‖z‖ ≤ ‖z + t • v‖ + ‖t • v‖ := by
          calc ‖z‖ = ‖(z + t • v) - t • v‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖z + t • v‖ + ‖t • v‖ := norm_sub_le _ _
        have hRz : R ≤ ‖z + t • v‖ := by linarith
        rw [hR _ hRz, norm_zero]
        exact indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hC 0)) _
    have hdiff : ∀ z : Rn n, ∀ t ∈ ball (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => G (z + t • v)) (fderiv ℝ G (z + t • v) v) t := by
      intro z t _
      have h1 : HasDerivAt (fun t : ℝ => z + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add z
      exact (hGd (z + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have hd : HasDerivAt (fun t : ℝ => ∫ z, G (z + t • v)) (∫ z, fderiv ℝ G (z + (0 : ℝ) • v) v) 0 :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (F := fun (t : ℝ) (z : Rn n) => G (z + t • v))
        (F' := fun (t : ℝ) (z : Rn n) => fderiv ℝ G (z + t • v) v)
        (x₀ := 0) (ball_mem_nhds (0 : ℝ) one_pos)
        (Eventually.of_forall fun t =>
          (hG.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
        (by simpa using hG.continuous.integrable_of_hasCompactSupport hGc)
        ((hG'.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
        (Eventually.of_forall hb) hbound (Eventually.of_forall hdiff)).2
    have hd0 : HasDerivAt (fun t : ℝ => ∫ z, G (z + t • v)) 0 0 := by
      have hconst : (fun t : ℝ => ∫ z, G (z + t • v)) = fun _ => ∫ z, G z :=
        funext fun t => integral_add_right_eq_self G (t • v)
      rw [hconst]
      exact hasDerivAt_const _ _
    simpa using hd.unique hd0
  -- Integration by parts in the direction `v` against `Ψ`, applying `key` to `f Ψ`.
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
  have ibp : ∀ f : Rn n → ℝ, ContDiff ℝ 1 f → ∀ v : Rn n,
      Integrable (fun z => fderiv ℝ f z v * Ψ z) ∧ Integrable (fun z => f z * fderiv ℝ Ψ z v) ∧
        ∫ z, f z * fderiv ℝ Ψ z v = -∫ z, fderiv ℝ f z v * Ψ z := by
    intro f hf v
    have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
    have h1 : Integrable (fun z => fderiv ℝ f z v * Ψ z) :=
      (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hΨ.continuous).integrable_of_hasCompactSupport hΨc.mul_left
    have h2 : Integrable (fun z => f z * fderiv ℝ Ψ z v) :=
      (hf.continuous.mul ((hΨ.continuous_fderiv one_ne_zero).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hΨc.fderiv_apply ℝ v).mul_left
    refine ⟨h1, h2, ?_⟩
    have h3 := key (fun z => f z * Ψ z) (hf.mul hΨ) hΨc.mul_left v
    have h4 : ∀ z, fderiv ℝ (fun z => f z * Ψ z) z v =
        fderiv ℝ f z v * Ψ z + f z * fderiv ℝ Ψ z v := by
      intro z
      rw [show (fun z => f z * Ψ z) = f * Ψ from rfl, fderiv_mul (hfd z) (hΨd z)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    simp only [h4] at h3
    rw [integral_add h1 h2] at h3
    linarith
  -- Second derivatives: `D(DH(·)[v])(z)[v] = D²H(z)[v, v]`.
  have hH1 : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hd2 : ∀ v z : Rn n,
      fderiv ℝ (fun y => fderiv ℝ H y v) z v = iteratedFDeriv ℝ 2 H z ![v, v] := by
    intro v z
    rw [iteratedFDeriv_two_apply,
      fderiv_clm_apply ((hH1.differentiable one_ne_zero) z) (differentiableAt_const v)]
    simp
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  -- `DH(z)[w(z)] = Σᵢ ∂ᵢH(z) ∂ᵢΨ(z)`, expanding `w(z)` in the standard orthonormal basis.
  have hexp : ∀ z, fderiv ℝ H z (w z) = ∑ i, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) := by
    intro z
    conv_lhs => rw [← e.sum_repr' (w z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hw, real_inner_comm (w z) (e i)]
    ring
  -- `ΔH(z) = Σᵢ D²H(z)[eᵢ, eᵢ]`.
  have hlap : ∀ z, Laplacian.laplacian H z * Ψ z =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z := by
    intro z
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis H e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hd2]
  have hfC : ∀ i, ContDiff ℝ 1 (fun y => fderiv ℝ H y (e i)) := fun i => hH1.clm_apply contDiff_const
  calc ∫ z, fderiv ℝ H z (w z) = ∫ z, ∑ i, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) := by
        simp only [hexp]
    _ = ∑ i, ∫ z, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) :=
        integral_finsetSum _ fun i _ => (ibp _ (hfC i) (e i)).2.1
    _ = ∑ i, -∫ z, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z :=
        Finset.sum_congr rfl fun i _ => (ibp _ (hfC i) (e i)).2.2
    _ = -∫ z, ∑ i, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z := by
        rw [integral_finsetSum _ fun i _ => (ibp _ (hfC i) (e i)).1, Finset.sum_neg_distrib]
    _ = -∫ z, Laplacian.laplacian H z * Ψ z := by
        simp only [hlap]
/-- **Laplacian of an affinely rescaled `C²` function** (scaling step in the mean value property
behind Weyl's lemma, used for Simon Ch. 5, Lemma 3.1, p. 114).  If `h : ℝⁿ → ℝ` is `C²`, then
`Δ(y ↦ h(x₀ + σ y))(z) = σ² Δh(x₀ + σ z)` for all `x₀, z ∈ ℝⁿ` and `σ ∈ ℝ`.
Proof: `y ↦ h(x₀ + σ y) = h₀ ∘ L` with `h₀ = h(x₀ + ·)` of class `C²` and `L = σ • id`.  Expanding
both Laplacians in the standard orthonormal basis `(eᵢ)`, it suffices that
`D²(h₀ ∘ L)(z)[eᵢ, eᵢ] = D²h₀(σ z)[σ eᵢ, σ eᵢ] = σ² D²h₀(σ z)[eᵢ, eᵢ]` (composition with a linear
map on the right, then multilinearity) and `D²h₀(σ z) = D²h(x₀ + σ z)` (translation). -/
theorem mvk_laplacian_comp_add_smul : ∀ (n : ℕ) (h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), ContDiff ℝ 2 h → ∀ z : Rn n, Laplacian.laplacian (fun y => h (x₀ + σ • y)) z = σ ^ 2 * Laplacian.laplacian h (x₀ + σ • z) := by
  intro n h x₀ σ hh z
  -- Step 1: `y ↦ h (x₀ + σ • y) = h₀ ∘ L`, where `h₀ y = h (x₀ + y)` is `C²` and `L = σ • id`.
  have h₀ : ContDiff ℝ 2 (fun y : Rn n => h (x₀ + y)) := hh.comp (contDiff_const.add contDiff_id)
  set L : Rn n →L[ℝ] Rn n := σ • ContinuousLinearMap.id ℝ (Rn n)
  have hcomp : (fun y => h (x₀ + σ • y)) = (fun y => h (x₀ + y)) ∘ L := by
    ext y
    simp [L]
  -- Step 2: expand both Laplacians in the standard orthonormal basis `eᵢ`.
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e, Finset.mul_sum, hcomp]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Step 3: `D²(h₀ ∘ L)(z)[eᵢ, eᵢ] = D²h₀(σ z)[σ eᵢ, σ eᵢ] = σ² D²h₀(σ z)[eᵢ, eᵢ]`.
  rw [L.iteratedFDeriv_comp_right h₀ z le_rfl, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hsmul : (fun j => L (![e i, e i] j)) = fun j => σ • ![e i, e i] j := by
    ext1 j
    simp [L]
  rw [hsmul, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  -- Step 4: `D²h₀(σ z) = D²h(x₀ + σ z)`.
  rw [iteratedFDeriv_comp_add_left]
  simp [L]
/-- Rescaling and reflection of the convolution integral for an even kernel (used for the mean
value kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): for `t > 0` and `ρ` even,
`∫ t⁻ⁿ ρ(t⁻¹ y) h(x₀ − y) dy = ∫ ρ(z) h(x₀ + t z) dz`.  No integrability is needed: the Haar
scaling formula, constant factors and the reflection `z ↦ −z` hold for the Bochner integral of an
arbitrary function. -/
theorem mvk_integral_rescale_reflect : ∀ (n : ℕ) (ρ h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 < t → (∀ z : Rn n, ρ (-z) = ρ z) → ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y) = ∫ z, ρ z * h (x₀ + t • z) := by
  intro n ρ h x₀ t ht hρ
  -- The integrand is `f (t⁻¹ • y)` for `f z = t⁻ⁿ ρ(z) h(x₀ − t z)`, since `t • t⁻¹ • y = y`.
  calc ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y)
      = ∫ y, (fun z : Rn n => t⁻¹ ^ n * (ρ z * h (x₀ - t • z))) (t⁻¹ • y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [smul_inv_smul₀ ht.ne', mul_assoc]
    -- Scaling of Lebesgue measure: `∫ f (t⁻¹ • y) dy = tⁿ ∫ f`, since `finrank ℝ ℝⁿ = n`.
    _ = t ^ n • ∫ z, t⁻¹ ^ n * (ρ z * h (x₀ - t • z)) := by
        have hs := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rn n))
          (fun z : Rn n => t⁻¹ ^ n * (ρ z * h (x₀ - t • z))) ht.le
        rw [finrank_euclideanSpace_fin] at hs
        exact hs
    -- Pull out the constant `t⁻ⁿ` and cancel `tⁿ t⁻ⁿ = 1`.
    _ = ∫ z, ρ z * h (x₀ - t • z) := by
        rw [integral_const_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht.ne',
          one_pow, one_mul]
    -- `ρ` is even and `t • -z = -(t • z)`.
    _ = ∫ z, ρ (-z) * h (x₀ + t • -z) := by
        congr 1
        ext z
        rw [hρ, smul_neg, sub_eq_add_neg]
    -- Lebesgue measure is invariant under `z ↦ -z`.
    _ = ∫ z, ρ z * h (x₀ + t • z) := integral_neg_eq_self (fun z => ρ z * h (x₀ + t • z)) volume
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), mean value step of Weyl's lemma: integration by parts
of the radial derivative against the kernel potential.  If `h` is `C²`, `σ ≠ 0`, and the `C¹`
function `Ψ` vanishes for `‖z‖ ≥ 1` and has `DΨ(z)[v] = ρ(z) ⟨z, v⟩`, then
`∫ ρ(z) Dh(x₀ + σ z)[z] dz = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz`.  For `H(y) = h(x₀ + σ y)` the chain rule
gives `ρ(z) Dh(x₀ + σ z)[z] = σ⁻¹ DH(z)[ρ(z) z]`.  Green's first identity
(`mvk_integral_fderiv_grad_eq_neg_laplacian`, applied to the compactly supported `Ψ` with
gradient `ρ(z) z`) gives `∫ DH(z)[ρ(z) z] dz = -∫ ΔH(z) Ψ(z) dz`, and
`ΔH(z) = σ² Δh(x₀ + σ z)` (`mvk_laplacian_comp_add_smul`). -/
theorem mvk_integral_radial_fderiv_eq_neg_laplacian : ∀ (n : ℕ) (ρ Ψ h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), σ ≠ 0 → ContDiff ℝ 2 h → ContDiff ℝ 1 Ψ → (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) → (∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v) → ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = -σ * ∫ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z := by
  intro n ρ Ψ h x₀ σ hσ hh hΨ hΨ1 hdΨ
  -- Step 1: `H(y) = h(x₀ + σ y)` is `C²`, with `DH(z)[v] = σ Dh(x₀ + σ z)[v]`.
  have hH : ContDiff ℝ 2 (fun y : Rn n => h (x₀ + σ • y)) :=
    hh.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have hdH : ∀ z v : Rn n,
      fderiv ℝ (fun y => h (x₀ + σ • y)) z v = σ * fderiv ℝ h (x₀ + σ • z) v := by
    intro z v
    have hA : HasFDerivAt (fun y : Rn n => x₀ + σ • y) (σ • ContinuousLinearMap.id ℝ (Rn n)) z :=
      ((hasFDerivAt_id z).const_smul σ).const_add x₀
    have hc : HasFDerivAt (fun y => h (x₀ + σ • y))
        ((fderiv ℝ h (x₀ + σ • z)).comp (σ • ContinuousLinearMap.id ℝ (Rn n))) z :=
      (hh.differentiable (by norm_num) (x₀ + σ • z)).hasFDerivAt.comp z hA
    rw [hc.fderiv]
    simp
  -- Step 2: `Ψ` vanishes off the closed unit ball, so it has compact support.
  have hΨc : HasCompactSupport Ψ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
      hΨ1 z (le_of_lt (by simpa using hz))
  -- Step 3: `w(z) = ρ(z) z` is the gradient of `Ψ`.
  have hw : ∀ z v : Rn n, fderiv ℝ Ψ z v = inner ℝ (ρ z • z) v := fun z v => by
    rw [hdΨ, real_inner_smul_left]
  -- Step 4: `ρ(z) Dh(x₀ + σ z)[z] = σ⁻¹ DH(z)[w(z)]`.
  have hpt : ∀ z, ρ z * fderiv ℝ h (x₀ + σ • z) z =
      σ⁻¹ * fderiv ℝ (fun y => h (x₀ + σ • y)) z (ρ z • z) := fun z => by
    rw [hdH, map_smul, smul_eq_mul, inv_mul_cancel_left₀ hσ]
  -- Steps 5–6: Green's first identity for `H`, `Ψ`, `w`, and `ΔH(z) = σ² Δh(x₀ + σ z)`.
  have hG := Submission.mvk_integral_fderiv_grad_eq_neg_laplacian n
    (fun y => h (x₀ + σ • y)) Ψ (fun z => ρ z • z) hH hΨ hΨc hw
  have hL := Submission.mvk_laplacian_comp_add_smul n h x₀ σ hh
  -- Step 7: pull out the constants.
  calc ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z
      = ∫ z, σ⁻¹ * fderiv ℝ (fun y => h (x₀ + σ • y)) z (ρ z • z) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = σ⁻¹ * -∫ z, Laplacian.laplacian (fun y => h (x₀ + σ • y)) z * Ψ z := by
        rw [integral_const_mul, hG]
    _ = σ⁻¹ * -∫ z, σ ^ 2 * (Laplacian.laplacian h (x₀ + σ • z) * Ψ z) := by
        simp only [hL, mul_assoc]
    _ = -σ * ∫ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z := by
        rw [integral_const_mul]
        field_simp
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), mean value step of Weyl's lemma: there is a smooth
kernel `ρ` vanishing off the open unit ball with `∫ t⁻ⁿ ρ(t⁻¹ y) h(x₀ - y) dy = h(x₀)` for every
`t > 0` and every `C²` function `h` with `Δh = 0` on `B_t(x₀)`.  Take `ρ` (even, `∫ ρ = 1`) and
its potential `Ψ` (`DΨ(z)[v] = ρ(z) ⟨z, v⟩`, `Ψ = 0` off the unit ball); rescaling and reflecting
turn the left side into `∫ ρ(z) h(x₀ + t z) dz`, the fundamental theorem of calculus along rays
and Fubini give `h(x₀) + ∫₀ᵗ I(σ) dσ` with `I(σ) = ∫ ρ(z) Dh(x₀ + σ z)[z] dz`, and integration by
parts against `Ψ` gives `I(σ) = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz = 0` for `0 < σ ≤ t`. -/
theorem exists_smooth_mean_value_kernel : ∀ n : ℕ, 1 ≤ n → ∃ ρ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ ∀ (h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 < t → ContDiff ℝ 2 h → (∀ y ∈ closedBall x₀ t, Laplacian.laplacian h y = 0) → ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y) = h x₀ := by
  intro n _
  -- Step 1: the kernel `ρ` and its potential `Ψ`.
  obtain ⟨ρ, Ψ, hρ, hΨ, hρ1, hΨ1, hρneg, hρint, hdΨ⟩ := Submission.mvk_exists_kernel_potential n
  refine ⟨ρ, hρ, hρ1, fun h x₀ t ht hh hΔ => ?_⟩
  -- Step 2: `I(σ) = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz = 0` for `0 < σ ≤ t`, since `Ψ(z) = 0` for
  -- `‖z‖ ≥ 1` and `x₀ + σ z ∈ B_t(x₀)` for `‖z‖ < 1`.
  have hI : ∀ σ ∈ Ioc (0 : ℝ) t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = 0 := by
    rintro σ ⟨hσ, hσt⟩
    rw [Submission.mvk_integral_radial_fderiv_eq_neg_laplacian n ρ Ψ h x₀ σ hσ.ne' hh
      (hΨ.of_le (by exact_mod_cast le_top)) hΨ1 hdΨ]
    have hzero : ∀ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z = 0 := by
      intro z
      rcases le_or_gt 1 ‖z‖ with hz | hz
      · rw [hΨ1 z hz, mul_zero]
      · have hmem : x₀ + σ • z ∈ closedBall x₀ t := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hσ.le]
          nlinarith [norm_nonneg z]
        rw [hΔ _ hmem, zero_mul]
    simp only [hzero, integral_zero, mul_zero]
  -- Step 3: so `∫₀ᵗ I(σ) dσ = 0`, the endpoint `σ = 0` being outside `(0, t]`.
  have hint : ∫ σ in (0 : ℝ)..t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = 0 :=
    intervalIntegral.integral_zero_ae (Eventually.of_forall fun σ hσ =>
      hI σ (by rwa [uIoc_of_le ht.le] at hσ))
  -- Step 4: rescale and reflect, then integrate along rays:
  -- `∫ ρ(z) h(x₀ + t z) dz = (∫ ρ) h(x₀) + ∫₀ᵗ I(σ) dσ = h(x₀)`.
  rw [Submission.mvk_integral_rescale_reflect n ρ h x₀ t ht hρneg,
    Submission.mvk_integral_ray_fubini n ρ h x₀ t ht.le hρ.continuous hρ1
      (hh.of_le (by norm_num)), hρint, one_mul, hint, add_zero]

/-- **Local harmonic representatives of a weakly harmonic function** (step 5 of the proof of
Weyl's lemma, used for Simon Ch. 5, Lemma 3.1).  Let `w` be integrable on `B = B̆₁(0)` with
`∫_B w Δζ = 0` for every `ζ ∈ C^∞_c(B)`, and let `0 < ε < 1/2`.  Then some `v`, harmonic near every
point of `B̆_{1-ε}(0)`, agrees with `w` a.e. on `B̆_{1-2ε}(0)`.

Take `v(x) = ∫_B κ(x - y) w(y) dy` with the mean-value kernel scaled to `κ(z) = ε⁻ⁿ ρ(z/ε)`; it
is harmonic on `B̆_{1-ε}(0)`.  For normalized bumps `ψⱼ` supported in `B̆_{sⱼ}(0)`, `sⱼ = ε/(j+2)`,
the mollifications `vⱼ = ψⱼ ⋆ 1_B w` are harmonic on `B̆_{1-ε}(0)` too, so for `|x₀| < 1 - 2ε` the
mean value property and Fubini give `vⱼ(x₀) = (ψⱼ ⋆ v)(x₀)`.  As `j → ∞` this tends to `v(x₀)` by
continuity of `v`, and to `w(x₀)` for a.e. `x₀` by Lebesgue differentiation. -/
theorem ball_weakly_harmonic_local_representative : ∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0) → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ v : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd v (ball (0 : Rn n) (1 - ε)) ∧ ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (1 - 2 * ε))), v x = w x := by
  -- Steps 3 and 6: normalized bumps `ψⱼ` vanishing off `B̆_{sⱼ}(0)`, `sⱼ = δ/(j+2) → 0`, with
  -- `ψⱼ ⋆ v → v` pointwise for continuous `v`, and `ψⱼ ⋆ 1_B w → w` a.e. on `B`.
  have hA : ∀ n : ℕ, ∀ δ : ℝ, 0 < δ → ∃ ψ : ℕ → Rn n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) ∧ (∀ j, ∀ z : Rn n, δ ≤ ‖z‖ → ψ j z = 0) ∧ (∀ v : Rn n → ℝ, Continuous v → ∀ x : Rn n, Tendsto (fun j => ∫ b, ψ j b * v (x - b)) atTop (𝓝 (v x))) ∧ ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y) atTop (𝓝 (w x)) := by
    intro n δ hδ
    -- The radii `sⱼ = δ/(j+2)` lie in `(0, δ)` and tend to `0`.
    set s : ℕ → ℝ := fun j => δ / ((j : ℝ) + 2) with hs
    have hs_pos : ∀ j, 0 < s j := fun j => div_pos hδ (by positivity)
    have hs_lt : ∀ j, s j < δ := by
      intro j
      simp only [s]
      rw [div_lt_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hs_tend : Tendsto s atTop (𝓝 0) := by
      have h1 : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact h1.const_div_atTop δ
    -- `φⱼ` is the bump equal to `1` on `B_{sⱼ/2}(0)` with support `B̆_{sⱼ}(0)`; `ψⱼ = φⱼ / ∫ φⱼ`.
    let φ : ℕ → ContDiffBump (0 : Rn n) := fun j =>
      ⟨s j / 2, s j, half_pos (hs_pos j), half_lt_self (hs_pos j)⟩
    have hφint : ∀ j, Integrable (φ j) volume := fun j =>
      (φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport
    have hIpos : ∀ j, 0 < ∫ x, φ j x := by
      intro j
      refine (integral_pos_iff_support_of_nonneg (fun x => (φ j).nonneg) (hφint j)).mpr ?_
      rw [(φ j).support_eq]
      exact measure_ball_pos volume 0 (φ j).rOut_pos
    set ψ : ℕ → Rn n → ℝ := fun j x => φ j x / ∫ y, φ j y with hψdef
    have hψ_nonneg : ∀ j x, 0 ≤ ψ j x := fun j x => div_nonneg (φ j).nonneg (hIpos j).le
    have hψ_int1 : ∀ j, ∫ x, ψ j x = 1 := by
      intro j
      simp only [ψ]
      rw [integral_div]
      exact div_self (hIpos j).ne'
    have hψ_supp : ∀ j, Function.support (ψ j) = ball (0 : Rn n) (s j) := by
      intro j
      have : ψ j = fun x => φ j x / ∫ y, φ j y := rfl
      rw [this, Function.support_div, (φ j).support_eq, Function.support_const (hIpos j).ne',
        inter_univ]
    -- `|B_{sⱼ/2}(0)| ≤ ∫ φⱼ` and `|B_{sⱼ}(0)| = 2ᵈ |B_{sⱼ/2}(0)|`, so `|ψⱼ| ≤ 2ᵈ / |B_{sⱼ}(0)|`.
    have hIge : ∀ j, volume.real (closedBall (0 : Rn n) (s j / 2)) ≤ ∫ x, φ j x := by
      intro j
      calc volume.real (closedBall (0 : Rn n) (s j / 2))
          = ∫ x in closedBall (0 : Rn n) (s j / 2), (1 : ℝ) := by simp
        _ = ∫ x in closedBall (0 : Rn n) (s j / 2), φ j x := by
            refine setIntegral_congr_fun measurableSet_closedBall (fun x hx => ?_)
            exact ((φ j).one_of_mem_closedBall hx).symm
        _ ≤ ∫ x, φ j x :=
            setIntegral_le_integral (hφint j) (Eventually.of_forall (fun x => (φ j).nonneg))
    have hvol : ∀ j, volume.real (closedBall (0 : Rn n) (s j))
        = 2 ^ Module.finrank ℝ (Rn n) * volume.real (closedBall (0 : Rn n) (s j / 2)) := by
      intro j
      rw [Measure.addHaar_real_closedBall' _ _ (hs_pos j).le,
        Measure.addHaar_real_closedBall' _ _ (half_pos (hs_pos j)).le, ← mul_assoc, ← mul_pow]
      congr 2
      ring
    have hvolpos : ∀ j, 0 < volume.real (closedBall (0 : Rn n) (s j / 2)) := by
      intro j
      exact ENNReal.toReal_pos (measure_closedBall_pos _ _ (half_pos (hs_pos j))).ne'
        measure_closedBall_lt_top.ne
    have hψ_bound : ∀ j x, |ψ j x| ≤
        2 ^ Module.finrank ℝ (Rn n) / volume.real (closedBall (0 : Rn n) (s j)) := by
      intro j x
      rw [abs_of_nonneg (hψ_nonneg j x), hvol j]
      have h2 : (0 : ℝ) < 2 ^ Module.finrank ℝ (Rn n) := by positivity
      rw [div_mul_cancel_left₀ h2.ne']
      calc ψ j x = φ j x / ∫ y, φ j y := rfl
        _ ≤ 1 / ∫ y, φ j y := by
            gcongr
            · exact (hIpos j).le
            · exact (φ j).le_one
        _ ≤ 1 / volume.real (closedBall (0 : Rn n) (s j / 2)) := by
            gcongr
            · exact hvolpos j
            · exact hIge j
        _ = (volume.real (closedBall (0 : Rn n) (s j / 2)))⁻¹ := one_div _
    refine ⟨ψ, ?_, ?_, ?_, ?_⟩
    · -- `ψⱼ` is `C^∞`.
      intro j
      exact (φ j).contDiff.div_const _
    · -- `ψⱼ(z) = 0` for `|z| ≥ δ > sⱼ`.
      intro j z hz
      by_contra hne
      have hmem : z ∈ Function.support (ψ j) := hne
      rw [hψ_supp j, mem_ball, dist_zero_right] at hmem
      linarith [hs_lt j]
    · -- Approximate identity: `ψⱼ ⋆ v → v` at every point for continuous `v`.
      intro v hv x
      have hsmall : Tendsto (fun j => Function.support (ψ j)) atTop (𝓝 (0 : Rn n)).smallSets := by
        rw [nhds_basis_ball.smallSets.tendsto_right_iff]
        intro r hr
        have := (tendsto_order.1 hs_tend).2 r hr
        filter_upwards [this] with j hj
        rw [hψ_supp j]
        exact ball_subset_ball hj.le
      have h := convolution_tendsto_right (μ := volume) (Eventually.of_forall hψ_nonneg)
        (Eventually.of_forall hψ_int1) hsmall (Eventually.of_forall fun _ => hv.aestronglyMeasurable)
        ((hv.tendsto x).comp tendsto_snd) tendsto_const_nhds
      simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h
    · -- Lebesgue differentiation for `W = 1_B w` along the closed balls `B_{sⱼ}(x)`, with
      -- kernels `y ↦ ψⱼ(x - y)` bounded by `2ᵈ / |B_{sⱼ}(x)|`.
      intro w hw
      set W : Rn n → ℝ := (ball (0 : Rn n) 1).indicator w with hWdef
      have hWi : Integrable W := (integrable_indicator_iff measurableSet_ball).mpr hw
      have hleb := (Besicovitch.vitaliFamily (volume : Measure (Rn n))).ae_tendsto_average_norm_sub
        hWi.locallyIntegrable
      filter_upwards [ae_restrict_of_ae hleb, ae_restrict_mem measurableSet_ball] with x hx hxB
      have hs' : Tendsto s atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨hs_tend, Eventually.of_forall hs_pos⟩
      have hav := (hx.comp (Besicovitch.tendsto_filterAt volume x)).comp hs'
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub
        (μ := volume) (a := fun j => closedBall x (s j)) (f := W) (c := W x)
        (g := fun j y => ψ j (x - y)) (2 ^ Module.finrank ℝ (Rn n)) hav
        (Eventually.of_forall fun j => hWi.integrableOn)
        (by
          refine tendsto_const_nhds.congr (fun j => ?_)
          rw [integral_sub_left_eq_self (fun y => ψ j y) volume x, hψ_int1 j])
        (Eventually.of_forall fun j => by
          intro y hy
          have hmem : x - y ∈ Function.support (ψ j) := hy
          rw [hψ_supp j, mem_ball, dist_zero_right] at hmem
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hmem.le)
        (Eventually.of_forall fun j y => by
          rw [Measure.addHaar_real_closedBall_center]
          exact hψ_bound j (x - y))
      have hconv : ∀ j, ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y = ∫ y, ψ j (x - y) • W y := by
        intro j
        rw [← integral_indicator measurableSet_ball]
        congr 1
        funext y
        simp only [smul_eq_mul, W]
        exact Set.indicator_mul_right _ (fun y => ψ j (x - y)) w
      have hWx : W x = w x := Set.indicator_of_mem hxB w
      simp_rw [hconv]
      rw [← hWx]
      exact key
  -- Step 5: Fubini exchanges two ball mollifications of `w`:
  -- `∫ κ(a) (ψ ⋆ 1_B w)(x₀ - a) da = ∫ ψ(b) (κ ⋆ 1_B w)(x₀ - b) db`.
  have hB : ∀ n : ℕ, ∀ κ ψ w : Rn n → ℝ, Continuous κ → HasCompactSupport κ → Continuous ψ → HasCompactSupport ψ → IntegrableOn w (ball (0 : Rn n) 1) → ∀ x₀ : Rn n, ∫ a, κ a * ∫ y in ball (0 : Rn n) 1, ψ (x₀ - a - y) * w y = ∫ b, ψ b * ∫ y in ball (0 : Rn n) 1, κ (x₀ - b - y) * w y := by
    intro n κ ψ w hκc hκs hψc hψs hw x₀
    set W : Rn n → ℝ := (ball (0 : Rn n) 1).indicator w with hWdef
    have hWi : Integrable W := (integrable_indicator_iff measurableSet_ball).mpr hw
    have conv : ∀ (φ : Rn n → ℝ) (x : Rn n),
        ∫ y in ball (0 : Rn n) 1, φ (x - y) * w y = ∫ t, φ t * W (x - t) := by
      intro φ x
      rw [← integral_indicator measurableSet_ball]
      have h1 : (ball (0 : Rn n) 1).indicator (fun y => φ (x - y) * w y)
          = fun y => φ (x - y) * W y := by
        funext y
        exact Set.indicator_mul_right _ (fun y => φ (x - y)) w
      rw [h1, ← integral_sub_left_eq_self _ volume x]
      simp only [sub_sub_cancel]
    simp_rw [conv]
    -- `(a, t) ↦ κ(a) ψ(t) W(x₀ - a - t)` is integrable on `ℝⁿ × ℝⁿ`: multiply the convolution
    -- integrand `ψ(t) W(a - t)` by the bounded `κ(x₀ - a)`, then substitute `a ↦ x₀ - a`.
    obtain ⟨Cκ, hCκ⟩ := hκc.bounded_above_of_compact_support hκs
    have hG : Integrable (fun p : Rn n × Rn n => κ (x₀ - p.1) * (ψ p.2 * W (p.1 - p.2)))
        (volume.prod volume) := by
      have h0 : Integrable (fun p : Rn n × Rn n => ψ p.2 * W (p.1 - p.2)) (volume.prod volume) := by
        have := (hψc.integrable_of_hasCompactSupport hψs : Integrable ψ volume).convolution_integrand
          (ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hWi
        simpa using this
      refine h0.bdd_mul (c := Cκ) ?_ ?_
      · exact ((hκc.comp (continuous_const.sub continuous_fst))).aestronglyMeasurable
      · exact Eventually.of_forall (fun p => hCκ _)
    have hR : MeasurePreserving (fun p : Rn n × Rn n => (x₀ - p.1, p.2))
        (volume.prod volume) (volume.prod volume) :=
      (Measure.measurePreserving_sub_left volume x₀).prod (MeasurePreserving.id volume)
    have hF : Integrable (Function.uncurry fun a t => κ a * (ψ t * W (x₀ - a - t)))
        (volume.prod volume) := by
      have := (hR.integrable_comp hG.aestronglyMeasurable).mpr hG
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp [Function.uncurry, sub_sub_cancel]
    calc ∫ a, κ a * ∫ t, ψ t * W (x₀ - a - t)
        = ∫ a, ∫ t, κ a * (ψ t * W (x₀ - a - t)) := by
          congr 1; funext a; rw [integral_const_mul]
      _ = ∫ t, ∫ a, κ a * (ψ t * W (x₀ - a - t)) := integral_integral_swap hF
      _ = ∫ b, ψ b * ∫ t, κ t * W (x₀ - b - t) := by
          congr 1; funext b; rw [← integral_const_mul]
          congr 1; funext a
          rw [sub_right_comm x₀ a b]; ring
  intro n hn w hint hlap ε hε hε2
  -- Step 1: the mean-value kernel `ρ`, scaled to `κ(z) = ε⁻ⁿ ρ(z/ε)`, vanishes for `|z| ≥ ε`.
  obtain ⟨ρ, hρs, hρv, hρm⟩ := Submission.exists_smooth_mean_value_kernel n hn
  set κ : Rn n → ℝ := fun z => ε⁻¹ ^ n * ρ (ε⁻¹ • z) with hκdef
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ :=
    contDiff_const.mul (hρs.comp (contDiff_const_smul _))
  have hκv : ∀ z : Rn n, ε ≤ ‖z‖ → κ z = 0 := by
    intro z hz
    have h1 : 1 ≤ ‖ε⁻¹ • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), inv_mul_eq_div,
        le_div_iff₀ hε]
      linarith
    simp only [κ, hρv _ h1, mul_zero]
  have hcs : ∀ (φ : Rn n → ℝ), (∀ z : Rn n, ε ≤ ‖z‖ → φ z = 0) → HasCompactSupport φ := by
    intro φ hφ
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) ε) (fun z hz => hφ z ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  -- Step 2: `v = κ ⋆ 1_B w` is `C^∞` with `Δv = 0` on `B̆_{1-ε}(0)`, hence harmonic there.
  obtain ⟨hvs, hvl⟩ :=
    Submission.ball_convolution_contDiff_laplacian_eq_zero n hn w hint hlap κ ε hκs hκv
  set v : Rn n → ℝ := fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y with hvdef
  have h2top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    refine ⟨hvs.contDiffAt.of_le h2top, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hvl y hy
  -- Step 4: for `|x₀| < 1 - 2ε`, `vⱼ = ψⱼ ⋆ 1_B w` is harmonic on `B_ε(x₀) ⊆ B̆_{1-ε}(0)`, so the
  -- mean value property and step 5 give `vⱼ(x₀) = (ψⱼ ⋆ v)(x₀)`.
  obtain ⟨ψ, hψs, hψv, hψc, hψa⟩ := hA n ε hε
  have key : ∀ x₀ ∈ ball (0 : Rn n) (1 - 2 * ε), ∀ j : ℕ,
      (∫ y in ball (0 : Rn n) 1, ψ j (x₀ - y) * w y) = ∫ b, ψ j b * v (x₀ - b) := by
    intro x₀ hx₀ j
    obtain ⟨hvjs, hvjl⟩ :=
      Submission.ball_convolution_contDiff_laplacian_eq_zero n hn w hint hlap (ψ j) ε (hψs j)
        (hψv j)
    have hlapj : ∀ y ∈ closedBall x₀ ε,
        Laplacian.laplacian (fun x => ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y) y = 0 := by
      intro y hy
      apply hvjl
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_zero_right] at hx₀
      rw [mem_closedBall, dist_eq_norm] at hy
      calc ‖y‖ = ‖(y - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x₀‖ + ‖x₀‖ := norm_add_le _ _
        _ < 1 - ε := by linarith
    have hmvp := hρm (fun x => ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y) x₀ ε hε
      (hvjs.of_le h2top) hlapj
    have hswap := hB n κ (ψ j) w hκs.continuous (hcs κ hκv)
      (hψs j).continuous (hcs (ψ j) (hψv j)) hint x₀
    rw [← hmvp]
    exact hswap
  -- Step 7: for a.e. `x₀ ∈ B̆_{1-2ε}(0)`, `vⱼ(x₀) = (ψⱼ ⋆ v)(x₀)` tends both to `w(x₀)` and,
  -- by continuity of `v`, to `v(x₀)`.
  have hae := hψa w hint
  have hae' : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (1 - 2 * ε))),
      Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y) atTop (𝓝 (w x)) :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hae
  filter_upwards [hae', ae_restrict_mem (measurableSet_ball :
    MeasurableSet (ball (0 : Rn n) (1 - 2 * ε)))] with x hx hxm
  have hlim1 : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, ψ j (x - y) * w y) atTop (𝓝 (v x)) := by
    have := hψc v hvs.continuous x
    refine this.congr (fun j => ?_)
    exact (key x hxm j).symm
  exact tendsto_nhds_unique hlim1 hx
/-- **Gluing local harmonic representatives on the unit ball** (the patching step of Weyl's lemma).
If for every `ε ∈ (0, 1/2)` some `v_ε` is harmonic near every point of `B̆_{1-ε}(0)` and agrees with
`w` almost everywhere on `B̆_{1-2ε}(0)`, then some `u` is harmonic near every point of `B̆₁(0)` and
agrees with `w` almost everywhere on `B̆₁(0)`.
Proof: two representatives `v_ε, v_ε'` are continuous and a.e. equal on the open ball
`B̆_{1-2 max(ε, ε')}(0)`, hence equal there.  So `u(x) = v_{(1-|x|)/4}(x)` coincides with
`v_{ε₀}`, `ε₀ = (1-|x₀|)/4`, on `B̆_{ε₀}(x₀)` and is harmonic at `x₀`; and `u(x) = v_{1/(m+3)}(x)`
as soon as `1/(m+3) < (1-|x|)/4`, so `u = w` off a countable union of null sets. -/
theorem ball_harmonic_patching : ∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ v : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd v (ball (0 : Rn n) (1 - ε)) ∧ ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (1 - 2 * ε))), v x = w x) → ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball (0 : Rn n) 1) ∧ ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), u x = w x := by
  intro n _ w hw
  -- A representative `v ε` for every `ε` (any function outside `(0, 1/2)`).
  have hw' : ∀ ε : ℝ, ∃ v : Rn n → ℝ, 0 < ε → ε < 1 / 2 →
      InnerProductSpace.HarmonicOnNhd v (ball (0 : Rn n) (1 - ε)) ∧
        ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) (1 - 2 * ε))), v x = w x := by
    intro ε
    by_cases h : 0 < ε ∧ ε < 1 / 2
    · obtain ⟨v, hv⟩ := hw ε h.1 h.2
      exact ⟨v, fun _ _ => hv⟩
    · exact ⟨w, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose v hv using hw'
  -- Compatibility: two representatives agree everywhere on `B̆_{1 - 2 max(ε, ε')}(0)`.
  have compat : ∀ ε ε' : ℝ, 0 < ε → ε < 1 / 2 → 0 < ε' → ε' < 1 / 2 →
      ∀ x ∈ ball (0 : Rn n) (1 - 2 * max ε ε'), v ε x = v ε' x := by
    intro ε ε' hε hε2 hε' hε'2
    have hU : ball (0 : Rn n) (1 - 2 * max ε ε') ⊆ ball 0 (1 - 2 * ε) :=
      ball_subset_ball (by linarith [le_max_left ε ε'])
    have hU' : ball (0 : Rn n) (1 - 2 * max ε ε') ⊆ ball 0 (1 - 2 * ε') :=
      ball_subset_ball (by linarith [le_max_right ε ε'])
    have hc : ContinuousOn (v ε) (ball (0 : Rn n) (1 - 2 * max ε ε')) :=
      (hv ε hε hε2).1.continuousOn.mono (hU.trans (ball_subset_ball (by linarith)))
    have hc' : ContinuousOn (v ε') (ball (0 : Rn n) (1 - 2 * max ε ε')) :=
      (hv ε' hε' hε'2).1.continuousOn.mono (hU'.trans (ball_subset_ball (by linarith)))
    have h1 : v ε =ᵐ[volume.restrict (ball (0 : Rn n) (1 - 2 * max ε ε'))] w :=
      ae_restrict_of_ae_restrict_of_subset hU (hv ε hε hε2).2
    have h2 : v ε' =ᵐ[volume.restrict (ball (0 : Rn n) (1 - 2 * max ε ε'))] w :=
      ae_restrict_of_ae_restrict_of_subset hU' (hv ε' hε' hε'2).2
    exact fun x hx => Measure.eqOn_open_of_ae_eq (h1.trans h2.symm) isOpen_ball hc hc' hx
  -- The patched function `u(x) = v_{(1 - |x|)/4}(x)`.
  refine ⟨fun x => v ((1 - ‖x‖) / 4) x, ?_, ?_⟩
  · -- Near `x₀`, `u = v_{ε₀}` with `ε₀ = (1 - |x₀|)/4`.
    intro x₀ hx₀
    rw [mem_ball_zero_iff] at hx₀
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 - ‖x₀‖ := ⟨_, rfl⟩
    have hε₀ : 0 < d / 4 := by linarith
    have hε₀' : d / 4 < 1 / 2 := by linarith [norm_nonneg x₀]
    have heq : (fun x => v ((1 - ‖x‖) / 4) x) =ᶠ[𝓝 x₀] v (d / 4) := by
      filter_upwards [ball_mem_nhds x₀ hε₀] with x hx
      rw [mem_ball_iff_norm] at hx
      have h1 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := norm_sub_norm_le x x₀
      have h2 : ‖x₀‖ - ‖x‖ ≤ ‖x₀ - x‖ := norm_sub_norm_le x₀ x
      rw [norm_sub_rev] at h2
      have hex : 0 < (1 - ‖x‖) / 4 := by linarith
      have hex' : (1 - ‖x‖) / 4 < 1 / 2 := by linarith [norm_nonneg x]
      refine compat _ _ hex hex' hε₀ hε₀' x ?_
      rw [mem_ball_zero_iff]
      have hmax : max ((1 - ‖x‖) / 4) (d / 4) < 5 * d / 16 :=
        max_lt (by linarith) (by linarith)
      linarith
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).2
      ((hv (d / 4) hε₀ hε₀').1 x₀ (by rw [mem_ball_zero_iff]; linarith))
  · -- Off the null set where some `v_{1/(m+3)}` differs from `w`, `u = w`.
    have hmem : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 3) ∧ 1 / ((m : ℝ) + 3) < 1 / 2 := by
      intro m
      have hm : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ⟨by positivity, one_div_lt_one_div_of_lt (by norm_num) (by linarith)⟩
    have hall : ∀ᵐ x ∂(volume : Measure (Rn n)), ∀ m : ℕ,
        x ∈ ball (0 : Rn n) (1 - 2 * (1 / ((m : ℝ) + 3))) → v (1 / ((m : ℝ) + 3)) x = w x := by
      rw [ae_all_iff]
      intro m
      exact (ae_restrict_iff' measurableSet_ball).1 (hv _ (hmem m).1 (hmem m).2).2
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hall] with x hx hxB
    show v ((1 - ‖x‖) / 4) x = w x
    rw [mem_ball_zero_iff] at hxB
    have hex : 0 < (1 - ‖x‖) / 4 := by linarith
    have hex' : (1 - ‖x‖) / 4 < 1 / 2 := by linarith [norm_nonneg x]
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hex
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hm3 : 1 / ((m : ℝ) + 3) < (1 - ‖x‖) / 4 :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (by linarith) (by linarith)) hm
    rw [compat _ _ hex hex' (hmem m).1 (hmem m).2 x
      (by rw [mem_ball_zero_iff, max_eq_left hm3.le]; linarith)]
    exact hx m (by rw [mem_ball_zero_iff]; linarith)
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Weyl's lemma step "thus `w` is harmonic in `B`":
if `w ∈ W^{1,2}(B)` has weak gradient `g` and `u` is `C¹` on the open unit ball `B` with `u = w`
a.e. on `B`, then `∇u = g` a.e. on `B`.  For a test function `ζ`, `φ = u ζ` is `C¹` with compact
support in `B`, so translation invariance of Lebesgue measure gives `∫ Dφ = 0`, i.e.
`∫ u ∇ζ = -∫ ζ ∇u`.  With `u = w` a.e. and the weak-gradient identity this yields
`∫ ζ (∇u - g) = 0`, and the fundamental lemma of the calculus of variations on the open ball `B`
gives `∇u = g` a.e. on `B`. -/
theorem w12_ball_gradient_ae_eq_of_contDiffAt : ∀ n : ℕ, 1 ≤ n → ∀ (w u : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient w g (ball 0 1) → (∀ x ∈ ball (0 : Rn n) 1, ContDiffAt ℝ 1 u x) → (∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), u x = w x) → ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), gradient u x = g x := by
  intro n _ w u g hw hu huw
  obtain ⟨-, hgL, hweak⟩ := hw
  -- `∇u` is continuous on `B` and `g` is integrable on `B`, so `∇u - g` is locally integrable.
  have hgu : ∀ x ∈ ball (0 : Rn n) 1, ContinuousAt (gradient u) x := fun x hx =>
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.continuousAt.comp
      ((hu x hx).continuousAt_fderiv one_ne_zero)
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hg : IntegrableOn g (ball (0 : Rn n) 1) := hgL.integrable one_le_two
  have hloc : LocallyIntegrableOn (fun x => gradient u x - g x) (ball (0 : Rn n) 1) :=
    ((continuousOn_of_forall_continuousAt hgu).locallyIntegrableOn measurableSet_ball).sub
      hg.locallyIntegrableOn
  -- `∫ ζ (∇u - g) = 0` for every test function `ζ` supported in `B`.
  have key : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball 0 1 → ∫ x, ζ x • (gradient u x - g x) = 0 := by
    intro ζ hζ hζc hζB
    have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by exact_mod_cast le_top)
    have hgζ : Continuous (gradient ζ) :=
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp
        (hζ1.continuous_fderiv one_ne_zero)
    -- `ζ` and `∇ζ` vanish on the open set `(tsupport ζ)ᶜ`.
    have hζ0 : ∀ x ∉ tsupport ζ, ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hgζ0 : ∀ x ∉ tsupport ζ, gradient ζ x = 0 := fun x hx => by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]
    have hK : ∀ x ∉ tsupport ζ, ∀ᶠ y in 𝓝 x, y ∉ tsupport ζ := fun x hx =>
      (isClosed_tsupport ζ).isOpen_compl.mem_nhds hx
    -- `φ = u ζ` is `C¹` with compact support in `B`, and `∇φ = u ∇ζ + ζ ∇u`.
    set φ : Rn n → ℝ := fun x => u x * ζ x
    have hφ0 : ∀ x ∉ tsupport ζ, φ =ᶠ[𝓝 x] fun _ => 0 := fun x hx => by
      filter_upwards [hK x hx] with y hy
      simp [φ, hζ0 y hy]
    have hφ1 : ContDiff ℝ 1 φ := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ tsupport ζ
      · exact (hu x (hζB hx)).mul hζ1.contDiffAt
      · exact contDiffAt_const.congr_of_eventuallyEq (hφ0 x hx)
    have hφc : HasCompactSupport φ := hζc.mul_left
    have hφB : tsupport φ ⊆ ball 0 1 := tsupport_mul_subset_right.trans hζB
    have hφg : ∀ x, gradient φ x = u x • gradient ζ x + ζ x • gradient u x := by
      intro x
      by_cases hx : x ∈ tsupport ζ
      · have hd : HasFDerivAt φ (u x • fderiv ℝ ζ x + ζ x • fderiv ℝ u x) x :=
          (((hu x (hζB hx)).differentiableAt one_ne_zero).hasFDerivAt).mul
            ((hζ1.differentiable one_ne_zero x).hasFDerivAt)
        rw [gradient, hd.fderiv, map_add, map_smulₛₗ, map_smulₛₗ]
        simp [gradient]
      · rw [gradient, (hφ0 x hx).fderiv_eq, hζ0 x hx, hgζ0 x hx]
        simp
    -- Translation invariance: `y ↦ ∫ φ (x + y) dx` is constant, so `∫ Dφ = 0`.
    have hdφ : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
    obtain ⟨M, hM⟩ := hdφ.bounded_above_of_compact_support (hφc.fderiv ℝ)
    have hDφ : ∫ x, fderiv ℝ φ x = 0 := by
      have hderiv : HasFDerivAt (fun y : Rn n => ∫ x, φ (x + y)) (∫ x, fderiv ℝ φ (x + 0)) 0 := by
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F' := fun y x => fderiv ℝ φ (x + y))
          (bound := (ball (0 : Rn n) 2).indicator fun _ => M) (ball_mem_nhds 0 one_pos)
          (Eventually.of_forall fun y =>
            (hφ1.continuous.comp (continuous_id.add_const y)).aestronglyMeasurable)
          ?_ (hdφ.comp (continuous_id.add_const 0)).aestronglyMeasurable ?_ ?_ ?_
        · simpa using hφ1.continuous.integrable_of_hasCompactSupport hφc
        · refine Eventually.of_forall fun x y hy => ?_
          by_cases hx : x ∈ ball (0 : Rn n) 2
          · rw [indicator_of_mem hx]
            exact hM _
          · rw [indicator_of_notMem hx]
            have hxy : x + y ∉ tsupport φ := by
              intro h
              have h1 := hφB h
              rw [mem_ball_zero_iff] at h1 hy
              rw [mem_ball_zero_iff, not_lt] at hx
              have h2 := norm_sub_le (x + y) y
              rw [add_sub_cancel_right] at h2
              linarith
            rw [fderiv_of_notMem_tsupport ℝ hxy, norm_zero]
        · exact (integrableOn_const (measure_ball_lt_top).ne).integrable_indicator
            measurableSet_ball
        · exact Eventually.of_forall fun x y _ =>
            (hasFDerivAt_comp_add_left x).2 (hφ1.differentiable one_ne_zero (x + y)).hasFDerivAt
      have hconst : (fun y : Rn n => ∫ x, φ (x + y)) = fun _ => ∫ x, φ x := by
        funext y
        exact integral_add_right_eq_self φ y
      rw [hconst] at hderiv
      simpa using hderiv.unique (hasFDerivAt_const _ _)
    have hgφ : ∫ x, gradient φ x = 0 := by
      have h := ContinuousLinearMap.integral_comp_commSL (σ := starRingEnd ℝ) (by simp)
        ((InnerProductSpace.toDual ℝ (Rn n)).symm.toContinuousLinearEquiv :
          StrongDual ℝ (Rn n) →SL[starRingEnd ℝ] Rn n)
        (μ := volume) (hdφ.integrable_of_hasCompactSupport (hφc.fderiv ℝ))
      simpa [gradient, hDφ] using h
    -- Integrability of the three pieces.
    have hA : Integrable (fun x => u x • gradient ζ x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · refine continuous_iff_continuousAt.2 fun x => ?_
        by_cases hx : x ∈ tsupport ζ
        · exact ((hu x (hζB hx)).continuousAt).smul hgζ.continuousAt
        · refine ContinuousAt.congr (f := fun _ => (0 : Rn n)) continuousAt_const ?_
          filter_upwards [hK x hx] with y hy
          simp [hgζ0 y hy]
      · refine hζc.mono' fun x hx => ?_
        by_contra h
        exact hx (by simp [hgζ0 x h])
    have hC : Integrable (fun x => ζ x • gradient u x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · refine continuous_iff_continuousAt.2 fun x => ?_
        by_cases hx : x ∈ tsupport ζ
        · exact hζ.continuous.continuousAt.smul (hgu x (hζB hx))
        · refine ContinuousAt.congr (f := fun _ => (0 : Rn n)) continuousAt_const ?_
          filter_upwards [hK x hx] with y hy
          simp [hζ0 y hy]
      · refine hζc.mono' fun x hx => ?_
        by_contra h
        exact hx (by simp [hζ0 x h])
    have hD : Integrable (fun x => ζ x • g x) := by
      obtain ⟨Cζ, hCζ⟩ := hζ.continuous.bounded_above_of_compact_support hζc
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero
        (hg.bdd_smul Cζ hζ.continuous.aestronglyMeasurable (Eventually.of_forall hCζ)) ?_
      intro x hx
      simp [hζ0 x fun h => hx (hζB h)]
    -- `∫ u ∇ζ = -∫ ζ ∇u` and `∫ ζ g = -∫ u ∇ζ`.
    have hibp : (∫ x, u x • gradient ζ x) + ∫ x, ζ x • gradient u x = 0 := by
      rw [← integral_add hA hC, ← hgφ]
      exact integral_congr_ae (Eventually.of_forall fun x => (hφg x).symm)
    have hζg : ∫ x, ζ x • g x = -∫ x, u x • gradient ζ x := by
      have h1 : ∫ x in ball (0 : Rn n) 1, ζ x • g x = ∫ x, ζ x • g x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp [hζ0 x fun h => hx (hζB h)]
      have h2 : ∫ x in ball (0 : Rn n) 1, u x • gradient ζ x = ∫ x, u x • gradient ζ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp [hgζ0 x fun h => hx (hζB h)]
      have h3 : ∫ x in ball (0 : Rn n) 1, w x • gradient ζ x =
          ∫ x in ball (0 : Rn n) 1, u x • gradient ζ x :=
        integral_congr_ae (by filter_upwards [huw] with x hx; rw [hx])
      rw [← h1, ← h2, ← h3, hweak ζ hζ hζc hζB, neg_neg]
    have hsub : ∫ x, ζ x • (gradient u x - g x) =
        (∫ x, ζ x • gradient u x) - ∫ x, ζ x • g x := by
      rw [← integral_sub hC hD]
      simp only [smul_sub]
    rw [hsub, hζg, sub_neg_eq_add, add_comm, hibp]
  -- Fundamental lemma of the calculus of variations on the open ball.
  have h0 := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [h0] with x hx hxB
  exact sub_eq_zero.1 (hx hxB)
/-- **Weyl's lemma** for `W^{1,2}(B)`, `B = B̆₁(0)` (Simon Ch. 5, proof of Lemma 3.1, p. 114: "Thus
`w` is harmonic in `B`"; Weyl 1940, cf. Hörmander, ALPDO I, Thm. 4.4.1).  If `w` has weak gradient
`g` on `B` and `∫_B ⟨g, ∇ζ⟩ = 0` for every `ζ ∈ C^∞_c(B)`, then `w` agrees a.e. on `B` with a
function `u` harmonic near every point of `B`, and `∇u = g` a.e. on `B`.  Since `w ∈ L²(B) ⊆ L¹(B)`,
`w` is weakly harmonic in Laplacian form; mollification and the mean value property give harmonic
representatives on each `B_{1-ε}`, which glue to `u`; and the weak gradient of a `C¹`
representative is its classical gradient. -/
theorem w12_ball_weyl_lemma : ∀ n : ℕ, 1 ≤ n → ∀ (w : Rn n → ℝ) (g : Rn n → Rn n), IsW12WithGradient w g (ball 0 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, inner ℝ (g x) (gradient ζ x) = 0) → ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧ (∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), u x = w x) ∧ ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) 1)), gradient u x = g x := by
  intro n hn w g hwg hg
  -- `w ∈ L²(B)` and `|B| < ∞`, so `w ∈ L¹(B)`.
  have hint : IntegrableOn w (ball (0 : Rn n) 1) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact hwg.1.integrable one_le_two
  -- Weak harmonicity in Laplacian form: `∫_B w Δζ = 0` for every test function `ζ`.
  have hlap := Submission.w12_ball_weak_laplacian_eq_zero n hn w g hwg hg
  -- Harmonic representatives on the balls `B_{1-ε}`, glued into `u` harmonic on `B`, `u = w` a.e.
  obtain ⟨u, hu, huw⟩ := Submission.ball_harmonic_patching n hn w
    (Submission.ball_weakly_harmonic_local_representative n hn w hint hlap)
  -- `u` is `C²`, hence `C¹`, near each point of `B`, so its gradient is the weak gradient `g`.
  exact ⟨u, hu, huw, Submission.w12_ball_gradient_ae_eq_of_contDiffAt n hn w u g hwg
    (fun x hx => (hu x hx).1.of_le one_le_two) huw⟩

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

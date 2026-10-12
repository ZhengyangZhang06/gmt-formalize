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

/-- **Whitney's `C¹` extension theorem on `ℝⁿ`, value part** (Simon Ch. 2, Theorem 1.6, whose
proof Simon cites from [EG92] §6.5 and [Fed69] 3.1.14).  Let `A ⊆ ℝⁿ` be closed, and let
`h : ℝⁿ → ℝ` and `D : ℝⁿ → L(ℝⁿ, ℝ)` be continuous on `A`.  Suppose the first-order Taylor remainder
satisfies `|h y - h x - D x (y - x)| ≤ τ |y - x|` uniformly for `x` in each compact `Q ⊆ A` and
`y ∈ A` near `x`.  Then some `g ∈ C¹(ℝⁿ)` equals `h` on `A`.
Proof (the Evans–Gariepy/Federer construction):
* compactness of `A ∩ B(a, 1)` and continuity of `D` give a uniform estimate near each `a ∈ A`;
* Vitali selects Whitney balls `B(c, r c)`, `r = min 1 (dist (·, A)) / 100`, with bounded overlap;
* rescaled bumps give a smooth partition of unity `φ c` on `Aᶜ` with `∑ ‖Dφ c‖ ≤ M / r`;
* `g = ∑ φ c · (h b_c + D b_c (· - b_c))` off `A`, with nearest-point anchors `b_c`, and `g = h`
  on `A`.
Then `Dg(a) = D a` on `A`, `Dg` is continuous at points of `A`, and `g` is `C¹` off `A`. -/
theorem rsod_c1ab_whitney_c1_extension : ∀ (n : ℕ) (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖h y - h x - D x (y - x)‖ ≤ τ * ‖y - x‖) → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ ∀ a ∈ A, g a = h a := by
  intro n A h D hA _ hDc hcpt
  -- The local uniform estimate near `a ∈ A`, from compactness of `A ∩ B(a, 1)`.
  have hW : ∀ a ∈ A, ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ e) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ → |h c - h b - D b (c - b)| ≤ e * ‖c - b‖ := by
    intro a ha e he
    obtain ⟨ρ, hρ, hρQ⟩ := hcpt (A ∩ closedBall a 1) ((isCompact_closedBall a 1).inter_left hA)
      inter_subset_left e he
    obtain ⟨η, hη, hηD⟩ := Metric.continuousOn_iff.1 hDc a ha e he
    obtain ⟨δ, hδ0, hδ1, hδη, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ η ∧ δ ≤ ρ / 3 :=
      ⟨min 1 (min η (ρ / 3)), lt_min one_pos (lt_min hη (by positivity)), min_le_left _ _,
        (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
    refine ⟨δ, hδ0, hδ1, fun b hb hba => ?_, fun b hb hba c hc hca => ?_⟩
    · rw [← dist_eq_norm]
      exact (hηD b hb (hba.trans_le hδη)).le
    · have hbc : dist b c < ρ := by
        have := dist_triangle b a c
        rw [dist_comm a c] at this
        linarith
      have h1 := hρQ b ⟨hb, mem_closedBall.2 (by linarith)⟩ c hc hbc
      rwa [Real.norm_eq_abs] at h1
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, fun x hx => hx.elim⟩
  classical
  -- Whitney radius `r x = min 1 (dist (x, A)) / 100`.
  obtain ⟨r, hr⟩ : ∃ r : Rn n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 := ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]; exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).1 hx)) (by norm_num)
  have hcomp : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := by
      intro x y
      have h1 := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h1
      rw [hr, hr]
      linarith [(abs_sub_le_iff.1 h1).1]
    intro x c hxc
    have h1 := hrlip x c
    have h2 := hrlip c x
    rw [dist_comm c x] at h2
    have h3 := hr0 x
    have h4 := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)` whose fourfold enlargements cover `Aᶜ`.
  obtain ⟨Cs, hCsA, hCsdisj, hCscov⟩ : ∃ Cs : Set (Rn n), Cs ⊆ Aᶜ ∧
      Cs.PairwiseDisjoint (fun c => ball c (r c)) ∧ ∀ x ∉ A, ∃ c ∈ Cs, dist x c < 4 * r c := by
    have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
      rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball Aᶜ
      (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Cs, ∀ c' ∈ Cs, c ≠ c' → r c ≤ dist c c' := by
    intro c hc c' hc' hcc
    by_contra hlt
    exact Set.disjoint_left.1 (hCsdisj hc hc' hcc) (show c' ∈ ball c (r c) by
      rw [mem_ball, dist_comm]; exact not_le.1 hlt) (mem_ball_self (hrpos c' (hCsA hc')))
  -- A uniform packing bound for `1/2`-separated subsets of `B(0, 21)`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Rn n), s ⊆ closedBall 0 21 →
      s.Pairwise (fun y z => 1 / 2 ≤ dist y z) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1
      (isCompact_closedBall (0 : Rn n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hs2 => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Rn n) y < 1 / 4 := by
      intro x
      obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.1 (hcover (hs x.2))
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Function.Injective c := by
      intro x y hxy
      by_contra hne
      have hd := hs2 x.2 y.2 (fun h' => hne (Subtype.ext h'))
      have htri := dist_triangle (x : Rn n) (c x) y
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Rn n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- The finite sets `F x` of centres near `x ∉ A`.
  obtain ⟨F, hF⟩ : ∃ F : Rn n → Finset (Rn n), ∀ x, x ∉ A →
      (∀ c, c ∈ F x ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ (F x).card ≤ N := by
    have key : ∀ x, x ∉ A → ∃ s : Finset (Rn n),
        (∀ c, c ∈ s ↔ c ∈ Cs ∧ dist x c ≤ r x + 10 * r c) ∧ s.card ≤ N := by
      intro x hx
      have hrx := hrpos x hx
      set T : Set (Rn n) := {c | c ∈ Cs ∧ dist x c ≤ r x + 10 * r c} with hT
      obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n, ∀ c, φ c = (r x)⁻¹ • (c - x) := ⟨_, fun _ => rfl⟩
      have hφi : Function.Injective φ := by
        intro c d hcd
        rw [hφ, hφ] at hcd
        have := congrArg (fun z => r x • z) hcd
        simpa [smul_smul, hrx.ne'] using this
      have hnφ : ∀ c d, dist (φ c) (φ d) = dist c d / r x := by
        intro c d
        rw [hφ, hφ, dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hrx.le), ← dist_eq_norm, inv_mul_eq_div]
      have hsub : φ '' T ⊆ closedBall 0 21 := by
        rintro _ ⟨c, hc, rfl⟩
        have h0 : φ x = 0 := by rw [hφ, sub_self, smul_zero]
        rw [mem_closedBall, ← h0, hnφ, div_le_iff₀ hrx, dist_comm]
        exact (hcomp x c hc.2).2.2
      have hsep' : (φ '' T).Pairwise (fun y z => 1 / 2 ≤ dist y z) := by
        rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
        have h1 := hsep c hc.1 d hd.1 (fun h' => hcd (congrArg φ h'))
        have h2 := (hcomp x c hc.2).1
        rw [hnφ, le_div_iff₀ hrx]
        linarith
      obtain ⟨hfin, hcard⟩ := hN (φ '' T) hsub hsep'
      have hTfin : T.Finite := hfin.of_finite_image hφi.injOn
      refine ⟨hTfin.toFinset, fun c => hTfin.mem_toFinset, ?_⟩
      rw [← Set.ncard_eq_toFinset_card T hTfin, ← Set.ncard_image_of_injective T hφi]
      exact hcard
    choose! F hF using key
    exact ⟨F, hF⟩
  -- A fixed bump `β`, equal to `1` on `B(0, 4)` and to `0` off `B(0, 8)`.
  obtain ⟨β, hβ0, hβ1, hβone, hβzero, hβs, L, hL⟩ : ∃ β : Rn n → ℝ, (∀ y, 0 ≤ β y) ∧
      (∀ y, β y ≤ 1) ∧ (∀ y, ‖y‖ ≤ 4 → β y = 1) ∧ (∀ y, 8 ≤ ‖y‖ → β y = 0) ∧
      ContDiff ℝ 1 β ∧ ∃ L : ℝ≥0, LipschitzWith L β := by
    let b : ContDiffBump (0 : Rn n) := ⟨4, 8, by norm_num, by norm_num⟩
    refine ⟨b, fun y => b.nonneg, fun y => b.le_one, fun y hy => b.one_of_mem_closedBall ?_,
      fun y hy => Function.notMem_support.1 ?_, b.contDiff (n := 1),
      ContDiff.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (b.contDiff (n := 1))
        one_ne_zero⟩
    · rw [mem_closedBall, dist_zero_right]; exact hy
    · rw [b.support_eq, mem_ball, dist_zero_right]; exact not_lt.2 hy
  -- The rescaled bumps `ψ c y = β ((y - c) / r c)`.
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Rn n → Rn n → ℝ, ∀ c y, ψ c y = β ((r c)⁻¹ • (y - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hnsc : ∀ c y, 0 < r c → ‖(r c)⁻¹ • (y - c)‖ = dist y c / r c := by
    intro c y hc
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, inv_mul_eq_div]
  have hψ0 : ∀ c y, 0 ≤ ψ c y := fun c y => by rw [hψ]; exact hβ0 _
  have hψone : ∀ c y, 0 < r c → dist y c ≤ 4 * r c → ψ c y = 1 := by
    intro c y hc hy; rw [hψ]; apply hβone; rw [hnsc c y hc, div_le_iff₀ hc]; exact hy
  have hψzero : ∀ c y, 0 < r c → 8 * r c ≤ dist y c → ψ c y = 0 := by
    intro c y hc hy; rw [hψ]; apply hβzero; rw [hnsc c y hc, le_div_iff₀ hc]; exact hy
  have hψs : ∀ c, ContDiff ℝ 1 (ψ c) := by
    intro c
    rw [show ψ c = fun y => β ((r c)⁻¹ • (y - c)) from funext (hψ c)]
    exact hβs.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hψd : ∀ c y, 0 < r c → ‖fderiv ℝ (ψ c) y‖ ≤ L / r c := by
    intro c y hc
    have hlip : LipschitzWith (L * (Real.toNNReal (r c))⁻¹) (ψ c) := by
      refine LipschitzWith.of_dist_le_mul fun y z => ?_
      rw [hψ, hψ, NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le]
      refine (hL.dist_le_mul _ _).trans (le_of_eq ?_)
      rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hc.le), dist_eq_norm, mul_assoc]
    have := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := y)
    rwa [NNReal.coe_mul, NNReal.coe_inv, Real.coe_toNNReal _ hc.le, ← div_eq_mul_inv] at this
  -- The locally finite sum `S = ∑ c ∈ Cs, ψ c ≥ 1` on `Aᶜ`.
  obtain ⟨S, hS⟩ : ∃ S : Rn n → ℝ, ∀ y, S y = ∑ᶠ c ∈ Cs, ψ c y := ⟨_, fun _ => rfl⟩
  have hψF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → ψ c y = 0 := by
    intro x hx y hy c hc hcF
    apply hψzero c y (hrpos c (hCsA hc))
    have h1 : ¬ dist x c ≤ r x + 10 * r c := fun h' => hcF (((hF x hx).1 c).2 ⟨hc, h'⟩)
    have h2 := dist_triangle x y c
    rw [dist_comm x y] at h2
    have h3 := hr0 c
    linarith
  have hSloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → S y = ∑ c ∈ F x, ψ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext c
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    exact ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 (hψF x hx y hy c hc.1 h'), hc.2⟩,
      fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
  have hS1 : ∀ x, x ∉ A → 1 ≤ S x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hCscov x hx
    have hcF : c ∈ F x := ((hF x hx).1 c).2 ⟨hc, by linarith [hr0 x, hr0 c]⟩
    rw [hSloc x hx x (by rw [dist_self]; exact hrpos x hx)]
    calc (1 : ℝ) = ψ c x := (hψone c x (hrpos c (hCsA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, ψ c x := Finset.single_le_sum (fun c _ => hψ0 c x) hcF
  have hSc : ∀ x, x ∉ A → ContDiffAt ℝ 1 S x := by
    intro x hx
    refine (ContDiff.contDiffAt (ContDiff.sum (s := F x) fun c _ => hψs c)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSloc x hx y hy
  have hnotA : ∀ x, x ∉ A → ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA
    have h1 := infDist_le_dist_of_mem (x := x) hyA
    rw [dist_comm] at h1
    linarith [hrd x, hr0 x]
  -- The partition of unity `φ c = ψ c / S` on `Aᶜ`.
  obtain ⟨φ, hφ⟩ : ∃ φ : Rn n → Rn n → ℝ, ∀ c y, φ c y = ψ c y / S y := ⟨_, fun _ _ => rfl⟩
  have hφcd : ∀ c x, x ∉ A → ContDiffAt ℝ 1 (φ c) x := by
    intro c x hx
    rw [show φ c = ψ c / S from funext (hφ c)]
    exact (hψs c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hφ0 : ∀ c y, y ∉ A → 0 ≤ φ c y := fun c y hy => by
    rw [hφ]; exact div_nonneg (hψ0 c y) (le_trans zero_le_one (hS1 y hy))
  have hφsum : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∑ c ∈ F x, φ c y = 1 := by
    intro x hx y hy
    simp only [hφ]
    rw [← Finset.sum_div, ← hSloc x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hnotA x hx y hy))))
  have hφF : ∀ x, x ∉ A → ∀ y, dist y x < r x → ∀ c ∈ Cs, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc hcF
    rw [hφ, hψF x hx y hy c hc hcF, zero_div]
  have hφdsum : ∀ x, x ∉ A → ∑ c ∈ F x, fderiv ℝ (φ c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, φ c y) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hφsum x hx y hy
    have h1 := heq.fderiv_eq (𝕜 := ℝ)
    rwa [fderiv_fun_const, Pi.zero_apply, fderiv_fun_sum fun c _ =>
      (hφcd c x hx).differentiableAt one_ne_zero] at h1
  -- `‖Dφ_c‖ ≤ ‖Dψ_c‖ + ‖DS‖` off `A` (quotient rule, `S ≥ 1`, `0 ≤ ψ_c ≤ 1`).
  have hφd : ∀ c x, x ∉ A → ‖fderiv ℝ (φ c) x‖ ≤ ‖fderiv ℝ (ψ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro c x hx
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hb := ((hψs c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hder : fderiv ℝ (φ c) x =
        ψ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (ψ c) x := by
      rw [show φ c = fun y => ψ c y * ((fun t : ℝ => t⁻¹) ∘ S) y from
        funext fun y => by rw [hφ, div_eq_mul_inv]; rfl]
      exact (hb.fun_mul hi).fderiv
    have hp0 := hψ0 c x
    have hp1 : ψ c x ≤ 1 := by rw [hψ]; exact hβ1 _
    have hsi : (S x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1x
    have hsi2 : (S x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hS1x)
    rw [hder]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_of_nonneg hp0,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), add_comm]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hsi)
      (mul_le_of_le_one_left (by positivity) hp1 |>.trans (mul_le_of_le_one_left (norm_nonneg _) hsi2))
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, x ∉ A → ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ M / r x := by
    refine ⟨(N + 1) * (N * (2 * L)), by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    have hb : ∀ c ∈ F x, ‖fderiv ℝ (ψ c) x‖ ≤ 2 * L / r x := by
      intro c hc
      have hc' := ((hF x hx).1 c).1 hc
      have hrc := hrpos c (hCsA hc'.1)
      refine (hψd c x hrc).trans ?_
      rw [div_le_div_iff₀ hrc hrx]
      calc (L : ℝ) * r x ≤ L * (2 * r c) :=
            mul_le_mul_of_nonneg_left (by linarith [(hcomp x c hc'.2).1]) L.2
        _ = 2 * L * r c := by ring
    have hN' : ((F x).card : ℝ) ≤ N := by exact_mod_cast (hF x hx).2
    have hb0 : (0 : ℝ) ≤ 2 * L / r x := div_nonneg (by positivity) hrx.le
    have hSd : ‖fderiv ℝ S x‖ ≤ N * (2 * L / r x) := by
      have heq : S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, ψ c y := by
        filter_upwards [ball_mem_nhds x hrx] with y hy
        exact hSloc x hx y hy
      rw [heq.fderiv_eq, fderiv_fun_sum fun c _ => (hψs c).differentiable one_ne_zero x]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hN' hb0
    calc ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, (2 * L / r x + N * (2 * L / r x)) :=
          Finset.sum_le_sum fun c hc => (hφd c x hx).trans (add_le_add (hb c hc) hSd)
      _ = (F x).card * ((N + 1) * (2 * L / r x)) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ N * ((N + 1) * (2 * L / r x)) := mul_le_mul_of_nonneg_right hN' (by positivity)
      _ = (N + 1) * (N * (2 * L)) / r x := by ring
  -- Nearest-point anchors and the affine jets `Q a y = h a + D a (y - a)`.
  obtain ⟨anc, hancA, hancd⟩ : ∃ anc : Rn n → Rn n, (∀ x, anc x ∈ A) ∧
      ∀ x, dist x (anc x) = infDist x A := by
    choose anc hanc using fun x => hA.exists_infDist_eq_dist hne x
    exact ⟨anc, fun x => (hanc x).1, fun x => (hanc x).2.symm⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Rn n → Rn n → ℝ, ∀ a y, Q a y = h a + (D a y - D a a) :=
    ⟨_, fun _ _ => rfl⟩
  have hQs : ∀ a, ContDiff ℝ 1 (Q a) := by
    intro a
    rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
    exact contDiff_const.add ((D a).contDiff.sub contDiff_const)
  have hQd : ∀ a y, HasFDerivAt (Q a) (D a) y := by
    intro a y
    rw [show Q a = fun y => h a + (D a y - D a a) from funext (hQ a)]
    exact ((D a).hasFDerivAt.sub_const _).const_add _
  have hQsub : ∀ a b y,
      |Q b y - Q a y| ≤ |h b - h a - D a (b - a)| + ‖D b - D a‖ * ‖y - b‖ := by
    intro a b y
    have e1 : Q b y - Q a y = (h b - h a - D a (b - a)) + (D b - D a) (y - b) := by
      rw [hQ, hQ]; simp only [map_sub, sub_apply]; ring
    rw [e1]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    have := (D b - D a).le_opNorm (y - b)
    rwa [Real.norm_eq_abs] at this
  have hancF : ∀ x, x ∉ A → ∀ c ∈ F x, dist x (anc c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have h1 := (hcomp x c (((hF x hx).1 c).1 hc).2).2.2
    have h2 := hrd x
    have h3 := infDist_le_infDist_add_dist (s := A) (x := c) (y := x)
    have h4 := dist_triangle x c (anc c)
    rw [hancd c] at h4
    rw [dist_comm c x] at h3
    linarith [hr0 x]
  have hancP : ∀ x, x ∉ A → ∀ a ∈ A, ∀ c ∈ F x, dist (anc c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have h1 := hancF x hx c hc
    have h2 := infDist_le_dist_of_mem (x := x) ha
    have h3 := dist_triangle (anc c) x a
    rw [dist_comm (anc c) x] at h3
    linarith
  -- The Whitney extension `g`.
  obtain ⟨g, hg⟩ : ∃ g : Rn n → ℝ, ∀ y,
      g y = if y ∈ A then h y else ∑ᶠ c ∈ Cs, φ c y * Q (anc c) y := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgloc : ∀ x, x ∉ A → ∀ y, dist y x < r x → g y = ∑ c ∈ F x, φ c y * Q (anc c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hnotA x hx y hy)]
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext c
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    refine ⟨fun hc => ⟨Classical.byContradiction fun h' => hc.2 ?_, hc.2⟩,
      fun hc => ⟨(((hF x hx).1 c).1 hc.1).1, hc.2⟩⟩
    rw [hφF x hx y hy c hc.1 h', zero_mul]
  have hgev : ∀ x, x ∉ A → g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y * Q (anc c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgloc x hx y hy
  have hgd : ∀ x, x ∉ A → HasFDerivAt g
      (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) x := by
    intro x hx
    refine HasFDerivAt.congr_of_eventuallyEq ?_ (hgev x hx)
    exact HasFDerivAt.fun_sum fun c _ =>
      ((hφcd c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hQd (anc c) x)
  have hgcd : ∀ x, x ∉ A → ContDiffAt ℝ 1 g x := by
    intro x hx
    refine ContDiffAt.congr_of_eventuallyEq ?_ (hgev x hx)
    exact ContDiffAt.sum fun c _ => (hφcd c x hx).mul (hQs (anc c)).contDiffAt
  -- `g` has derivative `D a` at each `a ∈ A`.
  have hgdA : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    refine HasFDerivAt.of_isLittleO (Asymptotics.IsLittleO.of_bound fun e he => ?_)
    obtain ⟨δ, hδ, -, hDd, hrem⟩ := hW a ha (e / 5) (by positivity)
    have haa : dist a a < δ := by rw [dist_self]; exact hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA, Real.norm_eq_abs]
      exact (hrem a ha haa x hxA (by linarith)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hx0 : dist x x < r x := by rw [dist_self]; exact hrpos x hxA
      have e1 : g x - h a - D a (x - a) = ∑ c ∈ F x, φ c x * (Q (anc c) x - Q a x) := by
        rw [hgloc x hxA x hx0]
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hφsum x hxA x hx0, one_mul, hQ a x,
          map_sub]
        ring
      rw [e1, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ c ∈ F x, |φ c x * (Q (anc c) x - Q a x)| ≤ ∑ c ∈ F x, φ c x * (e * ‖x - a‖) := by
            refine Finset.sum_le_sum fun c hc => ?_
            rw [abs_mul, abs_of_nonneg (hφ0 c x hxA)]
            refine mul_le_mul_of_nonneg_left ?_ (hφ0 c x hxA)
            have hba := hancP x hxA a ha c hc
            have hxb : dist x (anc c) ≤ 2 * dist x a :=
              (hancF x hxA c hc).trans (by linarith [infDist_le_dist_of_mem (x := x) ha])
            have hbaδ : dist (anc c) a < δ := by linarith
            have h1 := hrem a ha haa (anc c) (hancA c) hbaδ
            have h2 := hDd (anc c) (hancA c) hbaδ
            rw [dist_eq_norm] at hba hxb
            refine (hQsub a (anc c) x).trans ?_
            calc |h (anc c) - h a - D a (anc c - a)| + ‖D (anc c) - D a‖ * ‖x - anc c‖
                ≤ e / 5 * ‖anc c - a‖ + e / 5 * ‖x - anc c‖ :=
                  add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
              _ ≤ e / 5 * (3 * ‖x - a‖) + e / 5 * (2 * ‖x - a‖) :=
                  add_le_add (mul_le_mul_of_nonneg_left hba (by positivity))
                    (mul_le_mul_of_nonneg_left hxb (by positivity))
              _ = e * ‖x - a‖ := by ring
        _ = e * ‖x - a‖ := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
  -- `Dg` is continuous at each `a ∈ A`.
  have hgcA : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    rw [Metric.continuousAt_iff]
    intro e he
    obtain ⟨δ, hδ, hδ1, hDd, hrem⟩ := hW a ha (e / (2 * (1 + 700 * M))) (by positivity)
    set η := e / (2 * (1 + 700 * M)) with hη
    have hη0 : 0 < η := by positivity
    have hηM : η * (1 + 700 * M) = e / 2 := by rw [hη]; field_simp
    have hηM' := mul_nonneg hη0.le hM0
    refine ⟨δ / 4, by positivity, fun x hxa => ?_⟩
    rw [(hgdA a ha).fderiv, dist_eq_norm]
    by_cases hxA : x ∈ A
    · rw [(hgdA x hxA).fderiv]
      exact (hDd x hxA (by linarith)).trans_lt (by linarith)
    · have hrx := hrpos x hxA
      have hx0 : dist x x < r x := by rw [dist_self]; exact hrx
      have hbA : anc x ∈ A := hancA x
      have hdxa : infDist x A ≤ dist x a := infDist_le_dist_of_mem ha
      have hba : dist (anc x) a < δ := by
        have := dist_triangle (anc x) x a
        rw [dist_comm (anc x) x, hancd x] at this
        linarith
      have hd1 : infDist x A = 100 * r x := by
        rw [hr, min_eq_right (by linarith : infDist x A ≤ 1)]
        ring
      have hDb := hDd (anc x) hbA hba
      have e1 : (∑ c ∈ F x, (φ c x • D (anc c) + Q (anc c) x • fderiv ℝ (φ c) x)) - D a =
          (∑ c ∈ F x, φ c x • (D (anc c) - D a)) +
            ∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x := by
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hφsum x hxA x hx0, hφdsum x hxA, one_smul,
          smul_zero, sub_zero]
        abel
      rw [(hgd x hxA).fderiv, e1]
      have hT1 : ‖∑ c ∈ F x, φ c x • (D (anc c) - D a)‖ ≤ η := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ c ∈ F x, ‖φ c x • (D (anc c) - D a)‖ ≤ ∑ c ∈ F x, φ c x * η :=
              Finset.sum_le_sum fun c hc => by
                rw [norm_smul, Real.norm_of_nonneg (hφ0 c x hxA)]
                exact mul_le_mul_of_nonneg_left
                  (hDd (anc c) (hancA c) (by linarith [hancP x hxA a ha c hc])) (hφ0 c x hxA)
          _ = η := by rw [← Finset.sum_mul, hφsum x hxA x hx0, one_mul]
      have hT2 : ‖∑ c ∈ F x, (Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖ ≤
          700 * η * r x * (M / r x) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ c ∈ F x, ‖(Q (anc c) x - Q (anc x) x) • fderiv ℝ (φ c) x‖
            ≤ ∑ c ∈ F x, 700 * η * r x * ‖fderiv ℝ (φ c) x‖ :=
              Finset.sum_le_sum fun c hc => by
                rw [norm_smul, Real.norm_eq_abs]
                refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
                have hcaδ : dist (anc c) a < δ := by linarith [hancP x hxA a ha c hc]
                have hxc := hancF x hxA c hc
                have hcb : dist (anc c) (anc x) ≤ 3 * infDist x A := by
                  have := dist_triangle (anc c) x (anc x)
                  rw [dist_comm (anc c) x, hancd x] at this
                  linarith
                have h1 := hrem (anc x) hbA hba (anc c) (hancA c) hcaδ
                have h2 : ‖D (anc c) - D (anc x)‖ ≤ 2 * η := by
                  rw [← sub_sub_sub_cancel_right (D (anc c)) (D (anc x)) (D a)]
                  exact (norm_sub_le _ _).trans (by linarith [hDd (anc c) (hancA c) hcaδ])
                rw [dist_eq_norm] at hcb hxc
                refine (hQsub (anc x) (anc c) x).trans ?_
                calc |h (anc c) - h (anc x) - D (anc x) (anc c - anc x)| +
                      ‖D (anc c) - D (anc x)‖ * ‖x - anc c‖
                    ≤ η * ‖anc c - anc x‖ + 2 * η * ‖x - anc c‖ :=
                      add_le_add h1 (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
                  _ ≤ η * (3 * infDist x A) + 2 * η * (2 * infDist x A) :=
                      add_le_add (mul_le_mul_of_nonneg_left hcb hη0.le)
                        (mul_le_mul_of_nonneg_left hxc (by positivity))
                  _ = 700 * η * r x := by rw [hd1]; ring
          _ = 700 * η * r x * ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := by rw [Finset.mul_sum]
          _ ≤ 700 * η * r x * (M / r x) :=
              mul_le_mul_of_nonneg_left (hM x hxA) (mul_nonneg (by positivity) hrx.le)
      have hfin : 700 * η * r x * (M / r x) = 700 * (η * M) := by field_simp
      rw [hfin] at hT2
      exact (norm_add_le _ _).trans_lt (by linarith)
  refine ⟨g, contDiff_one_iff_fderiv.2 ⟨fun x => ?_, continuous_iff_continuousAt.2 fun x => ?_⟩,
    hgA⟩
  · by_cases hx : x ∈ A
    · exact (hgdA x hx).differentiableAt
    · exact (hgd x hx).differentiableAt
  · by_cases hx : x ∈ A
    · exact hgcA x hx
    · exact (hgcd x hx).continuousAt_fderiv one_ne_zero

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

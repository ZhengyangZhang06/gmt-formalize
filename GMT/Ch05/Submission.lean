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

/-- **Approximate tangent spaces of a bi-Lipschitz `C¹` chart image** (Simon Ch. 3, Def. 1.4):
if `G : ℝⁿ → ℝ^{n+ℓ}` is `C¹`, `DG(v)` is injective and `κ|v − w| ≤ |G v − G w|` on the open ball
`B̆_ρ(c)`, then `N = G(B̆_ρ(c))` is Borel with `Hⁿ(N) < ∞`, and `T(x) = DG(ψ x)(ℝⁿ)` (`ψ` the inverse
chart) is the approximate tangent space of `N` at every `x ∈ N`, with `x ↦ p_{T(x)}` continuous on
`N`.  Proof: `N` is `σ`-compact, and the Lipschitz image bound gives `Hⁿ(N) < ∞`; the projection
onto `L(ℝⁿ)` is `L (Lᵀ L)⁻¹ Lᵀ`, continuous in injective `L`.  For the tangent limit at `x = G w`,
the rescaled chart `Φ_r(s) = r⁻¹ (G(w + r s) − G w)`, reparametrized over an isometry
`ι : ℝⁿ → DG(w)(ℝⁿ)`, is `(1 ± ε)`-bi-Lipschitz on a fixed ball `D` for small `r` (mean value
inequality); so `Hⁿ` on its image is squeezed between `(1 ± ε)ⁿ` times the pushforward of Lebesgue
measure on `D` (the Lipschitz image bound replaces the area formula), and dominated convergence
gives `∫_{η_{x,r}(N)} f dHⁿ → ∫_D f ∘ ι = ∫_{T(x)} f dHⁿ`; the lower bound `κ` keeps the support of
`f ∘ Φ_r` inside `D`. -/
theorem tae_c1_chart_image_approxTangent : ∀ {n ℓ : ℕ} (G : Rn n → Amb n ℓ) (c : Rn n) (ρ κ : ℝ), 1 ≤ n → ContDiff ℝ 1 G → 0 < κ → (∀ v ∈ ball c ρ, Function.Injective (fderiv ℝ G v)) → (∀ v ∈ ball c ρ, ∀ w ∈ ball c ρ, κ * ‖v - w‖ ≤ ‖G v - G w‖) → MeasurableSet (G '' ball c ρ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c ρ) < ⊤ ∧ ∃ T : Amb n ℓ → Submodule ℝ (Amb n ℓ), ContinuousOn (fun x => (T x).starProjection) (G '' ball c ρ) ∧ ∀ x ∈ G '' ball c ρ, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c ρ) x (T x) := by
  intro n ℓ G c ρ κ hn hG hκ hinj hlow
  -- Step A (parent steps 0, 1, 3): `N = G(B')` is Borel and `Hⁿ(N) < ∞`.
  have hmeasfin : MeasurableSet (G '' ball c ρ) ∧ (μHE[n] : Measure (Amb n ℓ)) (G '' ball c ρ) < ⊤ := by
    have hGc : Continuous G := hG.continuous
    constructor
    · have hσ : IsSigmaCompact (ball c ρ) := by
        refine ⟨fun m : ℕ => closedBall c (ρ - 1 / ((m : ℝ) + 1)),
          fun m => isCompact_closedBall _ _, ?_⟩
        ext v
        simp only [mem_iUnion, mem_closedBall, mem_ball]
        constructor
        · rintro ⟨m, hm⟩
          have : 0 < 1 / ((m : ℝ) + 1) := by positivity
          linarith
        · intro hv
          obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hv)
          exact ⟨m, by linarith⟩
      obtain ⟨K, hK, hKU⟩ := hσ.image hGc
      rw [← hKU]
      exact MeasurableSet.iUnion fun j => (hK j).measurableSet
    · rcases le_or_gt ρ 0 with hρ | hρ
      · rw [ball_eq_empty.mpr hρ, image_empty, measure_empty]
        exact ENNReal.zero_lt_top
      · have hcont : Continuous (fun v => ‖fderiv ℝ G v‖₊) :=
          (hG.continuous_fderiv one_ne_zero).nnnorm
        obtain ⟨v₀, -, hv₀⟩ := (isCompact_closedBall c ρ).exists_isMaxOn
          (nonempty_closedBall.mpr hρ.le) hcont.continuousOn
        have hLip : LipschitzOnWith ‖fderiv ℝ G v₀‖₊ G (ball c ρ) :=
          (convex_ball c ρ).lipschitzOnWith_of_nnnorm_fderiv_le
            (fun v _ => (hG.differentiable one_ne_zero).differentiableAt)
            (fun v hv => hv₀ (ball_subset_closedBall hv))
        have himg := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
        refine lt_of_le_of_lt himg (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ?_)
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact measure_ball_lt_top
  -- Step B (parent step 5): `L ↦ p_{L(ℝⁿ)}` is continuous on injective `L`, via `L (Lᵀ L)⁻¹ Lᵀ`.
  have hproj : ContinuousOn (fun L : Rn n →L[ℝ] Amb n ℓ => (LinearMap.range L.toLinearMap).starProjection) {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} := by
    -- The transpose `T L = Lᵀ`, built from the standard basis `e i` of `ℝⁿ`.
    let e : Fin n → Rn n := fun i => EuclideanSpace.single i (1 : ℝ)
    let T : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Rn n) :=
      fun L => ∑ i, (innerSL ℝ (L (e i))).smulRight (e i)
    have hT : ∀ L (w : Amb n ℓ) (v : Rn n), inner ℝ (T L w) v = inner ℝ w (L v) := by
      intro L w v
      have hv : v = ∑ i, v i • e i := by
        simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
      have hTw : T L w = ∑ i, inner ℝ (L (e i)) w • e i := by
        simp [T]
      rw [hTw]
      conv_rhs => rw [hv]
      simp only [sum_inner, inner_sum, map_sum, map_smul, real_inner_smul_left,
        real_inner_smul_right, e, EuclideanSpace.inner_single_left, one_mul, map_one]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm]
      ring
    have hTc : Continuous T := by
      refine continuous_finsetSum _ fun i _ => ?_
      have h1 : Continuous fun L : Rn n →L[ℝ] Amb n ℓ => innerSL ℝ (L (e i)) :=
        (innerSL ℝ).continuous.comp (continuous_id.clm_apply continuous_const)
      exact ((ContinuousLinearMap.smulRightL ℝ (Amb n ℓ) (Rn n)).continuous.comp h1).clm_apply
        continuous_const
    -- The Gram operator `A L = Lᵀ L` and the candidate projection `Q L = L (Lᵀ L)⁻¹ Lᵀ`.
    let A : (Rn n →L[ℝ] Amb n ℓ) → (Rn n →L[ℝ] Rn n) := fun L => (T L).comp L
    let Q : (Rn n →L[ℝ] Amb n ℓ) → (Amb n ℓ →L[ℝ] Amb n ℓ) :=
      fun L => L.comp ((Ring.inverse (A L)).comp (T L))
    -- `A L` is a unit for injective `L`: `A L v = 0` gives `|L v|² = ⟨A L v, v⟩ = 0`.
    have hA : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → IsUnit (A L) := by
      intro L hL
      rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
        LinearMap.ker_eq_bot']
      intro v hv
      have h0 : T L (L v) = 0 := hv
      have h1 : inner ℝ (L v) (L v) = 0 := by
        rw [← hT, h0, inner_zero_left]
      exact hL (by rw [inner_self_eq_zero.mp h1, map_zero])
    -- `Q L = p_{L(ℝⁿ)}` for injective `L`: `Q L w ∈ L(ℝⁿ)` and `Lᵀ (w − Q L w) = 0`.
    have hQ : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L →
        (LinearMap.range L.toLinearMap).starProjection = Q L := by
      intro L hL
      ext1 w
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · exact ⟨_, rfl⟩
      · rintro _ ⟨v, rfl⟩
        have h1 : T L (L (Ring.inverse (A L) (T L w))) = T L w := by
          have h2 := congrArg (fun S : Rn n →L[ℝ] Rn n => S (T L w))
            (Ring.mul_inverse_cancel _ (hA L hL))
          simpa [A] using h2
        rw [inner_sub_left, ContinuousLinearMap.coe_coe, ← hT, ← hT]
        simp only [Q, ContinuousLinearMap.coe_comp, Function.comp_apply]
        rw [h1, sub_self]
    -- `Q` is continuous at every injective `L`, since inversion is continuous at units.
    have hQc : ∀ L : Rn n →L[ℝ] Amb n ℓ, Function.Injective L → ContinuousAt Q L := by
      intro L hL
      have hAc : Continuous A := hTc.clm_comp continuous_id
      obtain ⟨u, hu⟩ := hA L hL
      have hinv : ContinuousAt (fun L => Ring.inverse (A L)) L := by
        have h1 := NormedRing.inverse_continuousAt u
        rw [hu] at h1
        exact h1.comp hAc.continuousAt
      exact continuous_id.continuousAt.clm_comp (hinv.clm_comp hTc.continuousAt)
    intro L hL
    exact (hQc L hL).continuousWithinAt.congr (fun L' hL' => hQ L' hL') (hQ L hL)
  -- Step C (parent steps 6-8): `DG(w)(ℝⁿ)` is the approximate tangent space of `N` at `G w`.
  have htan : ∀ w ∈ ball c ρ, Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (G '' ball c ρ) (G w) (LinearMap.range (fderiv ℝ G w).toLinearMap) := by
    intro w hw
    have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hDc : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
    set L := fderiv ℝ G w
    have hLinj : Function.Injective L := hinj w hw
    set P : Submodule ℝ (Amb n ℓ) := LinearMap.range L.toLinearMap with hPdef
    have hPdim : Module.finrank ℝ P = n := by
      rw [hPdef, LinearMap.finrank_range_of_inj hLinj, finrank_euclideanSpace_fin]
    refine ⟨hPdim, fun f => ?_⟩
    -- An isometric parametrization `ιL` of the plane `P`, and `A = ιL⁻¹ ∘ L` with inverse `Bc`.
    let e : P ≃ₗᵢ[ℝ] Rn n := ((stdOrthonormalBasis ℝ P).reindex (finCongr hPdim)).repr
    let ιL : Rn n →ₗᵢ[ℝ] Amb n ℓ := P.subtypeₗᵢ.comp e.symm.toLinearIsometry
    have hιrange : Set.range ιL = (P : Set (Amb n ℓ)) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact (e.symm z).2
      · intro hy
        exact ⟨e ⟨y, hy⟩, by simp [ιL]⟩
    let A : Rn n ≃ₗ[ℝ] Rn n := (LinearEquiv.ofInjective L.toLinearMap hLinj).trans e.toLinearEquiv
    have hιA : ∀ s, ιL (A s) = L s := by
      intro s
      simp [ιL, A]
    let Bc : Rn n →L[ℝ] Rn n := LinearMap.toContinuousLinearMap (A.symm : Rn n →ₗ[ℝ] Rn n)
    have hBc : ∀ z, Bc z = A.symm z := fun z => by simp [Bc]
    have hBA : ∀ s, Bc (A s) = s := fun s => by rw [hBc, LinearEquiv.symm_apply_apply]
    have hLB : ∀ z, L (Bc z) = ιL z := by
      intro z
      have h := hιA (A.symm z)
      simp only [LinearEquiv.apply_symm_apply] at h
      rw [hBc, h]
    have hAn : ∀ s, ‖A s‖ = ‖L s‖ := by
      intro s
      rw [← hιA, LinearIsometry.norm_map]
    set CB : ℝ := ‖Bc‖
    have hCB0 : 0 ≤ CB := norm_nonneg _
    have hB : ∀ z, ‖Bc z‖ ≤ CB * ‖z‖ := fun z => Bc.le_opNorm z
    -- The support radius `R` of `f` and the parameter ball `D`.
    obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Amb n ℓ)
    set R : ℝ := max R₀ 0
    have hR0 : 0 ≤ R := le_max_right _ _
    have hfR : ∀ y : Amb n ℓ, R < ‖y‖ → f y = 0 := by
      intro y hy
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR₀ hmem
      rw [mem_closedBall_zero_iff] at this
      linarith [le_max_left R₀ 0]
    set M : ℝ := R + ‖L‖ * R / κ
    have hRM : R ≤ M := by
      have : 0 ≤ ‖L‖ * R / κ := div_nonneg (mul_nonneg (norm_nonneg _) hR0) hκ.le
      linarith
    have hM0 : 0 ≤ M := hR0.trans hRM
    set D : Set (Rn n) := closedBall (0 : Rn n) M with hDdef
    have hCB1 : 0 < CB + 1 := add_pos_of_nonneg_of_pos hCB0 one_pos
    have hCBM : 0 < CB * M + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hCB0 hM0) one_pos
    -- The rescaled chart `Φ r s = r⁻¹ (G (w + r s) - G w)` and its reparametrization `H r = Φ r ∘ Bc`.
    set Φ : ℝ → Rn n → Amb n ℓ := fun r s => r⁻¹ • (G (w + r • s) - G w) with hΦdef
    set Bp : ℝ → Set (Rn n) := fun r => (fun s => w + r • s) ⁻¹' ball c ρ with hBdef
    set H : ℝ → Rn n → Amb n ℓ := fun r z => Φ r (Bc z) with hHdef
    have haff : ∀ r : ℝ, Continuous (fun s : Rn n => w + r • s) := fun r =>
      continuous_const.add (continuous_id.const_smul r)
    have hΦc : ∀ r, Continuous (Φ r) := fun r =>
      ((hG.continuous.comp (haff r)).sub continuous_const).const_smul r⁻¹
    have hHc : ∀ r, Continuous (H r) := fun r => (hΦc r).comp Bc.continuous
    have hderiv : ∀ r : ℝ, r ≠ 0 → ∀ s, HasFDerivAt (Φ r) (fderiv ℝ G (w + r • s)) s := by
      intro r hr0 s
      have h1 : HasFDerivAt (fun s : Rn n => w + r • s) (r • ContinuousLinearMap.id ℝ (Rn n)) s :=
        ((hasFDerivAt_id s).const_smul r).const_add w
      have h2 := (((hGd (w + r • s)).hasFDerivAt.comp s h1).sub_const (G w)).const_smul r⁻¹
      have hfun : (r⁻¹ • fun x => (G ∘ fun s => w + r • s) x - G w) = Φ r := by
        funext x
        simp only [hΦdef, Pi.smul_apply, Function.comp_apply]
      have hlin : r⁻¹ • (fderiv ℝ G (w + r • s)).comp (r • ContinuousLinearMap.id ℝ (Rn n)) =
          fderiv ℝ G (w + r • s) := by
        refine ContinuousLinearMap.ext fun v => ?_
        rw [smul_apply, ContinuousLinearMap.comp_apply,
          smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_smul,
          inv_mul_cancel₀ hr0, one_smul]
      rw [hfun, hlin] at h2
      exact h2
    -- pointwise convergence `Φ r s → L s`
    have hΦt : ∀ s, Tendsto (fun r => Φ r s) (𝓝[>] 0) (𝓝 (L s)) := by
      intro s
      have hd : HasDerivAt (fun t : ℝ => G (w + t • s)) (L s) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => w + t • s) s 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const s).const_add w
        have h2 := (hGd (w + (0 : ℝ) • s)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
        rw [zero_smul, add_zero] at h2
        exact h2
      have h3 := hd.tendsto_slope_zero_right
      simpa [hΦdef] using h3
    have hHt : ∀ z, Tendsto (fun r => H r z) (𝓝[>] 0) (𝓝 (ιL z)) := by
      intro z
      rw [← hLB z]
      exact hΦt (Bc z)
    -- the blown-up set is `Φ r '' Bp r`, and it is measurable
    have himg : ∀ r : ℝ, r ≠ 0 →
        Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ) = Φ r '' Bp r := by
      intro r hr0
      ext y
      simp only [mem_image, mem_preimage, hΦdef, hBdef, Poincare.SimonGMT.Chapter03.blowUpMap]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨r⁻¹ • (v - w), ?_, ?_⟩
        · rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
          exact hv
        · rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
      · rintro ⟨s, hs, rfl⟩
        exact ⟨G (w + r • s), ⟨w + r • s, hs, rfl⟩, rfl⟩
    have hmeasη : ∀ r : ℝ, r ≠ 0 →
        MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ)) := by
      intro r hr0
      have hpre : Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ) =
          (fun y => G w + r • y) ⁻¹' (G '' ball c ρ) := by
        ext y
        constructor
        · rintro ⟨y₀, hy₀, rfl⟩
          show G w + r • (r⁻¹ • (y₀ - G w)) ∈ G '' ball c ρ
          rw [smul_smul, mul_inv_cancel₀ hr0, one_smul, add_sub_cancel]
          exact hy₀
        · intro hy
          refine ⟨G w + r • y, hy, ?_⟩
          show r⁻¹ • (G w + r • y - G w) = y
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr0, one_smul]
      rw [hpre]
      exact hmeasfin.1.preimage (continuous_const.add (continuous_id.const_smul r)).measurable
    -- `f` vanishes on `Φ r s` unless `s = Bc z` with `z ∈ D` (lower bound `κ`)
    have hfar : ∀ r : ℝ, 0 < r → ∀ s ∈ Bp r, (∀ z ∈ D, Bc z ≠ s) → f (Φ r s) = 0 := by
      intro r hr s hs hsD
      apply hfR
      have hAs : M < ‖A s‖ := by
        by_contra hcon
        exact hsD (A s) (mem_closedBall_zero_iff.mpr (not_lt.mp hcon)) (hBA s)
      have hsR : R / κ < ‖s‖ := by
        by_contra hcon
        have h1 : ‖L s‖ ≤ ‖L‖ * (R / κ) :=
          (L.le_opNorm s).trans (mul_le_mul_of_nonneg_left (not_lt.mp hcon) (norm_nonneg _))
        rw [hAn] at hAs
        have h2 : ‖L‖ * (R / κ) = ‖L‖ * R / κ := by ring
        linarith
      have h1 := hlow (w + r • s) hs w hw
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : ‖Φ r s‖ = r⁻¹ * ‖G (w + r • s) - G w‖ := by
        simp only [hΦdef]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      rw [h2]
      have h3 : κ * ‖s‖ ≤ r⁻¹ * ‖G (w + r • s) - G w‖ := by
        rw [le_inv_mul_iff₀ hr]
        calc r * (κ * ‖s‖) = κ * (r * ‖s‖) := by ring
          _ ≤ _ := h1
      have h4 : R < κ * ‖s‖ := by
        rw [div_lt_iff₀ hκ] at hsR
        linarith
      linarith
    -- for small `r`, `Bc '' D ⊆ Bp r`, so the blow-up integral is an integral over `H r '' D`
    have hr₀ : 0 < (ρ - dist w c) / (CB * M + 1) :=
      div_pos (sub_pos.mpr (mem_ball.mp hw)) hCBM
    have hcover : ∀ r ∈ Ioo (0 : ℝ) ((ρ - dist w c) / (CB * M + 1)), ∀ z ∈ D, Bc z ∈ Bp r := by
      rintro r ⟨hr0, hr1⟩ z hz
      show w + r • Bc z ∈ ball c ρ
      rw [mem_ball]
      have h1 : ‖r • Bc z‖ ≤ r * (CB * M) := by
        rw [norm_smul, Real.norm_of_nonneg hr0.le]
        exact mul_le_mul_of_nonneg_left ((hB z).trans
          (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hCB0)) hr0.le
      have h2 : r * (CB * M) < ρ - dist w c := by
        rw [lt_div_iff₀ hCBM] at hr1
        linarith
      calc dist (w + r • Bc z) c ≤ dist (w + r • Bc z) w + dist w c := dist_triangle _ _ _
        _ = ‖r • Bc z‖ + dist w c := by rw [dist_eq_norm, add_sub_cancel_left]
        _ < ρ := by linarith
    have hsetint : ∀ r ∈ Ioo (0 : ℝ) ((ρ - dist w c) / (CB * M + 1)),
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ), f y
          ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ y in H r '' D, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by
      intro r hr
      have hr0 : r ≠ 0 := hr.1.ne'
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeasη r hr0)
      · rw [himg r hr0]
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨Bc z, hcover r hr z hz, rfl⟩
      · rintro y ⟨hy, hyH⟩
        rw [himg r hr0] at hy
        obtain ⟨s, hs, rfl⟩ := hy
        refine hfar r hr.1 s hs fun z hz hzs => hyH ⟨z, hz, ?_⟩
        simp only [hHdef, hzs]
    -- `H r` is `C¹`-close to the isometry `ιL` on `D` for small `r` (mean value inequality)
    have hLip : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ z ∈ D, ∀ z' ∈ D,
        ‖H r z - H r z' - (ιL z - ιL z')‖ ≤ ε * ‖z - z'‖ := by
      intro ε hε
      have hε' : 0 < ε / (CB + 1) := div_pos hε hCB1
      obtain ⟨η, hη, hηD⟩ := Metric.continuousAt_iff.mp hDc.continuousAt (ε / (CB + 1)) hε'
      have hr₁ : 0 < η / (CB * M + 1) := div_pos hη hCBM
      filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
      obtain ⟨hr0, hr1⟩ := hr
      intro z hz z' hz'
      have hsK : ∀ z ∈ D, Bc z ∈ closedBall (0 : Rn n) (CB * M) := fun z hz => by
        rw [mem_closedBall_zero_iff]
        exact (hB z).trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hCB0)
      set ψ : Rn n → Amb n ℓ := fun t => Φ r t - L t with hψdef
      have hψd : ∀ t ∈ closedBall (0 : Rn n) (CB * M),
          HasFDerivWithinAt ψ (fderiv ℝ G (w + r • t) - L) (closedBall (0 : Rn n) (CB * M)) t :=
        fun t _ => ((hderiv r hr0.ne' t).sub L.hasFDerivAt).hasFDerivWithinAt
      have hψb : ∀ t ∈ closedBall (0 : Rn n) (CB * M), ‖fderiv ℝ G (w + r • t) - L‖ ≤ ε / (CB + 1) := by
        intro t ht
        have h1 : dist (w + r • t) w < η := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
          have h2 : r * ‖t‖ ≤ r * (CB * M) :=
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp ht) hr0.le
          rw [lt_div_iff₀ hCBM] at hr1
          linarith
        have h3 := hηD h1
        rw [dist_eq_norm] at h3
        exact h3.le
      have hmvt := (convex_closedBall (0 : Rn n) (CB * M)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        hψd hψb (hsK z' hz') (hsK z hz)
      have hkey : H r z - H r z' - (ιL z - ιL z') = ψ (Bc z) - ψ (Bc z') := by
        simp only [hψdef, hHdef]
        rw [hLB z, hLB z']
        abel
      rw [hkey]
      calc ‖ψ (Bc z) - ψ (Bc z')‖ ≤ ε / (CB + 1) * ‖Bc z - Bc z'‖ := hmvt
        _ = ε / (CB + 1) * ‖Bc (z - z')‖ := by rw [map_sub]
        _ ≤ ε / (CB + 1) * (CB * ‖z - z'‖) := mul_le_mul_of_nonneg_left (hB _) hε'.le
        _ ≤ ε * ‖z - z'‖ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hCB1]
          have h1 : 0 ≤ ε * ‖z - z'‖ := mul_nonneg hε.le (norm_nonneg _)
          linarith
    have hDfin : (volume : Measure (Rn n)) D < ∞ := measure_closedBall_lt_top
    -- Squeeze: for continuous `g ≥ 0`, `∫_{H r '' D} g dHⁿ → ∫_D g ∘ ιL` (bi-Lipschitz comparison
    -- of `Hⁿ ⌞ H r '' D` with the pushforward of Lebesgue measure on `D`)
    have hinner : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ y, 0 ≤ g y) → ∀ Cg : ℝ, (∀ y, g y ≤ Cg) →
        Tendsto (fun r => ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0)
          (𝓝 (∫ z in D, g (ιL z))) := by
      intro g hgc hg0 Cg hgC
      have hCg : 0 ≤ Cg := (hg0 0).trans (hgC 0)
      have hY : Tendsto (fun r => ∫ z in D, g (H r z)) (𝓝[>] 0) (𝓝 (∫ z in D, g (ιL z))) := by
        refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cg) ?_ ?_ ?_ ?_
        · exact Eventually.of_forall fun r => (hgc.comp (hHc r)).aestronglyMeasurable
        · refine Eventually.of_forall fun r => Eventually.of_forall fun z => ?_
          rw [Real.norm_of_nonneg (hg0 _)]
          exact hgC _
        · exact integrableOn_const hDfin.ne
        · exact Eventually.of_forall fun z => (hgc.tendsto _).comp (hHt z)
      set K : ℝ := Cg * (volume : Measure (Rn n)).real D
      have hK0 : 0 ≤ K := mul_nonneg hCg measureReal_nonneg
      have hXY : Tendsto (fun r => ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) -
          ∫ z in D, g (H r z)) (𝓝[>] 0) (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        -- choose `ε` with `((1 + ε)ⁿ - (1 - ε)ⁿ) K < δ`
        have hφc : Continuous fun ε : ℝ => ((1 + ε) ^ n - (1 - ε) ^ n) * K := by fun_prop
        have hφ0 : ((1 + (0 : ℝ)) ^ n - (1 - 0) ^ n) * K < δ := by simpa using hδ
        obtain ⟨ε, hεδ, hεI⟩ := ((((hφc.tendsto 0).eventually (gt_mem_nhds hφ0)).filter_mono
          nhdsWithin_le_nhds).and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num))).exists
        obtain ⟨hε0, hε1⟩ := hεI
        filter_upwards [hLip ε hε0, self_mem_nhdsWithin] with r hr hr0
        rw [mem_Ioi] at hr0
        -- bi-Lipschitz bounds for `H r` on `D`
        have hιsub : ∀ z z', ‖ιL z - ιL z'‖ = ‖z - z'‖ := fun z z' => by
          rw [← map_sub, LinearIsometry.norm_map]
        have hup : ∀ z ∈ D, ∀ z' ∈ D, ‖H r z - H r z'‖ ≤ (1 + ε) * ‖z - z'‖ := by
          intro z hz z' hz'
          have h1 := hr z hz z' hz'
          calc ‖H r z - H r z'‖ = ‖(H r z - H r z' - (ιL z - ιL z')) + (ιL z - ιL z')‖ := by
                rw [sub_add_cancel]
            _ ≤ ‖H r z - H r z' - (ιL z - ιL z')‖ + ‖ιL z - ιL z'‖ := norm_add_le _ _
            _ ≤ (1 + ε) * ‖z - z'‖ := by rw [hιsub]; linarith
        have hlo : ∀ z ∈ D, ∀ z' ∈ D, (1 - ε) * ‖z - z'‖ ≤ ‖H r z - H r z'‖ := by
          intro z hz z' hz'
          have h1 := hr z hz z' hz'
          have h2 : ‖ιL z - ιL z'‖ ≤ ‖H r z - H r z'‖ + ‖H r z - H r z' - (ιL z - ιL z')‖ := by
            calc ‖ιL z - ιL z'‖ = ‖(H r z - H r z') - (H r z - H r z' - (ιL z - ιL z'))‖ := by
                  rw [sub_sub_cancel]
              _ ≤ _ := norm_sub_le _ _
          rw [hιsub] at h2
          linarith
        have h1ε : 0 < 1 - ε := by linarith
        have hLipH : LipschitzOnWith (Real.toNNReal (1 + ε)) (H r) D := by
          refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
          rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
          exact hup z hz z' hz'
        have hInjH : InjOn (H r) D := by
          intro z hz z' hz' hzz
          have h1 := hlo z hz z' hz'
          rw [hzz, sub_self, norm_zero] at h1
          have h2 : ‖z - z'‖ ≤ 0 := by
            by_contra hcon
            have h3 := mul_pos h1ε (lt_of_not_ge hcon)
            linarith
          exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
        set Hinv : Amb n ℓ → Rn n := Function.invFunOn (H r) D
        have hHinv : ∀ z ∈ D, Hinv (H r z) = z := fun z hz => hInjH.leftInvOn_invFunOn hz
        have hLipInv : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Hinv (H r '' D) := by
          refine LipschitzOnWith.of_dist_le_mul ?_
          rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
          rw [hHinv z hz, hHinv z' hz', dist_eq_norm, dist_eq_norm,
            Real.coe_toNNReal _ (inv_nonneg.mpr h1ε.le), inv_mul_eq_div, le_div_iff₀ h1ε]
          linarith [hlo z hz z' hz']
        -- comparison of `μ₁ = Hⁿ ⌞ H r '' D` with `ν = (H r)_# (Lⁿ ⌞ D)`
        have hHm : Measurable (H r) := (hHc r).measurable
        set μ₁ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (H r '' D) with hμ₁def
        set ν : Measure (Amb n ℓ) := Measure.map (H r) ((volume : Measure (Rn n)).restrict D)
          with hνdef
        have hM1 : μ₁ ≤ ENNReal.ofReal ((1 + ε) ^ n) • ν := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, hνdef, Measure.map_apply hHm hS,
            Measure.restrict_apply (hS.preimage hHm), hμ₁def, Measure.restrict_apply hS, smul_eq_mul]
          have h1 : S ∩ H r '' D = H r '' (D ∩ H r ⁻¹' S) := by
            rw [image_inter_preimage, inter_comm]
          have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipH.mono (inter_subset_left : D ∩ H r ⁻¹' S ⊆ D))
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h2
          rw [h1, inter_comm (H r ⁻¹' S) D, ENNReal.ofReal_pow (by linarith)]
          exact h2
        have hM2 : ENNReal.ofReal ((1 - ε) ^ n) • ν ≤ μ₁ := by
          rw [Measure.le_iff]
          intro S hS
          rw [Measure.smul_apply, hνdef, Measure.map_apply hHm hS,
            Measure.restrict_apply (hS.preimage hHm), hμ₁def, Measure.restrict_apply hS, smul_eq_mul]
          have h1 : H r ⁻¹' S ∩ D ⊆ Hinv '' (S ∩ H r '' D) := by
            rintro z ⟨hzS, hzD⟩
            exact ⟨H r z, ⟨hzS, z, hzD, rfl⟩, hHinv z hzD⟩
          have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipInv.mono (inter_subset_right : S ∩ H r '' D ⊆ H r '' D))
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h2
          have h3 : ENNReal.ofReal ((1 - ε) ^ n) * (ENNReal.ofReal (1 - ε)⁻¹) ^ n = 1 := by
            rw [← ENNReal.ofReal_pow (inv_nonneg.mpr h1ε.le),
              ← ENNReal.ofReal_mul (pow_nonneg h1ε.le n), ← mul_pow, mul_inv_cancel₀ h1ε.ne',
              one_pow, ENNReal.ofReal_one]
          calc ENNReal.ofReal ((1 - ε) ^ n) * volume (H r ⁻¹' S ∩ D)
              ≤ ENNReal.ofReal ((1 - ε) ^ n) * volume (Hinv '' (S ∩ H r '' D)) :=
                mul_le_mul_right (measure_mono h1) _
            _ ≤ ENNReal.ofReal ((1 - ε) ^ n) * ((ENNReal.ofReal (1 - ε)⁻¹) ^ n *
                (μHE[n] : Measure (Amb n ℓ)) (S ∩ H r '' D)) :=
                mul_le_mul_right h2 _
            _ = (μHE[n] : Measure (Amb n ℓ)) (S ∩ H r '' D) := by
                rw [← mul_assoc, h3, one_mul]
        -- integral comparison
        have : IsFiniteMeasure ν := by
          refine ⟨?_⟩
          rw [hνdef, Measure.map_apply hHm MeasurableSet.univ, preimage_univ,
            Measure.restrict_apply MeasurableSet.univ, univ_inter]
          exact hDfin
        have hμ₁fin : μ₁ univ < ∞ := by
          calc μ₁ univ ≤ (ENNReal.ofReal ((1 + ε) ^ n) • ν) univ := hM1 univ
            _ < ∞ := by
              rw [Measure.smul_apply, smul_eq_mul]
              exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ)
        have : IsFiniteMeasure μ₁ := ⟨hμ₁fin⟩
        have hgbd : ∀ y, ‖g y‖ ≤ Cg := fun y => by
          rw [Real.norm_of_nonneg (hg0 y)]
          exact hgC y
        have hgν : Integrable g ν :=
          Integrable.of_bound hgc.aestronglyMeasurable Cg (Eventually.of_forall hgbd)
        have hgμ₁ : Integrable g μ₁ :=
          Integrable.of_bound hgc.aestronglyMeasurable Cg (Eventually.of_forall hgbd)
        have hYeq : ∫ y, g y ∂ν = ∫ z in D, g (H r z) :=
          integral_map hHm.aemeasurable hgc.aestronglyMeasurable
        have hXle : ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) ≤
            (1 + ε) ^ n * ∫ z in D, g (H r z) := by
          have h := integral_mono_measure hM1 (Eventually.of_forall fun y => hg0 y)
            (hgν.smul_measure ENNReal.ofReal_ne_top)
          rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg (by linarith) n), smul_eq_mul,
            hYeq] at h
          exact h
        have hXge : (1 - ε) ^ n * ∫ z in D, g (H r z) ≤
            ∫ y in H r '' D, g y ∂(μHE[n] : Measure (Amb n ℓ)) := by
          have h := integral_mono_measure hM2 (Eventually.of_forall fun y => hg0 y) hgμ₁
          rw [integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg h1ε.le n), smul_eq_mul,
            hYeq] at h
          exact h
        have hY0 : 0 ≤ ∫ z in D, g (H r z) :=
          setIntegral_nonneg measurableSet_closedBall fun z _ => hg0 _
        have hYK : ∫ z in D, g (H r z) ≤ K :=
          (Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const hDfin fun z _ => hgbd _)
        have hpow1 : 1 ≤ (1 + ε) ^ n := one_le_pow₀ (by linarith)
        have hpow2 : (1 - ε) ^ n ≤ 1 := pow_le_one₀ h1ε.le (by linarith)
        rw [dist_zero_right, Real.norm_eq_abs, abs_lt]
        have ha := mul_le_mul_of_nonneg_left hYK (sub_nonneg.mpr hpow1)
        have hb := mul_le_mul_of_nonneg_left hYK (sub_nonneg.mpr hpow2)
        have ha0 := mul_nonneg (sub_nonneg.mpr hpow1) hK0
        have hb0 := mul_nonneg (sub_nonneg.mpr hpow2) hK0
        constructor
        · linarith
        · linarith
      have h := hXY.add hY
      simp only [sub_add_cancel, zero_add] at h
      exact h
    -- `f = f⁺ - f⁻` with `f^± ≥ 0` continuous; apply the squeeze to both parts
    obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    have hCf' : ∀ y, |f y| ≤ Cf := fun y => by
      rw [← Real.norm_eq_abs]
      exact hCf y
    have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf' 0)
    set fp : Amb n ℓ → ℝ := fun y => max (f y) 0
    set fm : Amb n ℓ → ℝ := fun y => max (-f y) 0
    have hfpc : Continuous fp := f.continuous.max continuous_const
    have hfmc : Continuous fm := f.continuous.neg.max continuous_const
    have hfpm : ∀ y, fp y - fm y = f y := fun y => max_zero_sub_max_neg_zero_eq_self (f y)
    have hfpC : ∀ y, fp y ≤ Cf := fun y => max_le ((le_abs_self _).trans (hCf' y)) hCf0
    have hfmC : ∀ y, fm y ≤ Cf := fun y => max_le ((neg_le_abs _).trans (hCf' y)) hCf0
    have hp := hinner fp hfpc (fun y => le_max_right _ _) Cf hfpC
    have hm := hinner fm hfmc (fun y => le_max_right _ _) Cf hfmC
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ∫ y in H r '' D, fp y ∂(μHE[n] : Measure (Amb n ℓ)) -
          ∫ y in H r '' D, fm y ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (G w) r '' (G '' ball c ρ), f y
          ∂(μHE[n] : Measure (Amb n ℓ)) := by
      filter_upwards [hLip 1 one_pos, Ioo_mem_nhdsGT hr₀] with r hr hr'
      have hLipH : LipschitzOnWith (Real.toNNReal 2) (H r) D := by
        refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by norm_num)]
        have h1 := hr z hz z' hz'
        have h2 : ‖ιL z - ιL z'‖ = ‖z - z'‖ := by rw [← map_sub, LinearIsometry.norm_map]
        calc ‖H r z - H r z'‖ = ‖(H r z - H r z' - (ιL z - ιL z')) + (ιL z - ιL z')‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖H r z - H r z' - (ιL z - ιL z')‖ + ‖ιL z - ιL z'‖ := norm_add_le _ _
          _ ≤ 2 * ‖z - z'‖ := by rw [h2]; linarith
      have hfin : (μHE[n] : Measure (Amb n ℓ)) (H r '' D) ≠ ∞ := by
        have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLipH
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
        exact (h.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hDfin)).ne
      have hip : IntegrableOn fp (H r '' D) (μHE[n] : Measure (Amb n ℓ)) :=
        Measure.integrableOn_of_bounded hfin hfpc.aestronglyMeasurable (M := Cf)
          (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (le_max_right _ _)]
            exact hfpC y)
      have him : IntegrableOn fm (H r '' D) (μHE[n] : Measure (Amb n ℓ)) :=
        Measure.integrableOn_of_bounded hfin hfmc.aestronglyMeasurable (M := Cf)
          (Eventually.of_forall fun y => by
            rw [Real.norm_of_nonneg (le_max_right _ _)]
            exact hfmC y)
      rw [hsetint r hr', ← integral_sub hip him]
      congr 1
      funext y
      exact hfpm y
    have hlim : (∫ z in D, fp (ιL z)) - ∫ z in D, fm (ιL z) =
        ∫ y in (P : Set (Amb n ℓ)), f y ∂(μHE[n] : Measure (Amb n ℓ)) := by
      have hιc : Continuous ιL := ιL.continuous
      have hi1 : IntegrableOn (fun z => fp (ιL z)) D (volume : Measure (Rn n)) :=
        (hfpc.comp hιc).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
      have hi2 : IntegrableOn (fun z => fm (ιL z)) D (volume : Measure (Rn n)) :=
        (hfmc.comp hιc).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
      rw [← integral_sub hi1 hi2]
      have h1 : ∫ z in D, (fp (ιL z) - fm (ιL z)) = ∫ z in D, f (ιL z) := by
        congr 1
        funext z
        exact hfpm _
      have hfc : Continuous (fun y : Amb n ℓ => f y) := f.continuous
      rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero, ← integral_map hιc.aemeasurable
        hfc.aestronglyMeasurable, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
        ιL.isometry.map_euclideanHausdorffMeasure, hιrange]
      intro z hz
      apply hfR
      rw [LinearIsometry.norm_map]
      rw [hDdef, mem_closedBall_zero_iff, not_le] at hz
      linarith
    rw [← hlim]
    exact (hp.sub hm).congr' hev
  -- Assembly (parent steps 2, 4): inverse chart `ψ`, `T x = DG(ψ x)(ℝⁿ)`.
  obtain ⟨hmeas, hfin⟩ := hmeasfin
  refine ⟨hmeas, hfin, ?_⟩
  -- the lower bound makes `G` injective on the ball
  have hInjOn : InjOn G (ball c ρ) := by
    intro v hv w hw hvw
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h0 : ‖v - w‖ ≤ 0 := by
      by_contra hcon
      have := mul_pos hκ (lt_of_not_ge hcon)
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  -- the inverse chart `ψ` on `N = G(B')`, Lipschitz with constant `κ⁻¹`
  set ψ : Amb n ℓ → Rn n := Function.invFunOn G (ball c ρ) with hψdef
  have hψG : ∀ v ∈ ball c ρ, ψ (G v) = v := fun v hv => hInjOn.leftInvOn_invFunOn hv
  have hψmaps : MapsTo ψ (G '' ball c ρ) (ball c ρ) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hψG v hv]
    exact hv
  have hψcont : ContinuousOn ψ (G '' ball c ρ) := by
    have hL : LipschitzOnWith (Real.toNNReal κ⁻¹) ψ (G '' ball c ρ) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
      rw [hψG v hv, hψG w hw, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.mpr hκ.le), inv_mul_eq_div, le_div_iff₀ hκ, mul_comm]
      exact hlow v hv w hw
    exact hL.continuousOn
  -- `T x = DG(ψ x)(ℝⁿ)`
  refine ⟨fun x => LinearMap.range (fderiv ℝ G (ψ x)).toLinearMap, ?_, ?_⟩
  · have hD : ContinuousOn (fun x => fderiv ℝ G (ψ x)) (G '' ball c ρ) :=
      (hG.continuous_fderiv one_ne_zero).comp_continuousOn hψcont
    have hmaps : MapsTo (fun x => fderiv ℝ G (ψ x)) (G '' ball c ρ)
        {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} :=
      fun x hx => hinj _ (hψmaps hx)
    exact hproj.comp hD hmaps
  · rintro x ⟨w, hw, rfl⟩
    simp only [hψG w hw]
    exact htan w hw

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

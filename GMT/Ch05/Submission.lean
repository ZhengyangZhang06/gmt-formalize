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

/-- **Radial height bound for general radii** (Simon Ch. 5, Remark 5.3; step 7(b) of the proof of
`AllardRegularityAnyRadius`).  There is `C = C(n) > 0`, independent of `ℓ`, such that if
`0 < r₁ < R`, `u` is `C¹` on `B̆_R(0)` with `u(0) = 0`, `‖Du‖ ≤ 1` there, `|u(x)| ≤ ε|x|` for
`|x| < r₁`, and `∫_{B̆_R(0)} |u(x) − Du(x)x|²/|x|^{n+2} dx ≤ m`, then
`|u(x)| ≤ (ε + C (log(R/r₁) m)^{1/(n+1)}) |x|` on `B̆_R(0)`.

Proof: `W(t, w) = u(tw)/t` satisfies `t |∂ₜW|² = g(tw) tⁿ⁻¹` with
`g(x) = |u(x) − Du(x)x|²/|x|^{n+2}`, so by the fundamental theorem of calculus and Cauchy–Schwarz
`D = W(r, ·) − W(r₁, ·)` has `|D(w)|² ≤ log(R/r₁) ∫ g(sy) sⁿ⁻¹ ds` along the ray through any `y`
in the shell `1/2 ≤ |y| ≤ 1` with direction `w`.  Integrating over the shell, Tonelli and the
scaling `y ↦ sy` (Jacobian `sⁿ`) give `∫_{shell} |D(y/|y|)|² ≤ log(R/r₁) m` (this replaces polar
coordinates).  `D` is `2`-Lipschitz on the sphere, and the shell points whose directions lie
within `t ≤ 1/2` of a unit vector have volume `≥ c tⁿ⁻¹` (they contain a box), so
`|D| ≤ C (log(R/r₁) m)^{1/(n+1)}`; finally `|W(r₁, ·)| ≤ ε` by continuity. -/
theorem any_radius_radial_height : ∀ (n : ℕ), 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u : Rn n → Rn ℓ) (R r₁ ε m : ℝ), 0 < r₁ → r₁ < R → 0 ≤ ε → 0 ≤ m → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ 1) → (∀ x ∈ ball (0 : Rn n) r₁, ‖u x‖ ≤ ε * ‖x‖) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal m → ∀ x ∈ ball (0 : Rn n) R, ‖u x‖ ≤ (ε + C * (Real.log (R / r₁) * m) ^ (1 / ((n : ℝ) + 1))) * ‖x‖ := by
  intro n hn
  -- Step 1 (cap estimate): the shell points `1/2 ≤ |x| ≤ 1` whose direction is within `t ≤ 1/2`
  -- of a unit vector `w₀` have volume `≥ c tⁿ⁻¹`: they contain a box of that volume.
  obtain ⟨c, hc, hcap⟩ : ∃ c : ℝ, 0 < c ∧ ∀ (w₀ : Rn n), ‖w₀‖ = 1 → ∀ (t : ℝ), 0 < t →
      t ≤ 1 / 2 → ENNReal.ofReal (c * t ^ (n - 1)) ≤
        volume {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    set N : ℝ := ((k + 1 : ℕ) : ℝ) with hN
    have hN1 : (1 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    refine ⟨1 / (4 * (4 * N) ^ k), by positivity, ?_⟩
    intro w₀ hw₀ t ht ht2
    rw [Nat.add_sub_cancel]
    set s : ℝ := t / (8 * N) with hs
    have hs0 : 0 < s := by positivity
    set e : Rn (k + 1) := EuclideanSpace.single 0 1 with he
    have he1 : ‖e‖ = 1 := by simp [he]
    set α : Fin (k + 1) → ℝ := Fin.cons (5/8 : ℝ) (fun _ : Fin k => -s) with hα
    set β : Fin (k + 1) → ℝ := Fin.cons (7/8 : ℝ) (fun _ : Fin k => s) with hβ
    set P : Set (Rn (k + 1)) := (WithLp.ofLp : Rn (k + 1) → (Fin (k + 1) → ℝ)) ⁻¹' (Icc α β)
      with hP
    have hPmeas : MeasurableSet P :=
      measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin (k + 1))).measurable
    -- the box `P` (around `(3/4) e`) lies in the sector around `e`
    have hPsub : ∀ x ∈ P, 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - e‖ < t := by
      intro x hx
      have hx' : α ≤ WithLp.ofLp x ∧ WithLp.ofLp x ≤ β := hx
      have h0 : 5/8 ≤ x 0 ∧ x 0 ≤ 7/8 := by
        have h1 := hx'.1 0
        have h2 := hx'.2 0
        simp only [hα, hβ, Fin.cons_zero] at h1 h2
        exact ⟨h1, h2⟩
      have hi : ∀ i : Fin k, |x i.succ| ≤ s := by
        intro i
        have h1 := hx'.1 i.succ
        have h2 := hx'.2 i.succ
        simp only [hα, hβ, Fin.cons_succ] at h1 h2
        exact abs_le.mpr ⟨h1, h2⟩
      set a := x 0 with ha
      set q := ∑ i : Fin k, (x i.succ) ^ 2 with hq
      have hnorm2 : ‖x‖ ^ 2 = a ^ 2 + q := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
      have hq0 : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hqle : q ≤ t ^ 2 / 64 := by
        calc q ≤ ∑ _i : Fin k, s ^ 2 := Finset.sum_le_sum (fun i _ => by
                have h := hi i
                rw [← sq_abs]
                exact pow_le_pow_left₀ (abs_nonneg _) h 2)
          _ = k * s ^ 2 := by simp
          _ ≤ N * s ^ 2 := by
                gcongr
                rw [hN]; push_cast; linarith
          _ = t ^ 2 / (64 * N) := by rw [hs]; field_simp; ring
          _ ≤ t ^ 2 / 64 := by
                apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
                linarith
      have ht2' : t ^ 2 ≤ 1 / 4 := (pow_le_pow_left₀ ht.le ht2 2).trans_eq (by norm_num)
      have hρa : a ≤ ‖x‖ := by
        have : a ^ 2 ≤ ‖x‖ ^ 2 := by rw [hnorm2]; linarith
        exact (sq_le_sq₀ (by linarith [h0.1]) (norm_nonneg x)).mp this
      have hρ0 : 0 < ‖x‖ := by linarith [h0.1]
      have hρ1 : ‖x‖ ≤ 1 := by
        have h7 : a ^ 2 ≤ 49 / 64 :=
          (pow_le_pow_left₀ (by linarith [h0.1]) h0.2 2).trans_eq (by norm_num)
        have hx2 : ‖x‖ ^ 2 ≤ 1 := by rw [hnorm2]; linarith
        exact (pow_le_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).mp hx2
      have hinner : @inner ℝ _ _ x e = a := by
        rw [he, EuclideanSpace.inner_single_right]; simp [ha]
      have hkey : ‖‖x‖⁻¹ • x - e‖ ^ 2 = 2 * (‖x‖ - a) / ‖x‖ := by
        rw [@norm_sub_sq_real, norm_smul, real_inner_smul_left, hinner, he1,
          Real.norm_eq_abs, abs_inv, abs_norm]
        field_simp
        ring
      have hlt : ‖‖x‖⁻¹ • x - e‖ ^ 2 < t ^ 2 := by
        rw [hkey, div_lt_iff₀ hρ0]
        have h1 : (‖x‖ - a) * (‖x‖ + a) = q := by linear_combination hnorm2
        have h2 : (‖x‖ - a) * (5/4) ≤ q := by
          rw [← h1]; exact mul_le_mul_of_nonneg_left (by linarith [h0.1]) (by linarith)
        have h5 : t ^ 2 * (5/8) ≤ t ^ 2 * ‖x‖ :=
          mul_le_mul_of_nonneg_left (by linarith [h0.1]) (sq_nonneg t)
        have h6 : 0 < t ^ 2 := by positivity
        linarith
      refine ⟨by linarith [h0.1], hρ1, ?_⟩
      exact lt_of_pow_lt_pow_left₀ 2 ht.le hlt
    -- the volume of the box
    have hvolP : volume P = ENNReal.ofReal (1 / (4 * (4 * N) ^ k) * t ^ k) := by
      rw [hP, (PiLp.volume_preserving_ofLp (Fin (k + 1))).measure_preimage
        measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Fin.prod_univ_succ]
      simp only [hα, hβ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      have hN0 : N ≠ 0 := (by linarith : (0:ℝ) < N).ne'
      rw [hs, show t / (8 * N) - -(t / (8 * N)) = t / (4 * N) by ring, div_pow, mul_pow]
      field_simp
      ring
    -- a reflection takes `w₀` to `e` and preserves volume
    set T : Rn (k + 1) ≃ₗᵢ[ℝ] Rn (k + 1) :=
      (Submodule.span ℝ {w₀ - e})ᗮ.reflection with hT
    have hTw : T w₀ = e := Submodule.reflection_sub (by rw [hw₀, he1])
    have hsub : T ⁻¹' P ⊆
        {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hPsub (T x) hx
      have hnT : ‖T x‖ = ‖x‖ := T.norm_map x
      rw [hnT] at h1 h2 h3
      refine ⟨h1, h2, ?_⟩
      have hmap : T (‖x‖⁻¹ • x - w₀) = ‖x‖⁻¹ • T x - e := by
        rw [map_sub, map_smul, hTw]
      rw [← T.norm_map, hmap]
      exact h3
    calc ENNReal.ofReal (1 / (4 * (4 * N) ^ k) * t ^ k) = volume P := hvolP.symm
      _ = volume (T ⁻¹' P) :=
          ((T.measurePreserving).measure_preimage hPmeas.nullMeasurableSet).symm
      _ ≤ _ := measure_mono hsub
  -- Step 2 (the constant `C = C(n)`): a `2`-Lipschitz `D` with `|D| ≤ 2` on the unit sphere and
  -- `∫_{shell} |D(x/|x|)|² ≤ m₁` satisfies `|D| ≤ C m₁^{1/(n+1)}` (`|D| ≥ M/2` on a cap).
  obtain ⟨C, hC, hsup⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (D : Rn n → Rn ℓ) (m₁ : ℝ), 0 ≤ m₁ →
      (∀ w w' : Rn n, ‖w‖ = 1 → ‖w'‖ = 1 → ‖D w - D w'‖ ≤ 2 * ‖w - w'‖) →
      (∀ w : Rn n, ‖w‖ = 1 → ‖D w‖ ≤ 2) →
      ∫⁻ x in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) ≤
        ENNReal.ofReal m₁ →
      ∀ w : Rn n, ‖w‖ = 1 → ‖D w‖ ≤ C * m₁ ^ (1 / ((n : ℝ) + 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    set C : ℝ := max (((4 : ℝ) ^ (k + 1) / c) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1))) 1 with hCdef
    refine ⟨C, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro ℓ D m₁ hm₁ hLip hb hint w₀ hw₀
    have hpowm : 0 ≤ m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := Real.rpow_nonneg hm₁ _
    rcases eq_or_lt_of_le (norm_nonneg (D w₀)) with hM0 | hMpos
    · rw [← hM0]
      exact mul_nonneg (lt_of_lt_of_le one_pos (le_max_right _ _)).le hpowm
    set M := ‖D w₀‖ with hM
    set t : ℝ := M / 4 with ht
    have ht0 : 0 < t := by positivity
    have hM2 : M ≤ 2 := hb w₀ hw₀
    have hthalf : t ≤ 1 / 2 := by rw [ht]; linarith
    set A : Set (Rn (k + 1)) := {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} with hA
    set K : Set (Rn (k + 1)) :=
      {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 ∧ ‖‖x‖⁻¹ • x - w₀‖ < t} with hK
    have hKA : K ⊆ A := fun x hx => ⟨hx.1, hx.2.1⟩
    have hKmeas : MeasurableSet K := by
      have hm1 : Measurable (fun x : Rn (k + 1) => ‖‖x‖⁻¹ • x - w₀‖) := by fun_prop
      have : K = {x : Rn (k + 1) | 1 / 2 ≤ ‖x‖} ∩ ({x : Rn (k + 1) | ‖x‖ ≤ 1} ∩
          {x : Rn (k + 1) | ‖‖x‖⁻¹ • x - w₀‖ < t}) := rfl
      rw [this]
      exact (measurableSet_le measurable_const measurable_norm).inter
        ((measurableSet_le measurable_norm measurable_const).inter
          (measurableSet_lt hm1 measurable_const))
    have hlow : ∀ x ∈ K, ENNReal.ofReal ((M / 2) ^ 2) ≤ ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := by
      intro x hx
      have hx0 : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hx.1
      have hxn : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hx0.ne']
      have h1 : ‖D w₀ - D (‖x‖⁻¹ • x)‖ ≤ 2 * ‖w₀ - ‖x‖⁻¹ • x‖ := hLip _ _ hw₀ hxn
      have h2 : ‖w₀ - ‖x‖⁻¹ • x‖ < t := by rw [norm_sub_rev]; exact hx.2.2
      have h3 : M ≤ ‖D (‖x‖⁻¹ • x)‖ + ‖D w₀ - D (‖x‖⁻¹ • x)‖ := by
        rw [hM]; linarith [norm_sub_norm_le (D w₀) (D (‖x‖⁻¹ • x))]
      have h4 : M / 2 ≤ ‖D (‖x‖⁻¹ • x)‖ := by rw [ht] at h2; linarith
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) h4 2)
    have key : ENNReal.ofReal ((M / 2) ^ 2) * ENNReal.ofReal (c * t ^ (k + 1 - 1)) ≤
        ENNReal.ofReal m₁ :=
      calc ENNReal.ofReal ((M / 2) ^ 2) * ENNReal.ofReal (c * t ^ (k + 1 - 1))
          ≤ ENNReal.ofReal ((M / 2) ^ 2) * volume K := by
            gcongr
            exact hcap w₀ hw₀ t ht0 hthalf
        _ = ∫⁻ _ in K, ENNReal.ofReal ((M / 2) ^ 2) := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ x in K, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := setLIntegral_mono' hKmeas hlow
        _ ≤ ∫⁻ x in A, ENNReal.ofReal (‖D (‖x‖⁻¹ • x)‖ ^ 2) := lintegral_mono_set hKA
        _ ≤ ENNReal.ofReal m₁ := hint
    have key' : (M / 2) ^ 2 * (c * t ^ (k + 1 - 1)) ≤ m₁ := by
      rw [← ENNReal.ofReal_mul (by positivity)] at key
      exact (ENNReal.ofReal_le_ofReal_iff hm₁).mp key
    have key2 : M ^ (k + 2) ≤ (4 : ℝ) ^ (k + 1) / c * m₁ := by
      have heq : (M / 2) ^ 2 * (c * t ^ (k + 1 - 1)) = c * M ^ (k + 2) / (4 : ℝ) ^ (k + 1) := by
        rw [ht, Nat.add_sub_cancel, div_pow, div_pow, pow_succ (4 : ℝ) k]
        field_simp
        ring
      rw [heq] at key'
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h4 : (0 : ℝ) < 4 ^ (k + 1) := by positivity
      rw [div_le_iff₀ h4] at key'
      linarith
    have hexp : (1 / (((k + 1 : ℕ) : ℝ) + 1)) = 1 / ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    have hMle : M ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
      rw [hexp]
      have hM0 : 0 ≤ M := norm_nonneg _
      calc M = (M ^ (k + 2)) ^ (1 / ((k + 2 : ℕ) : ℝ)) := by
            rw [one_div, Real.pow_rpow_inv_natCast hM0 (by omega)]
        _ ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / ((k + 2 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow (by positivity) key2 (by positivity)
    calc M ≤ ((4 : ℝ) ^ (k + 1) / c * m₁) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := hMle
      _ = ((4 : ℝ) ^ (k + 1) / c) ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) *
            m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) :=
          Real.mul_rpow (by positivity) hm₁
      _ ≤ C * m₁ ^ (1 / (((k + 1 : ℕ) : ℝ) + 1)) := by
          gcongr
          exact le_max_left _ _
  -- Step 3 (radial integration, replacing polar coordinates): for measurable `h ≥ 0`,
  -- `∫_{shell} ∫_0^∞ h(sy) sⁿ⁻¹ ds dy ≤ ∫ h`, by Tonelli and the scaling `y ↦ sy`, since
  -- `∫_{|z|}^{2|z|} ds/s ≤ 1`.
  have hpolar : ∀ h : Rn n → ℝ≥0∞, Measurable h →
      ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
          ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) ≤ ∫⁻ z, h z := by
    intro h hh
    have hfin : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
    have hAm : MeasurableSet {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
      (measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    have hm1 : Measurable (Function.uncurry fun (y : Rn n) (s : ℝ) =>
        h (s • y) * ENNReal.ofReal (s ^ (n - 1))) :=
      (hh.comp (measurable_snd.smul measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _))
    have hm2 : Measurable (Function.uncurry fun (s : ℝ) (z : Rn n) =>
        ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) := by
      have hset : MeasurableSet {p : ℝ × Rn n | p.1 / 2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ p.1} :=
        (measurableSet_le (measurable_fst.div_const 2) measurable_snd.norm).inter
          (measurableSet_le measurable_snd.norm measurable_fst)
      have heq : (Function.uncurry fun (s : ℝ) (z : Rn n) =>
          ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) =
          fun p : ℝ × Rn n => ENNReal.ofReal p.1⁻¹ *
            {p : ℝ × Rn n | p.1 / 2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ p.1}.indicator (fun p => h p.2) p := by
        funext p
        rfl
      rw [heq]
      exact (ENNReal.measurable_ofReal.comp measurable_fst.inv).mul
        ((hh.comp measurable_snd).indicator hset)
    -- the inner integral over the shell, rescaled by `s`
    have hscale : ∀ s ∈ Ioi (0:ℝ), ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
        h (s • y) * ENNReal.ofReal (s ^ (n - 1)) =
          ∫⁻ z, ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z := by
      intro s hs
      have hs0 : (0:ℝ) < s := hs
      have hBm : MeasurableSet {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} :=
        (measurableSet_le measurable_const measurable_norm).inter
          (measurableSet_le measurable_norm measurable_const)
      have hGm : Measurable ({z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h) :=
        hh.indicator hBm
      have hind : ∀ y : Rn n,
          {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}.indicator (fun y => h (s • y)) y =
            {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h (s • y) := by
        intro y
        have hn : ‖s • y‖ = s * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
        by_cases hy : 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 1
        · have hsy : s / 2 ≤ ‖s • y‖ ∧ ‖s • y‖ ≤ s := by
            rw [hn]
            exact ⟨by linarith [mul_le_mul_of_nonneg_left hy.1 hs0.le],
              mul_le_of_le_one_right hs0.le hy.2⟩
          rw [Set.indicator_of_mem (show y ∈ {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} from hy),
            Set.indicator_of_mem (show s • y ∈ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsy)]
        · have hsy : ¬ (s / 2 ≤ ‖s • y‖ ∧ ‖s • y‖ ≤ s) := by
            rw [hn]
            rintro ⟨h1, h2⟩
            exact hy ⟨le_of_mul_le_mul_left (by linarith : s * (1 / 2) ≤ s * ‖y‖) hs0,
              le_of_mul_le_mul_left (by linarith : s * ‖y‖ ≤ s * 1) hs0⟩
          rw [Set.indicator_of_notMem (show y ∉ {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} from hy),
            Set.indicator_of_notMem (show s • y ∉ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsy)]
      have hconst : ENNReal.ofReal (s ^ (n - 1)) * ENNReal.ofReal |(s ^ n)⁻¹| =
          ENNReal.ofReal s⁻¹ := by
        rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
          ← pow_sub_one_mul (by omega : n ≠ 0) s, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hs0.ne'), one_mul]
      calc ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, h (s • y) * ENNReal.ofReal (s ^ (n - 1))
          = ENNReal.ofReal (s ^ (n - 1)) *
              ∫⁻ y in {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, h (s • y) := by
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
        _ = ENNReal.ofReal (s ^ (n - 1)) *
              ∫⁻ y, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h (s • y) := by
            rw [← lintegral_indicator hAm, lintegral_congr hind]
        _ = ENNReal.ofReal (s ^ (n - 1)) * ∫⁻ z, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z
              ∂(Measure.map (fun y : Rn n => s • y) volume) := by
            rw [lintegral_map hGm (measurable_const_smul s)]
        _ = ENNReal.ofReal (s ^ (n - 1)) * (ENNReal.ofReal |(s ^ n)⁻¹| *
              ∫⁻ z, {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z) := by
            rw [Measure.map_addHaar_smul volume hs0.ne', hfin, lintegral_smul_measure, smul_eq_mul]
        _ = ∫⁻ z, ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z := by
            rw [← mul_assoc, hconst, lintegral_const_mul _ hGm]
    rw [lintegral_lintegral_swap hm1.aemeasurable, setLIntegral_congr_fun measurableSet_Ioi hscale,
      lintegral_lintegral_swap hm2.aemeasurable]
    apply lintegral_mono
    intro z
    calc ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal s⁻¹ * {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s}.indicator h z
        ≤ ∫⁻ s in Ioi (0:ℝ), (Icc ‖z‖ (2 * ‖z‖)).indicator
            (fun _ => ENNReal.ofReal ‖z‖⁻¹ * h z) s := by
          apply setLIntegral_mono' measurableSet_Ioi
          intro s hs
          by_cases hsz : s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s
          · have hs0 : (0:ℝ) < s := hs
            have hz0 : 0 < ‖z‖ := by linarith [hsz.1]
            rw [Set.indicator_of_mem (show z ∈ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsz),
              Set.indicator_of_mem (show s ∈ Icc ‖z‖ (2 * ‖z‖) from ⟨hsz.2, by linarith [hsz.1]⟩)]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (inv_anti₀ hz0 hsz.2)) _
          · rw [Set.indicator_of_notMem (show z ∉ {z : Rn n | s / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ s} from hsz),
              mul_zero]
            exact zero_le
      _ ≤ ∫⁻ s, (Icc ‖z‖ (2 * ‖z‖)).indicator (fun _ => ENNReal.ofReal ‖z‖⁻¹ * h z) s :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal ‖z‖⁻¹ * h z * volume (Icc ‖z‖ (2 * ‖z‖)) :=
          lintegral_indicator_const measurableSet_Icc _
      _ = h z * ENNReal.ofReal (‖z‖⁻¹ * ‖z‖) := by
          rw [Real.volume_Icc, show 2 * ‖z‖ - ‖z‖ = ‖z‖ by ring, mul_comm (ENNReal.ofReal _) (h z),
            mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg z))]
      _ ≤ h z * 1 := by
          gcongr
          rw [ENNReal.ofReal_le_one]
          rcases eq_or_ne ‖z‖ 0 with hz | hz
          · rw [hz]; norm_num
          · rw [inv_mul_cancel₀ hz]
      _ = h z := mul_one _
  refine ⟨C, hC, ?_⟩
  intro ℓ u R r₁ ε m hr₁ hr₁R hε hm hu hu0 hDu hnear hint x hx
  have hR : 0 < R := hr₁.trans hr₁R
  set L : ℝ := Real.log (R / r₁) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hr₁]; linarith)
  have hLm : 0 ≤ L * m := mul_nonneg hL0 hm
  have hCpow : 0 ≤ C * (L * m) ^ (1 / ((n : ℝ) + 1)) :=
    mul_nonneg hC.le (Real.rpow_nonneg hLm _)
  have hcont : ContinuousOn u (ball (0 : Rn n) R) := hu.continuousOn
  -- Step 4 (near zero): `|u(y)| ≤ ε|y|` also on the sphere `|y| = r₁`, by continuity.
  have hbd : ∀ y : Rn n, ‖y‖ = r₁ → ‖u y‖ ≤ ε * ‖y‖ := by
    intro y hy
    have hyR : y ∈ ball (0 : Rn n) R := by
      rw [mem_ball, dist_zero_right, hy]; exact hr₁R
    have hcl : y ∈ closure (ball (0 : Rn n) r₁) := by
      rw [closure_ball (0 : Rn n) hr₁.ne', mem_closedBall, dist_zero_right, hy]
    have hca : ContinuousAt u y := hcont.continuousAt (isOpen_ball.mem_nhds hyR)
    exact ContinuousWithinAt.closure_le hcl
      (continuous_norm.continuousAt.comp hca).continuousWithinAt
      (continuousAt_const.mul continuous_norm.continuousAt).continuousWithinAt hnear
  have hxR : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hx
  rcases lt_or_ge ‖x‖ r₁ with hxr | hxr
  · exact (hnear x (by simpa [mem_ball, dist_zero_right] using hxr)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpow) (norm_nonneg x))
  rcases eq_or_lt_of_le hxr with hxr | hxr
  · exact (hbd x hxr.symm).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpow) (norm_nonneg x))
  -- main case `r₁ < |x| < R`
  set r : ℝ := ‖x‖ with hr
  have hr0 : 0 < r := hr₁.trans hxr
  -- Step 5 (Lipschitz bounds): `W(t, ·) = u(t ·)/t` is `1`-Lipschitz on the sphere, `|W| ≤ 1`.
  have hdiff : ∀ z ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hz)
  have hfd : ContinuousOn (fderiv ℝ u) (ball (0 : Rn n) R) :=
    hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hmv : ∀ y ∈ ball (0 : Rn n) R, ∀ z ∈ ball (0 : Rn n) R, ‖u y - u z‖ ≤ ‖y - z‖ := by
    intro y hy z hz
    have := (convex_ball (0 : Rn n) R).norm_image_sub_le_of_norm_fderiv_le hdiff hDu hz hy
    simpa using this
  have hS5 : ∀ t : ℝ, 0 < t → t < R → ∀ w w' : Rn n, ‖w‖ = 1 → ‖w'‖ = 1 →
      ‖t⁻¹ • u (t • w) - t⁻¹ • u (t • w')‖ ≤ ‖w - w'‖ ∧ ‖t⁻¹ • u (t • w)‖ ≤ 1 := by
    intro t ht htR w w' hw hw'
    have hmem : ∀ v : Rn n, ‖v‖ = 1 → t • v ∈ ball (0 : Rn n) R := by
      intro v hv
      rw [mem_ball, dist_zero_right, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ht]
      exact htR
    have h0 : (0 : Rn n) ∈ ball (0 : Rn n) R := mem_ball_self (ht.trans htR)
    have htinv : ‖t⁻¹‖ = t⁻¹ := by rw [Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    constructor
    · rw [← smul_sub, norm_smul, htinv]
      calc t⁻¹ * ‖u (t • w) - u (t • w')‖ ≤ t⁻¹ * ‖t • w - t • w'‖ := by
            gcongr; exact hmv _ (hmem w hw) _ (hmem w' hw')
        _ = ‖w - w'‖ := by
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht, ← mul_assoc,
              inv_mul_cancel₀ ht.ne', one_mul]
    · rw [norm_smul, htinv]
      calc t⁻¹ * ‖u (t • w)‖ = t⁻¹ * ‖u (t • w) - u 0‖ := by rw [hu0, sub_zero]
        _ ≤ t⁻¹ * ‖t • w - 0‖ := by gcongr; exact hmv _ (hmem w hw) _ h0
        _ = 1 := by
            rw [sub_zero, norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos ht,
              inv_mul_cancel₀ ht.ne']
  set w : Rn n := r⁻¹ • x with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, inv_mul_cancel₀ hr0.ne']
  have hxw : x = r • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  set D : Rn n → Rn ℓ := fun v => r⁻¹ • u (r • v) - r₁⁻¹ • u (r₁ • v) with hD
  have hLip : ∀ v v' : Rn n, ‖v‖ = 1 → ‖v'‖ = 1 → ‖D v - D v'‖ ≤ 2 * ‖v - v'‖ := by
    intro v v' hv hv'
    have h1 := (hS5 r hr0 hxR v v' hv hv').1
    have h2 := (hS5 r₁ hr₁ hr₁R v v' hv hv').1
    calc ‖D v - D v'‖ = ‖(r⁻¹ • u (r • v) - r⁻¹ • u (r • v')) -
          (r₁⁻¹ • u (r₁ • v) - r₁⁻¹ • u (r₁ • v'))‖ := by
          congr 1; simp only [hD]; abel
      _ ≤ ‖r⁻¹ • u (r • v) - r⁻¹ • u (r • v')‖ + ‖r₁⁻¹ • u (r₁ • v) - r₁⁻¹ • u (r₁ • v')‖ :=
          norm_sub_le _ _
      _ ≤ 2 * ‖v - v'‖ := by linarith
  have hDb : ∀ v : Rn n, ‖v‖ = 1 → ‖D v‖ ≤ 2 := by
    intro v hv
    have h1 := (hS5 r hr0 hxR v v hv hv).2
    have h2 := (hS5 r₁ hr₁ hr₁R v v hv hv).2
    calc ‖D v‖ ≤ ‖r⁻¹ • u (r • v)‖ + ‖r₁⁻¹ • u (r₁ • v)‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  set A : Set (Rn n) := {x : Rn n | 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} with hA
  have hAmeas : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  set g : Rn n → ℝ := fun z => ‖u z - fderiv ℝ u z z‖ ^ 2 / ‖z‖ ^ (n + 2) with hg
  set Ω : Set (Rn n) := ball (0 : Rn n) R \ {0} with hΩ
  classical
  set h : Rn n → ℝ≥0∞ := Ω.indicator (fun z => ENNReal.ofReal (g z)) with hh
  have hgcont : ContinuousOn g Ω := by
    have hsub : Ω ⊆ ball (0 : Rn n) R := sdiff_subset
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((hcont.mono hsub).sub ((hfd.mono hsub).clm_apply continuousOn_id)).norm.pow 2
    · exact (continuous_norm.pow _).continuousOn
    · intro z hz
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz.2)
  have hΩmeas : MeasurableSet Ω := measurableSet_ball.diff (measurableSet_singleton 0)
  have hhmeas : Measurable h := by
    have := ContinuousOn.measurable_piecewise (f := fun z => ENNReal.ofReal (g z))
      (g := fun _ => (0 : ℝ≥0∞)) (s := Ω)
      (ENNReal.continuous_ofReal.comp_continuousOn hgcont) continuousOn_const hΩmeas
    have heq : h = Ω.piecewise (fun z => ENNReal.ofReal (g z)) (fun _ => (0 : ℝ≥0∞)) := by
      ext z
      by_cases hz : z ∈ Ω <;> simp [hh, hz, Set.piecewise]
    rw [heq]
    exact this
  -- Step 6 (radial Cauchy–Schwarz along the ray through `y` in the shell, `ρ = |y|`):
  -- `|D(y/ρ)|² ≤ log(R/r₁) ∫_0^∞ h(sy) sⁿ⁻¹ ds`.
  have hpt : ∀ y ∈ A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2) ≤
      ENNReal.ofReal L * ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
    intro y hy
    have hρ0 : 0 < ‖y‖ := lt_of_lt_of_le (by norm_num) hy.1
    have hρ1 : ‖y‖ ≤ 1 := hy.2
    set ρ : ℝ := ‖y‖ with hρ
    set a : ℝ := r₁ / ρ with ha
    set b : ℝ := r / ρ with hb
    have ha0 : 0 < a := div_pos hr₁ hρ0
    have hab : a < b := div_lt_div_of_pos_right hxr hρ0
    have hab' : a ≤ b := hab.le
    have hpos : ∀ s ∈ Icc a b, 0 < s := fun s hs => ha0.trans_le hs.1
    have hnsy : ∀ s : ℝ, 0 < s → ‖s • y‖ = s * ρ := fun s hs => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have hmaps : MapsTo (fun s : ℝ => s • y) (Icc a b) (ball (0 : Rn n) R) := by
      intro s hs
      rw [mem_ball, dist_zero_right, hnsy s (hpos s hs)]
      calc s * ρ ≤ b * ρ := mul_le_mul_of_nonneg_right hs.2 hρ0.le
        _ = r := div_mul_cancel₀ r hρ0.ne'
        _ < R := hxR
    set V' : ℝ → Rn ℓ :=
      fun s => ρ⁻¹ • ((s ^ 2)⁻¹ • (fderiv ℝ u (s • y) (s • y) - u (s • y))) with hV'
    have hderiv : ∀ s ∈ uIcc a b,
        HasDerivAt (fun τ : ℝ => ρ⁻¹ • (τ⁻¹ • u (τ • y))) (V' s) s := by
      intro s hs
      rw [uIcc_of_le hab'] at hs
      have hs0 := hpos s hs
      have h1 : HasDerivAt (fun τ : ℝ => τ • y) y s := by
        simpa using (hasDerivAt_id s).smul_const y
      have h2 : HasDerivAt (fun τ : ℝ => u (τ • y)) (fderiv ℝ u (s • y) y) s :=
        (hdiff _ (hmaps hs)).hasFDerivAt.comp_hasDerivAt s h1
      have h3 : HasDerivAt (fun τ : ℝ => τ⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hs0.ne'
      have h4 := (h3.smul h2).const_smul ρ⁻¹
      convert h4 using 1
      rw [hV']
      dsimp only
      congr 1
      rw [ContinuousLinearMap.map_smul, smul_sub, smul_smul, neg_smul, ← sub_eq_add_neg]
      congr 2
      field_simp
    have hsm : Continuous (fun s : ℝ => s • y) := continuous_id.smul continuous_const
    have hc1 : ContinuousOn (fun s : ℝ => fderiv ℝ u (s • y)) (Icc a b) :=
      hfd.comp hsm.continuousOn hmaps
    have hc2 : ContinuousOn (fun s : ℝ => u (s • y)) (Icc a b) :=
      hcont.comp hsm.continuousOn hmaps
    have hc3 : ContinuousOn (fun s : ℝ => fderiv ℝ u (s • y) (s • y)) (Icc a b) :=
      hc1.clm_apply hsm.continuousOn
    have hc4 : ContinuousOn (fun s : ℝ => (s ^ 2)⁻¹) (Icc a b) :=
      (continuous_pow 2).continuousOn.inv₀ (fun s hs => pow_ne_zero 2 (hpos s hs).ne')
    have hcV : ContinuousOn V' (Icc a b) := (hc4.smul (hc3.sub hc2)).const_smul ρ⁻¹
    have hFTC : ∫ s in a..b, V' s = ρ⁻¹ • (b⁻¹ • u (b • y)) - ρ⁻¹ • (a⁻¹ • u (a • y)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab']; exact hcV))
    have hend : ∀ τ : ℝ, 0 < τ →
        ρ⁻¹ • ((τ / ρ)⁻¹ • u ((τ / ρ) • y)) = τ⁻¹ • u (τ • (ρ⁻¹ • y)) := by
      intro τ hτ
      rw [show (τ / ρ) • y = τ • (ρ⁻¹ • y) by rw [div_eq_mul_inv, mul_smul], smul_smul,
        show ρ⁻¹ * (τ / ρ)⁻¹ = τ⁻¹ by field_simp]
    have hDeq : D (ρ⁻¹ • y) = ∫ s in a..b, V' s := by
      rw [hFTC, ha, hb, hend r hr0, hend r₁ hr₁]
    set J := ∫ s in a..b, ‖V' s‖ with hJ
    set I := ∫ s in a..b, s * ‖V' s‖ ^ 2 with hI
    set L' := Real.log (b / a) with hL'
    have hnorm_le : ‖D (ρ⁻¹ • y)‖ ≤ J := by
      rw [hDeq]; exact intervalIntegral.norm_integral_le_integral_norm hab'
    have hLint : ∫ s in a..b, s⁻¹ = L' := integral_inv_of_pos ha0 (ha0.trans hab)
    have hL'0 : 0 < L' := Real.log_pos ((one_lt_div ha0).mpr hab)
    have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hab' (fun s _ => norm_nonneg _)
    have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hab'
      (fun s hs => mul_nonneg (hpos s hs).le (sq_nonneg _))
    have hcN : ContinuousOn (fun s => ‖V' s‖) (Icc a b) := hcV.norm
    have hcI : ContinuousOn (fun s => s * ‖V' s‖ ^ 2) (Icc a b) := continuousOn_id.mul (hcN.pow 2)
    have hcinv : ContinuousOn (fun s : ℝ => s⁻¹) (Icc a b) :=
      continuousOn_id.inv₀ (fun s hs => (hpos s hs).ne')
    -- Cauchy–Schwarz, in the form `J ≤ (λ/2) L' + I/(2λ)`
    have key : ∀ lam : ℝ, 0 < lam → J ≤ lam / 2 * L' + 1 / (2 * lam) * I := by
      intro lam hlam
      rw [← hLint]
      have hi1 : IntervalIntegrable (fun s => ‖V' s‖) volume a b :=
        ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hab']; exact hcN)
      have hi2 : IntervalIntegrable (fun s : ℝ => lam / 2 * s⁻¹) volume a b :=
        ContinuousOn.intervalIntegrable
          (by rw [uIcc_of_le hab']; exact continuousOn_const.mul hcinv)
      have hi3 : IntervalIntegrable (fun s : ℝ => 1 / (2 * lam) * (s * ‖V' s‖ ^ 2)) volume a b :=
        ContinuousOn.intervalIntegrable
          (by rw [uIcc_of_le hab']; exact continuousOn_const.mul hcI)
      calc J ≤ ∫ s in a..b, (lam / 2 * s⁻¹ + 1 / (2 * lam) * (s * ‖V' s‖ ^ 2)) := by
            apply intervalIntegral.integral_mono_on hab' hi1 (hi2.add hi3)
            intro s hs
            have hs0 := hpos s hs
            set q := ‖V' s‖
            rw [show lam / 2 * s⁻¹ + 1 / (2 * lam) * (s * q ^ 2) =
                (lam ^ 2 + s ^ 2 * q ^ 2) / (2 * lam * s) by field_simp,
              le_div_iff₀ (by positivity)]
            linear_combination sq_nonneg (lam - s * q)
        _ = lam / 2 * (∫ s in a..b, s⁻¹) + 1 / (2 * lam) * I := by
            rw [intervalIntegral.integral_add hi2 hi3, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
    have hJ2 : J ^ 2 ≤ L' * I := by
      rcases eq_or_lt_of_le hJ0 with hJz | hJp
      · rw [← hJz]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg hL'0.le hI0
      · have hk := key (J / L') (by positivity)
        have h1 : J / L' / 2 * L' = J / 2 := by field_simp
        have h2 : 1 / (2 * (J / L')) * I = L' * I / (2 * J) := by field_simp
        rw [h1, h2] at hk
        have h3 : J / 2 ≤ L' * I / (2 * J) := by linarith
        rw [le_div_iff₀ (by positivity)] at h3
        linear_combination h3
    have hsq : ‖D (ρ⁻¹ • y)‖ ^ 2 ≤ L' * I :=
      (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2).trans hJ2
    -- `s |∂ₛ(ρ⁻¹ u(sy)/s)|² = ρⁿ g(sy) sⁿ⁻¹ ≤ g(sy) sⁿ⁻¹`
    have hIlin : ENNReal.ofReal I ≤ ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
      rw [hI, intervalIntegral.integral_of_le hab',
        ofReal_integral_eq_lintegral_ofReal ((hcI.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
            exact mul_nonneg (ha0.trans hs.1).le (sq_nonneg _))]
      calc ∫⁻ s in Ioc a b, ENNReal.ofReal (s * ‖V' s‖ ^ 2)
          ≤ ∫⁻ s in Ioc a b, h (s • y) * ENNReal.ofReal (s ^ (n - 1)) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro s hs
            have hs0 : 0 < s := ha0.trans hs.1
            have hsΩ : s • y ∈ Ω := by
              refine ⟨hmaps ⟨hs.1.le, hs.2⟩, ?_⟩
              intro h0
              have h00 : ‖s • y‖ = 0 := by rw [Set.mem_singleton_iff.mp h0, norm_zero]
              rw [hnsy s hs0] at h00
              exact (mul_pos hs0 hρ0).ne' h00
            have hg0 : 0 ≤ g (s • y) := div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)
            rw [hh, Set.indicator_of_mem hsΩ, ← ENNReal.ofReal_mul hg0]
            apply ENNReal.ofReal_le_ofReal
            show s * ‖V' s‖ ^ 2 ≤
              ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖ ^ 2 / ‖s • y‖ ^ (n + 2) * s ^ (n - 1)
            have hV'n : ‖V' s‖ =
                ρ⁻¹ * ((s ^ 2)⁻¹ * ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖) := by
              show ‖ρ⁻¹ • ((s ^ 2)⁻¹ • (fderiv ℝ u (s • y) (s • y) - u (s • y)))‖ = _
              rw [norm_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
                abs_inv, abs_of_pos hρ0, abs_of_pos (by positivity : (0:ℝ) < s ^ 2)]
            rw [hV'n, hnsy s hs0]
            set E := ‖u (s • y) - fderiv ℝ u (s • y) (s • y)‖
            have hρpow : ρ ^ (n + 2) ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
            have hspow : s ^ (n + 2) = s ^ (n - 1) * s ^ 3 := by
              rw [← pow_add]; congr 1; omega
            rw [mul_pow s ρ (n + 2), hspow]
            have hs1 : 0 < s ^ (n - 1) := pow_pos hs0 _
            calc s * (ρ⁻¹ * ((s ^ 2)⁻¹ * E)) ^ 2 = E ^ 2 / (s ^ 3 * ρ ^ 2) := by
                  field_simp
              _ ≤ E ^ 2 / (s ^ 3 * ρ ^ (n + 2)) := by
                  apply div_le_div_of_nonneg_left (sq_nonneg E) (by positivity)
                  exact mul_le_mul_of_nonneg_left hρpow (by positivity)
              _ = E ^ 2 / (s ^ (n - 1) * s ^ 3 * ρ ^ (n + 2)) * s ^ (n - 1) := by
                  field_simp
        _ ≤ _ := lintegral_mono_set (fun s (hs : s ∈ Ioc a b) => (ha0.trans hs.1 : (0:ℝ) < s))
    have hLL : L' ≤ L := by
      have hba : b / a = r / r₁ := by rw [ha, hb]; field_simp
      rw [hL', hba]
      exact Real.log_le_log (div_pos hr0 hr₁) (div_le_div_of_nonneg_right hxR.le hr₁.le)
    calc ENNReal.ofReal (‖D (ρ⁻¹ • y)‖ ^ 2) ≤ ENNReal.ofReal (L' * I) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal L' * ENNReal.ofReal I := ENNReal.ofReal_mul hL'0.le
      _ ≤ ENNReal.ofReal L * ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hLL) hIlin
  -- Step 7 (integral bound on the sphere): `∫_{shell} |D(y/|y|)|² ≤ log(R/r₁) m`.
  have henergy : ∫⁻ y in A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2) ≤ ENNReal.ofReal (L * m) := by
    calc ∫⁻ y in A, ENNReal.ofReal (‖D (‖y‖⁻¹ • y)‖ ^ 2)
        ≤ ∫⁻ y in A, ENNReal.ofReal L *
            ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          setLIntegral_mono' hAmeas hpt
      _ = ENNReal.ofReal L *
            ∫⁻ y in A, ∫⁻ s in Ioi (0:ℝ), h (s • y) * ENNReal.ofReal (s ^ (n - 1)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal L * ∫⁻ z, h z := mul_le_mul_right (hpolar h hhmeas) _
      _ = ENNReal.ofReal L * ∫⁻ z in Ω, ENNReal.ofReal (g z) := by
          rw [hh, lintegral_indicator hΩmeas]
      _ ≤ ENNReal.ofReal L * ∫⁻ z in ball (0 : Rn n) R, ENNReal.ofReal (g z) :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal m := mul_le_mul_right hint _
      _ = ENNReal.ofReal (L * m) := (ENNReal.ofReal_mul hL0).symm
  -- Step 8 (conclusion): `|u(x)|/|x| ≤ |W(r₁, w)| + |D(w)| ≤ ε + C (log(R/r₁) m)^{1/(n+1)}`.
  have hDw := hsup ℓ D (L * m) hLm hLip hDb henergy w hwn
  have hW1 : ‖r₁⁻¹ • u (r₁ • w)‖ ≤ ε := by
    have hn1 : ‖r₁ • w‖ = r₁ := by
      rw [norm_smul, hwn, mul_one, Real.norm_eq_abs, abs_of_pos hr₁]
    have hb := hbd (r₁ • w) hn1
    rw [hn1] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr₁]
    calc r₁⁻¹ * ‖u (r₁ • w)‖ ≤ r₁⁻¹ * (ε * r₁) := by gcongr
      _ = ε := by field_simp
  have hux : u x = r • (r₁⁻¹ • u (r₁ • w) + D w) := by
    simp only [hD]
    rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, ← hxw]
  calc ‖u x‖ = r * ‖r₁⁻¹ • u (r₁ • w) + D w‖ := by
        rw [hux, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    _ ≤ r * (ε + C * (L * m) ^ (1 / ((n : ℝ) + 1))) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hW1 hDw)
    _ = (ε + C * (L * m) ^ (1 / ((n : ℝ) + 1))) * r := mul_comm _ _

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

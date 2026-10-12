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

/-- Quantitative right inverse on balls of a near-linear self-map of `ℝⁿ`: if
`|A h| ≥ (11/12)|h|` and `Φ` is `ε`-close to `A` on `B_r(0)` with `ε ≤ 1/24`, then every
`w ∈ B_{r/2}(Φ 0)` has a preimage `X w ∈ B_{3r/5}(0)`, unique in `B_r(0)`, and `X` is
`8/7`-Lipschitz on `B_{r/2}(Φ 0)`. -/
theorem arp_rgr_ball_right_inverse : ∀ {n : ℕ} (Φ : Rn n → Rn n) (A : Rn n →L[ℝ] Rn n) (c : Rn n) (r ε : ℝ), 0 < r → 0 ≤ ε → ε ≤ 1 / 24 → (∀ h : Rn n, 11 / 12 * ‖h‖ ≤ ‖A h‖) → (∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r, ‖Φ x₁ - Φ x₂ - A (x₁ - x₂)‖ ≤ ε * ‖x₁ - x₂‖) → Φ 0 = c → ∃ X : Rn n → Rn n, (∀ w ∈ closedBall c (r / 2), X w ∈ closedBall (0 : Rn n) (3 * r / 5) ∧ Φ (X w) = w) ∧ (∀ x ∈ closedBall (0 : Rn n) r, ∀ w ∈ closedBall c (r / 2), Φ x = w → x = X w) ∧ (∀ w₁ ∈ closedBall c (r / 2), ∀ w₂ ∈ closedBall c (r / 2), 7 / 8 * ‖X w₁ - X w₂‖ ≤ ‖w₁ - w₂‖) := by
  intro n Φ A c r ε hr hε0 hε hA hΦ hc
  -- Step 1: `(7/8)|x₁ − x₂| ≤ |Φ(x₁) − Φ(x₂)|` for `x₁, x₂ ∈ B_r(0)`.
  have hinj : ∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r,
      7 / 8 * ‖x₁ - x₂‖ ≤ ‖Φ x₁ - Φ x₂‖ := by
    intro x₁ hx₁ x₂ hx₂
    have h₁ := hA (x₁ - x₂)
    have h₂ := hΦ x₁ hx₁ x₂ hx₂
    have h₃ : ‖A (x₁ - x₂)‖ ≤ ‖Φ x₁ - Φ x₂‖ + ‖Φ x₁ - Φ x₂ - A (x₁ - x₂)‖ :=
      calc ‖A (x₁ - x₂)‖ = ‖(Φ x₁ - Φ x₂) - (Φ x₁ - Φ x₂ - A (x₁ - x₂))‖ := by
            rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have h₄ : ε * ‖x₁ - x₂‖ ≤ 1 / 24 * ‖x₁ - x₂‖ :=
      mul_le_mul_of_nonneg_right hε (norm_nonneg _)
    linarith
  -- Step 2: `A` is injective, hence bijective, with a right inverse of norm `≤ 12/11`.
  have hAinj : Function.Injective A := by
    intro a b hab
    have h := hA (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h
    have h' : ‖a - b‖ = 0 := le_antisymm (by linarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h')
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := (A : Rn n →ₗ[ℝ] Rn n))).mp hAinj
  let Ainv : A.NonlinearRightInverse :=
    { toFun := Function.surjInv hAsurj
      nnnorm := 12 / 11
      bound' := fun k => by
        have h := hA (Function.surjInv hAsurj k)
        rw [Function.surjInv_eq hAsurj] at h
        push_cast
        linarith
      right_inv' := Function.surjInv_eq hAsurj }
  -- Step 3: `B_{r/2}(c) ⊆ Φ(B_{3r/5}(0))`, by the contraction argument packaged in
  -- `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`.
  have happrox : ApproximatesLinearOn Φ A (closedBall 0 r) ⟨ε, hε0⟩ := hΦ
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse Ainv (ε := 3 * r / 5)
    (b := 0) (by positivity) (closedBall_subset_closedBall (by linarith))
  have hball : closedBall c (r / 2) ⊆
      closedBall (Φ 0) (((Ainv.nnnorm : ℝ)⁻¹ - ((⟨ε, hε0⟩ : ℝ≥0) : ℝ)) * (3 * r / 5)) := by
    rw [hc]
    refine closedBall_subset_closedBall ?_
    show r / 2 ≤ (((12 / 11 : ℝ≥0) : ℝ)⁻¹ - ε) * (3 * r / 5)
    push_cast
    nlinarith
  have hex : ∀ w ∈ closedBall c (r / 2), ∃ x ∈ closedBall (0 : Rn n) (3 * r / 5), Φ x = w :=
    fun w hw => hsurj (hball hw)
  -- Step 4: `X(w)` is a chosen preimage for `w ∈ B_{r/2}(c)`, and `0` otherwise.
  classical
  let X : Rn n → Rn n := fun w =>
    if hw : w ∈ closedBall c (r / 2) then (hex w hw).choose else 0
  have hX : ∀ w ∈ closedBall c (r / 2),
      X w ∈ closedBall (0 : Rn n) (3 * r / 5) ∧ Φ (X w) = w := by
    intro w hw
    simp only [X, hw, ↓reduceDIte]
    exact (hex w hw).choose_spec
  have hXr : ∀ w ∈ closedBall c (r / 2), X w ∈ closedBall (0 : Rn n) r := fun w hw =>
    closedBall_subset_closedBall (by linarith) (hX w hw).1
  refine ⟨X, hX, ?_, ?_⟩
  · -- Step 5: a preimage in `B_r(0)` is `X(w)`.
    intro x hx w hw hxw
    have h := hinj x hx (X w) (hXr w hw)
    rw [hxw, (hX w hw).2, sub_self, norm_zero] at h
    have h' : ‖x - X w‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - X w)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h')
  · -- Step 6: `(7/8)|X(w₁) − X(w₂)| ≤ |w₁ − w₂|`.
    intro w₁ hw₁ w₂ hw₂
    have h := hinj (X w₁) (hXr w₁ hw₁) (X w₂) (hXr w₂ hw₂)
    rwa [(hX w₁ hw₁).2, (hX w₂ hw₂).2] at h
/-- Simon Ch. 5, proof of Theorem 5.2 / Remark 5.3 (re-graphing over a rotated plane): regularity
of a continuous right inverse.  Let `U, W ⊆ ℝⁿ` be open, `κ > 0`, `Φ` `C¹` on `U` with
`κ |h| ≤ |DΦ(x) h|` for `x ∈ U`, and `X` continuous on `W` with `X(w) ∈ U` and `Φ(X(w)) = w` for
`w ∈ W`.  Then `X` is `C¹` on `W` and `‖DX(w)‖ ≤ κ⁻¹`.  Each `DΦ(x)` is injective, hence (finite
dimension) invertible with `‖DΦ(x)⁻¹‖ ≤ κ⁻¹`; the local-left-inverse rule gives
`DX(w) = DΦ(X(w))⁻¹ = Ring.inverse (DΦ(X(w)))`, which is continuous in `w` because `X`, `DΦ` and
`Ring.inverse` (at units of the complete normed ring of endomorphisms) are. -/
theorem arp_rgr_right_inverse_contDiffOn : ∀ {n : ℕ} (Φ X : Rn n → Rn n) (U W : Set (Rn n)) (κ : ℝ), IsOpen U → IsOpen W → 0 < κ → ContDiffOn ℝ 1 Φ U → (∀ x ∈ U, ∀ h : Rn n, κ * ‖h‖ ≤ ‖fderiv ℝ Φ x h‖) → ContinuousOn X W → (∀ w ∈ W, X w ∈ U ∧ Φ (X w) = w) → ContDiffOn ℝ 1 X W ∧ ∀ w ∈ W, ‖fderiv ℝ X w‖ ≤ κ⁻¹ := by
  intro n Φ X U W κ hU hW hκ hΦ hlow hX hXW
  -- Step 1: for `x ∈ U`, `DΦ(x)` is a continuous linear equivalence `E x` with `‖(E x)⁻¹‖ ≤ κ⁻¹`.
  have hequiv : ∀ x ∈ U, ∃ L : Rn n ≃L[ℝ] Rn n, (L : Rn n →L[ℝ] Rn n) = fderiv ℝ Φ x ∧
      ‖(L.symm : Rn n →L[ℝ] Rn n)‖ ≤ κ⁻¹ := by
    intro x hx
    -- `κ |a − b| ≤ |DΦ(x)(a − b)|`, so `DΦ(x)` is injective, hence bijective (finite dimension).
    have hinj : Function.Injective (fderiv ℝ Φ x) := by
      intro a b hab
      have h1 := hlow x hx (a - b)
      rw [map_sub, hab, sub_self, norm_zero] at h1
      have h2 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
    let L : Rn n ≃L[ℝ] Rn n :=
      (LinearEquiv.ofInjectiveEndo (fderiv ℝ Φ x).toLinearMap hinj).toContinuousLinearEquiv
    refine ⟨L, ContinuousLinearMap.ext fun v => rfl, ?_⟩
    -- `κ |L⁻¹ k| ≤ |L (L⁻¹ k)| = |k|`.
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hκ.le) fun k => ?_
    rw [le_inv_mul_iff₀ hκ]
    have h1 := hlow x hx (L.symm k)
    have h2 : fderiv ℝ Φ x (L.symm k) = k := L.apply_symm_apply k
    rw [h2] at h1
    exact h1
  choose! E hE hEn using hequiv
  -- Step 2: `Φ` has derivative `E x` at each `x ∈ U`, and `DΦ` is continuous on `U`.
  have hΦd : ∀ x ∈ U, HasFDerivAt Φ (E x : Rn n →L[ℝ] Rn n) x := by
    intro x hx
    rw [hE x hx]
    exact ((hΦ.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hΦc : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Step 3: by the local-left-inverse rule, `X` has derivative `(E (X w))⁻¹` at `w ∈ W`.
  have hXd : ∀ w ∈ W, HasFDerivAt X ((E (X w)).symm : Rn n →L[ℝ] Rn n) w := by
    intro w hw
    have hfg : ∀ᶠ y in 𝓝 w, Φ (X y) = y :=
      Filter.eventually_of_mem (hW.mem_nhds hw) fun y hy => (hXW y hy).2
    exact HasFDerivAt.of_local_left_inverse (hX.continuousAt (hW.mem_nhds hw))
      (hΦd (X w) (hXW w hw).1) hfg
  have hXfd : ∀ w ∈ W, fderiv ℝ X w = ((E (X w)).symm : Rn n →L[ℝ] Rn n) :=
    fun w hw => (hXd w hw).fderiv
  -- Step 4: `DX(w) = Ring.inverse (DΦ(X w))`, the inverse of the unit `(E (X w)).toUnit`.
  have hXinv : ∀ w ∈ W, fderiv ℝ X w = Ring.inverse (fderiv ℝ Φ (X w)) := by
    intro w hw
    rw [hXfd w hw, ← hE (X w) (hXW w hw).1]
    have : ((E (X w)).toUnit : Rn n →L[ℝ] Rn n) = (E (X w) : Rn n →L[ℝ] Rn n) := rfl
    rw [← this, Ring.inverse_unit]
    rfl
  -- Step 5: `DX` is continuous on `W`: `X`, `DΦ` and `Ring.inverse` (at units) are continuous.
  have hcont : ContinuousOn (fderiv ℝ X) W := by
    intro w hw
    have hxU := (hXW w hw).1
    have h1 : ContinuousAt (fun w' => fderiv ℝ Φ (X w')) w :=
      (hΦc.continuousAt (hU.mem_nhds hxU)).comp (hX.continuousAt (hW.mem_nhds hw))
    have h2 : ContinuousAt Ring.inverse (fderiv ℝ Φ (X w)) := by
      rw [← hE (X w) hxU]
      exact NormedRing.inverse_continuousAt (E (X w)).toUnit
    have h3 : ContinuousAt (fun w' => Ring.inverse (fderiv ℝ Φ (X w'))) w :=
      ContinuousAt.comp (f := fun w' => fderiv ℝ Φ (X w')) h2 h1
    have h4 : (fun w' => Ring.inverse (fderiv ℝ Φ (X w'))) =ᶠ[𝓝 w] fderiv ℝ X :=
      Filter.eventually_of_mem (hW.mem_nhds hw) fun y hy => (hXinv y hy).symm
    exact (h3.congr h4).continuousWithinAt
  refine ⟨?_, fun w hw => ?_⟩
  · -- Step 6: differentiable with continuous derivative on the open set `W`, so `C¹` on `W`.
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm,
      contDiffOn_succ_iff_fderiv_of_isOpen hW]
    exact ⟨fun w hw => (hXd w hw).differentiableAt.differentiableWithinAt, by simp,
      contDiffOn_zero.2 hcont⟩
  · rw [hXfd w hw]
    exact hEn (X w) (hXW w hw).1
/-- Simon Ch. 5, proof of Theorem 5.2 / Remark 5.3 (re-graphing over a rotated plane): for a linear
isometry `q` of `ℝ^{n+ℓ}`, `y ∈ ℝ^{n+ℓ}` and `v` `C¹` on the open set `U ⊆ ℝⁿ`, the graph map
`Ψ(x) = y + q(x, v(x))` is `C¹` on `U` with `DΨ(x) h = q(h, Dv(x) h)`.  With
`E = EuclideanSpace.finAddEquivProd` we have `graphPoint a b = E⁻¹ (a, b)`, so
`Ψ = y + L ∘ (id, v)` for the continuous linear map `L = q ∘ E⁻¹`; then apply the product and chain
rules. -/
theorem arp_rgr_graph_map_fderiv : ∀ {n ℓ : ℕ} (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ) (y : Amb n ℓ) (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ 1 v U → ContDiffOn ℝ 1 (fun x => y + q (graphPoint x (v x))) U ∧ ∀ x ∈ U, ∀ h : Rn n, fderiv ℝ (fun x => y + q (graphPoint x (v x))) x h = q (graphPoint h (fderiv ℝ v x h)) := by
  intro n ℓ q v y U hU hv
  -- Step 1: `graphPoint a b = E⁻¹ (a, b)`, checked coordinatewise (`Fin.append_left/right`).
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b =
      (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (a, b) := by
    intro a b
    apply (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ext i <;> simp [graphPoint]
  -- Step 2: `Ψ(x) = y + L (x, v x)` for the continuous linear map `L = q ∘ E⁻¹`.
  let L : Rn n × Rn ℓ →L[ℝ] Amb n ℓ :=
    (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
        Rn n × Rn ℓ →L[ℝ] Amb n ℓ)
  have hL : ∀ a b, L (a, b) = q (graphPoint a b) := by
    intro a b
    simp [L, hgp]
  have hΨ : (fun x => y + q (graphPoint x (v x))) = fun x => y + L (x, v x) := by
    funext x
    rw [hL]
  refine ⟨?_, ?_⟩
  · -- Step 3: `x ↦ (x, v x)` is `C¹` on `U`; compose with `L` and add the constant `y`.
    rw [hΨ]
    exact contDiffOn_const.add (L.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hv))
  · -- Step 4: `U` is open, so `v` is differentiable at `x`; then the product and chain rules.
    intro x hx h
    have hvx : HasFDerivAt v (fderiv ℝ v x) x :=
      ((hv.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hpair : HasFDerivAt (fun x' => (x', v x'))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ v x)) x :=
      (hasFDerivAt_id x).prodMk hvx
    have hΨx : HasFDerivAt (fun x' => y + L (x', v x'))
        (L.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ v x))) x :=
      (L.hasFDerivAt.comp x hpair).const_add y
    rw [hΨ, hΨx.fderiv]
    simp [hL]
/-- The graph point `(x, y) ∈ ℝ^{n+ℓ}` is the inverse image of `(x, y)` under Mathlib's canonical
equivalence `EuclideanSpace.finAddEquivProd : ℝ^{n+ℓ} ≃L[ℝ] ℝⁿ × ℝ^ℓ` (reindexing by
`finSumFinEquiv.symm`, then splitting into the `Sum.inl`/`Sum.inr` parts).  Compare coordinates:
every index of `Fin (n + ℓ)` is `Fin.castAdd ℓ j` or `Fin.natAdd n k` (`Fin.addCases`); there both
sides equal `x j`, resp. `y k` (`Fin.append_left`/`Fin.append_right` on the left,
`finSumFinEquiv_symm_apply_castAdd`/`finSumFinEquiv_symm_apply_natAdd` on the right). -/
theorem rsod_graphPoint_eq_finAddEquivProd_symm : ∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ),
    graphPoint x y = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (x, y) := by
  intro n ℓ x y
  ext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp [graphPoint]
  · simp [graphPoint]
/-- Pythagorean identity for graph points: `|(x, y)|² = |x|² + |y|²` for the point
`(x, y) ∈ ℝⁿ × ℝ^ℓ = ℝ^{n+ℓ}`.  Expand the three squared Euclidean norms as sums of squared
coordinates (`EuclideanSpace.real_norm_sq_eq`), split the sum over `Fin (n + ℓ)` into the indices
`Fin.castAdd ℓ j` and `Fin.natAdd n k` (`Fin.sum_univ_add`), and read off the coordinates `x j`,
resp. `y k`, of `graphPoint x y` there (`Fin.append_left`/`Fin.append_right`). -/
theorem rsod_norm_graphPoint_sq : ∀ {n ℓ : ℕ} (x : Rn n) (y : Rn ℓ),
    ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  intro n ℓ x y
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]
  simp [graphPoint]

/-- Coordinates adapted to a rotated plane `q₀(ℝⁿ × {0})`: (i) the graph point `(a, b)` is
`E⁻¹(a, b)` for `E = EuclideanSpace.finAddEquivProd`; (ii) `|(a, b)|² = |a|² + |b|²`; and
(iii) `dist(q₀(a, b), q₀(ℝⁿ × {0})) = |b|`.  (i) and (ii) are
`rsod_graphPoint_eq_finAddEquivProd_symm` and `rsod_norm_graphPoint_sq`.  For (iii), the isometry
`q₀` maps `H = ℝⁿ × {0}` onto `rotatedPlane q₀` (`Submodule.map_coe`, `Metric.infDist_image`), and
`H = {(a', 0)}`: `(a', 0) = Σᵢ a'ᵢ eᵢ ∈ H`, and `H` lies in the range of the linear map
`a' ↦ E⁻¹(a', 0)`, which contains every generator `eᵢ = (eᵢ, 0)` (`Submodule.span_le`).  By (i),
`(a, b) - (a', 0) = (a - a', b)`, so `(a, 0) ∈ H` is at distance `|(0, b)| = |b|`, and by (ii)
every `(a', 0)` is at distance `|(a - a', b)| ≥ |b|` (`Metric.le_infDist`). -/
theorem arp_rotatedPlane_graphPoint_coords : ∀ (n ℓ : ℕ),
    (∀ (a : Rn n) (b : Rn ℓ),
      graphPoint a b = (EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm (a, b)) ∧
    (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧
    ∀ (q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (a : Rn n) (b : Rn ℓ),
      infDist (q₀ (graphPoint a b)) (rotatedPlane q₀ : Set (Amb n ℓ)) = ‖b‖ := by
  intro n ℓ
  refine ⟨fun a b => rsod_graphPoint_eq_finAddEquivProd_symm a b,
    fun a b => rsod_norm_graphPoint_sq a b, fun q₀ a b => ?_⟩
  -- graph points are linear in the pair, as `E⁻¹` is
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    rw [rsod_graphPoint_eq_finAddEquivProd_symm, rsod_graphPoint_eq_finAddEquivProd_symm,
      rsod_graphPoint_eq_finAddEquivProd_symm, ← map_sub, Prod.mk_sub_mk]
  let L : Rn n →ₗ[ℝ] Amb n ℓ :=
    ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
      Rn n × Rn ℓ →L[ℝ] Amb n ℓ).toLinearMap ∘ₗ LinearMap.inl ℝ (Rn n) (Rn ℓ)
  have hL : ∀ a' : Rn n, L a' = graphPoint a' 0 := by
    intro a'
    rw [rsod_graphPoint_eq_finAddEquivProd_symm]
    rfl
  have hl : ∀ (a' : Rn n) (b' : Rn ℓ) (i : Fin n), graphPoint a' b' (Fin.castAdd ℓ i) = a' i := by
    intro a' b' i
    simp [graphPoint]
  have hr : ∀ (a' : Rn n) (b' : Rn ℓ) (j : Fin ℓ), graphPoint a' b' (Fin.natAdd n j) = b' j := by
    intro a' b' j
    simp [graphPoint]
  have hne : ∀ (i : Fin n) (j : Fin ℓ), Fin.natAdd n j ≠ Fin.castAdd ℓ i := by
    intro i j h
    have h' := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
    omega
  -- reduce to the horizontal plane `H`
  have hset : (rotatedPlane q₀ : Set (Amb n ℓ)) = q₀ '' (horizontalPlane n ℓ : Set (Amb n ℓ)) :=
    Submodule.map_coe _ _
  rw [hset, infDist_image q₀.isometry]
  -- `H = {graphPoint a' 0}`
  have hmemH : ∀ a' : Rn n, graphPoint a' 0 ∈ horizontalPlane n ℓ := by
    intro a'
    have e : graphPoint a' (0 : Rn ℓ) =
        ∑ i : Fin n, a' i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
      ext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [hl]
        simp [Pi.single_apply, Fin.castAdd_inj]
      · rw [hr]
        simp [hne]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hHle : horizontalPlane n ℓ ≤ LinearMap.range L := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨EuclideanSpace.single i 1, ?_⟩
    rw [hL]
    ext k
    refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
    · rw [hl]
      simp [Fin.castAdd_inj]
    · rw [hr]
      simp [hne i j]
  have hnorm0 : ‖graphPoint (0 : Rn n) b‖ = ‖b‖ := by
    have h := rsod_norm_graphPoint_sq (0 : Rn n) b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  apply le_antisymm
  · calc infDist (graphPoint a b) (horizontalPlane n ℓ : Set (Amb n ℓ))
        ≤ dist (graphPoint a b) (graphPoint a 0) := infDist_le_dist_of_mem (hmemH a)
      _ = ‖graphPoint (a - a) (b - 0)‖ := by rw [dist_eq_norm, hsub]
      _ = ‖b‖ := by rw [sub_self, sub_zero, hnorm0]
  · refine (le_infDist ⟨0, (horizontalPlane n ℓ).zero_mem⟩).mpr ?_
    intro p hp
    obtain ⟨a', rfl⟩ := hHle hp
    rw [hL, dist_eq_norm, hsub, sub_zero]
    have hsq : ‖b‖ ^ 2 ≤ ‖graphPoint (a - a') b‖ ^ 2 := by
      rw [rsod_norm_graphPoint_sq]
      nlinarith [sq_nonneg ‖a - a'‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Regraphing a `C¹` graph over a rotated plane (step 6 of the any-radius patching argument).
Let `π z`, `σ z` be the coordinates of `q₀⁻¹ z` along `ℝⁿ × {0}` and `{0} × ℝ^ℓ`, so that
`z = q₀(π z, σ z)`, `|z|² = |π z|² + |σ z|²` and `dist(z, T₀) = |σ z|`
(`arp_rotatedPlane_graphPoint_coords`).  The chart `Φ(x) = π(y + q(x, v x)) = c + A x + π(q(0, v x))`,
with `A h = π(q(h, 0))`, satisfies `|A h| ≥ (11/12)|h|` (Pythagoras and the tilt bound) and
`|Φ x₁ - Φ x₂ - A(x₁ - x₂)| ≤ ε|x₁ - x₂|` (mean value inequality), so
`arp_rgr_ball_right_inverse` gives a unique `8/7`-Lipschitz right inverse `X` on `B_{r/2}(c)` with
values in `B_{3r/5}(0)`.  By `arp_rgr_graph_map_fderiv`, `DΦ(x) h = A h + π(q(0, Dv(x) h))` has
`|DΦ(x) h| ≥ (7/8)|h|` on `B̆_r(0)`, so `arp_rgr_right_inverse_contDiffOn` makes `X` `C¹` on
`B̆_{r/2}(c)` with `|DX| ≤ 8/7`.  Then `f := σ ∘ (y + q(·, v ·)) ∘ X` is `C¹`, and
`Df(w) k = σ(q(h, Dv h))` with `h = DX(w) k` has norm `≤ (ϑ + ε)|h| ≤ |h|/8 ≤ |k|/7`; (b) holds
with `x = X w` since `|X w|² + |v(X w)|² ≤ (3r/5)² + (r/40)² ≤ r²`, and (c) is the uniqueness
of `X`. -/
theorem arp_regraph_over_rotatedPlane : ∀ {n ℓ : ℕ} (q q₀ : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (v : Rn n → Rn ℓ) (y : Amb n ℓ) (c : Rn n) (d : Rn ℓ) (r ε ϑ : ℝ), 0 < r → 0 ≤ ε → ε ≤ 1 / 24 → 0 ≤ ϑ → ϑ ≤ 1 / 12 → ContDiffOn ℝ 1 v (closedBall 0 r) → v 0 = 0 → (∀ x ∈ closedBall (0 : Rn n) r, ‖fderivWithin ℝ v (closedBall 0 r) x‖ ≤ ε) → (∀ x : Rn n, infDist (q (graphPoint x 0)) (rotatedPlane q₀ : Set (Amb n ℓ)) ≤ ϑ * ‖x‖) → y = q₀ (graphPoint c d) → ∃ f : Rn n → Rn ℓ, ContDiffOn ℝ 1 f (ball c (r / 2)) ∧ (∀ w ∈ ball c (r / 2), ‖fderiv ℝ f w‖ ≤ 1 / 7) ∧ (∀ w ∈ closedBall c (r / 2), ∃ x ∈ closedBall (0 : Rn n) r, y + q (graphPoint x (v x)) = q₀ (graphPoint w (f w)) ∧ ‖graphPoint x (v x)‖ ≤ r) ∧ (∀ x ∈ closedBall (0 : Rn n) r, ∀ (w : Rn n) (b : Rn ℓ), y + q (graphPoint x (v x)) = q₀ (graphPoint w b) → w ∈ closedBall c (r / 2) → b = f w) := by
  intro n ℓ q q₀ v y c d r ε ϑ hr hε0 hε hϑ0 hϑ hv hv0 hDv htilt hy
  obtain ⟨hG, hG2, hG3⟩ := Submission.arp_rotatedPlane_graphPoint_coords n ℓ
  -- graph points are linear in the pair
  have hGsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint (a - a') (b - b') = graphPoint a b - graphPoint a' b' := by
    intro a a' b b'
    rw [hG, hG, hG, ← map_sub, Prod.mk_sub_mk]
  have hsplit : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = graphPoint a 0 + graphPoint 0 b := by
    intro a b
    rw [hG, hG, hG, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hG0 : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    rw [hG, Prod.mk_zero_zero, map_zero]
  have hnG0 : ∀ b : Rn ℓ, ‖graphPoint (0 : Rn n) b‖ = ‖b‖ := by
    intro b
    have h := hG2 0 b
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hnG0' : ∀ a : Rn n, ‖graphPoint a (0 : Rn ℓ)‖ = ‖a‖ := by
    intro a
    have h := hG2 a 0
    rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  -- step 0: coordinates `π`, `σ` adapted to `T₀ = rotatedPlane q₀`
  obtain ⟨π, σ, hrec, hπ, hσ⟩ : ∃ (π : Amb n ℓ →L[ℝ] Rn n) (σ : Amb n ℓ →L[ℝ] Rn ℓ),
      (∀ z, q₀ (graphPoint (π z) (σ z)) = z) ∧ (∀ a b, π (q₀ (graphPoint a b)) = a) ∧
        ∀ a b, σ (q₀ (graphPoint a b)) = b := by
    let F : Amb n ℓ →L[ℝ] Rn n × Rn ℓ :=
      ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ) :
        Amb n ℓ →L[ℝ] Rn n × Rn ℓ).comp
        (q₀.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ)
    have hF : ∀ a b, F (q₀ (graphPoint a b)) = (a, b) := by
      intro a b
      simp [F, hG]
    refine ⟨(ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp F,
      (ContinuousLinearMap.snd ℝ (Rn n) (Rn ℓ)).comp F, fun z => ?_, fun a b => ?_,
      fun a b => ?_⟩
    · change q₀ (graphPoint (F z).1 (F z).2) = z
      rw [hG, Prod.mk.eta]
      change q₀ ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm
        ((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ) (q₀.symm z))) = z
      rw [ContinuousLinearEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    · simp [hF]
    · simp [hF]
  have hnorm : ∀ z : Amb n ℓ, ‖z‖ ^ 2 = ‖π z‖ ^ 2 + ‖σ z‖ ^ 2 := by
    intro z
    conv_lhs => rw [← hrec z]
    rw [LinearIsometryEquiv.norm_map, hG2]
  have hπle : ∀ z : Amb n ℓ, ‖π z‖ ≤ ‖z‖ := by
    intro z
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    linarith [hnorm z, sq_nonneg ‖σ z‖]
  have hσle : ∀ z : Amb n ℓ, ‖σ z‖ ≤ ‖z‖ := by
    intro z
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
    linarith [hnorm z, sq_nonneg ‖π z‖]
  have hπy : π y = c := by rw [hy, hπ]
  -- the linear part `A h = π (q (h, 0))` and the splitting of `π ∘ q` and `σ ∘ q`
  obtain ⟨A, hA⟩ : ∃ A : Rn n →L[ℝ] Rn n, ∀ h, A h = π (q (graphPoint h 0)) := by
    refine ⟨π.comp ((q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).comp
      (((EuclideanSpace.finAddEquivProd : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ).symm :
        Rn n × Rn ℓ →L[ℝ] Amb n ℓ).comp (ContinuousLinearMap.inl ℝ (Rn n) (Rn ℓ)))),
      fun h => ?_⟩
    simp [hG]
  have hπq : ∀ (a : Rn n) (b : Rn ℓ), π (q (graphPoint a b)) = A a + π (q (graphPoint 0 b)) := by
    intro a b
    rw [hsplit a b, map_add, map_add, hA]
  have hσq : ∀ (a : Rn n) (b : Rn ℓ),
      σ (q (graphPoint a b)) = σ (q (graphPoint a 0)) + σ (q (graphPoint 0 b)) := by
    intro a b
    rw [hsplit a b, map_add, map_add]
  have hπq0 : ∀ b : Rn ℓ, ‖π (q (graphPoint 0 b))‖ ≤ ‖b‖ := fun b =>
    (hπle _).trans_eq (by rw [LinearIsometryEquiv.norm_map, hnG0])
  have hσq0 : ∀ b : Rn ℓ, ‖σ (q (graphPoint 0 b))‖ ≤ ‖b‖ := fun b =>
    (hσle _).trans_eq (by rw [LinearIsometryEquiv.norm_map, hnG0])
  -- the tilt hypothesis: `|σ (q (h, 0))| = dist(q (h, 0), T₀) ≤ ϑ |h|`
  have hV : ∀ h : Rn n, ‖σ (q (graphPoint h 0))‖ ≤ ϑ * ‖h‖ := by
    intro h
    have e : infDist (q (graphPoint h 0)) (rotatedPlane q₀ : Set (Amb n ℓ)) =
        ‖σ (q (graphPoint h 0))‖ := by
      conv_lhs => rw [← hrec (q (graphPoint h 0))]
      exact hG3 q₀ _ _
    rw [← e]
    exact htilt h
  -- step 2: `|A h| ≥ (11/12)|h|`
  have hAlow : ∀ h : Rn n, 11 / 12 * ‖h‖ ≤ ‖A h‖ := by
    intro h
    have h1 := hnorm (q (graphPoint h 0))
    rw [LinearIsometryEquiv.norm_map, hnG0', ← hA] at h1
    have h2 : ‖σ (q (graphPoint h 0))‖ ^ 2 ≤ (ϑ * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hV h) 2
    have h3 : (ϑ * ‖h‖) ^ 2 ≤ (1 / 12 * ‖h‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hϑ0 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hϑ (norm_nonneg _)) 2
    refine (pow_le_pow_iff_left₀ (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).mp ?_
    linarith [sq_nonneg ‖h‖]
  -- step 1: mean value bounds for `v`
  have hvlip : ∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r,
      ‖v x₁ - v x₂‖ ≤ ε * ‖x₁ - x₂‖ := fun x₁ h₁ x₂ h₂ =>
    (convex_closedBall (0 : Rn n) r).norm_image_sub_le_of_norm_fderivWithin_le
      (hv.differentiableOn one_ne_zero) hDv h₂ h₁
  have hDvb : ∀ x ∈ ball (0 : Rn n) r, ‖fderiv ℝ v x‖ ≤ ε := by
    intro x hx
    rw [← fderivWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hx)]
    exact hDv x (ball_subset_closedBall hx)
  -- step 3: the chart `Φ x = π (y + q (x, v x))` is `ε`-close to `c + A x`
  have hΦx : ∀ x : Rn n,
      π (y + q (graphPoint x (v x))) = c + A x + π (q (graphPoint 0 (v x))) := by
    intro x
    rw [map_add, hπq, hπy, add_assoc]
  have hΦA : ∀ x₁ ∈ closedBall (0 : Rn n) r, ∀ x₂ ∈ closedBall (0 : Rn n) r,
      ‖π (y + q (graphPoint x₁ (v x₁))) - π (y + q (graphPoint x₂ (v x₂))) - A (x₁ - x₂)‖ ≤
        ε * ‖x₁ - x₂‖ := by
    intro x₁ h₁ x₂ h₂
    have e : graphPoint (0 : Rn n) (v x₁ - v x₂) = graphPoint 0 (v x₁) - graphPoint 0 (v x₂) := by
      rw [← hGsub, sub_zero]
    have e' : π (y + q (graphPoint x₁ (v x₁))) - π (y + q (graphPoint x₂ (v x₂))) - A (x₁ - x₂) =
        π (q (graphPoint 0 (v x₁ - v x₂))) := by
      rw [hΦx, hΦx, e, map_sub, map_sub, map_sub]
      abel
    rw [e']
    exact (hπq0 _).trans (hvlip x₁ h₁ x₂ h₂)
  have hΦ0 : π (y + q (graphPoint 0 (v 0))) = c := by
    rw [hv0, hG0, map_zero, add_zero, hπy]
  -- steps 4, 5, 7, 9: the right inverse `X` of the chart
  obtain ⟨X, hX1, hX2, hX3⟩ := Submission.arp_rgr_ball_right_inverse
    (fun x => π (y + q (graphPoint x (v x)))) A c r ε hr hε0 hε hAlow hΦA hΦ0
  beta_reduce at hX1 hX2
  have hXU : ∀ w ∈ ball c (r / 2),
      X w ∈ ball (0 : Rn n) r ∧ π (y + q (graphPoint (X w) (v (X w)))) = w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hX1 w (ball_subset_closedBall hw)
    exact ⟨closedBall_subset_ball (by linarith) h1, h2⟩
  have hXcont : ContinuousOn X (ball c (r / 2)) := by
    have hlip : LipschitzOnWith 2 X (closedBall c (r / 2)) := by
      refine LipschitzOnWith.of_dist_le_mul fun w₁ h₁ w₂ h₂ => ?_
      rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
      linarith [hX3 w₁ h₁ w₂ h₂, norm_nonneg (X w₁ - X w₂)]
    exact hlip.continuousOn.mono ball_subset_closedBall
  -- step 8: derivatives of the graph map `Ψ` and of the chart `Φ = π ∘ Ψ`
  obtain ⟨hΨ, hDΨ⟩ := Submission.arp_rgr_graph_map_fderiv q v y (ball 0 r) isOpen_ball
    (hv.mono ball_subset_closedBall)
  have hΨd : ∀ x ∈ ball (0 : Rn n) r,
      HasFDerivAt (fun x => y + q (graphPoint x (v x)))
        (fderiv ℝ (fun x => y + q (graphPoint x (v x))) x) x := fun x hx =>
    ((hΨ.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hx)).hasFDerivAt
  have hΦlow : ∀ x ∈ ball (0 : Rn n) r, ∀ h : Rn n,
      7 / 8 * ‖h‖ ≤ ‖fderiv ℝ (fun x => π (y + q (graphPoint x (v x)))) x h‖ := by
    intro x hx h
    have hd : HasFDerivAt (fun x => π (y + q (graphPoint x (v x))))
        (π.comp (fderiv ℝ (fun x => y + q (graphPoint x (v x))) x)) x :=
      π.hasFDerivAt.comp x (hΨd x hx)
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, hDΨ x hx h, hπq]
    have h1 : ‖π (q (graphPoint 0 (fderiv ℝ v x h)))‖ ≤ ε * ‖h‖ :=
      (hπq0 _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDvb x hx) (norm_nonneg _)))
    have h2 := norm_sub_le (A h + π (q (graphPoint 0 (fderiv ℝ v x h))))
      (π (q (graphPoint 0 (fderiv ℝ v x h))))
    rw [add_sub_cancel_right] at h2
    linarith [hAlow h, mul_le_mul_of_nonneg_right hε (norm_nonneg h)]
  -- the normal component of `DΨ` is small: `|σ (q (h, Dv h))| ≤ (ϑ + ε)|h| ≤ |h|/8`
  have hσDΨ : ∀ x ∈ ball (0 : Rn n) r, ∀ h : Rn n,
      ‖σ (q (graphPoint h (fderiv ℝ v x h)))‖ ≤ 1 / 8 * ‖h‖ := by
    intro x hx h
    rw [hσq]
    have h1 : ‖σ (q (graphPoint 0 (fderiv ℝ v x h)))‖ ≤ ε * ‖h‖ :=
      (hσq0 _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDvb x hx) (norm_nonneg _)))
    linarith [norm_add_le (σ (q (graphPoint h 0))) (σ (q (graphPoint 0 (fderiv ℝ v x h)))),
      hV h, mul_le_mul_of_nonneg_right hε (norm_nonneg h),
      mul_le_mul_of_nonneg_right hϑ (norm_nonneg h)]
  -- steps 10, 11: `X` is `C¹` with `|DX| ≤ 8/7`
  obtain ⟨hXC, hDX⟩ := Submission.arp_rgr_right_inverse_contDiffOn
    (fun x => π (y + q (graphPoint x (v x)))) X (ball 0 r) (ball c (r / 2)) (7 / 8)
    isOpen_ball isOpen_ball (by norm_num) (hΨ.continuousLinearMap_comp π) hΦlow hXcont hXU
  refine ⟨fun w => σ (y + q (graphPoint (X w) (v (X w)))),
    (hΨ.comp hXC fun w hw => (hXU w hw).1).continuousLinearMap_comp σ, ?_, ?_, ?_⟩
  · -- (a): `|Df| ≤ (1/8)(8/7) = 1/7`
    intro w hw
    have hXd : HasFDerivAt X (fderiv ℝ X w) w :=
      ((hXC.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hw)).hasFDerivAt
    have hd : HasFDerivAt (fun w => σ (y + q (graphPoint (X w) (v (X w)))))
        (σ.comp ((fderiv ℝ (fun x => y + q (graphPoint x (v x))) (X w)).comp
          (fderiv ℝ X w))) w :=
      σ.hasFDerivAt.comp w ((hΨd (X w) (hXU w hw).1).comp w hXd)
    rw [hd.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun k => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hDΨ _ (hXU w hw).1]
    have h1 := hσDΨ (X w) (hXU w hw).1 (fderiv ℝ X w k)
    have h2 : ‖fderiv ℝ X w k‖ ≤ (7 / 8)⁻¹ * ‖k‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDX w hw) (norm_nonneg _))
    norm_num at h2
    linarith
  · -- (b): the point `x = X w`
    intro w hw
    obtain ⟨h1, h2⟩ := hX1 w hw
    refine ⟨X w, closedBall_subset_closedBall (by linarith) h1, ?_, ?_⟩
    · conv_lhs => rw [← hrec (y + q (graphPoint (X w) (v (X w))))]
      rw [h2]
    · have hx : ‖X w‖ ≤ 3 * r / 5 := mem_closedBall_zero_iff.mp h1
      have hvx : ‖v (X w)‖ ≤ ε * ‖X w‖ := by
        have h := hvlip (X w) (closedBall_subset_closedBall (by linarith) h1) 0
          (mem_closedBall_self hr.le)
        rwa [hv0, sub_zero, sub_zero] at h
      have hvx' : ‖v (X w)‖ ≤ r / 40 := by
        linarith [mul_le_mul_of_nonneg_left hx hε0,
          mul_le_mul_of_nonneg_right hε (by linarith : (0 : ℝ) ≤ 3 * r / 5)]
      have e1 : ‖X w‖ ^ 2 ≤ (3 * r / 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
      have e2 : ‖v (X w)‖ ^ 2 ≤ (r / 40) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvx' 2
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp ?_
      linarith [hG2 (X w) (v (X w)), sq_nonneg r]
  · -- (c): uniqueness of `X`
    intro x hx w b heq hw
    have hxX : x = X w := hX2 x hx w hw (by rw [heq, hπ])
    show b = σ (y + q (graphPoint (X w) (v (X w))))
    rw [← hxX, heq, hσ]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

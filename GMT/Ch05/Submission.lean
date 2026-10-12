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

/-- **Hole estimate** (Simon Ch. 5, proof of Lemma 2.6, (9)–(10)).  If `ζ ∈ F` lies at distance
`d = 2s ∈ (0, σ₀/16]` from `spt V`, then `sⁿ ≤ C₀ (μ_V(B_{3s}(ζ) \ F) + ∫_{B_{3s}(ζ)} |p_{T_x M} − p_T|²)`.
The nearest point `y` of `spt V` has `|y − ζ| = 2s`, so `μ_V(B_s(ζ)) = 0`; monotonicity at `ζ`
between `s` and `3s` and the lower density bound on `B_s(y) ⊆ B_{3s}(ζ)` give
`s^{n+2} ≤ C ∫_{B_{3s}(ζ)} |p_{T_x M}^⊥(x − ζ)|²`, and `p_{T_x M}^⊥ = (I − p_T) + (p_T − p_{T_x M})`
with the cone condition on `F` and the upper density bound on `B_{5s}(y)` absorb the rest. -/
theorem lip_approx_hole_estimate : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ ε δ₀ C₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ 0 < C₀ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → V.AllardHypotheses H p δ ρ → ∀ (T : Submodule ℝ (Amb n ℓ)) (F : Set (Amb n ℓ)), IsClosed F → (∀ x ∈ F, ∀ z ∈ F, ‖(x - z) - T.starProjection (x - z)‖ ≤ ε * ‖x - z‖) → ∀ ζ ∈ F, ‖ζ‖ ≤ 17 * (δ * ρ) / 32 → 0 < infDist ζ V.support → infDist ζ V.support ≤ δ * ρ / 16 → ENNReal.ofReal ((infDist ζ V.support / 2) ^ n) ≤ ENNReal.ofReal C₀ * (V.weight (closedBall ζ (3 * (infDist ζ V.support / 2)) \ F) + ENNReal.ofReal (∫ x in closedBall ζ (3 * (infDist ζ V.support / 2)), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) := by
  have lip_approx_hole_support_gap : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ρ : ℝ) (ζ : Amb n ℓ), closedBall (0 : Amb n ℓ) ρ ⊆ U → 0 < infDist ζ V.support → ‖ζ‖ + infDist ζ V.support < ρ → (∃ y ∈ V.support, ‖y - ζ‖ = infDist ζ V.support) ∧ V.weight (ball ζ (infDist ζ V.support)) = 0 := by
    intro n ℓ U V ρ ζ hρU hd hζd
    set d := infDist ζ V.support with hd_def
    set S := V.weight.support with hS_def
    have hsupp : V.support = U ∩ S := rfl
    -- membership in `V.support` for points of `S` close to `ζ`
    have hmem : ∀ z ∈ S, ‖z - ζ‖ < ρ - ‖ζ‖ → z ∈ V.support := by
      intro z hz hzd
      refine ⟨hρU ?_, hz⟩
      rw [mem_closedBall, dist_zero_right]
      have : ‖z‖ ≤ ‖ζ‖ + ‖z - ζ‖ := by
        have := norm_add_le ζ (z - ζ)
        simpa using this
      linarith
    have hne : V.support.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      rw [hd_def, h, infDist_empty] at hd
      exact lt_irrefl _ hd
    have hSne : S.Nonempty := hne.mono inter_subset_right
    have hle : infDist ζ S ≤ d := infDist_le_infDist_of_subset inter_subset_right hne
    obtain ⟨y, hyS, hy⟩ := (Measure.isClosed_support (μ := V.weight)).exists_infDist_eq_dist hSne ζ
    have hyd : ‖y - ζ‖ ≤ d := by
      rw [← dist_eq_norm, dist_comm, ← hy]; exact hle
    have hyV : y ∈ V.support := hmem y hyS (by linarith)
    have hdy : d ≤ ‖y - ζ‖ := by
      rw [← dist_eq_norm, dist_comm]; exact infDist_le_dist_of_mem hyV
    refine ⟨⟨y, hyV, le_antisymm hyd hdy⟩, ?_⟩
    have hball : ball ζ d ⊆ Sᶜ := by
      intro z hz hzS
      rw [mem_ball, dist_eq_norm] at hz
      have hzV : z ∈ V.support := hmem z hzS (by linarith)
      have : d ≤ dist ζ z := infDist_le_dist_of_mem hzV
      rw [dist_comm, dist_eq_norm] at this
      linarith
    exact measure_mono_null hball Measure.measure_compl_support
  have lip_approx_hole_norm_apply_sq_le_hsNormSq : ∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k) (v : Rn m), ‖A v‖ ^ 2 ≤ hsNormSq A * ‖v‖ ^ 2 := by
    intro m k A v
    set b := EuclideanSpace.basisFun (Fin m) ℝ
    have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
    have hAv : A v = ∑ i, b.repr v i • A (EuclideanSpace.single i 1) := by
      conv_lhs => rw [hv]
      simp [b, map_sum, map_smul]
    have h1 : ‖A v‖ ≤ ∑ i, |b.repr v i| * ‖A (EuclideanSpace.single i 1)‖ := by
      rw [hAv]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i, |b.repr v i| * ‖A (EuclideanSpace.single i 1)‖) ^ 2 ≤
        (∑ i, |b.repr v i| ^ 2) * ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ i, |b.repr v i| ^ 2 = ‖v‖ ^ 2 := by
      have := b.repr.norm_map v
      rw [← this, EuclideanSpace.norm_sq_eq]
      simp [sq_abs]
    have h0 : 0 ≤ ‖A v‖ := norm_nonneg _
    calc ‖A v‖ ^ 2 ≤ (∑ i, |b.repr v i| * ‖A (EuclideanSpace.single i 1)‖) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ ≤ (∑ i, |b.repr v i| ^ 2) * ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 := h2
      _ = hsNormSq A * ‖v‖ ^ 2 := by rw [h3, hsNormSq]; ring
  have lip_approx_hole_normal_part_bound : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (P : Amb n ℓ → Amb n ℓ →L[ℝ] Amb n ℓ) (T : Submodule ℝ (Amb n ℓ)) (F : Set (Amb n ℓ)) (ε r : ℝ) (ζ : Amb n ℓ), AEStronglyMeasurable P μ → MeasurableSet F → (∀ x ∈ F, ∀ z ∈ F, ‖(x - z) - T.starProjection (x - z)‖ ≤ ε * ‖x - z‖) → ζ ∈ F → μ (closedBall ζ r) < ⊤ → IntegrableOn (fun x => hsNormSq (P x - T.starProjection)) (closedBall ζ r) μ → IntegrableOn (fun x => ‖(x - ζ) - P x (x - ζ)‖ ^ 2) (closedBall ζ r) μ ∧ ∫ x in closedBall ζ r, ‖(x - ζ) - P x (x - ζ)‖ ^ 2 ∂μ ≤ 2 * r ^ 2 * (ε ^ 2 * μ.real (closedBall ζ r) + μ.real (closedBall ζ r \ F) + ∫ x in closedBall ζ r, hsNormSq (P x - T.starProjection) ∂μ) := by
    intro n ℓ μ P T F ε r ζ hP hF hcone hζ hfin hτ
    have hB : MeasurableSet (closedBall ζ r) := measurableSet_closedBall
    -- `v - p_T v` is the orthogonal projection onto `Tᗮ`, so it has norm `≤ ‖v‖`.
    have hQ : ∀ v : Amb n ℓ, ‖v - T.starProjection v‖ ≤ ‖v‖ := by
      intro v
      have h := Submodule.norm_sq_eq_add_norm_sq_starProjection v T
      have e2 : Tᗮ.starProjection v = v - T.starProjection v := by
        rw [Submodule.starProjection_orthogonal']; simp
      rw [e2] at h
      have h4 : ‖v - T.starProjection v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        have := sq_nonneg ‖T.starProjection v‖
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h4
    have hτnn : ∀ x, 0 ≤ hsNormSq (P x - T.starProjection) :=
      fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    -- Pointwise: `|p_x^⊥ v|² ≤ 2|Q v|² + 2 |p_x - p_T|²_HS |v|²`.
    have hpt : ∀ x, ‖(x - ζ) - P x (x - ζ)‖ ^ 2 ≤
        2 * ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 +
          2 * (hsNormSq (P x - T.starProjection) * ‖x - ζ‖ ^ 2) := by
      intro x
      have hdecomp : (x - ζ) - P x (x - ζ) =
          ((x - ζ) - T.starProjection (x - ζ)) - (P x - T.starProjection) (x - ζ) := by
        rw [sub_apply]; abel
      rw [hdecomp]
      have hHS := lip_approx_hole_norm_apply_sq_le_hsNormSq _ _ (P x - T.starProjection) (x - ζ)
      have hn := norm_sub_le ((x - ζ) - T.starProjection (x - ζ)) ((P x - T.starProjection) (x - ζ))
      nlinarith [norm_nonneg ((x - ζ) - T.starProjection (x - ζ)),
        norm_nonneg ((P x - T.starProjection) (x - ζ)),
        norm_nonneg (((x - ζ) - T.starProjection (x - ζ)) - (P x - T.starProjection) (x - ζ)),
        sq_nonneg (‖(x - ζ) - T.starProjection (x - ζ)‖ - ‖(P x - T.starProjection) (x - ζ)‖)]
    -- The dominating function `g`.
    set g : Amb n ℓ → ℝ := fun x => 2 * (ε ^ 2 * r ^ 2) + 2 * r ^ 2 * Fᶜ.indicator 1 x +
      2 * r ^ 2 * hsNormSq (P x - T.starProjection) with hg_def
    have hfg : ∀ x ∈ closedBall ζ r, ‖(x - ζ) - P x (x - ζ)‖ ^ 2 ≤ g x := by
      intro x hx
      have hxr : ‖x - ζ‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hx; exact hx
      have hsq : ‖x - ζ‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
      have hτb : hsNormSq (P x - T.starProjection) * ‖x - ζ‖ ^ 2 ≤
          hsNormSq (P x - T.starProjection) * r ^ 2 := mul_le_mul_of_nonneg_left hsq (hτnn x)
      by_cases hxF : x ∈ F
      · have hc := hcone x hxF ζ hζ
        have h1 : ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ (ε * ‖x - ζ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hc 2
        have h3 : ε ^ 2 * ‖x - ζ‖ ^ 2 ≤ ε ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
        have hind : Fᶜ.indicator (1 : Amb n ℓ → ℝ) x = 0 :=
          indicator_of_notMem (by simpa using hxF) _
        simp only [hg_def, hind]
        nlinarith [hpt x]
      · have h1 : ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ ‖x - ζ‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hQ (x - ζ)) 2
        have hind : Fᶜ.indicator (1 : Amb n ℓ → ℝ) x = 1 :=
          indicator_of_mem (by simpa using hxF) _
        simp only [hg_def, hind]
        nlinarith [hpt x, sq_nonneg ε, sq_nonneg r, mul_nonneg (sq_nonneg ε) (sq_nonneg r)]
    -- Measurability of the integrand.
    have hPv : AEStronglyMeasurable (fun x => P x (x - ζ)) μ :=
      (ContinuousLinearMap.id ℝ (Amb n ℓ →L[ℝ] Amb n ℓ)).aestronglyMeasurable_comp₂ hP
        (continuous_id.sub continuous_const).aestronglyMeasurable
    have hfm : AEStronglyMeasurable (fun x => ‖(x - ζ) - P x (x - ζ)‖ ^ 2) μ :=
      (((continuous_id.sub continuous_const).aestronglyMeasurable.sub hPv).norm).pow 2
    -- Integrability of `g` on the ball.
    have hfin' : μ (closedBall ζ r) ≠ ⊤ := hfin.ne
    have hc1 : IntegrableOn (fun _ : Amb n ℓ => 2 * (ε ^ 2 * r ^ 2)) (closedBall ζ r) μ :=
      integrableOn_const hfin'
    have hc2 : IntegrableOn (fun x => 2 * r ^ 2 * Fᶜ.indicator (1 : Amb n ℓ → ℝ) x) (closedBall ζ r) μ := by
      have : IntegrableOn (Fᶜ.indicator (fun _ : Amb n ℓ => (1 : ℝ))) (closedBall ζ r) μ :=
        (integrableOn_const hfin').indicator hF.compl
      exact this.const_mul _
    have hc3 : IntegrableOn (fun x => 2 * r ^ 2 * hsNormSq (P x - T.starProjection)) (closedBall ζ r) μ :=
      hτ.const_mul _
    have hgi : IntegrableOn g (closedBall ζ r) μ := (hc1.add hc2).add hc3
    have hfi : IntegrableOn (fun x => ‖(x - ζ) - P x (x - ζ)‖ ^ 2) (closedBall ζ r) μ := by
      refine Integrable.mono' hgi hfm.restrict ?_
      rw [ae_restrict_iff' hB]
      refine Eventually.of_forall fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hfg x hx
    refine ⟨hfi, ?_⟩
    have hind : ∫ x in closedBall ζ r, Fᶜ.indicator (1 : Amb n ℓ → ℝ) x ∂μ =
        μ.real (closedBall ζ r \ F) := by
      rw [integral_indicator_one hF.compl, Measure.real, Measure.restrict_apply hF.compl,
        Measure.real]
      congr 1
      rw [inter_comm, sdiff_eq]
    have hint_g : ∫ x in closedBall ζ r, g x ∂μ = 2 * (ε ^ 2 * r ^ 2) * μ.real (closedBall ζ r) +
        2 * r ^ 2 * μ.real (closedBall ζ r \ F) +
        2 * r ^ 2 * ∫ x in closedBall ζ r, hsNormSq (P x - T.starProjection) ∂μ := by
      have e1 : ∫ x in closedBall ζ r, g x ∂μ =
          ∫ x in closedBall ζ r, (2 * (ε ^ 2 * r ^ 2) + 2 * r ^ 2 * Fᶜ.indicator (1 : Amb n ℓ → ℝ) x) ∂μ +
          ∫ x in closedBall ζ r, 2 * r ^ 2 * hsNormSq (P x - T.starProjection) ∂μ :=
        integral_add (hc1.add hc2) hc3
      have e2 : ∫ x in closedBall ζ r, (2 * (ε ^ 2 * r ^ 2) + 2 * r ^ 2 * Fᶜ.indicator (1 : Amb n ℓ → ℝ) x) ∂μ =
          ∫ _ in closedBall ζ r, 2 * (ε ^ 2 * r ^ 2) ∂μ +
          ∫ x in closedBall ζ r, 2 * r ^ 2 * Fᶜ.indicator (1 : Amb n ℓ → ℝ) x ∂μ :=
        integral_add hc1 hc2
      rw [e1, e2, setIntegral_const (2 * (ε ^ 2 * r ^ 2)),
        integral_const_mul (2 * r ^ 2) (fun x => Fᶜ.indicator (1 : Amb n ℓ → ℝ) x),
        integral_const_mul (2 * r ^ 2) (fun x => hsNormSq (P x - T.starProjection)), hind, smul_eq_mul]
      ring
    calc ∫ x in closedBall ζ r, ‖(x - ζ) - P x (x - ζ)‖ ^ 2 ∂μ
        ≤ ∫ x in closedBall ζ r, g x ∂μ := setIntegral_mono_on hfi hgi hB hfg
      _ = _ := hint_g
      _ = 2 * r ^ 2 * (ε ^ 2 * μ.real (closedBall ζ r) + μ.real (closedBall ζ r \ F) +
            ∫ x in closedBall ζ r, hsNormSq (P x - T.starProjection) ∂μ) := by ring
  have lip_approx_hole_annulus_integral_le : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (ζ : Amb n ℓ) (k : ℕ) (s r : ℝ), 0 < s → (∀ x, 0 ≤ f x) → IntegrableOn f (closedBall ζ r) μ → ∫ x in closedBall ζ r \ closedBall ζ s, f x / ‖x - ζ‖ ^ k ∂μ ≤ (s ^ k)⁻¹ * ∫ x in closedBall ζ r, f x ∂μ := by
    intro n ℓ μ f ζ k s r hs hf hfi
    have hA : MeasurableSet (closedBall ζ r \ closedBall ζ s) :=
      measurableSet_closedBall.diff measurableSet_closedBall
    have hsk : 0 < s ^ k := pow_pos hs k
    have hsub : closedBall ζ r \ closedBall ζ s ⊆ closedBall ζ r := sdiff_subset
    have h1 : ∫ x in closedBall ζ r \ closedBall ζ s, f x / ‖x - ζ‖ ^ k ∂μ ≤
        ∫ x in closedBall ζ r \ closedBall ζ s, (s ^ k)⁻¹ * f x ∂μ := by
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · exact Eventually.of_forall fun x => div_nonneg (hf x) (pow_nonneg (norm_nonneg _) _)
      · exact ((hfi.mono_set hsub).const_mul _)
      · rw [EventuallyLE, ae_restrict_iff' hA]
        refine Eventually.of_forall fun x hx => ?_
        have hx' : s < ‖x - ζ‖ := by
          have := hx.2
          rw [mem_closedBall, dist_eq_norm, not_le] at this
          exact this
        have hpow : s ^ k ≤ ‖x - ζ‖ ^ k := pow_le_pow_left₀ hs.le hx'.le k
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hsk hpow) (hf x)
    have h2 : ∫ x in closedBall ζ r \ closedBall ζ s, f x ∂μ ≤ ∫ x in closedBall ζ r, f x ∂μ :=
      setIntegral_mono_set hfi (Eventually.of_forall fun x => hf x) (Eventually.of_forall hsub)
    calc ∫ x in closedBall ζ r \ closedBall ζ s, f x / ‖x - ζ‖ ^ k ∂μ
        ≤ ∫ x in closedBall ζ r \ closedBall ζ s, (s ^ k)⁻¹ * f x ∂μ := h1
      _ = (s ^ k)⁻¹ * ∫ x in closedBall ζ r \ closedBall ζ s, f x ∂μ := integral_const_mul _ _
      _ ≤ (s ^ k)⁻¹ * ∫ x in closedBall ζ r, f x ∂μ :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hsk.le)
  intro n ℓ hn p hp
  obtain ⟨δP, hδP0, hδP8, hpin⟩ := Submission.lip_approx_pinched_density n ℓ hn p hp
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpn : 0 < p - n := by linarith
  have hp0 : 0 < p := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h3n : (0 : ℝ) < 3 ^ n := by positivity
  have h5n : (0 : ℝ) < 5 ^ n := by positivity
  obtain ⟨A8, hA8def⟩ : ∃ A8 : ℝ, A8 = 72 * 3 ^ n * Real.exp 1 ^ 2 / unitBallVolume n := ⟨_, rfl⟩
  have hA8 : 0 < A8 := by rw [hA8def]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.sqrt (1 / (4 * A8 * unitBallVolume n * 5 ^ n)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact Real.sqrt_pos.mpr (by positivity)
  have hε2 : ε ^ 2 = 1 / (4 * A8 * unitBallVolume n * 5 ^ n) := by
    rw [hεdef]; exact Real.sq_sqrt (by positivity)
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (p - n) / (4 * p) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨δ₃, hδ₃_def⟩ : ∃ δ₃ : ℝ,
      δ₃ = unitBallVolume n * (p - n) / (3 ^ n * 32 * Real.exp 1 * p) := ⟨_, rfl⟩
  have hδ₃ : 0 < δ₃ := by rw [hδ₃_def]; positivity
  refine ⟨ε, min δP (min κ δ₃), 2 * A8, hε, lt_min hδP0 (lt_min hκ hδ₃), by positivity, ?_⟩
  intro U hU V H δ ρ hδ hδ0 hA T F hFc hcone ζ hζF hζn hd hdle
  have hδP : δ ≤ δP := le_trans hδ0 (min_le_left _ _)
  have hδκ : δ ≤ κ := le_trans hδ0 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ3 : δ ≤ δ₃ := le_trans hδ0 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ8 : δ ≤ 1 / 8 := le_trans hδP hδP8
  have hρ : 0 < ρ := hA.1
  have hρU : closedBall (0 : Amb n ℓ) ρ ⊆ U := hA.2.2.2.2.1
  set d := infDist ζ V.support with hd_def
  set s := d / 2 with hs_def
  have hs : 0 < s := by positivity
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hd2 : d = 2 * s := by rw [hs_def]; ring
  have hδρ8 : δ * ρ ≤ ρ / 8 := by
    have := mul_le_mul_of_nonneg_right hδ8 hρ.le
    linarith
  -- norm triangle helper
  have tri : ∀ a b : Amb n ℓ, ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
    intro a b
    have := norm_add_le b (a - b)
    simpa using this
  -- Step 1: nearest support point
  have hζd : ‖ζ‖ + d < ρ := by linarith
  obtain ⟨⟨y, hyV, hyζ⟩, hnull⟩ := lip_approx_hole_support_gap n ℓ U V ρ ζ hρU hd hζd
  have hBs0 : V.weight (closedBall ζ s) = 0 :=
    measure_mono_null (closedBall_subset_ball (by rw [hs_def]; linarith)) hnull
  have hyn : ‖y‖ ≤ 3 * (δ * ρ) := by
    have := tri y ζ
    linarith
  have hBy_sub : closedBall y s ⊆ closedBall ζ (3 * s) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have := norm_sub_le_norm_sub_add_norm_sub x y ζ
    linarith
  have hBζ_sub : closedBall ζ (3 * s) ⊆ closedBall y (5 * s) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have := norm_sub_le_norm_sub_add_norm_sub x ζ y
    have h' : ‖ζ - y‖ = ‖y - ζ‖ := norm_sub_rev ζ y
    linarith
  -- pinched density at `y`
  have hs_le : s ≤ ρ / 2 := by linarith
  have h5s_le : 5 * s ≤ ρ / 2 := by linarith
  have hlow := (hpin U hU V H δ ρ hδ hδP hA y hyn s hs hs_le).2 hyV
  have hup := (hpin U hU V H δ ρ hδ hδP hA y hyn (5 * s) (by positivity) h5s_le).1
  have hfin5 : V.weight (closedBall y (5 * s)) < ⊤ := lt_of_le_of_lt hup ENNReal.ofReal_lt_top
  have hfin3 : V.weight (closedBall ζ (3 * s)) < ⊤ := lt_of_le_of_lt (measure_mono hBζ_sub) hfin5
  -- Step 2: monotonicity at `ζ`
  obtain ⟨Λ, hΛ_def⟩ : ∃ Λ : ℝ, Λ = 4 * p * δ / (p - n) := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ_def]; positivity
  have hΛ1 : Λ ≤ 1 := by
    rw [hΛ_def, div_le_one hpn]
    have h1 : δ ≤ (p - n) / (4 * p) := hκdef ▸ hδκ
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = (1 - 3 * δ) * ρ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hR_def]; exact mul_pos (by linarith) hρ
  have hRsub : closedBall ζ R ⊆ closedBall 0 ρ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    have := tri x ζ
    have hRe : R = ρ - 3 * (δ * ρ) := by rw [hR_def]; ring
    rw [hRe] at hx
    linarith
  have h3sR : 3 * s < R := by
    have hRe : R = ρ - 3 * (δ * ρ) := by rw [hR_def]; ring
    rw [hRe]; linarith
  have hmono := (Submission.lip_approx_monotonicity n ℓ hn p hp U hU V H δ ρ Λ hδ hA (le_of_eq hΛ_def.symm)
    hΛ1 ζ R hR hRsub s (3 * s) hs (by linarith) h3sR).2.1
  -- tangent structure
  obtain ⟨hmeas, hint, -⟩ := Submission.lip_approx_tangent_structure n ℓ hn U hU V
  have hB3sub : closedBall ζ (3 * s) ⊆ U := by
    intro x hx
    apply hρU
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    have := tri x ζ
    linarith
  have hτ := hint T (closedBall ζ (3 * s)) (isCompact_closedBall _ _) hB3sub
  -- children C and D
  obtain ⟨hIi, hIb⟩ := lip_approx_hole_normal_part_bound n ℓ V.weight V.tangentProj T F ε (3 * s) ζ
    hmeas hFc.measurableSet hcone hζF hfin3 hτ
  have hJ := lip_approx_hole_annulus_integral_le n ℓ V.weight
    (fun x => ‖(x - ζ) - V.tangentProj x (x - ζ)‖ ^ 2) ζ (n + 2) s (3 * s) hs
    (fun x => sq_nonneg _) hIi
  beta_reduce at hJ
  set I := ∫ x in closedBall ζ (3 * s), ‖(x - ζ) - V.tangentProj x (x - ζ)‖ ^ 2 ∂V.weight with hI_def
  set J := ∫ x in closedBall ζ (3 * s) \ closedBall ζ s,
    ‖(x - ζ) - V.tangentProj x (x - ζ)‖ ^ 2 / ‖x - ζ‖ ^ (n + 2) ∂V.weight with hJ_def
  set m3 := V.weight.real (closedBall ζ (3 * s)) with hm3_def
  set M := V.weight.real (closedBall ζ (3 * s) \ F) with hM_def
  set t := ∫ x in closedBall ζ (3 * s), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight
    with ht_def
  clear_value I J m3 M t
  have hBs0' : V.weight.real (closedBall ζ s) = 0 := by simp [Measure.real, hBs0]
  have f1 : m3 / (3 * s) ^ n ≤ 2 * Real.exp Λ * Λ + Real.exp (2 * Λ) * J := by
    have h := hmono
    rw [hBs0', zero_div, mul_zero, zero_add] at h
    exact h
  have f3 : unitBallVolume n * s ^ n / 2 ≤ m3 := by
    have h1 : ENNReal.ofReal (unitBallVolume n * s ^ n / 2) ≤ V.weight (closedBall ζ (3 * s)) :=
      le_trans hlow (measure_mono hBy_sub)
    rw [hm3_def, Measure.real]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin3.ne).mp h1
  have f4 : m3 ≤ 2 * unitBallVolume n * (5 * s) ^ n := by
    have h1 : V.weight (closedBall ζ (3 * s)) ≤ ENNReal.ofReal (2 * unitBallVolume n * (5 * s) ^ n) :=
      le_trans (measure_mono hBζ_sub) hup
    rw [hm3_def, Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1
  have hI0 : 0 ≤ I := by rw [hI_def]; exact integral_nonneg fun x => sq_nonneg _
  have hM0 : 0 ≤ M := by rw [hM_def]; exact ENNReal.toReal_nonneg
  have ht0 : 0 ≤ t := by
    rw [ht_def]; exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have f6 : 2 * Real.exp 1 * Λ ≤ unitBallVolume n / (4 * 3 ^ n) := by
    have h1 : δ * (3 ^ n * 32 * Real.exp 1 * p) ≤ unitBallVolume n * (p - n) := by
      have h2 := hδ3
      rw [hδ₃_def, le_div_iff₀ (by positivity)] at h2
      exact h2
    rw [hΛ_def, le_div_iff₀ (by positivity)]
    have h3 : 2 * Real.exp 1 * (4 * p * δ / (p - n)) * (4 * 3 ^ n) =
        δ * (3 ^ n * 32 * Real.exp 1 * p) / (p - n) := by
      field_simp
      ring
    rw [h3, div_le_iff₀ hpn]
    linarith
  have hexpΛ : Real.exp Λ ≤ Real.exp 1 := Real.exp_le_exp.mpr hΛ1
  have hexp2Λ : Real.exp (2 * Λ) ≤ Real.exp 1 ^ 2 := by
    rw [two_mul, Real.exp_add, sq]
    exact mul_le_mul hexpΛ hexpΛ (Real.exp_pos _).le he.le
  have h3s : (3 * s) ^ n = 3 ^ n * s ^ n := mul_pow 3 s n
  have h5s : (5 * s) ^ n = 5 ^ n * s ^ n := mul_pow 5 s n
  have hsn2 : s ^ (n + 2) = s ^ n * s ^ 2 := pow_add s n 2
  have hX : 0 < s ^ n := pow_pos hs n
  -- Step 3: lower bound
  have g1 : m3 / (3 * s) ^ n ≤ 2 * Real.exp 1 * Λ + Real.exp 1 ^ 2 * ((s ^ (n + 2))⁻¹ * I) := by
    have hJ0 : 0 ≤ (s ^ (n + 2))⁻¹ * I := mul_nonneg (inv_nonneg.mpr (by positivity)) hI0
    have k1 : 2 * Real.exp Λ * Λ ≤ 2 * Real.exp 1 * Λ :=
      mul_le_mul_of_nonneg_right (by linarith) hΛ0
    have k2 : Real.exp (2 * Λ) * J ≤ Real.exp (2 * Λ) * ((s ^ (n + 2))⁻¹ * I) :=
      mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le
    have k3 : Real.exp (2 * Λ) * ((s ^ (n + 2))⁻¹ * I) ≤ Real.exp 1 ^ 2 * ((s ^ (n + 2))⁻¹ * I) :=
      mul_le_mul_of_nonneg_right hexp2Λ hJ0
    linarith
  have g2 : unitBallVolume n / (2 * 3 ^ n) ≤ m3 / (3 * s) ^ n := by
    rw [h3s, div_le_div_iff₀ (by positivity) (by positivity)]
    have k := mul_le_mul_of_nonneg_left f3 h3n.le
    have k' : 3 ^ n * (unitBallVolume n * s ^ n / 2) * 2 = unitBallVolume n * (3 ^ n * s ^ n) := by ring
    linarith [k, k']
  have g3 : unitBallVolume n * s ^ (n + 2) ≤ 4 * 3 ^ n * Real.exp 1 ^ 2 * I := by
    have k1 : unitBallVolume n / (4 * 3 ^ n) ≤ Real.exp 1 ^ 2 * ((s ^ (n + 2))⁻¹ * I) := by
      have : unitBallVolume n / (2 * 3 ^ n) =
          unitBallVolume n / (4 * 3 ^ n) + unitBallVolume n / (4 * 3 ^ n) := by
        field_simp
        ring
      linarith
    have hpos : 0 < s ^ (n + 2) := by positivity
    rw [div_le_iff₀ (by positivity)] at k1
    have k2 : Real.exp 1 ^ 2 * ((s ^ (n + 2))⁻¹ * I) * (4 * 3 ^ n) =
        4 * 3 ^ n * Real.exp 1 ^ 2 * I / s ^ (n + 2) := by
      field_simp
    rw [k2, le_div_iff₀ hpos] at k1
    linarith
  -- Step 4: upper bound for `I`
  have g4 : I ≤ 18 * s ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) := by
    have k : ε ^ 2 * m3 ≤ ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ε)
      have := f4
      rw [h5s] at this
      linarith
    calc I ≤ 2 * (3 * s) ^ 2 * (ε ^ 2 * m3 + M + t) := hIb
      _ ≤ 2 * (3 * s) ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) := by
        gcongr
      _ = 18 * s ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) := by ring
  -- Step 5: absorption
  have g5 : s ^ n ≤ 2 * A8 * (M + t) := by
    have hs2 : 0 < s ^ 2 := by positivity
    have k : unitBallVolume n * s ^ n * s ^ 2 ≤
        72 * 3 ^ n * Real.exp 1 ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) * s ^ 2 := by
      have h1 := g3
      rw [hsn2] at h1
      have h2 : 4 * 3 ^ n * Real.exp 1 ^ 2 * I ≤
          4 * 3 ^ n * Real.exp 1 ^ 2 * (18 * s ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t)) :=
        mul_le_mul_of_nonneg_left g4 (by positivity)
      have h3 : unitBallVolume n * (s ^ n * s ^ 2) = unitBallVolume n * s ^ n * s ^ 2 := by ring
      have h4 : 4 * 3 ^ n * Real.exp 1 ^ 2 *
          (18 * s ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t)) =
          72 * 3 ^ n * Real.exp 1 ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) * s ^ 2 := by
        ring
      linarith
    have k2 : unitBallVolume n * s ^ n ≤
        72 * 3 ^ n * Real.exp 1 ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) :=
      le_of_mul_le_mul_right k hs2
    have hA8ω : A8 * unitBallVolume n = 72 * 3 ^ n * Real.exp 1 ^ 2 := by
      rw [hA8def]; field_simp
    have hhalf : A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n)) = 1 / 2 := by
      rw [hε2]; field_simp; ring
    have k3 : s ^ n ≤ A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) := by
      have k4 : unitBallVolume n * s ^ n ≤
          unitBallVolume n * (A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t)) := by
        calc unitBallVolume n * s ^ n
            ≤ 72 * 3 ^ n * Real.exp 1 ^ 2 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) := k2
          _ = unitBallVolume n * (A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t)) := by
            rw [← hA8ω]; ring
      exact le_of_mul_le_mul_left k4 hω
    have k5 : A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n) + M + t) =
        s ^ n / 2 + A8 * (M + t) := by
      have : A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n)) = s ^ n / 2 := by
        calc A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n * s ^ n))
            = A8 * (ε ^ 2 * (2 * unitBallVolume n * 5 ^ n)) * s ^ n := by ring
          _ = s ^ n / 2 := by rw [hhalf]; ring
      linear_combination this
    linarith
  -- conversion to `[0, ∞]`
  have hMfin : V.weight (closedBall ζ (3 * s) \ F) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono sdiff_subset) hfin3).ne
  have hMeq : V.weight (closedBall ζ (3 * s) \ F) = ENNReal.ofReal M := by
    rw [hM_def, Measure.real, ENNReal.ofReal_toReal hMfin]
  rw [hMeq, ← ENNReal.ofReal_add hM0 ht0, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal g5

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

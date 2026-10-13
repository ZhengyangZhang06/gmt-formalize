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

/-- Shifted integration by parts (difference-quotient step of the `C^{1,α} ⇒ C^{2,α}` regularity for
Euler–Lagrange systems in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1): if `g` is continuous on
the open set `U`, `ζ ∈ C¹_c(ℝⁿ; ℝ^ℓ)` and `x + t d e ∈ U` for `x ∈ spt ζ`, `t ∈ [0, 1]`, then
`∫ ⟨ζ(x) − ζ(x − de), g(x)⟩ dx = d ∫ ⟨∫₀¹ g(x + tde) dt, Dζ(x) e⟩ dx`.  Write
`ζ(x) − ζ(x − de) = d ∫₀¹ Dζ(x − sde) e ds`, exchange the integrals (Fubini), translate
`x = y + sde` for each `s`, and exchange back; `s` is clamped to `[0, 1]` so that both integrands are
continuous on `ℝ × ℝⁿ` and vanish off a compact set. -/
theorem dohr_eb_elc2_shift_ibp : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (g ζ : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), IsOpen U → ContinuousOn g U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ x ∈ tsupport ζ, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = d * ∫ x, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e) := by
  intro n ℓ U g ζ e d hU hg hζ hζc hseg
  set K := tsupport ζ with hK_def
  have hKc : IsCompact K := hζc
  have hKcl : IsClosed K := isClosed_tsupport ζ
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ y ∉ K, fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hζdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- clamp
  set c : ℝ → ℝ := fun s => max 0 (min s 1) with hc_def
  have hc_cont : Continuous c := by simp only [hc_def]; fun_prop
  have hc_mem : ∀ s, c s ∈ Icc (0:ℝ) 1 := fun s =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hc_eq : ∀ s ∈ Icc (0:ℝ) 1, c s = s := fun s hs => by
    simp only [hc_def, min_eq_left hs.2, max_eq_right hs.1]
  have hc_eq' : ∀ s ∈ uIcc (0:ℝ) 1, c s = s := fun s hs => hc_eq s (by rwa [uIcc_of_le zero_le_one] at hs)
  -- the compact set K'
  set K' : Set (Rn n) := (fun p : ℝ × Rn n => p.2 + (p.1 * d) • e) '' (Icc (0:ℝ) 1 ×ˢ K) with hK'_def
  have hK'c : IsCompact K' := (isCompact_Icc.prod hKc).image (by fun_prop)
  have hK'U : K' ⊆ U := by
    rintro _ ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    exact hseg y hy t ht
  -- F and Ft
  set F : ℝ → Rn n → ℝ := fun s x => inner ℝ (fderiv ℝ ζ (x - (c s * d) • e) e) (g x) with hF_def
  set Ft : ℝ → Rn n → ℝ := fun s y => inner ℝ (fderiv ℝ ζ y e) (g (y + (c s * d) • e)) with hFt_def
  have hFcont : Continuous (Function.uncurry F) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨s, x⟩
    by_cases hx : x - (c s * d) • e ∈ K
    · have hxU : x ∈ U := by
        have := hseg _ hx (c s) (hc_mem s)
        simpa using this
      have hgx : ContinuousAt g x := hg.continuousAt (hU.mem_nhds hxU)
      have h1 : Continuous (fun p : ℝ × Rn n => fderiv ℝ ζ (p.2 - (c p.1 * d) • e) e) := by
        have hm : Continuous (fun p : ℝ × Rn n => p.2 - (c p.1 * d) • e) := by fun_prop
        exact (hDζ.comp hm).clm_apply continuous_const
      have h2 : ContinuousAt (fun p : ℝ × Rn n => g p.2) (s, x) := hgx.comp continuousAt_snd
      exact h1.continuousAt.inner h2
    · have hopen : IsOpen {p : ℝ × Rn n | p.2 - (c p.1 * d) • e ∉ K} :=
        hKcl.isOpen_compl.preimage (by fun_prop)
      have hev : Function.uncurry F =ᶠ[𝓝 (s, x)] fun _ => (0:ℝ) := by
        filter_upwards [hopen.mem_nhds hx] with p hp
        simp [hF_def, Function.uncurry, hDζ0 _ hp]
      exact continuousAt_const.congr hev.symm
  have hFtcont : Continuous (Function.uncurry Ft) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨s, y⟩
    by_cases hy : y ∈ K
    · have hyU : y + (c s * d) • e ∈ U := hseg y hy (c s) (hc_mem s)
      have hgy : ContinuousAt g (y + (c s * d) • e) := hg.continuousAt (hU.mem_nhds hyU)
      have h1 : Continuous (fun p : ℝ × Rn n => fderiv ℝ ζ p.2 e) :=
        (hDζ.comp continuous_snd).clm_apply continuous_const
      have hm : Continuous (fun p : ℝ × Rn n => p.2 + (c p.1 * d) • e) := by fun_prop
      have h2 : ContinuousAt (fun p : ℝ × Rn n => g (p.2 + (c p.1 * d) • e)) (s, y) :=
        hgy.comp_of_eq hm.continuousAt rfl
      exact h1.continuousAt.inner h2
    · have hopen : IsOpen {p : ℝ × Rn n | p.2 ∉ K} := hKcl.isOpen_compl.preimage continuous_snd
      have hev : Function.uncurry Ft =ᶠ[𝓝 (s, y)] fun _ => (0:ℝ) := by
        filter_upwards [hopen.mem_nhds hy] with p hp
        simp [hFt_def, Function.uncurry, hDζ0 _ hp]
      exact continuousAt_const.congr hev.symm
  -- integrability on the product
  have hprod : (volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Rn n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Rn n))).restrict (uIoc (0:ℝ) 1 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hsub : uIoc (0:ℝ) 1 ×ˢ (univ : Set (Rn n)) ⊆ Icc (0:ℝ) 1 ×ˢ univ := by
    rw [uIoc_of_le zero_le_one]
    exact prod_mono Ioc_subset_Icc_self le_rfl
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Rn n))) := by
    rw [hprod]
    have h1 : IntegrableOn (Function.uncurry F) (Icc (0:ℝ) 1 ×ˢ K')
        ((volume : Measure ℝ).prod (volume : Measure (Rn n))) :=
      hFcont.continuousOn.integrableOn_compact (isCompact_Icc.prod hK'c)
    have h2 : IntegrableOn (Function.uncurry F) (Icc (0:ℝ) 1 ×ˢ univ)
        ((volume : Measure ℝ).prod (volume : Measure (Rn n))) := by
      refine h1.of_forall_sdiff_eq_zero (measurableSet_Icc.prod MeasurableSet.univ) ?_
      rintro ⟨s, x⟩ ⟨⟨hs, -⟩, hnot⟩
      have hx : x ∉ K' := fun hx => hnot ⟨hs, hx⟩
      have hnk : x - (c s * d) • e ∉ K := by
        intro hk
        apply hx
        refine ⟨(c s, x - (c s * d) • e), ⟨hc_mem s, hk⟩, ?_⟩
        simp
      simp [hF_def, Function.uncurry, hDζ0 _ hnk]
    exact h2.mono_set hsub
  have hFtint : Integrable (Function.uncurry Ft)
      ((volume.restrict (uIoc (0:ℝ) 1)).prod (volume : Measure (Rn n))) := by
    rw [hprod]
    have h1 : IntegrableOn (Function.uncurry Ft) (Icc (0:ℝ) 1 ×ˢ K)
        ((volume : Measure ℝ).prod (volume : Measure (Rn n))) :=
      hFtcont.continuousOn.integrableOn_compact (isCompact_Icc.prod hKc)
    have h2 : IntegrableOn (Function.uncurry Ft) (Icc (0:ℝ) 1 ×ˢ univ)
        ((volume : Measure ℝ).prod (volume : Measure (Rn n))) := by
      refine h1.of_forall_sdiff_eq_zero (measurableSet_Icc.prod MeasurableSet.univ) ?_
      rintro ⟨s, y⟩ ⟨⟨hs, -⟩, hnot⟩
      have hy : y ∉ K := fun hy => hnot ⟨hs, hy⟩
      simp [hFt_def, Function.uncurry, hDζ0 _ hy]
    exact h2.mono_set hsub
  -- pointwise identity (i)
  have hI : ∀ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = d * ∫ s in (0:ℝ)..1, F s x := by
    intro x
    have hderiv : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => ζ (x - (s * d) • e))
        (fderiv ℝ ζ (x - (s * d) • e) (-(d • e))) s := by
      intro s _
      have hl : HasDerivAt (fun s : ℝ => x - (s * d) • e) (-(d • e)) s := by
        have := (((hasDerivAt_id s).mul_const d).smul_const e).const_sub x
        simpa using this
      exact (hζdiff _).hasFDerivAt.comp_hasDerivAt s hl
    have hcontd : Continuous (fun s : ℝ => fderiv ℝ ζ (x - (s * d) • e) e) := by
      have hm : Continuous (fun s : ℝ => x - (s * d) • e) := by fun_prop
      exact (hDζ.comp hm).clm_apply continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
      have hm : Continuous (fun s : ℝ => x - (s * d) • e) := by fun_prop
      exact ((hDζ.comp hm).clm_apply continuous_const).intervalIntegrable 0 1)
    have hrw : (fun s : ℝ => fderiv ℝ ζ (x - (s * d) • e) (-(d • e))) =
        fun s => -(d • fderiv ℝ ζ (x - (s * d) • e) e) := by
      funext s; rw [map_neg, map_smul]
    rw [hrw, intervalIntegral.integral_neg, intervalIntegral.integral_smul] at hftc
    simp only [one_mul, zero_mul, zero_smul, sub_zero] at hftc
    have hdiff : ζ x - ζ (x - d • e) = d • ∫ s in (0:ℝ)..1, fderiv ℝ ζ (x - (s * d) • e) e := by
      rw [← neg_neg (d • ∫ s in (0:ℝ)..1, fderiv ℝ ζ (x - (s * d) • e) e), hftc]; abel
    rw [hdiff, real_inner_smul_left]
    congr 1
    have hcongr : ∫ s in (0:ℝ)..1, F s x =
        ∫ s in (0:ℝ)..1, inner ℝ (fderiv ℝ ζ (x - (s * d) • e) e) (g x) := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [hF_def, hc_eq' s hs]
    rw [hcongr, real_inner_comm]
    have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ (g x))
      (hcontd.intervalIntegrable (μ := volume) 0 1)
    simp only [innerSL_apply_apply] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [real_inner_comm]
  -- pointwise identity (ii)
  have hII : ∀ y, ∫ s in (0:ℝ)..1, Ft s y =
      inner ℝ (∫ t in (0 : ℝ)..1, g (y + (t * d) • e)) (fderiv ℝ ζ y e) := by
    intro y
    by_cases hy : y ∈ K
    · have hgc : ContinuousOn (fun t : ℝ => g (y + (t * d) • e)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact hg.comp (by fun_prop) (fun t ht => hseg y hy t ht)
      have hcongr : ∫ s in (0:ℝ)..1, Ft s y =
          ∫ s in (0:ℝ)..1, inner ℝ (fderiv ℝ ζ y e) (g (y + (s * d) • e)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        simp only [hFt_def, hc_eq' s hs]
      rw [hcongr, real_inner_comm]
      have := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ (fderiv ℝ ζ y e))
        (hgc.intervalIntegrable (μ := volume))
      simp only [innerSL_apply_apply] at this
      exact this
    · simp [hFt_def, hDζ0 _ hy]
  -- translation
  have hT : ∀ s, ∫ x, F s x = ∫ y, Ft s y := by
    intro s
    rw [← integral_add_right_eq_self (fun x => F s x) ((c s * d) • e)]
    congr 1
    funext y
    simp [hF_def, hFt_def]
  -- main chain
  calc ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x)
      = ∫ x, d * ∫ s in (0:ℝ)..1, F s x := by
        congr 1; funext x; exact hI x
    _ = d * ∫ x, ∫ s in (0:ℝ)..1, F s x := integral_const_mul d _
    _ = d * ∫ s in (0:ℝ)..1, ∫ x, F s x := by
        rw [intervalIntegral_integral_swap hFint]
    _ = d * ∫ s in (0:ℝ)..1, ∫ y, Ft s y := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _
        exact hT s
    _ = d * ∫ y, ∫ s in (0:ℝ)..1, Ft s y := by
        rw [intervalIntegral_integral_swap hFtint]
    _ = d * ∫ x, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e) := by
        congr 1
        congr 1
        funext y
        exact hII y

/-- Elliptic bootstrap for Simon Ch. 5, Theorem 7.1 (second assertion), `C^{1,α} ⇒ C^{2,α}` step:
difference quotients of a weak solution satisfy the averaged linearized weak equation.  Let
`Ψ ∈ C²`, `u ∈ C¹(U; ℝ^ℓ)` and `g ∈ C⁰(U; ℝ^ℓ)` with `∫_U DΨ(Du)[Dφ] = -∫_U ⟨φ, g⟩` for every
`φ ∈ C¹_c(U; ℝ^ℓ)`, let `d ≠ 0` and `x + t d e ∈ U` for `x ∈ V`, `t ∈ [0, 1]`.  With
`Δ(x) = Du(x + d e) - Du(x)`, every `ζ ∈ C¹_c(V; ℝ^ℓ)` satisfies
`∫_V ∫₀¹ D²Ψ(Du(x) + tΔ(x))[d⁻¹Δ(x)][Dζ(x)] dt dx = ∫_V ⟨∫₀¹ g(x + t d e) dt, Dζ(x) e⟩ dx`.
Test the equation with `ζ` and with `ζ(· - d e)` and translate back.  By the fundamental theorem of
calculus for the real function `t ↦ DΨ(Du(x) + tΔ(x))[Dζ(x)]` the difference of the left sides is
`d` times the left side above; by `dohr_eb_elc2_shift_ibp` the difference of the right sides is `d`
times the right side above; cancel `d`. -/
theorem dohr_eb_elc2_dq_weak_equation : ∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U V : Set (Rn n)) (u g : Rn n → Rn ℓ) (e : Rn n) (d : ℝ), ContDiff ℝ 2 Ψ → IsOpen U → IsOpen V → ContDiffOn ℝ 1 u U → ContinuousOn g U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ V → ∫ x in V, (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) = ∫ x in V, inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e) := by
  intro n ℓ Ψ U V u g e d hΨ hU hV hu hg hd hseg hweak ζ hζ hζc hζV
  set K := tsupport ζ
  have hKc : IsCompact K := hζc
  have hKV : K ⊆ V := hζV
  -- the segments from points of `K` stay in `U`
  have hsegK : ∀ y ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, y + (t * d) • e ∈ U := fun y hy => hseg y (hKV hy)
  have hKU : K ⊆ U := fun y hy => by simpa using hsegK y hy 0 (by simp)
  have hKdU : ∀ y ∈ K, y + d • e ∈ U := fun y hy => by simpa using hsegK y hy 1 (by simp)
  have hDuAt : ∀ y ∈ U, ContinuousAt (fderiv ℝ u) y := fun y hy =>
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hgAt : ∀ y ∈ U, ContinuousAt g y := fun y hy => hg.continuousAt (hU.mem_nhds hy)
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hζcont : Continuous ζ := hζ.continuous
  have hDζ0 : ∀ y ∉ K, fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hζ0 : ∀ y ∉ K, ζ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- `A = DΨ` is `C¹` with derivative `B = D²Ψ`
  have hA1 : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hAc : Continuous (fderiv ℝ Ψ) := hA1.continuous
  have hAd : Differentiable ℝ (fderiv ℝ Ψ) := hA1.differentiable one_ne_zero
  -- a function vanishing off a compact `C` and continuous at the points of `C` is integrable
  have integ_of : ∀ (F : Rn n → ℝ) (C : Set (Rn n)), IsCompact C → (∀ y ∉ C, F y = 0) →
      (∀ y ∈ C, ContinuousAt F y) → Integrable F := by
    intro F C hC h0 hcont
    have hFc : Continuous F := by
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ C
      · exact hcont y hy
      · have hev : F =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hy] with z hz using h0 z hz
        exact continuousAt_const.congr hev.symm
    exact hFc.integrable_of_hasCompactSupport (HasCompactSupport.intro hC h0)
  -- the integrands of the two tested equations
  set F1 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u (y + d • e)) (fderiv ℝ ζ y) with hF1
  set F2 : Rn n → ℝ := fun y => fderiv ℝ Ψ (fderiv ℝ u y) (fderiv ℝ ζ y) with hF2
  set R2 : Rn n → ℝ := fun y => inner ℝ (ζ y) (g y) with hR2
  set R3 : Rn n → ℝ := fun x => inner ℝ (ζ (x - d • e)) (g x) with hR3
  set Kd : Set (Rn n) := (fun y => y + d • e) '' K
  have hKdc : IsCompact Kd := hKc.image (continuous_id.add continuous_const)
  have hmemKd : ∀ x, x - d • e ∈ K → x ∈ Kd := fun x hx => ⟨x - d • e, hx, by simp⟩
  have hKdU' : Kd ⊆ U := by rintro _ ⟨y, hy, rfl⟩; exact hKdU y hy
  have hF1i : Integrable F1 := by
    refine integ_of F1 K hKc (fun y hy => by simp [hF1, hDζ0 y hy]) (fun y hy => ?_)
    have h1 : ContinuousAt (fun y => fderiv ℝ u (y + d • e)) y :=
      (hDuAt _ (hKdU y hy)).comp_of_eq (continuous_id.add continuous_const).continuousAt rfl
    exact (hAc.continuousAt.comp h1).clm_apply hDζ.continuousAt
  have hF2i : Integrable F2 := by
    refine integ_of F2 K hKc (fun y hy => by simp [hF2, hDζ0 y hy]) (fun y hy => ?_)
    exact (hAc.continuousAt.comp (hDuAt y (hKU hy))).clm_apply hDζ.continuousAt
  have hR2i : Integrable R2 := by
    refine integ_of R2 K hKc (fun y hy => by simp [hR2, hζ0 y hy]) (fun y hy => ?_)
    exact hζcont.continuousAt.inner (hgAt y (hKU hy))
  have hR3i : Integrable R3 := by
    refine integ_of R3 Kd hKdc (fun x hx => ?_) (fun x hx => ?_)
    · have : x - d • e ∉ K := fun h => hx (hmemKd x h)
      simp [hR3, hζ0 _ this]
    · have h1 : ContinuousAt (fun x => ζ (x - d • e)) x :=
        (hζcont.comp (continuous_sub_right _)).continuousAt
      exact h1.inner (hgAt x (hKdU' hx))
  -- (E2): the equation tested with `ζ`
  have hE2 : ∫ y, F2 y = -∫ y, R2 y := by
    have h := hweak ζ hζ hζc hKU
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ x) = ∫ y, F2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hDζ0 x this]
    have hr : ∫ x in U, inner ℝ (ζ x) (g x) = ∫ y, R2 y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x ∉ K := fun h' => hx (hKU h')
      simp [hζ0 x this]
    rw [hl, hr] at h
    exact h
  -- (E1): the equation tested with the translate `φ₁ = ζ(· - d e)`, translated back
  set φ1 : Rn n → Rn ℓ := fun x => ζ (x - d • e) with hφ1
  have hφ1C : ContDiff ℝ 1 φ1 := hζ.comp (contDiff_id.sub contDiff_const)
  have hφ1c : HasCompactSupport φ1 :=
    hζc.comp_isClosedEmbedding (Homeomorph.subRight (d • e)).isClosedEmbedding
  have hφ1ts : tsupport φ1 ⊆ U := by
    intro x hx
    have h := (tsupport_comp_eq_preimage ζ (Homeomorph.subRight (d • e))).subset hx
    have hxK : x - d • e ∈ K := h
    simpa using hKdU _ hxK
  have hφ1D : ∀ x, fderiv ℝ φ1 x = fderiv ℝ ζ (x - d • e) := fun x => fderiv_comp_sub (d • e)
  have hE1 : ∫ y, F1 y = -∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
    have h := hweak φ1 hφ1C hφ1c hφ1ts
    have hl : ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ1 x) =
        ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp only [hφ1D]
      · intro x hx
        have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
        simp [hφ1D, hDζ0 _ this]
    have hr : ∫ x in U, inner ℝ (φ1 x) (g x) = ∫ x, R3 x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have : x - d • e ∉ K := fun h' => hx (hKdU' (hmemKd x h'))
      simp [hφ1, hζ0 _ this]
    have hl' : ∫ x, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ ζ (x - d • e)) = ∫ y, F1 y := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hF1]
    have hr' : ∫ x, R3 x = ∫ y, inner ℝ (ζ y) (g (y + d • e)) := by
      rw [← integral_add_right_eq_self _ (d • e)]
      simp [hR3]
    rw [hl, hr, hl', hr'] at h
    exact h
  have hR1R3 : ∫ y, inner ℝ (ζ y) (g (y + d • e)) = ∫ x, R3 x := by
    rw [← integral_add_right_eq_self R3 (d • e)]
    simp [hR3]
  -- (E1) - (E2)
  have hE3 : ∫ y, (F1 y - F2 y) = ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) := by
    rw [integral_sub hF1i hF2i, hE1, hE2, hR1R3]
    have : ∫ x, inner ℝ (ζ x - ζ (x - d • e)) (g x) = ∫ x, (R2 x - R3 x) := by
      congr 1; funext x; simp [hR2, hR3, inner_sub_left]
    rw [this, integral_sub hR2i hR3i]
    ring
  -- pointwise: `F1 - F2 = d • I`, by the fundamental theorem of calculus for the real function
  -- `t ↦ DΨ(P + t (Q - P))[w]` with `P = Du(y)`, `Q = Du(y + d e)`, `w = Dζ(y)`
  set I : Rn n → ℝ := fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ)
    (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x))
    (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x) with hI
  set J : Rn n → ℝ := fun x => inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (fderiv ℝ ζ x e)
    with hJ
  have hFTC : ∀ y, F1 y - F2 y = d * I y := by
    intro y
    simp only [hF1, hF2, hI]
    generalize fderiv ℝ u (y + d • e) = Q
    generalize fderiv ℝ u y = P
    generalize fderiv ℝ ζ y = w
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => fderiv ℝ Ψ (P + t • (Q - P)) w)
          (fderiv ℝ (fderiv ℝ Ψ) (P + t • (Q - P)) (Q - P) w) t := by
      intro t _
      have h1 := (hAd (P + t • (Q - P))).hasFDerivAt.clm_apply
        (hasFDerivAt_const w (P + t • (Q - P)))
      have hl : HasDerivAt (fun t : ℝ => P + t • (Q - P)) (Q - P) t := by
        simpa using ((hasDerivAt_id t).smul_const (Q - P)).const_add P
      have h2 := h1.comp_hasDerivAt t hl
      simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
        ContinuousLinearMap.flip_apply] at h2
      exact h2
    have hcont : Continuous fun t : ℝ => fderiv ℝ (fderiv ℝ Ψ) (P + t • (Q - P)) (Q - P) w := by
      have hB := hA1.continuous_fderiv one_ne_zero
      fun_prop
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
    rw [one_smul ℝ (Q - P), add_sub_cancel P Q, zero_smul ℝ (Q - P), add_zero P] at hftc
    rw [← hftc, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  -- the right sides, by the sibling `dohr_eb_elc2_shift_ibp`
  have hIBP := Submission.dohr_eb_elc2_shift_ibp n ℓ U g ζ e d hU hg hζ hζc hsegK
  have hmain : ∫ x, I x = ∫ x, J x := by
    have h1 : ∫ y, (F1 y - F2 y) = d * ∫ x, I x := by
      rw [← integral_const_mul]; congr 1; funext y; exact hFTC y
    have h2 : d * ∫ x, I x = d * ∫ x, J x := by rw [← h1, hE3, hIBP]
    exact mul_left_cancel₀ hd h2
  -- both integrands vanish off `K ⊆ V`
  have hIV : ∫ x in V, I x = ∫ x, I x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hI, hDζ0 x this]
  have hJV : ∫ x in V, J x = ∫ x, J x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have : x ∉ K := fun h' => hx (hKV h')
    simp [hJ, hDζ0 x this]
  calc _ = ∫ x in V, I x := rfl
    _ = ∫ x in V, J x := by rw [hIV, hJV, hmain]
    _ = _ := rfl

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

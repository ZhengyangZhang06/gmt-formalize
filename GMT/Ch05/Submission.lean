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

/-- **Lusin's theorem for `Lⁿ` on sets of possibly infinite measure** (used in Simon Ch. 2, proof of
Theorem 1.5, p. 44), for a Borel map `F : ℝⁿ → L(ℝⁿ, ℝ)`.  Proof: `Lⁿ` is inner regular by closed
sets also on Borel sets of infinite measure (exhaust by the bounded pieces `E ∩ B̆(0, k + 1)` with
summable tolerances and intersect the sets `Kₖ ∪ B̆(0, k + 1)ᶜ`).  Fix a countable basis `(V)` of the
second-countable space `L(ℝⁿ, ℝ)` and tolerances `ε_V` with `Σ ε_V < δ`; choose closed
`K_V ⊆ S ∩ F⁻¹(V)` and `K'_V ⊆ S \ F⁻¹(V)` missing measure `< ε_V` of `S`.  Then
`C = ⋂_V (K_V ∪ K'_V)` is closed, `Lⁿ(S \ C) ≤ Σ ε_V < δ`, and `F|C` is continuous because
`C ∩ F⁻¹(V) = C \ K'_V` is relatively open in `C` for every basic `V`. -/
theorem tae_c1_lusin_clm_volume : ∀ {n : ℕ} (F : Rn n → (Rn n →L[ℝ] ℝ)), Measurable F → ∀ S : Set (Rn n), MeasurableSet S → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ C : Set (Rn n), C ⊆ S ∧ IsClosed C ∧ volume (S \ C) < δ ∧ ContinuousOn F C := by
  intro n F hF S hS δ hδ
  -- Inner regularity of `Lⁿ` by closed sets, also for Borel sets of infinite measure.
  have hreg : ∀ E : Set (Rn n), MeasurableSet E → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K ⊆ E, IsClosed K ∧ volume (E \ K) < ε := by
    intro E hE ε hε
    obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable hε ℕ
    have hK : ∀ k : ℕ, ∃ K ⊆ E ∩ ball (0 : Rn n) (k + 1), IsClosed K ∧
        volume ((E ∩ ball (0 : Rn n) (k + 1)) \ K) < ε' k := fun k =>
      (hE.inter measurableSet_ball).exists_isClosed_sdiff_lt
        ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        (ENNReal.coe_ne_zero.2 (hε'0 k).ne')
    choose K hKE hKc hKμ using hK
    refine ⟨⋂ k : ℕ, (K k ∪ (ball (0 : Rn n) (k + 1))ᶜ), fun x hx => ?_,
      isClosed_iInter fun k => (hKc k).union isOpen_ball.isClosed_compl, ?_⟩
    · obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
      rcases mem_iInter.1 hx k with hxK | hxB
      · exact (hKE k hxK).1
      · exact absurd (mem_ball_zero_iff.2 (hk.trans (lt_add_one _))) hxB
    · calc volume (E \ ⋂ k : ℕ, (K k ∪ (ball (0 : Rn n) (k + 1))ᶜ))
          ≤ volume (⋃ k : ℕ, (E ∩ ball (0 : Rn n) (k + 1)) \ K k) := by
            refine measure_mono fun x hx => ?_
            obtain ⟨hxE, hxK⟩ := hx
            rw [mem_iInter, not_forall] at hxK
            obtain ⟨k, hk⟩ := hxK
            rw [mem_union, mem_compl_iff, not_or, not_not] at hk
            exact mem_iUnion.2 ⟨k, ⟨hxE, hk.2⟩, hk.1⟩
        _ ≤ ∑' k : ℕ, volume ((E ∩ ball (0 : Rn n) (k + 1)) \ K k) := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, (ε' k : ℝ≥0∞) := ENNReal.tsum_le_tsum fun k => (hKμ k).le
        _ < ε := hε'
  -- A countable basis of `L(ℝⁿ, ℝ)` and summable tolerances indexed by it.
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (Rn n →L[ℝ] ℝ)
  have : Countable b := hbc.to_subtype
  obtain ⟨ε, hε0, hε⟩ := ENNReal.exists_pos_sum_of_countable hδ b
  have hK : ∀ V : b, ∃ K ⊆ S ∩ F ⁻¹' V, IsClosed K ∧ ∃ K' ⊆ S \ F ⁻¹' V, IsClosed K' ∧
      volume (S \ (K ∪ K')) < ε V := by
    intro V
    have hP : MeasurableSet (F ⁻¹' (V : Set (Rn n →L[ℝ] ℝ))) := hF (hb.isOpen V.2).measurableSet
    have hε2 : (ε V : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_ne_zero.2 (hε0 V).ne')).ne'
    obtain ⟨K, hKs, hKc, hKμ⟩ := hreg _ (hS.inter hP) _ hε2
    obtain ⟨K', hK's, hK'c, hK'μ⟩ := hreg _ (hS.diff hP) _ hε2
    refine ⟨K, hKs, hKc, K', hK's, hK'c, ?_⟩
    calc volume (S \ (K ∪ K')) ≤ volume ((S ∩ F ⁻¹' V) \ K ∪ (S \ F ⁻¹' V) \ K') := by
          refine measure_mono fun x hx => ?_
          by_cases hxV : x ∈ F ⁻¹' (V : Set (Rn n →L[ℝ] ℝ))
          · exact Or.inl ⟨⟨hx.1, hxV⟩, fun h => hx.2 (Or.inl h)⟩
          · exact Or.inr ⟨⟨hx.1, hxV⟩, fun h => hx.2 (Or.inr h)⟩
      _ ≤ volume ((S ∩ F ⁻¹' V) \ K) + volume ((S \ F ⁻¹' V) \ K') := measure_union_le _ _
      _ < (ε V : ℝ≥0∞) / 2 + (ε V : ℝ≥0∞) / 2 := ENNReal.add_lt_add hKμ hK'μ
      _ = ε V := ENNReal.add_halves _
  choose K hKs hKc K' hK's hK'c hKμ using hK
  refine ⟨⋂ V : b, (K V ∪ K' V), fun x hx => ?_, isClosed_iInter fun V => (hKc V).union (hK'c V),
    ?_, ?_⟩
  · obtain ⟨V, hVb, -⟩ := hb.exists_subset_of_mem_open (mem_univ (F x)) isOpen_univ
    rcases mem_iInter.1 hx ⟨V, hVb⟩ with h | h
    · exact (hKs _ h).1
    · exact (hK's _ h).1
  · calc volume (S \ ⋂ V : b, (K V ∪ K' V)) = volume (⋃ V : b, S \ (K V ∪ K' V)) := by
          rw [sdiff_iInter]
      _ ≤ ∑' V : b, volume (S \ (K V ∪ K' V)) := measure_iUnion_le _
      _ ≤ ∑' V : b, (ε V : ℝ≥0∞) := ENNReal.tsum_le_tsum fun V => (hKμ V).le
      _ < δ := hε
  · rw [_root_.continuousOn_iff]
    intro x _ t ht hxt
    obtain ⟨V, hVb, hxV, hVt⟩ := hb.exists_subset_of_mem_open hxt ht
    refine ⟨(K' ⟨V, hVb⟩)ᶜ, (hK'c _).isOpen_compl, fun h => (hK's _ h).2 hxV, ?_⟩
    rintro y ⟨hy1, hy2⟩
    rcases mem_iInter.1 hy2 ⟨V, hVb⟩ with h | h
    · exact hVt (hKs _ h).2
    · exact absurd h hy1
/-- Simon Ch. 2, proof of Theorem 1.5 (p. 44), Egorov step: if `f : ℝⁿ → ℝ` is `K`-Lipschitz and
differentiable at every point of the closed set `C`, then for every `δ > 0` there is a closed
`A ⊆ C` with `Lⁿ(C \ A) < δ` on whose compact subsets the first-order Taylor remainder is uniformly
small: `|f(y) - f(x) - Df(x)(y - x)| ≤ η |y - x|` for `x ∈ Q`, `y ∈ A`, `|x - y| < ρ`.  The
quotients `σₖ(x, L) = sup {|f(x + v) - f(x) - L v| / |v| : 0 < |v| < 1/(k+1)}` are bounded by
`K + ‖L‖` and lower semicontinuous in `(x, L)`, so `x ↦ σₖ(x, Df(x))` is Borel, and they tend to
`0` at every point of `C`.  Egorov's theorem on the finite-measure pieces `B(0, J) ∩ C` with
summable tolerances and outer regularity give an open `U` of measure `< δ` containing the
exceptional sets; `A = C \ U` works, since a compact `Q ⊆ A` lies in some `B(0, J)`. -/
theorem tae_c1_uniform_remainder : ∀ {n : ℕ} (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ C : Set (Rn n), IsClosed C → C ⊆ {x | DifferentiableAt ℝ f x} → ∀ δ : ℝ≥0∞, δ ≠ 0 → ∃ A : Set (Rn n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < δ ∧ ∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ η * ‖y - x‖ := by
  intro n f K hf C hC hCd δ hδ
  have hfc : Continuous f := hf.continuous
  -- Remainder quotients `σ k (x, L) = sup {|f (x + v) - f x - L v| / |v| : 0 < |v| < 1/(k+1)}`.
  obtain ⟨σ, hσ0, hσle, hσge, hσlsc⟩ : ∃ σ : ℕ → Rn n × (Rn n →L[ℝ] ℝ) → ℝ,
      (∀ k p, 0 ≤ σ k p) ∧
      (∀ (k : ℕ) p (v : Rn n), 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ σ k p * ‖v‖) ∧
      (∀ (k : ℕ) p (t : ℝ), 0 ≤ t → (∀ v : Rn n, 0 < ‖v‖ → ‖v‖ < 1 / ((k : ℝ) + 1) →
        |f (p.1 + v) - f p.1 - p.2 v| ≤ t * ‖v‖) → σ k p ≤ t) ∧
      ∀ k, LowerSemicontinuous (σ k) := by
    have hbdd : ∀ (k : ℕ) (p : Rn n × (Rn n →L[ℝ] ℝ)), BddAbove (range fun v :
        {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
          |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) := by
      intro k p
      refine ⟨K + ‖p.2‖, ?_⟩
      rintro _ ⟨v, rfl⟩
      rw [div_le_iff₀ v.2.1]
      have h1 := hf.dist_le_mul (p.1 + v) p.1
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h1
      have h2 := p.2.le_opNorm v
      rw [Real.norm_eq_abs] at h2
      calc |f (p.1 + v) - f p.1 - p.2 v| ≤ |f (p.1 + v) - f p.1| + |p.2 v| := abs_sub _ _
        _ ≤ K * ‖(v : Rn n)‖ + ‖p.2‖ * ‖(v : Rn n)‖ := add_le_add h1 h2
        _ = (K + ‖p.2‖) * ‖(v : Rn n)‖ := by ring
    refine ⟨fun k p => ⨆ v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)},
      |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖, fun k p => Real.iSup_nonneg fun v =>
        div_nonneg (abs_nonneg _) (norm_nonneg _), fun k p v hv0 hv1 => ?_,
      fun k p t ht hle => Real.iSup_le (fun v => ?_) ht, fun k => ?_⟩
    · rw [← div_le_iff₀ hv0]
      exact le_ciSup (f := fun v : {v : Rn n // 0 < ‖v‖ ∧ ‖v‖ < 1 / ((k : ℝ) + 1)} =>
        |f (p.1 + v) - f p.1 - p.2 v| / ‖(v : Rn n)‖) (hbdd k p) ⟨v, hv0, hv1⟩
    · rw [div_le_iff₀ v.2.1]
      exact hle v v.2.1 v.2.2
    · refine lowerSemicontinuous_ciSup (hbdd k) fun v => Continuous.lowerSemicontinuous ?_
      exact (((hfc.comp (continuous_fst.add continuous_const)).sub (hfc.comp continuous_fst)).sub
        (continuous_snd.clm_apply continuous_const)).abs.div_const _
  have hσm : ∀ k, Measurable fun x => σ k (x, fderiv ℝ f x) := fun k =>
    (hσlsc k).measurable.comp (measurable_id.prodMk (measurable_fderiv ℝ f))
  have hσlim : ∀ x, DifferentiableAt ℝ f x →
      Tendsto (fun k => σ k (x, fderiv ℝ f x)) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro t ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1
      (Asymptotics.isLittleO_iff.1 hx.hasFDerivAt.isLittleO (half_pos ht))
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hρ
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hσ0 k _)]
    refine lt_of_le_of_lt (hσge k _ (t / 2) (by positivity) fun v hv0 hv1 => ?_) (half_lt_self ht)
    have hk' : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    have h1 := @hball (x + v) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
    rwa [add_sub_cancel_left, Real.norm_eq_abs] at h1
  -- Egorov on the finite-measure pieces `B(0, J) ∩ C`, with summable tolerances.
  obtain ⟨δs, hδs0, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hδ ℕ
  have hEg : ∀ J : ℕ, ∃ t ⊆ ball (0 : Rn n) J ∩ C, MeasurableSet t ∧
      volume t ≤ δs J ∧ TendstoUniformlyOn (fun k x => σ k (x, fderiv ℝ f x)) (fun _ => (0 : ℝ))
        atTop ((ball (0 : Rn n) J ∩ C) \ t) := fun J =>
    tendstoUniformlyOn_of_ae_tendsto (fun k => (hσm k).stronglyMeasurable) stronglyMeasurable_const
      (measurableSet_ball.inter hC.measurableSet) ((measure_mono inter_subset_left).trans_lt
        measure_ball_lt_top).ne (Filter.Eventually.of_forall fun x hx => hσlim x (hCd hx.2))
      (by exact_mod_cast hδs0 J)
  choose t _ _ htle htu using hEg
  -- An open `U ⊇ ⋃ J, t J` of measure `< δ`; take `A = C \ U`.
  obtain ⟨U, hZU, hUo, hUδ⟩ := Set.exists_isOpen_lt_of_lt (⋃ J, t J) δ
    (((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum htle)).trans_lt hδsum)
  refine ⟨C \ U, sdiff_subset, hC.sdiff hUo, (measure_mono fun x hx => ?_).trans_lt hUδ,
    fun Q hQ hQA η hη => ?_⟩
  · by_contra hxU
    exact hx.2 ⟨hx.1, hxU⟩
  -- A compact `Q ⊆ C \ U` lies in some `B(0, J)`, on which `σ k (·, Df ·) → 0` uniformly.
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball (0 : Rn n)
  obtain ⟨J, hJ⟩ := exists_nat_gt R
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.1 (htu J) η hη).exists
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun x hx y _ hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have hxJ : x ∈ (ball (0 : Rn n) J ∩ C) \ t J :=
    ⟨⟨ball_subset_ball hJ.le (hR hx), (hQA hx).1⟩,
      fun h' => (hQA hx).2 (hZU (mem_iUnion.2 ⟨J, h'⟩))⟩
  have h1 := hk x hxJ
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hσ0 _ _)] at h1
  have h2 : |f (x + (y - x)) - f x - fderiv ℝ f x (y - x)| ≤ σ k (x, fderiv ℝ f x) * ‖y - x‖ :=
    hσle k (x, fderiv ℝ f x) (y - x) (norm_pos_iff.2 (sub_ne_zero.2 hyx))
      (by rwa [← dist_eq_norm, dist_comm])
  rw [add_sub_cancel] at h2
  rw [Real.norm_eq_abs]
  exact h2.trans (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
/-- **Simon Ch. 2, Theorem 1.6 (Whitney's `C¹` extension theorem).**  Let `A ⊆ ℝⁿ` be closed and
let `h : ℝⁿ → ℝ`, `D : ℝⁿ → L(ℝⁿ, ℝ)` be continuous on `A`, with first-order Taylor remainder
`|h y - h x - D x (y - x)| ≤ η |y - x|` uniformly for `x` in compact subsets of `A` and `y ∈ A` near
`x`.  Then some `g ∈ C¹(ℝⁿ)` equals `h` on `A` and has derivative `D a` at every `a ∈ A`.
Proof (the Evans–Gariepy/Federer construction cited by Simon): compactness of `A ∩ B(a, 1)` gives
a local uniform estimate near each `a ∈ A`; Vitali-selected Whitney balls `B(c, r c)`,
`r = min 1 (dist (·, A)) / 100`, have bounded overlap; rescaled bumps give a smooth partition of
unity `φ c` on `Aᶜ` with `∑ ‖Dφ c‖ ≤ M / r`; `g = ∑ φ c · (h b_c + D b_c (· - b_c))` off `A`
(nearest-point anchors `b_c`) and `g = h` on `A`. -/
theorem tae_whitney_c1_extension : ∀ {n : ℕ} (A : Set (Rn n)) (h : Rn n → ℝ) (D : Rn n → (Rn n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Rn n), IsCompact Q → Q ⊆ A → ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < ρ → ‖h y - h x - D x (y - x)‖ ≤ η * ‖y - x‖) → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ (∀ a ∈ A, g a = h a) ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
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
  · exact ⟨fun _ => 0, contDiff_const, fun x hx => hx.elim, fun x hx => hx.elim⟩
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
    hgA, hgdA⟩
  · by_cases hx : x ∈ A
    · exact (hgdA x hx).differentiableAt
    · exact (hgd x hx).differentiableAt
  · by_cases hx : x ∈ A
    · exact hgcA x hx
    · exact (hgcd x hx).continuousAt_fderiv one_ne_zero
/-- **Simon Ch. 2, Theorem 1.5 (C¹ approximation of Lipschitz functions), with derivatives.**
A Lipschitz `f : ℝⁿ → ℝ` agrees with a `C¹` function `g`, and `Df` with `Dg`, outside a set of
arbitrarily small Lebesgue measure.  Proof, following Simon's printed argument: by Rademacher
`f` is differentiable off a Borel null set `Bᶜ` and `Df` is Borel; Lusin
(`tae_c1_lusin_clm_volume`) gives a closed `C ⊆ B` with `Df|C` continuous and `Lⁿ(B \ C) < ε/2`;
Egorov (`tae_c1_uniform_remainder`) gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` on whose
compact subsets the first-order Taylor remainder of `f` is uniformly small; Whitney's extension
theorem (`tae_whitney_c1_extension`, Simon Ch. 2, 1.6) then yields `g ∈ C¹` with `g = f` and
`Dg = Df` on `A`, so `{f ≠ g} ∪ {Df ≠ Dg} ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem tae_lipschitz_c1_approximation : ∀ {n : ℕ} (f : Rn n → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ ε : ℝ, 0 < ε → ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume ({x | f x ≠ g x} ∪ {x | fderiv ℝ f x ≠ fderiv ℝ g x}) < ENNReal.ofReal ε := by
  intro n f K hf ε hε
  -- Rademacher: `f` is differentiable off a Borel null set, and `Df` is Borel.
  have hBm : MeasurableSet {x | DifferentiableAt ℝ f x} := measurableSet_of_differentiableAt ℝ f
  have hB0 : volume {x | DifferentiableAt ℝ f x}ᶜ = 0 := by
    have h1 := hf.ae_differentiableAt (μ := (volume : Measure (Rn n)))
    rwa [ae_iff, ← Set.compl_ofPred] at h1
  have hε2 : ENNReal.ofReal ε / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.ofReal_pos.2 hε).ne').ne'
  -- Lusin: a closed `C ⊆ B` with `Lⁿ(B \ C) < ε/2` on which `Df` is continuous.
  obtain ⟨C, hCB, hCc, hBC, hDC⟩ :=
    Submission.tae_c1_lusin_clm_volume (fderiv ℝ f) (measurable_fderiv ℝ f) _ hBm _ hε2
  -- Egorov: a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` and a compact-uniform Taylor estimate.
  obtain ⟨A, hAC, hAc, hCA, hrem⟩ :=
    Submission.tae_c1_uniform_remainder f K hf C hCc hCB _ hε2
  -- Whitney: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`.
  obtain ⟨g, hg, hgA, hgD⟩ := Submission.tae_whitney_c1_extension A f (fderiv ℝ f) hAc
    hf.continuous.continuousOn (hDC.mono hAC) hrem
  refine ⟨g, hg, ?_⟩
  calc volume ({x | f x ≠ g x} ∪ {x | fderiv ℝ f x ≠ fderiv ℝ g x})
      ≤ volume ({x | DifferentiableAt ℝ f x}ᶜ ∪ ({x | DifferentiableAt ℝ f x} \ C) ∪ (C \ A)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · exfalso
          rcases hx with hx | hx
          · exact hx (hgA x hxA).symm
          · exact hx (hgD x hxA).fderiv.symm
        by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        by_cases hxB : DifferentiableAt ℝ f x
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
    _ ≤ volume {x | DifferentiableAt ℝ f x}ᶜ + volume ({x | DifferentiableAt ℝ f x} \ C)
          + volume (C \ A) := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = volume ({x | DifferentiableAt ℝ f x} \ C) + volume (C \ A) := by rw [hB0, zero_add]
    _ < ENNReal.ofReal ε / 2 + ENNReal.ofReal ε / 2 := ENNReal.add_lt_add hBC hCA
    _ = ENNReal.ofReal ε := ENNReal.add_halves _
/-- **Simon Ch. 3, Lemma 1.2 ('only if') and Remark 1.3: a countably `n`-rectifiable set is
covered, up to an `Hⁿ`-null set, by countably many bi-Lipschitz `C¹` chart images.**
Each Lipschitz parametrization `F_j` agrees with `C¹` maps `G_{ij}` off sets of Lebesgue measure
`< 1/i` (coordinatewise `Submission.tae_lipschitz_c1_approximation`), so `F_j(ℝⁿ)` lies in the
null set `F_j(Z_j)` together with `⋃ᵢ G_{ij}(ℝⁿ)`.  The critical image
`G_{ij}({v | DG_{ij}(v) not injective})` is `Hⁿ`-null; this is proved inline: on a grid cell of
side `< δ`, `G_{ij}` factors through a compression along a kernel direction of the derivative (of
determinant `ε`), and the Lipschitz image bound gives measure `≤ C ε`.  Around each regular point
the mean value inequality gives a ball on which `DG_{ij}` is injective and
`κ |v - w| ≤ |G_{ij}(v) - G_{ij}(w)|`, and Lindelöf extracts countably many such balls. -/
theorem tae_rectifiable_c1_chart_cover : ∀ {n ℓ : ℕ} (M : Set (Amb n ℓ)), 1 ≤ n → Poincare.SimonGMT.Chapter03.CountablyRectifiable n M → ∃ (N₀ : Set (Amb n ℓ)) (G : ℕ → Rn n → Amb n ℓ) (c : ℕ → Rn n) (ρ : ℕ → ℝ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧ (∀ k, ContDiff ℝ 1 (G k)) ∧ (∀ k, ∀ v ∈ ball (c k) (ρ k), Function.Injective (fderiv ℝ (G k) v)) ∧ (∀ k, ∃ κ : ℝ, 0 < κ ∧ ∀ v ∈ ball (c k) (ρ k), ∀ w ∈ ball (c k) (ρ k), κ * ‖v - w‖ ≤ ‖G k v - G k w‖) ∧ M ⊆ N₀ ∪ ⋃ k, G k '' ball (c k) (ρ k) := by
  intro n ℓ M _hn hM
  classical
  -- Parent step 2 input: the scalar approximation property from the resolved dependency.
  have happrox : ∀ (f : Rn n → ℝ) (K' : ℝ≥0), LipschitzWith K' f → ∀ ε : ℝ, 0 < ε →
      ∃ g : Rn n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x} < ENNReal.ofReal ε := by
    intro f K' hf ε hε
    obtain ⟨g, hg, hvol⟩ := Submission.tae_lipschitz_c1_approximation f K' hf ε hε
    exact ⟨g, hg, (measure_mono subset_union_left).trans_lt hvol⟩
  -- Parent step 4 (critical images are null), proved inline.
  have sard : ∀ G : Rn n → Amb n ℓ, ContDiff ℝ 1 G →
      (μHE[n] : Measure (Amb n ℓ)) (G '' {v | ¬ Function.Injective (fderiv ℝ G v)}) = 0 := by
    intro G hG
    classical
    have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
    set Crit : Set (Rn n) := {v | ¬ Function.Injective (fderiv ℝ G v)} with hCrit
    suffices H : ∀ R : ℕ, (μHE[n] : Measure (Amb n ℓ)) (G '' (Crit ∩ closedBall 0 R)) = 0 by
      have hsub : Crit ⊆ ⋃ R : ℕ, Crit ∩ closedBall 0 R := by
        intro v hv
        obtain ⟨R, hR⟩ := exists_nat_ge ‖v‖
        exact mem_iUnion.2 ⟨R, hv, by simpa [mem_closedBall, dist_zero_right] using hR⟩
      refine measure_mono_null (image_mono hsub) ?_
      rw [image_iUnion]
      exact measure_iUnion_null H
    intro R
    set K : Set (Rn n) := closedBall 0 ((R : ℝ) + 1) with hKdef
    have hKc : IsCompact K := isCompact_closedBall _ _
    obtain ⟨Λ, hΛ⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
    have h0K : (0 : Rn n) ∈ K := by
      simp only [K, mem_closedBall, dist_self]; positivity
    have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0 h0K)
    have hVK : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
    have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (μHE[n] : Measure (Amb n ℓ)) (G '' (Crit ∩ closedBall 0 R)) ≤
          ENNReal.ofReal ((Λ + 1) ^ n * ε) * volume K := by
      intro ε hε hε1
      obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.1
        (hKc.uniformContinuousOn_of_continuous hcont.continuousOn) ε hε
      set r : ℝ := min δ 1 with hr
      have hr0 : 0 < r := lt_min hδ one_pos
      set s : ℝ := r / ((n : ℝ) + 1) with hs
      have hs0 : 0 < s := by positivity
      -- grid cells
      let cell : (Fin n → ℤ) → Set (Rn n) := fun z =>
        {x | ∀ i, (z i : ℝ) ≤ x i / s ∧ x i / s < z i + 1}
      have cell_iff : ∀ z x, x ∈ cell z ↔ ∀ i, ⌊x i / s⌋ = z i := by
        intro z x
        simp only [cell, mem_ofPred_eq, Int.floor_eq_iff]
      have cell_meas : ∀ z, MeasurableSet (cell z) := by
        intro z
        have hcell : cell z = ⋂ i, ({x : Rn n | (z i : ℝ) ≤ x i / s} ∩ {x | x i / s < z i + 1}) := by
          ext x
          simp only [cell, mem_ofPred_eq, mem_iInter, mem_inter_iff]
        rw [hcell]
        refine MeasurableSet.iInter fun i => ?_
        have hm : Measurable fun x : Rn n => x i / s :=
          ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).div_const s).measurable
        exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)
      have cell_disj : Pairwise (Function.onFun Disjoint cell) := by
        intro z z' hzz'
        refine Set.disjoint_left.2 fun x hx hx' => hzz' ?_
        funext i
        rw [← (cell_iff z x).1 hx i, (cell_iff z' x).1 hx' i]
      have cell_cover : ∀ x, x ∈ cell (fun i => ⌊x i / s⌋) := fun x => (cell_iff _ x).2 fun i => rfl
      have cell_convex : ∀ z, Convex ℝ (cell z) := by
        intro z x hx y hy a b ha hb hab i
        obtain ⟨h1, h2⟩ := hx i
        obtain ⟨h3, h4⟩ := hy i
        have hxy : (a • x + b • y) i / s = a * (x i / s) + b * (y i / s) := by
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
          ring
        rw [hxy]
        have hz : a * (z i : ℝ) + b * (z i : ℝ) = z i := by rw [← add_mul, hab, one_mul]
        have hz1 : a * ((z i : ℝ) + 1) + b * ((z i : ℝ) + 1) = z i + 1 := by
          rw [← add_mul, hab, one_mul]
        have l1 := mul_le_mul_of_nonneg_left h1 ha
        have l3 := mul_le_mul_of_nonneg_left h3 hb
        constructor
        · linarith
        · rcases (eq_or_lt_of_le ha) with ha0 | ha0
          · have hb1 : b = 1 := by rw [← ha0] at hab; linarith
            rw [← ha0, hb1]
            linarith
          · have l2 := mul_lt_mul_of_pos_left h2 ha0
            have l4 := mul_le_mul_of_nonneg_left h4.le hb
            linarith
      have cell_small : ∀ z, ∀ x ∈ cell z, ∀ y ∈ cell z, ‖x - y‖ < r := by
        intro z x hx y hy
        have hcoord : ∀ i, (x i - y i) ^ 2 ≤ s ^ 2 := by
          intro i
          obtain ⟨h1, h2⟩ := hx i
          obtain ⟨h3, h4⟩ := hy i
          rw [le_div_iff₀ hs0] at h1 h3
          rw [div_lt_iff₀ hs0] at h2 h4
          exact sq_le_sq' (by linarith) (by linarith)
        have hsq : ‖x - y‖ ^ 2 ≤ (n : ℝ) * s ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          calc ∑ i, (x - y) i ^ 2 ≤ ∑ _i : Fin n, s ^ 2 :=
                Finset.sum_le_sum fun i _ => by rw [PiLp.sub_apply]; exact hcoord i
            _ = (n : ℝ) * s ^ 2 := by simp
        have hlt : (n : ℝ) * s ^ 2 < r ^ 2 := by
          have hrs : r = ((n : ℝ) + 1) * s := by rw [hs]; field_simp
          have hn : (n : ℝ) < ((n : ℝ) + 1) ^ 2 := (lt_add_one (n : ℝ)).trans_le
            (le_self_pow₀ (le_add_of_nonneg_left n.cast_nonneg) two_ne_zero)
          rw [hrs, mul_pow]
          exact mul_lt_mul_of_pos_right hn (by positivity)
        have h2 : ‖x - y‖ ^ 2 < r ^ 2 := lt_of_le_of_lt hsq hlt
        exact lt_of_pow_lt_pow_left₀ 2 hr0.le h2
      -- the per-cell estimate
      have cell_bound : ∀ z, (μHE[n] : Measure (Amb n ℓ)) (G '' (cell z ∩ (Crit ∩ closedBall 0 R))) ≤
          ENNReal.ofReal ((Λ + 1) ^ n * ε) * volume (cell z ∩ K) := by
        intro z
        by_cases hne : (cell z ∩ (Crit ∩ closedBall 0 R)).Nonempty
        swap
        · rw [not_nonempty_iff_eq_empty.1 hne, image_empty, measure_empty]
          exact bot_le
        obtain ⟨v₀, hv₀c, hv₀C, hv₀R⟩ := hne
        have hcellK : cell z ⊆ K := by
          intro x hx
          have h1 := cell_small z x hx v₀ hv₀c
          have h2 : r ≤ 1 := min_le_right _ _
          simp only [K, mem_closedBall, dist_zero_right] at hv₀R ⊢
          have h3 : ‖x‖ ≤ ‖x - v₀‖ + ‖v₀‖ := norm_le_norm_sub_add x v₀
          linarith
        have hcellK' : cell z ∩ K = cell z := inter_eq_left.2 hcellK
        have hclose : ∀ w ∈ cell z, ‖fderiv ℝ G w - fderiv ℝ G v₀‖ < ε := by
          intro w hw
          have h1 : dist w v₀ < δ := by
            rw [dist_eq_norm]
            exact (cell_small z w hw v₀ hv₀c).trans_le (min_le_left _ _)
          have := hδK w (hcellK hw) v₀ (hcellK hv₀c) h1
          rwa [dist_eq_norm] at this
        obtain ⟨e, he1, hLe⟩ : ∃ e : Rn n, ‖e‖ = 1 ∧ fderiv ℝ G v₀ e = 0 := by
          have hv₀C' : ¬ Function.Injective (fderiv ℝ G v₀) := hv₀C
          simp only [Function.Injective, not_forall] at hv₀C'
          obtain ⟨a, b, hab, hne⟩ := hv₀C'
          have hab' : a - b ≠ 0 := sub_ne_zero.2 hne
          refine ⟨(‖a - b‖⁻¹ : ℝ) • (a - b), norm_smul_inv_norm hab', ?_⟩
          rw [map_smul, map_sub, hab, sub_self, smul_zero]
        have hsmall : ∀ w ∈ cell z, ‖fderiv ℝ G w e‖ ≤ ε := by
          intro w hw
          have h1 : fderiv ℝ G w e = (fderiv ℝ G w - fderiv ℝ G v₀) e := by
            rw [sub_apply, hLe, sub_zero]
          rw [h1]
          calc ‖(fderiv ℝ G w - fderiv ℝ G v₀) e‖ ≤ ‖fderiv ℝ G w - fderiv ℝ G v₀‖ * ‖e‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ε := by rw [he1, mul_one]; exact (hclose w hw).le
        have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he1]; norm_num
        -- compression and decompression along `e`
        let P : Rn n →L[ℝ] Rn n := (innerSL ℝ e).smulRight e
        have hP : ∀ x, P x = inner ℝ e x • e := fun x => rfl
        let C : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) - (1 - ε) • P
        let D : Rn n →L[ℝ] Rn n := ContinuousLinearMap.id ℝ (Rn n) + (ε⁻¹ - 1) • P
        have hC : ∀ x, C x = x - (1 - ε) • (inner ℝ e x • e) := fun x => by
          simp only [C, sub_apply, ContinuousLinearMap.id_apply,
            smul_apply, hP]
        have hD : ∀ x, D x = x + (ε⁻¹ - 1) • (inner ℝ e x • e) := fun x => by
          simp only [D, add_apply, ContinuousLinearMap.id_apply,
            smul_apply, hP]
        have hDC : ∀ x, D (C x) = x := by
          intro x
          have hin : inner ℝ e (C x) = ε * inner ℝ e x := by
            rw [hC, inner_sub_right, inner_smul_right, inner_smul_right, hee]
            ring
          rw [hD, hin, hC]
          have hcoef : (ε⁻¹ - 1) * (ε * inner ℝ e x) - (1 - ε) * inner ℝ e x = 0 := by
            field_simp
            ring
          calc x - (1 - ε) • (inner ℝ e x • e) + (ε⁻¹ - 1) • ((ε * inner ℝ e x) • e)
              = x + ((ε⁻¹ - 1) * (ε * inner ℝ e x) - (1 - ε) * inner ℝ e x) • e := by
                rw [smul_smul, smul_smul, sub_smul]; abel
            _ = x := by rw [hcoef, zero_smul, add_zero]
        have himg : G '' cell z = (G ∘ D) '' (C '' cell z) := by
          rw [image_image]
          exact image_congr fun x _ => by simp only [Function.comp_apply, hDC]
        -- `G ∘ D` is `(Λ + 1)`-Lipschitz on the compressed cell
        have hlip : LipschitzOnWith (Real.toNNReal (Λ + 1)) (G ∘ D) (C '' cell z) := by
          refine ((cell_convex z).linear_image (C : Rn n →ₗ[ℝ] Rn n)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
            (f' := fun p => (fderiv ℝ G (D p)).comp D)
            (fun p _ => ((hdiff (D p)).hasFDerivAt.comp p D.hasFDerivAt).hasFDerivWithinAt) ?_
          rintro _ ⟨x, hx, rfl⟩
          change ‖(fderiv ℝ G (D (C x))).comp D‖₊ ≤ Real.toNNReal (Λ + 1)
          rw [hDC]
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by linarith)]
          refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun u => ?_
          rw [ContinuousLinearMap.comp_apply, hD, map_add, map_smul, map_smul]
          have hΛx : ‖fderiv ℝ G x‖ ≤ Λ := hΛ x (hcellK hx)
          have h1 : ‖fderiv ℝ G x u‖ ≤ Λ * ‖u‖ :=
            (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hΛx (norm_nonneg _))
          have h2 : |inner ℝ e u| ≤ ‖u‖ := by
            have := abs_real_inner_le_norm e u
            rwa [he1, one_mul] at this
          have h3 : ‖fderiv ℝ G x e‖ ≤ ε := hsmall x hx
          have hinv : 1 ≤ ε⁻¹ := one_le_inv₀ hε |>.2 hε1
          have h4 : ‖(ε⁻¹ - 1) • (inner ℝ e u • fderiv ℝ G x e)‖ ≤ ‖u‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            have h5 : |inner ℝ e u| * ‖fderiv ℝ G x e‖ ≤ ‖u‖ * ε :=
              mul_le_mul h2 h3 (norm_nonneg _) (norm_nonneg _)
            have h6 : (ε⁻¹ - 1) * ε = 1 - ε := by field_simp
            calc (ε⁻¹ - 1) * (|inner ℝ e u| * ‖fderiv ℝ G x e‖) ≤ (ε⁻¹ - 1) * (‖u‖ * ε) :=
                  mul_le_mul_of_nonneg_left h5 (by linarith)
              _ = (1 - ε) * ‖u‖ := by rw [← h6]; ring
              _ ≤ ‖u‖ := mul_le_of_le_one_left (norm_nonneg u) (by linarith)
          calc ‖fderiv ℝ G x u + (ε⁻¹ - 1) • (inner ℝ e u • fderiv ℝ G x e)‖
              ≤ ‖fderiv ℝ G x u‖ + ‖(ε⁻¹ - 1) • (inner ℝ e u • fderiv ℝ G x e)‖ := norm_add_le _ _
            _ ≤ Λ * ‖u‖ + ‖u‖ := add_le_add h1 h4
            _ = (Λ + 1) * ‖u‖ := by ring
        -- determinant of the compression
        have hdet : LinearMap.det (C : Rn n →ₗ[ℝ] Rn n) = ε := by
          let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          rw [← LinearMap.det_toMatrix b]
          have hM : LinearMap.toMatrix b b (C : Rn n →ₗ[ℝ] Rn n) =
              1 + Matrix.replicateCol Unit (fun i => -(1 - ε) * e i) *
                Matrix.replicateRow Unit (fun j => e j) := by
            ext i j
            rw [LinearMap.toMatrix_apply]
            simp only [b, OrthonormalBasis.coe_toBasis,
              EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, hC,
              Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
              Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
            simp [EuclideanSpace.inner_single_right, PiLp.single_apply, eq_comm]
            ring
          rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
          have hsum : (fun j => e j) ⬝ᵥ (fun i => -(1 - ε) * e i) = -(1 - ε) := by
            simp only [dotProduct]
            have : ∑ i, e i * (-(1 - ε) * e i) = -(1 - ε) * ∑ i, e i ^ 2 := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            rw [this, ← EuclideanSpace.real_norm_sq_eq, he1]; ring
          rw [hsum]; ring
        calc (μHE[n] : Measure (Amb n ℓ)) (G '' (cell z ∩ (Crit ∩ closedBall 0 R)))
            ≤ (μHE[n] : Measure (Amb n ℓ)) (G '' cell z) := measure_mono (image_mono inter_subset_left)
          _ = (μHE[n] : Measure (Amb n ℓ)) ((G ∘ D) '' (C '' cell z)) := by rw [himg]
          _ ≤ (Real.toNNReal (Λ + 1) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) (C '' cell z) :=
              Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
          _ = (Real.toNNReal (Λ + 1) : ℝ≥0∞) ^ n * (ENNReal.ofReal |ε| * volume (cell z)) := by
              rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
                Measure.addHaar_image_continuousLinearMap, hdet]
          _ = ENNReal.ofReal ((Λ + 1) ^ n * ε) * volume (cell z ∩ K) := by
              rw [hcellK', abs_of_pos hε, ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_pow (by linarith), mul_assoc]
              rfl
      calc (μHE[n] : Measure (Amb n ℓ)) (G '' (Crit ∩ closedBall 0 R))
          ≤ (μHE[n] : Measure (Amb n ℓ)) (⋃ z, G '' (cell z ∩ (Crit ∩ closedBall 0 R))) := by
            apply measure_mono
            rintro _ ⟨x, hx, rfl⟩
            exact mem_iUnion.2 ⟨_, x, ⟨cell_cover x, hx⟩, rfl⟩
        _ ≤ ∑' z, (μHE[n] : Measure (Amb n ℓ)) (G '' (cell z ∩ (Crit ∩ closedBall 0 R))) :=
            measure_iUnion_le _
        _ ≤ ∑' z, ENNReal.ofReal ((Λ + 1) ^ n * ε) * volume (cell z ∩ K) :=
            ENNReal.tsum_le_tsum cell_bound
        _ = ENNReal.ofReal ((Λ + 1) ^ n * ε) * ∑' z, volume (cell z ∩ K) := ENNReal.tsum_mul_left
        _ = ENNReal.ofReal ((Λ + 1) ^ n * ε) * volume K := by
            congr 1
            rw [← measure_iUnion (fun z z' h => (cell_disj h).mono inter_subset_left inter_subset_left)
              (fun z => (cell_meas z).inter measurableSet_closedBall)]
            congr 1
            ext x
            simp only [mem_iUnion, mem_inter_iff]
            exact ⟨fun ⟨_, _, hx⟩ => hx, fun hx => ⟨_, cell_cover x, hx⟩⟩
    apply le_antisymm _ bot_le
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal ((Λ + 1) ^ n * (1 / ((m : ℝ) + 1))) * volume K)
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun m : ℕ => (Λ + 1) ^ n * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((Λ + 1) ^ n)
      have h2 := ENNReal.tendsto_ofReal h1
      rw [ENNReal.ofReal_zero] at h2
      simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hVK)
    refine ge_of_tendsto' hlim fun m => key _ (by positivity) ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  -- Parent step 5: bi-Lipschitz balls at regular points.
  have ballLemma : ∀ (G : Rn n → Amb n ℓ) (w₀ : Rn n), ContDiff ℝ 1 G →
      Function.Injective (fderiv ℝ G w₀) →
      ∃ δ : ℝ, 0 < δ ∧ (∀ v ∈ ball w₀ δ, Function.Injective (fderiv ℝ G v)) ∧
        ∃ κ : ℝ, 0 < κ ∧ ∀ v ∈ ball w₀ δ, ∀ w ∈ ball w₀ δ, κ * ‖v - w‖ ≤ ‖G v - G w‖ := by
    intro G w₀ hG hinj
    set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G w₀ with hL
    obtain ⟨K, Kpos, hK⟩ := (L : Rn n →ₗ[ℝ] Amb n ℓ).injective_iff_antilipschitz.mp hinj
    have hlow : ∀ h : Rn n, ‖h‖ ≤ (K : ℝ) * ‖L h‖ := fun h =>
      ZeroHomClass.bound_of_antilipschitz (L : Rn n →ₗ[ℝ] Amb n ℓ) hK h
    have Kpos' : (0 : ℝ) < K := Kpos
    set c₀ : ℝ := (K : ℝ)⁻¹ with hc₀
    have c₀pos : 0 < c₀ := inv_pos.mpr Kpos'
    have hlow' : ∀ h : Rn n, c₀ * ‖h‖ ≤ ‖L h‖ := by
      intro h
      rw [hc₀, inv_mul_le_iff₀ Kpos']
      exact hlow h
    have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
    obtain ⟨δ, δpos, hδ⟩ := Metric.continuous_iff.mp hcont w₀ (c₀ / 2) (by positivity)
    have hclose : ∀ v ∈ ball w₀ δ, ‖fderiv ℝ G v - L‖ ≤ c₀ / 2 := by
      intro v hv
      have := hδ v (by simpa [mem_ball] using hv)
      rw [dist_eq_norm] at this
      exact this.le
    refine ⟨δ, δpos, ?_, c₀ / 2, by positivity, ?_⟩
    · intro v hv
      have key : ∀ h : Rn n, c₀ / 2 * ‖h‖ ≤ ‖fderiv ℝ G v h‖ := by
        intro h
        have h1 : ‖(fderiv ℝ G v - L) h‖ ≤ c₀ / 2 * ‖h‖ :=
          ((fderiv ℝ G v - L).le_opNorm h).trans (by gcongr; exact hclose v hv)
        have h3 : ‖L h‖ ≤ ‖fderiv ℝ G v h‖ + ‖(fderiv ℝ G v - L) h‖ :=
          calc ‖L h‖ = ‖fderiv ℝ G v h - (fderiv ℝ G v - L) h‖ := by rw [sub_apply, sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        linarith [hlow' h]
      intro a b hab
      have h0 := key (a - b)
      rw [map_sub, hab, sub_self, norm_zero] at h0
      have : ‖a - b‖ ≤ 0 := by
        by_contra hpos
        have := mul_pos (half_pos c₀pos) (not_le.mp hpos)
        linarith
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    · intro v hv w hw
      set H : Rn n → Amb n ℓ := fun u => G u - L u with hHdef
      have hHd : ∀ u, HasFDerivAt H (fderiv ℝ G u - L) u := fun u =>
        (hdiff u).hasFDerivAt.sub L.hasFDerivAt
      have hHb : ∀ u ∈ ball w₀ δ, ‖fderiv ℝ H u‖ ≤ c₀ / 2 := by
        intro u hu
        rw [(hHd u).fderiv]
        exact hclose u hu
      have hmv := (convex_ball w₀ δ).norm_image_sub_le_of_norm_fderiv_le
        (fun u _ => (hHd u).differentiableAt) hHb hw hv
      have hHvw : H v - H w = (G v - G w) - L (v - w) := by
        simp only [hHdef, map_sub]; abel
      rw [hHvw] at hmv
      have h3 : ‖L (v - w)‖ ≤ ‖G v - G w‖ + ‖(G v - G w) - L (v - w)‖ := by
        calc ‖L (v - w)‖ = ‖(G v - G w) - ((G v - G w) - L (v - w))‖ := by rw [sub_sub_cancel]
          _ ≤ _ := norm_sub_le _ _
      linarith [hlow' (v - w)]
  -- Parent steps 4 and 6: Lindelöf cover of the regular set.
  have rangeCover : ∀ G : Rn n → Amb n ℓ, ContDiff ℝ 1 G →
      ∃ (N₀ : Set (Amb n ℓ)) (c : ℕ → Rn n) (ρ : ℕ → ℝ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧
        (∀ m, ∀ v ∈ ball (c m) (ρ m), Function.Injective (fderiv ℝ G v)) ∧
        (∀ m, ∃ κ : ℝ, 0 < κ ∧ ∀ v ∈ ball (c m) (ρ m), ∀ w ∈ ball (c m) (ρ m),
          κ * ‖v - w‖ ≤ ‖G v - G w‖) ∧
        range G ⊆ N₀ ∪ ⋃ m, G '' ball (c m) (ρ m) := by
    intro G hG
    classical
    have hdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
    set Crit : Set (Rn n) := {v | ¬ Function.Injective (fderiv ℝ G v)} with hCrit
    have hcrit : (μHE[n] : Measure (Amb n ℓ)) (G '' Crit) = 0 := sard G hG
    set O : Set (Rn n) := {v | Function.Injective (fderiv ℝ G v)} with hO
    have hball : ∀ v : O, ∃ δ : ℝ, 0 < δ ∧
        (∀ u ∈ ball (v : Rn n) δ, Function.Injective (fderiv ℝ G u)) ∧
        ∃ κ : ℝ, 0 < κ ∧ ∀ u ∈ ball (v : Rn n) δ, ∀ w ∈ ball (v : Rn n) δ,
          κ * ‖u - w‖ ≤ ‖G u - G w‖ :=
      fun v => ballLemma G v hG v.2
    choose δ δpos hinj κ κpos hκ using hball
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun v : O => ball (v : Rn n) (δ v)) (fun v => isOpen_ball)
    have hOcov : ∀ v, v ∉ Crit → v ∈ ⋃ i ∈ T, ball (i : Rn n) (δ i) := by
      intro v hv
      have : v ∈ ⋃ i : O, ball (i : Rn n) (δ i) :=
        mem_iUnion.mpr ⟨⟨v, not_not.mp hv⟩, mem_ball_self (δpos _)⟩
      rwa [← hTU] at this
    rcases T.eq_empty_or_nonempty with hT | hT
    · refine ⟨G '' Crit, fun _ => 0, fun _ => 0, hcrit, ?_, ?_, ?_⟩
      · intro m v hv; simp at hv
      · intro m; exact ⟨1, one_pos, fun v hv => by simp at hv⟩
      · rintro _ ⟨v, rfl⟩
        left
        refine ⟨v, ?_, rfl⟩
        by_contra hv
        have := hOcov v hv
        rw [hT] at this
        simp at this
    · obtain ⟨e, he⟩ := hTc.exists_eq_range hT
      refine ⟨G '' Crit, fun m => (e m : Rn n), fun m => δ (e m), hcrit, fun m => hinj (e m),
        fun m => ⟨κ (e m), κpos (e m), hκ (e m)⟩, ?_⟩
      rintro _ ⟨v, rfl⟩
      by_cases hv : v ∈ Crit
      · exact Or.inl ⟨v, hv, rfl⟩
      · right
        obtain ⟨i, hiT, hvi⟩ := mem_iUnion₂.mp (hOcov v hv)
        rw [he] at hiT
        obtain ⟨m, rfl⟩ := hiT
        exact mem_iUnion.mpr ⟨m, ⟨v, hvi, rfl⟩⟩
  -- Parent steps 2-3: Lipschitz ranges are covered by C¹ ranges up to a null set.
  have lipCover : ∀ (F : Rn n → Amb n ℓ) (K : ℝ≥0), LipschitzWith K F →
      ∃ (N₀ : Set (Amb n ℓ)) (G : ℕ → Rn n → Amb n ℓ), (μHE[n] : Measure (Amb n ℓ)) N₀ = 0 ∧
        (∀ i, ContDiff ℝ 1 (G i)) ∧ range F ⊆ N₀ ∪ ⋃ i, range (G i) := by
    intro F K hF
    classical
    have hcoord : ∀ q : Fin (n + ℓ), LipschitzWith K (fun x => F x q) := by
      intro q
      have h1 : LipschitzWith 1 (fun y : Amb n ℓ => y q) := by
        refine LipschitzWith.of_dist_le_mul fun y z => ?_
        rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
        simpa using PiLp.norm_apply_le (y - z) q
      have h2 := h1.comp hF
      rw [one_mul] at h2
      exact h2
    set N : ℕ := n + ℓ with hN
    have hpos : ∀ i : ℕ, (0 : ℝ) < 1 / (((i : ℝ) + 1) * ((N : ℝ) + 1)) := by
      intro i; positivity
    choose g hg hgvol using fun (i : ℕ) (q : Fin (n + ℓ)) =>
      happrox (fun x => F x q) K (hcoord q) _ (hpos i)
    let G : ℕ → Rn n → Amb n ℓ := fun i x => WithLp.toLp 2 (fun q => g i q x)
    have hGc : ∀ i, ContDiff ℝ 1 (G i) := by
      intro i
      rw [contDiff_piLp]
      intro q
      simpa [G] using hg i q
    have hsub : ∀ i, {x | F x ≠ G i x} ⊆ ⋃ q, {x | F x q ≠ g i q x} := by
      intro i x hx
      by_contra h
      simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at h
      apply hx
      ext q
      simp [G, h q]
    have hvol : ∀ i : ℕ, volume {x | F x ≠ G i x} ≤ ENNReal.ofReal (1 / ((i : ℝ) + 1)) := by
      intro i
      calc volume {x | F x ≠ G i x} ≤ volume (⋃ q, {x | F x q ≠ g i q x}) := measure_mono (hsub i)
        _ ≤ ∑ q, volume {x | F x q ≠ g i q x} := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _q : Fin (n + ℓ), ENNReal.ofReal (1 / (((i : ℝ) + 1) * ((N : ℝ) + 1))) :=
            Finset.sum_le_sum fun q _ => (hgvol i q).le
        _ = ENNReal.ofReal ((N : ℝ) * (1 / (((i : ℝ) + 1) * ((N : ℝ) + 1)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (1 / ((i : ℝ) + 1)) := by
            apply ENNReal.ofReal_le_ofReal
            have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
            have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
            rw [mul_one_div, div_le_div_iff₀ (mul_pos hi hN1) hi, one_mul, mul_comm ((i : ℝ) + 1)]
            exact mul_le_mul_of_nonneg_right (by linarith) hi.le
    set Z : Set (Rn n) := ⋂ i, {x | F x ≠ G i x} with hZdef
    have hZ : volume Z = 0 := by
      apply le_antisymm _ bot_le
      have hlim : Tendsto (fun i : ℕ => ENNReal.ofReal (1 / ((i : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact ge_of_tendsto' hlim fun i => (measure_mono (iInter_subset _ i)).trans (hvol i)
    have hFZ : (μHE[n] : Measure (Amb n ℓ)) (F '' Z) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hF.lipschitzOnWith (s := Z))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero] at h
      exact le_antisymm h bot_le
    refine ⟨F '' Z, G, hFZ, hGc, ?_⟩
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ Z
    · exact Or.inl ⟨x, hx, rfl⟩
    · right
      simp only [hZdef, mem_iInter, mem_ofPred_eq, not_forall, not_not] at hx
      obtain ⟨i, hi⟩ := hx
      exact mem_iUnion.mpr ⟨i, x, hi.symm⟩
  -- Parent steps 1 and 7: assembly.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  choose N₁ G₁ hN₁ hG₁ hF₁ using fun j => lipCover (F j) (K j) (hK j)
  choose N₂ c₂ ρ₂ hN₂ hinj₂ hκ₂ hG₂ using fun j i => rangeCover (G₁ j i) (hG₁ j i)
  let J : ℕ → ℕ := fun k => (Nat.unpair k).1
  let I : ℕ → ℕ := fun k => (Nat.unpair (Nat.unpair k).2).1
  let Mi : ℕ → ℕ := fun k => (Nat.unpair (Nat.unpair k).2).2
  refine ⟨M₀ ∪ (⋃ j, N₁ j) ∪ ⋃ j, ⋃ i, N₂ j i, fun k => G₁ (J k) (I k),
    fun k => c₂ (J k) (I k) (Mi k), fun k => ρ₂ (J k) (I k) (Mi k), ?_, ?_, ?_, ?_, ?_⟩
  · refine measure_union_null (measure_union_null hM₀ (measure_iUnion_null hN₁)) ?_
    exact measure_iUnion_null fun j => measure_iUnion_null fun i => hN₂ j i
  · exact fun k => hG₁ (J k) (I k)
  · exact fun k => hinj₂ (J k) (I k) (Mi k)
  · exact fun k => hκ₂ (J k) (I k) (Mi k)
  · intro x hx
    rcases hcover hx with h0 | hx
    · exact Or.inl (Or.inl (Or.inl h0))
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    rcases hF₁ j hj with h1 | hx
    · exact Or.inl (Or.inl (Or.inr (mem_iUnion.mpr ⟨j, h1⟩)))
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hG₂ j i hi with h2 | hx
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨i, h2⟩⟩))
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    refine Or.inr (mem_iUnion.mpr ⟨Nat.pair j (Nat.pair i m), ?_⟩)
    simpa [J, I, Mi, Nat.unpair_pair] using hm
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

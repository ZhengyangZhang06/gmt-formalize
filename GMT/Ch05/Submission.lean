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

/-! ### Simon 2.6, (3)–(4): the good set is flat

Auxiliary facts for `lip_approx_good_set_flat`: the Hilbert–Schmidt inequalities
`|S − T|² ≤ 2|X − S|² + 2|X − T|²` and `|A v| ≤ |A| |v|`, `dist(v, T) = |v − p_T v|`, and the
comparison of two planes on a set of finite measure through their tilt integrals. -/

namespace LipApproxGoodSetFlat

/-- `|A|² ≥ 0`. -/
theorem hsNormSq_nonneg {m k : ℕ} (A : Rn m →L[ℝ] Rn k) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `|S − T|² ≤ 2|X − S|² + 2|X − T|²` (triangle inequality and `(a + b)² ≤ 2a² + 2b²`). -/
theorem hsNormSq_sub_le {m k : ℕ} (X S T : Rn m →L[ℝ] Rn k) :
    hsNormSq (S - T) ≤ 2 * hsNormSq (X - S) + 2 * hsNormSq (X - T) := by
  unfold hsNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set e : Rn m := EuclideanSpace.single i 1
  have h1 : ‖(S - T) e‖ ≤ ‖(X - T) e‖ + ‖(X - S) e‖ := by
    have h : (S - T) e = (X - T) e - (X - S) e := by
      simp only [sub_apply]
      abel
    rw [h]
    exact norm_sub_le _ _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖(X - T) e‖ - ‖(X - S) e‖)]

/-- The operator norm is dominated by the Hilbert–Schmidt norm: `|A v| ≤ |A| |v|`
(expand `v` in the standard basis and apply Cauchy–Schwarz). -/
theorem norm_apply_le_hsNorm {m k : ℕ} (A : Rn m →L[ℝ] Rn k) (v : Rn m) :
    ‖A v‖ ≤ hsNorm A * ‖v‖ := by
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v]
    simp
  have hAv : A v = ∑ i, v i • A (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul]
  have hS0 : 0 ≤ ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖ := by
    rw [hAv]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : (∑ i, |v i| * ‖A (EuclideanSpace.single i 1)‖) ^ 2 ≤
      (∑ i, |v i| ^ 2) * ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => sq_abs _
  rw [h3] at h2
  have hb : 0 ≤ hsNorm A * ‖v‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hA2 : hsNorm A ^ 2 = hsNormSq A := Real.sq_sqrt (hsNormSq_nonneg A)
  refine h1.trans ((sq_le_sq₀ hS0 hb).1 ?_)
  rw [mul_pow, hA2]
  calc _ ≤ ‖v‖ ^ 2 * ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 := h2
    _ = hsNormSq A * ‖v‖ ^ 2 := by unfold hsNormSq; ring

/-- `dist(v, T) = |v − p_T v|`. -/
theorem infDist_eq_norm_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : Submodule ℝ E) [T.HasOrthogonalProjection] (v : E) :
    infDist v (T : Set E) = ‖v - T.starProjection v‖ := by
  rw [← T.dist_starProjection_eq_infDist v, dist_eq_norm]

/-- `a ≤ c b²` with `b ≥ 0` gives `√a ≤ √c · b`. -/
theorem sqrt_le_sqrt_mul_of_le {a b c : ℝ} (hb : 0 ≤ b) (h : a ≤ c * b ^ 2) :
    Real.sqrt a ≤ Real.sqrt c * b := by
  calc Real.sqrt a ≤ Real.sqrt (c * b ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt c * b := by rw [Real.sqrt_mul' c (sq_nonneg b), Real.sqrt_sq hb]

/-- Comparison of two planes on a set `B` of finite measure: integrate
`|S − T|² ≤ 2|f(x) − S|² + 2|f(x) − T|²` over `B`. -/
theorem hsNormSq_mul_measureReal_le {α : Type*} [MeasurableSpace α] {m k : ℕ}
    {μ : Measure α} {B : Set α} (hB : MeasurableSet B) (hμB : μ B ≠ ∞)
    (f : α → (Rn m →L[ℝ] Rn k)) (S T : Rn m →L[ℝ] Rn k)
    (hS : IntegrableOn (fun x => hsNormSq (f x - S)) B μ)
    (hT : IntegrableOn (fun x => hsNormSq (f x - T)) B μ) :
    hsNormSq (S - T) * μ.real B ≤
      2 * ∫ x in B, hsNormSq (f x - S) ∂μ + 2 * ∫ x in B, hsNormSq (f x - T) ∂μ := by
  have hS2 : IntegrableOn (fun x => 2 * hsNormSq (f x - S)) B μ := Integrable.const_mul hS 2
  have hT2 : IntegrableOn (fun x => 2 * hsNormSq (f x - T)) B μ := Integrable.const_mul hT 2
  have h : hsNormSq (S - T) * μ.real B ≤
      ∫ x in B, (2 * hsNormSq (f x - S) + 2 * hsNormSq (f x - T)) ∂μ :=
    setIntegral_ge_of_const_le_real hB hμB (fun x _ => hsNormSq_sub_le (f x) S T)
      (hS2.add hT2)
  rwa [integral_add hS2 hT2, integral_const_mul, integral_const_mul] at h

end LipApproxGoodSetFlat

/-- **Simon Ch. 5, proof of Lemma 2.6, (3)–(4)**, with `T₀ = q(ℝⁿ × {0})`, `P = p_{T₀}` and
`σ₀ = δρ`.  If `∫_{B_{σ₀}(0)} |p_{T_x M} − P|² dμ_V ≤ β²L²σ₀ⁿ`, then
(1) `dist(x, T₀) ≤ C₀βLσ₀` on `spt V ∩ B_{2σ₀}(0)`, and
(2) `|(y₂ − y₁) − P(y₂ − y₁)| ≤ C₀βL|y₂ − y₁|` whenever `y₁, y₂ ∈ spt V ∩ B_{3σ₀/4}(0)` and `y₁` is
good (`∫_{B_{s/2}(y₁)} |p_{T_x M} − P|² ≤ β²L²sⁿ` for `s ∈ (0, σ₀/2]`).

Write `D = δ^{1/(2n+2)} ≤ βL`.  Lemma 2.5 at `(ξ, σ)` gives a plane `T` with height
`≤ C D σ` on `spt V ∩ B_σ(ξ)` and tilt `∫_{B_{σ/2}(ξ)} |p_{T_x M} − p_T|² ≤ C²(C + 1)²D²σⁿ`
(its `H`-term is `≤ δ ≤ D`).  Comparing that plane with `T₀` on a ball whose mass is bounded below
by the pinched density (`lip_approx_pinched_density`; tilt integrability is
`lip_approx_tangent_structure`) shows `|p_T − P| ≤ C'βL`; the plane `T*` at `(0, 2σ₀)` gives (1),
the plane at `(y₁, |y₂ − y₁|)` gives (2) for `|y₂ − y₁| ≤ σ₀/2`, and longer pairs follow
from (1). -/
theorem lip_approx_good_set_flat : AffineApproximationLemma → ∀ (n ℓ : ℕ), 1 ≤ n →
    ∀ p : ℝ, (n : ℝ) < p → ∃ C₀ δ₀ : ℝ, 0 < C₀ ∧ 0 < δ₀ ∧ ∀ β L : ℝ, 0 < β → 0 < L → L ≤ 1 →
    ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ)
    (δ ρ : ℝ), 0 < δ → δ ≤ δ₀ → δ ≤ (β * L) ^ (2 * n + 2) → V.AllardHypotheses H p δ ρ →
    ∀ q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ, ∫ x in closedBall 0 (δ * ρ),
      hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤
        β ^ 2 * L ^ 2 * (δ * ρ) ^ n →
    (∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      infDist x (rotatedPlane q : Set (Amb n ℓ)) ≤ C₀ * β * L * (δ * ρ)) ∧
    ∀ y₁ ∈ V.support ∩ closedBall 0 (3 * (δ * ρ) / 4),
    ∀ y₂ ∈ V.support ∩ closedBall 0 (3 * (δ * ρ) / 4),
      (∀ s : ℝ, 0 < s → s ≤ δ * ρ / 2 → ∫ x in closedBall y₁ (s / 2),
        hsNormSq (V.tangentProj x - (rotatedPlane q).starProjection) ∂V.weight ≤
          β ^ 2 * L ^ 2 * s ^ n) →
      ‖(y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁)‖ ≤ C₀ * β * L * ‖y₂ - y₁‖ := by
  intro hAAL n ℓ hn p hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  obtain ⟨C, hC, hAA⟩ := hAAL n ℓ hn p hp
  obtain ⟨δP, hδP, -, hPD⟩ := Submission.lip_approx_pinched_density n ℓ hn p hp
  -- The constants of the natural-language proof.  Its normalisation `C_A = max{C, 1}` is not
  -- needed: every step below only uses `C > 0`, so we take `C_A = C`.
  obtain ⟨C₁, hC₁_def⟩ : ∃ C₁ : ℝ, C₁ = 2 ^ n * C ^ 2 * (C + 1) ^ 2 := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂_def⟩ : ∃ C₂ : ℝ, C₂ = Real.sqrt (4 * (1 + C₁) / unitBallVolume n) := ⟨_, rfl⟩
  obtain ⟨C₃, hC₃_def⟩ : ∃ C₃ : ℝ, C₃ = 2 * C + 2 * C₂ := ⟨_, rfl⟩
  obtain ⟨C₅, hC₅_def⟩ : ∃ C₅ : ℝ,
      C₅ = Real.sqrt (2 ^ (n + 2) * (1 + C₁) / unitBallVolume n) := ⟨_, rfl⟩
  obtain ⟨C₆, hC₆_def⟩ : ∃ C₆ : ℝ, C₆ = C + C₅ := ⟨_, rfl⟩
  have hC₁ : 0 ≤ C₁ := by rw [hC₁_def]; positivity
  have hC₂ : 0 ≤ C₂ := by rw [hC₂_def]; exact Real.sqrt_nonneg _
  have hC₃ : 0 < C₃ := by rw [hC₃_def]; positivity
  have hC₅ : 0 ≤ C₅ := by rw [hC₅_def]; exact Real.sqrt_nonneg _
  have hC₆ : 0 < C₆ := by rw [hC₆_def]; positivity
  refine ⟨max C₆ (4 * C₃), min (1 / 4) δP, lt_max_of_lt_left hC₆, lt_min (by norm_num) hδP, ?_⟩
  intro β L hβ hL _ U hU V H δ ρ hδ hδ₀ hδβL hA q htilt
  have hδ4 : δ ≤ 1 / 4 := hδ₀.trans (min_le_left _ _)
  have hδδP : δ ≤ δP := hδ₀.trans (min_le_right _ _)
  have hA' := hA
  obtain ⟨hρ, -, -, h0, hBU, -, hK⟩ := hA'
  have hσ₀ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ4 : δ * ρ ≤ ρ / 4 := by nlinarith
  have hβL : 0 < β * L := mul_pos hβ hL
  -- Step 1(a): `D = δ^{1/(2n+2)}` satisfies `δ ≤ D ≤ βL`.
  obtain ⟨D, hD_def⟩ : ∃ D : ℝ, D = δ ^ (1 / (2 * (n : ℝ) + 2)) := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hD_def]; exact Real.rpow_pos_of_pos hδ _
  have hDβL : D ≤ β * L := by
    have hk : (((2 * n + 2 : ℕ) : ℝ))⁻¹ = 1 / (2 * (n : ℝ) + 2) := by push_cast; ring
    calc D = δ ^ (((2 * n + 2 : ℕ) : ℝ))⁻¹ := by rw [hD_def, hk]
      _ ≤ ((β * L) ^ (2 * n + 2)) ^ (((2 * n + 2 : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow hδ.le hδβL (by positivity)
      _ = β * L := Real.pow_rpow_inv_natCast hβL.le (by omega)
  have hδD : δ ≤ D := by
    have hα1 : 1 / (2 * (n : ℝ) + 2) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ (1 / (2 * (n : ℝ) + 2)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ (by linarith) hα1
      _ = D := hD_def.symm
  -- Step 1(b): `K(z, t) ≤ δ` whenever `B_t(z) ⊆ B_ρ(0)`.
  have hKball : ∀ (z : Amb n ℓ) (t : ℝ), 0 < t → t ≤ ρ → closedBall z t ⊆ closedBall 0 ρ →
      V.scaledLpNorm H p z t ≤ ENNReal.ofReal δ := by
    intro z t ht htρ hsub
    have hp0 : 0 < p := lt_of_le_of_lt hn0 hp
    refine le_trans ?_ hK
    unfold RectifiableVarifold.scaledLpNorm
    refine ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
      (lintegral_mono_set hsub)) (by positivity)
    exact Real.rpow_le_rpow ht.le htρ (sub_pos.2 hp).le
  have hball : ∀ (z : Amb n ℓ) (t : ℝ), t + ‖z‖ ≤ ρ → closedBall z t ⊆ closedBall 0 ρ :=
    fun z t h => closedBall_subset_closedBall' (by rwa [dist_zero_right])
  -- Step 1(f): tilt integrands are integrable on closed balls inside `B_ρ(0)`.
  have hint : ∀ (T : Submodule ℝ (Amb n ℓ)) (z : Amb n ℓ) (t : ℝ),
      closedBall z t ⊆ closedBall 0 ρ →
      IntegrableOn (fun x => hsNormSq (V.tangentProj x - T.starProjection)) (closedBall z t)
        V.weight :=
    fun T z t hsub => (Submission.lip_approx_tangent_structure n ℓ hn U hU V).2.1 T _
      (isCompact_closedBall z t) (hsub.trans hBU)
  -- Step 1(g): the output of the affine approximation lemma at `(ξ, σ)`.
  have hAff : ∀ ξ ∈ V.support ∩ closedBall 0 (δ * ρ), ∀ σ : ℝ, 0 < σ → σ ≤ 2 * δ * ρ →
      ∃ T : Submodule ℝ (Amb n ℓ),
        (∀ x ∈ V.support ∩ closedBall ξ σ, infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ C * D * σ) ∧
        ∫ x in closedBall ξ (σ / 2), hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight ≤
          C ^ 2 * (C + 1) ^ 2 * D ^ 2 * σ ^ n := by
    intro ξ hξ σ hσ hσ2
    obtain ⟨T, -, h1, h2⟩ := hAA U hU V H δ ρ hδ hδ4 hA ξ hξ σ hσ hσ2
    rw [← hD_def] at h2
    refine ⟨T, fun x hx => ?_, ?_⟩
    · have hx' : ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ))) ≤ V.heightSup ξ σ T :=
        le_iSup₂ (f := fun y (_ : y ∈ V.support ∩ closedBall ξ σ) =>
          ENNReal.ofReal (infDist (y - ξ) (T : Set (Amb n ℓ)))) x hx
      have h3 : ENNReal.ofReal (σ⁻¹ * infDist (x - ξ) (T : Set (Amb n ℓ))) ≤
          ENNReal.ofReal (C * D) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.2 hσ.le)]
        calc ENNReal.ofReal σ⁻¹ * ENNReal.ofReal (infDist (x - ξ) (T : Set (Amb n ℓ))) ≤
              ENNReal.ofReal σ⁻¹ * V.heightSup ξ σ T := by gcongr
          _ ≤ ENNReal.ofReal (C * D) := h2
      have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
      rw [inv_mul_le_iff₀ hσ] at h4
      calc infDist (x - ξ) (T : Set (Amb n ℓ)) ≤ σ * (C * D) := h4
        _ = C * D * σ := by ring
    · have hξn : ‖ξ‖ ≤ δ * ρ := mem_closedBall_zero_iff.1 hξ.2
      have hK' := hKball ξ σ hσ (by linarith) (hball ξ σ (by linarith))
      have h3 : ENNReal.ofReal (C⁻¹ * Real.sqrt ((σ ^ n)⁻¹ * ∫ x in closedBall ξ (σ / 2),
          hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight)) ≤
            ENNReal.ofReal (C * D + δ) := by
        rw [ENNReal.ofReal_add (by positivity) hδ.le]
        exact h1.trans (add_le_add h2 hK')
      have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
      rw [inv_mul_le_iff₀ hC] at h4
      have hI0 : 0 ≤ ∫ x in closedBall ξ (σ / 2),
          hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight :=
        integral_nonneg fun x => LipApproxGoodSetFlat.hsNormSq_nonneg _
      generalize (∫ x in closedBall ξ (σ / 2),
        hsNormSq (V.tangentProj x - T.starProjection) ∂V.weight) = I at hI0 h4 ⊢
      have h5 : Real.sqrt ((σ ^ n)⁻¹ * I) ≤ C * (C + 1) * D :=
        calc Real.sqrt ((σ ^ n)⁻¹ * I) ≤ C * (C * D + δ) := h4
          _ ≤ C * (C * D + D) := by gcongr
          _ = C * (C + 1) * D := by ring
      have h6 := (Real.sqrt_le_left (by positivity)).1 h5
      rw [inv_mul_le_iff₀ (pow_pos hσ n)] at h6
      calc I ≤ σ ^ n * (C * (C + 1) * D) ^ 2 := h6
        _ = C ^ 2 * (C + 1) ^ 2 * D ^ 2 * σ ^ n := by ring
  -- Step 2: the plane `T*` of Lemma 2.5 at `(0, 2σ₀)` is `C₂βL`-close to `T₀`.
  obtain ⟨Ts, hTs_height, hTs_tilt⟩ := hAff 0 ⟨h0, mem_closedBall_self hσ₀.le⟩
    (2 * (δ * ρ)) (by positivity) (le_of_eq (by ring))
  rw [show 2 * (δ * ρ) / 2 = δ * ρ by ring] at hTs_tilt
  have hsub0 : closedBall (0 : Amb n ℓ) (δ * ρ) ⊆ closedBall 0 ρ :=
    closedBall_subset_closedBall (by linarith)
  obtain ⟨hup0, hlow0⟩ := hPD U hU V H δ ρ hδ hδδP hA 0 (by rw [norm_zero]; positivity)
    (δ * ρ) hσ₀ (by linarith)
  have hne0 : V.weight (closedBall 0 (δ * ρ)) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup0
  have hmeas0 : unitBallVolume n * (δ * ρ) ^ n / 2 ≤ V.weight.real (closedBall 0 (δ * ρ)) := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal hne0).1 (hlow0 h0)
  have hTs_hs : hsNormSq (Ts.starProjection - (rotatedPlane q).starProjection) ≤
      4 * (1 + C₁) / unitBallVolume n * (β * L) ^ 2 := by
    have hI : ∫ x in closedBall 0 (δ * ρ),
        hsNormSq (V.tangentProj x - Ts.starProjection) ∂V.weight ≤
          C₁ * (β * L) ^ 2 * (δ * ρ) ^ n :=
      calc _ ≤ C ^ 2 * (C + 1) ^ 2 * D ^ 2 * (2 * (δ * ρ)) ^ n := hTs_tilt
        _ = C₁ * D ^ 2 * (δ * ρ) ^ n := by rw [hC₁_def, mul_pow]; ring
        _ ≤ C₁ * (β * L) ^ 2 * (δ * ρ) ^ n := by gcongr
    have hm : 0 < unitBallVolume n * (δ * ρ) ^ n / 2 := by positivity
    have key : hsNormSq (Ts.starProjection - (rotatedPlane q).starProjection) *
        (unitBallVolume n * (δ * ρ) ^ n / 2) ≤ 2 * (1 + C₁) * (β * L) ^ 2 * (δ * ρ) ^ n :=
      calc _ ≤ hsNormSq (Ts.starProjection - (rotatedPlane q).starProjection) *
            V.weight.real (closedBall 0 (δ * ρ)) :=
          mul_le_mul_of_nonneg_left hmeas0 (LipApproxGoodSetFlat.hsNormSq_nonneg _)
        _ ≤ _ := LipApproxGoodSetFlat.hsNormSq_mul_measureReal_le measurableSet_closedBall hne0
            V.tangentProj Ts.starProjection (rotatedPlane q).starProjection
            (hint Ts 0 (δ * ρ) hsub0) (hint (rotatedPlane q) 0 (δ * ρ) hsub0)
        _ ≤ 2 * (C₁ * (β * L) ^ 2 * (δ * ρ) ^ n) + 2 * (β ^ 2 * L ^ 2 * (δ * ρ) ^ n) := by
          gcongr
        _ = 2 * (1 + C₁) * (β * L) ^ 2 * (δ * ρ) ^ n := by ring
    rw [← le_div_iff₀ hm] at key
    calc _ ≤ _ := key
      _ = 4 * (1 + C₁) / unitBallVolume n * (β * L) ^ 2 := by
        field_simp
        ring
  have hTs_norm : hsNorm (Ts.starProjection - (rotatedPlane q).starProjection) ≤ C₂ * (β * L) := by
    rw [hC₂_def, hsNorm]
    exact LipApproxGoodSetFlat.sqrt_le_sqrt_mul_of_le hβL.le hTs_hs
  -- The height bound relative to `T₀`.
  have hstep2 : ∀ x ∈ V.support ∩ closedBall 0 (2 * (δ * ρ)),
      ‖x - (rotatedPlane q).starProjection x‖ ≤ C₃ * (β * L) * (δ * ρ) := by
    intro x hx
    have hxn : ‖x‖ ≤ 2 * (δ * ρ) := mem_closedBall_zero_iff.1 hx.2
    have h1 : ‖x - Ts.starProjection x‖ ≤ C * D * (2 * (δ * ρ)) := by
      have := hTs_height x hx
      rwa [sub_zero, LipApproxGoodSetFlat.infDist_eq_norm_sub_starProjection] at this
    have h2 : ‖(Ts.starProjection - (rotatedPlane q).starProjection) x‖ ≤
        C₂ * (β * L) * (2 * (δ * ρ)) :=
      (LipApproxGoodSetFlat.norm_apply_le_hsNorm _ _).trans
        (mul_le_mul hTs_norm hxn (norm_nonneg _) (mul_nonneg hC₂ hβL.le))
    have hdecomp : x - (rotatedPlane q).starProjection x =
        (x - Ts.starProjection x) + (Ts.starProjection - (rotatedPlane q).starProjection) x := by
      rw [sub_apply]
      abel
    calc ‖x - (rotatedPlane q).starProjection x‖ ≤
          ‖x - Ts.starProjection x‖ +
            ‖(Ts.starProjection - (rotatedPlane q).starProjection) x‖ := by
          rw [hdecomp]
          exact norm_add_le _ _
      _ ≤ C * D * (2 * (δ * ρ)) + C₂ * (β * L) * (2 * (δ * ρ)) := add_le_add h1 h2
      _ ≤ C * (β * L) * (2 * (δ * ρ)) + C₂ * (β * L) * (2 * (δ * ρ)) := by gcongr
      _ = C₃ * (β * L) * (δ * ρ) := by rw [hC₃_def]; ring
  refine ⟨fun x hx => ?_, ?_⟩
  · -- Conclusion (1).
    rw [LipApproxGoodSetFlat.infDist_eq_norm_sub_starProjection]
    calc ‖x - (rotatedPlane q).starProjection x‖ ≤ C₃ * (β * L) * (δ * ρ) := hstep2 x hx
      _ ≤ max C₆ (4 * C₃) * (β * L) * (δ * ρ) := by
          gcongr
          exact le_max_of_le_right (by linarith)
      _ = max C₆ (4 * C₃) * β * L * (δ * ρ) := by ring
  -- Step 3: conclusion (2).
  intro y₁ hy₁ y₂ hy₂ hgood
  have hy₁n : ‖y₁‖ ≤ 3 * (δ * ρ) / 4 := mem_closedBall_zero_iff.1 hy₁.2
  have hy₂n : ‖y₂‖ ≤ 3 * (δ * ρ) / 4 := mem_closedBall_zero_iff.1 hy₂.2
  rcases le_or_gt ‖y₂ - y₁‖ (δ * ρ / 2) with hs | hs
  · rcases (norm_nonneg (y₂ - y₁)).eq_or_lt with hs0 | hs0
    · -- `y₁ = y₂`: both sides vanish.
      rw [norm_eq_zero.1 hs0.symm]
      simp
    -- Step 3(a): short pairs, `0 < s = |y₂ − y₁| ≤ σ₀/2`; the plane `T₁` at `(y₁, s)`.
    set s := ‖y₂ - y₁‖
    obtain ⟨T₁, hT₁_height, hT₁_tilt⟩ :=
      hAff y₁ ⟨hy₁.1, mem_closedBall_zero_iff.2 (by linarith)⟩ s hs0 (by linarith)
    have h1 : ‖(y₂ - y₁) - T₁.starProjection (y₂ - y₁)‖ ≤ C * D * s := by
      have := hT₁_height y₂ ⟨hy₂.1, by rw [mem_closedBall, dist_eq_norm]⟩
      rwa [LipApproxGoodSetFlat.infDist_eq_norm_sub_starProjection] at this
    have hsub1 : closedBall y₁ (s / 2) ⊆ closedBall 0 ρ := hball y₁ (s / 2) (by linarith)
    obtain ⟨hup1, hlow1⟩ := hPD U hU V H δ ρ hδ hδδP hA y₁ (by linarith) (s / 2)
      (by positivity) (by linarith)
    have hne1 : V.weight (closedBall y₁ (s / 2)) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup1
    have hmeas1 : unitBallVolume n * (s / 2) ^ n / 2 ≤ V.weight.real (closedBall y₁ (s / 2)) := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal hne1).1 (hlow1 hy₁.1)
    have hT₁_hs : hsNormSq (T₁.starProjection - (rotatedPlane q).starProjection) ≤
        2 ^ (n + 2) * (1 + C₁) / unitBallVolume n * (β * L) ^ 2 := by
      have hI : ∫ x in closedBall y₁ (s / 2),
          hsNormSq (V.tangentProj x - T₁.starProjection) ∂V.weight ≤
            C₁ * (β * L) ^ 2 * s ^ n :=
        calc _ ≤ C ^ 2 * (C + 1) ^ 2 * D ^ 2 * s ^ n := hT₁_tilt
          _ ≤ C ^ 2 * (C + 1) ^ 2 * (β * L) ^ 2 * s ^ n := by gcongr
          _ ≤ 2 ^ n * (C ^ 2 * (C + 1) ^ 2 * (β * L) ^ 2 * s ^ n) :=
            le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
          _ = C₁ * (β * L) ^ 2 * s ^ n := by rw [hC₁_def]; ring
      have hm : 0 < unitBallVolume n * (s / 2) ^ n / 2 := by positivity
      have key : hsNormSq (T₁.starProjection - (rotatedPlane q).starProjection) *
          (unitBallVolume n * (s / 2) ^ n / 2) ≤ 2 * (1 + C₁) * (β * L) ^ 2 * s ^ n :=
        calc _ ≤ hsNormSq (T₁.starProjection - (rotatedPlane q).starProjection) *
              V.weight.real (closedBall y₁ (s / 2)) :=
            mul_le_mul_of_nonneg_left hmeas1 (LipApproxGoodSetFlat.hsNormSq_nonneg _)
          _ ≤ _ := LipApproxGoodSetFlat.hsNormSq_mul_measureReal_le measurableSet_closedBall hne1
              V.tangentProj T₁.starProjection (rotatedPlane q).starProjection
              (hint T₁ y₁ (s / 2) hsub1) (hint (rotatedPlane q) y₁ (s / 2) hsub1)
          _ ≤ 2 * (C₁ * (β * L) ^ 2 * s ^ n) + 2 * (β ^ 2 * L ^ 2 * s ^ n) := by
            gcongr
            exact hgood s hs0 hs
          _ = 2 * (1 + C₁) * (β * L) ^ 2 * s ^ n := by ring
      rw [← le_div_iff₀ hm] at key
      calc _ ≤ _ := key
        _ = 2 ^ (n + 2) * (1 + C₁) / unitBallVolume n * (β * L) ^ 2 := by
          rw [div_pow]
          field_simp
          ring
    have hT₁_norm : hsNorm (T₁.starProjection - (rotatedPlane q).starProjection) ≤
        C₅ * (β * L) := by
      rw [hC₅_def, hsNorm]
      exact LipApproxGoodSetFlat.sqrt_le_sqrt_mul_of_le hβL.le hT₁_hs
    have h2 : ‖(T₁.starProjection - (rotatedPlane q).starProjection) (y₂ - y₁)‖ ≤
        C₅ * (β * L) * s :=
      (LipApproxGoodSetFlat.norm_apply_le_hsNorm _ _).trans
        (mul_le_mul_of_nonneg_right hT₁_norm (norm_nonneg _))
    have hdecomp : (y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁) =
        ((y₂ - y₁) - T₁.starProjection (y₂ - y₁)) +
          (T₁.starProjection - (rotatedPlane q).starProjection) (y₂ - y₁) := by
      rw [sub_apply]
      abel
    calc ‖(y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁)‖ ≤
          ‖(y₂ - y₁) - T₁.starProjection (y₂ - y₁)‖ +
            ‖(T₁.starProjection - (rotatedPlane q).starProjection) (y₂ - y₁)‖ := by
          rw [hdecomp]
          exact norm_add_le _ _
      _ ≤ C * D * s + C₅ * (β * L) * s := add_le_add h1 h2
      _ ≤ C * (β * L) * s + C₅ * (β * L) * s := by gcongr
      _ = C₆ * β * L * s := by rw [hC₆_def]; ring
      _ ≤ max C₆ (4 * C₃) * β * L * s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hβ.le) hL.le) (norm_nonneg _)
  · -- Step 3(b): long pairs, `|y₂ − y₁| > σ₀/2`; add the two height bounds of step 2.
    have h1 := hstep2 y₁ ⟨hy₁.1, mem_closedBall_zero_iff.2 (by linarith)⟩
    have h2 := hstep2 y₂ ⟨hy₂.1, mem_closedBall_zero_iff.2 (by linarith)⟩
    have hdecomp : (y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁) =
        (y₂ - (rotatedPlane q).starProjection y₂) - (y₁ - (rotatedPlane q).starProjection y₁) := by
      rw [map_sub]
      abel
    calc ‖(y₂ - y₁) - (rotatedPlane q).starProjection (y₂ - y₁)‖ ≤
          ‖y₂ - (rotatedPlane q).starProjection y₂‖ +
            ‖y₁ - (rotatedPlane q).starProjection y₁‖ := by
          rw [hdecomp]
          exact norm_sub_le _ _
      _ ≤ C₃ * (β * L) * (δ * ρ) + C₃ * (β * L) * (δ * ρ) := add_le_add h2 h1
      _ = 2 * (C₃ * (β * L)) * (δ * ρ) := by ring
      _ ≤ 2 * (C₃ * (β * L)) * (2 * ‖y₂ - y₁‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * C₃ * β * L * ‖y₂ - y₁‖ := by ring
      _ ≤ max C₆ (4 * C₃) * β * L * ‖y₂ - y₁‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hβ.le) hL.le) (norm_nonneg _)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

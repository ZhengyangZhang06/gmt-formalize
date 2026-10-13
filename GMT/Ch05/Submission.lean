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

/-- The linear algebra in the proof of Simon Ch. 5, Lemma 2.1 (p. 107): (i) the operator norm of a
linear map is at most its Hilbert–Schmidt norm `|A|`; (ii) `|p_{T⊥} v| = dist(v, T)`; and
(iii) display (2) of the proof, `trace(p_{T⊥} ∘ p_P) = ½ |p_P − p_T|²` when `dim P = dim T`. -/
theorem hsNorm_starProjection_trace_identities : (∀ (m k : ℕ) (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A) ∧ (∀ (m : ℕ) (T : Submodule ℝ (Rn m)) (v : Rn m), ‖Tᗮ.starProjection v‖ = Metric.infDist v (T : Set (Rn m))) ∧ ∀ (m : ℕ) (P T : Submodule ℝ (Rn m)), Module.finrank ℝ P = Module.finrank ℝ T → LinearMap.trace ℝ (Rn m) (Tᗮ.starProjection.toLinearMap ∘ₗ P.starProjection.toLinearMap) = hsNormSq (P.starProjection - T.starProjection) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `‖A v‖ ≤ Σᵢ |vᵢ| ‖A eᵢ‖ ≤ ‖v‖ |A|` by the triangle and Cauchy–Schwarz inequalities.
    intro m k A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  · -- (ii) `p_{T⊥} v = v − p_T v`, and `p_T v` is the point of `T` nearest to `v`.
    intro m T v
    rw [Submodule.starProjection_orthogonal_val, ← dist_eq_norm,
      Submodule.dist_starProjection_eq_infDist]
  · -- (iii) Compute both sides in the standard orthonormal basis `eᵢ`.
    intro m P T hPT
    -- The trace is the sum of the diagonal entries `⟪eᵢ, f eᵢ⟫`.
    have htr : ∀ f : Rn m →ₗ[ℝ] Rn m, LinearMap.trace ℝ (Rn m) f =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ)) (f (EuclideanSpace.single i 1)) := by
      intro f
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis f,
        Matrix.trace]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply]
    -- The trace of an orthogonal projection is the dimension of its range.
    have hproj : ∀ W : Submodule ℝ (Rn m),
        LinearMap.trace ℝ (Rn m) W.starProjection.toLinearMap = Module.finrank ℝ W := fun W =>
      LinearMap.IsProj.trace
        ⟨W.starProjection_apply_mem, fun _ hx => W.starProjection_eq_self_iff.2 hx⟩
    -- `‖p_W x‖² = ⟪x, p_W x⟫`, since `p_W` is self-adjoint and idempotent.
    have hsq : ∀ (W : Submodule ℝ (Rn m)) (x : Rn m),
        ‖W.starProjection x‖ ^ 2 = inner ℝ x (W.starProjection x) := by
      intro W x
      rw [← real_inner_self_eq_norm_sq, W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.2 (W.starProjection_apply_mem x)]
    -- Pointwise, `2 ⟪x, (I − q) p x⟫ = ‖(p − q) x‖² + ⟪x, p x⟫ − ⟪x, q x⟫`.
    have hterm : ∀ x : Rn m, 2 * inner ℝ x (Tᗮ.starProjection (P.starProjection x)) =
        ‖(P.starProjection - T.starProjection) x‖ ^ 2 + inner ℝ x (P.starProjection x) -
          inner ℝ x (T.starProjection x) := by
      intro x
      rw [Submodule.starProjection_orthogonal_val, sub_apply, norm_sub_sq_real, hsq P, hsq T,
        inner_sub_right, ← T.inner_starProjection_left_eq_right,
        real_inner_comm (T.starProjection x)]
      ring
    -- `trace p_P = dim P = dim T = trace p_T`.
    have hdim : ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (P.starProjection (EuclideanSpace.single i 1)) =
        ∑ i, inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (T.starProjection (EuclideanSpace.single i 1)) := by
      have h := hproj P
      rw [hPT, ← hproj T, htr, htr] at h
      exact h
    rw [htr, hsNormSq, eq_div_iff two_ne_zero, mul_comm, Finset.mul_sum]
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [Finset.sum_congr rfl fun i _ => hterm (EuclideanSpace.single i 1), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hdim, add_sub_cancel_right]
/-- Simon Ch. 5, Lemma 2.6 and its proof (pp. 110–111): graph coordinates on
`ℝ^{n+ℓ} = ℝⁿ × ℝ^ℓ` and the projection onto `T₀ = q(ℝⁿ × {0})`, the plane the book takes to be
`ℝⁿ × {0}` without loss of generality. For a linear isometry `q` of `ℝ^{n+ℓ}`:
(i) `(a, b) − (a', b') = (a − a', b − b')`; (ii) `|(a, b)|² = |a|² + |b|²`; (iii) every
`z ∈ ℝ^{n+ℓ}` is some `(a, b)`; (iv) `p_{T₀}(q(a, b)) = q(a, 0)`.
The coordinate of `(a, b)` at `castAdd ℓ i` is `a_i` and at `natAdd n j` is `b_j`, and every index
of `Fin (n + ℓ)` has one of these forms (`Fin.addCases`); this gives (i) and (iii), and (ii) by
splitting `Σ_k z_k²` with `Fin.sum_univ_add`. For (iv), `(a, 0) = Σ_i a_i e_{castAdd ℓ i}` lies in
`ℝⁿ × {0}`, `(0, b)` is orthogonal to every `e_{castAdd ℓ i}` and hence to `ℝⁿ × {0}`, and `q`
preserves inner products; so `q(a, 0) ∈ T₀` and `q(a, b) − q(a, 0) = q(0, b) ⊥ T₀`, which
characterizes `q(a, 0)` as the orthogonal projection of `q(a, b)` onto `T₀`. -/
theorem lip_approx_graph_coordinates : ∀ (n ℓ : ℕ) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), (∀ (a a' : Rn n) (b b' : Rn ℓ), graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b')) ∧ (∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2) ∧ (∀ z : Amb n ℓ, ∃ (a : Rn n) (b : Rn ℓ), z = graphPoint a b) ∧ (∀ (a : Rn n) (b : Rn ℓ), (rotatedPlane q).starProjection (q (graphPoint a b)) = q (graphPoint a 0)) := by
  intro n ℓ q
  -- the coordinates of `graphPoint a b`
  have hl : ∀ (a : Rn n) (b : Rn ℓ) (i : Fin n), graphPoint a b (Fin.castAdd ℓ i) = a i := by
    intro a b i
    simp [graphPoint]
  have hr : ∀ (a : Rn n) (b : Rn ℓ) (j : Fin ℓ), graphPoint a b (Fin.natAdd n j) = b j := by
    intro a b j
    simp [graphPoint]
  -- (i): subtraction is coordinatewise
  have hsub : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b') := by
    intro a a' b b'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [PiLp.sub_apply, hl]
    · simp only [PiLp.sub_apply, hr]
  refine ⟨hsub, ?_, ?_, ?_⟩
  -- (ii): split `‖z‖² = Σ_k ‖z_k‖²` over the two blocks of indices
  · intro a b
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp only [hl, hr]
  -- (iii): read off `a` and `b` from the two blocks of coordinates of `z`
  · intro z
    refine ⟨WithLp.toLp 2 (fun i => z (Fin.castAdd ℓ i)),
      WithLp.toLp 2 (fun j => z (Fin.natAdd n j)), ?_⟩
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · rw [hl]
    · rw [hr]
  -- (iv)
  · intro a b
    -- `graphPoint a 0 = Σ_i a_i e_{castAdd ℓ i}` lies in `ℝⁿ × {0}`
    have hmem : graphPoint a 0 ∈ horizontalPlane n ℓ := by
      have e : graphPoint a 0 =
          ∑ i : Fin n, a i • EuclideanSpace.single (Fin.castAdd ℓ i) (1 : ℝ) := by
        ext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · rw [hl]
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply,
            Pi.smul_apply, Pi.single_apply, Fin.castAdd_inj, smul_eq_mul, mul_ite, mul_one,
            mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        · rw [hr]
          simp only [PiLp.zero_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single,
            Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine (Finset.sum_eq_zero fun x _ => ?_).symm
          have hne : Fin.natAdd n j ≠ Fin.castAdd ℓ x := by
            intro h
            have h' := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
            have := x.isLt
            omega
          rw [Pi.single_eq_of_ne hne, mul_zero]
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `graphPoint 0 b` is orthogonal to every `e_{castAdd ℓ i}`, hence to `ℝⁿ × {0}`
    have horth : ∀ h ∈ horizontalPlane n ℓ, inner ℝ (graphPoint 0 b) h = 0 := by
      have hle : horizontalPlane n ℓ ≤ (ℝ ∙ graphPoint 0 b)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
          EuclideanSpace.inner_single_right, hl]
        simp
      intro h hh
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hh)
    -- `q(a, 0) ∈ T₀`, and `q(a, b) - q(a, 0) = q(0, b)` is orthogonal to `T₀ = q(ℝⁿ × {0})`
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.mem_map_of_mem hmem) ?_
    intro w hw
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hw
    rw [← map_sub, hsub, sub_self, sub_zero]
    exact (q.inner_map_map _ _).trans (horth h hh)
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the profile of the cutoff `ζ(x) = φ(|x − ξ|/ρ)` with
`ζ ≡ 1` in `B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B_ρ(ξ)` and `|∇ζ| ≤ 3/ρ`.  With `S = smoothTransition`,
the bump `g(t) = S(12(t − 1/2)) S(12(1 − t)) ∈ [0, 1]` vanishes for `t ≤ 1/2` and for `t ≥ 1` and
equals `1` on `[7/12, 11/12]`, so `c = ∫_{1/2}^1 g ≥ 1/3`; then `φ(t) = 1 − c⁻¹ ∫_{1/2}^t g` is
`C^∞` with `|φ'| = c⁻¹ g ≤ 3`. -/
theorem exists_smooth_step_profile_lipschitz_three : ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧ (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
  -- The bump `g`: smooth, with values in `[0, 1]`, zero off `(1/2, 1)`, one on `[7/12, 11/12]`.
  set g : ℝ → ℝ := fun t =>
    Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
    have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
    exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
  have hg_cont : Continuous g := hg_smooth.continuous
  have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hg_cont.intervalIntegrable a b
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
      (Real.smoothTransition.le_one _)
  have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
    simp only [hg_def]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
  have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
    simp only [hg_def]
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  -- The normalizing constant `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`.
  set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_def
  have hc_ge : 1 / 3 ≤ c := by
    have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
      · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        norm_num
      · intro s hs
        rw [uIcc_of_le (by norm_num)] at hs
        exact hg_mid s hs.1 hs.2
    rw [← h]
    exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
      (ae_of_all _ hg_nonneg) (hg_int _ _)
  have hc_pos : 0 < c := by linarith
  have hcinv_le : c⁻¹ ≤ 3 := by
    rw [inv_le_comm₀ hc_pos (by norm_num)]
    linarith
  -- The primitive `F(t) = ∫_{1/2}^t g`: `F' = g` (FTC), so `F` is smooth; `0 ≤ F ≤ c`,
  -- `F = 0` on `(-∞, 1/2]` and `F = c` on `[1, ∞)`.
  set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_def
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
    (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
      (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
  have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
    simp only [hF_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_ge ht] at hs
      exact hg_left s hs.2
  have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
    simp only [hF_def, hc_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
    have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_le ht] at hs
        exact hg_right s hs.1
    rw [h, add_zero]
  have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
    rcases le_total t (1 / 2) with ht | ht
    · rw [hF_left t ht]
      exact ⟨le_rfl, hc_pos.le⟩
    rcases le_total 1 t with ht' | ht'
    · rw [hF_right t ht']
      exact ⟨hc_pos.le, le_rfl⟩
    exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
      intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
  -- The profile `φ = 1 − c⁻¹ F`, with `φ' = −c⁻¹ g`.
  have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
    simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
  refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
  · intro t
    obtain ⟨h₀, h₁⟩ := hF_bounds t
    have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
    have h : c⁻¹ * F t ≤ 1 := by
      calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
        _ = 1 := inv_mul_cancel₀ hc_pos.ne'
    exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
  · intro t ht
    simp only [hF_left t ht, mul_zero, sub_zero]
  · intro t ht
    simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
  · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
    rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
    calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
      _ ≤ 3 := by rw [mul_one]; exact hcinv_le
      _ = ((3 : ℝ≥0) : ℝ) := by norm_num
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 107), smoothness of the cutoff: if `φ` is `C^∞` with
`φ ≡ 1` on `(-∞, 1/2]` and `ρ > 0`, then `ζ(x) = φ(‖x − ξ‖/ρ)` is `C^∞` on `ℝᵐ`.  Near `ξ`,
`ζ ≡ 1` on `B̆_{ρ/2}(ξ)`; at `x ≠ ξ` the norm is `C^∞` at `x − ξ ≠ 0`. -/
theorem contDiff_radial_profile_of_eq_one_le_half : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (φ : ℝ → ℝ), 0 < ρ → ContDiff ℝ (⊤ : ℕ∞) φ → (∀ t, t ≤ 1 / 2 → φ t = 1) → ContDiff ℝ (⊤ : ℕ∞) (fun x : Rn m => φ (‖x - ξ‖ / ρ)) := by
  intro m ξ ρ φ hρ hφ hφ1
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x ξ with rfl | hx
  · -- `ζ ≡ 1` on the open ball `B̆_{ρ/2}(ξ)`, a neighbourhood of `ξ`.
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds x (half_pos hρ)] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hφ1 _ ((div_le_iff₀ hρ).2 (by linarith))
  · -- `y ↦ ‖y − ξ‖/ρ` is `C^∞` at `x` since `x − ξ ≠ 0`; compose with `φ`.
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Rn m => ‖y - ξ‖ / ρ) x :=
      ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const ρ
    exact hφ.contDiffAt.comp x h
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): the cutoff gradient bound `|∇ζ| ≤ 3/ρ`, for a general
Lipschitz constant `K` in place of `3`.  If `φ` is `K`-Lipschitz and `ρ > 0`, then
`ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality, so
`‖Dζ(x)‖ ≤ K/ρ` at every `x` (where `ζ` is not differentiable, `fderiv ℝ ζ x = 0`). -/
theorem norm_fderiv_radial_profile_le_of_lipschitzWith : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ) (K : ℝ≥0) (φ : ℝ → ℝ), 0 < ρ → LipschitzWith K φ → ∀ x : Rn m, ‖fderiv ℝ (fun y : Rn m => φ (‖y - ξ‖ / ρ)) x‖ ≤ (K : ℝ) / ρ := by
  intro m ξ ρ K φ hρ hφ x
  -- `ζ(y) = φ(‖y - ξ‖/ρ)` is `(K/ρ)`-Lipschitz by the reverse triangle inequality.
  have hKρ : ((K / ρ.toNNReal : ℝ≥0) : ℝ) = K / ρ := by
    rw [NNReal.coe_div, Real.coe_toNNReal ρ hρ.le]
  have hlip : LipschitzWith (K / ρ.toNNReal) fun y : Rn m => φ (‖y - ξ‖ / ρ) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [hKρ]
    calc dist (φ (‖y - ξ‖ / ρ)) (φ (‖z - ξ‖ / ρ))
        ≤ K * dist (‖y - ξ‖ / ρ) (‖z - ξ‖ / ρ) := hφ.dist_le_mul _ _
      _ = K / ρ * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ]; ring
      _ ≤ K / ρ * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = K / ρ * dist y z := by rw [sub_sub_sub_cancel_right, dist_eq_norm]
  -- A `C`-Lipschitz function has `‖Dζ(x)‖ ≤ C` (and `fderiv ℝ ζ x = 0` where not differentiable).
  exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq hKρ
/-- Simon Ch. 5, proof of Lemma 2.1 (p. 108): a cutoff `ζ ∈ C^∞(ℝᵐ)` with `0 ≤ ζ ≤ 1`, `ζ ≡ 1` on
`B_{ρ/2}(ξ)`, `ζ ≡ 0` outside `B̆_ρ(ξ)` and `|Dζ| ≤ 3/ρ`.  Take `ζ(x) = φ(|x − ξ|/ρ)` for the smooth
`3`-Lipschitz step profile `φ` (`φ = 1` on `(-∞, 1/2]`, `φ = 0` on `[1, ∞)`): `ζ` is smooth since it
is constant near `ξ`, and the radial lift of a `3`-Lipschitz profile has `|Dζ| ≤ 3/ρ`. -/
theorem exists_smooth_cutoff_half_ball_grad_le : ∀ (m : ℕ) (ξ : Rn m) (ρ : ℝ), 0 < ρ → ∃ ζ : Rn m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ Metric.closedBall ξ (ρ / 2), ζ x = 1) ∧ (∀ x, ρ ≤ dist x ξ → ζ x = 0) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / ρ := by
  intro m ξ ρ hρ
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ :=
    Submission.exists_smooth_step_profile_lipschitz_three
  refine ⟨fun x => φ (‖x - ξ‖ / ρ),
    Submission.contDiff_radial_profile_of_eq_one_le_half m ξ ρ φ hρ hφ_smooth hφ_one,
    fun x => hφ_bounds _, fun x hx => hφ_one _ ?_, fun x hx => hφ_zero _ ?_, fun x => ?_⟩
  · -- `|x − ξ| ≤ ρ/2`, so `|x − ξ|/ρ ≤ 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hρ]
    linarith
  · -- `ρ ≤ |x − ξ|`, so `1 ≤ |x − ξ|/ρ`.
    rw [dist_eq_norm] at hx
    rw [le_div_iff₀ hρ]
    linarith
  · -- The profile is `3`-Lipschitz, so `|Dζ(x)| ≤ 3/ρ`.
    have h := Submission.norm_fderiv_radial_profile_le_of_lipschitzWith m ξ ρ 3 φ hρ hφ_lip x
    rwa [NNReal.coe_ofNat] at h
/-- **The Gram matrix of a linear map** (Simon Ch. 5, proof of Theorem 4.5, p. 119: the graph
Jacobian `J_F = √det(δ_ij + D_i f · D_j f)`).  For `D : ℝⁿ →L[ℝ] ℝ^ℓ` let `G_ab = ⟨D e_a, D e_b⟩`.
Then (i) `G` is symmetric, since the real inner product is; (ii) `G` is positive semidefinite:
`x · Gx = Σ_{a,b} x_a x_b ⟨D e_a, D e_b⟩ = |Σ_a x_a D e_a|² ≥ 0` by bilinearity; and
(iii) `trace G = Σ_a |D e_a|² = |D|²` (`hsNormSq`). -/
theorem gwe_gjb_gram_symm_psd_trace : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), Matrix.IsSymm (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) ∧ (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x)) ∧ Matrix.trace (Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) = hsNormSq D := by
  intro n ℓ D
  refine ⟨?_, fun x => ?_, ?_⟩
  · -- (i) `G_ba = ⟨D e_b, D e_a⟩ = ⟨D e_a, D e_b⟩ = G_ab`.
    refine Matrix.IsSymm.ext fun a b => ?_
    simp only [Matrix.of_apply]
    exact real_inner_comm _ _
  · -- (ii) `x · Gx = ⟨w, w⟩` for `w = Σ_a x_a • D e_a`, by bilinearity.
    have h : dotProduct x (Matrix.mulVec (Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) x) =
        inner ℝ (∑ a, x a • D (EuclideanSpace.single a (1 : ℝ)))
          (∑ b, x b • D (EuclideanSpace.single b (1 : ℝ))) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sum_inner, inner_sum,
        real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_comm (D (EuclideanSpace.single a (1 : ℝ)))]
      ring
    rw [h]
    exact real_inner_self_nonneg
  · -- (iii) `trace G = Σ_a ⟨D e_a, D e_a⟩ = Σ_a ‖D e_a‖² = hsNormSq D`.
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, hsNormSq, real_inner_self_eq_norm_sq]
/-- **Determinant bounds for `I + G`** (graph Jacobian bounds in the tilt-excess decay argument):
if `G` is a symmetric real `n × n` matrix with `0 ≤ x ⬝ᵥ G x` for all `x`, then
`1 ≤ det (I + G) ≤ exp (trace G)`.  By Gaussian elimination: `A = I + G` satisfies
`x ⬝ᵥ x ≤ x ⬝ᵥ A x`, so its pivot `a = A₀₀` is at least `1`, and clearing the first column gives
`det A = a * det S` for the Schur complement `S = C - a⁻¹ b bᵀ`.  `S` is again symmetric with
`x ⬝ᵥ x ≤ x ⬝ᵥ S x` (test `A` on `(-(b ⬝ᵥ x) / a, x)`) and `trace S ≤ trace A - a`, so induction
gives `1 ≤ det A ≤ exp (trace A - n)` using `a ≤ exp (a - 1)`; finally `trace (I + G) = n + trace G`.
-/
theorem gwe_gjb_det_one_add_bounds : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ), Matrix.IsSymm G → (∀ x : Fin n → ℝ, 0 ≤ dotProduct x (Matrix.mulVec G x)) → 1 ≤ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ∧ Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + G) ≤ Real.exp (Matrix.trace G) := by
  -- Induction on the size: a symmetric `A` with `x ⬝ᵥ x ≤ x ⬝ᵥ A x` for all `x` satisfies
  -- `1 ≤ det A ≤ exp (trace A - m)`.
  have key : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℝ), (∀ i j, A j i = A i j) →
      (∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec A x)) →
      1 ≤ A.det ∧ A.det ≤ Real.exp (A.trace - m) := by
    intro m
    induction m with
    | zero =>
      intro A _ _
      simp [Matrix.det_fin_zero, Matrix.trace]
    | succ m ih =>
      intro A hA hq
      -- The pivot `a = A₀₀ = e₀ ⬝ᵥ A e₀` is at least `e₀ ⬝ᵥ e₀ = 1`.
      have ha : 1 ≤ A 0 0 := by
        have h := hq (Pi.single 0 1)
        simpa using h
      have ha0 : A 0 0 ≠ 0 := (by linarith : (0 : ℝ) < A 0 0).ne'
      -- The Schur complement `S = C - a⁻¹ b bᵀ` of the pivot.
      obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin m) ℝ,
          S = Matrix.of fun i j => A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ := ⟨_, rfl⟩
      have hSs : ∀ i j, S j i = S i j := by
        intro i j
        rw [hS, Matrix.of_apply, Matrix.of_apply, hA i.succ j.succ, hA 0 i.succ, hA 0 j.succ]
        ring
      -- `x ⬝ᵥ S x = y ⬝ᵥ A y` for `y = (-(b ⬝ᵥ x) / a, x)`, and `y ⬝ᵥ y ≥ x ⬝ᵥ x`.
      have hSq : ∀ x : Fin m → ℝ, dotProduct x x ≤ dotProduct x (Matrix.mulVec S x) := by
        intro x
        obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ∑ j : Fin m, A 0 j.succ * x j := ⟨_, rfl⟩
        obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ i : Fin m, x i * ∑ j : Fin m, A i.succ j.succ * x j :=
          ⟨_, rfl⟩
        have hrow : ∀ i : Fin m,
            Matrix.mulVec S x i = ∑ j, A i.succ j.succ * x j - A 0 i.succ / A 0 0 * b := by
          intro i
          simp only [Matrix.mulVec, dotProduct, hS, Matrix.of_apply]
          rw [hb, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hA 0 i.succ]
          ring
        have eS : dotProduct x (Matrix.mulVec S x) = Q - b * b / A 0 0 := by
          calc dotProduct x (Matrix.mulVec S x)
              = ∑ i, (x i * ∑ j, A i.succ j.succ * x j - A 0 i.succ * x i * (b / A 0 0)) := by
                simp only [dotProduct]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [hrow i]
                ring
            _ = Q - b * b / A 0 0 := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hQ, ← hb]
                ring
        have eA : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ)
            (Matrix.mulVec A (Fin.cons t x)) = A 0 0 * t * t + 2 * t * b + Q := by
          intro t
          simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          have h1 : ∑ i : Fin m, x i * (A i.succ 0 * t + ∑ j, A i.succ j.succ * x j) =
              t * b + Q := by
            rw [hb, hQ, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hA 0 i.succ]
            ring
          rw [h1, ← hb]
          ring
        have eI : ∀ t : ℝ, dotProduct (Fin.cons t x : Fin (m + 1) → ℝ) (Fin.cons t x) =
            t * t + dotProduct x x := by
          intro t
          simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
        have h := hq (Fin.cons (-b / A 0 0) x)
        rw [eA, eI] at h
        rw [eS]
        have e : A 0 0 * (-b / A 0 0) * (-b / A 0 0) + 2 * (-b / A 0 0) * b + Q =
            Q - b * b / A 0 0 := by
          field_simp
          ring
        nlinarith [mul_self_nonneg (-b / A 0 0)]
      -- Eliminating the first column below the pivot: `det A = a * det S`.
      have hdet : A.det = A 0 0 * S.det := by
        obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → ℝ,
            c = Fin.cons 0 (fun i : Fin m => A i.succ 0 / A 0 0) := ⟨_, rfl⟩
        obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
            E = Matrix.of fun i j => A i j - c i * A 0 j := ⟨_, rfl⟩
        have hc0 : c 0 = 0 := by rw [hc]; rfl
        have hE0 : ∀ j, E 0 j = A 0 j := by
          intro j
          rw [hE, Matrix.of_apply, hc0]
          ring
        have hAE : A.det = E.det :=
          Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 hc0 fun i j => by
            rw [hE0, hE, Matrix.of_apply]
            ring
        have hcol : ∀ i : Fin m, E i.succ 0 = 0 := by
          intro i
          rw [hE, Matrix.of_apply, hc, Fin.cons_succ, div_mul_cancel₀ _ ha0, sub_self]
        have hsub : E.submatrix Fin.succ Fin.succ = S := by
          ext i j
          simp only [Matrix.submatrix_apply, hE, hS, Matrix.of_apply, hc, Fin.cons_succ]
        rw [hAE, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
        simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
          pow_zero, one_mul, Fin.succAbove_zero, hE0, hsub]
      -- `trace A = a + trace S + Σᵢ bᵢ² / a`.
      have htr : A.trace = A 0 0 + S.trace + ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 := by
        simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, hS, Matrix.of_apply]
        rw [Finset.sum_sub_distrib]
        have e : ∀ i : Fin m, A i.succ 0 / A 0 0 * A 0 i.succ = A 0 i.succ ^ 2 / A 0 0 := by
          intro i
          rw [hA 0 i.succ]
          ring
        simp only [e]
        ring
      obtain ⟨h1, h2⟩ := ih S hSs hSq
      have hsum : 0 ≤ ∑ i : Fin m, A 0 i.succ ^ 2 / A 0 0 :=
        Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (by linarith)
      have hexp : A 0 0 ≤ Real.exp (A 0 0 - 1) := by
        have := Real.add_one_le_exp (A 0 0 - 1)
        linarith
      refine ⟨?_, ?_⟩
      · rw [hdet]
        nlinarith
      · rw [hdet]
        calc A 0 0 * S.det ≤ Real.exp (A 0 0 - 1) * Real.exp (S.trace - m) :=
              mul_le_mul hexp h2 (by linarith) (Real.exp_pos _).le
          _ = Real.exp (A 0 0 - 1 + (S.trace - m)) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (A.trace - ↑(m + 1)) := by
              apply Real.exp_le_exp.mpr
              rw [htr]
              push_cast
              linarith
  intro n G hG hpos
  have hsymm : ∀ i j, ((1 : Matrix (Fin n) (Fin n) ℝ) + G) j i =
      ((1 : Matrix (Fin n) (Fin n) ℝ) + G) i j :=
    (Matrix.isSymm_one.add hG).apply
  have hquad : ∀ x : Fin n → ℝ,
      dotProduct x x ≤ dotProduct x (Matrix.mulVec ((1 : Matrix (Fin n) (Fin n) ℝ) + G) x) := by
    intro x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    linarith [hpos x]
  obtain ⟨h1, h2⟩ := key n _ hsymm hquad
  refine ⟨h1, h2.trans_eq ?_⟩
  rw [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin]
  congr 1
  ring
/-- **Scalar exponential bound** for the area Jacobian of a linear graph (used with `s = |D|²`,
`T = n` in `J(D) ≤ exp(|D|²/2) ≤ 1 + (e^{n/2}/2)|D|²`): for `0 ≤ s ≤ T`,
`exp(s/2) ≤ 1 + (exp(T/2)/2) s`.  With `t = s/2`, `1 - t ≤ exp(-t)` (`add_one_le_exp` at `-t`)
times `exp t > 0` gives `exp t ≤ 1 + t exp t`, and `t exp t ≤ t exp(T/2)` by monotonicity of
`exp` and `0 ≤ t ≤ T/2`. -/
theorem gwe_gjb_exp_half_le : ∀ (s T : ℝ), 0 ≤ s → s ≤ T → Real.exp (s / 2) ≤ 1 + Real.exp (T / 2) / 2 * s := by
  intro s T hs hsT
  -- `1 - s/2 ≤ exp (-(s/2))`: `add_one_le_exp` at `-(s/2)`.
  have h1 : 1 - s / 2 ≤ Real.exp (-(s / 2)) := by
    linarith [Real.add_one_le_exp (-(s / 2))]
  -- Multiply by `exp (s/2) > 0`, using `exp (-(s/2)) * exp (s/2) = exp 0 = 1`.
  have h2 : (1 - s / 2) * Real.exp (s / 2) ≤ 1 := by
    calc (1 - s / 2) * Real.exp (s / 2) ≤ Real.exp (-(s / 2)) * Real.exp (s / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  -- `exp` is monotone, `s/2 ≤ T/2` and `0 ≤ s/2`.
  have h4 : s / 2 * Real.exp (s / 2) ≤ s / 2 * Real.exp (T / 2) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by linarith)
  -- `exp (s/2) ≤ 1 + (s/2) exp (s/2) ≤ 1 + (s/2) exp (T/2)`.
  linarith
/-- **Hilbert–Schmidt versus operator norm** (Simon, Notation p. ix), as used in the hole estimate
of the proof of Ch. 5, Corollary 2.7 (`‖A‖ ≤ |A|`).  For `A : ℝᵐ →L ℝᵏ` the squared Hilbert–Schmidt
norm `|A|² = Σᵢ |A eᵢ|²` is continuous in `A` (a finite sum of squared norms of the evaluations
`A ↦ A eᵢ`) and satisfies `0 ≤ |A|² ≤ m ‖A‖²` (`|A eᵢ| ≤ ‖A‖ |eᵢ| = ‖A‖`).  Moreover
`|A v|² ≤ |A|² |v|²`: expanding `v = Σᵢ vᵢ eᵢ` gives `|A v| ≤ Σᵢ |vᵢ| |A eᵢ|`, and Cauchy–Schwarz
bounds the square of the right side by `(Σᵢ |vᵢ|²)(Σᵢ |A eᵢ|²) = |v|² |A|²`. -/
theorem lgc_hsNormSq_bounds : ∀ (m k : ℕ), Continuous (fun A : Rn m →L[ℝ] Rn k => hsNormSq A) ∧ ∀ A : Rn m →L[ℝ] Rn k, 0 ≤ hsNormSq A ∧ hsNormSq A ≤ m * ‖A‖ ^ 2 ∧ ∀ v : Rn m, ‖A v‖ ^ 2 ≤ hsNormSq A * ‖v‖ ^ 2 := by
  intro m k
  refine ⟨?_, fun A => ⟨?_, ?_, fun v => ?_⟩⟩
  · -- Continuity: a finite sum of `‖A eᵢ‖ ^ 2`, each continuous in `A`.
    unfold hsNormSq
    fun_prop
  · unfold hsNormSq
    positivity
  · -- `‖A eᵢ‖ ≤ ‖A‖ ‖eᵢ‖ = ‖A‖` for each of the `m` summands.
    unfold hsNormSq
    calc ∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin m, ‖A‖ ^ 2 := by
          gcongr with i
          calc ‖A (EuclideanSpace.single i 1)‖ ≤ ‖A‖ * ‖EuclideanSpace.single i (1:ℝ)‖ :=
                A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = m * ‖A‖ ^ 2 := by simp
  · unfold hsNormSq
    set e : Fin m → Rn m := fun i => EuclideanSpace.single i 1 with he
    -- Expand `v` in the standard basis and apply the triangle inequality.
    have hv : v = ∑ i, v i • e i := by
      ext j
      simp [he, Pi.single_apply]
    have hAv : A v = ∑ i, v i • A (e i) := by
      conv_lhs => rw [hv]
      simp [map_sum, map_smul]
    have h1 : ‖A v‖ ≤ ∑ i, |v i| * ‖A (e i)‖ := by
      rw [hAv]
      calc _ ≤ ∑ i, ‖v i • A (e i)‖ := norm_sum_le _ _
        _ = _ := by simp [norm_smul]
    -- Cauchy–Schwarz for the finite sums, and `‖v‖² = Σᵢ |vᵢ|²`.
    have h2 : (∑ i, |v i| * ‖A (e i)‖) ^ 2 ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ‖v‖ ^ 2 = ∑ i, |v i| ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [sq_abs]
    have h0 : 0 ≤ ‖A v‖ := norm_nonneg _
    calc ‖A v‖ ^ 2 ≤ (∑ i, |v i| * ‖A (e i)‖) ^ 2 := by gcongr
      _ ≤ (∑ i, |v i| ^ 2) * (∑ i, ‖A (e i)‖ ^ 2) := h2
      _ = (∑ i, ‖A (e i)‖ ^ 2) * ‖v‖ ^ 2 := by rw [h3, mul_comm]

/-- **Area Jacobian of a linear graph** (Simon Ch. 5, proof of Theorem 4.5, p. 119:
`1 ≤ J_F ≤ 1 + C |∇f|²`).  For `D : ℝⁿ →L ℝ^ℓ` with Gram matrix `G = (⟨D eₐ, D e_b⟩)_{a,b}`, the
area Jacobian of `v ↦ (v, D v)` is `J(D) = √det(I + G)`; then `1 ≤ J(D)`, and `‖D‖ ≤ 1` implies
`J(D) ≤ 1 + (e^{n/2}/2) |D|²`.  `G` is symmetric positive semidefinite with `trace G = |D|²`, so
`1 ≤ det(I + G) ≤ exp |D|²` and `1 ≤ J(D) ≤ exp(|D|²/2)`.  If `‖D‖ ≤ 1` then `0 ≤ |D|² ≤ n ‖D‖² ≤ n`,
and `exp(s/2) ≤ 1 + (e^{T/2}/2) s` for `0 ≤ s ≤ T` (with `s = |D|²`, `T = n`). -/
theorem gwe_graph_jacobian_bounds : ∀ (n ℓ : ℕ) (D : Rn n →L[ℝ] Rn ℓ), 1 ≤ Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ∧ (‖D‖ ≤ 1 → Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D) := by
  intro n ℓ D
  -- Steps 1, 2, 6: the Gram matrix `G` of `D` is symmetric positive semidefinite, `trace G = |D|²`.
  obtain ⟨hsymm, hpsd, htr⟩ := Submission.gwe_gjb_gram_symm_psd_trace n ℓ D
  -- Steps 3, 4, 7: `1 ≤ det(I + G) ≤ exp (trace G) = exp |D|²`.
  obtain ⟨hdet, hdet_le⟩ := Submission.gwe_gjb_det_one_add_bounds n _ hsymm hpsd
  rw [htr] at hdet_le
  refine ⟨?_, fun hD => ?_⟩
  · -- Step 5: `J(D) = √det(I + G) ≥ √1 = 1`.
    exact Real.one_le_sqrt.2 hdet
  · -- Step 9: `0 ≤ |D|² ≤ n ‖D‖² ≤ n`, since `‖D‖ ≤ 1`.
    obtain ⟨h0, hle, -⟩ := (Submission.lgc_hsNormSq_bounds n ℓ).2 D
    have hn : hsNormSq D ≤ n :=
      hle.trans (mul_le_of_le_one_right (Nat.cast_nonneg n) (pow_le_one₀ (norm_nonneg D) hD))
    -- Steps 8, 10, 11: `J(D) ≤ √(exp |D|²) = exp (|D|²/2) ≤ 1 + (e^{n/2}/2) |D|²`.
    calc Real.sqrt _ ≤ Real.sqrt (Real.exp (hsNormSq D)) := Real.sqrt_le_sqrt hdet_le
      _ = Real.exp (hsNormSq D / 2) := (Real.exp_half _).symm
      _ ≤ 1 + Real.exp ((n : ℝ) / 2) / 2 * hsNormSq D := Submission.gwe_gjb_exp_half_le _ _ h0 hn

/-- Simon Ch. 2, 3.5 (area formula) for a rotated Lipschitz graph, as used in the proof of Ch. 5,
Theorem 4.5: if `f` is `K`-Lipschitz on `B_R(0)`, `A ⊆ B_R(0)` is Borel and `q` is a linear isometry
of `ℝ^{n+ℓ}`, then `∫_{q(graph f|A)} g dHⁿ = ∫_A J_f(x) g(q(x, f(x))) dx` for every `g ≥ 0`, where
`J_f = √det(I + (Df eₐ · Df e_b)_{a,b})`. Extend `f` to a globally Lipschitz `f'`; the graph map
`G x = q(x, f' x)` is injective, Lipschitz and does not decrease distances. For linear `D`, the map
`T_D v = q(v, D v)` is an isometry after an endomorphism `W` of `ℝⁿ` with `|det W| = J(D)`, so
`Hⁿ(T_D(s)) = J(D) Lⁿ(s)` (Simon (3.1)) and `J(D) ≥ 1`. Split a set of differentiability points
of `f'` into the cells `tᵐ ≤ J(Df') < tᵐ⁺¹` and these into pieces on which `G` is `δ`-close to
some `T_{Df'(y)}`: there `Hⁿ(G(·))` and `∫ J(Df')` agree up to `t²`. Letting `t → 1` and using
Rademacher, `Hⁿ(G(·)) = J(Df') Lⁿ`, which transfers to integrals along the embedding `G`.
Finally `f = f'` near almost every point of `A`, as the sphere `∂B_R(0)` is null. -/
theorem gwe_lipschitz_graph_area_formula : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ closedBall 0 R → ∀ g : Amb n ℓ → ℝ≥0∞, ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ)) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ f x (EuclideanSpace.single b (1 : ℝ)))))) * g (q (graphPoint x (f x))) := by
  intro n ℓ hn q f K R hf A hA hAR g
  -- graph coordinates: `(a, b) - (a', b') = (a - a', b - b')`, `|(a, b)|² = |a|² + |b|²`
  obtain ⟨hsub, hnorm, -, -⟩ := lip_approx_graph_coordinates n ℓ q
  -- `⟨(a, b), (a', b')⟩ = ⟨a, a'⟩ + ⟨b, b'⟩`
  have hinner : ∀ (a a' : Rn n) (b b' : Rn ℓ),
      inner ℝ (graphPoint a b) (graphPoint a' b') = inner ℝ a a' + inner ℝ b b' := by
    intro a a' b b'
    simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  -- `(a, b) ↦ graphPoint a b` is the linear isomorphism `ℝⁿ × ℝ^ℓ ≃ ℝ^{n+ℓ}`
  let Φ := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := ℓ)).symm
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = Φ (a, b) := by
    intro a b
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [Φ, graphPoint]
    · simp [Φ, graphPoint]
  -- the Jacobian `J(D) = √det(I + (⟨D eₐ, D e_b⟩))` of the graph of a linear map `D`
  obtain ⟨J, hJ⟩ : ∃ J : (Rn n →L[ℝ] Rn ℓ) → ℝ, ∀ D, J D = Real.sqrt (Matrix.det
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ))))) :=
    ⟨_, fun _ => rfl⟩
  have hJcont : Continuous J := by
    rw [show J = _ from funext hJ]
    fun_prop
  -- the graph map `T D : v ↦ q(v, D v)` of a linear map `D`
  obtain ⟨T, hT⟩ : ∃ T : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Amb n ℓ),
      ∀ D v, T D v = q (graphPoint v (D v)) :=
    ⟨fun D => (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ) ∘L
      ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ) ∘L ((ContinuousLinearMap.id ℝ (Rn n)).prod D)),
      fun D v => by simp [hgp]⟩
  have hTinner : ∀ D u w, inner ℝ (T D u) (T D w) = inner ℝ u w + inner ℝ (D u) (D w) := by
    intro D u w
    rw [hT, hT, LinearIsometryEquiv.inner_map_map, hinner]
  have hTnorm : ∀ D v, ‖v‖ ≤ ‖T D v‖ := by
    intro D v
    have h := hTinner D v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by nlinarith [sq_nonneg ‖D v‖])
  have hTinj : ∀ D, Function.Injective (T D) := by
    intro D x y hxy
    have h := hTnorm D (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  -- Simon (3.1), linear area formula: `Hⁿ(T D (s)) = J(D) Lⁿ(s)`
  have hlin : ∀ D (s : Set (Rn n)),
      (μHE[n] : Measure (Amb n ℓ)) (T D '' s) = ENNReal.ofReal (J D) * volume s := by
    intro D s
    have hTinj' : Function.Injective (T D : Rn n →ₗ[ℝ] Amb n ℓ) := hTinj D
    set V : Submodule ℝ (Amb n ℓ) := LinearMap.range (T D : Rn n →ₗ[ℝ] Amb n ℓ) with hVdef
    have hV : Module.finrank ℝ V = n := by
      rw [hVdef, LinearMap.finrank_range_of_inj hTinj', finrank_euclideanSpace_fin]
    set bV : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hV)
    -- `T D = ι ∘ W` with `ι` a linear isometry and `W` an endomorphism of `ℝⁿ`
    set W : Rn n →ₗ[ℝ] Rn n := (bV.repr.toLinearEquiv : V →ₗ[ℝ] Rn n) ∘ₗ
      (T D : Rn n →ₗ[ℝ] Amb n ℓ).rangeRestrict
    set ι : Rn n →ₗᵢ[ℝ] Amb n ℓ := V.subtypeₗᵢ.comp bV.repr.symm.toLinearIsometry
    have hιW : ∀ v, ι (W v) = T D v := by
      intro v
      simp [ι, W]
    have himage : T D '' s = ι '' (W '' s) := by
      rw [Set.image_image]
      exact Set.image_congr fun v _ => (hιW v).symm
    rw [himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    congr 2
    -- `|det W| = √det(Wᵀ W)` and `Wᵀ W = I + (⟨D eₐ, D e_b⟩)`
    set M := LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis W with hM
    have hWinner : ∀ u w, inner ℝ (W u) (W w) = inner ℝ (T D u) (T D w) := by
      intro u w
      rw [← hιW, ← hιW, LinearIsometry.inner_map_map]
    have hgram : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of (fun a b : Fin n =>
        inner ℝ (D (EuclideanSpace.single a (1 : ℝ))) (D (EuclideanSpace.single b (1 : ℝ)))) =
        M.transpose * M := by
      ext a b
      have h1 := hWinner (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ))
      rw [hTinner, EuclideanSpace.inner_single_left, PiLp.inner_apply] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hM, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_toBasis,
        PiLp.basisFun_apply, PiLp.basisFun_repr]
      simp only [map_one, one_mul, PiLp.ofLp_single, Pi.single_apply, RCLike.inner_apply,
        conj_trivial] at h1
      rw [Finset.sum_congr rfl (fun x _ => mul_comm _ _), h1]
    rw [hJ, hgram, Matrix.det_mul, Matrix.det_transpose, hM, LinearMap.det_toMatrix, ← sq,
      Real.sqrt_sq_eq_abs]
  -- comparison of image measures through a pairwise distance bound
  have hcomp : ∀ (φ ψ : Rn n → Amb n ℓ) (s : Set (Rn n)) (c : ℝ≥0), Set.InjOn ψ s →
      (∀ x ∈ s, ∀ y ∈ s, dist (φ x) (φ y) ≤ c * dist (ψ x) (ψ y)) →
      (μHE[n] : Measure (Amb n ℓ)) (φ '' s) ≤ (c : ℝ≥0∞) ^ n * μHE[n] (ψ '' s) := by
    intro φ ψ s c hψ hd
    have hh : LipschitzOnWith c (φ ∘ Function.invFunOn ψ s) (ψ '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [Function.comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy]
        using hd x hx y hy
    have himage : (φ ∘ Function.invFunOn ψ s) '' (ψ '' s) = φ '' s := by
      rw [Set.image_comp, hψ.invFunOn_image Set.Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  -- `J(D) ≥ 1`: `T D` does not decrease distances
  have hJ1 : ∀ D, 1 ≤ J D := by
    intro D
    have hiso : Isometry (fun v : Rn n => q (graphPoint v 0)) := by
      refine Isometry.of_dist_eq fun x y => ?_
      have h := hnorm (x - y) 0
      rw [norm_zero, zero_pow two_ne_zero, add_zero] at h
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, hsub, sub_zero]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
    have hB := hcomp (fun v => q (graphPoint v 0)) (T D) (closedBall 0 1) 1 (hTinj D).injOn
      (fun x _ y _ => by
        rw [hiso.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
        exact hTnorm D (x - y))
    rw [hiso.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hlin, ENNReal.coe_one, one_pow, one_mul] at hB
    have hpos : volume (closedBall (0 : Rn n) 1) ≠ 0 :=
      (measure_closedBall_pos volume 0 one_pos).ne'
    have hfin : volume (closedBall (0 : Rn n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
    exact ENNReal.one_le_ofReal.mp
      ((ENNReal.mul_le_mul_iff_left hpos hfin).mp (by rwa [one_mul]))
  -- Step 1: extend `f` from `B_R(0)` to a globally Lipschitz map `f'`
  obtain ⟨f', hf'L, hf'eq⟩ := hf.extend_finite_dimension
  -- Step 2: the graph map `G x = q(x, f' x)` is Lipschitz, injective, and expands distances
  obtain ⟨G, hG⟩ : ∃ G : Rn n → Amb n ℓ, ∀ x, G x = q (graphPoint x (f' x)) :=
    ⟨_, fun _ => rfl⟩
  have hGL : LipschitzWith (1 * (‖(Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ)‖₊ *
      max 1 (lipschitzExtensionConstant (Rn ℓ) * K))) G := by
    have h := q.lipschitzWith.comp ((Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).lipschitzWith.comp
      (LipschitzWith.id.prodMk hf'L))
    convert h using 1
    funext x
    simp [hG, hgp]
  have hGdist : ∀ x y, dist x y ≤ dist (G x) (G y) := by
    intro x y
    have h := hnorm (x - y) (f' x - f' y)
    rw [dist_eq_norm, dist_eq_norm, hG, hG, ← map_sub, LinearIsometryEquiv.norm_map, hsub]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [h]; nlinarith [sq_nonneg ‖f' x - f' y‖])
  have hGinj : Function.Injective G := by
    intro x y hxy
    have h := hGdist x y
    rw [hxy, dist_self] at h
    exact dist_le_zero.mp h
  have hGemb : MeasurableEmbedding G := hGL.continuous.measurableEmbedding hGinj
  -- at a differentiability point of `f'`, `DG(x) v = q(v, Df'(x) v)`
  have hGd : ∀ x, DifferentiableAt ℝ f' x → HasFDerivAt G (T (fderiv ℝ f' x)) x := by
    intro x hdx
    have h1 : HasFDerivAt (fun y => (y, f' y))
        ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ f' x)) x :=
      (hasFDerivAt_id x).prodMk hdx.hasFDerivAt
    have h2 := (Φ : Rn n × Rn ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h1
    have h3 := (q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp x h2
    convert h3 using 1
    · funext y
      simp [hG, hgp]
    · refine ContinuousLinearMap.ext fun v => ?_
      simp [hT, hgp]
  -- Step 3: the measures `ν(s) = Hⁿ(G(s))` and `ρ = J(Df') Lⁿ` on `ℝⁿ`
  set ν : Measure (Rn n) := Measure.comap G (μHE[n] : Measure (Amb n ℓ)) with hνdef
  have hν : ∀ s, ν s = (μHE[n] : Measure (Amb n ℓ)) (G '' s) := fun s =>
    hGemb.comap_apply _ s
  have hJm : Measurable fun x => J (fderiv ℝ f' x) :=
    hJcont.measurable.comp (measurable_fderiv ℝ f')
  have hjmeas : Measurable fun x => ENNReal.ofReal (J (fderiv ℝ f' x)) :=
    ENNReal.measurable_ofReal.comp hJm
  set ρ : Measure (Rn n) := (volume : Measure (Rn n)).withDensity
    (fun x => ENNReal.ofReal (J (fderiv ℝ f' x))) with hρdef
  have hρ : ∀ s, MeasurableSet s →
      ρ s = ∫⁻ x in s, ENNReal.ofReal (J (fderiv ℝ f' x)) := fun s hs =>
    withDensity_apply _ hs
  -- countable additivity transfers a ratio bound from a partition to its union
  have hsum : ∀ (μ₁ μ₂ : Measure (Rn n)) (c : ℝ≥0∞) (B : Set (Rn n)) (P : ℕ → Set (Rn n)),
      (∀ k, MeasurableSet (P k)) → Pairwise (Function.onFun Disjoint P) → B = ⋃ k, P k →
      (∀ k, μ₁ (P k) ≤ c * μ₂ (P k)) → μ₁ B ≤ c * μ₂ B := by
    intro μ₁ μ₂ c B P hPm hPd hB hle
    rw [hB, measure_iUnion hPd hPm, measure_iUnion hPd hPm, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hle
  -- Step 4: `ν ≤ t² ρ` and `ρ ≤ t² ν` on measurable sets of differentiability points, `t > 1`
  have hDmeas : MeasurableSet {x : Rn n | DifferentiableAt ℝ f' x} :=
    measurableSet_of_differentiableAt ℝ f'
  have hpiece : ∀ t : ℝ≥0, 1 < t → ∀ B, MeasurableSet B →
      B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} →
      ν B ≤ (t : ℝ≥0∞) ^ 2 * ρ B ∧ ρ B ≤ (t : ℝ≥0∞) ^ 2 * ν B := by
    intro t ht B hB hBD
    have ht' : (1 : ℝ) < t := by exact_mod_cast ht
    -- an approximation error `δ` with `(1 + δ)ⁿ ≤ t` and `(1 - δ)⁻ⁿ ≤ t`
    obtain ⟨δ, hδpos, hδ1, hδup, hδlow⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
        ((1 - δ)⁻¹) ^ n < t := by
      have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ < 1 := eventually_lt_nhds zero_lt_one
      have hupper : ∀ᶠ δ : ℝ≥0 in 𝓝 0, (1 + δ) ^ n < t :=
        ((continuousAt_const.add continuousAt_id).pow _).eventually_lt continuousAt_const
          (by simpa using ht)
      have hlower : ∀ᶠ δ : ℝ≥0 in 𝓝 0, ((1 - δ)⁻¹) ^ n < t := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using ht)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub continuousAt_id
        · simp
      have hevent : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ ∧ δ < 1 ∧ (1 + δ) ^ n < t ∧
          ((1 - δ)⁻¹) ^ n < t := by
        filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
          hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds]
          with δ h1 h2 h3 h4
        exact ⟨h1, h2, h3, h4⟩
      exact hevent.exists
    have hup : ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδup.le
    have hlow : (((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n ≤ t := by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlow.le
    have hpow : ∀ m : ℕ, ENNReal.ofReal ((t : ℝ) ^ m) = (t : ℝ≥0∞) ^ m := by
      intro m
      rw [ENNReal.ofReal_pow (NNReal.coe_nonneg t), ENNReal.ofReal_coe_nnreal]
    -- the cells `C m = {x ∈ B : tᵐ ≤ J(Df'(x)) < tᵐ⁺¹}` (recall `J ≥ 1`)
    obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (Rn n), ∀ m, C m = B ∩ {x | (t : ℝ) ^ m ≤ J (fderiv ℝ f' x) ∧
        J (fderiv ℝ f' x) < (t : ℝ) ^ (m + 1)} := ⟨_, fun _ => rfl⟩
    have hCmeas : ∀ m, MeasurableSet (C m) := fun m => by
      rw [hC]
      exact hB.inter ((measurableSet_le measurable_const hJm).inter
        (measurableSet_lt hJm measurable_const))
    have hCdisj : Pairwise (Function.onFun Disjoint C) := by
      intro m m' hmm'
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      rw [hC] at hx hx'
      have e1 : m < m' + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx.2.1.trans_lt hx'.2.2)
      have e2 : m' < m + 1 := (pow_lt_pow_iff_right₀ ht').mp (hx'.2.1.trans_lt hx.2.2)
      exact hmm' (by omega)
    have hCcover : B = ⋃ m, C m := by
      ext x
      simp only [mem_iUnion, hC, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := exists_nat_pow_near (hJ1 (fderiv ℝ f' x)) ht'
        exact ⟨m, hx, hm⟩
      · rintro ⟨m, hx, -⟩
        exact hx
    have hcell : ∀ m, ν (C m) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m) ∧
        ρ (C m) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m) := by
      intro m
      rcases (C m).eq_empty_or_nonempty with hempty | hne
      · simp [hempty]
      have hCD : C m ⊆ {x : Rn n | DifferentiableAt ℝ f' x} := fun x hx => by
        rw [hC] at hx
        exact hBD hx.1
      -- pieces of `C m` on which `G` is `δ`-close to `T(Df'(y))` for some `y ∈ C m`
      obtain ⟨P, L, hPdisj, hPmeas, hPcover, hPapprox, hPL⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G (C m)
          (fun x => T (fderiv ℝ f' x))
          (fun x hx => (hGd x (hCD hx)).hasFDerivWithinAt) (fun _ => δ) (fun _ => hδpos.ne')
      have hQmeas : ∀ k, MeasurableSet (C m ∩ P k) := fun k => (hCmeas m).inter (hPmeas k)
      have hQdisj : Pairwise (Function.onFun Disjoint fun k => C m ∩ P k) := fun i j hij =>
        (hPdisj hij).mono inter_subset_right inter_subset_right
      have hQcover : C m = ⋃ k, C m ∩ P k := by
        rw [← inter_iUnion]
        exact (inter_eq_left.2 hPcover).symm
      have hpc : ∀ k, ν (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) ∧
          ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by
        intro k
        obtain ⟨y, hy, hLy⟩ := hPL hne k
        have hQ : ApproximatesLinearOn G (T (fderiv ℝ f' y)) (C m ∩ P k) δ := by
          have h := hPapprox k
          rwa [hLy] at h
        rw [hC] at hy
        have hJy1 : (t : ℝ≥0∞) ^ m ≤ ENNReal.ofReal (J (fderiv ℝ f' y)) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.1
        have hJy2 : ENNReal.ofReal (J (fderiv ℝ f' y)) ≤ (t : ℝ≥0∞) ^ (m + 1) := by
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hy.2.2.le
        have hρlow : (t : ℝ≥0∞) ^ m * volume (C m ∩ P k) ≤ ρ (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono hjmeas fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.1
        have hρup : ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := by
          rw [hρ _ (hQmeas k), ← setLIntegral_const]
          refine setLIntegral_mono measurable_const fun x hx => ?_
          have hx1 := hx.1
          rw [hC] at hx1
          rw [← hpow]
          exact ENNReal.ofReal_le_ofReal hx1.2.2.le
        -- `G` and `T(Df'(y))` have comparable distances on the piece
        have hd1 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k, dist (G x) (G z) ≤
            ((1 + δ : ℝ≥0) : ℝ) * dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) := by
          intro x hx z hz
          have happ := hQ x hx z hz
          have hl := hTnorm (fderiv ℝ f' y) (x - z)
          rw [map_sub] at happ hl
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
          calc ‖G x - G z‖ ≤ ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := norm_le_norm_sub_add _ _
            _ ≤ δ * ‖x - z‖ + ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ ≤ δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ +
                ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by gcongr
            _ = (1 + δ) * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by ring
        have hd2 : ∀ x ∈ C m ∩ P k, ∀ z ∈ C m ∩ P k,
            dist (T (fderiv ℝ f' y) x) (T (fderiv ℝ f' y) z) ≤
              (((1 - δ)⁻¹ : ℝ≥0) : ℝ) * dist (G x) (G z) := by
          intro x hx z hz
          have happ : ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ ≤
              δ * ‖x - z‖ := by
            simpa only [map_sub] using hQ x hx z hz
          have hl : ‖x - z‖ ≤ ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by
            simpa only [map_sub] using hTnorm (fderiv ℝ f' y) (x - z)
          have hδR : (δ : ℝ) < 1 := by exact_mod_cast hδ1
          have htri : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              ‖G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z)‖ := by
            have h := norm_sub_le (G x - G z)
              (G x - G z - (T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z))
            rwa [sub_sub_cancel] at h
          have hm := mul_le_mul_of_nonneg_left hl (NNReal.coe_nonneg δ)
          have key : ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ ≤ ‖G x - G z‖ +
              δ * ‖T (fderiv ℝ f' y) x - T (fderiv ℝ f' y) z‖ := by linarith
          rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ1.le, NNReal.coe_one,
            inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR), mul_sub, mul_one, mul_comm]
          linarith
        constructor
        · calc ν (C m ∩ P k) = μHE[n] (G '' (C m ∩ P k)) := hν _
            _ ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) :=
              hcomp G _ _ _ (hTinj _).injOn hd1
            _ = ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ n *
                (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k)) := by gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) ^ 2 * ρ (C m ∩ P k) := by gcongr
        · calc ρ (C m ∩ P k) ≤ (t : ℝ≥0∞) ^ (m + 1) * volume (C m ∩ P k) := hρup
            _ = (t : ℝ≥0∞) * ((t : ℝ≥0∞) ^ m * volume (C m ∩ P k)) := by ring
            _ ≤ (t : ℝ≥0∞) * (ENNReal.ofReal (J (fderiv ℝ f' y)) * volume (C m ∩ P k)) := by
              gcongr
            _ = (t : ℝ≥0∞) * μHE[n] (T (fderiv ℝ f' y) '' (C m ∩ P k)) := by rw [hlin]
            _ ≤ (t : ℝ≥0∞) * ((((1 - δ)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * μHE[n] (G '' (C m ∩ P k))) := by
              gcongr
              exact hcomp _ G _ _ hGinj.injOn hd2
            _ ≤ (t : ℝ≥0∞) * ((t : ℝ≥0∞) * ν (C m ∩ P k)) := by
              rw [hν]
              gcongr
            _ = (t : ℝ≥0∞) ^ 2 * ν (C m ∩ P k) := by ring
      exact ⟨hsum ν ρ _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).1,
        hsum ρ ν _ (C m) _ hQmeas hQdisj hQcover fun k => (hpc k).2⟩
    exact ⟨hsum ν ρ _ B C hCmeas hCdisj hCcover fun m => (hcell m).1,
      hsum ρ ν _ B C hCmeas hCdisj hCcover fun m => (hcell m).2⟩
  -- Step 5: letting `t → 1`, `ν = ρ` on sets of differentiability points
  have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
    intro a
    have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
      (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
    simpa only [one_pow, one_mul] using
      ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
  have hD : ∀ B, MeasurableSet B → B ⊆ {x : Rn n | DifferentiableAt ℝ f' x} → ν B = ρ B := by
    intro B hB hBD
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hpiece t ht B hB hBD).2
  -- Step 6: `ν = ρ`, as both vanish on the null set of nondifferentiability points (Rademacher)
  have hDnull : volume {x : Rn n | ¬ DifferentiableAt ℝ f' x} = 0 :=
    ae_iff.mp hf'L.ae_differentiableAt
  have hmain : ν = ρ := by
    ext B hB
    have h1 : ν (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 := by
      rw [hν]
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hGL.lipschitzOnWith (s := B \ {x : Rn n | DifferentiableAt ℝ f' x}))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        measure_mono_null (fun x hx => hx.2) hDnull, mul_zero] at h
      exact le_zero_iff.mp h
    have h2 : ρ (B \ {x : Rn n | DifferentiableAt ℝ f' x}) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null (fun x hx => hx.2) hDnull)
    rw [← measure_inter_add_sdiff B hDmeas, ← measure_inter_add_sdiff (μ := ρ) B hDmeas, h1, h2,
      hD _ (hB.inter hDmeas) inter_subset_right]
  -- Step 7: transfer the integral along the measurable embedding `G`
  have himg : q '' graphOver f A = G '' A := by
    rw [graphOver, Set.image_image]
    refine Set.image_congr fun x hx => ?_
    rw [hG, hf'eq (hAR hx)]
  have hGA : MeasurableSet (G '' A) := hGemb.measurableSet_image' hA
  have hpres : MeasurePreserving G ν ((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) :=
    ⟨hGemb.measurable, hGemb.map_comap _⟩
  calc ∫⁻ y in q '' graphOver f A, g y ∂(μHE[n] : Measure (Amb n ℓ))
      = ∫⁻ y in G '' A, g y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (range G)) := by
        rw [himg, Measure.restrict_restrict hGA, inter_eq_left.2 (image_subset_range G A)]
    _ = ∫⁻ x in A, g (G x) ∂ν := (hpres.setLIntegral_comp_emb hGemb g A).symm
    _ = ∫⁻ x in A, g (G x) ∂ρ := by rw [hmain]
    _ = ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ f' x)) * g (G x) := by
        rw [hρdef, restrict_withDensity hA,
          lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hjmeas.aemeasurable
            (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ = _ := by
        -- a.e. on `A`, `x` is interior to `B_R(0)`, where `f = f'`
        refine setLIntegral_congr_fun_ae hA ?_
        have hnt : Nontrivial (Rn n) := by
          have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
          infer_instance
        have hsph : ∀ᵐ x ∂(volume : Measure (Rn n)), x ∉ sphere (0 : Rn n) R :=
          measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume 0 R)
        filter_upwards [hsph] with x hxs hxA
        have hxb : x ∈ ball (0 : Rn n) R := by
          have h1 := hAR hxA
          rw [mem_closedBall] at h1
          rw [mem_sphere] at hxs
          exact mem_ball.mpr (lt_of_le_of_ne h1 hxs)
        have hev : f =ᶠ[𝓝 x] f' :=
          Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxb) fun y hy =>
            hf'eq (ball_subset_closedBall hy)
        rw [hJ, hG, hev.fderiv_eq, hf'eq (hAR hxA)]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

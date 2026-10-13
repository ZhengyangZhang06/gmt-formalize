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

/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (p. 127): if `H = h` `μ_V`-a.e. for some
`h` continuous on `U`, then `H` is locally in `Lᵖ(μ_V)` in `U` for every `p > 0`.  On a compact
`K ⊆ U`, `|h| ≤ A` and `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞`, so `∫_K |H|ᵖ dμ_V ≤ Aᵖ μ_V(K) < ∞`. -/
theorem dohr_locally_lp_of_continuous : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ), ContinuousOn h U → (∀ᵐ x ∂V.weight, H x = h x) → ∀ p : ℝ, 0 < p → V.LocallyLp H p := by
  intro n ℓ U V H h hh hHh p hp K hK hKU
  -- `|h| ≤ A` on the compact set `K ⊆ U`.
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hh.mono hKU)
  -- `μ_V(K) = ∫_{M ∩ K} θ dHⁿ < ∞` since `θ` is `Hⁿ`-integrable on `M ∩ K`.
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hμK : V.weight K < ∞ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm]
    exact (V.integrableOn_mult K hK hKU).setLIntegral_lt_top
  calc ∫⁻ x in K, ‖H x‖ₑ ^ p ∂V.weight
      = ∫⁻ x in K, ‖h x‖ₑ ^ p ∂V.weight :=
        lintegral_congr_ae (by filter_upwards [ae_restrict_of_ae hHh] with x hx; rw [hx])
    _ ≤ ∫⁻ _ in K, ENNReal.ofReal A ^ p ∂V.weight :=
        setLIntegral_mono measurable_const fun x hx => by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hA x hx)
    _ = ENNReal.ofReal A ^ p * V.weight K := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top) hμK
/-- **Simon Ch. 5, Theorem 7.1, proof, first sentence (p. 127).**  If `H` is locally in `Lᵖ(μ_V)`
on the open set `U` for some `p > n` and `ξ ∈ U` has `Θⁿ(μ_V, ξ) = 1`, then `ξ ∈ spt V`, and for
every `δ > 0` there is `r > 0` with `B_r(ξ) ⊆ U`, `μ_V(B_r(ξ)) ≤ (1 + δ) ω_n rⁿ` and
`(r^{p−n} ∫_{B_r(ξ)} |H|ᵖ dμ_V)^{1/p} ≤ δ`. -/
theorem density_one_allard_scale : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U)
    (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (δ : ℝ), IsOpen U → (n : ℝ) < p →
    V.LocallyLp H p → ξ ∈ U → V.HasDensity ξ 1 → 0 < δ → ξ ∈ V.support ∧ ∃ r : ℝ, 0 < r ∧
      closedBall ξ r ⊆ U ∧
      V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) ∧
      V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ := by
  intro n ℓ U V H p ξ δ hU hp hLp hξU hξ hδ
  rw [RectifiableVarifold.HasDensity, ENNReal.ofReal_one] at hξ
  have hω : 0 < unitBallVolume n :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  -- A closed ball `B_{r₀}(ξ) ⊆ U`; it is compact, so `∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V < ∞`.
  obtain ⟨r₀, hr₀, hr₀U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hξU)
  have hA := hLp _ (isCompact_closedBall ξ r₀) hr₀U
  -- `(r^{p−n} ∫_{B_{r₀}(ξ)} |H|ᵖ dμ_V)^{1/p} → 0` as `r ↓ 0`, since `p > n`.
  have hdecay : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
      ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ (p - n)) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (p - n) (Or.inr hpn.le)).tendsto
      rw [Real.zero_rpow hpn.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hA.ne)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    have h3 : Tendsto (fun r : ℝ => (ENNReal.ofReal (r ^ (p - n)) *
        ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p)) (𝓝[>] 0) (𝓝 (0 ^ (1 / p))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h2
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at h3
  refine ⟨⟨hξU, nhds_basis_closedBall.mem_measureSupport.mpr fun ε hε => ?_⟩, ?_⟩
  · -- `ξ ∈ spt μ_V`: the density ratio tends to `1 > 0`, so `μ_V(B_ε(ξ)) > 0` for every `ε > 0`.
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 ε ∧
        0 < V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) := by
      filter_upwards [Ioo_mem_nhdsGT hε, hξ.eventually_const_lt zero_lt_one] with r h1 h2
      exact ⟨h1, h2⟩
    obtain ⟨r, hr, hQ⟩ := hev.exists
    have h0 : V.weight (closedBall ξ r) ≠ 0 := fun h0 => by simp [h0] at hQ
    exact (pos_iff_ne_zero.mpr h0).trans_le (measure_mono (closedBall_subset_closedBall hr.2.le))
  -- A radius `r ∈ (0, r₀)` below both the mass threshold and the `Lᵖ` threshold.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 r₀ ∧
      V.weight (closedBall ξ r) / ENNReal.ofReal (unitBallVolume n * r ^ n) <
        ENNReal.ofReal (1 + δ) ∧
      (ENNReal.ofReal (r ^ (p - n)) * ∫⁻ x in closedBall ξ r₀, ‖H x‖ₑ ^ p ∂V.weight) ^ (1 / p) <
        ENNReal.ofReal δ := by
    filter_upwards [Ioo_mem_nhdsGT hr₀,
      hξ.eventually_lt_const (ENNReal.one_lt_ofReal.mpr (show (1 : ℝ) < 1 + δ by linarith)),
      hdecay.eventually_lt_const (ENNReal.ofReal_pos.mpr hδ)] with r h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨r, ⟨hr, hrr₀⟩, hQ, hS⟩ := hev.exists
  have hball : closedBall ξ r ⊆ closedBall ξ r₀ := closedBall_subset_closedBall hrr₀.le
  refine ⟨r, hr, hball.trans hr₀U, ?_, ?_⟩
  · have hv : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr n)
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + δ by linarith)]
    exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hv).ne' ENNReal.ofReal_ne_top).mp hQ.le
  · refine le_trans ?_ hS.le
    exact ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono_set hball))
      (one_div_pos.mpr hp0).le
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`.  If `V` has generalized mean curvature `H` in `U`,
then `V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`, and the hypotheses 5.1 of `V` in
`B_r(ξ)` become the hypotheses 5.1 (`AllardHypotheses`) of `V'` in `B_r(0)`. -/
theorem exists_translated_varifold_allardHypotheses : ∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ x, V'.mult x = V.mult (x + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ (∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ))) ∧ ∀ (H : Amb n ℓ → Amb n ℓ) (p δ r : ℝ), V.HasGeneralizedMeanCurvature H → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ξ ∈ V.support → 0 < r → closedBall ξ r ⊆ U → V.weight (closedBall ξ r) ≤ ENNReal.ofReal ((1 + δ) * (unitBallVolume n * r ^ n)) → V.scaledLpNorm H p ξ r ≤ ENNReal.ofReal δ → V'.AllardHypotheses (fun x => H (x + ξ)) p δ r := by
  intro n ℓ U V ξ
  -- Step 1: `τ = (· − ξ)` is an isometric measurable equivalence with inverse `(· + ξ)`; both
  -- preserve `Hⁿ`, and `τ(S) = (· + ξ)⁻¹(S)`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro hx
      exact ⟨x + ξ, hx, by simp⟩
  have hiso : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hmp_add : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hmp_sub : MeasurePreserving (fun x : Amb n ℓ => x - ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hme_add : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  have hme_sub : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  -- `τ⁻¹(K) ⊆ U` whenever `K ⊆ τ(U)`.
  have hpre_sub : ∀ K : Set (Amb n ℓ), K ⊆ (fun x => x - ξ) '' U → (fun x => x - ξ) ⁻¹' K ⊆ U := by
    intro K hKU y hy
    obtain ⟨u, hu, hu'⟩ := hKU hy
    have : u = y := by simpa using hu'
    exact this ▸ hu
  -- Step 2: the structure fields of `V' = v(τ(M), θ(· + ξ))` in `τ(U)`.
  have hc_meas : NullMeasurableSet ((fun x => x - ξ) '' V.carrier) (μHE[n] : Measure (Amb n ℓ)) := by
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hmp_add.quasiMeasurePreserving
  have hc_rect : Poincare.SimonGMT.Chapter03.CountablyRectifiable n
      ((fun x => x - ξ) '' V.carrier) := by
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j y => F j y - ξ, fun j => ?_, ?_⟩
    · rw [hiso.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨1 * K, hiso.lipschitzWith.comp hK⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, y, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, y, rfl⟩)
  have hm_pos : ∀ x ∈ (fun x => x - ξ) '' V.carrier, 0 < V.mult (x + ξ) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using V.mult_pos x hx
  have hm_aemeas : AEMeasurable (fun x => V.mult (x + ξ))
      ((μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier)) := by
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hmp_add.restrict_preimage_emb hme_add V.carrier).quasiMeasurePreserving
  have hm_int : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ (fun x => x - ξ) '' U →
      IntegrableOn (fun x => V.mult (x + ξ)) ((fun x => x - ξ) '' V.carrier ∩ K)
        (μHE[n] : Measure (Amb n ℓ)) := by
    intro K hK hKU
    have hK' : IsCompact ((fun x => x - ξ) ⁻¹' K) := (Homeomorph.subRight ξ).isCompact_preimage.2 hK
    have h := V.integrableOn_mult _ hK' (hpre_sub K hKU)
    rw [← hmp_add.integrableOn_comp_preimage hme_add] at h
    have hset : (fun x => x - ξ) '' V.carrier ∩ K =
        (fun x => x + ξ) ⁻¹' (V.carrier ∩ (fun x => x - ξ) ⁻¹' K) := by
      rw [himage]
      ext x
      simp
    rw [hset]
    exact h
  obtain ⟨V', hV'c, hV'm⟩ : ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U),
      V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ x, V'.mult x = V.mult (x + ξ) :=
    ⟨⟨(fun x => x - ξ) '' V.carrier, fun x => V.mult (x + ξ), image_mono V.carrier_subset,
      hc_meas, hc_rect, hm_pos, hm_aemeas, hm_int⟩, rfl, fun _ => rfl⟩
  have hV'mf : V'.mult = fun x => V.mult (x + ξ) := funext hV'm
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hweight : V'.weight = V.weight.map (fun x => x - ξ) := by
    have hres : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map (fun x => x - ξ) =
        (μHE[n] : Measure (Amb n ℓ)).restrict ((fun x => x - ξ) '' V.carrier) := by
      have h1 := hme_sub.restrict_map (μHE[n] : Measure (Amb n ℓ)) ((fun x => x - ξ) '' V.carrier)
      rw [hmp_sub.map_eq, preimage_image_eq _ hme_sub.injective] at h1
      exact h1.symm
    ext s hs
    rw [Measure.map_apply hme_sub.measurable hs]
    simp only [RectifiableVarifold.weight]
    rw [hV'c, hV'mf, withDensity_apply _ hs, withDensity_apply _ (hme_sub.measurable hs),
      ← hres, hme_sub.restrict_map, hme_sub.lintegral_map]
    simp
  -- Step 4: `spt V' = τ(spt V)`, since `spt(τ_# μ) = τ(spt μ)` for the homeomorphism `τ`.
  have hsupport : V'.support = (fun x => x - ξ) '' V.support := by
    have hspt : (V.weight.map (fun x => x - ξ)).support =
        (fun x => x - ξ) '' V.weight.support := by
      ext x
      rw [himage, mem_preimage, Measure.mem_support_iff_forall, Measure.mem_support_iff_forall]
      constructor
      · intro h N' hN'
        have hN : (fun y => y + ξ) ⁻¹' N' ∈ 𝓝 x :=
          (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds hN'
        have := h _ hN
        rw [hme_sub.map_apply] at this
        convert this using 2
        ext y
        simp
      · intro h N hN
        have hN' : (fun y => y - ξ) ⁻¹' N ∈ 𝓝 (x + ξ) := by
          apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
          simpa using hN
        rw [hme_sub.map_apply]
        exact h _ hN'
    unfold RectifiableVarifold.support
    rw [hweight, hspt, image_inter hme_sub.injective]
  -- Step 5: weighted approximate tangent spaces, hence `tangentProj`, are translation equivariant.
  have htangent : ∀ x, V'.tangentProj x = V.tangentProj (x + ξ) := by
    intro x
    have hpred : (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V'.carrier V'.mult x P) =
        (fun P => Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n
        V.carrier V.mult (x + ξ) P) := by
      funext P
      have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap x r '' V'.carrier =
          Poincare.SimonGMT.Chapter03.blowUpMap (x + ξ) r '' V.carrier := by
        intro r
        rw [hV'c, image_image]
        congr 1
        funext m
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
        congr 1
        abel
      have hmult : ∀ (r : ℝ) (y : Amb n ℓ), V'.mult (x + r • y) = V.mult (x + ξ + r • y) := by
        intro r y
        rw [hV'm]
        congr 1
        abel
      unfold Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt
      simp only [hset, hmult, hV'm]
    have hchoose : ∀ {p q : Submodule ℝ (Amb n ℓ) → Prop} (h1 : ∃ P, p P) (h2 : ∃ P, q P),
        p = q → Classical.choose h1 = Classical.choose h2 := by
      intro p q h1 h2 h
      subst h
      rfl
    have hproj : ∀ {K L : Submodule ℝ (Amb n ℓ)} [K.HasOrthogonalProjection]
        [L.HasOrthogonalProjection], K = L → K.starProjection = L.starProjection := by
      intro K L _ _ h
      subst h
      rfl
    unfold RectifiableVarifold.tangentProj
    split_ifs with h1 h2 h2
    · exact hproj (hchoose h1 h2 hpred)
    · exact absurd (hpred ▸ h1) h2
    · exact absurd (hpred ▸ h2) h1
    · rfl
  -- Step 6: `div_{M'} X ∘ τ = div_M (X ∘ τ)`.
  have hdiv : ∀ (X : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ),
      V'.divM X (y - ξ) = V.divM (fun z => X (z - ξ)) y := by
    intro X y
    unfold RectifiableVarifold.divM
    rw [htangent, fderiv_comp_sub, sub_add_cancel]
  -- Step 7: generalized mean curvature transfers to `V'` with `H' = H(· + ξ)`.
  have hGMC : ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H →
      V'.HasGeneralizedMeanCurvature (fun x => H (x + ξ)) := by
    intro H hH
    obtain ⟨hloc, hid⟩ := hH
    let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
    have he : (fun x : Amb n ℓ => x - ξ) = ⇑e := rfl
    refine ⟨?_, ?_⟩
    · rw [hweight]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨N, hN, hint⟩ := hloc y hy
      refine ⟨(fun x => x - ξ) '' N, ?_, ?_⟩
      · have hmap := (Homeomorph.subRight ξ).isEmbedding.map_nhdsWithin_eq U y
        simp only [Homeomorph.coe_subRight] at hmap
        rw [← hmap]
        exact image_mem_map hN
      · rw [he, integrableOn_map_equiv e, preimage_image_eq _ e.injective]
        convert hint using 1
        funext z
        show H (z - ξ + ξ) = H z
        rw [sub_add_cancel]
    · intro X hX hXc hXU
      rw [hweight]
      have hI1 : ∫ x, V'.divM X x ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, V'.divM X (y - ξ) ∂V.weight := integral_map_equiv e _
      have hI2 : ∫ x, inner ℝ (X x) (H (x + ξ)) ∂(V.weight.map (fun x => x - ξ)) =
          ∫ y, inner ℝ (X (y - ξ)) (H (y - ξ + ξ)) ∂V.weight :=
        integral_map_equiv e (fun x => inner ℝ (X x) (H (x + ξ)))
      rw [hI1, hI2]
      simp only [hdiv, sub_add_cancel]
      have hY1 : ContDiff ℝ 1 (fun z => X (z - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
      have hY2 : HasCompactSupport (fun z => X (z - ξ)) :=
        hXc.comp_homeomorph (Homeomorph.subRight ξ)
      have hY3 : tsupport (fun z => X (z - ξ)) ⊆ U := by
        have hts : tsupport (fun z => X (z - ξ)) = (fun z => z - ξ) ⁻¹' tsupport X := by
          have := (Homeomorph.subRight ξ).preimage_closure (Function.support X)
          simp only [Homeomorph.coe_subRight] at this
          rw [tsupport, tsupport, this]
          rfl
        rw [hts]
        exact hpre_sub _ hXU
      exact hid _ hY1 hY2 hY3
  refine ⟨V', hV'c, hV'm, hweight, hsupport, hGMC, ?_⟩
  -- Step 8: the hypotheses 5.1 of `V` in `B_r(ξ)` are those of `V'` in `B_r(0)`.
  intro H p δ r hH hθ hξ hr hball hmass hLp
  have hball_pre : (fun x => x - ξ) ⁻¹' closedBall (0 : Amb n ℓ) r = closedBall ξ r := by
    ext y
    simp [dist_eq_norm]
  refine ⟨hr, hGMC H hH, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hweight, hme_sub.ae_map_iff]
    filter_upwards [hθ] with y hy
    rw [hV'm, sub_add_cancel]
    exact hy
  · rw [hsupport]
    exact ⟨ξ, hξ, sub_self ξ⟩
  · intro z hz
    refine ⟨z + ξ, hball ?_, by simp⟩
    rw [← hball_pre]
    simpa using hz
  · rw [hweight, hme_sub.map_apply, hball_pre]
    exact hmass
  · unfold RectifiableVarifold.scaledLpNorm at hLp ⊢
    rw [hweight, hme_sub.restrict_map, hme_sub.lintegral_map, hball_pre]
    simpa using hLp
/-- In the proof of Simon 7.1 (p. 127), `u ∈ C^{1,1−n/p}` comes from the estimate of Theorem 5.2:
a finite scaled `C^{1,α}` norm on `B` puts `u` in the Hölder class `C^{1,α}(W)` for every
`W ⊆ int B`.  On `int B` the derivative within `B` is the derivative, and the operator norm of a
linear map is at most its Hilbert–Schmidt norm. -/
theorem isHolderCk_one_of_scaledC1AlphaNorm_ne_top : ∀ {n ℓ : ℕ} (u : Rn n → Rn ℓ) (B W : Set (Rn n)) (α ρ : ℝ), 0 < α → 0 < ρ → ContDiffOn ℝ 1 u B → W ⊆ interior B → scaledC1AlphaNorm u B α ρ ≠ ∞ → IsHolderCkα 1 α u W := by
  intro n ℓ u B W α ρ hα hρ hu hW hN
  -- The operator norm is at most the Hilbert–Schmidt norm (Cauchy–Schwarz in the standard basis).
  have hop : ∀ A : Rn n →L[ℝ] Rn ℓ, ‖A‖ ≤ hsNorm A := by
    intro A
    refine A.opNorm_le_bound (Real.sqrt_nonneg _) fun v => ?_
    have hv : ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    calc ‖A v‖ = ‖A (∑ i, v i • EuclideanSpace.single i (1 : ℝ))‖ := by rw [hv]
      _ = ‖∑ i, v i • A (EuclideanSpace.single i 1)‖ := by simp only [map_sum, map_smul]
      _ ≤ ∑ i, ‖v i‖ * ‖A (EuclideanSpace.single i 1)‖ :=
          (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)
      _ ≤ √(∑ i, ‖v i‖ ^ 2) * √(∑ i, ‖A (EuclideanSpace.single i 1)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = hsNorm A * ‖v‖ := by rw [EuclideanSpace.norm_eq v, mul_comm (hsNorm A)]; rfl
  -- The three suprema in the scaled norm are finite, since `ρ⁻¹ > 0` and `ρ ^ α > 0`.
  rw [scaledC1AlphaNorm, ENNReal.add_ne_top, ENNReal.add_ne_top] at hN
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := hN
  replace h₀ : (⨆ x ∈ B, ‖u x‖ₑ) ≠ ∞ := fun h =>
    h₀ (ENNReal.mul_eq_top.2 (Or.inl ⟨(ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne', h⟩))
  replace h₂ : (⨆ x ∈ B, ⨆ y ∈ B, ⨆ (_ : x ≠ y),
      ENNReal.ofReal (hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) / ‖x - y‖ ^ α)) ≠ ∞ :=
    fun h => h₂ (ENNReal.mul_eq_top.2
      (Or.inl ⟨(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hρ α)).ne', h⟩))
  -- Real bounds on `B` for `|u|`, `|D_B u|` and the Hölder quotients of `D_B u`.
  obtain ⟨s₀, hb₀⟩ : ∃ s : ℝ, ∀ x ∈ B, ‖u x‖ ≤ s :=
    ⟨_, fun x hx => (toReal_enorm (u x)).symm.trans_le
      (ENNReal.toReal_mono h₀ (le_iSup₂_of_le x hx le_rfl))⟩
  obtain ⟨s₁, hb₁⟩ : ∃ s : ℝ, ∀ x ∈ B, hsNorm (fderivWithin ℝ u B x) ≤ s :=
    ⟨_, fun x hx => (ENNReal.ofReal_le_iff_le_toReal h₁).1 (le_iSup₂_of_le x hx le_rfl)⟩
  obtain ⟨s₂, hb₂⟩ : ∃ s : ℝ, ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      hsNorm (fderivWithin ℝ u B x - fderivWithin ℝ u B y) ≤ s * ‖x - y‖ ^ α :=
    ⟨_, fun x hx y hy hxy =>
      (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hxy)) α)).1
        ((ENNReal.ofReal_le_iff_le_toReal h₂).1
          (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))))⟩
  -- On `W ⊆ int B` the derivative within `B` is the derivative.
  have hWB : W ⊆ B := hW.trans interior_subset
  have hD : ∀ x ∈ W, fderivWithin ℝ u B x = fderiv ℝ u x := fun x hx =>
    fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 (hW hx))
  refine ⟨?_, ⟨max s₀ s₁, ?_⟩, ⟨s₂, ?_⟩⟩
  · exact_mod_cast hu.mono hWB
  · intro i hi x hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
    · rw [norm_iteratedFDeriv_zero]
      exact (hb₀ x (hWB hx)).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one, ← hD x hx]
      exact ((hop _).trans (hb₁ x (hWB hx))).trans (le_max_right _ _)
  · intro x hx y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow hα.ne']
    · -- The first iterated derivative is the derivative, up to a linear isometry.
      have hD₁ : iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y =
          (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ u x - fderiv ℝ u y) := by
        ext m
        simp
      rw [hD₁, LinearIsometryEquiv.norm_map, ← hD x hx, ← hD y hy]
      exact (hop _).trans (hb₂ x (hWB hx) y (hWB hy) hxy)
/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): "after applying the appropriate translation".**
For `τ(x) = x − ξ`, `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)`.  `τ` and its
inverse `σ = (· + ξ)` are isometries, so they preserve `Hⁿ`, and `τ(S) = σ⁻¹(S)` for every set `S`;
null-measurability, countable rectifiability (via `τ(M₀)` and the Lipschitz maps `F_j − ξ`),
positivity, a.e.-measurability of `θ ∘ σ` and its integrability on `τ(M) ∩ K` (through the compact
set `σ(K) ⊆ U`) all transfer along `σ`. -/
theorem dohr_tv_exists_translate : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ ∀ y, V'.mult y = V.mult (y + ξ) := by
  intro n ℓ U V ξ
  -- Step 0: `τ = (· − ξ)` is an isometry, `σ = (· + ξ)` is an `Hⁿ`-measure-preserving measurable
  -- embedding, and `τ(S) = σ⁻¹(S)` for every set `S`.
  have himage : ∀ S : Set (Amb n ℓ), (fun x => x - ξ) '' S = (fun x => x + ξ) ⁻¹' S := by
    intro S
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + ξ, hy, add_sub_cancel_right y ξ⟩
  have hτ : Isometry (fun x : Amb n ℓ => x - ξ) := (IsometryEquiv.subRight ξ).isometry
  have hσ : MeasurePreserving (fun x : Amb n ℓ => x + ξ) μHE[n] μHE[n] :=
    (IsometryEquiv.addRight ξ).measurePreserving_euclideanHausdorffMeasure n
  have hσe : MeasurableEmbedding (fun x : Amb n ℓ => x + ξ) := measurableEmbedding_addRight ξ
  -- Steps 1–2: `V' = v(τ(M), θ ∘ σ)`; the two required equalities hold by definition.
  refine ⟨{
    carrier := (fun x => x - ξ) '' V.carrier
    mult := fun y => V.mult (y + ξ)
    carrier_subset := image_mono V.carrier_subset
    nullMeasurableSet_carrier := ?_
    countablyRectifiable := ?_
    mult_pos := ?_
    aemeasurable_mult := ?_
    integrableOn_mult := ?_ }, rfl, fun y => rfl⟩
  · -- Step 3: `τ(M) = σ⁻¹(M)` and `σ` is quasi-measure-preserving.
    rw [himage]
    exact V.nullMeasurableSet_carrier.preimage hσ.quasiMeasurePreserving
  · -- Step 4: translate the null set `M₀` and the Lipschitz pieces `F j` by `−ξ`.
    obtain ⟨M₀, hM₀, F, hF, hcov⟩ := V.countablyRectifiable
    refine ⟨(fun x => x - ξ) '' M₀, ?_, fun j z => F j z - ξ, fun j => ?_, ?_⟩
    · rw [hτ.euclideanHausdorffMeasure_image]
      exact hM₀
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨K, LipschitzWith.of_dist_le_mul fun z w =>
        (dist_sub_right (F j z) (F j w) ξ).le.trans (hK.dist_le_mul z w)⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov hx with h | h
      · exact Or.inl ⟨x, h, rfl⟩
      · obtain ⟨j, z, rfl⟩ := mem_iUnion.mp h
        exact Or.inr (mem_iUnion.mpr ⟨j, z, rfl⟩)
  · -- Step 5: `θ(x − ξ + ξ) = θ(x) > 0` for `x ∈ M`.
    rintro _ ⟨x, hx, rfl⟩
    show 0 < V.mult (x - ξ + ξ)
    rw [sub_add_cancel]
    exact V.mult_pos x hx
  · -- Step 6: `σ` is measure preserving from `Hⁿ⌞σ⁻¹(M)` to `Hⁿ⌞M`.
    rw [himage]
    exact V.aemeasurable_mult.comp_quasiMeasurePreserving
      (hσ.restrict_preimage_emb hσe V.carrier).quasiMeasurePreserving
  · -- Step 7: `σ(K)` is a compact subset of `U`, and `τ(M) ∩ K = σ⁻¹(M ∩ σ(K))`.
    intro K hK hKU
    have hσK : (fun x => x + ξ) '' K ⊆ U := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hKU hy
      simpa using hx
    have h := (hσ.integrableOn_comp_preimage hσe).2
      (V.integrableOn_mult _ (hK.image (continuous_add_const ξ)) hσK)
    rwa [preimage_inter, hσe.injective.preimage_image, ← himage] at h
/-- **Weight of a translated varifold** (Simon Ch. 4, 1.1; Ch. 5, proof of Theorem 7.1, p. 127:
"after applying the appropriate translation").  Let `τ(x) = x - ξ`.  If `V' = v(τ(M), θ(· + ξ))`,
then `μ_{V'} = τ_# μ_V`: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ` and
`τ_#(Hⁿ ⌞ M) = Hⁿ ⌞ τ(M)`; for measurable `S`, changing variables along `τ` gives
`μ_{V'}(S) = ∫_{τ⁻¹S} θ(x - ξ + ξ) d(Hⁿ ⌞ M)(x) = μ_V(τ⁻¹S)`. -/
theorem dohr_tv_weight_eq_map : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ))
    (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ),
    V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) →
    V'.weight = V.weight.map (fun x => x - ξ) := by
  intro n ℓ U U' V V' ξ hc hm
  -- `τ(x) = x - ξ` as a measurable equivalence `e` (inverse `y ↦ y + ξ`).
  let e : Amb n ℓ ≃ᵐ Amb n ℓ := MeasurableEquiv.subRight ξ
  -- Step 1: `τ` is an isometric bijection, so `τ_# Hⁿ = Hⁿ`.
  have h1 : (μHE[n] : Measure (Amb n ℓ)).map e = μHE[n] :=
    ((IsometryEquiv.subRight ξ).measurePreserving_euclideanHausdorffMeasure n).map_eq
  -- Step 2: `Hⁿ ⌞ τ(M) = (τ_# Hⁿ) ⌞ τ(M) = τ_#(Hⁿ ⌞ τ⁻¹(τ(M))) = τ_#(Hⁿ ⌞ M)`.
  have h2 : (μHE[n] : Measure (Amb n ℓ)).restrict V'.carrier =
      ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).map e := by
    have h := e.restrict_map (μHE[n] : Measure (Amb n ℓ)) (e '' V.carrier)
    rw [h1, Set.preimage_image_eq _ e.injective] at h
    rw [hc]
    exact h
  -- Step 3: compare `μ_{V'}` and `τ_# μ_V` on measurable sets `S`.
  show V'.weight = V.weight.map e
  ext S hS
  -- Step 4: `(τ_# μ_V)(S) = μ_V(τ⁻¹S) = ∫_{τ⁻¹S} θ d(Hⁿ ⌞ M)`.
  rw [e.map_apply]
  simp only [RectifiableVarifold.weight]
  rw [withDensity_apply _ (e.measurable hS)]
  -- Step 5: `μ_{V'}(S) = ∫_S θ' d(τ_#(Hⁿ ⌞ M)) = ∫_{τ⁻¹S} θ'(x - ξ) d(Hⁿ ⌞ M)(x)`.
  rw [withDensity_apply _ hS, h2, e.restrict_map, lintegral_map_equiv]
  -- Step 6: `θ'(x - ξ) = θ(x - ξ + ξ) = θ(x)`, so the two integrals agree.
  refine lintegral_congr fun x => ?_
  show ENNReal.ofReal (V'.mult (x - ξ)) = ENNReal.ofReal (V.mult x)
  rw [hm, sub_add_cancel]
/-- **Support of a translated measure** (used for Simon Ch. 5, Theorem 7.1, p. 127, where `V` is
translated by `τ(x) = x − ξ`).  For every measure `μ` on `ℝ^{n+ℓ}`, `spt (τ_# μ) = τ (spt μ)`.
`τ` is the measurable equivalence `MeasurableEquiv.subRight ξ`, so `(τ_# μ)(N) = μ(τ⁻¹ N)` for
every set `N`.  If `y ∈ spt (τ_# μ)` and `N` is a neighbourhood of `y + ξ`, then `σ⁻¹ N`
(`σ(x) = x + ξ`) is a neighbourhood of `y` and `μ N = (τ_# μ)(σ⁻¹ N) > 0`, so `y = τ(y + ξ)`
with `y + ξ ∈ spt μ`; conversely `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N`
of `τ(x)`. -/
theorem dohr_tv_support_map_sub : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (ξ : Amb n ℓ),
    (μ.map (fun x => x - ξ)).support = (fun x => x - ξ) '' μ.support := by
  intro n ℓ μ ξ
  -- `(τ_# μ)(N) = μ(τ⁻¹ N)` for every set `N`, measurable or not.
  have hmap : ∀ N : Set (Amb n ℓ), μ.map (fun x => x - ξ) N = μ ((fun x => x - ξ) ⁻¹' N) :=
    fun N => (MeasurableEquiv.subRight ξ).map_apply N
  ext y
  simp only [Measure.mem_support_iff_forall, hmap, mem_image]
  constructor
  · -- `y + ξ ∈ spt μ`: pull each neighbourhood `N` of `y + ξ` back along `σ`.
    intro hy
    refine ⟨y + ξ, fun N hN => ?_, add_sub_cancel_right y ξ⟩
    have h := hy ((fun x => x + ξ) ⁻¹' N)
      ((continuous_add_const ξ).continuousAt.preimage_mem_nhds hN)
    simpa [preimage_preimage] using h
  · -- `τ⁻¹ N` is a neighbourhood of `x` for every neighbourhood `N` of `τ(x)`.
    rintro ⟨x, hx, rfl⟩ N hN
    exact hx _ ((continuous_sub_right ξ).continuousAt.preimage_mem_nhds hN)
/-- Simon Ch. 5, proof of Theorem 7.1 (the translation `τ(x) = x − ξ` of `V = v(M, θ)`): if
`V'.carrier = τ(M)` and `V'.mult = θ(· + ξ)`, then `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` and
`V'.mult(y + r z) = θ((y + ξ) + r z)`, so the weighted approximate tangent predicates of `V'` at `y`
and of `V` at `y + ξ` coincide, and hence so do the classically chosen tangent projections. -/
theorem dohr_tv_tangentProj_eq : ∀ (n ℓ : ℕ) (U U' : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (V' : RectifiableVarifold n ℓ U') (ξ : Amb n ℓ), V'.carrier = (fun x => x - ξ) '' V.carrier → (∀ y, V'.mult y = V.mult (y + ξ)) → ∀ y, V'.tangentProj y = V.tangentProj (y + ξ) := by
  intro n ℓ U U' V V' ξ hM hθ y
  -- The blow-ups agree: `η_{y,r}(τ(M)) = η_{y+ξ,r}(M)` since `(x − ξ) − y = x − (y + ξ)`.
  have hblow : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap y r '' V'.carrier =
      Poincare.SimonGMT.Chapter03.blowUpMap (y + ξ) r '' V.carrier := by
    intro r
    rw [hM, Set.image_image]
    congr 1
    funext x
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, sub_sub, add_comm ξ y]
  -- The weights agree: `V'.mult(y + r z) = θ((y + ξ) + r z)`.
  have hw : ∀ (r : ℝ) (z : Amb n ℓ), V'.mult (y + r • z) = V.mult (y + ξ + r • z) := by
    intro r z
    rw [hθ, add_right_comm]
  -- Hence the weighted approximate tangent predicates of `V'` at `y` and of `V` at `y + ξ` agree.
  have hP :
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V'.carrier V'.mult y =
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult
          (y + ξ) := by
    funext P
    simp only [Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt, hblow, hw, hθ y]
  -- `tangentProj` only sees the tangent predicate, so equal predicates give equal projections.
  have key : ∀ A B : Submodule ℝ (Amb n ℓ) → Prop, A = B →
      @dite _ (∃ P, A P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => (0 : Amb n ℓ →L[ℝ] Amb n ℓ)) =
        @dite _ (∃ P, B P) (Classical.propDecidable _)
          (fun h => (Classical.choose h).starProjection) (fun _ => 0) := by
    rintro A B rfl
    rfl
  exact key _ _ hP
/-- **Generalized mean curvature under the translation `τ(x) = x − ξ`** (Simon Ch. 4, 3.14).  Let
`V'` be a rectifiable varifold in `τ(U)` with `μ_{V'} = τ_# μ_V` and `p_{T_y V'} = p_{T_{y+ξ} V}`
for every `y`.  If `V` has generalized mean curvature `H` in `U`, then `V'` has generalized mean
curvature `y ↦ H(y + ξ)` in `τ(U)`.
Proof: `τ` is a homeomorphism and a measurable embedding.  Local integrability moves along `τ`,
because `τ` maps `𝓝[U] x` onto `𝓝[τ(U)] τ(x)` and `H(· + ξ) ∘ τ = H`.  For `X ∈ C¹_c(τ(U))` the
field `Y = X ∘ τ` lies in `C¹_c(U)`, and `div_{M'} X(τ(x)) = div_M Y(x)` because
`DY(x) = DX(τ(x))`.  Changing variables in both first-variation integrals then gives the identity
for `V'`. -/
theorem dohr_tv_gmc_transfer : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U)), V'.weight = V.weight.map (fun x => x - ξ) → (∀ y, V'.tangentProj y = V.tangentProj (y + ξ)) → ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ V' hw htp H hH
  obtain ⟨hloc, hvar⟩ := hH
  -- `τ(x) = x − ξ` is a measurable embedding and a topological embedding.
  have hτm : MeasurableEmbedding (fun x : Amb n ℓ => x - ξ) := measurableEmbedding_subRight ξ
  have hτe : Topology.IsEmbedding (fun x : Amb n ℓ => x - ξ) := (Homeomorph.subRight ξ).isEmbedding
  refine ⟨?_, fun X hX hXc hXs => ?_⟩
  · -- Step 1: `H(· + ξ)` is locally integrable on `τ(U)`.  At `τ(x)`, `x ∈ U`, the filter
    -- `𝓝[τ(U)] τ(x)` is the image of `𝓝[U] x` under `τ`, and `H(· + ξ) ∘ τ = H`.
    rintro _ ⟨x, hxU, rfl⟩
    rw [hw, ← hτe.map_nhdsWithin_eq, hτm.integrableAtFilter_map_iff]
    simpa only [Function.comp_def, sub_add_cancel] using hloc x hxU
  · -- Step 2: the first variation of `V'`, tested against `X`, via the field `Y = X ∘ τ` on `U`.
    have hY : ContDiff ℝ 1 (fun x => X (x - ξ)) := hX.comp (contDiff_id.sub contDiff_const)
    have hYc : HasCompactSupport (fun x => X (x - ξ)) :=
      hXc.comp_homeomorph (Homeomorph.subRight ξ)
    have hYs : tsupport (fun x => X (x - ξ)) ⊆ U := by
      intro x hx
      have hx' : x - ξ ∈ tsupport X := by
        have h : x ∈ tsupport (X ∘ Homeomorph.subRight ξ) := hx
        rwa [tsupport_comp_eq_preimage] at h
      obtain ⟨u, hu, hux⟩ := hXs hx'
      rwa [← sub_left_injective hux]
    -- `div_{M'} X (x − ξ) = div_M Y x`: the tangent planes match and `DY(x) = DX(x − ξ)`.
    have hdiv : ∀ x, V'.divM X (x - ξ) = V.divM (fun x => X (x - ξ)) x := by
      intro x
      simp only [RectifiableVarifold.divM]
      rw [htp, sub_add_cancel, fderiv_comp_sub]
    calc ∫ y, V'.divM X y ∂V'.weight = ∫ x, V'.divM X (x - ξ) ∂V.weight := by
          rw [hw, hτm.integral_map]
      _ = ∫ x, V.divM (fun x => X (x - ξ)) x ∂V.weight := by simp only [hdiv]
      _ = -∫ x, inner ℝ (X (x - ξ)) (H x) ∂V.weight := hvar _ hY hYc hYs
      _ = -∫ y, inner ℝ (X y) (H (y + ξ)) ∂V'.weight := by
          rw [hw, hτm.integral_map]
          simp only [sub_add_cancel]
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one), steps 1–2: if
`Q(S − ξ) ∩ B̆_R(0) = Γ ∩ B̆_R(0)` for the graph `Γ = graph u` of a `C¹` map `u` on `B̆ⁿ_R(0)`
whose `Hⁿ`-density is `1` at each of its points, then `Hⁿ(S ∩ B̆_ρ(ξ)) < ∞` for `ρ < R` and `S`
has `Hⁿ`-density `1` at each point of `S ∩ B̆_R(ξ)`.  The isometry `T z = Q(z − ξ)` preserves
`Hⁿ`; `T(S ∩ B̆_ρ(ξ))` lies in the compact set `G(Bⁿ_ρ(0)) ⊆ Γ`, `G x = (x, u x)`, covered by
finitely many balls `B_r(G x)` with `Hⁿ(Γ ∩ B_r(G x)) < ∞`; and if `T y = G x`, then
`T(S ∩ B_r(y)) = Γ ∩ B_r(G x)` for `0 < r < R − |y − ξ|`. -/
theorem dohr_lmo_graph_support_density : ∀ n ℓ : ℕ, ∀ (S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ x ∈ ball (0 : Rn n) R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ ρ : ℝ, ρ < R → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball ξ ρ) < ⊤) ∧ ∀ y ∈ S ∩ ball ξ R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (S ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ S ξ R Q u hu hgraph hdens
  -- Step 0: `T z = Q (z - ξ)` is an isometry, so it preserves `Hⁿ`, and
  -- `T(S) ∩ B̆_R(0) = Γ ∩ B̆_R(0)` with `Γ = graph u`.
  have hT : ∀ X : Set (Amb n ℓ),
      (μHE[n] : Measure (Amb n ℓ)) (Q '' ((fun x => x - ξ) '' X)) = μHE[n] X := fun X => by
    rw [Q.isometry.euclideanHausdorffMeasure_image,
      (Isometry.of_dist_eq fun x y => dist_sub_right x y ξ).euclideanHausdorffMeasure_image]
  have hSΓ : ∀ z ∈ S, ‖z - ξ‖ < R → ∃ x ∈ ball (0 : Rn n) R, graphPoint x (u x) = Q (z - ξ) := by
    intro z hz hzR
    have hmem : Q (z - ξ) ∈ Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R :=
      ⟨⟨z - ξ, ⟨z, hz, rfl⟩, rfl⟩, by rwa [mem_ball_zero_iff, Q.norm_map]⟩
    rw [hgraph] at hmem
    exact hmem.1
  have hΓS : ∀ w ∈ graphOver u (ball 0 R), ‖w‖ < R → ∃ z ∈ S, Q (z - ξ) = w := by
    intro w hw hwR
    have hmem : w ∈ graphOver u (ball 0 R) ∩ ball 0 R := ⟨hw, mem_ball_zero_iff.2 hwR⟩
    rw [← hgraph] at hmem
    obtain ⟨⟨_, ⟨z, hz, rfl⟩, rfl⟩, -⟩ := hmem
    exact ⟨z, hz, rfl⟩
  refine ⟨fun ρ hρ => ?_, fun y hy => ?_⟩
  · -- (a) `T(S ∩ B̆_ρ(ξ)) ⊆ G(Bⁿ_ρ(0))` with `G x = (x, u x)`; this compact subset of `Γ` has
    -- finite measure since every point of it has a ball `B_r(G x)` with `Hⁿ(Γ ∩ B_r(G x)) < ∞`.
    have hKR : closedBall (0 : Rn n) ρ ⊆ ball 0 R := closedBall_subset_ball hρ
    have hnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖a‖ ≤ ‖graphPoint a b‖ := by
      intro a b
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_add]
      refine Real.sqrt_le_sqrt (le_add_of_le_of_nonneg (le_of_eq ?_)
        (Finset.sum_nonneg fun j _ => by positivity))
      simp [graphPoint]
    have hgp : Continuous fun p : Rn n × Rn ℓ => graphPoint p.1 p.2 := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      induction i using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_fst)
      | right j =>
        simp only [Fin.append_right]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
    have hGc : ContinuousOn (fun x => graphPoint x (u x)) (closedBall (0 : Rn n) ρ) :=
      hgp.comp_continuousOn (continuousOn_id.prodMk (hu.continuousOn.mono hKR))
    have hfin : (μHE[n] : Measure (Amb n ℓ))
        ((fun x => graphPoint x (u x)) '' closedBall (0 : Rn n) ρ) < ⊤ := by
      refine ((isCompact_closedBall 0 ρ).image_of_continuousOn hGc).measure_lt_top_of_nhdsWithin ?_
      rintro _ ⟨x, hxK, rfl⟩
      obtain ⟨r, hr2, hr0⟩ := (((hdens x (hKR hxK)).eventually_lt_const
        ENNReal.one_lt_two).and self_mem_nhdsWithin).exists
      refine ⟨graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r, ?_, ?_⟩
      · refine mem_nhdsWithin.2 ⟨ball (graphPoint x (u x)) r, isOpen_ball, mem_ball_self hr0, ?_⟩
        rintro _ ⟨hw, ⟨x', hx', rfl⟩⟩
        exact ⟨⟨x', hKR hx', rfl⟩, ball_subset_closedBall hw⟩
      · refine lt_top_iff_ne_top.2 fun htop => ?_
        rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
        exact not_top_lt hr2
    refine lt_of_le_of_lt ?_ hfin
    rw [← hT (S ∩ ball ξ ρ)]
    refine measure_mono ?_
    rintro _ ⟨_, ⟨z, ⟨hz, hzB⟩, rfl⟩, rfl⟩
    have hzρ : ‖z - ξ‖ < ρ := by rwa [mem_ball, dist_eq_norm] at hzB
    obtain ⟨x, -, hxe⟩ := hSΓ z hz (hzρ.trans hρ)
    refine ⟨x, mem_closedBall_zero_iff.2 ?_, hxe⟩
    calc ‖x‖ ≤ ‖graphPoint x (u x)‖ := hnorm x (u x)
      _ = ‖z - ξ‖ := by rw [hxe, Q.norm_map]
      _ ≤ ρ := hzρ.le
  · -- (b) `T y = G x` with `x ∈ B̆ⁿ_R(0)`; for `0 < r < R - |y - ξ|`,
    -- `T(S ∩ B_r(y)) = Γ ∩ B_r(G x)`, so the density ratios agree near `0`.
    obtain ⟨hyS, hyB⟩ := hy
    have hyR : ‖y - ξ‖ < R := by rwa [mem_ball, dist_eq_norm] at hyB
    obtain ⟨x, hx, hxy⟩ := hSΓ y hyS hyR
    refine (hdens x hx).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hyR)] with r hr
    have hset : graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r =
        Q '' ((fun x => x - ξ) '' (S ∩ closedBall y r)) := by
      ext w
      constructor
      · rintro ⟨hwΓ, hwB⟩
        rw [mem_closedBall, hxy] at hwB
        have hwR : ‖w‖ < R := by
          calc ‖w‖ = dist w 0 := (dist_zero_right w).symm
            _ ≤ dist w (Q (y - ξ)) + dist (Q (y - ξ)) 0 := dist_triangle _ _ _
            _ = dist w (Q (y - ξ)) + ‖y - ξ‖ := by rw [dist_zero_right, Q.norm_map]
            _ < R := by linarith [hr.2]
        obtain ⟨z, hz, rfl⟩ := hΓS w hwΓ hwR
        refine ⟨z - ξ, ⟨z, ⟨hz, ?_⟩, rfl⟩, rfl⟩
        rw [mem_closedBall, ← dist_sub_right z y ξ, ← Q.dist_map]
        exact hwB
      · rintro ⟨_, ⟨z, ⟨hz, hzB⟩, rfl⟩, rfl⟩
        rw [mem_closedBall] at hzB
        have hzR : ‖z - ξ‖ < R := by
          calc ‖z - ξ‖ = dist z ξ := (dist_eq_norm z ξ).symm
            _ ≤ dist z y + dist y ξ := dist_triangle _ _ _
            _ = dist z y + ‖y - ξ‖ := by rw [dist_eq_norm y ξ]
            _ < R := by linarith [hr.2]
        obtain ⟨x', hx', hx'e⟩ := hSΓ z hz hzR
        refine ⟨⟨x', hx', hx'e⟩, ?_⟩
        show Q (z - ξ) ∈ closedBall (graphPoint x (u x)) r
        rw [mem_closedBall, hxy, Q.dist_map, dist_sub_right]
        exact hzB
    rw [hset, hT]
/-- Graph tangent planes are `n`-dimensional `μ_V`-a.e. in the graph region.  `μ_V`-a.e. `y` lies in
`spt μ_V` (`Measure.support_mem_ae`), so for `y ∈ B̆_R(ξ)` the point `Q(y − ξ)` lies on the graph:
`Q(y − ξ) = G(x)` with `x ∈ B̆ⁿ_R(0)`, `G(z) = graphPoint z (u z)`.  By (TP) the tangent projection
at `y` is the projection onto `Q⁻¹(range DG(x))`.  `G` is differentiable at `x` coordinatewise, and
its first `n` coordinates are those of `z`, so by uniqueness of derivatives the first `n`
coordinates of `DG(x) v` are those of `v`; hence `DG(x)` is injective, `range DG(x)` has dimension
`n`, and so has its image under the linear equivalence `Q⁻¹`. -/
theorem dohr_lmo_graph_tangent_rank : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ball ξ R ⊆ U → DifferentiableOn ℝ u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection) → ∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj y = P.starProjection := by
  intro n ℓ U V ξ R Q u hball hdiff hgraph hTP
  filter_upwards [hTP, Measure.support_mem_ae (μ := V.weight)] with y hTPy hy hyR
  have hmem : Q (y - ξ) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R := by
    refine ⟨⟨y - ξ, ⟨y, ⟨hball hyR, hy⟩, rfl⟩, rfl⟩, ?_⟩
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
    exact hyR
  rw [hgraph] at hmem
  obtain ⟨⟨x, hx, hxy⟩, -⟩ := hmem
  have hux : DifferentiableAt ℝ u x := hdiff.differentiableAt (isOpen_ball.mem_nhds hx)
  have hG : DifferentiableAt ℝ (fun z : Rn n => graphPoint z (u z)) x := by
    rw [differentiableAt_euclidean]
    intro i
    induction i using Fin.addCases with
    | left j =>
      simpa [graphPoint] using (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x j).differentiableAt
    | right k => simpa [graphPoint] using differentiableAt_euclidean.mp hux k
  have hcoord : ∀ (j : Fin n) (v : Rn n),
      fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x v (Fin.castAdd ℓ j) = v j := by
    intro j v
    have h1 := (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (graphPoint x (u x))
      (Fin.castAdd ℓ j)).hasFDerivAt.comp x hG.hasFDerivAt
    have h2 : HasFDerivAt (fun z : Rn n => graphPoint z (u z) (Fin.castAdd ℓ j))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j) x := by
      simpa [graphPoint] using (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 x j).hasFDerivAt
    simpa using congrArg (fun L => L v) (h1.unique h2)
  have hinj : Function.Injective
      (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x : Rn n →ₗ[ℝ] Amb n ℓ) := by
    intro v w hvw
    ext j
    rw [← hcoord j v, ← hcoord j w]
    exact congrArg (fun z : Amb n ℓ => z (Fin.castAdd ℓ j)) hvw
  refine ⟨_, ?_, hTPy hyR x hx hxy.symm⟩
  rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one): the `Lᵖ` monotonicity
formula `hM` with an error `Λ(t) → 0`, uniformly for centres near `ξ`.  Put `κ = (p − n)/(4p)`,
`a = (∫_{B_R(ξ)} |H|ᵖ dμ_V)^{1/p} < ∞`, `Λ(t) = max {t^{(p−n)/p} a/κ, t}`, and choose `t₁ ≤ R/8`
with `Λ ≤ 1` on `(0, t₁]`.  For `y ∈ B̆_{R/2}(ξ)`, `t ∈ (0, t₁]` and `z ∈ B_t(y)` the ball
`B_t(z)` lies in `B̆_R(ξ)`, so `(t^{p−n} ∫_{B_t(z)} |H|ᵖ dμ_V)^{1/p} ≤ t^{(p−n)/p} a ≤ κ Λ(t)`
and `hM` applies at `(z, t, Λ(t))`; as `Φ` is nondecreasing on `(0, t)` with `Φ(r) → ω_n Θ`,
`ω_n Θ ≤ Φ(r) ≤ e^{Λ(t)} r⁻ⁿ μ_V(B_r(z)) + Λ(t)` for `r ∈ (0, t)`. -/
theorem dohr_lmo_uniform_monotonicity_bound : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ) (ξ : Amb n ℓ) (R : ℝ), (n : ℝ) < p → 0 < R → closedBall ξ R ⊆ U → (∀ (y : Amb n ℓ) (R' Λ : ℝ), 0 < R' → closedBall y R' ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R' → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R')) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R' ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R', |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R') ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t))) → (∀ᵐ x ∂V.weight, x ∈ ball ξ R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball ξ R)) → ∫⁻ x in closedBall ξ R, ‖H x‖ₑ ^ p ∂V.weight < ⊤ → ∃ t₁ > 0, ∃ Λ : ℝ → ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 0) ∧ ∀ y ∈ ball ξ (R / 2), ∀ t ∈ Ioc 0 t₁, ∀ z ∈ closedBall y t, ∃ Θ : ℝ, 0 ≤ Θ ∧ V.HasDensity z Θ ∧ ∀ r ∈ Ioo 0 t, unitBallVolume n * Θ ≤ Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + Λ t := by
  intro n ℓ U V H p ξ R hp hR hBU hM hTP hmeas hLp
  -- Step 1: `κ = (p - n)/(4p) > 0`, `β = (p - n)/p > 0` and `a = A^{1/p}`, where
  -- `A = ∫_{B_R(ξ)} |H|ᵖ dμ_V < ∞`.
  have hp0 : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hp
  have hpn : 0 < p - n := sub_pos.mpr hp
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  have hβ : 0 < (p - n) * (1 / p) := mul_pos hpn (by positivity)
  set κ : ℝ := (p - n) / (4 * p)
  have hκ : 0 < κ := div_pos hpn (by positivity)
  set A : ℝ≥0∞ := ∫⁻ x in closedBall ξ R, ‖H x‖ₑ ^ p ∂V.weight
  set a : ℝ := (A ^ (1 / p)).toReal
  have hAa : A ^ (1 / p) = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg hp1 hLp.ne)).symm
  -- Step 2: `Λ(t) = max (t^β a/κ) t`, which tends to `max 0 0 = 0` as `t → 0+`.
  set Λ : ℝ → ℝ := fun t => max (t ^ ((p - n) * (1 / p)) * a / κ) t
  have hΛlim : Tendsto Λ (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ ((p - n) * (1 / p)) * a / κ) (𝓝 0)
        (𝓝 ((0 : ℝ) ^ ((p - n) * (1 / p)) * a / κ)) :=
      (((Real.continuousAt_rpow_const 0 _ (Or.inr hβ.le)).tendsto).mul_const a).div_const κ
    have h2 := h1.max (tendsto_id (x := 𝓝 (0 : ℝ)))
    rw [Real.zero_rpow hβ.ne', zero_mul, zero_div, max_self] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  -- Step 3: `t₁ = min (R/8) (ε/2)`, where `Λ < 1` on `(0, ε)`.
  obtain ⟨ε, hε, hεsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hΛlim.eventually_lt_const one_pos)
  have hε0 : 0 < ε := hε
  refine ⟨min (R / 8) (ε / 2), lt_min (by positivity) (by positivity), Λ, hΛlim, ?_⟩
  intro y hy t ht z hz
  have ht0 : 0 < t := ht.1
  have htR : t ≤ R / 8 := ht.2.trans (min_le_left _ _)
  have htε : t < ε := lt_of_le_of_lt (ht.2.trans (min_le_right _ _)) (by linarith)
  have hΛ0 : 0 < Λ t := lt_of_lt_of_le ht0 (le_max_right _ _)
  have hΛ1 : Λ t ≤ 1 := (show Λ t < 1 from hεsub ⟨ht0, htε⟩).le
  -- Step 4: `B_t(z) ⊆ B̆_R(ξ)`, since `t + t + R/2 ≤ R/4 + R/2 < R`.
  have hsub : closedBall z t ⊆ ball ξ R := by
    intro w hw
    rw [mem_closedBall] at hw hz
    rw [mem_ball] at hy ⊢
    calc dist w ξ ≤ dist w z + dist z y + dist y ξ := dist_triangle4 w z y ξ
      _ < R := by linarith
  have hsubU : closedBall z t ⊆ U := hsub.trans (ball_subset_closedBall.trans hBU)
  have hsubo : ball z t ⊆ ball ξ R := ball_subset_closedBall.trans hsub
  -- Step 5: the hypotheses of `hM` at `(z, t, Λ(t))`.
  have hTP' : ∀ᵐ x ∂V.weight, x ∈ ball z t → ∃ P : Submodule ℝ (Amb n ℓ),
      Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection :=
    hTP.mono fun x hx hxb => hx (hsubo hxb)
  have hmeas' : AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball z t)) :=
    hmeas.mono_measure (Measure.restrict_mono hsubo le_rfl)
  -- `(t^{p-n} ∫_{B_t(z)} |H|ᵖ dμ_V)^{1/p} ≤ (t^{p-n} A)^{1/p} = t^β a ≤ κ Λ(t)`.
  have hLp' : V.scaledLpNorm H p z t ≤ ENNReal.ofReal (κ * Λ t) := by
    have hI : ∫⁻ x in closedBall z t, ‖H x‖ₑ ^ p ∂V.weight ≤ A :=
      lintegral_mono_set (hsub.trans ball_subset_closedBall)
    have htn : 0 ≤ t ^ (p - n) := Real.rpow_nonneg ht0.le _
    calc V.scaledLpNorm H p z t
        = (ENNReal.ofReal (t ^ (p - n)) * ∫⁻ x in closedBall z t, ‖H x‖ₑ ^ p ∂V.weight) ^
            (1 / p) := rfl
      _ ≤ (ENNReal.ofReal (t ^ (p - n)) * A) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hI) hp1
      _ = ENNReal.ofReal (t ^ (p - n)) ^ (1 / p) * A ^ (1 / p) :=
          ENNReal.mul_rpow_of_nonneg _ _ hp1
      _ = ENNReal.ofReal (t ^ ((p - n) * (1 / p)) * a) := by
          rw [ENNReal.ofReal_rpow_of_nonneg htn hp1, hAa,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg htn _), Real.rpow_mul ht0.le]
      _ ≤ ENNReal.ofReal (κ * Λ t) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : t ^ ((p - n) * (1 / p)) * a / κ ≤ Λ t := le_max_left _ _
          have h2 := (div_le_iff₀ hκ).mp h1
          linarith [mul_comm (Λ t) κ]
  -- Step 6: apply `hM` at `(z, t, Λ(t))`.
  obtain ⟨F, hFb, -, hFmono, Θ, hΘ0, hΘd, hΘlim⟩ :=
    hM z t (Λ t) ht0 hsubU hTP' hmeas' hΛ0 hΛ1 hLp'
  refine ⟨Θ, hΘ0, hΘd, fun r hr => ?_⟩
  -- Step 7: `ω_n Θ ≤ Φ(r)`, as `Φ` is nondecreasing on `(0, t)` and `Φ(r') → ω_n Θ` (`r' → 0+`).
  have h7 : unitBallVolume n * Θ ≤
      F r * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + F r - 1 := by
    refine le_of_tendsto hΘlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr.1] with r' hr'
    exact hFmono ⟨hr'.1, hr'.2.trans hr.2⟩ hr hr'.2.le
  -- Step 8: `Φ(r) ≤ e^{Λ(t)} r⁻ⁿ μ_V(B_r(z)) + Λ(t)`, by `F(r) ≤ e^{Λ(t)}`, `|F(r) - 1| ≤ Λ(t)`.
  obtain ⟨hF1, -, hF3⟩ := hFb r hr
  have hm : 0 ≤ (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.1.le n)) ENNReal.toReal_nonneg
  have h8 : F r * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal ≤
      Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hF3 hm
  linarith [le_abs_self (F r - 1)]
/-- Upper semicontinuity of the density at `y`, in the form used in steps 5 and 7 of the proof of
Simon Ch. 5, Theorem 7.1 (cf. Ch. 4, 3.11 and 4.9).  Put `ω = ω_n > 0`, `b = Θy + (c − Θy)/3` and
pick `ε ∈ (0, 1/2]` with `a := (1 + 2ε)ⁿ b < c`.  The density at `y` gives `σ₁ > 0` with
`μ_V(B_s(y)) ≤ b ω sⁿ` for `s ∈ (0, σ₁)`.  As `Λ(t) → 0`, some `t ∈ (0, t₁]` with `t < σ₁` has
`e^{Λ(t)} a + Λ(t)/ω < c`; take `d = εt`.  For `z ∈ B_d(y)`, the monotonicity bound at `z` with
`r = t/2` and `B_{t/2}(z) ⊆ B_{t/2 + εt}(y)` give
`ω Θ ≤ e^{Λ(t)} (t/2)⁻ⁿ μ_V(B_{t/2}(z)) + Λ(t) ≤ e^{Λ(t)} ω a + Λ(t)`, so `Θ < c`. -/
theorem dohr_lmo_density_usc : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y : Amb n ℓ) (t₁ : ℝ) (Λ : ℝ → ℝ), 0 < t₁ → Tendsto Λ (𝓝[>] 0) (𝓝 0) → (∀ t ∈ Ioc 0 t₁, ∀ z ∈ closedBall y t, ∃ Θ : ℝ, 0 ≤ Θ ∧ V.HasDensity z Θ ∧ ∀ r ∈ Ioo 0 t, unitBallVolume n * Θ ≤ Real.exp (Λ t) * (r ^ n)⁻¹ * (V.weight (closedBall z r)).toReal + Λ t) → ∀ Θy : ℝ, 0 ≤ Θy → V.HasDensity y Θy → ∀ c : ℝ, Θy < c → ∃ d > 0, ∀ z ∈ closedBall y d, ∃ Θ : ℝ, Θ < c ∧ V.HasDensity z Θ := by
  intro n ℓ U V y t₁ Λ ht₁ hΛ hmon Θy hΘy hy c hc
  -- `ω_n > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    apply div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    apply Real.Gamma_pos_of_pos
    positivity
  -- The levels `Θy < b < a' < c` and `ε ∈ (0, 1/2]` with `a := (1 + 2ε)ⁿ b < a'`.
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = Θy + (c - Θy) / 3 := ⟨_, rfl⟩
  obtain ⟨a', ha'_def⟩ : ∃ a' : ℝ, a' = Θy + 2 * (c - Θy) / 3 := ⟨_, rfl⟩
  have hb_pos : 0 < b := by rw [hb_def]; linarith
  have hΘb : Θy < b := by rw [hb_def]; linarith
  have hba' : b < a' := by rw [hb_def, ha'_def]; linarith
  have ha'c : a' < c := by rw [ha'_def]; linarith
  have hcont : Tendsto (fun ε : ℝ => (1 + 2 * ε) ^ n * b) (𝓝[>] 0) (𝓝 b) := by
    have h : Continuous (fun ε : ℝ => (1 + 2 * ε) ^ n * b) := by fun_prop
    have h0 := h.tendsto 0
    simp only [mul_zero, add_zero, one_pow, one_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hεev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + 2 * ε) ^ n * b < a' ∧ ε ∈ Ioc 0 (1 / 2) :=
    (hcont.eventually (eventually_lt_nhds hba')).and (Ioc_mem_nhdsGT (by norm_num))
  obtain ⟨ε, hεa, hε⟩ := hεev.exists
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (1 + 2 * ε) ^ n * b := ⟨_, rfl⟩
  have hac : a < c := by rw [ha_def]; linarith
  -- Mass bound at `y`: `μ_V(B_s(y)) ≤ b ω_n sⁿ` for `s ∈ (0, σ₁)`, from the density at `y`.
  have hlt : ENNReal.ofReal Θy < ENNReal.ofReal b :=
    (ENNReal.ofReal_lt_ofReal_iff hb_pos).2 hΘb
  obtain ⟨σ₁, hσ₁pos, hσ₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hy (Iio_mem_nhds hlt))
  have hσ₁pos' : (0 : ℝ) < σ₁ := hσ₁pos
  have hmass : ∀ s ∈ Ioo 0 σ₁,
      V.weight (closedBall y s) ≤ ENNReal.ofReal (b * (unitBallVolume n * s ^ n)) := by
    intro s hs
    have h := hσ₁ hs
    simp only [mem_preimage, mem_Iio] at h
    have hne0 : ENNReal.ofReal (unitBallVolume n * s ^ n) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos hω (pow_pos hs.1 n)
    rw [ENNReal.div_lt_iff (Or.inl hne0) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul hb_pos.le] at h
    exact h.le
  -- Choice of `t ∈ (0, t₁]` with `t < σ₁` and `e^{Λ(t)} a + Λ(t)/ω_n < c`; then `d := ε t`.
  have hlim : Tendsto (fun t => Real.exp (Λ t) * a + Λ t / unitBallVolume n) (𝓝[>] 0)
      (𝓝 (Real.exp 0 * a + 0 / unitBallVolume n)) :=
    (((Real.continuous_exp.tendsto 0).comp hΛ).mul_const a).add (hΛ.div_const _)
  rw [Real.exp_zero, one_mul, zero_div, add_zero] at hlim
  obtain ⟨t, ⟨htc, ht⟩, htσ⟩ :=
    (((hlim.eventually (eventually_lt_nhds hac)).and (Ioc_mem_nhdsGT ht₁)).and
      (Ioo_mem_nhdsGT hσ₁pos')).exists
  have ht0 : 0 < t := ht.1
  refine ⟨ε * t, mul_pos hε.1 ht0, ?_⟩
  -- For `z ∈ B_{εt}(y) ⊆ B_t(y)`: the monotonicity bound at `z` with `r := t/2`.
  intro z hz
  have hzy : dist z y ≤ ε * t := mem_closedBall.1 hz
  have hεt : ε * t ≤ t / 2 := by
    have := mul_le_mul_of_nonneg_right hε.2 ht0.le
    linarith
  have hzt : z ∈ closedBall y t := mem_closedBall.2 (by linarith)
  obtain ⟨Θ, -, hΘz, hΘbound⟩ := hmon t ht z hzt
  refine ⟨Θ, ?_, hΘz⟩
  have key := hΘbound (t / 2) ⟨by linarith, by linarith⟩
  -- `B_{t/2}(z) ⊆ B_s(y)` with `s := t/2 + εt = (1 + 2ε) t/2 ≤ t < σ₁`, so
  -- `(t/2)⁻ⁿ μ_V(B_{t/2}(z)) ≤ (t/2)⁻ⁿ b ω_n sⁿ = ω_n a`.
  have hs : t / 2 + ε * t ∈ Ioo 0 σ₁ := by
    have := mul_pos hε.1 ht0
    exact ⟨by linarith, by linarith [htσ.2]⟩
  have hsub : closedBall z (t / 2) ⊆ closedBall y (t / 2 + ε * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hle := (measure_mono hsub).trans (hmass _ hs)
  have hreal : (V.weight (closedBall z (t / 2))).toReal ≤
      b * (unitBallVolume n * (t / 2 + ε * t) ^ n) :=
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hb_pos.le (mul_nonneg hω.le (pow_nonneg hs.1.le n))) hle
  have hs_eq : (t / 2 + ε * t) ^ n = (t / 2) ^ n * (1 + 2 * ε) ^ n := by
    rw [← mul_pow]; congr 1; ring
  have hpow : 0 < (t / 2) ^ n := pow_pos (by linarith) n
  have h6 : ((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal ≤ unitBallVolume n * a := by
    rw [inv_mul_le_iff₀ hpow]
    calc (V.weight (closedBall z (t / 2))).toReal
        ≤ b * (unitBallVolume n * (t / 2 + ε * t) ^ n) := hreal
      _ = (t / 2) ^ n * (unitBallVolume n * a) := by rw [hs_eq, ha_def]; ring
  -- Hence `ω_n Θ ≤ e^{Λ(t)} ω_n a + Λ(t)`, i.e. `Θ ≤ e^{Λ(t)} a + Λ(t)/ω_n < c`.
  have h7 : unitBallVolume n * Θ ≤ Real.exp (Λ t) * (unitBallVolume n * a) + Λ t :=
    calc unitBallVolume n * Θ
        ≤ Real.exp (Λ t) * ((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal + Λ t := key
      _ = Real.exp (Λ t) * (((t / 2) ^ n)⁻¹ * (V.weight (closedBall z (t / 2))).toReal) + Λ t := by
          ring
      _ ≤ Real.exp (Λ t) * (unitBallVolume n * a) + Λ t := by
          gcongr
  have h8 : Θ ≤ Real.exp (Λ t) * a + Λ t / unitBallVolume n :=
    calc Θ ≤ (Real.exp (Λ t) * (unitBallVolume n * a) + Λ t) / unitBallVolume n :=
          (le_div_iff₀' hω).2 h7
      _ = Real.exp (Λ t) * a + Λ t / unitBallVolume n := by
          rw [add_div, mul_div_assoc, mul_div_cancel_left₀ a hω.ne']
  linarith
/-- **Besicovitch differentiation of a density measure against a gauge** (a step in the proof of
Simon Ch. 5, Theorem 7.1, second assertion: density equals multiplicity a.e.).  If `ν` is a locally
finite measure on `ℝ^{n+ℓ}`, `f` is `ν`-a.e. measurable and `ν ⌞ f` (`ν.withDensity f`) is locally
finite, then for `ν`-a.e. `y` and every gauge `c` with `ν(B_r(y)) / c(r) → 1` as `r ↓ 0`, also
`(ν ⌞ f)(B_r(y)) / c(r) → f(y)`.
Proof: Besicovitch differentiation gives `(ν ⌞ f)(B_r(y)) / ν(B_r(y)) → D_ν(ν ⌞ f)(y) = f(y)` for
`ν`-a.e. `y`.  For such `y`, eventually `ν(B_r(y)) / c(r) > 0`, so `ν(B_r(y)) ≠ 0`, while
`ν(B_r(y)) < ∞` (closed balls are compact); hence
`(ν ⌞ f)(B_r(y)) / c(r) = [(ν ⌞ f)(B_r(y)) / ν(B_r(y))] · [ν(B_r(y)) / c(r)] → f(y) · 1`. -/
theorem dohr_lmo_dema_withDensity_density_ae : ∀ n ℓ : ℕ, ∀ (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ≥0∞), IsLocallyFiniteMeasure ν → IsLocallyFiniteMeasure (ν.withDensity f) → AEMeasurable f ν → ∀ᵐ y ∂ν, ∀ c : ℝ → ℝ≥0∞, Tendsto (fun r : ℝ => ν (closedBall y r) / c r) (𝓝[>] 0) (𝓝 1) → Tendsto (fun r : ℝ => (ν.withDensity f) (closedBall y r) / c r) (𝓝[>] 0) (𝓝 (f y)) := by
  intro n ℓ ν f hν hρ hf
  -- Besicovitch differentiation of `ν ⌞ f` with respect to `ν` (σ-finite, being locally finite),
  -- and `D_ν(ν ⌞ f) = f` `ν`-a.e.
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.withDensity f) ν,
    Measure.rnDeriv_withDensity₀ ν hf] with y hy hfy c hc
  rw [hfy] at hy
  -- Eventually `ν(B_r(y)) / c(r) > 0`, so `0 < ν(B_r(y)) < ∞` and the ratio factors.
  have heq : (fun r : ℝ => (ν.withDensity f) (closedBall y r) / ν (closedBall y r) *
      (ν (closedBall y r) / c r)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun r : ℝ => (ν.withDensity f) (closedBall y r) / c r := by
    filter_upwards [hc.eventually (lt_mem_nhds zero_lt_one)] with r hr
    exact ENNReal.div_mul_div_cancel (ENNReal.div_pos_iff.1 hr).1 measure_closedBall_lt_top.ne
  -- The two factors tend to `f(y)` and `1`.
  have hlim := ENNReal.Tendsto.mul hy (Or.inr ENNReal.one_ne_top) hc (Or.inl one_ne_zero)
  rw [mul_one] at hlim
  exact hlim.congr' heq
/-- The weight measure restricted to a measurable `O ⊆ U` is `Hⁿ` on `spt V ∩ O` with density
`1_M θ`: `μ_V ⌞ O = (Hⁿ ⌞ (spt V ∩ O)).withDensity (ofReal ∘ 1_M θ)`.
Proof: `spt V ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is measurable since `spt μ_V` is closed, and
`μ_V((spt μ_V)ᶜ) = 0`, so `μ_V(S ∩ O) = μ_V(S ∩ (spt V ∩ O))` for measurable `S`.  Both sides then
equal `∫ θ dHⁿ` over `S ∩ (spt V ∩ O) ∩ M`, by `withDensity_apply`, `restrict_restrict` and, on
the right, `lintegral_indicator₀`/`restrict_restrict₀` for the `Hⁿ`-null-measurable carrier `M`. -/
theorem dohr_lmo_dema_weight_restrict_withDensity : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → O ⊆ U → V.weight.restrict O = ((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)).withDensity (fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)) := by
  intro n ℓ U V O hO hOU
  -- `spt V ∩ O = spt μ_V ∩ O` is measurable.
  have hA : V.support ∩ O = V.weight.support ∩ O := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hOU hx.2, hx.1⟩, hx.2⟩⟩
  have hAm : MeasurableSet (V.support ∩ O) := by
    rw [hA]
    exact V.weight.isClosed_support.measurableSet.inter hO
  ext S hS
  have hSA : MeasurableSet (S ∩ (V.support ∩ O)) := hS.inter hAm
  rw [Measure.restrict_apply hS, withDensity_apply _ hS, Measure.restrict_restrict hS]
  -- `μ_V` vanishes off its support, so `μ_V(S ∩ O) = μ_V(S ∩ (spt V ∩ O))`.
  have hSO : V.weight (S ∩ O) = V.weight (S ∩ (V.support ∩ O)) := by
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ inter_subset_right))
    calc V.weight (S ∩ O)
        ≤ V.weight (S ∩ (V.support ∩ O) ∪ V.weight.supportᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hx' : x ∈ V.weight.support
          · exact Or.inl ⟨hx.1, hA ▸ ⟨hx', hx.2⟩⟩
          · exact Or.inr hx'
      _ ≤ V.weight (S ∩ (V.support ∩ O)) + V.weight V.weight.supportᶜ := measure_union_le _ _
      _ = V.weight (S ∩ (V.support ∩ O)) := by rw [Measure.measure_compl_support, add_zero]
  rw [hSO, RectifiableVarifold.weight, withDensity_apply _ hSA, Measure.restrict_restrict hSA]
  -- On the right, `ofReal (1_M θ) = 1_M (ofReal ∘ θ)` and `M` is null-measurable.
  have hf : (fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)) =
      V.carrier.indicator (fun x => ENNReal.ofReal (V.mult x)) := by
    funext x
    by_cases hx : x ∈ V.carrier <;> simp [hx]
  have hM : NullMeasurableSet V.carrier
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ (V.support ∩ O))) :=
    V.nullMeasurableSet_carrier.mono Measure.restrict_le_self
  rw [hf, lintegral_indicator₀ hM, Measure.restrict_restrict₀ hM, inter_comm]
/-- Simon Ch. 5, 7.1, second assertion (local multiplicity step): **density equals multiplicity
almost everywhere**.  Let `O = B̆_{r₀}(y₀)` with `B_{r₀}(y₀) ⊆ U`, write `Σ = spt V`, and suppose
`Hⁿ(Σ ∩ O) < ∞` and `Hⁿ(Σ ∩ B_r(y)) / (ω_n rⁿ) → 1` as `r ↓ 0` for every `y ∈ Σ ∩ O`.  Then
(a) `Θⁿ(μ_V, y) = θ(y)` for `μ_V`-a.e. `y ∈ O`, and (b) `Θⁿ(μ_V, y) = 0` for `Hⁿ`-a.e.
`y ∈ (Σ ∩ O) \ M`.  With `ν = Hⁿ ⌞ (Σ ∩ O)` and `f = 1_M θ` we have `μ_V ⌞ O = ν ⌞ f`, so
Besicovitch differentiation together with the unit density of `ν` gives `Θⁿ(μ_V, y) = f(y)` for
`ν`-a.e. `y`; this is (b), and (a) follows because `μ_V ⌞ O ≪ ν` and `μ_V` is carried by `M`. -/
theorem dohr_lmo_density_eq_mult_ae : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (y₀ : Amb n ℓ) (r₀ : ℝ), closedBall y₀ r₀ ⊆ U → (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ ball y₀ r₀) < ⊤ → (∀ y ∈ V.support ∩ ball y₀ r₀, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (V.support ∩ closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1)) → (∀ᵐ y ∂V.weight, y ∈ ball y₀ r₀ → V.HasDensity y (V.mult y)) ∧ ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball y₀ r₀)), y ∉ V.carrier → V.HasDensity y 0 := by
  intro n ℓ U V y₀ r₀ hBU hfin hdens
  -- Notation: `O = B̆_{r₀}(y₀)`, `ν = Hⁿ ⌞ (Σ ∩ O)` and `f = ofReal ∘ 1_M θ`.
  set O : Set (Amb n ℓ) := ball y₀ r₀
  set ν : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O) with hν_def
  set f : Amb n ℓ → ℝ≥0∞ := fun x => ENNReal.ofReal (V.carrier.indicator V.mult x)
  have hOm : MeasurableSet O := measurableSet_ball
  have hOU : O ⊆ U := ball_subset_closedBall.trans hBU
  -- Step 1: `μ_V ⌞ O = ν ⌞ f`.
  have hrestr : V.weight.restrict O = ν.withDensity f :=
    Submission.dohr_lmo_dema_weight_restrict_withDensity n ℓ U V O hOm hOU
  -- Step 2: `ν` is finite by hypothesis, and `μ_V ⌞ O` is finite because `θ` is integrable on
  -- `M ∩ B_{r₀}(y₀)` (`B_{r₀}(y₀) ⊆ U` is compact); `f` is `ν`-a.e. measurable.
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin.ne
  have hBfin : V.weight (closedBall y₀ r₀) < ⊤ := by
    unfold RectifiableVarifold.weight
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall _ _) hBU).lintegral_lt_top
  have : IsFiniteMeasure (ν.withDensity f) := by
    rw [← hrestr]
    exact isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono ball_subset_closedBall) hBfin).ne
  have hfm : AEMeasurable f ν :=
    (((aemeasurable_indicator_iff₀ V.nullMeasurableSet_carrier).mpr
      V.aemeasurable_mult).mono_measure Measure.restrict_le_self).ennreal_ofReal
  -- `Σ ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is a Borel set.
  have hAm : MeasurableSet (V.support ∩ O) := by
    have hA : V.support ∩ O = V.weight.support ∩ O := by
      ext x
      simp only [RectifiableVarifold.support, mem_inter_iff]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hOU h.2, h.1⟩, h.2⟩⟩
    rw [hA]
    exact Measure.isClosed_support.measurableSet.inter hOm
  -- Step 3: `Θⁿ(μ_V, y) = f(y)` for `ν`-a.e. `y`, using the gauge `c(r) = ω_n rⁿ`: for
  -- `0 < r < r₀ - |y - y₀|` we have `B_r(y) ⊆ O`, so `ν(B_r(y)) = Hⁿ(Σ ∩ B_r(y))` and
  -- `(ν ⌞ f)(B_r(y)) = μ_V(B_r(y))`.
  have hmain : ∀ᵐ y ∂ν, V.HasDensity y (V.carrier.indicator V.mult y) := by
    filter_upwards [Submission.dohr_lmo_dema_withDensity_density_ae n ℓ ν f inferInstance
      inferInstance hfm, (ae_restrict_mem hAm : ∀ᵐ y ∂ν, y ∈ V.support ∩ O)] with y hy hyA
    have hδ : 0 < r₀ - dist y y₀ := sub_pos.mpr (mem_ball.mp hyA.2)
    have hsub : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall y r ⊆ O := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
      exact closedBall_subset_ball' (by linarith [hr.2])
    have hν1 : Tendsto (fun r : ℝ => ν (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n))
        (𝓝[>] 0) (𝓝 1) := by
      refine (hdens y hyA).congr' ?_
      filter_upwards [hsub] with r hr
      have hBr : closedBall y r ∩ (V.support ∩ O) = V.support ∩ closedBall y r := by
        ext x
        simp only [mem_inter_iff]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, hr h.2⟩⟩
      rw [hν_def, Measure.restrict_apply measurableSet_closedBall, hBr]
    refine (hy (fun r : ℝ => ENNReal.ofReal (unitBallVolume n * r ^ n)) hν1).congr' ?_
    filter_upwards [hsub] with r hr
    rw [← hrestr, Measure.restrict_apply measurableSet_closedBall, Set.inter_eq_left.mpr hr]
  refine ⟨?_, ?_⟩
  · -- (a): `μ_V ⌞ O ≪ ν` transfers Step 3 to `μ_V`-a.e. `y ∈ O`, and `μ_V`-a.e. `y` lies in `M`.
    have hM : ∀ᵐ y ∂V.weight, y ∈ V.carrier :=
      (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
    have hO : ∀ᵐ y ∂V.weight.restrict O, V.HasDensity y (V.carrier.indicator V.mult y) := by
      rw [hrestr]
      exact (withDensity_absolutelyContinuous ν f).ae_le hmain
    filter_upwards [(ae_restrict_iff' hOm).mp hO, hM] with y hy hyM hyO
    have h := hy hyO
    rwa [Set.indicator_of_mem hyM] at h
  · -- (b): off `M` the density `1_M θ` vanishes.
    filter_upwards [hmain] with y hy hyM
    rwa [Set.indicator_of_notMem hyM] at hy
/-- `μ_V`-null subsets of the carrier are `Hⁿ`-null: if `A ⊆ M` and `μ_V(A) = 0`, then
`Hⁿ(A) = 0`.  `μ_V = Hⁿ ⌞ M` with density `θ`, so `μ_V(A) = 0` forces `θ = 0` `Hⁿ ⌞ M`-a.e. on `A`;
as `θ > 0` on `M ⊇ A`, the set `A` itself is `Hⁿ ⌞ M`-null, hence `Hⁿ`-null. -/
theorem dohr_lmo_hausdorff_null_of_weight_null : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (A : Set (Amb n ℓ)), A ⊆ V.carrier → V.weight A = 0 → (μHE[n] : Measure (Amb n ℓ)) A = 0 := by
  intro n ℓ U V A hA hw
  -- `μ_V(A) = 0` with the a.e.-measurable density `ofReal ∘ θ`: `{θ > 0} ∩ A` is `Hⁿ ⌞ M`-null.
  have h0 : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier)
      ({x | ENNReal.ofReal (V.mult x) ≠ 0} ∩ A) = 0 :=
    (withDensity_apply_eq_zero' V.aemeasurable_mult.ennreal_ofReal).mp hw
  -- `A` lies in this set and in `M`, since `A ⊆ M` and `θ > 0` on `M`.
  have hsub : A ⊆ ({x | ENNReal.ofReal (V.mult x) ≠ 0} ∩ A) ∩ V.carrier := fun x hx =>
    ⟨⟨(ENNReal.ofReal_pos.mpr (V.mult_pos x (hA hx))).ne', hx⟩, hA hx⟩
  exact measure_mono_null hsub (nonpos_iff_eq_zero.mp ((Measure.le_restrict_apply _ _).trans h0.le))
/-- Carrier versus support (step 6 of the local multiplicity-one argument for Simon 7.1): let
`O ⊆ U` be measurable, let `Hⁿ`-a.e. point of `spt V ∩ O` off `M` have density `0`, and let
every point of `spt V ∩ O` have a density `Θ ≥ 1`. Then `Hⁿ((M ∩ O) ∆ (spt V ∩ O)) = 0`.
`(M ∩ O) \ spt V` lies outside `spt μ_V`, so it is `μ_V`-null; since it lies inside `M`, the
sibling `dohr_lmo_hausdorff_null_of_weight_null` makes it `Hⁿ`-null. On `(spt V ∩ O) \ M`,
`Hⁿ`-a.e. point would have both density `0` and density `Θ ≥ 1`, which uniqueness of limits
rules out. -/
theorem dohr_lmo_carrier_support_null : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → O ⊆ U → (∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)), y ∉ V.carrier → V.HasDensity y 0) → (∀ y ∈ V.support ∩ O, ∃ Θ : ℝ, 1 ≤ Θ ∧ V.HasDensity y Θ) → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ O) (V.support ∩ O)) = 0 := by
  intro n ℓ U V O hO hOU hzero hdens
  rw [Set.symmDiff_def]
  refine measure_union_null ?_ ?_
  · -- `(M ∩ O) \ (spt V ∩ O)` lies in `M` and, as `O ⊆ U`, outside `spt μ_V`.
    refine Submission.dohr_lmo_hausdorff_null_of_weight_null n ℓ U V _ (fun x hx => hx.1.1)
      (measure_mono_null ?_ (Measure.measure_compl_support (μ := V.weight)))
    rintro x ⟨⟨-, hxO⟩, hxS⟩ hxμ
    exact hxS ⟨⟨hOU hxO, hxμ⟩, hxO⟩
  · -- `spt V ∩ O = spt μ_V ∩ O` (as `O ⊆ U`) is measurable.
    have hmeas : MeasurableSet (V.support ∩ O) := by
      have h : V.support ∩ O = V.weight.support ∩ O := by
        ext x
        exact ⟨fun ⟨⟨_, hx⟩, hxO⟩ => ⟨hx, hxO⟩, fun ⟨hx, hxO⟩ => ⟨⟨hOU hxO, hx⟩, hxO⟩⟩
      rw [h]
      exact (Measure.isClosed_support (μ := V.weight)).measurableSet.inter hO
    -- A.e. point of `spt V ∩ O` lies in `M`: off `M` it would have densities `0` and `Θ ≥ 1`.
    have hae : ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)), y ∈ V.carrier := by
      filter_upwards [ae_restrict_mem hmeas, hzero] with y hy hy0
      by_contra hyM
      obtain ⟨Θ, hΘ, hyΘ⟩ := hdens y hy
      have h := tendsto_nhds_unique (hy0 hyM) hyΘ
      rw [ENNReal.ofReal_zero, eq_comm, ENNReal.ofReal_eq_zero] at h
      linarith
    refine measure_mono_null (t := V.carrierᶜ ∩ (V.support ∩ O)) ?_ ?_
    · rintro x ⟨hx, hxM⟩
      exact ⟨fun h => hxM ⟨h, hx.2⟩, hx⟩
    · exact nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans (ae_iff.1 hae).le)
/-- **`μ_V ⌞ O = Hⁿ ⌞ (spt V ∩ O)` where `θ = 1`** (node
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.weight_restrict_eq-a1`; step 10 of
`dohr_local_multiplicity_one`).  If `θ = 1` `μ_V`-a.e. on the measurable set `O` and
`Hⁿ((M ∩ O) ∆ (spt V ∩ O)) = 0`, then `μ_V ⌞ O = Hⁿ ⌞ (spt V ∩ O)`.

`N = {x ∈ M ∩ O : θ(x) ≠ 1}` is `μ_V`-null, hence `Hⁿ`-null by
`dohr_lmo_hausdorff_null_of_weight_null`.  For measurable `S`,
`μ_V(S ∩ O) = ∫_{S ∩ O ∩ M} θ dHⁿ = Hⁿ(S ∩ O ∩ M)` since `θ = 1` `Hⁿ`-a.e. on `S ∩ O ∩ M`, and
`Hⁿ(S ∩ O ∩ M) = Hⁿ(S ∩ (spt V ∩ O))` since `M ∩ O = spt V ∩ O` up to an `Hⁿ`-null set. -/
theorem dohr_lmo_weight_restrict_eq : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → (∀ᵐ x ∂V.weight, x ∈ O → V.mult x = 1) → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ O) (V.support ∩ O)) = 0 → V.weight.restrict O = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O) := by
  intro n ℓ U V O hO hθ hsd
  /- Step 1: `N = {x ∈ M ∩ O : θ(x) ≠ 1}` is `μ_V`-null, hence `Hⁿ`-null. -/
  have hNw : V.weight {x | x ∈ V.carrier ∩ O ∧ V.mult x ≠ 1} = 0 := by
    have hθ' := ae_iff.1 hθ
    refine measure_mono_null ?_ hθ'
    intro x hx
    show ¬(x ∈ O → V.mult x = 1)
    exact fun h' => hx.2 (h' hx.1.2)
  have hNH : (μHE[n] : Measure (Amb n ℓ)) {x | x ∈ V.carrier ∩ O ∧ V.mult x ≠ 1} = 0 :=
    Submission.dohr_lmo_hausdorff_null_of_weight_null n ℓ U V _ (fun x hx => hx.1.1) hNw
  ext S hS
  /- Step 2: `μ_V(S ∩ O) = ∫_{S ∩ O ∩ M} θ dHⁿ`. -/
  have hSO : MeasurableSet (S ∩ O) := hS.inter hO
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS, RectifiableVarifold.weight,
    withDensity_apply _ hSO, Measure.restrict_restrict hSO]
  /- Step 3: `θ = 1` `Hⁿ`-a.e. on `S ∩ O ∩ M`, so the integral is `Hⁿ(S ∩ O ∩ M)`. -/
  have hX : NullMeasurableSet (S ∩ O ∩ V.carrier) (μHE[n] : Measure (Amb n ℓ)) :=
    hSO.nullMeasurableSet.inter V.nullMeasurableSet_carrier
  have h1 : ∀ᵐ x ∂(μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O ∩ V.carrier),
      ENNReal.ofReal (V.mult x) = 1 := by
    filter_upwards [ae_restrict_mem₀ hX,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hNH)] with x hxX hxN
    have hx1 : V.mult x = 1 := by
      by_contra h
      exact hxN ⟨⟨hxX.2, hxX.1.2⟩, h⟩
    rw [hx1, ENNReal.ofReal_one]
  rw [lintegral_congr_ae h1, setLIntegral_one]
  /- Steps 4–5: `S ∩ O ∩ M = S ∩ (spt V ∩ O)` up to the `Hⁿ`-null `(M ∩ O) ∆ (spt V ∩ O)`. -/
  have h2 : S ∩ (V.carrier ∩ O) =ᵐ[(μHE[n] : Measure (Amb n ℓ))] S ∩ (V.support ∩ O) :=
    EventuallyEqSet.rfl.inter (measure_symmDiff_eq_zero_iff.1 hsd)
  rw [inter_assoc, inter_comm O]
  exact measure_congr h2
/-- Simon Ch. 5, 7.1 (second assertion, local multiplicity one): carrier versus graph on
`B̆_ρ(0)`.  Put `τ z = z − ξ`; `Q ∘ τ` is an isometry.  If `Q(τ(S)) ∩ B̆_R(0)` is the graph of `u`
over `B̆ⁿ_R(0)` (inside `B̆_R(0)`), `s ≤ R` and `Hⁿ((M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))) = 0`, then for
`ρ ∈ (0, s]` the set `Q(τ(M)) ∩ B̆_ρ(0)` agrees `Hⁿ`-a.e. with the graph of `u` over
`{x ∈ B̆ⁿ_ρ(0) : |(x, u(x))| < ρ}`: by `|x| ≤ |(x, u(x))|`, their symmetric difference lies in
`Q(τ((M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))))`, which is `Hⁿ`-null. -/
theorem dohr_lmo_carrier_graph_symmDiff : ∀ n ℓ : ℕ, ∀ (M S : Set (Amb n ℓ)) (ξ : Amb n ℓ) (R s : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), s ≤ R → Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (M ∩ ball ξ s) (S ∩ ball ξ s)) = 0 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' M) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0 := by
  intro n ℓ M S ξ R s Q u hsR hgraph hnull ρ hρ hρs
  -- `‖x‖ ≤ ‖(x, y)‖`, since `‖(x, y)‖² = ‖x‖² + ‖y‖²`.
  have hnorm : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := by
    intro x y
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    rw [Fin.sum_univ_add]
    simp only [graphPoint, PiLp.toLp_apply, Fin.append_left, Fin.append_right]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  -- `‖Q (z - ξ)‖ = ‖z - ξ‖`.
  have hQ : ∀ z : Amb n ℓ, ‖Q (z - ξ)‖ = ‖z - ξ‖ := fun z => Q.norm_map _
  -- The set in the claim lies in `Q (τ (Z))`, `Z = (M ∩ B̆_s(ξ)) ∆ (S ∩ B̆_s(ξ))`, `τ z = z - ξ`.
  have hsub : symmDiff (Q '' ((fun x => x - ξ) '' M) ∩ ball 0 ρ)
      (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ}) ⊆
      Q '' ((fun x => x - ξ) '' symmDiff (M ∩ ball ξ s) (S ∩ ball ξ s)) := by
    intro w hw
    rcases mem_symmDiff.mp hw with ⟨⟨⟨_, ⟨z, hzM, rfl⟩, rfl⟩, hwρ⟩, hwG⟩ | ⟨⟨x, hxW, rfl⟩, hwM⟩
    · -- `w = Q (z - ξ)` with `z ∈ M`, `‖z - ξ‖ < ρ`, and `w` off the graph part.
      rw [mem_ball_zero_iff, hQ] at hwρ
      refine ⟨z - ξ, ⟨z, mem_symmDiff.mpr (Or.inl ⟨⟨hzM, ?_⟩, ?_⟩), rfl⟩, rfl⟩
      · exact mem_ball_iff_norm.mpr (hwρ.trans_le hρs)
      · rintro ⟨hzS, -⟩
        have hw : Q (z - ξ) ∈ Q '' ((fun x => x - ξ) '' S) ∩ ball 0 R :=
          ⟨⟨z - ξ, ⟨z, hzS, rfl⟩, rfl⟩,
            mem_ball_zero_iff.mpr ((hQ z).trans_lt (hwρ.trans_le (hρs.trans hsR)))⟩
        rw [hgraph] at hw
        obtain ⟨⟨x, -, hx⟩, -⟩ := hw
        have hxρ : ‖graphPoint x (u x)‖ < ρ := by
          rw [show graphPoint x (u x) = Q (z - ξ) from hx, hQ]; exact hwρ
        exact hwG ⟨x, ⟨mem_ball_zero_iff.mpr ((hnorm x (u x)).trans_lt hxρ), hxρ⟩, hx⟩
    · -- `w = (x, u x)` with `‖x‖ < ρ`, `‖(x, u x)‖ < ρ`, and `w` off the carrier part.
      obtain ⟨hxρ, hGρ⟩ := hxW
      have hw : graphPoint x (u x) ∈ graphOver u (ball 0 R) ∩ ball 0 R :=
        ⟨⟨x, mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hxρ).trans_le (hρs.trans hsR)), rfl⟩,
          mem_ball_zero_iff.mpr (hGρ.trans_le (hρs.trans hsR))⟩
      rw [← hgraph] at hw
      obtain ⟨⟨_, ⟨z, hzS, rfl⟩, hz⟩, -⟩ := hw
      have hzρ : ‖z - ξ‖ < ρ := by rw [← hQ, hz]; exact hGρ
      refine ⟨z - ξ, ⟨z, mem_symmDiff.mpr (Or.inr ⟨⟨hzS, ?_⟩, ?_⟩), rfl⟩, hz⟩
      · exact mem_ball_iff_norm.mpr (hzρ.trans_le hρs)
      · rintro ⟨hzM, -⟩
        exact hwM ⟨⟨z - ξ, ⟨z, hzM, rfl⟩, hz⟩, mem_ball_zero_iff.mpr hGρ⟩
  -- `Q` and `τ` are isometries, so `Hⁿ(Q (τ (Z))) = Hⁿ(Z) = 0`.
  have hτ : Isometry (fun x : Amb n ℓ => x - ξ) :=
    Isometry.of_dist_eq fun a b => dist_sub_right a b ξ
  refine measure_mono_null hsub ?_
  rw [Q.isometry.euclideanHausdorffMeasure_image, hτ.euclideanHausdorffMeasure_image]
  exact hnull
/-- **`Hⁿ ⌞ P` on balls about `0`** (the normalization `Hⁿ = Lⁿ` on `n`-planes, Simon's Notation
p. ix, with scaling).  If `P ⊆ ℝ^{n+ℓ}` is an `n`-dimensional subspace and `s ≥ 0`, then
`Hⁿ(P ∩ B_s(0)) = ω_n sⁿ`.  The inclusion `P → ℝ^{n+ℓ}` is an isometry, so `Hⁿ ⌞ P` is the image
of `Hⁿ` on `P`, which is Lebesgue measure of the `n`-dimensional inner product space `P`; there
`|B_s(0)| = sⁿ |B_1(0)|`.  Mathlib's value of `|B_1(0)|` lies outside the frozen import closure, so
it is computed here by evaluating `I = ∫_P e^{-|x|²} dx` twice: in orthonormal coordinates
`I = (∫_ℝ e^{-t²} dt)ⁿ = π^{n/2}` (Fubini), while the layer-cake formula with
`{e^{-|x|²} > t} = B_{√(-log t)}(0)` and the substitution `t = e^{-u}` give
`I = |B_1(0)| ∫_0^∞ u^{n/2} e^{-u} du = |B_1(0)| Γ(n/2 + 1)`. -/
theorem rsod_planeMeasure_closedBall : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (P : Submodule ℝ (Amb n ℓ)), Module.finrank ℝ P = n → ∀ s : ℝ, 0 ≤ s → ((μHE[n] : Measure (Amb n ℓ)).restrict (P : Set (Amb n ℓ))) (closedBall 0 s) = ENNReal.ofReal (unitBallVolume n * s ^ n) := by
  intro n ℓ hn P hP s hs
  have : Nontrivial P := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  -- `Hⁿ ⌞ P` is the image of `Hⁿ` on `P` under the isometric inclusion `ι : P → ℝ^{n+ℓ}`, and
  -- `ι⁻¹(B_s(0))` is the closed ball `B_s(0)` of `P`.
  have hrange : range (P.subtypeₗᵢ : P → Amb n ℓ) = (P : Set (Amb n ℓ)) := by ext x; simp
  rw [← hrange, ← P.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
    Measure.map_apply P.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
  have hpre : (P.subtypeₗᵢ : P → Amb n ℓ) ⁻¹' closedBall (0 : Amb n ℓ) s =
      closedBall (0 : P) s := by
    ext x; simp [mem_closedBall, dist_eq_norm]
  -- On the `n`-dimensional inner product space `P`, `Hⁿ` is Lebesgue measure.
  have hvol : (μHE[n] : Measure P) = volume := by
    have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P); rwa [hP] at h
  -- `∫_ℝ e^{-t²} dt = √π`.
  have hA : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) = ENNReal.ofReal (√Real.pi) := by
    have h := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at h
    rw [← h, ofReal_integral_eq_lintegral_ofReal]
    · simpa using integrable_exp_neg_mul_sq (b := 1) one_pos
    · exact ae_of_all _ (fun x => (Real.exp_pos _).le)
  -- Fubini, splitting off the first coordinate: `∫_{ℝᵐ} e^{-|y|²} dy = (√π)ᵐ`.
  have hB : ∀ m : ℕ, ∫⁻ x : Fin m → ℝ, ENNReal.ofReal (Real.exp (-∑ i, x i ^ 2)) =
      ENNReal.ofReal (√Real.pi) ^ m := by
    intro m
    induction m with
    | zero => simp [volume_pi]
    | succ m ih =>
      have e := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      have hf : Measurable fun p : ℝ × (Fin m → ℝ) =>
          ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)) := by
        fun_prop
      calc ∫⁻ x : Fin (m + 1) → ℝ, ENNReal.ofReal (Real.exp (-∑ i, x i ^ 2))
          = ∫⁻ x : Fin (m + 1) → ℝ, (fun p : ℝ × (Fin m → ℝ) =>
              ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)))
                (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 x) := by
            refine lintegral_congr fun x => ?_
            simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.sum_univ_succ]
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add]
            rfl
        _ = ∫⁻ p : ℝ × (Fin m → ℝ), ENNReal.ofReal (Real.exp (-p.1 ^ 2)) *
              ENNReal.ofReal (Real.exp (-∑ i, p.2 i ^ 2)) := e.lintegral_comp hf
        _ = (∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-a ^ 2))) *
              ∫⁻ y : Fin m → ℝ, ENNReal.ofReal (Real.exp (-∑ i, y i ^ 2)) :=
            lintegral_prod_mul (f := fun a : ℝ => ENNReal.ofReal (Real.exp (-a ^ 2)))
              (g := fun y : Fin m → ℝ => ENNReal.ofReal (Real.exp (-∑ i, y i ^ 2)))
              (by fun_prop) (Measurable.aemeasurable (by fun_prop))
        _ = ENNReal.ofReal (√Real.pi) ^ (m + 1) := by rw [hA, ih, pow_succ']
  -- In orthonormal coordinates on `P`: `∫_P e^{-|x|²} dx = (√π)^{dim P}`.
  have hC : ∫⁻ x : P, ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
      ENNReal.ofReal (√Real.pi) ^ Module.finrank ℝ P := by
    have e := (PiLp.volume_preserving_ofLp (Fin (Module.finrank ℝ P))).comp
      (stdOrthonormalBasis ℝ P).measurePreserving_repr
    rw [← hB, ← e.lintegral_comp (by fun_prop)]
    refine lintegral_congr fun x => ?_
    rw [← (stdOrthonormalBasis ℝ P).repr.norm_map x, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  -- `t = e^{-u}`: `∫_0^∞ (√(-log t))^{dim P} dt = ∫_0^∞ u^{dim P/2} e^{-u} du = Γ(dim P/2 + 1)`.
  have hE : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (√(-Real.log t) ^ Module.finrank ℝ P) =
      ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1)) := by
    have himg : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
      rw [image_univ]; ext t; simp only [mem_range, mem_Ioi]
      constructor
      · rintro ⟨u, rfl⟩; exact Real.exp_pos _
      · intro ht; exact ⟨-Real.log t, by rw [neg_neg, Real.exp_log ht]⟩
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun u _ => (hasDerivAt_neg u).exp.hasDerivWithinAt)
        (fun u _ v _ h => by simpa using h), Measure.restrict_univ]
    simp only [mul_neg, mul_one, abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    rw [Real.Gamma_eq_integral (by positivity), ofReal_integral_eq_lintegral_ofReal
      (Real.GammaIntegral_convergent (by positivity))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
        have : 0 < u := hu
        positivity)]
    rw [← setLIntegral_eq_of_support_subset (s := Ioi 0)]
    · refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu : 0 < u := hu
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
        ← Real.rpow_mul hu.le]
      congr 3
      ring
    · intro u hu
      by_contra h
      simp only [mem_Ioi, not_lt] at h
      apply hu
      simp [Real.sqrt_eq_zero'.2 h, zero_pow (by omega : Module.finrank ℝ P ≠ 0)]
  -- Layer cake: `{x ∈ P : e^{-|x|²} > t}` is the ball `B_{√(-log t)}(0)` of `P`.
  have hD : ∫⁻ x : P, ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) =
      ENNReal.ofReal (Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1)) * volume (ball (0 : P) 1) := by
    rw [lintegral_eq_lintegral_meas_lt volume (ae_of_all _ fun x => (Real.exp_pos _).le)
      (by fun_prop), ← hE, ← lintegral_mul_const _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : 0 < t := ht
    have hset : {a : P | t < Real.exp (-‖a‖ ^ 2)} = ball (0 : P) √(-Real.log t) := by
      ext a
      rw [mem_ofPred_eq, mem_ball_zero_iff, ← Real.log_lt_iff_lt_exp ht,
        Real.lt_sqrt (norm_nonneg _)]
      constructor <;> intro h <;> linarith
    rw [hset, Measure.addHaar_ball volume 0 (Real.sqrt_nonneg _)]
  -- Hence `|B_1(0)| = (√π)ⁿ / Γ(n/2 + 1) = π^{n/2} / Γ(n/2 + 1) = ω_n`.
  have hΓ : 0 < Real.Gamma ((Module.finrank ℝ P : ℝ) / 2 + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hω : unitBallVolume n = √Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by
    unfold unitBallVolume
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 2
    ring
  have hball : volume (ball (0 : P) 1) = ENNReal.ofReal (unitBallVolume n) := by
    rw [hP] at hC hD hΓ
    rw [hω, ENNReal.ofReal_div_of_pos hΓ,
      ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hΓ).ne' ENNReal.ofReal_ne_top, ← hD, hC,
      ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
  rw [hpre, hvol, Measure.addHaar_closedBall volume (0 : P) hs, hball, hP,
    ← ENNReal.ofReal_mul (pow_nonneg hs n), mul_comm]
/-- **Uniform first-order approximation of a `C¹` map** (step 2 of the density-one argument for
`C¹` graphs in Simon 7.1, in two-point form).  If `u` is `C¹` on the open set `U ⊆ ℝⁿ` and
`x₀ ∈ U`, then for every `ε > 0` there is `η > 0` with `B_η(x₀) ⊆ U` and
`|u(x) − u(y) − Du(x₀)(x − y)| ≤ ε |x − y|` for all `x, y ∈ B_η(x₀)`: by continuity of `Du` at `x₀`
choose `η` with `‖Du(z) − Du(x₀)‖ ≤ ε` on `B_η(x₀) ⊆ U`, and apply the mean value inequality on the
convex ball `B_η(x₀)`. -/
theorem dohr_c1_uniform_first_order : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiffOn ℝ 1 u U → ∀ x₀ ∈ U, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ closedBall x₀ η ⊆ U ∧ ∀ x ∈ closedBall x₀ η, ∀ y ∈ closedBall x₀ η, ‖u x - u y - fderiv ℝ u x₀ (x - y)‖ ≤ ε * ‖x - y‖ := by
  intro n ℓ U u hU hu x₀ hx₀ ε hε
  -- `u` is differentiable at every point of the open set `U`, and `Du` is continuous at `x₀`.
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hca : ContinuousAt (fderiv ℝ u) x₀ :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx₀)
  -- `B̆_{η₁}(x₀) ⊆ U`, `‖Du(z) − Du(x₀)‖ < ε` for `|z − x₀| < η₂`; take `η = min(η₁, η₂)/2`.
  obtain ⟨η₁, hη₁, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  obtain ⟨η₂, hη₂, hclose⟩ := Metric.continuousAt_iff.1 hca ε hε
  have hη : min η₁ η₂ / 2 < min η₁ η₂ := half_lt_self (lt_min hη₁ hη₂)
  have hsub : closedBall x₀ (min η₁ η₂ / 2) ⊆ U := fun z hz =>
    hball (mem_ball.2 ((mem_closedBall.1 hz).trans_lt (hη.trans_le (min_le_left η₁ η₂))))
  refine ⟨min η₁ η₂ / 2, half_pos (lt_min hη₁ hη₂), hsub, fun x hx y hy => ?_⟩
  -- Mean value inequality on the convex ball, measured against the fixed linear map `Du(x₀)`.
  refine (convex_closedBall x₀ _).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hdiff z (hsub hz)).hasFDerivAt.hasFDerivWithinAt) (fun z hz => ?_) hy hx
  rw [← dist_eq_norm]
  exact (hclose ((mem_closedBall.1 hz).trans_lt (hη.trans_le (min_le_right η₁ η₂)))).le

/-- **Two-sided mass pinching for `C¹` graphs** (towards `Θⁿ = 1` on `C¹` graphs, for Simon Ch. 5,
Theorem 7.1).  If `u` is `C¹` on `B̆_R(0) ⊆ ℝⁿ`, `x ∈ B̆_R(0)` and `0 < ε < 1`, then for all small
`r > 0` the graph `Γ = graph(u|B̆_R(0))` satisfies
`((1-ε)/(1+ε))ⁿ ω_n rⁿ ≤ Hⁿ(Γ ∩ B_r((x, u(x)))) ≤ ((1+ε)/(1-ε))ⁿ ω_n rⁿ`.
With `G(z) = (z, u(z))` and the tangent map `L v = (v, Du(x) v)`, the uniform first-order estimate
gives `(1-ε)|L(z-z')| ≤ |G(z) - G(z')| ≤ (1+ε)|L(z-z')|` near `x`.  Hence `Γ ∩ B_r((x, u(x)))` is
squeezed between `G`-images of `x + E_{r/(1+ε)}` and `x + E_{r/(1-ε)}`, `E_t = {v : |L v| ≤ t}`,
and `L(E_t)` is the closed `t`-ball of the `n`-plane `range L`, of measure `ω_n tⁿ`.  The two
comparisons use `Hⁿ(f(S)) ≤ Kⁿ Hⁿ(S)` for the `K`-Lipschitz maps `w ↦ G(x + π w)` (`K = 1+ε`) and
`z ↦ L(π z - x)` (`K = (1-ε)⁻¹`), where `π` is the projection onto the first `n` coordinates. -/
theorem dohr_c1_graph_mass_pinching : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, 0 < r → r ≤ η → ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) ≤ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ∧ (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) ≤ ENNReal.ofReal ((1 + ε) ^ n / (1 - ε) ^ n * (unitBallVolume n * r ^ n)) := by
  intro n ℓ hn R u hu x₀ hx₀ ε hε hε1
  set P : Rn n →L[ℝ] Rn ℓ := fderiv ℝ u x₀ with hP
  have h1ε : 0 < 1 - ε := by linarith
  -- (1) Graph-coordinate algebra: `(x, y)` is linear and `|(x, y)|² = |x|² + |y|²`.
  have gp_sub : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint x y - graphPoint x' y' = graphPoint (x - x') (y - y') := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_add : ∀ (x x' : Rn n) (y y' : Rn ℓ),
      graphPoint (x + x') (y + y') = graphPoint x y + graphPoint x' y' := by
    intro x x' y y'
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_smul : ∀ (c : ℝ) (x : Rn n) (y : Rn ℓ),
      graphPoint (c • x) (c • y) = c • graphPoint x y := by
    intro c x y
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp [graphPoint]
  have gp_norm : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have gp_le : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := fun x y =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg ‖y‖)).trans (gp_norm x y).ge)
  have gp_zero : ∀ y : Rn ℓ, ‖graphPoint (0 : Rn n) y‖ = ‖y‖ := by
    intro y
    have h := gp_norm 0 y
    rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  -- (2) The first-coordinate projection `π` and the tangent map `L v = (v, P v)`.
  let π : Amb n ℓ → Rn n := fun w => WithLp.toLp 2 (fun i : Fin n => w (Fin.castAdd ℓ i))
  have hπ : ∀ (x : Rn n) (y : Rn ℓ), π (graphPoint x y) = x := by
    intro x y
    ext i
    simp [π, graphPoint]
  let L : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (P v)
      map_add' := fun v w => by
        simp only [map_add]
        exact gp_add v w (P v) (P w)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        exact gp_smul c v (P v) }
  have hL : ∀ v, L v = graphPoint v (P v) := fun v => rfl
  have hLle : ∀ v, ‖v‖ ≤ ‖L v‖ := fun v => gp_le v (P v)
  have hLinj : Function.Injective L := by
    intro v w h
    have := hLle (v - w)
    rw [map_sub, h, sub_self, norm_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hπL : ∀ v, π (L v) = v := fun v => hπ v (P v)
  let G : Rn n → Amb n ℓ := fun x => graphPoint x (u x)
  have hπG : ∀ x, π (G x) = x := fun x => hπ x (u x)
  have hGsub : ∀ x x', G x - G x' = graphPoint (x - x') (u x - u x') := fun x x' => gp_sub _ _ _ _
  have hGdist : ∀ x x', ‖x - x'‖ ≤ ‖G x - G x'‖ := by
    intro x x'
    rw [hGsub]
    exact gp_le _ _
  -- (3) First-order estimate on the closed ball `B = B_{η₀}(x₀)`:
  -- `(1-ε)|L(x-x')| ≤ |G(x) - G(x')| ≤ (1+ε)|L(x-x')|`.
  obtain ⟨η₀, hη₀, hB, hest⟩ :=
    Submission.dohr_c1_uniform_first_order n ℓ (ball 0 R) u isOpen_ball hu x₀ hx₀ ε hε
  have hGL : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x' - L (x - x')‖ ≤ ε * ‖L (x - x')‖ := by
    intro x hx x' hx'
    have h1 : G x - G x' - L (x - x') = graphPoint 0 (u x - u x' - P (x - x')) := by
      rw [hGsub, hL, gp_sub, sub_self]
    rw [h1, gp_zero]
    exact (hest x hx x' hx').trans (mul_le_mul_of_nonneg_left (hLle _) hε.le)
  have hup : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      ‖G x - G x'‖ ≤ (1 + ε) * ‖L (x - x')‖ := by
    intro x hx x' hx'
    calc ‖G x - G x'‖ = ‖(G x - G x' - L (x - x')) + L (x - x')‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - G x' - L (x - x')‖ + ‖L (x - x')‖ := norm_add_le _ _
      _ ≤ ε * ‖L (x - x')‖ + ‖L (x - x')‖ := by gcongr; exact hGL x hx x' hx'
      _ = (1 + ε) * ‖L (x - x')‖ := by ring
  have hlow : ∀ x ∈ closedBall x₀ η₀, ∀ x' ∈ closedBall x₀ η₀,
      (1 - ε) * ‖L (x - x')‖ ≤ ‖G x - G x'‖ := by
    intro x hx x' hx'
    have : ‖L (x - x')‖ ≤ ‖G x - G x'‖ + ‖G x - G x' - L (x - x')‖ := by
      calc ‖L (x - x')‖ = ‖(G x - G x') - (G x - G x' - L (x - x'))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    nlinarith [hGL x hx x' hx']
  -- (4) Choice of `η = (1-ε)η₀`, localization `Γ ∩ B_r(G(x₀)) = G(D)` and the ellipsoid sandwich
  -- `x₀ + E_{r/(1+ε)} ⊆ D ⊆ x₀ + E_{r/(1-ε)}`.
  refine ⟨(1 - ε) * η₀, mul_pos h1ε hη₀, ?_⟩
  intro r hr hrη
  have hrη₀ : r / (1 - ε) ≤ η₀ := by rw [div_le_iff₀ h1ε]; linarith
  have hrη₀' : r / (1 + ε) ≤ η₀ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let D : Set (Rn n) := ball 0 R ∩ G ⁻¹' closedBall (G x₀) r
  have hΓ : graphOver u (ball 0 R) ∩ closedBall (graphPoint x₀ (u x₀)) r = G '' D := by
    rw [graphOver, ← Set.image_inter_preimage]
  let E : ℝ → Set (Rn n) := fun t => {v | ‖L v‖ ≤ t}
  have hEB : ∀ t, t ≤ η₀ → ∀ v ∈ E t, x₀ + v ∈ closedBall x₀ η₀ := by
    intro t ht v hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact (hLle v).trans (le_trans hv ht)
  have hx₀B : x₀ ∈ closedBall x₀ η₀ := mem_closedBall_self hη₀.le
  have hDB : D ⊆ closedBall x₀ η₀ := by
    rintro x ⟨-, hx⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm]
    have : r ≤ η₀ := by nlinarith
    linarith [hGdist x x₀]
  have hED : ∀ v ∈ E (r / (1 + ε)), x₀ + v ∈ D := by
    intro v hv
    have hxB := hEB _ hrη₀' v hv
    refine ⟨hB hxB, ?_⟩
    rw [mem_preimage, mem_closedBall, dist_eq_norm]
    have h := hup (x₀ + v) hxB x₀ hx₀B
    rw [add_sub_cancel_left] at h
    have hv' : ‖L v‖ ≤ r / (1 + ε) := hv
    calc ‖G (x₀ + v) - G x₀‖ ≤ (1 + ε) * ‖L v‖ := h
      _ ≤ (1 + ε) * (r / (1 + ε)) := by gcongr
      _ = r := by field_simp
  have hDE : ∀ x ∈ D, x - x₀ ∈ E (r / (1 - ε)) := by
    intro x hx
    have hxB := hDB hx
    have hx2 : ‖G x - G x₀‖ ≤ r := by
      have := hx.2
      rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
    show ‖L (x - x₀)‖ ≤ r / (1 - ε)
    rw [le_div_iff₀ h1ε]
    linarith [hlow x hxB x₀ hx₀B]
  -- (5) The images `L(E_t)` are the closed `t`-balls of the `n`-plane `range L`.
  have hrank : Module.finrank ℝ (LinearMap.range L) = n := by
    rw [LinearMap.finrank_range_of_inj hLinj, finrank_euclideanSpace_fin]
  have hplane : ∀ t, 0 ≤ t →
      (μHE[n] : Measure (Amb n ℓ)) (L '' E t) = ENNReal.ofReal (unitBallVolume n * t ^ n) := by
    intro t ht
    have hset : L '' E t = closedBall (0 : Amb n ℓ) t ∩
        ((LinearMap.range L : Submodule ℝ (Amb n ℓ)) : Set (Amb n ℓ)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨mem_closedBall_zero_iff.2 hv, LinearMap.mem_range_self L v⟩
      · rintro ⟨hy, ⟨v, rfl⟩⟩
        exact ⟨v, mem_closedBall_zero_iff.1 hy, rfl⟩
    rw [hset, ← Measure.restrict_apply measurableSet_closedBall]
    exact Submission.rsod_planeMeasure_closedBall n ℓ hn (LinearMap.range L) hrank t ht
  -- (6) Lipschitz images: `Hⁿ(f(S)) ≤ Kⁿ Hⁿ(S)` for `K`-Lipschitz `f`.
  have hlip : ∀ (K : ℝ≥0) (f : Amb n ℓ → Amb n ℓ) (s : Set (Amb n ℓ)), LipschitzOnWith K f s →
      (μHE[n] : Measure (Amb n ℓ)) (f '' s) ≤ (K : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) s := by
    intro K f s hf
    have h := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [ENNReal.rpow_natCast] at h
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
    calc _ ≤ _ * ((K : ℝ≥0∞) ^ n * μH[(n : ℝ)] s) := by gcongr
      _ = _ := by ring
  have hpow : ∀ c : ℝ, 0 ≤ c → ((Real.toNNReal c : ℝ≥0) : ℝ≥0∞) ^ n = ENNReal.ofReal (c ^ n) :=
    fun c hc => (ENNReal.ofReal_pow hc n).symm
  have hω : 0 ≤ unitBallVolume n := by
    unfold unitBallVolume
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.Gamma_pos_of_pos (by positivity)).le
  rw [hΓ]
  constructor
  · -- Lower bound via `Ψ(z) = L(π z - x₀)`, which is `(1 - ε)⁻¹`-Lipschitz on `G(D)`.
    let Ψ : Amb n ℓ → Amb n ℓ := fun z => L (π z - x₀)
    have hΨlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) Ψ (G '' D) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
      simp only [Ψ, hπG]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right,
        Real.coe_toNNReal _ (inv_nonneg.2 h1ε.le)]
      rw [inv_mul_eq_div, le_div_iff₀ h1ε, mul_comm]
      exact hlow x (hDB hx) x' (hDB hx')
    have himg : L '' E (r / (1 + ε)) ⊆ Ψ '' (G '' D) := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨G (x₀ + v), ⟨x₀ + v, hED v hv, rfl⟩, ?_⟩
      simp only [Ψ, hπG, add_sub_cancel_left]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 + ε))) ≤
        ((Real.toNNReal (1 - ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ n * (μHE[n] : Measure (Amb n ℓ)) (G '' D) :=
      (measure_mono himg).trans (hlip _ _ _ hΨlip)
    rw [hplane _ (by positivity), hpow _ (inv_nonneg.2 h1ε.le)] at h1
    have key : ENNReal.ofReal ((1 - ε) ^ n / (1 + ε) ^ n * (unitBallVolume n * r ^ n)) =
        ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_pow]
      field_simp
    rw [key]
    calc ENNReal.ofReal ((1 - ε) ^ n) * ENNReal.ofReal (unitBallVolume n * (r / (1 + ε)) ^ n)
        ≤ ENNReal.ofReal ((1 - ε) ^ n) *
            (ENNReal.ofReal ((1 - ε)⁻¹ ^ n) * (μHE[n] : Measure (Amb n ℓ)) (G '' D)) := by
          gcongr
      _ = (μHE[n] : Measure (Amb n ℓ)) (G '' D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            mul_inv_cancel₀ h1ε.ne', one_pow, ENNReal.ofReal_one, one_mul]
  · -- Upper bound via `Φ(w) = G(x₀ + π w)`, which is `(1 + ε)`-Lipschitz on `L(E_{r/(1-ε)})`.
    let Φ : Amb n ℓ → Amb n ℓ := fun w => G (x₀ + π w)
    have hΦlip : LipschitzOnWith (Real.toNNReal (1 + ε)) Φ (L '' E (r / (1 - ε))) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
      simp only [Φ, hπL]
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ (by linarith)]
      have h := hup (x₀ + v) (hEB _ hrη₀ v hv) (x₀ + v') (hEB _ hrη₀ v' hv')
      rwa [add_sub_add_left_eq_sub] at h
    have himg : G '' D ⊆ Φ '' (L '' E (r / (1 - ε))) := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨L (x - x₀), ⟨x - x₀, hDE x hx, rfl⟩, ?_⟩
      simp only [Φ, hπL, add_sub_cancel]
    have h1 : (μHE[n] : Measure (Amb n ℓ)) (G '' D) ≤
        ((Real.toNNReal (1 + ε) : ℝ≥0) : ℝ≥0∞) ^ n *
          (μHE[n] : Measure (Amb n ℓ)) (L '' E (r / (1 - ε))) :=
      (measure_mono himg).trans (hlip _ _ _ hΦlip)
    rw [hplane _ (by positivity), hpow _ (by linarith)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
/-- **Squeeze lemma for `[0, ∞]`-valued ratios as `r ↓ 0`.**  If for every `δ > 0`, eventually as
`r ↓ 0`, `g r > 0` and `ofReal((1 - δ) g r) ≤ f r ≤ ofReal((1 + δ) g r)`, then
`f r / ofReal(g r) → 1`.  Dividing by `ofReal(g r) ∈ (0, ∞)` gives
`ofReal(1 - δ) ≤ f r / ofReal(g r) ≤ ofReal(1 + δ)` eventually; by `tendsto_order`, a target
`a < 1` is beaten with `δ = (1 - a)/2`, and a target `b > 1` with `δ = (b - 1)/2` (`δ = 1` if
`b = ∞`). -/
theorem dohr_ratio_tendsto_one_of_pinching : ∀ (f : ℝ → ℝ≥0∞) (g : ℝ → ℝ), (∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < g r ∧ ENNReal.ofReal ((1 - δ) * g r) ≤ f r ∧ f r ≤ ENNReal.ofReal ((1 + δ) * g r)) → Tendsto (fun r => f r / ENNReal.ofReal (g r)) (𝓝[>] 0) (𝓝 1) := by
  intro f g h
  -- Pointwise: the bounds give `ofReal (1 - δ) ≤ f r / ofReal (g r) ≤ ofReal (1 + δ)`.
  have key : ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (1 - δ) ≤ f r / ENNReal.ofReal (g r) ∧
        f r / ENNReal.ofReal (g r) ≤ ENNReal.ofReal (1 + δ) := by
    intro δ hδ
    filter_upwards [h δ hδ] with r ⟨hg, hlo, hhi⟩
    have hg0 : ENNReal.ofReal (g r) ≠ 0 := (ENNReal.ofReal_pos.2 hg).ne'
    have hgt : ENNReal.ofReal (g r) ≠ ∞ := ENNReal.ofReal_ne_top
    constructor
    · rcases le_or_gt (1 - δ) 0 with hd | hd
      · rw [ENNReal.ofReal_of_nonpos hd]
        exact zero_le
      · rw [ENNReal.le_div_iff_mul_le (Or.inl hg0) (Or.inl hgt), ← ENNReal.ofReal_mul hd.le]
        exact hlo
    · rw [ENNReal.div_le_iff hg0 hgt, ← ENNReal.ofReal_mul (by linarith)]
      exact hhi
  rw [tendsto_order]
  constructor
  · -- `a < 1`, so `a = ofReal a.toReal` with `0 ≤ a.toReal < 1`; take `δ = (1 - a.toReal)/2`.
    intro a ha
    have hat : a ≠ ∞ := ne_top_of_lt ha
    have ha' : a.toReal < 1 := by
      simpa using (ENNReal.toReal_lt_toReal hat ENNReal.one_ne_top).2 ha
    have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hδ : 0 < (1 - a.toReal) / 2 := by linarith
    filter_upwards [key _ hδ] with r ⟨hlo, _⟩
    refine lt_of_lt_of_le ?_ hlo
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
      _ < ENNReal.ofReal (1 - (1 - a.toReal) / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  · -- `b > 1`: if `b = ∞` take `δ = 1`; otherwise `1 < b.toReal`, take `δ = (b.toReal - 1)/2`.
    intro b hb
    rcases eq_or_ne b ∞ with rfl | hbt
    · filter_upwards [key 1 one_pos] with r ⟨_, hhi⟩
      exact lt_of_le_of_lt hhi ENNReal.ofReal_lt_top
    · have hb' : 1 < b.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hbt).2 hb
      have hδ : 0 < (b.toReal - 1) / 2 := by linarith
      filter_upwards [key _ hδ] with r ⟨_, hhi⟩
      refine lt_of_le_of_lt hhi ?_
      calc ENNReal.ofReal (1 + (b.toReal - 1) / 2) < ENNReal.ofReal b.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
        _ = b := ENNReal.ofReal_toReal hbt

/-- **A `C¹` graph has `Hⁿ`-density one at each of its points** (Simon p. 128: "graph `u` is a
`C¹` submanifold so then `Θⁿ(μ_V, x) = 1` at every point of graph `u`").  If `n ≥ 1`, `u` is `C¹`
on the open ball `B̆_R(0) ⊆ ℝⁿ` and `x ∈ B̆_R(0)`, then
`Hⁿ(graph u|_{B̆_R(0)} ∩ B_r((x, u(x)))) / (ω_n rⁿ) → 1` as `r ↓ 0`.  Given `δ > 0`, continuity of
`ε ↦ (1 + ε)ⁿ / (1 − ε)ⁿ` at `0` gives `ε ∈ (0, 1)` with `(1 + ε)ⁿ / (1 − ε)ⁿ < 1 + δ`, hence
`(1 − ε)ⁿ / (1 + ε)ⁿ ≥ (1 + δ)⁻¹ ≥ 1 − δ`.  For small `r > 0` the graph mass in `B_r((x, u(x)))` lies
between `(1 − ε)ⁿ / (1 + ε)ⁿ · ω_n rⁿ` and `(1 + ε)ⁿ / (1 − ε)ⁿ · ω_n rⁿ`
(`dohr_c1_graph_mass_pinching`), so between `(1 ∓ δ) ω_n rⁿ` with `ω_n rⁿ > 0`, and the ratio
squeeze `dohr_ratio_tendsto_one_of_pinching` gives the limit. -/
theorem dohr_c1_graph_density_one : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R, Tendsto (fun r : ℝ => (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 1) := by
  intro n ℓ hn R u hu x hx
  -- `ω_n = π^{n/2} / Γ(n/2 + 1) > 0`.
  have hω : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
  refine Submission.dohr_ratio_tendsto_one_of_pinching
    (fun r => (μHE[n] : Measure (Amb n ℓ))
      (graphOver u (ball 0 R) ∩ closedBall (graphPoint x (u x)) r))
    (fun r => unitBallVolume n * r ^ n) fun δ hδ => ?_
  -- Choose `ε ∈ (0, 1)` with `(1 + ε)ⁿ / (1 − ε)ⁿ < 1 + δ`, by continuity at `ε = 0`.
  have hcont : ContinuousAt (fun ε : ℝ => (1 + ε) ^ n / (1 - ε) ^ n) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε) ^ n / (1 - ε) ^ n < 1 + δ ∧ ε < 1 ∧ 0 < ε :=
    ((hcont.tendsto.eventually (gt_mem_nhds (a := 1 + δ) (by simp [hδ]))).filter_mono
      nhdsWithin_le_nhds).and (((gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨ε, hεδ, hε1, hε0⟩ := hev.exists
  -- `(1 − ε)ⁿ / (1 + ε)ⁿ = ((1 + ε)ⁿ / (1 − ε)ⁿ)⁻¹ ≥ (1 + δ)⁻¹ ≥ 1 − δ`.
  have hlower : 1 - δ ≤ (1 - ε) ^ n / (1 + ε) ^ n := by
    have h1e : 0 < 1 - ε := by linarith
    have h1 : (1 + δ)⁻¹ ≤ (1 - ε) ^ n / (1 + ε) ^ n := by
      rw [← inv_div]
      exact inv_anti₀ (by positivity) hεδ.le
    have h2 : 1 - δ ≤ (1 + δ)⁻¹ := by
      rw [← one_div, le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  -- The pinching bounds hold for `r ∈ (0, η]`, a right neighbourhood of `0`.
  obtain ⟨η, hη, hb⟩ := Submission.dohr_c1_graph_mass_pinching n ℓ hn R u hu x hx ε hε0 hε1
  filter_upwards [Ioc_mem_nhdsGT hη] with r ⟨hr0, hrη⟩
  have hg : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr0 n)
  obtain ⟨hlo, hhi⟩ := hb r hr0 hrη
  exact ⟨hg, (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hlower hg.le)).trans hlo,
    hhi.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hεδ.le hg.le))⟩
/-- Linear graph area formula.  For a linear map `P : ℝⁿ → ℝ^ℓ` put
`g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}`.  Then `det g(P) > 0` and the graph map `v ↦ (v, P v)` scales
`Hⁿ` by `√(det g(P))`: `Hⁿ({(v, P v) : v ∈ S}) = √(det g(P)) Lⁿ(S)` for every `S ⊆ ℝⁿ`.
Write `v ↦ (v, P v)` as `ι ∘ M`, with `ι` a linear isometry of `ℝⁿ` onto its range (orthonormal
coordinates) and `M` linear on `ℝⁿ`.  Then `g(P) = Mᵀ M`, so `det g(P) = (det M)² > 0`, and
`Hⁿ(ι(M S)) = Lⁿ(M S) = |det M| Lⁿ(S)` (`Isometry.euclideanHausdorffMeasure_image`,
`Measure.addHaar_image_linearMap`). -/
theorem dohr_vel_linear_graph_area : ∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, 0 < Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) ∧ ∀ S : Set (Rn n), (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) = ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) * (volume : Measure (Rn n)) S := by
  intro n ℓ P
  have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
      inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
    intro v v' w w'
    simp [graphPoint, PiLp.inner_apply, Fin.sum_univ_add]
  let Λ : Rn n →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun v => graphPoint v (P v)
      map_add' := by
        intro v w
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c v
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  have hΛ : ∀ v, Λ v = graphPoint v (P v) := fun v => rfl
  have hΛinj : Function.Injective Λ := by
    intro v w h
    have h' := congrArg (fun z : Amb n ℓ => (WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j)) : Rn n)) h
    simpa [hΛ, graphPoint] using h'
  have hW : Module.finrank ℝ (LinearMap.range Λ) = n := by
    rw [LinearMap.finrank_range_of_inj hΛinj, finrank_euclideanSpace_fin]
  let e : (LinearMap.range Λ) ≃ₗᵢ[ℝ] Rn n :=
    ((stdOrthonormalBasis ℝ (LinearMap.range Λ)).reindex (finCongr hW)).repr
  let M : Rn n →ₗ[ℝ] Rn n := e.toLinearEquiv.toLinearMap ∘ₗ Λ.rangeRestrict
  let ι : Rn n → Amb n ℓ := fun z => ((e.symm z : LinearMap.range Λ) : Amb n ℓ)
  have hι : Isometry ι := ((LinearMap.range Λ).subtypeₗᵢ.comp e.symm.toLinearIsometry).isometry
  have hΛM : ∀ v, ι (M v) = Λ v := by
    intro v
    simp [ι, M]
  have himage : ∀ S : Set (Rn n), (fun v => graphPoint v (P v)) '' S = ι '' (M '' S) := by
    intro S
    rw [Set.image_image]
    refine Set.image_congr (fun v _ => ?_)
    rw [hΛM, hΛ]
  have hinnerM : ∀ v w, inner ℝ (M v) (M w) = inner ℝ (Λ v) (Λ w) := by
    intro v w
    rw [← hΛM, ← hΛM]
    show inner ℝ (M v) (M w) = inner ℝ ((e.symm (M v) : LinearMap.range Λ) : Amb n ℓ) ((e.symm (M w) : LinearMap.range Λ) : Amb n ℓ)
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  let bs := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let Mm : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix bs bs M
  have hMm : ∀ k a, Mm k a = (M (EuclideanSpace.single a (1 : ℝ))) k := by
    intro k a
    simp [Mm, bs, LinearMap.toMatrix_apply]
  have hgm : ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
      inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) = Mm.transpose * Mm := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hMm]
    have h1 : ∑ k, (M (EuclideanSpace.single a (1 : ℝ))) k * (M (EuclideanSpace.single b (1 : ℝ))) k =
        inner ℝ (M (EuclideanSpace.single a (1 : ℝ))) (M (EuclideanSpace.single b (1 : ℝ))) := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [h1, hinnerM, hΛ, hΛ, hinner, EuclideanSpace.inner_single_left, PiLp.single_apply]
    simp [Matrix.one_apply]
  have hdet : Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
      inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) = (LinearMap.det M) ^ 2 := by
    rw [hgm, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
    ring
  have hMinj : Function.Injective M := by
    intro v w h
    apply hΛinj
    rw [← hΛM, ← hΛM, h]
  have hdetM : LinearMap.det M ≠ 0 := by
    have hsurj : Function.Surjective M := LinearMap.injective_iff_surjective.mp hMinj
    let Me : Rn n ≃ₗ[ℝ] Rn n := LinearEquiv.ofBijective M ⟨hMinj, hsurj⟩
    have : LinearMap.det M = LinearMap.det (Me : Rn n →ₗ[ℝ] Rn n) := rfl
    rw [this]
    exact (LinearEquiv.isUnit_det' Me).ne_zero
  refine ⟨by rw [hdet]; positivity, fun S => ?_⟩
  rw [himage, hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_image_linearMap, hdet, Real.sqrt_sq_eq_abs]
theorem dohr_vel_graph_fderiv : ∀ n ℓ : ℕ, ∀ (u : Rn n → Rn ℓ) (x : Rn n), DifferentiableAt ℝ u x → DifferentiableAt ℝ (fun z : Rn n => graphPoint z (u z)) x ∧ ∀ v : Rn n, fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x v = graphPoint v (fderiv ℝ u x v) := by
  intro n ℓ u x hu
  let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  let Γ : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ := LinearMap.toContinuousLinearMap Γl
  have h1 : HasFDerivAt (fun z : Rn n => (z, u z))
      ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x)) x :=
    (hasFDerivAt_id x).prodMk hu.hasFDerivAt
  have h2 : HasFDerivAt (fun z : Rn n => graphPoint z (u z))
      (Γ.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x))) x :=
    Γ.hasFDerivAt.comp x h1
  refine ⟨h2.differentiableAt, fun v => ?_⟩
  rw [h2.fderiv]
  rfl

theorem dohr_vel_vertical_test_field : ∀ n ℓ : ℕ, ∀ (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (s r : ℝ) (u φ : Rn n → Rn ℓ), 0 < s → ContinuousOn u (ball 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖graphPoint x (u x)‖ < s) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∃ X : Amb n ℓ → Amb n ℓ, ContDiff ℝ 1 X ∧ HasCompactSupport X ∧ tsupport X ⊆ ball ξ s ∧ (∀ x : Rn n, X (ξ + Q.symm (graphPoint x (u x))) = Q.symm (graphPoint 0 (φ x))) ∧ ∀ (x v : Rn n) (w : Rn ℓ), fderiv ℝ X (ξ + Q.symm (graphPoint x (u x))) (Q.symm (graphPoint v w)) = Q.symm (graphPoint 0 (fderiv ℝ φ x v)) := by
  intro n ℓ ξ Q s r u φ hs hu hGs hφ hφc hφr
  -- the pairing map (v, w) ↦ graphPoint v w and the projection onto the first n coordinates
  let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  let Γ : (Rn n × Rn ℓ) →L[ℝ] Amb n ℓ := LinearMap.toContinuousLinearMap Γl
  let ιL : Rn ℓ →L[ℝ] Amb n ℓ := Γ.comp (ContinuousLinearMap.inr ℝ (Rn n) (Rn ℓ))
  have hι : ∀ w, ιL w = graphPoint 0 w := fun w => rfl
  let πl : Amb n ℓ →ₗ[ℝ] Rn n :=
    { toFun := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
      map_add' := by intro z z'; rfl
      map_smul' := by intro c z; rfl }
  let πL : Amb n ℓ →L[ℝ] Rn n := LinearMap.toContinuousLinearMap πl
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), πL (graphPoint x w) = x := by
    intro x w
    show (WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp (graphPoint x w) (Fin.castAdd ℓ j)) : Rn n) = x
    simp [graphPoint]
  have hGc : ContinuousOn (fun x => graphPoint x (u x)) (ball 0 r) :=
    Γ.continuous.comp_continuousOn (continuousOn_id.prodMk hu)
  -- the compact image K of tsupport φ and the radii s' < s'' < s
  have hKc : IsCompact ((fun x => graphPoint x (u x)) '' tsupport φ) :=
    hφc.isCompact.image_of_continuousOn (hGc.mono hφr)
  have hKs : (fun x => graphPoint x (u x)) '' tsupport φ ⊆ ball 0 s := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_ball_zero_iff.mpr (hGs x (hφr hx))
  obtain ⟨s1, hs1, hKs1⟩ := exists_lt_subset_ball hKc.isClosed hKs
  have hs'pos : 0 < max s1 (s / 2) := lt_of_lt_of_le (half_pos hs) (le_max_right _ _)
  have hs's : max s1 (s / 2) < s := max_lt hs1 (half_lt_self hs)
  have hs's'' : max s1 (s / 2) < (max s1 (s / 2) + s) / 2 := by linarith
  have hs''s : (max s1 (s / 2) + s) / 2 < s := by linarith
  let ψ : ContDiffBump (0 : Amb n ℓ) := ⟨max s1 (s / 2), (max s1 (s / 2) + s) / 2, hs'pos, hs's''⟩
  have hKψ : (fun x => graphPoint x (u x)) '' tsupport φ ⊆ ball 0 (max s1 (s / 2)) :=
    hKs1.trans (ball_subset_ball (le_max_left _ _))
  have hψ1 : ∀ z ∈ ball (0 : Amb n ℓ) (max s1 (s / 2)), ψ z = 1 := fun z hz =>
    ψ.one_of_mem_closedBall (ball_subset_closedBall hz)
  -- the fields
  let Xt : Amb n ℓ → Amb n ℓ := fun z => ψ z • ιL (φ (πL z))
  let X : Amb n ℓ → Amb n ℓ := fun y => Q.symm (Xt (Q (y - ξ)))
  have hXt1 : ContDiff ℝ 1 Xt :=
    (ψ.contDiff (n := 1)).smul (ιL.contDiff.comp (hφ.comp πL.contDiff))
  have hX1 : ContDiff ℝ 1 X :=
    Q.symm.contDiff.comp (hXt1.comp (Q.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hsuppX : Function.support X ⊆ closedBall ξ ((max s1 (s / 2) + s) / 2) := by
    intro y hy
    have hψne : ψ (Q (y - ξ)) ≠ 0 := by
      intro h0
      apply hy
      show Q.symm (ψ (Q (y - ξ)) • ιL (φ (πL (Q (y - ξ))))) = 0
      rw [h0, zero_smul, map_zero]
    have hmem : Q (y - ξ) ∈ Function.support ψ := hψne
    rw [ψ.support_eq, mem_ball_zero_iff, LinearIsometryEquiv.norm_map] at hmem
    rw [mem_closedBall, dist_eq_norm]
    exact hmem.le
  have htsuppX : tsupport X ⊆ closedBall ξ ((max s1 (s / 2) + s) / 2) :=
    closure_minimal hsuppX isClosed_closedBall
  -- derivative of Xt on the graph
  have hXtD : ∀ x : Rn n, HasFDerivAt Xt (ιL.comp ((fderiv ℝ φ x).comp πL)) (graphPoint x (u x)) := by
    intro x
    have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφ.differentiable one_ne_zero) y
    by_cases hx : x ∈ tsupport φ
    · have hGK : graphPoint x (u x) ∈ ball (0 : Amb n ℓ) (max s1 (s / 2)) := hKψ ⟨x, hx, rfl⟩
      have hh : HasFDerivAt (fun z => ιL (φ (πL z))) (ιL.comp ((fderiv ℝ φ x).comp πL)) (graphPoint x (u x)) := by
        have h1 := (hφd (πL (graphPoint x (u x)))).hasFDerivAt.comp (graphPoint x (u x)) πL.hasFDerivAt
        rw [hπG] at h1
        exact ιL.hasFDerivAt.comp (graphPoint x (u x)) h1
      refine hh.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hGK] with z hz
      show ψ z • ιL (φ (πL z)) = ιL (φ (πL z))
      rw [hψ1 z hz, one_smul]
    · have hdφ : fderiv ℝ φ x = 0 := by
        by_contra hne
        exact hx (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      rw [hdφ, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
      refine (hasFDerivAt_const (0 : Amb n ℓ) _).congr_of_eventuallyEq ?_
      have hN : IsOpen (πL ⁻¹' (tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl.preimage πL.continuous
      have hGN : graphPoint x (u x) ∈ πL ⁻¹' (tsupport φ)ᶜ := by
        show πL (graphPoint x (u x)) ∉ tsupport φ
        rw [hπG]
        exact hx
      filter_upwards [hN.mem_nhds hGN] with z hz
      show ψ z • ιL (φ (πL z)) = 0
      rw [image_eq_zero_of_notMem_tsupport hz, map_zero, smul_zero]
  refine ⟨X, hX1, ?_, htsuppX.trans (closedBall_subset_ball hs''s), ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall ξ ((max s1 (s / 2) + s) / 2))
      (fun y hy => by
        by_contra hne
        exact hy (hsuppX hne))
  · intro x
    show Q.symm (ψ (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)) • ιL (φ (πL (Q (ξ + Q.symm (graphPoint x (u x)) - ξ))))) =
      Q.symm (graphPoint 0 (φ x))
    rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, hπG]
    by_cases hx : x ∈ tsupport φ
    · rw [hψ1 _ (hKψ ⟨x, hx, rfl⟩), one_smul, hι]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [h0, ← hι 0]
      simp
  · intro x v w
    have hT : HasFDerivAt (fun y => Q (y - ξ)) (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ)
        (ξ + Q.symm (graphPoint x (u x))) := by
      have := (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp
        (ξ + Q.symm (graphPoint x (u x))) ((hasFDerivAt_id _).sub_const ξ)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have hTx : Q (ξ + Q.symm (graphPoint x (u x)) - ξ) = graphPoint x (u x) := by
      rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
    have hXt' := hXtD x
    rw [← hTx] at hXt'
    have hX := (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).hasFDerivAt.comp
      (ξ + Q.symm (graphPoint x (u x))) (hXt'.comp (ξ + Q.symm (graphPoint x (u x))) hT)
    have hXeq : X = (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ) ∘ (Xt ∘ fun y => Q (y - ξ)) := rfl
    rw [hXeq, hX.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    show Q.symm (ιL (fderiv ℝ φ x (πL (Q (Q.symm (graphPoint v w)))))) = Q.symm (graphPoint 0 (fderiv ℝ φ x v))
    rw [LinearIsometryEquiv.apply_symm_apply, hπG, hι]

theorem dohr_vel_holder_rigid_transport : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ) (ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), IsLocallyHolderCkα q α h U → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U) := by
  intro n ℓ U hU h q α ξ Q hh
  obtain ⟨hhC, hhH⟩ := hh
  -- T and its inverse A
  have hTA : ∀ z, Q (ξ + Q.symm z - ξ) = z := fun z => by
    rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
  have hAT : ∀ y, ξ + Q.symm (Q (y - ξ)) = y := fun y => by
    rw [LinearIsometryEquiv.symm_apply_apply]
    abel
  have hO : (fun y => Q (y - ξ)) '' U = (fun z => ξ + Q.symm z) ⁻¹' U :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun y => Q (y - ξ)) (g := fun z => ξ + Q.symm z)
      (fun y => hAT y) (fun z => hTA z)) U
  have hAcont : Continuous (fun z : Amb n ℓ => ξ + Q.symm z) := continuous_const.add Q.symm.continuous
  refine ⟨?_, ?_, ?_⟩
  · rw [hO]
    exact hU.preimage hAcont
  · -- C^q on O
    rw [hO]
    have hA : ContDiff ℝ q (fun z : Amb n ℓ => ξ + Q.symm z) := contDiff_const.add Q.symm.contDiff
    have h1 : ContDiffOn ℝ q (h ∘ fun z : Amb n ℓ => ξ + Q.symm z) ((fun z => ξ + Q.symm z) ⁻¹' U) :=
      hhC.comp hA.contDiffOn (fun z hz => hz)
    exact Q.contDiff.comp_contDiffOn h1
  · -- Hölder bound on compact subsets
    intro K hK hKO
    -- formula for the iterated derivative at every point
    have hformula : ∀ z, iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) z =
        (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ q h (ξ + Q.symm z)).compContinuousLinearMap
            (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) := by
      intro z
      have e1 : (fun z => Q (h (ξ + Q.symm z))) =
          (Q.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) ∘ (fun z => h (ξ + Q.symm z)) := rfl
      rw [e1, ContinuousLinearEquiv.iteratedFDeriv_comp_left]
      congr 1
      have e2 : (fun z => h (ξ + Q.symm z)) =
          (fun w => h (ξ + w)) ∘ (Q.symm.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) := rfl
      have h3 := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
        (Q.symm.toContinuousLinearEquiv : Amb n ℓ ≃L[ℝ] Amb n ℓ) (fun w => h (ξ + w))
        (s := Set.univ) uniqueDiffOn_univ (x := z) (Set.mem_univ _) q
      rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h3
      rw [e2, h3, iteratedFDeriv_comp_add_left]
      rfl
    have hnorm : ∀ z w, ‖iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) z -
        iteratedFDeriv ℝ q (fun z => Q (h (ξ + Q.symm z))) w‖ =
        ‖iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)‖ := by
      intro z w
      have hsub : (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm z)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) -
          (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) =
          (Q.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ).compContinuousMultilinearMap
            ((iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
              (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ))) := by
        ext v
        simp only [LinearIsometryEquiv.toContinuousLinearEquiv_symm, sub_apply,
          ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, PiLp.sub_apply, map_sub]
      rw [hformula, hformula, hsub]
      have hQ := LinearIsometry.norm_compContinuousMultilinearMap Q.toLinearIsometry
        ((iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)).compContinuousLinearMap
          (fun _ => (Q.symm.toContinuousLinearEquiv : Amb n ℓ →L[ℝ] Amb n ℓ)))
      have hQs := ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv
        (iteratedFDeriv ℝ q h (ξ + Q.symm z) - iteratedFDeriv ℝ q h (ξ + Q.symm w)) (fun _ : Fin q => Q.symm)
      exact hQ.trans hQs
    -- the compact image A(K) ⊆ U
    have hAK : IsCompact ((fun z => ξ + Q.symm z) '' K) := hK.image hAcont
    have hAKU : (fun z => ξ + Q.symm z) '' K ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      have := hKO hz
      rw [hO] at this
      exact this
    obtain ⟨C, hC⟩ := hhH _ hAK hAKU
    refine ⟨C, fun z hz w hw => ?_⟩
    rw [hnorm]
    have := hC _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    have hdist : ‖ξ + Q.symm z - (ξ + Q.symm w)‖ = ‖z - w‖ := by
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    rwa [hdist] at this

/-- Derivative of the graph area integrand (Jacobi's formula).  For a linear map `P : ℝⁿ → ℝ^ℓ`
put `g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}` and `J(P) = √(det g(P))`.  Then `J` is differentiable at
`P` and `DJ(P)[Ψ] = J(P) Σ_{a,c} (g(P)⁻¹)_{ac} ⟨P e_c, Ψ eₐ⟩`.
The entries of `g` have derivative `E(Ψ)_{ab} = ⟨P eₐ, Ψ e_b⟩ + ⟨Ψ eₐ, P e_b⟩`, `det` is a
polynomial in the entries (Leibniz formula), and `D det(g)[E] = det g · tr(g⁻¹ E)` because
`det(g + s E) = det g · det(1 + s g⁻¹ E)` (`Matrix.det_one_add_smul`).  Since `det g > 0`
(`dohr_vel_linear_graph_area`) and `g⁻¹` is symmetric, `tr(g⁻¹ E(Ψ)) = 2 Σ_{a,c} (g⁻¹)_{ac} ⟨P e_c, Ψ eₐ⟩`,
and the chain rule for `√` at `det g > 0` gives the formula. -/
theorem dohr_vel_area_integrand_fderiv : ∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, DifferentiableAt ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P ∧ ∀ Ψ : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))))) P Ψ = Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))) * ∑ a : Fin n, ∑ c : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))⁻¹ a c * inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
  intro n ℓ P
  -- the Gram-type matrix as a map into the normed space of arrays, and det on arrays
  let Gm : (Rn n →L[ℝ] Rn ℓ) → (Fin n → Fin n → ℝ) := fun P' a b =>
    (1 : Matrix (Fin n) (Fin n) ℝ) a b +
      inner ℝ (P' (EuclideanSpace.single a (1 : ℝ))) (P' (EuclideanSpace.single b (1 : ℝ)))
  let detPi : (Fin n → Fin n → ℝ) → ℝ := fun M => Matrix.det (Matrix.of M)
  have hJ : (fun P' : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.of fun a b : Fin n => inner ℝ (P' (EuclideanSpace.single a (1 : ℝ)))
        (P' (EuclideanSpace.single b (1 : ℝ)))))) = fun P' => Real.sqrt (detPi (Gm P')) := rfl
  set g : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
    inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) with hg
  have hgG : Matrix.of (Gm P) = g := rfl
  -- g is positive definite, symmetric, invertible
  have hdetpos : 0 < g.det := (dohr_vel_linear_graph_area n ℓ P).1
  have hunit : IsUnit g.det := isUnit_iff_ne_zero.mpr hdetpos.ne'
  have hgT : g.transpose = g := by
    ext a c
    simp only [hg, Matrix.transpose_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    rw [real_inner_comm]
    by_cases hac : a = c
    · subst hac; rfl
    · rw [ite_eq_right hac, ite_eq_right (Ne.symm hac)]
  have hsymm : ∀ a c, g⁻¹ a c = g⁻¹ c a := by
    intro a c
    have h1 : (g⁻¹).transpose = g⁻¹ := by rw [Matrix.transpose_nonsing_inv, hgT]
    have h2 := congrFun (congrFun h1 c) a
    simpa [Matrix.transpose_apply] using h2
  -- derivative of Gm
  let Gd : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Fin n → Fin n → ℝ) :=
    ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
      (fderivInnerCLM ℝ (P (EuclideanSpace.single a (1 : ℝ)), P (EuclideanSpace.single b (1 : ℝ)))).comp
        ((ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).prod
          (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))))
  have hGd : ∀ Ψ a b, Gd Ψ a b = inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (Ψ (EuclideanSpace.single b (1 : ℝ))) +
      inner ℝ (Ψ (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) := by
    intro Ψ a b
    simp [Gd, fderivInnerCLM_apply]
  have hGm : HasFDerivAt Gm Gd P := by
    refine hasFDerivAt_pi.mpr (fun a => hasFDerivAt_pi.mpr (fun b => ?_))
    have ha := (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).hasFDerivAt (x := P)
    have hb := (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).hasFDerivAt (x := P)
    exact (ha.inner ℝ hb).const_add _
  -- det is differentiable on arrays (Leibniz formula)
  have hdetDiff : Differentiable ℝ detPi := by
    have hform : detPi = fun M => ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i := by
      funext M
      simp only [detPi, Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
    rw [hform]
    refine Differentiable.fun_sum (fun σ _ => ?_)
    refine Differentiable.const_mul (fun M => ?_) _
    have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt (fun M : Fin n → Fin n → ℝ => M (σ i) i)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) (σ i))) M := fun i _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) (σ i))).hasFDerivAt
    exact (HasFDerivAt.finsetProd (g := fun i (M : Fin n → Fin n → ℝ) => M (σ i) i) hcoord).differentiableAt
  -- Jacobi's formula for the directional derivative of det at an invertible matrix
  have hdir : ∀ (G E : Fin n → Fin n → ℝ), IsUnit (Matrix.of G).det →
      fderiv ℝ detPi G E = (Matrix.of G).det * Matrix.trace ((Matrix.of G)⁻¹ * Matrix.of E) := by
    intro G E hG
    have h1 : HasDerivAt (fun s : ℝ => G + s • E) E 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const E).const_add G
    have h0 : (fun s : ℝ => G + s • E) 0 = G := by simp
    have hline : HasDerivAt (fun s : ℝ => detPi (G + s • E)) (fderiv ℝ detPi G E) 0 := by
      have h2 := ((hdetDiff G).hasFDerivAt).comp_hasDerivAt_of_eq 0 h1 h0.symm
      exact h2
    set A : Matrix (Fin n) (Fin n) ℝ := (Matrix.of G)⁻¹ * Matrix.of E with hA
    set p2 : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det.divX.divX with hp2
    have heq : (fun s : ℝ => detPi (G + s • E)) =
        fun s => (Matrix.of G).det * (1 + A.trace * s + p2.eval s * s ^ 2) := by
      funext s
      have hm : Matrix.of (G + s • E) = Matrix.of G * (1 + s • A) := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hA, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
        rfl
      show Matrix.det (Matrix.of (G + s • E)) = _
      rw [hm, Matrix.det_mul, Matrix.det_one_add_smul]
    have hpoly : HasDerivAt (fun s : ℝ => (Matrix.of G).det * (1 + A.trace * s + p2.eval s * s ^ 2))
        ((Matrix.of G).det * A.trace) 0 := by
      have h3 : HasDerivAt (fun s : ℝ => 1 + A.trace * s + p2.eval s * s ^ 2)
          (A.trace * 1 + (p2.derivative.eval 0 * 0 ^ 2 + p2.eval 0 * (↑2 * 0 ^ (2 - 1)))) 0 :=
        (((hasDerivAt_id (0 : ℝ)).const_mul A.trace).const_add 1).add
          ((p2.hasDerivAt 0).mul (hasDerivAt_pow 2 (0 : ℝ)))
      have h4 := h3.const_mul (Matrix.of G).det
      convert h4 using 1
      simp
    rw [heq] at hline
    exact hline.unique hpoly
  -- assemble
  have hΔ : HasFDerivAt (fun P' => detPi (Gm P')) ((fderiv ℝ detPi (Gm P)).comp Gd) P :=
    (hdetDiff (Gm P)).hasFDerivAt.comp P hGm
  have hΔpos : 0 < detPi (Gm P) := hdetpos
  have hJd := hΔ.sqrt hΔpos.ne'
  rw [hJ]
  refine ⟨hJd.differentiableAt, fun Ψ => ?_⟩
  rw [hJd.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hdir (Gm P) (Gd Ψ) (by rw [hgG]; exact hunit), hgG]
  have htr : Matrix.trace (g⁻¹ * Matrix.of (Gd Ψ)) =
      2 * ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
        inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hGd, mul_add,
      Finset.sum_add_distrib]
    have h2 : ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
          inner ℝ (Ψ (EuclideanSpace.single c (1 : ℝ))) (P (EuclideanSpace.single a (1 : ℝ))) =
        ∑ a : Fin n, ∑ c : Fin n, g⁻¹ a c *
          inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
      rw [hsymm c a, real_inner_comm]
    rw [h2]
    ring
  have hsq : Real.sqrt (detPi (Gm P)) ^ 2 = detPi (Gm P) := Real.sq_sqrt hΔpos.le
  have hsqpos : 0 < Real.sqrt (detPi (Gm P)) := Real.sqrt_pos.mpr hΔpos
  have hdg : detPi (Gm P) = g.det := rfl
  rw [htr, ← hdg]
  field_simp
  rw [hsq]

/-- Trace of a vertical map composed with the projection onto a rotated graph plane.
Put `b_a = L e_a = (e_a, P e_a)`, so `⟨b_a, b_c⟩ = g_{ac}` with `g = I + (⟨P e_a, P e_b⟩)_{a,b}`;
`g` is symmetric and invertible (`det g > 0` by `dohr_vel_linear_graph_area`).  The projection onto
`τ = range L` is `z ↦ Σ_{a,c} g^{ac} ⟨b_c, z⟩ b_a`
(`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`), and the projection onto `Q⁻¹ τ` is
`Q⁻¹ ∘ p_τ ∘ Q` (`Submodule.starProjection_map_apply`).  Hence `D ∘ p` is the rank-one sum
`z ↦ Σ_{a,c} g^{ac} ⟨Q⁻¹ b_c, z⟩ Q⁻¹(0, Ψ e_a)`, whose trace is `Σ_{a,c} g^{ac} ⟨P e_c, Ψ e_a⟩`
(`LinearMap.trace_smulRight`). -/
theorem dohr_vel_graph_projection_trace : ∀ n ℓ : ℕ, ∀ (P Ψ : Rn n →L[ℝ] Rn ℓ) (L : Rn n →L[ℝ] Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (D : Amb n ℓ →L[ℝ] Amb n ℓ), (∀ v : Rn n, L v = graphPoint v (P v)) → (∀ (v : Rn n) (w : Rn ℓ), D (Q.symm (graphPoint v w)) = Q.symm (graphPoint 0 (Ψ v))) → LinearMap.trace ℝ (Amb n ℓ) (D.toLinearMap ∘ₗ (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range L.toLinearMap)).starProjection.toLinearMap) = ∑ a : Fin n, ∑ c : Fin n, ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))⁻¹ a c * inner ℝ (P (EuclideanSpace.single c (1 : ℝ))) (Ψ (EuclideanSpace.single a (1 : ℝ))) := by
  intro n ℓ P Ψ L Q D hL hD
  have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
      inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
    intro v v' w w'
    simp only [graphPoint, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right]
  set g : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
    inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) with hg
  let bv : Fin n → Amb n ℓ := fun a => L (EuclideanSpace.single a (1 : ℝ))
  have hdet : g.det ≠ 0 := (dohr_vel_linear_graph_area n ℓ P).1.ne'
  have hunit : IsUnit g.det := isUnit_iff_ne_zero.mpr hdet
  have hinvg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hunit
  have hgT : g.transpose = g := by
    ext a c
    simp only [hg, Matrix.transpose_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    rw [real_inner_comm]
    by_cases hac : a = c
    · subst hac; rfl
    · rw [ite_eq_right hac, ite_eq_right (Ne.symm hac)]
  have hsymm : ∀ a c, g⁻¹ a c = g⁻¹ c a := by
    intro a c
    have h1 : (g⁻¹).transpose = g⁻¹ := by rw [Matrix.transpose_nonsing_inv, hgT]
    have h2 := congrFun (congrFun h1 c) a
    simpa [Matrix.transpose_apply] using h2
  -- the orthogonal projection onto the graph plane τ = range L
  have hproj : ∀ z, (LinearMap.range L.toLinearMap).starProjection z =
      ∑ a, ∑ c, (g⁻¹ a c * inner ℝ (bv c) z) • bv a := by
    intro z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · refine Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ ?_))
      exact ⟨EuclideanSpace.single a (1 : ℝ), rfl⟩
    · have hd : ∀ d, inner ℝ (z - ∑ a, ∑ c, (g⁻¹ a c * inner ℝ (bv c) z) • bv a) (bv d) = 0 := by
        intro d
        have hgd : ∀ a, inner ℝ (bv a) (bv d) = g a d := fun a => by
          simp only [bv, hL, hinner, hg, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply,
            EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]
        rw [inner_sub_left, sum_inner]
        simp_rw [sum_inner, real_inner_smul_left, hgd]
        have hswap : ∑ a, ∑ c, g⁻¹ a c * inner ℝ (bv c) z * g a d =
            ∑ c, inner ℝ (bv c) z * ∑ a, g⁻¹ c a * g a d := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hsymm a c]
          ring
        rw [hswap]
        simp_rw [← Matrix.mul_apply, hinvg, Matrix.one_apply]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [real_inner_comm]
        exact sub_self _
      intro w hw
      obtain ⟨v, rfl⟩ := hw
      have hv : v = ∑ a, (v a) • EuclideanSpace.single a (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
        simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
      have hLv : L.toLinearMap v = ∑ a, (v a) • bv a := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul, ContinuousLinearMap.coe_coe, bv]
      rw [hLv, inner_sum]
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [real_inner_smul_right, hd a, mul_zero]
  -- rotate the plane
  have hp : ∀ z, (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range L.toLinearMap)).starProjection z =
      Q.symm ((LinearMap.range L.toLinearMap).starProjection (Q z)) := by
    intro z
    have := Submodule.starProjection_map_apply Q.symm (LinearMap.range L.toLinearMap) z
    rw [LinearIsometryEquiv.symm_symm] at this
    exact this
  have hDb : ∀ a, D (Q.symm (bv a)) = Q.symm (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ)))) := by
    intro a
    simp only [bv, hL]
    exact hD _ _
  have hDp : D.toLinearMap ∘ₗ (Submodule.map Q.symm.toLinearEquiv.toLinearMap
        (LinearMap.range L.toLinearMap)).starProjection.toLinearMap =
      ∑ a, ∑ c, g⁻¹ a c • (innerₛₗ ℝ (Q.symm (bv c))).smulRight
        (Q.symm (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ))))) := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hp, hproj, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      innerₛₗ_apply_apply, hDb]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm, smul_smul]
  rw [hDp]
  simp only [map_sum, map_smul, LinearMap.trace_smulRight, innerₛₗ_apply_apply, LinearIsometryEquiv.inner_map_map,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
  show g⁻¹ a c * inner ℝ (L (EuclideanSpace.single c (1 : ℝ))) (graphPoint 0 (Ψ (EuclideanSpace.single a (1 : ℝ)))) = _
  rw [hL, hinner, inner_zero_right, zero_add]

/-- Area formula for the graph of a `C¹` map.  Let `u` be `C¹` on the open set `D ⊆ ℝⁿ` and
`G(x) = (x, u x)`.  For measurable `A ⊆ D`, `Hⁿ(G(A)) = ∫_A √(det g(Du(x))) dx`, where
`g(P) = I + (⟨P eₐ, P e_b⟩)_{a,b}`.  Near `x₀ ∈ D`, `u` is `ε`-close to `P = Du(x₀)`
(`ApproximatesLinearOn`), so `G` and `v ↦ (v, P v)` are `(1+ε)`-Lipschitz equivalent on a small
ball (`LipschitzOnWith.hausdorffMeasure_image_le`) and `√(det g(Du))` stays within a factor `1+ε`
of `√(det g(P))`.  By `dohr_vel_linear_graph_area` both sides agree up to `(1+ε)^(n+1)` on each
piece of a countable disjoint ball cover of `A`; let `ε → 0`. -/
theorem dohr_vel_graph_area_formula : ∀ n ℓ : ℕ, ∀ (D : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen D → ContDiffOn ℝ 1 u D → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ D → (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) = ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ)))))) := by
  intro n ℓ D u hD hu A hA hAD
  have linArea := dohr_vel_linear_graph_area n ℓ
  have lipCompare : ∀ (u : Rn n → Rn ℓ) (P : Rn n →L[ℝ] Rn ℓ) (c : ℝ≥0) (S : Set (Rn n)),
    ApproximatesLinearOn u P S c →
    (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) ≤
        (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) ∧
      (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (P v)) '' S) ≤
        (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
    intro u P c S hS
    have hinner : ∀ (v v' : Rn n) (w w' : Rn ℓ),
        inner ℝ (graphPoint v w) (graphPoint v' w') = inner ℝ v v' + inner ℝ w w' := by
      intro v v' w w'
      simp [graphPoint, PiLp.inner_apply, Fin.sum_univ_add]
    have hsub : ∀ (v v' : Rn n) (w w' : Rn ℓ), graphPoint v w - graphPoint v' w' = graphPoint (v - v') (w - w') := by
      intro v v' w w'
      ext i
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
    have hadd : ∀ (v v' : Rn n) (w w' : Rn ℓ), graphPoint v w + graphPoint v' w' = graphPoint (v + v') (w + w') := by
      intro v v' w w'
      ext i
      refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
    have hnorm_ge : ∀ (v : Rn n) (w : Rn ℓ), ‖v‖ ≤ ‖graphPoint v w‖ := by
      intro v w
      have h1 : ‖graphPoint v w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hinner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      nlinarith [norm_nonneg v, norm_nonneg w, norm_nonneg (graphPoint v w), sq_nonneg ‖w‖]
    have hnorm0 : ∀ w : Rn ℓ, ‖graphPoint (0 : Rn n) w‖ = ‖w‖ := by
      intro w
      have h1 : ‖graphPoint (0 : Rn n) w‖ ^ 2 = ‖w‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hinner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
        simp
      rw [← Real.sqrt_sq (norm_nonneg (graphPoint (0 : Rn n) w)), h1, Real.sqrt_sq (norm_nonneg w)]
    let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
    have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
      intro x w
      simp [π, graphPoint]
    -- the key two-sided estimate on S
    have hkey : ∀ x ∈ S, ∀ x' ∈ S,
        ‖graphPoint x (u x) - graphPoint x' (u x')‖ ≤ (1 + (c : ℝ)) * ‖graphPoint x (P x) - graphPoint x' (P x')‖ ∧
        ‖graphPoint x (P x) - graphPoint x' (P x')‖ ≤ (1 + (c : ℝ)) * ‖graphPoint x (u x) - graphPoint x' (u x')‖ := by
      intro x hx x' hx'
      have happ : ‖u x - u x' - P (x - x')‖ ≤ (c : ℝ) * ‖x - x'‖ := hS x hx x' hx'
      have hdec : graphPoint (x - x') (u x - u x') =
          graphPoint (x - x') (P (x - x')) + graphPoint 0 (u x - u x' - P (x - x')) := by
        rw [hadd]
        congr 1 <;> abel
      have hP : graphPoint x (P x) - graphPoint x' (P x') = graphPoint (x - x') (P (x - x')) := by
        rw [hsub, map_sub]
      have hU : graphPoint x (u x) - graphPoint x' (u x') = graphPoint (x - x') (u x - u x') := by
        rw [hsub]
      have hc : (0 : ℝ) ≤ c := c.2
      have h1 := hnorm_ge (x - x') (P (x - x'))
      have h2 := hnorm_ge (x - x') (u x - u x')
      constructor
      · rw [hU, hP, hdec]
        calc ‖graphPoint (x - x') (P (x - x')) + graphPoint 0 (u x - u x' - P (x - x'))‖
            ≤ ‖graphPoint (x - x') (P (x - x'))‖ + ‖graphPoint (0 : Rn n) (u x - u x' - P (x - x'))‖ :=
              norm_add_le _ _
          _ ≤ ‖graphPoint (x - x') (P (x - x'))‖ + (c : ℝ) * ‖graphPoint (x - x') (P (x - x'))‖ := by
              rw [hnorm0]
              have := mul_le_mul_of_nonneg_left h1 hc
              linarith
          _ = (1 + (c : ℝ)) * ‖graphPoint (x - x') (P (x - x'))‖ := by ring
      · rw [hU, hP]
        have hdec' : graphPoint (x - x') (P (x - x')) =
            graphPoint (x - x') (u x - u x') - graphPoint 0 (u x - u x' - P (x - x')) := by
          rw [hdec]
          abel
        rw [hdec']
        calc ‖graphPoint (x - x') (u x - u x') - graphPoint 0 (u x - u x' - P (x - x'))‖
            ≤ ‖graphPoint (x - x') (u x - u x')‖ + ‖graphPoint (0 : Rn n) (u x - u x' - P (x - x'))‖ :=
              norm_sub_le _ _
          _ ≤ ‖graphPoint (x - x') (u x - u x')‖ + (c : ℝ) * ‖graphPoint (x - x') (u x - u x')‖ := by
              rw [hnorm0]
              have := mul_le_mul_of_nonneg_left h2 hc
              linarith
          _ = (1 + (c : ℝ)) * ‖graphPoint (x - x') (u x - u x')‖ := by ring
    -- Lipschitz maps between the two images
    have hψ : LipschitzOnWith (1 + c) (fun z => graphPoint (π z) (u (π z))) ((fun v => graphPoint v (P v)) '' S) := by
      refine LipschitzOnWith.of_dist_le_mul (fun y hy y' hy' => ?_)
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      simp only [hπG, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
      exact (hkey x hx x' hx').1
    have hφ : LipschitzOnWith (1 + c) (fun z => graphPoint (π z) (P (π z))) ((fun x => graphPoint x (u x)) '' S) := by
      refine LipschitzOnWith.of_dist_le_mul (fun y hy y' hy' => ?_)
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      simp only [hπG, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
      exact (hkey x hx x' hx').2
    have himg1 : (fun z => graphPoint (π z) (u (π z))) '' ((fun v => graphPoint v (P v)) '' S) =
        (fun x => graphPoint x (u x)) '' S := by
      rw [Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      simp only [hπG]
    have himg2 : (fun z => graphPoint (π z) (P (π z))) '' ((fun x => graphPoint x (u x)) '' S) =
        (fun v => graphPoint v (P v)) '' S := by
      rw [Set.image_image]
      refine Set.image_congr (fun v _ => ?_)
      simp only [hπG]
    have hscale : ∀ (f : Amb n ℓ → Amb n ℓ) (T : Set (Amb n ℓ)), LipschitzOnWith (1 + c) f T →
        (μHE[n] : Measure (Amb n ℓ)) (f '' T) ≤ (1 + (c : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) T := by
      intro f T hf
      have h := hf.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
        ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
      rw [ENNReal.rpow_natCast] at h
      push_cast at h
      calc _ ≤ ((volume : Measure (Rn n)).addHaarScalarFactor μH[(n : ℝ)] : ℝ≥0∞) *
            ((1 + (c : ℝ≥0∞)) ^ n * μH[(n : ℝ)] T) := by gcongr
        _ = _ := by ring
    refine ⟨?_, ?_⟩
    · rw [← himg1]
      exact hscale _ _ hψ
    · rw [← himg2]
      exact hscale _ _ hφ
  set J : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
      (P (EuclideanSpace.single b (1 : ℝ))))) with hJdef
  have hJpos : ∀ P, 0 < J P := fun P => Real.sqrt_pos.mpr (linArea P).1
  have hJcont : Continuous J := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_matrix (fun a b => ?_)
    simp only [Matrix.add_apply, Matrix.of_apply]
    exact continuous_const.add (Continuous.inner
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).continuous
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).continuous)
  have hdiff : ∀ x ∈ D, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (hD.mem_nhds hx)
  have hfcont : ContinuousOn (fderiv ℝ u) D := hu.continuousOn_fderiv_of_isOpen hD le_rfl
  let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
    intro x w
    simp [π, graphPoint]
  have hGinj : Function.Injective (fun x : Rn n => graphPoint x (u x)) := by
    intro x y h
    have := congrArg π h
    simpa [hπG] using this
  have hGcont : ContinuousOn (fun x : Rn n => graphPoint x (u x)) D := by
    intro x hx
    let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
      { toFun := fun p => graphPoint p.1 p.2
        map_add' := by
          intro p q
          ext i
          refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
        map_smul' := by
          intro c p
          ext i
          refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
    have hΓ : Continuous (LinearMap.toContinuousLinearMap Γl) := (LinearMap.toContinuousLinearMap Γl).continuous
    exact (hΓ.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_id.prodMk ((hdiff x hx).continuousAt.continuousWithinAt)))
  -- local two-sided estimate
  have hloc : ∀ ε : ℝ, 0 < ε → ∀ x0 ∈ D, ∃ ρ > 0, ball x0 ρ ⊆ D ∧ ∀ S : Set (Rn n), MeasurableSet S →
      S ⊆ ball x0 ρ →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
    intro ε hε x0 hx0
    have hJP := hJpos (fderiv ℝ u x0)
    have hc2 : ContinuousAt (fderiv ℝ u) x0 := (hfcont x0 hx0).continuousAt (hD.mem_nhds hx0)
    have hc1 : ContinuousAt (fun x => J (fderiv ℝ u x)) x0 := hJcont.continuousAt.comp hc2
    obtain ⟨ρ1, hρ1, h1⟩ := Metric.continuousAt_iff.mp hc1 (ε / (1 + ε) * J (fderiv ℝ u x0)) (by positivity)
    obtain ⟨ρ2, hρ2, h2⟩ := Metric.continuousAt_iff.mp hc2 ε hε
    obtain ⟨ρ3, hρ3, h3⟩ := Metric.isOpen_iff.mp hD x0 hx0
    have hρ : 0 < min ρ1 (min ρ2 ρ3) := lt_min hρ1 (lt_min hρ2 hρ3)
    have hBD : ball x0 (min ρ1 (min ρ2 ρ3)) ⊆ D :=
      (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans h3
    refine ⟨min ρ1 (min ρ2 ρ3), hρ, hBD, fun S hS hSB => ?_⟩
    set c : ℝ≥0 := ⟨ε, hε.le⟩ with hc
    have hcR : (c : ℝ) = ε := rfl
    have hcE : (c : ℝ≥0∞) = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hε.le]
      rfl
    have happrox : ApproximatesLinearOn u (fderiv ℝ u x0) S c := by
      intro x hx y hy
      rw [hcR]
      have hconv : Convex ℝ (ball x0 (min ρ1 (min ρ2 ρ3))) := convex_ball _ _
      have hbound : ∀ z ∈ ball x0 (min ρ1 (min ρ2 ρ3)), ‖fderiv ℝ u z - fderiv ℝ u x0‖ ≤ ε := by
        intro z hz
        have hz' : dist z x0 < ρ2 := lt_of_lt_of_le (mem_ball.mp hz) ((min_le_right _ _).trans (min_le_left _ _))
        have := h2 hz'
        rw [dist_eq_norm] at this
        exact this.le
      have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun z hz => (hdiff z (hBD hz)).hasFDerivAt.hasFDerivWithinAt) hbound (hSB hy) (hSB hx)
      simpa using hmv
    have hJb : ∀ x ∈ S, J (fderiv ℝ u x0) ≤ (1 + ε) * J (fderiv ℝ u x) ∧
        J (fderiv ℝ u x) ≤ (1 + ε) * J (fderiv ℝ u x0) := by
      intro x hx
      have hx1 : dist x x0 < ρ1 := lt_of_lt_of_le (mem_ball.mp (hSB hx)) (min_le_left _ _)
      have hxd := h1 hx1
      rw [Real.dist_eq, abs_lt] at hxd
      have hJx := hJpos (fderiv ℝ u x)
      have key : ε / (1 + ε) * J (fderiv ℝ u x0) * (1 + ε) = ε * J (fderiv ℝ u x0) := by
        field_simp
      constructor
      · nlinarith
      · have : ε / (1 + ε) * J (fderiv ℝ u x0) ≤ ε * J (fderiv ℝ u x0) := by
          have h1e : (1 : ℝ) ≤ 1 + ε := by linarith
          have : ε / (1 + ε) ≤ ε := div_le_self hε.le h1e
          exact mul_le_mul_of_nonneg_right this hJP.le
        nlinarith
    obtain ⟨hLC1, hLC2⟩ := lipCompare u (fderiv ℝ u x0) c S happrox
    have hLA := (linArea (fderiv ℝ u x0)).2 S
    have hfac : (1 + (c : ℝ≥0∞)) ^ n = ENNReal.ofReal ((1 + ε) ^ n) := by
      rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_add zero_le_one hε.le, ENNReal.ofReal_one, hcE]
    have hfac2 : ENNReal.ofReal ((1 + ε) ^ (n + 1)) = ENNReal.ofReal ((1 + ε) ^ n) * ENNReal.ofReal (1 + ε) := by
      rw [pow_succ, ENNReal.ofReal_mul (by positivity)]
    have hconst : ∫⁻ _ in S, ENNReal.ofReal (J (fderiv ℝ u x0)) =
        ENNReal.ofReal (J (fderiv ℝ u x0)) * (volume : Measure (Rn n)) S := by
      rw [setLIntegral_const]
    constructor
    · calc (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S)
          ≤ ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal (J (fderiv ℝ u x0)) * (volume : Measure (Rn n)) S) := by
            rw [← hfac, ← hLA]; exact hLC1
        _ = ENNReal.ofReal ((1 + ε) ^ n) * ∫⁻ _ in S, ENNReal.ofReal (J (fderiv ℝ u x0)) := by rw [hconst]
        _ ≤ ENNReal.ofReal ((1 + ε) ^ n) * ∫⁻ x in S, ENNReal.ofReal (1 + ε) * ENNReal.ofReal (J (fderiv ℝ u x)) := by
            refine mul_le_mul' le_rfl (setLIntegral_mono' hS (fun x hx => ?_))
            rw [← ENNReal.ofReal_mul (by linarith)]
            exact ENNReal.ofReal_le_ofReal (hJb x hx).1
        _ = ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hfac2, mul_assoc]
    · calc ∫⁻ x in S, ENNReal.ofReal (J (fderiv ℝ u x))
          ≤ ∫⁻ _ in S, ENNReal.ofReal (1 + ε) * ENNReal.ofReal (J (fderiv ℝ u x0)) := by
            refine setLIntegral_mono' hS (fun x hx => ?_)
            rw [← ENNReal.ofReal_mul (by linarith)]
            exact ENNReal.ofReal_le_ofReal (hJb x hx).2
        _ = ENNReal.ofReal (1 + ε) * (μHE[n] : Measure (Amb n ℓ)) ((fun v => graphPoint v (fderiv ℝ u x0 v)) '' S) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hconst, hLA]
        _ ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal ((1 + ε) ^ n) *
              (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S)) := by
            refine mul_le_mul' le_rfl ?_
            rw [← hfac]
            exact hLC2
        _ = ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' S) := by
            rw [hfac2]
            ring
  -- global two-sided estimate on A
  have hglob : ∀ ε : ℝ, 0 < ε →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) := by
    intro ε hε
    choose! ρ hρpos hρD hρest using hloc ε hε
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : D => ball (x : Rn n) (ρ x)) (fun _ => isOpen_ball)
    have hDcov : D ⊆ ⋃ i ∈ T, ball ((i : D) : Rn n) (ρ i) := by
      intro x hx
      rw [hTU]
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρpos x hx)⟩
    rcases T.eq_empty_or_nonempty with hT | hT
    · have hA0 : A = ∅ := by
        apply Set.subset_eq_empty (hAD.trans hDcov)
        simp [hT]
      subst hA0
      simp
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hT
    let B : ℕ → Set (Rn n) := fun k => ball ((f k : D) : Rn n) (ρ (f k))
    have hAcov : A ⊆ ⋃ k, B k := by
      intro x hx
      have := hDcov (hAD hx)
      rw [hf] at this
      simp only [Set.mem_iUnion, Set.mem_range, exists_prop] at this
      obtain ⟨i, ⟨k, rfl⟩, hxi⟩ := this
      exact Set.mem_iUnion.mpr ⟨k, hxi⟩
    let C : ℕ → Set (Rn n) := fun k => A ∩ disjointed B k
    have hCmeas : ∀ k, MeasurableSet (C k) := fun k =>
      hA.inter (MeasurableSet.disjointed (fun j => measurableSet_ball) k)
    have hCdisj : Pairwise (Function.onFun Disjoint C) := by
      intro i j hij
      exact ((disjoint_disjointed B) hij).mono Set.inter_subset_right Set.inter_subset_right
    have hCunion : ⋃ k, C k = A := by
      simp only [C, ← Set.inter_iUnion, iUnion_disjointed]
      exact Set.inter_eq_left.mpr hAcov
    have hCB : ∀ k, C k ⊆ B k := fun k => Set.inter_subset_right.trans (disjointed_subset B k)
    have hGCmeas : ∀ k, MeasurableSet ((fun x => graphPoint x (u x)) '' C k) := fun k =>
      (hCmeas k).image_of_continuousOn_injOn (hGcont.mono ((Set.inter_subset_left).trans hAD))
        hGinj.injOn
    have hGCdisj : Pairwise (Function.onFun Disjoint (fun k => (fun x => graphPoint x (u x)) '' C k)) := by
      intro i j hij
      exact (Set.disjoint_image_iff hGinj).mpr (hCdisj hij)
    have hGA : (fun x => graphPoint x (u x)) '' A = ⋃ k, (fun x => graphPoint x (u x)) '' C k := by
      rw [← Set.image_iUnion, hCunion]
    have hmeasG : (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' A) =
        ∑' k, (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) := by
      rw [hGA, measure_iUnion hGCdisj hGCmeas]
    have hlintA : ∫⁻ x in A, ENNReal.ofReal (J (fderiv ℝ u x)) =
        ∑' k, ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) := by
      conv_lhs => rw [← hCunion]
      exact lintegral_iUnion hCmeas hCdisj _
    have hk : ∀ k, (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) ∧
        ∫⁻ x in C k, ENNReal.ofReal (J (fderiv ℝ u x)) ≤
          ENNReal.ofReal ((1 + ε) ^ (n + 1)) * (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' C k) :=
      fun k => hρest (f k) (f k).2 (C k) (hCmeas k) (hCB k)
    constructor
    · rw [hmeasG, hlintA, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun k => (hk k).1)
    · rw [hmeasG, hlintA, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun k => (hk k).2)
  -- let ε → 0
  have hlim : ∀ X Y : ℝ≥0∞, (∀ ε : ℝ, 0 < ε → X ≤ ENNReal.ofReal ((1 + ε) ^ (n + 1)) * Y) → X ≤ Y := by
    intro X Y hXY
    by_cases hY : Y = ⊤
    · rw [hY]; exact le_top
    · have h0 : Tendsto (fun ε : ℝ => (1 + ε) ^ (n + 1)) (𝓝[>] 0) (𝓝 1) := by
        have hcont : Continuous (fun ε : ℝ => (1 + ε) ^ (n + 1)) := (continuous_const.add continuous_id).pow (n + 1)
        have h := hcont.tendsto (0 : ℝ)
        simp only [add_zero, one_pow] at h
        exact h.mono_left nhdsWithin_le_nhds
      have htend : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε) ^ (n + 1)) * Y) (𝓝[>] 0) (𝓝 (1 * Y)) := by
        refine ENNReal.Tendsto.mul_const ?_ (Or.inr hY)
        simpa using ENNReal.tendsto_ofReal h0
      rw [one_mul] at htend
      exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall (fun ε hε => hXY ε hε))
  exact le_antisymm (hlim _ _ (fun ε hε => (hglob ε hε).1)) (hlim _ _ (fun ε hε => (hglob ε hε).2))

/-- Area transport onto a graph piece of `spt V`: if `Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)` with
`u ∈ C¹(B̆ⁿ_R(0))`, `s ≤ R` and `μ_V ⌞ B̆_s(ξ) = Hⁿ ⌞ (spt V ∩ B̆_s(ξ))`, then for every `f`
`∫_{B̆_s(ξ)} f dμ_V = ∫_{D_s} J(Du) f(Φ(x)) dx`, where `D_s = {x ∈ B̆ⁿ_R(0) : |(x, u(x))| < s}`,
`Φ(x) = ξ + Q⁻¹(x, u(x))` and `J(P) = √det(I + PᵀP)`.  Proof: `spt V ∩ B̆_s(ξ) = Φ(D_s)`, and
`Φ|_{D_s}` is a measurable embedding pushing `J(Du) dx` forward to `Hⁿ ⌞ Φ(D_s)` by
`dohr_vel_graph_area_formula` and isometry invariance of `Hⁿ`. -/
theorem dohr_vel_graph_area_transport : ∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), s ≤ R → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) → ∀ f : Amb n ℓ → ℝ, ∫ y in ball ξ s, f y ∂V.weight = ∫ x in {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s}, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * f (ξ + Q.symm (graphPoint x (u x))) := by
  intro n ℓ U V ξ s R Q u hsR hu hgraph hmeas f
  -- `G(x) = (x, u(x))` is continuous on `B̆ⁿ_R(0)`; `π` recovers `x` from `G(x)`.
  have hdiff : ∀ x ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  let π : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hπG : ∀ (x : Rn n) (w : Rn ℓ), π (graphPoint x w) = x := by
    intro x w
    simp [π, graphPoint]
  let Γl : (Rn n × Rn ℓ) →ₗ[ℝ] Amb n ℓ :=
    { toFun := fun p => graphPoint p.1 p.2
      map_add' := by
        intro p q
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
      map_smul' := by
        intro c p
        ext i
        refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint] }
  have hGc : ContinuousOn (fun z : Rn n => graphPoint z (u z)) (ball 0 R) := fun x hx =>
    ((LinearMap.toContinuousLinearMap Γl).continuous.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_id.prodMk ((hdiff x hx).continuousAt.continuousWithinAt)))
  -- Step 2: `D_s` is open and contained in `B̆ⁿ_R(0)`.
  set Ds := {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} with hDsdef
  have hDo : IsOpen Ds := by
    have := hGc.isOpen_inter_preimage isOpen_ball (isOpen_ball : IsOpen (ball (0 : Amb n ℓ) s))
    convert this using 1
    ext x
    simp [hDsdef]
  have hDsR : Ds ⊆ ball 0 R := fun x hx => hx.1
  -- Step 3: `Σ ∩ B̆_s(ξ) = Φ(D_s)` with `Φ(x) = ξ + Q⁻¹(G x)`.
  set Φ : Rn n → Amb n ℓ := fun x => ξ + Q.symm (graphPoint x (u x)) with hΦdef
  have hset : V.support ∩ ball ξ s = Φ '' Ds := by
    ext y
    constructor
    · rintro ⟨hyS, hyb⟩
      have hTy : Q (y - ξ) ∈ graphOver u (ball 0 R) ∩ ball 0 R := by
        rw [← hgraph]
        refine ⟨⟨y - ξ, ⟨y, hyS, rfl⟩, rfl⟩, ?_⟩
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact lt_of_lt_of_le (mem_ball.mp hyb) hsR
      obtain ⟨⟨x, hxR, hxG⟩, -⟩ := hTy
      have hxG' : graphPoint x (u x) = Q (y - ξ) := hxG
      refine ⟨x, ⟨hxR, ?_⟩, ?_⟩
      · rw [hxG', LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact mem_ball.mp hyb
      · show ξ + Q.symm (graphPoint x (u x)) = y
        rw [hxG', LinearIsometryEquiv.symm_apply_apply]
        abel
    · rintro ⟨x, ⟨hxR, hxs⟩, rfl⟩
      have hGx : graphPoint x (u x) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R := by
        rw [hgraph]
        exact ⟨⟨x, hxR, rfl⟩, by rw [mem_ball_zero_iff]; exact lt_of_lt_of_le hxs hsR⟩
      obtain ⟨⟨z, ⟨y, hyS, rfl⟩, hz⟩, -⟩ := hGx
      have hz' : Q (y - ξ) = graphPoint x (u x) := hz
      refine ⟨?_, ?_⟩
      · show ξ + Q.symm (graphPoint x (u x)) ∈ V.support
        rw [← hz', LinearIsometryEquiv.symm_apply_apply]
        simpa using hyS
      · rw [mem_ball, dist_eq_norm]
        show ‖ξ + Q.symm (graphPoint x (u x)) - ξ‖ < s
        rw [add_sub_cancel_left, LinearIsometryEquiv.norm_map]
        exact hxs
  -- Step 4: `Φ` is continuous and injective on `D_s`; `z ↦ ξ + Q⁻¹ z` is an isometry.
  have hΦcont : ContinuousOn Φ Ds :=
    (continuous_const.add Q.symm.continuous).comp_continuousOn (hGc.mono hDsR)
  have hΦinj : Set.InjOn Φ Ds := by
    intro x _ x' _ h
    have h1 : graphPoint x (u x) = graphPoint x' (u x') := Q.symm.injective (add_left_cancel h)
    have := congrArg π h1
    rwa [hπG, hπG] at this
  have hAisom : Isometry (fun z : Amb n ℓ => ξ + Q.symm z) := by
    refine Isometry.of_dist_eq (fun z z' => ?_)
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 5: set-level area formula `Hⁿ(Φ B) = ∫_B J(Du)` for measurable `B ⊆ D_s`.
  have hsetF : ∀ B : Set (Rn n), MeasurableSet B → B ⊆ Ds →
      (μHE[n] : Measure (Amb n ℓ)) (Φ '' B) =
        ∫⁻ x in B, ENNReal.ofReal (Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ)))))) := by
    intro B hB hBD
    have hΦB : Φ '' B = (fun z : Amb n ℓ => ξ + Q.symm z) '' ((fun x => graphPoint x (u x)) '' B) := by
      rw [Set.image_image]
    rw [hΦB, hAisom.euclideanHausdorffMeasure_image]
    exact Submission.dohr_vel_graph_area_formula n ℓ Ds u hDo (hu.mono hDsR) B hB hBD
  -- Step 6: the area density `J(Du)` is measurable and nonnegative.
  set Jf : Rn n → ℝ := fun x => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
      (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) with hJfdef
  have hJcont : Continuous (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
        (P (EuclideanSpace.single b (1 : ℝ)))))) := by
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_matrix (fun a b => ?_)
    simp only [Matrix.add_apply, Matrix.of_apply]
    exact continuous_const.add (Continuous.inner
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single a (1 : ℝ))).continuous
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single b (1 : ℝ))).continuous)
  have hJfmeas : Measurable Jf := hJcont.measurable.comp (measurable_fderiv ℝ u)
  have hJfnn : ∀ x, 0 ≤ Jf x := fun x => Real.sqrt_nonneg _
  -- Step 7: `Φ|_{D_s}` pushes `(J(Du) dx)|_{D_s}` forward to `Hⁿ ⌞ Φ(D_s)`.
  have hemb : MeasurableEmbedding (Ds.domRestrict Φ) := hΦcont.measurableEmbedding hDo.measurableSet hΦinj
  have hsub := MeasurableEmbedding.subtype_coe hDo.measurableSet
  have hmap : Measure.map (Ds.domRestrict Φ)
      (((volume : Measure (Rn n)).withDensity (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) =
      (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' Ds) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((Ds.domRestrict Φ) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((Ds.domRestrict Φ) ⁻¹' t) ⊆ Ds := by
      rintro x ⟨w, _, rfl⟩
      exact w.property
    rw [withDensity_apply _ hB, ← hsetF _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨hw, ⟨w, w.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  -- Step 8: transport the integral of an arbitrary `f`.
  calc ∫ y in ball ξ s, f y ∂V.weight
      = ∫ y in V.support ∩ ball ξ s, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by rw [hmeas]
    _ = ∫ y in Φ '' Ds, f y ∂(μHE[n] : Measure (Amb n ℓ)) := by rw [hset]
    _ = ∫ z, f (Ds.domRestrict Φ z) ∂(((volume : Measure (Rn n)).withDensity
          (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) := by
        rw [← hmap, hemb.integral_map]
    _ = ∫ x in Ds, f (Φ x) ∂((volume : Measure (Rn n)).withDensity (fun x => ENNReal.ofReal (Jf x))) := by
        have h2 := hsub.integral_map (μ := ((volume : Measure (Rn n)).withDensity
          (fun x => ENNReal.ofReal (Jf x))).comap (Subtype.val : Ds → Rn n)) (fun x => f (Φ x))
        rw [map_comap_subtype_coe hDo.measurableSet] at h2
        exact h2.symm
    _ = ∫ x in Ds, Jf x * f (Φ x) := by
        have h1 : (fun x => ENNReal.ofReal (Jf x)) = fun x => ((Real.toNNReal (Jf x) : ℝ≥0) : ℝ≥0∞) := rfl
        rw [h1, setIntegral_withDensity_eq_setIntegral_smul (hJfmeas.real_toNNReal) _ hDo.measurableSet]
        refine setIntegral_congr_fun hDo.measurableSet (fun x _ => ?_)
        rw [NNReal.smul_def, Real.coe_toNNReal _ (hJfnn x), smul_eq_mul]

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
/-- Two-point blow-up estimate for a `C¹` map `G` on an open `U ⊆ ℝⁿ` at `x ∈ U`: for all small
`t > 0`, `x + t • v ∈ U` for `v ∈ B_ρ(0)`, and `v ↦ t⁻¹ • G (x + t • v)` is `ε`-close to
`L = DG(x)` in Lipschitz norm on `B_ρ(0)`.  Choose `δ > 0` with `B̆_δ(x) ⊆ U` and
`‖DG(z) − L‖ ≤ ε` on `B̆_δ(x)` (`G` is differentiable on the open `U` and `DG` is continuous
there); for `0 < t < δ / (|ρ| + 1)` the points `x + t • v` lie in `B̆_δ(x)`.  By the chain rule
`h v = t⁻¹ • G (x + t • v) − L v` has derivative `DG(x + t • v) − L` (as `t⁻¹ • t = 1`), of norm
`≤ ε`, so the mean value inequality on the convex ball gives `‖h v − h v'‖ ≤ ε ‖v − v'‖`, which
is the claim by linearity. -/
theorem dohr_tp_gat_blowup_two_point : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (G : Rn n → Amb n ℓ) (x : Rn n) (ρ ε : ℝ), IsOpen U → ContDiffOn ℝ 1 G U → x ∈ U → 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ v ∈ closedBall (0 : Rn n) ρ, x + t • v ∈ U) ∧ ∀ v ∈ closedBall (0 : Rn n) ρ, ∀ v' ∈ closedBall (0 : Rn n) ρ, ‖t⁻¹ • (G (x + t • v) - G (x + t • v')) - fderiv ℝ G x (v - v')‖ ≤ ε * ‖v - v'‖ := by
  intro n ℓ U G x ρ ε hU hG hx hε
  -- `G` is differentiable on `U` and `z ↦ DG(z)` is continuous on `U`.
  have hdiff : DifferentiableOn ℝ G U := hG.differentiableOn one_ne_zero
  have hcont : ContinuousOn (fderiv ℝ G) U := hG.continuousOn_fderiv_of_isOpen hU le_rfl
  -- A ball `B̆_δ(x) ⊆ U`, `δ = min δ₀ δ₁`, on which `‖DG(z) − DG(x)‖ ≤ ε`.
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousOn_iff.mp hcont x hx ε hε
  have hδ : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
  have hsub : ball x (min δ₀ δ₁) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hball
  have hder : ∀ z ∈ ball x (min δ₀ δ₁), ‖fderiv ℝ G z - fderiv ℝ G x‖ ≤ ε := by
    intro z hz
    have h₁ := hδ₁' z (hsub hz) (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
    rw [dist_eq_norm] at h₁
    exact h₁.le
  -- The scales `0 < t < δ / (|ρ| + 1)`: then `x + t • v ∈ B̆_δ(x)` for `v ∈ B_ρ(0)`.
  have hρ : 0 < |ρ| + 1 := by positivity
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hρ)] with t ht
  obtain ⟨ht0, htδ⟩ := ht
  have hmem : ∀ v ∈ closedBall (0 : Rn n) ρ, x + t • v ∈ ball x (min δ₀ δ₁) := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
    have hv' : ‖v‖ < |ρ| + 1 :=
      lt_of_le_of_lt ((mem_closedBall_zero_iff.mp hv).trans (le_abs_self ρ)) (lt_add_one _)
    calc t * ‖v‖ ≤ t * (|ρ| + 1) := mul_le_mul_of_nonneg_left hv'.le ht0.le
      _ < min δ₀ δ₁ := (lt_div_iff₀ hρ).mp htδ
  refine ⟨fun v hv => hsub (hmem v hv), ?_⟩
  -- `h w = t⁻¹ • G (x + t • w) - DG(x) w` has derivative `DG(x + t • v) − DG(x)` at `v`.
  have hderiv : ∀ v ∈ closedBall (0 : Rn n) ρ,
      HasFDerivWithinAt (fun w => t⁻¹ • G (x + t • w) - fderiv ℝ G x w)
        (fderiv ℝ G (x + t • v) - fderiv ℝ G x) (closedBall (0 : Rn n) ρ) v := by
    intro v hv
    have hGd : HasFDerivAt G (fderiv ℝ G (x + t • v)) (x + t • v) :=
      (hdiff.differentiableAt (hU.mem_nhds (hsub (hmem v hv)))).hasFDerivAt
    have haff : HasFDerivAt (fun w : Rn n => x + t • w) (t • ContinuousLinearMap.id ℝ (Rn n)) v :=
      ((ContinuousLinearMap.id ℝ (Rn n)).hasFDerivAt.const_smul t).const_add x
    have h₂ := ((hGd.comp v haff).const_smul t⁻¹).sub (fderiv ℝ G x).hasFDerivAt
    have heq : t⁻¹ • ((fderiv ℝ G (x + t • v)).comp (t • ContinuousLinearMap.id ℝ (Rn n))) -
        fderiv ℝ G x = fderiv ℝ G (x + t • v) - fderiv ℝ G x := by
      ext w
      simp [smul_smul, inv_mul_cancel₀ ht0.ne']
    rw [heq] at h₂
    exact h₂.hasFDerivWithinAt
  -- The mean value inequality on the convex ball `B_ρ(0)`, then linearity of `t⁻¹ • ·` and `DG(x)`.
  intro v hv v' hv'
  have key := (convex_closedBall (0 : Rn n) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv (fun w hw => hder _ (hmem w hw)) hv' hv
  have hrw : t⁻¹ • (G (x + t • v) - G (x + t • v')) - fderiv ℝ G x (v - v') =
      (t⁻¹ • G (x + t • v) - fderiv ℝ G x v) - (t⁻¹ • G (x + t • v') - fderiv ℝ G x v') := by
    rw [smul_sub, map_sub]
    abel
  rw [hrw]
  exact key

end Submission

namespace Submission

/-- Near-isometries change `Hⁿ` by at most the factor `(1 - δ)⁻ⁿ`: if `0 ≤ δ < 1`, `A` is
measurable and `‖Φ p - Φ q - (p - q)‖ ≤ δ‖p - q‖` on `A`, then
`Hⁿ ⌞ Φ(A) ≤ (1 - δ)⁻ⁿ Φ_#(Hⁿ ⌞ A)` and `Φ_#(Hⁿ ⌞ A) ≤ (1 - δ)⁻ⁿ Hⁿ ⌞ Φ(A)`.
`Φ` is `(1 + δ)`-Lipschitz on `A` and `invFunOn Φ A` is `(1 - δ)⁻¹`-Lipschitz on `Φ(A)`, while
`1 + δ ≤ (1 - δ)⁻¹`; so Simon Ch. 2, 1.8(i) (`Hⁿ(f(T)) ≤ (Lip f)ⁿ Hⁿ(T)`, any `T`), applied to
`Φ⁻¹(S) ∩ A` and to `Φ(Φ⁻¹(S) ∩ A) = S ∩ Φ(A)`, gives both inequalities on measurable `S`. -/
theorem dohr_tp_gat_bilip_measure_comparison : ∀ (n ℓ : ℕ) (A : Set (Amb n ℓ)) (Φ : Amb n ℓ → Amb n ℓ) (δ : ℝ), MeasurableSet A → 0 ≤ δ → δ < 1 → (∀ p ∈ A, ∀ q ∈ A, ‖Φ p - Φ q - (p - q)‖ ≤ δ * ‖p - q‖) → (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ∧ Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) • (μHE[n] : Measure (Amb n ℓ)).restrict (Φ '' A) := by
  intro n ℓ A Φ δ hA hδ0 hδ1 hΦ
  have h1δ : 0 < 1 - δ := sub_pos.2 hδ1
  -- `(1 - δ)‖p - q‖ ≤ ‖Φ p - Φ q‖ ≤ (1 + δ)‖p - q‖` on `A`.
  have hup : ∀ p ∈ A, ∀ q ∈ A, ‖Φ p - Φ q‖ ≤ (1 + δ) * ‖p - q‖ := by
    intro p hp q hq
    calc ‖Φ p - Φ q‖ = ‖(Φ p - Φ q - (p - q)) + (p - q)‖ := by rw [sub_add_cancel]
      _ ≤ ‖Φ p - Φ q - (p - q)‖ + ‖p - q‖ := norm_add_le _ _
      _ ≤ δ * ‖p - q‖ + ‖p - q‖ := add_le_add (hΦ p hp q hq) le_rfl
      _ = (1 + δ) * ‖p - q‖ := by ring
  have hlow : ∀ p ∈ A, ∀ q ∈ A, (1 - δ) * ‖p - q‖ ≤ ‖Φ p - Φ q‖ := by
    intro p hp q hq
    have h : ‖p - q‖ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := by
      calc ‖p - q‖ = ‖(Φ p - Φ q) - (Φ p - Φ q - (p - q))‖ := by rw [sub_sub_cancel]
        _ ≤ ‖Φ p - Φ q‖ + ‖Φ p - Φ q - (p - q)‖ := norm_sub_le _ _
    linarith [hΦ p hp q hq]
  -- `Φ` is `(1 + δ)`-Lipschitz on `A`, hence a.e.-measurable for `Hⁿ ⌞ A`.
  have hLipΦ : LipschitzOnWith (Real.toNNReal (1 + δ)) Φ A := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
    exact hup p hp q hq
  have hΦm : AEMeasurable Φ ((μHE[n] : Measure (Amb n ℓ)).restrict A) :=
    hLipΦ.continuousOn.aemeasurable hA
  -- `Φ` is injective on `A`; `Ψ = invFunOn Φ A` is a `(1 - δ)⁻¹`-Lipschitz left inverse on `Φ(A)`.
  have hinj : InjOn Φ A := by
    intro p hp q hq hpq
    have h := hlow p hp q hq
    rw [hpq, sub_self, norm_zero] at h
    have h' : ‖p - q‖ ≤ 0 := nonpos_of_mul_nonpos_right h h1δ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have hleft : LeftInvOn (Function.invFunOn Φ A) Φ A := hinj.leftInvOn_invFunOn
  have hLipΨ : LipschitzOnWith (Real.toNNReal ((1 - δ)⁻¹)) (Function.invFunOn Φ A) (Φ '' A) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hleft hp, hleft hq, dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.2 h1δ.le), inv_mul_eq_div, le_div_iff₀ h1δ, mul_comm]
    exact hlow p hp q hq
  -- The constants: `κ̂ = ((1 - δ)⁻¹)ⁿ` in `[0, ∞]`, and `(1 + δ)ⁿ ≤ κ̂` since `(1 + δ)(1 - δ) ≤ 1`.
  have hκ : ENNReal.ofReal (((1 - δ)⁻¹) ^ n) = ((Real.toNNReal ((1 - δ)⁻¹) : ℝ≥0∞)) ^ n :=
    ENNReal.ofReal_pow (inv_nonneg.2 h1δ.le) n
  have hκ' : ((Real.toNNReal (1 + δ) : ℝ≥0∞)) ^ n ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) := by
    rw [hκ]
    gcongr
    rw [← one_div, le_div_iff₀ h1δ]
    nlinarith
  -- For measurable `S`: `Φ_#(Hⁿ ⌞ A)(S) = Hⁿ(Φ⁻¹(S) ∩ A)`, `(Hⁿ ⌞ Φ(A))(S) = Hⁿ(Φ(Φ⁻¹(S) ∩ A))`;
  -- the Lipschitz image bound (Simon Ch. 2, 1.8(i)) for `Φ` and for `Ψ` gives the two inequalities.
  refine ⟨Measure.le_iff.2 fun S hS => ?_, Measure.le_iff.2 fun S hS => ?_⟩
  · rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
      Measure.restrict_apply hS, ← image_preimage_inter, smul_eq_mul]
    calc (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A))
        ≤ ((Real.toNNReal (1 + δ) : ℝ≥0∞)) ^ n * (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipΦ.mono inter_subset_right)
      _ ≤ ENNReal.ofReal (((1 - δ)⁻¹) ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A) := by
          gcongr
  · rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
      Measure.restrict_apply hS, ← image_preimage_inter, smul_eq_mul]
    calc (μHE[n] : Measure (Amb n ℓ)) (Φ ⁻¹' S ∩ A)
        = (μHE[n] : Measure (Amb n ℓ)) (Function.invFunOn Φ A '' (Φ '' (Φ ⁻¹' S ∩ A))) := by
          rw [hleft.image_image' inter_subset_right]
      _ ≤ ((Real.toNNReal ((1 - δ)⁻¹) : ℝ≥0∞)) ^ n *
            (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hLipΨ.mono (image_mono inter_subset_right))
      _ = ENNReal.ofReal (((1 - δ)⁻¹) ^ n) * (μHE[n] : Measure (Amb n ℓ)) (Φ '' (Φ ⁻¹' S ∩ A)) := by
          rw [hκ]
/-- Integral comparison for mutually bounded measures (the bi-Lipschitz sandwich step for
Simon Ch. 5, Theorem 7.1): if `μ₁ ≤ κ μ₂` and `μ₂ ≤ κ μ₁` with `κ ≥ 1`, `μ₂` is finite and `φ` is
continuous with `|φ| ≤ M`, then `|∫ φ dμ₁ - ∫ φ dμ₂| ≤ 2 (κ - 1) κ M μ₂(ℝ^{n+ℓ})`.
For continuous `g` with values in `[0, M]`, `a = ∫ g dμ₂ ∈ [0, M μ₂(ℝ^{n+ℓ})]` and `b = ∫ g dμ₁`
satisfy `b ≤ κ a` and `a ≤ κ b`, so `|b - a| ≤ (κ - 1) κ a`; apply this to `max φ 0` and
`max (-φ) 0`, whose difference is `φ`. -/
theorem dohr_tp_gat_bilip_integral_sandwich : ∀ (n ℓ : ℕ) (μ₁ μ₂ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (κ M : ℝ), IsFiniteMeasure μ₂ → Continuous φ → (∀ w, |φ w| ≤ M) → 1 ≤ κ → μ₁ ≤ ENNReal.ofReal κ • μ₂ → μ₂ ≤ ENNReal.ofReal κ • μ₁ → |∫ w, φ w ∂μ₁ - ∫ w, φ w ∂μ₂| ≤ 2 * ((κ - 1) * κ * (M * (μ₂ univ).toReal)) := by
  intro n ℓ μ₁ μ₂ φ κ M hμ₂ hφ hM hκ h12 h21
  have hκ0 : 0 ≤ κ := by linarith
  have hκ1 : 0 ≤ κ - 1 := by linarith
  have hκtop : ENNReal.ofReal κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκreal : (ENNReal.ofReal κ).toReal = κ := ENNReal.toReal_ofReal hκ0
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- `μ₁ ≤ κ μ₂` makes `μ₁` finite.
  have hμ₁ : IsFiniteMeasure μ₁ := by
    refine ⟨lt_of_le_of_lt (Measure.le_iff'.1 h12 univ) ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ₂ univ)
  -- The comparison for a continuous `g` with values in `[0, M]`.
  have key : ∀ g : Amb n ℓ → ℝ, Continuous g → (∀ w, 0 ≤ g w) → (∀ w, g w ≤ M) →
      |∫ w, g w ∂μ₁ - ∫ w, g w ∂μ₂| ≤ (κ - 1) * κ * (M * (μ₂ univ).toReal) := by
    intro g hg hg0 hgM
    have hgb : ∀ w, ‖g w‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
      exact hgM w
    have hi₁ : Integrable g μ₁ := Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ hgb)
    have hi₂ : Integrable g μ₂ := Integrable.of_bound hg.aestronglyMeasurable M (ae_of_all _ hgb)
    have ha0 : 0 ≤ ∫ w, g w ∂μ₂ := integral_nonneg hg0
    have haM : ∫ w, g w ∂μ₂ ≤ M * (μ₂ univ).toReal := by
      have h := norm_integral_le_of_norm_le_const (μ := μ₂) (ae_of_all _ hgb)
      rw [Real.norm_eq_abs, measureReal_def] at h
      exact (le_abs_self _).trans h
    have hba : ∫ w, g w ∂μ₁ ≤ κ * ∫ w, g w ∂μ₂ :=
      calc ∫ w, g w ∂μ₁ ≤ ∫ w, g w ∂(ENNReal.ofReal κ • μ₂) :=
            integral_mono_measure h12 (ae_of_all _ hg0) (hi₂.smul_measure hκtop)
        _ = κ * ∫ w, g w ∂μ₂ := by rw [integral_smul_measure, hκreal, smul_eq_mul]
    have hab : ∫ w, g w ∂μ₂ ≤ κ * ∫ w, g w ∂μ₁ :=
      calc ∫ w, g w ∂μ₂ ≤ ∫ w, g w ∂(ENNReal.ofReal κ • μ₁) :=
            integral_mono_measure h21 (ae_of_all _ hg0) (hi₁.smul_measure hκtop)
        _ = κ * ∫ w, g w ∂μ₁ := by rw [integral_smul_measure, hκreal, smul_eq_mul]
    -- With `a = ∫ g dμ₂`, `b = ∫ g dμ₁`, `V = μ₂(ℝ^{n+ℓ})`:
    -- `b - a ≤ (κ - 1) a ≤ (κ - 1) κ a ≤ (κ - 1) κ M V` and
    -- `a - b ≤ (κ - 1) b ≤ (κ - 1) κ a ≤ (κ - 1) κ M V`.
    have h1 : 0 ≤ (κ - 1) * ((κ - 1) * ∫ w, g w ∂μ₂) := mul_nonneg hκ1 (mul_nonneg hκ1 ha0)
    have h2 : (κ - 1) * κ * ∫ w, g w ∂μ₂ ≤ (κ - 1) * κ * (M * (μ₂ univ).toReal) :=
      mul_le_mul_of_nonneg_left haM (mul_nonneg hκ1 hκ0)
    have h3 : (κ - 1) * ∫ w, g w ∂μ₁ ≤ (κ - 1) * (κ * ∫ w, g w ∂μ₂) :=
      mul_le_mul_of_nonneg_left hba hκ1
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- Split `φ = max φ 0 - max (-φ) 0`; both parts are continuous with values in `[0, M]`.
  have hp : Continuous fun w => max (φ w) 0 := hφ.max continuous_const
  have hn : Continuous fun w => max (-φ w) 0 := hφ.neg.max continuous_const
  have hp0 : ∀ w, 0 ≤ max (φ w) 0 := fun w => le_max_right _ _
  have hn0 : ∀ w, 0 ≤ max (-φ w) 0 := fun w => le_max_right _ _
  have hpM : ∀ w, max (φ w) 0 ≤ M := fun w => max_le ((le_abs_self _).trans (hM w)) hM0
  have hnM : ∀ w, max (-φ w) 0 ≤ M := fun w => max_le ((neg_le_abs _).trans (hM w)) hM0
  have hsplit : ∀ μ : Measure (Amb n ℓ), IsFiniteMeasure μ →
      ∫ w, φ w ∂μ = ∫ w, max (φ w) 0 ∂μ - ∫ w, max (-φ w) 0 ∂μ := by
    intro μ hμ
    have hpb : ∀ w, ‖max (φ w) 0‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 w)]
      exact hpM w
    have hnb : ∀ w, ‖max (-φ w) 0‖ ≤ M := fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn0 w)]
      exact hnM w
    rw [← integral_sub (Integrable.of_bound hp.aestronglyMeasurable M (ae_of_all _ hpb))
      (Integrable.of_bound hn.aestronglyMeasurable M (ae_of_all _ hnb))]
    simp only [max_zero_sub_max_neg_zero_eq_self]
  have hP : |∫ w, max (φ w) 0 ∂μ₁ - ∫ w, max (φ w) 0 ∂μ₂| ≤
      (κ - 1) * κ * (M * (μ₂ univ).toReal) := key _ hp hp0 hpM
  have hN : |∫ w, max (-φ w) 0 ∂μ₁ - ∫ w, max (-φ w) 0 ∂μ₂| ≤
      (κ - 1) * κ * (M * (μ₂ univ).toReal) := key _ hn hn0 hnM
  have e₁ := hsplit μ₁ hμ₁
  have e₂ := hsplit μ₂ hμ₂
  rw [abs_le] at hP hN ⊢
  constructor <;> linarith [hP.1, hP.2, hN.1, hN.2]

end Submission

/-- **Integrals over `C¹`-close bi-Lipschitz images of a compact parameter set converge**
(the blow-up step for approximate tangent planes of `C¹` graphs).  Let `K ⊆ ℝⁿ` be compact,
`pr ∘ L = id`, and suppose that, as `t → 0+`, eventually `pr ∘ F t = id` on `K`,
`‖F t v - F t v' - L (v - v')‖ ≤ ε ‖v - v'‖` on `K` (every `ε > 0`) and `F t → L` uniformly on `K`.
Then `∫_{F t(K)} φ dHⁿ → ∫_{L(K)} φ dHⁿ` for continuous compactly supported `φ`.  With
`Φ = F t ∘ pr`, `Φ` is a `δ`-near-isometry of `A = L(K)` onto `F t(K)`, so `Hⁿ ⌞ F t(K)` and
`Φ_#(Hⁿ ⌞ A)` agree up to the factor `κ = (1 - δ)⁻ⁿ`; the integrals of `φ` against them differ
by at most `2 (κ - 1) κ M Hⁿ(A)`, and `∫_A (φ ∘ Φ - φ) dHⁿ` is small by uniform continuity. -/
theorem Submission.dohr_tp_gat_bilip_setIntegral_tendsto : ∀ (n ℓ : ℕ) (K : Set (Rn n)) (pr : Amb n ℓ →L[ℝ] Rn n) (L : Rn n →L[ℝ] Amb n ℓ) (F : ℝ → Rn n → Amb n ℓ) (φ : Amb n ℓ → ℝ), IsCompact K → Continuous φ → HasCompactSupport φ → (∀ v, pr (L v) = v) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, pr (F t v) = v) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ∀ v' ∈ K, ‖F t v - F t v' - L (v - v')‖ ≤ ε * ‖v - v'‖) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ‖F t v - L v‖ ≤ ε) → Tendsto (fun t : ℝ => ∫ w in F t '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ w in L '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ)))) := by
  intro n ℓ K pr L F φ hK hφc hφs hprL hH1 hH2 hH3
  -- Step 1: `‖v‖ ≤ C ‖L v‖` with `C = ‖pr‖ + 1`, since `pr (L v) = v`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖pr‖ + 1 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  have hLlow : ∀ v, ‖v‖ ≤ C * ‖L v‖ := by
    intro v
    calc ‖v‖ = ‖pr (L v)‖ := by rw [hprL]
      _ ≤ ‖pr‖ * ‖L v‖ := pr.le_opNorm _
      _ ≤ C * ‖L v‖ := by rw [hC]; gcongr; linarith
  -- Step 2: the plane piece `A = L(K)` is compact, hence measurable, and
  -- `Hⁿ(A) ≤ ‖L‖ⁿ Lⁿ(K) < ∞` by the Lipschitz image bound.
  have hA_meas : MeasurableSet (L '' K) := (hK.image L.continuous).isClosed.measurableSet
  have hA_fin : (μHE[n] : Measure (Amb n ℓ)) (L '' K) < ⊤ := by
    calc (μHE[n] : Measure (Amb n ℓ)) (L '' K)
        ≤ (‖L‖₊ : ℝ≥0∞) ^ n * (μHE[n] : Measure (Rn n)) K :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            L.lipschitzWith.lipschitzOnWith
      _ < ⊤ := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hK.measure_lt_top
  have : IsFiniteMeasure ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    isFiniteMeasure_restrict.mpr hA_fin.ne
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ((μHE[n] : Measure (Amb n ℓ)) (L '' K)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; exact ENNReal.toReal_nonneg
  -- Step 3: `|φ| ≤ M` and `φ` is uniformly continuous.
  obtain ⟨M, hM⟩ := hφc.bounded_above_of_compact_support hφs
  have hMabs : ∀ w, |φ w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
  have hUC : UniformContinuous φ := hφs.uniformContinuous_of_continuous hφc
  rw [Metric.tendsto_nhds]
  intro θ hθ
  -- Step 4: `τ` from uniform continuity, and `δ ∈ (0, 1)` with
  -- `2 (κ - 1) κ M V < θ / 2` for `κ = (1 - δ)⁻ⁿ`.
  obtain ⟨τ, hτ, hτφ⟩ := Metric.uniformContinuous_iff.mp hUC (θ / (2 * (V + 1))) (by positivity)
  have hg : ContinuousAt (fun d : ℝ => ((1 - d)⁻¹) ^ n) 0 :=
    ((continuousAt_const.sub continuousAt_id).inv₀ (by norm_num)).pow n
  have hcont : ContinuousAt
      (fun d : ℝ => 2 * ((((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n * (M * V))) 0 :=
    continuousAt_const.mul (((hg.sub continuousAt_const).mul hg).mul continuousAt_const)
  have hlim : Tendsto (fun d : ℝ => 2 * ((((1 - d)⁻¹) ^ n - 1) * ((1 - d)⁻¹) ^ n * (M * V)))
      (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto
  obtain ⟨δ, hδθ, hδ0, hδ1⟩ : ∃ δ : ℝ,
      2 * ((((1 - δ)⁻¹) ^ n - 1) * ((1 - δ)⁻¹) ^ n * (M * V)) < θ / 2 ∧ 0 < δ ∧ δ < 1 :=
    (((hlim.eventually (gt_mem_nhds (half_pos hθ))).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_set.mpr (Ioo_mem_nhdsGT one_pos))).exists
  have hκ1 : 1 ≤ ((1 - δ)⁻¹) ^ n :=
    one_le_pow₀ ((one_le_inv₀ (by linarith)).mpr (by linarith))
  have hδC : 0 < δ / C := div_pos hδ0 hC0
  -- Step 5: the scale `t`, with (H1), (H2) for `ε = δ / C` and (H3) for `ε = τ / 2`.
  filter_upwards [hH1, hH2 (δ / C) hδC, hH3 (τ / 2) (half_pos hτ)] with t h1 h2 h3
  -- Step 6: the comparison map `Φ = F t ∘ pr`, with `Φ (L z) = F t z` and `Φ(A) = F t '' K`.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Amb n ℓ → Amb n ℓ, Φ = fun y => F t (pr y) := ⟨_, rfl⟩
  have hΦL : ∀ z, Φ (L z) = F t z := fun z => by simp only [hΦ, hprL]
  have hΦA : Φ '' (L '' K) = F t '' K := by
    rw [Set.image_image]
    simp only [hΦL]
  -- Step 7: by (H2), `F t` is Lipschitz on `K`, so `Φ` is continuous on `A`.
  have hFlip : LipschitzOnWith (Real.toNNReal (δ / C + ‖L‖)) (F t) K := by
    refine LipschitzOnWith.of_dist_le' fun v hv v' hv' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖F t v - F t v'‖ = ‖(F t v - F t v' - L (v - v')) + L (v - v')‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖F t v - F t v' - L (v - v')‖ + ‖L (v - v')‖ := norm_add_le _ _
      _ ≤ δ / C * ‖v - v'‖ + ‖L‖ * ‖v - v'‖ := add_le_add (h2 v hv v' hv') (L.le_opNorm _)
      _ = (δ / C + ‖L‖) * ‖v - v'‖ := by ring
  have hΦcont : ContinuousOn Φ (L '' K) := by
    rw [hΦ]
    refine hFlip.continuousOn.comp pr.continuous.continuousOn ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [hprL]
    exact hz
  have hΦae : AEMeasurable Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    hΦcont.aemeasurable hA_meas
  -- Step 8: `Φ` is a `δ`-near-isometry on `A`, by (H2) and step 1.
  have hnear : ∀ p ∈ L '' K, ∀ q ∈ L '' K, ‖Φ p - Φ q - (p - q)‖ ≤ δ * ‖p - q‖ := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [hΦL, hΦL, ← map_sub L z w]
    calc ‖F t z - F t w - L (z - w)‖ ≤ δ / C * ‖z - w‖ := h2 z hz w hw
      _ ≤ δ / C * (C * ‖L (z - w)‖) := by gcongr; exact hLlow _
      _ = δ * ‖L (z - w)‖ := by field_simp
  -- Step 9: `Hⁿ ⌞ Φ(A) ≤ κ Φ_#(Hⁿ ⌞ A)` and `Φ_#(Hⁿ ⌞ A) ≤ κ Hⁿ ⌞ Φ(A)`; the push-forward
  -- is finite with total mass `V`.
  obtain ⟨hle1, hle2⟩ :=
    Submission.dohr_tp_gat_bilip_measure_comparison n ℓ (L '' K) Φ δ hA_meas hδ0.le hδ1 hnear
  have hfin2 : IsFiniteMeasure
      (Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))) := inferInstance
  have hμ₂univ :
      (Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) univ).toReal = V := by
    rw [Measure.map_apply_of_aemeasurable hΦae MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ, hV]
  -- Steps 10-11: `|∫ φ d(Hⁿ ⌞ Φ(A)) - ∫ φ dΦ_#(Hⁿ ⌞ A)| ≤ 2 (κ - 1) κ M V < θ / 2`.
  have hsw := Submission.dohr_tp_gat_bilip_integral_sandwich n ℓ _ _ φ (((1 - δ)⁻¹) ^ n) M
    hfin2 hφc hMabs hκ1 hle1 hle2
  rw [hμ₂univ] at hsw
  -- Step 12: `∫ φ dΦ_#(Hⁿ ⌞ A) = ∫_A φ ∘ Φ dHⁿ`.
  have hmap : ∫ w, φ w ∂(Measure.map Φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))) =
      ∫ y, φ (Φ y) ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    integral_map hΦae hφc.aestronglyMeasurable
  -- Step 13: by (H3), `|φ ∘ Φ - φ| ≤ θ / (2 (V + 1))` on `A`, so the integrals over `A`
  -- differ by less than `θ / 2`.
  have hint1 : Integrable (fun y => φ (Φ y)) ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    Integrable.of_bound ((hφc.comp_continuousOn hΦcont).aestronglyMeasurable hA_meas) M
      (ae_of_all _ fun y => hM (Φ y))
  have hint2 : Integrable φ ((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) :=
    Integrable.of_bound hφc.aestronglyMeasurable M (ae_of_all _ hM)
  have hclose : ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)),
      ‖φ (Φ y) - φ y‖ ≤ θ / (2 * (V + 1)) := by
    rw [ae_restrict_iff' hA_meas]
    refine Filter.Eventually.of_forall ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← dist_eq_norm]
    refine (hτφ ?_).le
    rw [dist_eq_norm, hΦL]
    linarith [h3 z hz]
  have hdiff : |∫ y, φ (Φ y) ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K)) -
      ∫ y, φ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict (L '' K))| ≤ θ / (2 * (V + 1)) * V := by
    have h := norm_integral_le_of_norm_le_const hclose
    rwa [integral_sub hint1 hint2, measureReal_restrict_apply_univ, measureReal_def, ← hV,
      Real.norm_eq_abs] at h
  have hθV : θ / (2 * (V + 1)) * V < θ / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- Step 14: `F t '' K = Φ(A)` and the triangle inequality.
  have hA1 := abs_sub_lt_iff.mp (lt_of_le_of_lt hsw hδθ)
  have hA2 := abs_sub_lt_iff.mp (lt_of_le_of_lt hdiff hθV)
  rw [hmap] at hA1
  rw [Real.dist_eq, ← hΦA, abs_sub_lt_iff]
  constructor <;> linarith [hA1.1, hA1.2, hA2.1, hA2.2]

namespace Submission

/-- **Localizing set integrals to `B`.**  If `φ` vanishes off the measurable set `B`, then
`φ = B.indicator φ`, so `∫_X φ dμ = ∫_{X ∩ B} φ dμ` for every set `X` (`setIntegral_indicator`;
neither integrability of `φ` nor measurability of `X` is needed).  From `S ∩ B ⊆ T ⊆ S` we get
`S ∩ B = T ∩ B`, hence `∫_S φ dμ = ∫_T φ dμ`. -/
theorem dohr_tp_gat_setIntegral_eq_of_inter : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (φ : Amb n ℓ → ℝ) (S T B : Set (Amb n ℓ)), MeasurableSet B → (∀ w, w ∉ B → φ w = 0) → S ∩ B ⊆ T → T ⊆ S → ∫ w in S, φ w ∂μ = ∫ w in T, φ w ∂μ := by
  intro n ℓ μ φ S T B hB hφ hST hTS
  -- `φ = B.indicator φ`, since `φ` vanishes off `B`.
  have hind : B.indicator φ = φ := by
    funext w
    by_cases hw : w ∈ B
    · exact indicator_of_mem hw φ
    · rw [indicator_of_notMem hw, hφ w hw]
  -- `S ∩ B = T ∩ B`: `S ∩ B ⊆ T` gives `⊆`, and `T ⊆ S` gives `⊇`.
  have hinter : S ∩ B = T ∩ B :=
    Subset.antisymm (subset_inter hST inter_subset_right) (inter_subset_inter_left B hTS)
  calc ∫ w in S, φ w ∂μ = ∫ w in S, B.indicator φ w ∂μ := by rw [hind]
    _ = ∫ w in S ∩ B, φ w ∂μ := setIntegral_indicator hB
    _ = ∫ w in T ∩ B, φ w ∂μ := by rw [hinter]
    _ = ∫ w in T, B.indicator φ w ∂μ := (setIntegral_indicator hB).symm
    _ = ∫ w in T, φ w ∂μ := by rw [hind]

/-- Simon Ch. 3, Definition 1.4 for `C¹` graphs: if `u` is `C¹` on the open ball `B̆_R(0) ⊆ ℝⁿ`,
`G(z) = (z, u(z))` and `x ∈ B̆_R(0)`, then `τ = range DG(x)` is the approximate tangent space of
`graph u = G(B̆_R(0))` at `G(x)`.  The projection `π` onto the first `n` coordinates
(`rsod_graphPoint_eq_finAddEquivProd_symm`) is `1`-Lipschitz (`rsod_norm_graphPoint_sq`) and
inverts `G`, hence also `DG(x)` (chain rule for `π ∘ G = id`), so `DG(x)` is
injective and `dim τ = n`.  For `f ∈ C_c(ℝ^{n+ℓ})` vanishing off `B_ρ(0)`, the blow-ups
`F_t(v) = t⁻¹ (G(x + tv) − G(x))` satisfy `π ∘ F_t = id` and, by `dohr_tp_gat_blowup_two_point`,
the two-point and uniform estimates of `dohr_tp_gat_bilip_setIntegral_tendsto` on `K = B_ρ(0)`, so
`∫_{F_t(K)} f dHⁿ → ∫_{DG(x)(K)} f dHⁿ`.  As `|v| ≤ |F_t(v)|` and `|v| ≤ |DG(x) v|`,
`dohr_tp_gat_setIntegral_eq_of_inter` (with `B = B_ρ(0)`) identifies these integrals with
`∫_{η_{G(x),t}(graph u)} f dHⁿ` for small `t > 0` and with `∫_τ f dHⁿ`. -/
theorem dohr_tp_graph_approx_tangent : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R : ℝ) (u : Rn n → Rn ℓ),
    ContDiffOn ℝ 1 u (ball 0 R) → ∀ x ∈ ball (0 : Rn n) R,
    Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n (graphOver u (ball 0 R))
      (graphPoint x (u x))
      (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap) := by
  intro n ℓ _ R u hu x hx
  -- `graphPoint a b` corresponds to `(a, b)` under the splitting `ℝ^{n+ℓ} ≃ ℝⁿ × ℝ^ℓ`,
  -- and `|(a, b)|² = |a|² + |b|²`
  let e : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  have hgp : ∀ (a : Rn n) (b : Rn ℓ), graphPoint a b = e.symm (a, b) :=
    fun a b => Submission.rsod_graphPoint_eq_finAddEquivProd_symm a b
  have hgp_norm : ∀ (a : Rn n) (b : Rn ℓ), ‖graphPoint a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
    fun a b => Submission.rsod_norm_graphPoint_sq a b
  -- the projection `π` onto the first `n` coordinates
  let pr : Amb n ℓ →L[ℝ] Rn n :=
    (ContinuousLinearMap.fst ℝ (Rn n) (Rn ℓ)).comp (e : Amb n ℓ →L[ℝ] Rn n × Rn ℓ)
  have hpr_gp : ∀ (a : Rn n) (b : Rn ℓ), pr (graphPoint a b) = a := by
    intro a b
    simp [pr, hgp]
  have hpr_norm : ∀ w : Amb n ℓ, ‖pr w‖ ≤ ‖w‖ := by
    intro w
    have hw : graphPoint (e w).1 (e w).2 = w := by rw [hgp]; exact e.symm_apply_apply w
    have h2 := hgp_norm (e w).1 (e w).2
    rw [hw] at h2
    have h3 : ‖pr w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      have hpw : pr w = (e w).1 := rfl
      rw [hpw, h2]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
  set G : Rn n → Amb n ℓ := fun z => graphPoint z (u z)
  have hprG : ∀ z, pr (G z) = z := fun z => hpr_gp z (u z)
  have hGc : ContDiffOn ℝ 1 G (ball 0 R) := by
    have hGe : G = e.symm ∘ fun z => (z, u z) := funext fun z => hgp z (u z)
    rw [hGe]
    exact e.symm.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)
  have hGd : DifferentiableAt ℝ G x :=
    (hGc.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hx)
  set L : Rn n →L[ℝ] Amb n ℓ := fderiv ℝ G x
  have hprL : ∀ v, pr (L v) = v := by
    have h1 : HasFDerivAt (pr ∘ G) (pr.comp L) x := pr.hasFDerivAt.comp x hGd.hasFDerivAt
    have h2 : (pr ∘ G) = id := funext hprG
    rw [h2] at h1
    have h3 := h1.unique (hasFDerivAt_id x)
    intro v
    exact congrArg (fun T : Rn n →L[ℝ] Rn n => T v) h3
  have hLinj : Function.Injective L := fun v v' h => by rw [← hprL v, ← hprL v', h]
  refine ⟨?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (f := L.toLinearMap) hLinj, finrank_euclideanSpace_fin]
  intro f
  -- a radius `ρ ≥ 0` outside of which `f` vanishes
  obtain ⟨ρ0, hρ0⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set ρ : ℝ := max ρ0 0
  have hρ_nn : 0 ≤ ρ := le_max_right _ _
  have hfz : ∀ w, w ∉ closedBall (0 : Amb n ℓ) ρ → f w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hw'
    exact hw (closedBall_subset_closedBall (le_max_left _ _) (hρ0 hw'))
  set K : Set (Rn n) := closedBall 0 ρ
  -- the blow-ups `F_t(v) = t⁻¹ (G(x + t v) - G(x))` of the graph map at `x`
  set F : ℝ → Rn n → Amb n ℓ := fun t v => t⁻¹ • (G (x + t • v) - G x) with hF
  have hprF : ∀ t : ℝ, t ≠ 0 → ∀ v, pr (F t v) = v := by
    intro t ht v
    simp only [hF, map_smul, map_sub, hprG, add_sub_cancel_left, inv_smul_smul₀ ht]
  have hF_blowUp : ∀ t : ℝ, t ≠ 0 → ∀ z,
      F t (t⁻¹ • (z - x)) = Poincare.SimonGMT.Chapter03.blowUpMap (G x) t (G z) := by
    intro t ht z
    simp only [hF, Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ ht, add_sub_cancel]
  have h_pr : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, pr (F t v) = v := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) v _
    exact hprF t ht.ne' v
  have h_two : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ∀ v' ∈ K,
      ‖F t v - F t v' - L (v - v')‖ ≤ ε * ‖v - v'‖ := by
    intro ε hε
    filter_upwards [Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ ε isOpen_ball
      hGc hx hε] with t ht v hv v' hv'
    have hsub : F t v - F t v' = t⁻¹ • (G (x + t • v) - G (x + t • v')) := by
      simp only [hF, ← smul_sub, sub_sub_sub_cancel_right]
    rw [hsub]
    exact ht.2 v hv v' hv'
  have h_one : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ‖F t v - L v‖ ≤ ε := by
    intro ε hε
    have hρ1 : (0 : ℝ) < ρ + 1 := by linarith
    have hε' : 0 < ε / (ρ + 1) := div_pos hε hρ1
    filter_upwards [Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ (ε / (ρ + 1))
      isOpen_ball hGc hx hε'] with t ht v hv
    have h1 := ht.2 v hv 0 (mem_closedBall_self hρ_nn)
    simp only [smul_zero, add_zero, sub_zero] at h1
    have hv' : ‖v‖ ≤ ρ := mem_closedBall_zero_iff.mp hv
    calc ‖F t v - L v‖ ≤ ε / (ρ + 1) * ‖v‖ := h1
      _ ≤ ε / (ρ + 1) * (ρ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε'.le
      _ = ε := div_mul_cancel₀ ε hρ1.ne'
  -- localize the blown-up graph to `F_t(K)` and the plane `τ` to `L(K)`
  have hloc1 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∫ w in F t '' K, f w ∂(μHE[n] : Measure (Amb n ℓ)) =
        ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap (G x) t '' graphOver u (ball 0 R),
          f w ∂(μHE[n] : Measure (Amb n ℓ)) := by
    filter_upwards [self_mem_nhdsWithin,
      Submission.dohr_tp_gat_blowup_two_point n ℓ (ball 0 R) G x ρ 1 isOpen_ball hGc hx one_pos]
      with t (ht : 0 < t) hball
    symm
    refine Submission.dohr_tp_gat_setIntegral_eq_of_inter n ℓ _ f _ _ (closedBall 0 ρ)
      measurableSet_closedBall hfz ?_ ?_
    · rintro w ⟨⟨y, ⟨z, hz, rfl⟩, rfl⟩, hwB⟩
      refine ⟨t⁻¹ • (z - x), ?_, hF_blowUp t ht.ne' z⟩
      rw [mem_closedBall_zero_iff] at hwB ⊢
      calc ‖t⁻¹ • (z - x)‖ = ‖pr (F t (t⁻¹ • (z - x)))‖ := by rw [hprF t ht.ne']
        _ ≤ ‖F t (t⁻¹ • (z - x))‖ := hpr_norm _
        _ = ‖Poincare.SimonGMT.Chapter03.blowUpMap (G x) t (G z)‖ := by
          rw [hF_blowUp t ht.ne' z]
        _ ≤ ρ := hwB
    · rintro w ⟨v, hv, rfl⟩
      exact ⟨G (x + t • v), ⟨x + t • v, hball.1 v hv, rfl⟩, rfl⟩
  have hloc2 : ∫ w in L '' K, f w ∂(μHE[n] : Measure (Amb n ℓ)) =
      ∫ w in (LinearMap.range L.toLinearMap : Set (Amb n ℓ)), f w
        ∂(μHE[n] : Measure (Amb n ℓ)) := by
    symm
    refine Submission.dohr_tp_gat_setIntegral_eq_of_inter n ℓ _ f _ _ (closedBall 0 ρ)
      measurableSet_closedBall hfz ?_ ?_
    · rintro w ⟨hw, hwB⟩
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall_zero_iff] at hwB ⊢
      calc ‖v‖ = ‖pr (L v)‖ := by rw [hprL]
        _ ≤ ‖L v‖ := hpr_norm _
        _ ≤ ρ := hwB
    · rintro w ⟨v, -, rfl⟩
      exact LinearMap.mem_range_self _ v
  have hlim := Submission.dohr_tp_gat_bilip_setIntegral_tendsto n ℓ K pr L F f
    (isCompact_closedBall 0 ρ) (map_continuous f) f.hasCompactSupport hprL h_pr h_two h_one
  have h := hlim.congr' hloc1
  rw [hloc2] at h
  exact h
/-- **Approximate tangent spaces under rigid motions** (Simon Ch. 3, 1.4; used for the graph
tangent planes in the proof of 7.1).  If `P` is the approximate tangent space of `S` at `z`, then
for every linear isometry `Q` of `ℝ^{n+ℓ}` and every `ξ`, `Q(P)` is the approximate tangent space
of `ξ + Q(S)` at `ξ + Q z`.
Proof: `η_{ξ+Qz,r}(ξ + Q w) = Q(η_{z,r} w)` and `Q` preserves `Hⁿ`, so for `φ ∈ C_c` the blown-up
integrals of `φ` over `ξ + Q(S)` equal those of `φ ∘ Q ∈ C_c` over `S`, while
`∫_{Q(P)} φ dHⁿ = ∫_P φ ∘ Q dHⁿ`; and `dim Q(P) = dim P`. -/
theorem dohr_tp_approx_tangent_affine_isometry : ∀ (n ℓ : ℕ) (S : Set (Amb n ℓ)) (z ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S z P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n ((fun w => ξ + Q w) '' S) (ξ + Q z) (Submodule.map Q.toLinearEquiv.toLinearMap P) := by
  intro n ℓ S z ξ Q P hP
  obtain ⟨hdim, hconv⟩ := hP
  -- `Q` is an isometric equivalence: a measurable embedding preserving `μHE[n]`, so
  -- `∫_{Q '' X} φ dHⁿ = ∫_X φ ∘ Q dHⁿ` for every set `X`.
  have hmp : MeasurePreserving Q (μHE[n] : Measure (Amb n ℓ)) μHE[n] :=
    Q.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n
  have hme : MeasurableEmbedding Q := Q.toHomeomorph.measurableEmbedding
  refine ⟨(LinearEquiv.finrank_map_eq Q.toLinearEquiv P).trans hdim, fun φ => ?_⟩
  -- The test function `ψ = φ ∘ Q` is again in `C_c`.
  set ψ : CompactlySupportedContinuousMap (Amb n ℓ) ℝ := φ.comp Q.toHomeomorph.toCocompactMap
  have hψ : ∀ X : Set (Amb n ℓ), ∫ y in Q '' X, φ y ∂μHE[n] = ∫ y in X, ψ y ∂μHE[n] :=
    fun X => hmp.setIntegral_image_emb hme φ X
  -- Blow-ups commute with `w ↦ ξ + Q w`: `η_{ξ+Qz,r}(ξ + Q w) = Q (η_{z,r} w)`.
  have himg : ∀ r : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap (ξ + Q z) r '' ((fun w => ξ + Q w) '' S) =
        Q '' (Poincare.SimonGMT.Chapter03.blowUpMap z r '' S) := by
    intro r
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr fun w _ => ?_
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_add_left_eq_sub, map_smul, map_sub]
  have hlim : ∫ y in (Submodule.map Q.toLinearEquiv.toLinearMap P : Set (Amb n ℓ)), φ y ∂μHE[n] =
      ∫ y in (P : Set (Amb n ℓ)), ψ y ∂μHE[n] := by
    rw [Submodule.map_coe]
    exact hψ P
  rw [hlim]
  refine (hconv ψ).congr fun r => ?_
  rw [himg r, hψ]
/-- `n`-dimensional growth of a compactly contained `C¹` graph piece: if `0 < ρ < R` and `u` is
`C¹` on `B̆_R(0)`, then `Hⁿ(graph u|B̆_ρ(0) ∩ B_r(z)) ≤ C rⁿ` for all `z` and all `r > 0`.  On the
compact convex ball `B_ρ(0) ⊆ B̆_R(0)` the map `u` is `K`-Lipschitz
(`ContDiffOn.exists_lipschitzOnWith`), so `G x = (x, u x)` satisfies
`|a - b| ≤ |G a - G b| ≤ (1 + K) |a - b|` there (`|G a - G b|² = |a - b|² + |u a - u b|²`, split the
coordinate sum with `Fin.sum_univ_add`).  Graph points in `B_r(z)` come from one parameter ball
`B_{2r}(a)`, and the Lipschitz image bound `LipschitzOnWith.hausdorffMeasure_image_le` (rescaled to
`μHE[n] = c • μH[n]`, which is Lebesgue measure on `ℝⁿ`) gives `C = (1 + K)ⁿ 2ⁿ Lⁿ(B_1(0))`. -/
theorem dohr_tp_graph_ball_growth : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (R ρ : ℝ) (u : Rn n → Rn ℓ), 0 < ρ →
    ρ < R → ContDiffOn ℝ 1 u (ball 0 R) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
      (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 ρ) ∩ closedBall z r) ≤
        ENNReal.ofReal (C * r ^ n) := by
  intro n ℓ _ R ρ u _ hρR hu
  obtain ⟨K, hK⟩ := (hu.mono (closedBall_subset_ball hρR)).exists_lipschitzOnWith one_ne_zero
    (convex_closedBall 0 ρ) (isCompact_closedBall 0 ρ)
  have hdist : ∀ a b : Rn n, dist (graphPoint a (u a)) (graphPoint b (u b)) ^ 2 =
      dist a b ^ 2 + dist (u a) (u b) ^ 2 := by
    intro a b
    simp only [EuclideanSpace.dist_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_add]
    simp [graphPoint]
  have hlow : ∀ a b : Rn n, dist a b ≤ dist (graphPoint a (u a)) (graphPoint b (u b)) := by
    intro a b
    nlinarith [hdist a b, dist_nonneg (x := a) (y := b), sq_nonneg (dist (u a) (u b)),
      dist_nonneg (x := graphPoint a (u a)) (y := graphPoint b (u b))]
  have hLip : LipschitzOnWith (1 + K) (fun x => graphPoint x (u x)) (closedBall 0 ρ) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hu' : dist (u a) (u b) ≤ K * dist a b := hK.dist_le_mul a ha b hb
    have h1 : dist (graphPoint a (u a)) (graphPoint b (u b)) ≤ dist a b + dist (u a) (u b) := by
      nlinarith [hdist a b, dist_nonneg (x := a) (y := b), dist_nonneg (x := u a) (y := u b),
        dist_nonneg (x := graphPoint a (u a)) (y := graphPoint b (u b))]
    push_cast
    linarith
  -- `μHE[n] = c • μH[n]` with the same `c` on every space, and `μHE[n] = volume` on `ℝⁿ`.
  have key : ∀ s : Set (Rn n), s ⊆ closedBall 0 ρ →
      (μHE[n] : Measure (Amb n ℓ)) ((fun x => graphPoint x (u x)) '' s) ≤
        ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume s := by
    intro s hs
    have h1 := (hLip.mono hs).hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [ENNReal.rpow_natCast] at h1
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def,
      Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul]
    calc _ ≤ _ := by gcongr
      _ = _ := mul_left_comm _ _ _
  set ω : ℝ≥0∞ := volume (closedBall (0 : Rn n) 1)
  have hωtop : ω ≠ ∞ := measure_closedBall_lt_top.ne
  refine ⟨((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal, by positivity, fun z r hr => ?_⟩
  rcases (graphOver u (ball 0 ρ) ∩ closedBall z r).eq_empty_or_nonempty with hE | ⟨p, hp⟩
  · rw [hE, measure_empty]
    exact zero_le
  obtain ⟨⟨a, -, rfl⟩, hpz⟩ := hp
  have hX : graphOver u (ball 0 ρ) ∩ closedBall z r ⊆
      (fun x => graphPoint x (u x)) '' (ball 0 ρ ∩ closedBall a (2 * r)) := by
    rintro y ⟨⟨b, hb, rfl⟩, hyz⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    rw [mem_closedBall] at hyz hpz ⊢
    calc dist b a ≤ dist (graphPoint b (u b)) (graphPoint a (u a)) := hlow b a
      _ ≤ dist (graphPoint b (u b)) z + dist (graphPoint a (u a)) z := dist_triangle_right _ _ _
      _ ≤ 2 * r := by linarith
  calc (μHE[n] : Measure (Amb n ℓ)) (graphOver u (ball 0 ρ) ∩ closedBall z r)
      ≤ (μHE[n] : Measure (Amb n ℓ))
          ((fun x => graphPoint x (u x)) '' (ball 0 ρ ∩ closedBall a (2 * r))) := measure_mono hX
    _ ≤ ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume (ball 0 ρ ∩ closedBall a (2 * r)) :=
        key _ (inter_subset_left.trans ball_subset_closedBall)
    _ ≤ ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * volume (closedBall a (2 * r)) := by
        gcongr
        exact inter_subset_right
    _ = ((1 + K : ℝ≥0) : ℝ≥0∞) ^ n * (ENNReal.ofReal ((2 * r) ^ n) * ω) := by
        rw [Measure.addHaar_closedBall' _ _ (by positivity), finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal * r ^ n) := by
        rw [show ((1 + K : ℝ≥0) : ℝ) ^ n * 2 ^ n * ω.toReal * r ^ n =
            ((1 + K : ℝ≥0) : ℝ) ^ n * ((2 * r) ^ n * ω.toReal) by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_toReal hωtop]
/-- Lebesgue points for a measure with `n`-dimensional growth: if `ν(B_r(z)) ≤ C rⁿ` for all `z`
and `r > 0` and `f` is `ν`-integrable, then for `ν`-a.e. `y`,
`r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν → 0` as `r ↓ 0`.  The growth bound makes `ν` locally finite, so the
Besicovitch differentiation theorem gives `ν(B_r(y))⁻¹ ∫_{B_r(y)} |f − f(y)| dν → 0`, and
`r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν ≤ C · ν(B_r(y))⁻¹ ∫_{B_r(y)} |f − f(y)| dν`. -/
theorem dohr_tp_ae_lebesgue_point_of_growth : ∀ (n ℓ : ℕ) (ν : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ) (C : ℝ), Integrable f ν → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → ν (closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂ν, Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) (𝓝[>] 0) (𝓝 0) := by
  intro n ℓ ν f C hf hgrowth
  -- The growth bound makes `ν` locally finite (hence σ-finite).
  have : IsLocallyFiniteMeasure ν :=
    ⟨fun y => ⟨closedBall y 1, closedBall_mem_nhds y one_pos,
      (hgrowth y 1 one_pos).trans_lt ENNReal.ofReal_lt_top⟩⟩
  -- Besicovitch differentiation: the averages of `|f − f(y)|` over `B_r(y)` tend to `0`.
  filter_upwards [(Besicovitch.vitaliFamily ν).ae_tendsto_lintegral_enorm_sub_div
    hf.locallyIntegrable] with y hy
  have hD := hy.comp (Besicovitch.tendsto_filterAt ν y)
  have hCD : Tendsto (fun r : ℝ => ENNReal.ofReal C *
      ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r))) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hD (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCD
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  -- `r⁻ⁿ ∫_{B_r(y)} |f − f(y)| dν ≤ C · (average)`, separating the case `ν(B_r(y)) = 0`.
  by_cases hm : ν (closedBall y r) = 0
  · rw [setLIntegral_measure_zero _ _ hm]
    simp
  have hmle := hgrowth y r hr
  have hmtop : ν (closedBall y r) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmle
  have hrn : 0 < r ^ n := pow_pos hr n
  calc ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν
      = ENNReal.ofReal ((r ^ n)⁻¹) * ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) /
          ν (closedBall y r) * ν (closedBall y r)) := by
        rw [ENNReal.div_mul_cancel hm hmtop]
    _ ≤ ENNReal.ofReal ((r ^ n)⁻¹) * ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) /
          ν (closedBall y r) * ENNReal.ofReal (C * r ^ n)) := by
        gcongr
    _ = ENNReal.ofReal ((r ^ n)⁻¹ * (C * r ^ n)) *
          ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r)) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrn.le)]
        ring
    _ = ENNReal.ofReal C *
          ((∫⁻ w in closedBall y r, ‖f w - f y‖ₑ ∂ν) / ν (closedBall y r)) := by
        rw [mul_comm C, inv_mul_cancel_left₀ hrn.ne']
/-- **Blow-up change of variables** (Simon Ch. 3, Remark 1.8(2)).  For `η = η_{x,r}`,
`η(z) = r⁻¹(z − x)`, with `r > 0`, any set `M` and any `f, θ`:
`∫_{η(M)} f(y) θ(x + r y) dHⁿ(y) = r⁻ⁿ ∫_M f(η z) θ(z) dHⁿ(z)`.  As `η` is a homeomorphism and
`Hⁿ(η(S)) = r⁻ⁿ Hⁿ(S)` for every `S`, `Hⁿ ⌞ η(M) = r⁻ⁿ η_#(Hⁿ ⌞ M)`; no integrability is needed. -/
theorem rsod_blowUp_setIntegral_eq : ∀ (n ℓ : ℕ) (M : Set (Amb n ℓ)) (f θ : Amb n ℓ → ℝ) (x : Amb n ℓ) (r : ℝ), 0 < r → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[n] : Measure (Amb n ℓ)) = (r ^ n)⁻¹ * ∫ z in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r z) * θ z ∂(μHE[n] : Measure (Amb n ℓ)) := by
  intro n ℓ M f θ x r hr
  set μ : Measure (Amb n ℓ) := (μHE[n] : Measure (Amb n ℓ))
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x r with hη
  -- `η` is the homeomorphism `z ↦ r⁻¹ • (z - x)`, hence a measurable embedding.
  let e : Amb n ℓ ≃ₜ Amb n ℓ :=
    (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : ⇑e = η := rfl
  have hemb : MeasurableEmbedding η := he ▸ e.toMeasurableEquiv.measurableEmbedding
  have hinj : Function.Injective η := he ▸ e.injective
  have hsurj : Function.Surjective η := he ▸ e.surjective
  -- `Hⁿ(η(S)) = (r⁻¹)ⁿ Hⁿ(S)` for every set `S`: a translation followed by a homothety.
  have hscale : ∀ S : Set (Amb n ℓ), μ (η '' S) = ENNReal.ofReal r⁻¹ ^ n * μ S := by
    intro S
    have hshift : Isometry (fun y : Amb n ℓ => y - x) :=
      Isometry.of_dist_eq fun a b => by simp only [dist_eq_norm, sub_sub_sub_cancel_right]
    have himage : η '' S = AffineMap.homothety (0 : Amb n ℓ) r⁻¹ '' ((fun y => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [hη, Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Amb n ℓ) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
      ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  -- `Hⁿ ⌞ η(M) = (r⁻¹)ⁿ η_#(Hⁿ ⌞ M)`, checked on measurable `A` via `A ∩ η(M) = η(η⁻¹(A) ∩ M)`.
  have hmeas : μ.restrict (η '' M) = (ENNReal.ofReal r⁻¹ ^ n) • (μ.restrict M).map η := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply hemb.measurable hA,
      Measure.restrict_apply (hemb.measurable hA), smul_eq_mul, ← hscale, image_inter hinj,
      image_preimage_eq A hsurj]
  -- Transfer the integral and simplify `x + r • η z = z`.
  rw [hmeas, integral_smul_measure, hemb.integral_map, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (inv_pos.mpr hr).le, inv_pow, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne',
    one_smul, add_sub_cancel]
/-- **Rescaling the radius in a scaled Lebesgue-point limit.**  If `t⁻ⁿ L(t) → 0` in `[0, ∞]` as
`t ↓ 0` and `ρ > 0`, then `L(rρ) < ∞` for all small `r > 0` and `r⁻ⁿ L(rρ) → 0` in `ℝ` as `r ↓ 0`:
`r ↦ rρ` maps `𝓝[>] 0` into itself, `toReal` is continuous at `0`, and for `r > 0`
`r⁻ⁿ L(rρ) = ρⁿ ((rρ)⁻ⁿ L(rρ)).toReal`. -/
theorem dohr_tp_wtlp_rescaled_limit : ∀ (n : ℕ) (L : ℝ → ℝ≥0∞) (ρ : ℝ), 0 < ρ → Tendsto (fun t : ℝ => ENNReal.ofReal ((t ^ n)⁻¹) * L t) (𝓝[>] 0) (𝓝 0) → (∀ᶠ r in 𝓝[>] (0 : ℝ), L (r * ρ) ≠ ⊤) ∧ Tendsto (fun r : ℝ => (r ^ n)⁻¹ * (L (r * ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
  intro n L ρ hρ hL
  -- `r ↦ r * ρ` maps `𝓝[>] 0` into `𝓝[>] 0`, so `((rρ)ⁿ)⁻¹ L(rρ) → 0` as `r ↓ 0`.
  have hmap : Tendsto (fun r : ℝ => r * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hr hρ
  have hF := hL.comp hmap
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  refine ⟨?_, ?_⟩
  · -- Eventually `((rρ)ⁿ)⁻¹ L(rρ) < 1`, while `L(rρ) = ∞` would make it `∞`.
    filter_upwards [hpos, hF.eventually (eventually_lt_nhds zero_lt_one)] with r hr hlt htop
    have hne : ENNReal.ofReal (((r * ρ) ^ n)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos (mul_pos hr hρ) n))).ne'
    simp [htop, ENNReal.mul_top hne] at hlt
  · -- `ρⁿ (((rρ)ⁿ)⁻¹ L(rρ)).toReal → 0` and equals `(rⁿ)⁻¹ (L(rρ)).toReal` for `r > 0`.
    have h1 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hF).const_mul (ρ ^ n)
    rw [ENNReal.toReal_zero, mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hpos] with r hr
    simp only [Function.comp_def, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg (mul_pos hr hρ).le n))]
    rw [mul_pow, mul_inv, mul_comm ((r ^ n)⁻¹), ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n hρ.ne'), one_mul]
/-- `Hⁿ`-a.e. on `M ∩ O`, approximate tangent planes of `S` are approximate tangent planes of `M`
with respect to `θ`, provided `Hⁿ((M ∩ O) \ S) = 0`, `θ` is integrable on `M ∩ O` and
`Hⁿ ⌞ (S ∩ O)` has `n`-dimensional growth.  `Hⁿ ⌞ (S ∩ O)`-a.e. point is a Lebesgue point of
`1_M θ` (`dohr_tp_ae_lebesgue_point_of_growth`); at such a point `y ∈ M ∩ O ∩ S` the small balls
`B_r(y)` lie in `O`, which turns this into the Lebesgue condition on `S` required by
`dohr_tp_weighted_tangent_of_lebesgue_point`. -/
theorem dohr_tp_ae_weighted_tangent_of_growth : ∀ (n ℓ : ℕ) (M S O : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (C : ℝ), IsOpen O → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → IntegrableOn θ (M ∩ O) (μHE[n] : Measure (Amb n ℓ)) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ O) \ S) = 0 → (∀ (z : Amb n ℓ) (r : ℝ), 0 < r → (μHE[n] : Measure (Amb n ℓ)) (S ∩ O ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n)) → ∀ᵐ y ∂((μHE[n] : Measure (Amb n ℓ)).restrict M), y ∈ O → ∀ P : Submodule ℝ (Amb n ℓ), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
  intro n ℓ M S O θ C hO hM hθ hθint hMS hgrowth
  -- Fixed-scale comparison: if `ψ` is measurable, `|ψ| ≤ K`, `ψ = 0` off the measurable set `B`,
  -- `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`, then
  -- `|∫_M ψ θ - c ∫_S ψ| ≤ K ∫_{S ∩ B} |1_M θ - c|` when the right side is finite: both integrals
  -- localize to `S ∩ B`, where the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
  have hcmp : ∀ (B : Set (Amb n ℓ)) (ψ : Amb n ℓ → ℝ) (c K : ℝ), MeasurableSet B →
      (μHE[n] : Measure (Amb n ℓ)) ((M ∩ B) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ B) ≠ ⊤ →
      Measurable ψ → (∀ w, |ψ w| ≤ K) → (∀ w, w ∉ B → ψ w = 0) →
      ∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) ≠ ⊤ →
      |∫ w in M, ψ w * θ w ∂(μHE[n] : Measure (Amb n ℓ)) -
          c * ∫ w in S, ψ w ∂(μHE[n] : Measure (Amb n ℓ))| ≤
        K * (∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))).toReal := by
    revert hM hθ
    generalize (μHE[n] : Measure (Amb n ℓ)) = μ
    intro hM hθ B ψ c K hB hMBS hSB hψ hψK hψB hΛ
    have hψK' : ∀ w, ‖ψ w‖ ≤ K := fun w => by rw [Real.norm_eq_abs]; exact hψK w
    -- The `S`-integral localizes to `S ∩ B`, as `ψ = 0` off `B`.
    have h1 : ∫ w in S, ψ w ∂μ = ∫ w in S ∩ B, ψ w ∂μ := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict S) hψB,
        Measure.restrict_restrict hB, inter_comm B S]
    -- The `M`-integral localizes to `M ∩ B =ᵐ M ∩ (S ∩ B)`, i.e. to the integral of `ψ · 1_M θ`
    -- over `S ∩ B`.
    have h2 : ∫ w in M, ψ w * θ w ∂μ = ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ := by
      have hae : (M ∩ B : Set (Amb n ℓ)) =ᵐ[μ] (M ∩ (S ∩ B) : Set (Amb n ℓ)) := by
        refine ae_eq_set.mpr ⟨measure_mono_null (fun w hw => ?_) hMBS, ?_⟩
        · exact ⟨hw.1, fun hS => hw.2 ⟨hw.1.1, hS, hw.1.2⟩⟩
        · rw [show (M ∩ (S ∩ B)) \ (M ∩ B) = ∅ from
            eq_empty_of_forall_notMem fun w hw => hw.2 ⟨hw.1.1, hw.1.2.2⟩, measure_empty]
      have hMν : NullMeasurableSet M (μ.restrict (S ∩ B)) := hM.mono Measure.restrict_le_self
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict M) (s := B)
          (f := fun w => ψ w * θ w) (fun w hw => by rw [hψB w hw, zero_mul]),
        Measure.restrict_restrict hB, inter_comm B M, setIntegral_congr_set hae,
        ← Measure.restrict_restrict₀ hMν, ← integral_indicator₀ hMν]
      congr 1
      funext w
      exact indicator_mul_right M ψ θ
    -- Integrability on `S ∩ B`, which has finite measure.
    have : IsFiniteMeasure (μ.restrict (S ∩ B)) := isFiniteMeasure_restrict.mpr hSB
    have hfB : AEStronglyMeasurable (M.indicator θ) (μ.restrict (S ∩ B)) :=
      ((aemeasurable_indicator_iff₀ hM).mpr hθ).restrict.aestronglyMeasurable
    have hfc : Integrable (fun w => M.indicator θ w - c) (μ.restrict (S ∩ B)) :=
      ⟨hfB.sub aestronglyMeasurable_const, hasFiniteIntegral_iff_enorm.mpr hΛ.lt_top⟩
    have hfi : Integrable (M.indicator θ) (μ.restrict (S ∩ B)) :=
      (hfc.add (integrable_const c)).congr (ae_of_all _ fun w => by simp)
    have hψb : ∀ᵐ w ∂(μ.restrict (S ∩ B)), ‖ψ w‖ ≤ K := ae_of_all _ hψK'
    have hψi : Integrable ψ (μ.restrict (S ∩ B)) :=
      (integrable_const K).mono' hψ.aestronglyMeasurable hψb
    have hψf : Integrable (fun w => ψ w * M.indicator θ w) (μ.restrict (S ∩ B)) :=
      hfi.bdd_mul hψ.aestronglyMeasurable hψb
    -- Linearity: the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
    have h6 : ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ - c * ∫ w in S ∩ B, ψ w ∂μ =
        ∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ := by
      rw [← integral_const_mul, ← integral_sub hψf (hψi.const_mul c)]
      congr 1
      funext w
      ring
    -- `|ψ (1_M θ - c)| ≤ K |1_M θ - c|`, and `∫ |1_M θ - c| = Λ.toReal`.
    have hle : ‖∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ‖ ≤
        ∫ w in S ∩ B, K * ‖M.indicator θ w - c‖ ∂μ :=
      norm_integral_le_of_norm_le (hfc.norm.const_mul K) (ae_of_all _ fun w => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hψK' w) (norm_nonneg _))
    rw [integral_const_mul, integral_norm_eq_lintegral_enorm hfc.aestronglyMeasurable] at hle
    rw [h2, h1, h6, ← Real.norm_eq_abs]
    exact hle
  -- Weighted approximate tangent space at a Lebesgue point (Simon Ch. 3, 1.4 ⇒ 1.7): if
  -- `Hⁿ((M ∩ B̆_ε(y)) \ S) = 0`, `Hⁿ(S ∩ B̆_ε(y)) < ∞`, `P` is the approximate tangent space of `S`
  -- at `y` and `r⁻ⁿ ∫_{S ∩ B_r(y)} |1_M θ − θ(y)| dHⁿ → 0`, then `P` is the approximate tangent
  -- space of `M` with respect to `θ` at `y`.
  have hPT : ∀ (y : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)) (ε : ℝ), 0 < ε →
      (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 →
      (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ →
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P →
      Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) *
        ∫⁻ w in S ∩ closedBall y r, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
        (𝓝[>] 0) (𝓝 0) →
      Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
    intro y P ε hε hMSε hSfin hS hleb
    refine ⟨hS.1, fun φ => ?_⟩
    -- `φ` vanishes outside `B_ρ(0)` for some `ρ > 0`, and `|φ| ≤ K`.
    obtain ⟨ρ, hρ, hφρ⟩ := φ.hasCompactSupport.exists_pos_le_norm
    obtain ⟨K, hK⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
    -- The Lebesgue-point hypothesis along the radii `r ρ`: `L(r ρ) < ∞` and `r⁻ⁿ L(r ρ) → 0`.
    obtain ⟨hLfin, hLlim⟩ := Submission.dohr_tp_wtlp_rescaled_limit n
      (fun t => ∫⁻ w in S ∩ closedBall y t, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
      ρ hρ hleb
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * ρ < ε :=
      (((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).eventually
        (eventually_lt_nhds hε)).filter_mono nhdsWithin_le_nhds
    -- `I(r) - θ(y) J(r) → 0` for the weighted and unweighted blow-up integrals `I`, `J`.
    have key : Tendsto (fun r : ℝ =>
        (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' M, φ z * θ (y + r • z)
            ∂(μHE[n] : Measure (Amb n ℓ))) -
          θ y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, φ z
            ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
      have hlimK := hLlim.const_mul K
      rw [mul_zero] at hlimK
      refine squeeze_zero_norm' ?_ hlimK
      filter_upwards [self_mem_nhdsWithin, hsmall, hLfin] with r hr hrε hLr
      have hr' : (0 : ℝ) < r := hr
      have hBε : closedBall y (r * ρ) ⊆ ball y ε := closedBall_subset_ball hrε
      -- `ψ = φ ∘ η_{y,r}` is continuous, bounded by `K`, and vanishes off `B_{rρ}(y)`.
      have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
        show Continuous fun w : Amb n ℓ => r⁻¹ • (w - y) by fun_prop
      have hψ0 : ∀ w, w ∉ closedBall y (r * ρ) →
          φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w) = 0 := by
        intro w hw
        apply hφρ
        rw [mem_closedBall, not_le] at hw
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
          Real.norm_of_nonneg hr'.le, ← dist_eq_norm, le_inv_mul_iff₀ hr']
        exact hw.le
      -- The comparison on `B_{rρ}(y)`, using `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`.
      have hcmpr := hcmp (closedBall y (r * ρ))
        (fun w => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w)) (θ y) K measurableSet_closedBall
        (measure_mono_null (sdiff_subset_sdiff_left (inter_subset_inter_right M hBε)) hMSε)
        (ne_top_of_le_ne_top hSfin (measure_mono (inter_subset_inter_right S hBε)))
        ((map_continuous φ).comp hηc).measurable
        (fun w => by rw [← Real.norm_eq_abs]; exact hK _) hψ0 hLr
      -- Undo the blow-ups: `I(r) = r⁻ⁿ ∫_M ψ θ` and `J(r) = r⁻ⁿ ∫_S ψ`.
      have hJ := rsod_blowUp_setIntegral_eq n ℓ S φ (fun _ => 1) y r hr'
      simp only [mul_one] at hJ
      have hpos : (0 : ℝ) < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr' n)
      rw [rsod_blowUp_setIntegral_eq n ℓ M φ θ y r hr', hJ, Real.norm_eq_abs, mul_left_comm (θ y),
        ← mul_sub, abs_mul, abs_of_pos hpos, mul_left_comm K]
      exact mul_le_mul_of_nonneg_left hcmpr hpos.le
    -- `J(r) → ∫_P φ` by the tangent-space hypothesis on `S`, hence `I(r) → θ(y) ∫_P φ`.
    have h2 := key.add ((hS.2 φ).const_mul (θ y))
    rw [zero_add] at h2
    refine Tendsto.congr (fun r => ?_) h2
    exact sub_add_cancel _ _
  -- `ν = Hⁿ ⌞ (S ∩ O)` has `n`-dimensional growth and `f = 1_M θ` is `ν`-integrable.
  have hνgrowth : ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) (closedBall z r) ≤
        ENNReal.ofReal (C * r ^ n) := by
    intro z r hr
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm (closedBall z r)]
    exact hgrowth z r hr
  have hf : Integrable (M.indicator θ) ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) :=
    (integrableOn_indicator_iff hM).2
      (hθint.mono_set (inter_subset_inter_right M inter_subset_right))
  -- The points of `S ∩ O` that are not Lebesgue points of `f` form an `Hⁿ`-null set.
  have hbad := nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply (S ∩ O) _).trans
    (ae_iff.1 (Submission.dohr_tp_ae_lebesgue_point_of_growth n ℓ
      ((μHE[n] : Measure (Amb n ℓ)).restrict (S ∩ O)) (M.indicator θ) C hf hνgrowth)).le)
  -- Inside `M`, the conclusion can only fail on `((M ∩ O) \ S) ∪ (non-Lebesgue points ∩ S ∩ O)`.
  rw [ae_iff, Measure.restrict_apply₀' hM]
  refine measure_mono_null ?_ (measure_union_null hMS hbad)
  rintro y ⟨hy, hyM⟩
  have hyO : y ∈ O := by
    by_contra hyO
    exact hy fun h => absurd h hyO
  by_cases hyS : y ∈ S
  · refine Or.inr ⟨fun hyLeb => hy fun _ P hP => ?_, hyS, hyO⟩
    -- `y ∈ M ∩ O ∩ S` is a Lebesgue point: use a ball `B̆_ε(y) ⊆ O`.
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO y hyO
    have hMε : (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 :=
      measure_mono_null (Set.sdiff_subset_sdiff_left (inter_subset_inter_right M hεO)) hMS
    have hSε : (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono ?_).trans (hgrowth y ε hε))
      exact fun x hx => ⟨⟨hx.1, hεO hx.2⟩, ball_subset_closedBall hx.2⟩
    refine hPT y P ε hε hMε hSε hP (hyLeb.congr' ?_)
    -- For `r < ε`, `B_r(y) ∩ (S ∩ O) = S ∩ B_r(y)`, and `f y = θ y` since `y ∈ M`.
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    have hball : closedBall y r ∩ (S ∩ O) = S ∩ closedBall y r := by
      ext x
      exact ⟨fun hx => ⟨hx.2.1, hx.1⟩,
        fun hx => ⟨hx.2, hx.1, hεO (closedBall_subset_ball hr.2 hx.2)⟩⟩
    rw [Measure.restrict_restrict measurableSet_closedBall, hball, indicator_of_mem hyM]
  · exact Or.inl ⟨⟨hyM, hyO⟩, hyS⟩

/-- The rotated, translated graph chart `φ x = q (graphPoint x (u x)) + x₀` of a map `u` that is
`C¹` on an open set `Ω ⊆ ℝⁿ` is injective on all of `ℝⁿ`, `C¹` on `Ω`, and has injective
derivative at every point of `Ω`.  By `rsod_graphPoint_eq_finAddEquivProd_symm`,
`φ x = A (x, u x) + x₀` for the injective continuous linear map `A = q ∘ E.symm`,
`E = EuclideanSpace.finAddEquivProd`.  Hence `φ x = φ x'` forces `(x, u x) = (x', u x')`; `φ` is
`C¹` on `Ω` as `A` after the `C¹` map `x ↦ (x, u x)`, plus a constant; and at `x ∈ Ω` (a
neighbourhood of `x`, so `u` is differentiable there) the chain rule gives
`Dφ(x) v = A (v, Du(x) v)`, which determines `v` since `A` is injective. -/
theorem rsod_graphChart_injective_contDiffOn_fderiv_injective : ∀ {n ℓ : ℕ}
    (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (x₀ : Amb n ℓ) (Ω : Set (Rn n)), IsOpen Ω →
    ContDiffOn ℝ 1 u Ω → Function.Injective (fun x => q (graphPoint x (u x)) + x₀) ∧
      ContDiffOn ℝ 1 (fun x => q (graphPoint x (u x)) + x₀) Ω ∧
      ∀ x ∈ Ω, Function.Injective (fderiv ℝ (fun x => q (graphPoint x (u x)) + x₀) x) := by
  intro n ℓ q u x₀ Ω hΩ hu
  let E : Amb n ℓ ≃L[ℝ] Rn n × Rn ℓ := EuclideanSpace.finAddEquivProd
  let A : Rn n × Rn ℓ →L[ℝ] Amb n ℓ := (q : Amb n ℓ →L[ℝ] Amb n ℓ).comp (E.symm : _ →L[ℝ] _)
  have hA : Function.Injective A := q.injective.comp E.symm.injective
  have hφ : (fun x => q (graphPoint x (u x)) + x₀) = fun x => A (x, u x) + x₀ := by
    funext x
    simp [A, E, rsod_graphPoint_eq_finAddEquivProd_symm]
  rw [hφ]
  refine ⟨fun x x' h => (Prod.ext_iff.mp (hA (add_right_cancel h))).1,
    (A.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)).add contDiffOn_const, fun x hx => ?_⟩
  have hux : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt
  have hφx : HasFDerivAt (fun x => A (x, u x) + x₀)
      (A.comp ((ContinuousLinearMap.id ℝ (Rn n)).prod (fderiv ℝ u x))) x :=
    (A.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hux)).add_const x₀
  rw [hφx.fderiv]
  exact fun v w h => (Prod.ext_iff.mp (hA h)).1
/-- Simon Ch. 3, Theorem 1.9 (measurability of `x ↦ p_{T_x M}`, used for Ch. 5, Lemma 2.1): for
injective `L : ℝⁿ → ℝ^{n+ℓ}` the orthogonal projection onto `L(ℝⁿ)` is `L (Lᵀ L)⁻¹ Lᵀ`, hence it
depends continuously on `L`.  Here `Lᵀ w = Σᵢ ⟨L eᵢ, w⟩ eᵢ` is the transpose, `Lᵀ L` is a unit of
`End(ℝⁿ)` because `⟨Lᵀ L v, v⟩ = |L v|²`, inversion is continuous at units, and
`w − L (Lᵀ L)⁻¹ Lᵀ w ⊥ L(ℝⁿ)` identifies the formula with `p_{L(ℝⁿ)}`. -/
theorem aetp_starProjection_range_continuousOn : ∀ (n ℓ : ℕ), ContinuousOn (fun L : Rn n →L[ℝ] Amb n ℓ => (LinearMap.range L.toLinearMap).starProjection) {L : Rn n →L[ℝ] Amb n ℓ | Function.Injective L} := by
  intro n ℓ
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

/-- Simon Ch. 5, Theorem 7.1 (tangent planes of the rotated graph `Q(graph u)`): if `u` is `C¹` on
the open ball `B̆_R(0)` and `G z = (z, u z)`, then the projection `p_{Q(DG(x)(ℝⁿ))}` onto the rotated
tangent plane depends continuously on `x ∈ B̆_R(0)`.  By
`rsod_graphChart_injective_contDiffOn_fderiv_injective` (with `q = id`, `x₀ = 0`), `G` is `C¹` on
the ball with injective derivative there, so `x ↦ DG(x)` is continuous on the ball and
`aetp_starProjection_range_continuousOn` makes `x ↦ p_{DG(x)(ℝⁿ)}` continuous there.  Finally
`p_{Q K} = Q ∘ p_K ∘ Q⁻¹` (`Submodule.starProjection_map_apply`), and composing with the fixed
maps `Q`, `Q⁻¹` is continuous. -/
theorem dohr_tp_projection_continuousOn : ∀ (n ℓ : ℕ) (R : ℝ) (u : Rn n → Rn ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ), ContDiffOn ℝ 1 u (ball 0 R) → ContinuousOn (fun x : Rn n => (Submodule.map Q.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection) (ball 0 R) := by
  intro n ℓ R u Q hu
  -- The graph map `G z = (z, u z)` is `C¹` on the ball, with injective derivative there.
  obtain ⟨-, hGc, hGi⟩ := rsod_graphChart_injective_contDiffOn_fderiv_injective
    (LinearIsometryEquiv.refl ℝ (Amb n ℓ)) u 0 (ball 0 R) isOpen_ball hu
  have hG : (fun x => (LinearIsometryEquiv.refl ℝ (Amb n ℓ)) (graphPoint x (u x)) + 0) =
      fun z : Rn n => graphPoint z (u z) := by
    funext x
    simp
  rw [hG] at hGc hGi
  set G := fun z : Rn n => graphPoint z (u z)
  -- `x ↦ p_{DG(x)(ℝⁿ)}` is continuous on the ball.
  have hP : ContinuousOn (fun x => (LinearMap.range (fderiv ℝ G x).toLinearMap).starProjection)
      (ball 0 R) :=
    (aetp_starProjection_range_continuousOn n ℓ).comp
      (hGc.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl) fun x hx => hGi x hx
  -- Conjugation by `Q`: `p_{Q K} = Q ∘ p_K ∘ Q⁻¹`.
  let Qc : Amb n ℓ →L[ℝ] Amb n ℓ := Q.toContinuousLinearEquiv
  let Qs : Amb n ℓ →L[ℝ] Amb n ℓ := Q.symm.toContinuousLinearEquiv
  have hconj : ContinuousOn (fun x =>
      Qc.comp ((LinearMap.range (fderiv ℝ G x).toLinearMap).starProjection.comp Qs)) (ball 0 R) :=
    continuousOn_const.clm_comp (hP.clm_comp continuousOn_const)
  refine hconj.congr fun x _ => ?_
  ext1 w
  simp [Submodule.starProjection_map_apply, Qc, Qs]
/-- **Tangent planes of `V` where `spt V` is a `C¹` graph** (Simon Ch. 3, 1.4–1.9).  If
`Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)`, `u ∈ C¹(B̆_R(0))`, `B_s(ξ) ⊆ U` and `s ≤ R`, then
`p_{T_y V}` is the projection onto `Q⁻¹(range DG(x))` for `μ_V`-a.e. `y ∈ B̆_s(ξ)` and every `x`
with `Q(y − ξ) = G(x) = (x, u(x))`, and `y ↦ p_{T_y V}` is `μ_V ⌞ B̆_s(ξ)`-a.e. strongly measurable.
On `B̆_{s'}(ξ)`, `s' < s`, `M` lies in `S = ξ + Q⁻¹(graph u)` up to an `Hⁿ`-null set and `S` has
`n`-dimensional growth, so a.e. the plane `Q⁻¹(range DG(x))` of `S` at `y` is a weighted
approximate tangent plane of `(M, θ)`; uniqueness (`θ(y) > 0`) identifies `tangentProj`.  The
measurable representative is `y ↦ p(π(Q(y − ξ)))`, `π` the first `n` coordinates. -/
theorem dohr_graph_tangent_planes : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → AEStronglyMeasurable (fun y => V.tangentProj y) (V.weight.restrict (ball ξ s)) ∧ ∀ᵐ y ∂V.weight, y ∈ ball ξ s → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
  intro n ℓ hn U _ V ξ s R Q u hs hsR hBU hu hgraph
  -- `A w = ξ + Q⁻¹ w` is an isometry inverting `y ↦ Q (y - ξ)`.
  have hA : Isometry (fun w : Amb n ℓ => ξ + Q.symm w) :=
    Isometry.of_dist_eq fun a b => by rw [dist_add_left, Q.symm.dist_map]
  have hback : ∀ (y : Amb n ℓ) (x : Rn n), Q (y - ξ) = graphPoint x (u x) →
      ξ + Q.symm (graphPoint x (u x)) = y := by
    intro y x h
    rw [← h, LinearIsometryEquiv.symm_apply_apply, add_sub_cancel]
  -- `|a| ≤ |(a, b)|`.
  have hnorm : ∀ (a : Rn n) (b : Rn ℓ), ‖a‖ ≤ ‖graphPoint a b‖ := by
    intro a b
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    rw [Fin.sum_univ_add]
    simp only [graphPoint, Fin.append_left]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  -- Points of `spt V` in `B̆_R(ξ)` lie on the graph after the motion `y ↦ Q (y - ξ)`.
  have hon : ∀ y ∈ V.support, y ∈ ball ξ R →
      ∃ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) := by
    intro y hy hyR
    have hmem : Q (y - ξ) ∈ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R :=
      ⟨⟨y - ξ, ⟨y, hy, rfl⟩, rfl⟩, by
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact hyR⟩
    rw [hgraph] at hmem
    obtain ⟨⟨x, hx, hxy⟩, -⟩ := hmem
    exact ⟨x, hx, hxy.symm⟩
  -- `μ_V` is carried by `spt μ_V` and by `M`, and `M \ spt μ_V` is `Hⁿ`-null.
  have hsupp : ∀ᵐ y ∂V.weight, y ∈ V.weight.support := Measure.support_mem_ae
  have hac : V.weight ≪ (μHE[n] : Measure (Amb n ℓ)).restrict V.carrier :=
    withDensity_absolutelyContinuous _ _
  have hmemM : ∀ᵐ y ∂V.weight, y ∈ V.carrier :=
    hac.ae_le (ae_restrict_mem₀ V.nullMeasurableSet_carrier)
  have hMsupp : (μHE[n] : Measure (Amb n ℓ)) (V.carrier ∩ V.weight.supportᶜ) = 0 := by
    have h0 : ((μHE[n] : Measure (Amb n ℓ)).restrict V.carrier).withDensity
        (fun x => ENNReal.ofReal (V.mult x)) V.weight.supportᶜ = 0 :=
      Measure.measure_compl_support
    rw [withDensity_apply_eq_zero' V.aemeasurable_mult.ennreal_ofReal,
      Measure.restrict_apply₀' V.nullMeasurableSet_carrier] at h0
    refine measure_mono_null ?_ h0
    rintro y ⟨hyM, hy⟩
    exact ⟨⟨(ENNReal.ofReal_pos.2 (V.mult_pos y hyM)).ne', hy⟩, hyM⟩
  -- `Q⁻¹(range DG(x))` is the approximate tangent space of `S = A(graph u)` at `A(G x)`.
  have htan : ∀ x ∈ ball (0 : Rn n) R,
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n
        ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) (ξ + Q.symm (graphPoint x (u x)))
        (Submodule.map Q.symm.toLinearEquiv.toLinearMap
          (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)) :=
    fun x hx => Submission.dohr_tp_approx_tangent_affine_isometry n ℓ _ _ ξ Q.symm _
      (Submission.dohr_tp_graph_approx_tangent n ℓ hn R u hu x hx)
  -- The claim on `B̆_{s'}(ξ)` for each `s' < s`.
  have hkey : ∀ s' : ℝ, 0 < s' → s' < s → ∀ᵐ y ∂V.weight, y ∈ ball ξ s' →
      ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) →
        V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
          (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
    intro s' hs' hs's
    have hball : ball ξ s' ⊆ closedBall ξ s :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall hs's.le)
    -- `n`-dimensional growth of `S ∩ B̆_{s'}(ξ)`, through the graph over `B̆_{s'}(0)`.
    obtain ⟨C, -, hC⟩ :=
      Submission.dohr_tp_graph_ball_growth n ℓ hn R s' u hs' (hs's.trans_le hsR) hu
    have hgrowth : ∀ (z : Amb n ℓ) (r : ℝ), 0 < r →
        (μHE[n] : Measure (Amb n ℓ)) ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R) ∩
          ball ξ s' ∩ closedBall z r) ≤ ENNReal.ofReal (C * r ^ n) := by
      intro z r hr
      refine le_trans (measure_mono ?_) ((hA.euclideanHausdorffMeasure_image
        (graphOver u (ball 0 s') ∩ closedBall (Q (z - ξ)) r)).trans_le (hC (Q (z - ξ)) r hr))
      rintro y ⟨⟨⟨g, ⟨x, -, rfl⟩, rfl⟩, hyb⟩, hyz⟩
      refine ⟨graphPoint x (u x), ⟨⟨x, ?_, rfl⟩, ?_⟩, rfl⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map] at hyb
        rw [mem_ball_zero_iff]
        exact (hnorm x (u x)).trans_lt hyb
      · rw [mem_closedBall] at hyz ⊢
        rw [← Q.symm.dist_map, LinearIsometryEquiv.symm_apply_apply, ← dist_add_left ξ,
          add_sub_cancel]
        exact hyz
    -- `M ∩ B̆_{s'}(ξ)` lies in `S` up to an `Hⁿ`-null set.
    have hnull : (μHE[n] : Measure (Amb n ℓ))
        ((V.carrier ∩ ball ξ s') \ (fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) = 0 := by
      refine measure_mono_null ?_ hMsupp
      rintro y ⟨⟨hyM, hyb⟩, hyS⟩
      refine ⟨hyM, fun hy => hyS ?_⟩
      obtain ⟨x, hx, hxy⟩ :=
        hon y ⟨hBU (hball hyb), hy⟩ (ball_subset_ball (hs's.le.trans hsR) hyb)
      exact ⟨graphPoint x (u x), ⟨x, hx, rfl⟩, hback y x hxy⟩
    have hint : IntegrableOn V.mult (V.carrier ∩ ball ξ s') (μHE[n] : Measure (Amb n ℓ)) :=
      (V.integrableOn_mult _ (isCompact_closedBall ξ s) hBU).mono_set
        (inter_subset_inter_right _ hball)
    have h6 := Submission.dohr_tp_ae_weighted_tangent_of_growth n ℓ V.carrier
      ((fun w => ξ + Q.symm w) '' graphOver u (ball 0 R)) (ball ξ s') V.mult C isOpen_ball
      V.nullMeasurableSet_carrier V.aemeasurable_mult hint hnull hgrowth
    filter_upwards [hac.ae_le h6, hmemM] with y hy6 hyM hyb x hx hxy
    have hT := htan x hx
    rw [hback y x hxy] at hT
    have hW := hy6 hyb _ hT
    have hex : ∃ P : Submodule ℝ (Amb n ℓ),
        Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n V.carrier V.mult y P :=
      ⟨_, hW⟩
    rw [RectifiableVarifold.tangentProj, dite_eq_left hex]
    congr 1
    exact Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt.unique
      (V.mult_pos y hyM).ne' (Classical.choose_spec hex) hW
  -- Exhaust `B̆_s(ξ)` by the balls `B̆_{s - s/(k+2)}(ξ)`.
  have hsecond : ∀ᵐ y ∂V.weight, y ∈ ball ξ s → ∀ x ∈ ball (0 : Rn n) R,
      Q (y - ξ) = graphPoint x (u x) →
        V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
          (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection := by
    have hrad : ∀ k : ℕ, 0 < s - s / ((k : ℝ) + 2) ∧ s - s / ((k : ℝ) + 2) < s := fun k =>
      ⟨sub_pos.2 (div_lt_self hs (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])),
        sub_lt_self _ (by positivity)⟩
    filter_upwards [ae_all_iff.2 fun k : ℕ => hkey _ (hrad k).1 (hrad k).2] with y hy hys
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos (sub_pos.2 (mem_ball.1 hys)) hs)
    refine hy k (mem_ball.2 ?_)
    have h1 : s / ((k : ℝ) + 2) < s / ((k : ℝ) + 1) :=
      div_lt_div_of_pos_left hs (by positivity) (by linarith)
    have h2 : s / ((k : ℝ) + 1) < s - dist y ξ := by
      rw [div_lt_div_iff₀ (by positivity) hs] at hk
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  refine ⟨?_, hsecond⟩
  -- Measurability: `tangentProj y = p (π (Q (y - ξ)))` a.e., with `p` continuous on `B̆_R(0)`.
  let π : Amb n ℓ → Rn n := fun w => WithLp.toLp 2 (fun i : Fin n => w (Fin.castAdd ℓ i))
  have hπ : Continuous π := by fun_prop
  have hπG : ∀ x : Rn n, π (graphPoint x (u x)) = x := by
    intro x
    ext i
    simp [π, graphPoint]
  let f : Amb n ℓ → Rn n := fun y => π (Q (y - ξ))
  have hf : Continuous f := hπ.comp (Q.continuous.comp (continuous_id.sub continuous_const))
  let p : Rn n → (Amb n ℓ →L[ℝ] Amb n ℓ) := fun x =>
    (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
      (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection
  have hp : ContinuousOn p (ball 0 R) :=
    Submission.dohr_tp_projection_continuousOn n ℓ R u Q.symm hu
  have hae : ∀ᵐ y ∂V.weight.restrict (ball ξ s),
      y ∈ f ⁻¹' ball 0 R ∧ (p ∘ f) y = V.tangentProj y := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hsecond, hsupp] with y hy hyS hys
    obtain ⟨x, hx, hxy⟩ := hon y ⟨hBU (ball_subset_closedBall hys), hyS⟩ (ball_subset_ball hsR hys)
    have hfx : f y = x := by
      show π (Q (y - ξ)) = x
      rw [hxy, hπG]
    refine ⟨by rw [mem_preimage, hfx]; exact hx, ?_⟩
    rw [Function.comp_apply, hfx]
    exact (hy hys x hx hxy).symm
  have hmeas : AEStronglyMeasurable (p ∘ f)
      ((V.weight.restrict (ball ξ s)).restrict (f ⁻¹' ball 0 R)) :=
    (hp.comp hf.continuousOn (mapsTo_preimage f _)).aestronglyMeasurable
      (isOpen_ball.preimage hf).measurableSet
  rw [Measure.restrict_eq_self_of_ae_mem (hae.mono fun y hy => hy.1)] at hmeas
  exact hmeas.congr (hae.mono fun y hy => hy.2)

/-- `det(I + G) > 0` for the Gram matrix `G = (⟨P eₐ, P e_b⟩)_{a,b}` of a linear map
`P : ℝⁿ → ℝ^ℓ`.  Since `ξ ⬝ᵥ G ξ = ‖P (Σₐ ξₐ eₐ)‖² ≥ 0`, the matrix `I + s G` has trivial kernel
for every `s ≥ 0` (`Matrix.exists_mulVec_eq_zero_iff`), so the continuous function
`s ↦ det(I + s G)` does not vanish on `[0, 1]`.  It equals `1` at `s = 0`, hence is positive at
`s = 1` by the intermediate value theorem (`intermediate_value_Icc'`). -/
theorem dohr_eb_ail_gram_det_pos : ∀ n ℓ : ℕ, ∀ P : Rn n →L[ℝ] Rn ℓ, 0 < Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) := by
  intro n ℓ P
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b : Fin n =>
    inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))) with hG
  have hquad : ∀ ξ : Fin n → ℝ, dotProduct ξ (G.mulVec ξ) =
      ‖P (∑ a, ξ a • EuclideanSpace.single a (1 : ℝ))‖ ^ 2 := by
    intro ξ
    rw [← real_inner_self_eq_norm_sq]
    simp only [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum, conj_trivial, hG]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [real_inner_comm]
    ring
  have hne : ∀ s : ℝ, 0 ≤ s → Matrix.det (1 + s • G) ≠ 0 := by
    intro s hs hdet
    obtain ⟨ξ, hξ, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : dotProduct ξ ((1 + s • G).mulVec ξ) = 0 := by rw [hker, dotProduct_zero]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, hquad] at h0
    have hsq : 0 ≤ dotProduct ξ ξ := Finset.sum_nonneg fun i _ => mul_self_nonneg (ξ i)
    have hξξ : dotProduct ξ ξ = 0 := by
      linarith [mul_nonneg hs (sq_nonneg ‖P (∑ a, ξ a • EuclideanSpace.single a (1 : ℝ))‖)]
    apply hξ
    funext i
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      fun j _ => mul_self_nonneg (ξ j)).mp hξξ i (Finset.mem_univ i))
  have hcont : Continuous fun s : ℝ => Matrix.det (1 + s • G) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  by_contra hneg
  have h1 : Matrix.det (1 + (1 : ℝ) • G) ≤ 0 := by
    rw [one_smul]
    exact not_lt.mp hneg
  have h0 : (0 : ℝ) ≤ Matrix.det (1 + (0 : ℝ) • G) := by
    rw [zero_smul, add_zero, Matrix.det_one]
    exact zero_le_one
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn ⟨h1, h0⟩
  exact hne s hs0 hs
/-- Smoothness of the graph area integrand.  For `P ∈ L(ℝⁿ, ℝ^ℓ)` put
`G(P) = (⟨P eₐ, P e_b⟩)_{a,b}`; then `J(P) = √(det(I + G(P)))` is `C^∞` on `L(ℝⁿ, ℝ^ℓ)`.
Each entry `P ↦ δ_{ab} + ⟨P eₐ, P e_b⟩` is smooth (evaluation at `eₐ` is continuous linear and
the inner product is bilinear), so `det(I + G(P))` is smooth by the Leibniz formula
(`Matrix.det_apply`, `ContDiff.sum`, `contDiff_prod`).  It is positive
(`dohr_eb_ail_gram_det_pos`), and `√` is smooth away from `0` (`ContDiff.sqrt`). -/
theorem dohr_eb_ail_contDiff : ∀ n ℓ : ℕ, ContDiff ℝ (⊤ : ℕ∞) (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) := by
  intro n ℓ
  have hentry : ∀ i j : Fin n, ContDiff ℝ (⊤ : ℕ∞) fun P : Rn n →L[ℝ] Rn ℓ =>
      ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
        inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) i j := by
    intro i j
    simp only [Matrix.add_apply, Matrix.of_apply]
    exact contDiff_const.add (ContDiff.inner ℝ
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single i (1 : ℝ))).contDiff
      (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single j (1 : ℝ))).contDiff)
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun P : Rn n →L[ℝ] Rn ℓ =>
      Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
        inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))) := by
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hentry (σ i) i)
  exact hdet.sqrt fun P => (Submission.dohr_eb_ail_gram_det_pos n ℓ P).ne'
/-- Second derivative of a `C²` function along a line (the chain-rule step used for the Legendre
condition of the area integrand in the elliptic bootstrap, Simon Ch. 5, Theorem 7.1): if
`F : E → ℝ` is `C²`, then `g(t) = F(x + t v)` satisfies `g''(0) = D²F(x)[v][v]`.  By the chain
rule `g'(t) = DF(x + t v)[v]` for every `t`; the chain rule for `t ↦ DF(x + t v)` at `t = 0` and
evaluation at the constant vector `v` give `g''(0) = D(DF)(x)[v][v]`. -/
theorem dohr_eb_ail_line_second_deriv : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F → ∀ x v : E, deriv (deriv (fun t : ℝ => F (x + t • v))) 0 = fderiv ℝ (fderiv ℝ F) x v v := by
  intro E _ _ F hF x v
  -- Step 1 (regularity): `F` is differentiable and `DF = fderiv ℝ F` is `C¹`, hence differentiable.
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- Step 2: the line `γ(t) = x + t v` has derivative `v` at every `t`.
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  -- Step 3 (chain rule): `deriv g` is `t ↦ DF(x + t v)[v]`.
  have hg : deriv (fun t : ℝ => F (x + t • v)) = fun t => fderiv ℝ F (x + t • v) v := by
    funext t
    exact ((hF1 _).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  rw [hg]
  -- Step 4 (chain rule for `t ↦ DF(x + t v)` at `0`, then evaluation at the constant `v`):
  -- the derivative at `0` is `D(DF)(x)[v][v] + DF(x)[0] = D(DF)(x)[v][v]`.
  have h0 := (hD _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
  have h2 := h0.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simp only [zero_smul, add_zero, map_zero] at h2
  -- Step 5: conclude.
  exact h2.deriv
/-- Second derivative of `t ↦ √(det(I + t² S))` at `0`.  By `Matrix.det_one_add_smul`,
`p(t) = det(I + t² S) = 1 + τ t² + R(t²) t⁴` with `τ = tr S` and a fixed polynomial `R`, so
`p(0) = 1`, `p'(0) = 0` and `p''(0) = 2τ`.  Near `0` we have `p > 0`, hence
`(√p)' = p' / (2√p)` there, and the quotient rule at `0` gives `(√p)''(0) = p''(0) / 2 = τ`. -/
theorem dohr_eb_ail_sqrt_det_second_deriv : ∀ n : ℕ, ∀ S : Matrix (Fin n) (Fin n) ℝ, deriv (deriv (fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + t ^ 2 • S)))) 0 = Matrix.trace S := by
  intro n S
  -- `p(t) = 1 + τ t² + R(t²) t⁴` (Taylor expansion of the determinant).
  obtain ⟨R, hR⟩ : ∃ R : Polynomial ℝ, ∀ r : ℝ,
      Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + r • S) =
        1 + Matrix.trace S * r + R.eval r * r ^ 2 :=
    ⟨_, fun r => Matrix.det_one_add_smul r S⟩
  have hf : (fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + t ^ 2 • S))) =
      fun t => Real.sqrt (1 + Matrix.trace S * t ^ 2 + R.eval (t ^ 2) * t ^ 4) := by
    funext t
    rw [hR (t ^ 2)]
    ring_nf
  rw [hf]
  -- It suffices to know `p(0) = 1`, `p'(0) = 0` and `p''(0) = 2τ`.
  suffices H : ∀ p p' : ℝ → ℝ, (∀ t, HasDerivAt p (p' t) t) → p 0 = 1 → p' 0 = 0 →
      HasDerivAt p' (2 * Matrix.trace S) 0 →
      deriv (deriv (fun t => Real.sqrt (p t))) 0 = Matrix.trace S by
    have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := fun t => by
      simpa using hasDerivAt_pow 2 t
    have hR2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => R.eval (t ^ 2))
        (R.derivative.eval (t ^ 2) * (2 * t)) t := fun t => by
      have := (R.hasDerivAt (t ^ 2)).comp t (h2 t)
      simpa [Function.comp_def] using this
    have hR2' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => R.derivative.eval (t ^ 2) * (2 * t))
        (R.derivative.derivative.eval (t ^ 2) * (2 * t) * (2 * t) +
          R.derivative.eval (t ^ 2) * 2) t := fun t => by
      have hR'2 : HasDerivAt (fun t : ℝ => R.derivative.eval (t ^ 2))
          (R.derivative.derivative.eval (t ^ 2) * (2 * t)) t := by
        have := (R.derivative.hasDerivAt (t ^ 2)).comp t (h2 t)
        simpa [Function.comp_def] using this
      have := hR'2.fun_mul ((hasDerivAt_id' t).const_mul 2)
      convert this using 1
      ring
    refine H (fun t => 1 + Matrix.trace S * t ^ 2 + R.eval (t ^ 2) * t ^ 4)
      (fun t => 2 * Matrix.trace S * t + R.derivative.eval (t ^ 2) * (2 * t) * t ^ 4 +
        R.eval (t ^ 2) * (4 * t ^ 3)) (fun t => ?_) (by simp) (by simp) ?_
    · have := (((hasDerivAt_const t (1 : ℝ)).fun_add ((h2 t).const_mul (Matrix.trace S))).fun_add
        ((hR2 t).fun_mul (hasDerivAt_pow 4 t)))
      convert this using 1
      push_cast
      ring
    · have := ((((hasDerivAt_id' (0 : ℝ)).const_mul (2 * Matrix.trace S)).fun_add
        ((hR2' 0).fun_mul (hasDerivAt_pow 4 (0 : ℝ)))).fun_add
        ((hR2 0).fun_mul ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4)))
      convert this using 1
      simp
  intro p p' hp hp0 hp'0 hp''
  -- Near `0`, `p > 0`, so `(√p)' = p' / (2√p)` there.
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < p t :=
    continuousAt_const.eventually_lt (hp 0).continuousAt (by rw [hp0]; norm_num)
  have hderiv : deriv (fun t => Real.sqrt (p t)) =ᶠ[𝓝 0]
      fun t => p' t / (2 * Real.sqrt (p t)) := by
    filter_upwards [hpos] with t ht
    exact ((hp t).sqrt ht.ne').deriv
  rw [hderiv.deriv_eq]
  -- Quotient rule at `0`.
  have hd : HasDerivAt (fun t => 2 * Real.sqrt (p t)) (2 * (p' 0 / (2 * Real.sqrt (p 0)))) 0 :=
    ((hp 0).sqrt (by rw [hp0]; norm_num)).const_mul 2
  rw [(hp''.fun_div hd (by rw [hp0]; norm_num)).deriv, hp'0, hp0]
  simp
  ring
/-- Hessian at the origin of the area integrand (Legendre condition for the elliptic bootstrap
of Simon 7.1): for `J(P) = √det(I + G(P))` with Gram matrix `G(P)_{ab} = ⟨P e_a, P e_b⟩`,
`D²J(0)[Q, Q] = Σ_a |Q e_a|²`.  Along the line `t ↦ t • Q` the Gram matrix scales as
`G(t • Q) = t² G(Q)`, so `D²J(0)[Q, Q]` is the second derivative at `0` of
`t ↦ √det(I + t² G(Q))`, which is `trace G(Q) = Σ_a |Q e_a|²`. -/
theorem dohr_eb_ail_hessian_zero : ∀ n ℓ : ℕ, ∀ Q : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))))) 0 Q Q = ∑ a : Fin n, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2 := by
  intro n ℓ Q
  -- Step 1: `J` is `C^∞`, hence `C²`.
  have hC2 := (Submission.dohr_eb_ail_contDiff n ℓ).of_le (m := 2) (by norm_cast)
  -- Step 2: `D²J(0)[Q, Q]` is the second derivative at `0` of `t ↦ J(0 + t • Q)`.
  rw [← Submission.dohr_eb_ail_line_second_deriv _ hC2 0 Q]
  -- Step 3: `G(0 + t • Q) = t² G(Q)`, so `J(0 + t • Q) = √det(I + t² G(Q))` for every `t`.
  have hfun : (fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      Matrix.of fun a b : Fin n => inner ℝ ((0 + t • Q) (EuclideanSpace.single a (1 : ℝ)))
        ((0 + t • Q) (EuclideanSpace.single b (1 : ℝ)))))) =
      fun t : ℝ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
        t ^ 2 • Matrix.of fun a b : Fin n => inner ℝ (Q (EuclideanSpace.single a (1 : ℝ)))
          (Q (EuclideanSpace.single b (1 : ℝ))))) := by
    funext t
    congr 3
    ext a b
    simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
  -- Steps 4–5: the one-variable second derivative is `trace G(Q) = Σ_a ‖Q e_a‖²`.
  rw [hfun, Submission.dohr_eb_ail_sqrt_det_second_deriv]
  simp [Matrix.trace]
/-- The operator norm is at most the Hilbert–Schmidt norm: `‖Q‖² ≤ Σₐ ‖Q eₐ‖²` for every linear
`Q : ℝᵐ → ℝᵏ`.  Expanding `h = Σₐ hₐ eₐ` gives `‖Q h‖ ≤ Σₐ |hₐ| ‖Q eₐ‖ ≤ ‖h‖ (Σₐ ‖Q eₐ‖²)^{1/2}`
(triangle inequality, then Cauchy–Schwarz), so `‖Q‖ ≤ (Σₐ ‖Q eₐ‖²)^{1/2}` by
`ContinuousLinearMap.opNorm_le_bound`; square both sides. -/
theorem dohr_eb_ail_opNorm_sq_le : ∀ m k : ℕ, ∀ Q : Rn m →L[ℝ] Rn k, ‖Q‖ ^ 2 ≤ ∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2 := by
  intro m k Q
  have hQ : ‖Q‖ ≤ Real.sqrt (∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun h => ?_)
    have hexp : h = ∑ a : Fin m, h a • EuclideanSpace.single a (1 : ℝ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    have hQh : Q h = ∑ a : Fin m, h a • Q (EuclideanSpace.single a (1 : ℝ)) := by
      conv_lhs => rw [hexp]
      simp [map_sum, map_smul]
    calc ‖Q h‖ = ‖∑ a : Fin m, h a • Q (EuclideanSpace.single a (1 : ℝ))‖ := by rw [hQh]
      _ ≤ ∑ a : Fin m, ‖h a • Q (EuclideanSpace.single a (1 : ℝ))‖ := norm_sum_le _ _
      _ = ∑ a : Fin m, ‖h a‖ * ‖Q (EuclideanSpace.single a (1 : ℝ))‖ := by simp_rw [norm_smul]
      _ ≤ Real.sqrt (∑ a : Fin m, ‖h a‖ ^ 2) *
            Real.sqrt (∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt (∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2) * ‖h‖ := by
          rw [EuclideanSpace.norm_eq h, mul_comm]
  calc ‖Q‖ ^ 2 ≤ (Real.sqrt (∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hQ 2
    _ = ∑ a : Fin m, ‖Q (EuclideanSpace.single a (1 : ℝ))‖ ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))
/-- Local uniform continuity of the Hessian.  For a `C²` function `F : E → ℝ` and `δ > 0` there is
`ε > 0` with `|D²F(x)(Q, Q') - D²F(x₀)(Q, Q')| ≤ δ ‖Q‖ ‖Q'‖` whenever `‖x - x₀‖ ≤ ε`.
`D²F = fderiv ℝ (fderiv ℝ F)` is continuous (`ContDiff.fderiv_right`, `ContDiff.continuous_fderiv`),
so `‖D²F(x) - D²F(x₀)‖ < δ` near `x₀`, and the bilinear bound `ContinuousLinearMap.le_opNorm₂`
finishes. -/
theorem dohr_eb_ail_hessian_local_unif : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ), ContDiff ℝ 2 F → ∀ x₀ : E, ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, ‖x - x₀‖ ≤ ε → ∀ Q Q' : E, |fderiv ℝ (fderiv ℝ F) x Q Q' - fderiv ℝ (fderiv ℝ F) x₀ Q Q'| ≤ δ * (‖Q‖ * ‖Q'‖) := by
  intro E _ _ F hF x₀ δ hδ
  have hc : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  obtain ⟨r, hr, hball⟩ :=
    (Metric.continuousAt_iff (f := fderiv ℝ (fderiv ℝ F)) (a := x₀)).mp hc.continuousAt δ hδ
  refine ⟨r / 2, half_pos hr, fun x hx Q Q' => ?_⟩
  have hdist : dist x x₀ < r := by
    rw [dist_eq_norm]
    linarith
  have hlt : ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) x₀‖ < δ :=
    lt_of_eq_of_lt (@dist_eq_norm (E →L[ℝ] E →L[ℝ] ℝ) _ _ _).symm (hball hdist)
  have key := (fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) x₀).le_opNorm₂ Q Q'
  simp only [sub_apply, Real.norm_eq_abs] at key
  calc |fderiv ℝ (fderiv ℝ F) x Q Q' - fderiv ℝ (fderiv ℝ F) x₀ Q Q'|
      ≤ ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) x₀‖ * ‖Q‖ * ‖Q'‖ := key
    _ ≤ δ * (‖Q‖ * ‖Q'‖) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hlt.le (by positivity)
/-- Smoothness and Legendre ellipticity of the area integrand (Step 1 of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion).  For a linear `P : ℝⁿ → ℝ^ℓ` put
`G(P)_{ab} = ⟨P eₐ, P e_b⟩` and `J(P) = √(det(I + G(P)))`.  Then
(i) `J` is `C^∞` on `L(ℝⁿ, ℝ^ℓ)`, and
(ii) there is `ε > 0` with `½ ‖Q‖² ≤ D²J(P)[Q][Q]` for every `Q` whenever `‖P‖ ≤ ε`
(operator norms, `D²J(P)[Q][Q] = fderiv ℝ (fderiv ℝ J) P Q Q`).
Since `J` is `C²`, continuity of `D²J` at `0` gives `ε` with
`|D²J(P)[Q][Q] − D²J(0)[Q][Q]| ≤ ½ ‖Q‖²` for `‖P‖ ≤ ε`, while
`D²J(0)[Q][Q] = Σₐ |Q eₐ|² ≥ ‖Q‖²` (Cauchy–Schwarz). -/
theorem dohr_eb_area_integrand_legendre : ∀ n ℓ : ℕ, ContDiff ℝ (⊤ : ℕ∞) (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q : Rn n →L[ℝ] Rn ℓ, 1 / 2 * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ))))))) P Q Q := by
  intro n ℓ
  -- (i) `J` is `C^∞`
  refine ⟨Submission.dohr_eb_ail_contDiff n ℓ, ?_⟩
  -- (ii) `J` is in particular `C²`
  have hC2 := (Submission.dohr_eb_ail_contDiff n ℓ).of_le (m := 2) (by norm_cast)
  -- continuity of `D²J` at `0` with `δ = 1/2`:
  -- `|D²J(P)[Q][Q'] − D²J(0)[Q][Q']| ≤ ½ ‖Q‖ ‖Q'‖` whenever `‖P − 0‖ ≤ ε`
  obtain ⟨ε, hε, hunif⟩ :=
    Submission.dohr_eb_ail_hessian_local_unif _ hC2 0 (1 / 2) (by norm_num)
  refine ⟨ε, hε, fun P hP Q => ?_⟩
  have hclose := hunif P (by simpa using hP) Q Q
  -- `D²J(0)[Q][Q] = Σₐ |Q eₐ|²`
  rw [Submission.dohr_eb_ail_hessian_zero n ℓ Q] at hclose
  -- `‖Q‖² ≤ Σₐ |Q eₐ|²`
  have hHS := Submission.dohr_eb_ail_opNorm_sq_le n ℓ Q
  -- `D²J(P)[Q][Q] ≥ Σₐ |Q eₐ|² − ½ ‖Q‖² ≥ ‖Q‖² − ½ ‖Q‖²`
  have hlow := (abs_le.mp hclose).1
  nlinarith [hlow, hHS]
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if `h`
is `C^{m+1}` on the open set `V` and `0 < α ≤ 1`, then `Dᵐh` is `α`-Hölder on every compact
`K ⊆ V`.  `Dᵐh` is `C¹` near each point of `K`, so Lipschitz near it by the mean value inequality,
hence Lipschitz on the compact `K`; and `‖x - y‖ ≤ D^{1-α} ‖x - y‖^α` for `x, y ∈ K`,
`‖x - y‖ ≤ D`. -/
theorem dohr_eb_holder_of_contDiffOn_succ : ∀ (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (m : ℕ) (α : ℝ) (h : E₁ → E₂) (V : Set E₁), 0 < α → α ≤ 1 → IsOpen V → ContDiffOn ℝ (m + 1 : ℕ) h V → ∀ K : Set E₁, IsCompact K → K ⊆ V → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m h x - iteratedFDeriv ℝ m h y‖ ≤ C * ‖x - y‖ ^ α := by
  intro E₁ E₂ _ _ _ _ m α h V hα hα1 hV hh K hK hKV
  -- Step 1: `Dᵐh` is `C¹` near every point of `K ⊆ V`, hence locally Lipschitz on `K`.
  have hloc : LocallyLipschitzOn K (iteratedFDeriv ℝ m h) := by
    intro x hx
    have hx' : ContDiffAt ℝ 1 (iteratedFDeriv ℝ m h) x :=
      (hh.contDiffAt (hV.mem_nhds (hKV hx))).iteratedFDeriv_right (by norm_cast; omega)
    obtain ⟨L, t, ht, hL⟩ := hx'.exists_lipschitzOnWith
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
  -- Steps 2–4: by compactness, `Dᵐh` is Lipschitz on `K`.
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  -- Step 5: `K` is bounded, and Lipschitz on a bounded set gives `α`-Hölder.
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 hK.isBounded
  refine ⟨L * D ^ (1 - α), fun x hx y hy => ?_⟩
  have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have h1 : 1 - α + α ≠ 0 := by rw [sub_add_cancel]; exact one_ne_zero
  have hxy : ‖x - y‖ ≤ D := by rw [← dist_eq_norm]; exact hD hx hy
  have hd : ‖x - y‖ ≤ D ^ (1 - α) * ‖x - y‖ ^ α :=
    calc ‖x - y‖ = ‖x - y‖ ^ (1 - α) * ‖x - y‖ ^ α := by
          rw [← Real.rpow_add' h0 h1, sub_add_cancel, Real.rpow_one]
      _ ≤ D ^ (1 - α) * ‖x - y‖ ^ α :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow h0 hxy (sub_nonneg.2 hα1))
            (Real.rpow_nonneg h0 α)
  rw [mul_assoc]
  exact hL.norm_sub_le_of_le hx hy hd

/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): the
local Hölder class `C^{m,α}` is stable under composition.  Let `f` be `C^m` on the open set `U`
with `f(U) ⊆ V`, `h` be `C^m` on the open set `V`, `Dᵐf` and `Dᵐh` be `α`-Hölder on compact sets,
and `f` or `h` be `C¹` (automatic if `m ≥ 1`).  On `U`, `Dᵐ(h ∘ f)` is the Faà di Bruno sum
`(D•h ∘ f).taylorComp D•f` (`iteratedFDeriv_comp`).  On a compact `K ⊆ U` every `Dᵏh ∘ f` and
`Dᵏf`, `k ≤ m`, is bounded and `α`-Hölder (lower orders are Lipschitz by
`dohr_eb_holder_of_contDiffOn_succ`), so `taylorComp_sub_taylorComp_isBigO` along `𝓟 (K ×ˢ K)`
gives one Hölder constant for `Dᵐ(h ∘ f)` on `K`. -/
theorem dohr_eb_holder_comp : ∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] (m : ℕ) (α : ℝ) (f : E₁ → E₂) (h : E₂ → E₃) (U : Set E₁) (V : Set E₂), 0 < α → α ≤ 1 → IsOpen U → IsOpen V → MapsTo f U V → (1 ≤ m ∨ ContDiffOn ℝ 1 f U ∨ ContDiffOn ℝ 1 h V) → ContDiffOn ℝ m f U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m h V → (∀ K : Set E₂, IsCompact K → K ⊆ V → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m h x - iteratedFDeriv ℝ m h y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m (h ∘ f) U ∧ ∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (h ∘ f) x - iteratedFDeriv ℝ m (h ∘ f) y‖ ≤ C * ‖x - y‖ ^ α := by
  intro E₁ E₂ E₃ _ _ _ _ _ _ m α f h U V hα hα1 hU hV hfUV hdisj hf hfH hh hhH
  -- Step 1: chain rule; `f(K)` is a compact subset of `V`.
  refine ⟨hh.comp hf hfUV, fun K hK hKU => ?_⟩
  have hfK : IsCompact (f '' K) := hK.image_of_continuousOn (hf.continuousOn.mono hKU)
  have hfKV : f '' K ⊆ V := (hfUV.mono_left hKU).image_subset
  -- A Hölder bound on `K` is an `IsBigO` bound along the principal filter of `K ×ˢ K` ...
  have hconv : ∀ {F : Type} [NormedAddCommGroup F] (A : E₁ → F) (C : ℝ),
      (∀ x ∈ K, ∀ y ∈ K, ‖A x - A y‖ ≤ C * ‖x - y‖ ^ α) →
      (fun p : E₁ × E₁ => A p.1 - A p.2) =O[𝓟 (K ×ˢ K)] (fun p => ‖p.1 - p.2‖ ^ α) := by
    intro F _ A C hA
    refine Asymptotics.isBigO_principal.2 ⟨C, fun p hp => ?_⟩
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hA _ hp.1 _ hp.2
  -- ... and a function continuous on the compact `K` is bounded there.
  have hbdd : ∀ {F : Type} [NormedAddCommGroup F] (A : E₁ → F), ContinuousOn A K →
      IsBoundedUnder (· ≤ ·) (𝓟 (K ×ˢ K)) (fun p : E₁ × E₁ => ‖A p.1‖) ∧
      IsBoundedUnder (· ≤ ·) (𝓟 (K ×ˢ K)) (fun p : E₁ × E₁ => ‖A p.2‖) := by
    intro F _ A hA
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hA
    exact ⟨isBoundedUnder_of_eventually_le (eventually_principal.2 fun p hp => hB _ hp.1),
      isBoundedUnder_of_eventually_le (eventually_principal.2 fun p hp => hB _ hp.2)⟩
  have h0 : ∀ x y, ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
    intro x y
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
  -- `f` is `α`-Hölder on `K`: by hypothesis if `m = 0`, being `C¹` otherwise.
  obtain ⟨Cf, hCf⟩ : ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨C, hC⟩ := hfH K hK hKU
      exact ⟨C, fun x hx y hy => (h0 x y).symm.trans_le (hC x hx y hy)⟩
    · obtain ⟨C, hC⟩ := dohr_eb_holder_of_contDiffOn_succ E₁ E₂ 0 α f U hα hα1 hU
        (hf.of_le (by exact_mod_cast hm)) K hK hKU
      exact ⟨C, fun x hx y hy => (h0 x y).symm.trans_le (hC x hx y hy)⟩
  -- Step 2: Faà di Bruno, `Dᵐ(h ∘ f) = (D•h ∘ f).taylorComp D•f` on `U`.
  have hFdB : ∀ z ∈ U, iteratedFDeriv ℝ m (h ∘ f) z =
      (ftaylorSeries ℝ h (f z)).taylorComp (ftaylorSeries ℝ f z) m := fun z hz =>
    iteratedFDeriv_comp (hh.contDiffAt (hV.mem_nhds (hfUV hz))) (hf.contDiffAt (hU.mem_nhds hz))
      le_rfl
  have hcf : ∀ k ≤ m, ContinuousOn (iteratedFDeriv ℝ k f) K := fun k hk x hx =>
    ((hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
      (by exact_mod_cast hk)).continuousWithinAt
  -- Step 3: the Faà di Bruno sums at `x` and `y` differ by `O(‖x - y‖ ^ α)` on `K ×ˢ K`.
  have H : (fun p : E₁ × E₁ => (ftaylorSeries ℝ h (f p.1)).taylorComp (ftaylorSeries ℝ f p.1) m -
      (ftaylorSeries ℝ h (f p.2)).taylorComp (ftaylorSeries ℝ f p.2) m) =O[𝓟 (K ×ˢ K)]
      (fun p => ‖p.1 - p.2‖ ^ α) := by
    apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO <;> intro k hk
    · -- `Dᵏh ∘ f` is bounded on `K`.
      refine (hbdd (fun x => iteratedFDeriv ℝ k h (f x)) fun x hx => ?_).1
      exact ((hh.contDiffAt (hV.mem_nhds (hfUV (hKU hx)))).continuousAt_iteratedFDeriv
        (by exact_mod_cast hk)).comp_continuousWithinAt (hf.continuousOn.mono hKU x hx)
    · -- `Dᵏh ∘ f` is `α`-Hölder on `K`.
      have hcase : ContDiffOn ℝ (k + 1 : ℕ) h V ∨ (k = m ∧ ContDiffOn ℝ 1 f U) := by
        rcases hk.lt_or_eq with hlt | hkm
        · exact Or.inl (hh.of_le (by exact_mod_cast hlt))
        · rcases hdisj with h1 | h1 | h1
          · exact Or.inr ⟨hkm, hf.of_le (by exact_mod_cast h1)⟩
          · exact Or.inr ⟨hkm, h1⟩
          · rcases Nat.eq_zero_or_pos k with hk0 | hk0
            · left
              rw [hk0]
              simpa using h1
            · exact Or.inr ⟨hkm, hf.of_le (by rw [← hkm]; exact_mod_cast hk0)⟩
      rcases hcase with hk1 | ⟨hkm, hf1⟩
      · -- `Dᵏh` is Lipschitz on `f(K)` and `f` is `α`-Hölder on `K`.
        obtain ⟨L, hL⟩ := dohr_eb_holder_of_contDiffOn_succ E₂ E₃ k 1 h V one_pos le_rfl hV hk1
          (f '' K) hfK hfKV
        refine hconv (fun x => iteratedFDeriv ℝ k h (f x)) (|L| * Cf) fun x hx y hy => ?_
        calc ‖iteratedFDeriv ℝ k h (f x) - iteratedFDeriv ℝ k h (f y)‖
            ≤ L * ‖f x - f y‖ ^ (1 : ℝ) := hL _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy)
          _ ≤ |L| * ‖f x - f y‖ := by
              rw [Real.rpow_one]
              exact mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)
          _ ≤ |L| * (Cf * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left (hCf x hx y hy) (abs_nonneg L)
          _ = |L| * Cf * ‖x - y‖ ^ α := (mul_assoc _ _ _).symm
      · -- `k = m`: `Dᵐh` is `α`-Hölder on `f(K)` and `f` is Lipschitz on `K`.
        subst hkm
        obtain ⟨Ch, hCh⟩ := hhH (f '' K) hfK hfKV
        obtain ⟨Lf, hLf⟩ := dohr_eb_holder_of_contDiffOn_succ E₁ E₂ 0 1 f U one_pos le_rfl hU
          (by simpa using hf1) K hK hKU
        refine hconv (fun x => iteratedFDeriv ℝ k h (f x)) (|Ch| * |Lf| ^ α) fun x hx y hy => ?_
        have hfxy : ‖f x - f y‖ ≤ |Lf| * ‖x - y‖ := by
          have := hLf x hx y hy
          rw [h0, Real.rpow_one] at this
          exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self Lf) (norm_nonneg _))
        calc ‖iteratedFDeriv ℝ k h (f x) - iteratedFDeriv ℝ k h (f y)‖
            ≤ Ch * ‖f x - f y‖ ^ α := hCh _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy)
          _ ≤ |Ch| * ‖f x - f y‖ ^ α :=
              mul_le_mul_of_nonneg_right (le_abs_self Ch) (Real.rpow_nonneg (norm_nonneg _) _)
          _ ≤ |Ch| * (|Lf| * ‖x - y‖) ^ α :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hfxy hα.le)
                (abs_nonneg Ch)
          _ = |Ch| * |Lf| ^ α * ‖x - y‖ ^ α := by
              rw [Real.mul_rpow (abs_nonneg Lf) (norm_nonneg _), mul_assoc]
    · -- `Dᵏf` is bounded on `K` (at `x` and at `y`).
      exact (hbdd _ (hcf k hk)).1
    · exact (hbdd _ (hcf k hk)).2
    · -- `Dᵏf` is `α`-Hölder on `K`: as a `C¹` map if `k < m`, by hypothesis if `k = m`.
      rcases hk.lt_or_eq with hlt | hkm
      · obtain ⟨C, hC⟩ := dohr_eb_holder_of_contDiffOn_succ E₁ E₂ k α f U hα hα1 hU
          (hf.of_le (by exact_mod_cast hlt)) K hK hKU
        exact hconv (iteratedFDeriv ℝ k f) C hC
      · subst hkm
        obtain ⟨C, hC⟩ := hfH K hK hKU
        exact hconv (iteratedFDeriv ℝ k f) C hC
  -- Step 4: `Asymptotics.isBigO_principal` gives one constant on `K ×ˢ K`.
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_principal.1 H
  refine ⟨c, fun x hx y hy => ?_⟩
  rw [hFdB x (hKU hx), hFdB y (hKU hy)]
  refine (hc (x, y) ⟨hx, hy⟩).trans_eq ?_
  congr 1
  exact Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): chain rule and Schwarz symmetry.**
If `Ψ : L(ℝⁿ, ℝ^ℓ) → ℝ` is `C²` and `u` is `C²` on the open set `U ⊆ ℝⁿ`, then for every direction
`e` and every `y ∈ U`, `D(DΨ ∘ Du)(y) e = D²Ψ(Du(y))[Dv_e(y)]`, where `v_e(z) = Du(z) e`.
Proof: the chain rule gives `D(DΨ ∘ Du)(y) e = D²Ψ(Du(y))[D²u(y) e]`, and
`Dv_e(y) w = D²u(y)[w][e]`; these agree because `D²u(y)` is symmetric (Schwarz).  Given `ε > 0`,
pick `δ > 0` with `B̆_δ(y) ⊆ U` and `‖D²u(z) − D²u(y)‖ < ε` on `B̆_δ(y)`.  For
`h = δ/(2(|v| + |w| + 1))` the mean value inequality for `z ↦ u(z + hw) − u(z)` on `[y, y + hv]`
bounds the second difference `Δ = u(y + hv + hw) − u(y + hv) − u(y + hw) + u(y)` by
`|Δ − h² D²u(y)[w][v]| ≤ ε h² |v| |w|`, and swapping `v` and `w` gives
`|Δ − h² D²u(y)[v][w]| ≤ ε h² |v| |w|`.  Hence `|D²u(y)[v][w] − D²u(y)[w][v]| ≤ 2ε |v| |w|` for
every `ε > 0`. -/
theorem dohr_eb_ehs_del_chain_symm : ∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ∀ (e y : Rn n), y ∈ U → fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) y e = fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y) (fderiv ℝ (fun z => fderiv ℝ u z e) y) := by
  intro n ℓ Ψ U u hU hΨ hu e y hy
  have hUy : U ∈ 𝓝 y := hU.mem_nhds hy
  -- Step 1: `u` and `Du` are differentiable on `U`, and `D²u` is continuous on `U`.
  have hDu : ContDiffOn ℝ 1 (fun z => fderiv ℝ u z) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hdu : ∀ z ∈ U, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn two_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hdDu : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ u) z := fun z hz =>
    (hDu.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hDuy : DifferentiableAt ℝ (fderiv ℝ u) y := hdDu y hy
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) U :=
    hDu.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Step 2: `DΨ` is `C¹`, hence differentiable at `Du(y)`.
  have hDΨ : ContDiff ℝ 1 (fderiv ℝ Ψ) := hΨ.fderiv_right (by norm_num)
  have hDΨd : DifferentiableAt ℝ (fderiv ℝ Ψ) (fderiv ℝ u y) :=
    hDΨ.differentiable one_ne_zero _
  -- Step 3: chain rule, `D(DΨ ∘ Du)(y) = D²Ψ(Du(y)) ∘ D²u(y)`.
  have h1 : fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) y =
      (fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u y)).comp (fderiv ℝ (fderiv ℝ u) y) :=
    fderiv_fun_comp (𝕜 := ℝ) (x := y) (g := fderiv ℝ Ψ) (f := fun z => fderiv ℝ u z)
      hDΨd hDuy
  -- Step 4: `Dv_e(y) w = D²u(y)[w][e]`.
  have h2 : fderiv ℝ (fun z => fderiv ℝ u z e) y = (fderiv ℝ (fderiv ℝ u) y).flip e := by
    rw [fderiv_clm_apply hDuy (differentiableAt_const e)]
    simp
  -- Step 5: Schwarz symmetry of `A = D²u(y)`, via the mean value inequality for `Du`.
  have hsymm : ∀ v w : Rn n,
      fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v := by
    intro v w
    set A := fderiv ℝ (fderiv ℝ u) y
    have hbound : ∀ ε > 0, ‖A v w - A w v‖ ≤ 2 * ε * (‖v‖ * ‖w‖) := by
      intro ε hε
      -- `δ = min r δ'`: `B̆_δ(y) ⊆ U` and `‖D²u(z) − A‖ < ε` on `B̆_δ(y)`
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU y hy
      obtain ⟨δ', hδ', hδ'A⟩ := (NormedAddCommGroup.tendsto_nhds_nhds (E := Rn n)
        (F := Rn n →L[ℝ] Rn n →L[ℝ] Rn ℓ)).mp (hD2.continuousAt hUy) ε hε
      have hδ : 0 < min r δ' := lt_min hr hδ'
      have hball : ball y (min r δ') ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hrU
      -- mean value inequality for `Du` on `B̆_δ(y)` with the fixed linear map `A`
      have hmvt : ∀ a ∈ ball y (min r δ'), ∀ b ∈ ball y (min r δ'),
          ‖fderiv ℝ u b - fderiv ℝ u a - A (b - a)‖ ≤ ε * ‖b - a‖ := by
        intro a ha b hb
        refine (convex_ball y (min r δ')).norm_image_sub_le_of_norm_fderiv_le'
          (fun z hz => hdDu z (hball hz)) (fun z hz => ?_) ha hb
        have hzy : ‖z - y‖ < δ' := by
          rw [← dist_eq_norm]
          exact lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)
        exact (hδ'A z hzy).le
      -- second difference estimate: `z ↦ u(z + h b) − u(z)` on the segment `[y, y + h a]`
      have hsecond : ∀ (h : ℝ) (a b : Rn n), |h| * (‖a‖ + ‖b‖) < min r δ' →
          ‖(u (y + h • a + h • b) - u (y + h • a) - (u (y + h • b) - u y)) - (h ^ 2) • A b a‖
            ≤ ε * (|h| * ‖b‖) * (|h| * ‖a‖) := by
        intro h a b hab
        have hseg : ∀ z ∈ segment ℝ y (y + h • a),
            z ∈ ball y (min r δ') ∧ z + h • b ∈ ball y (min r δ') := by
          intro z hz
          have hz' : z ∈ closedBall y (|h| * ‖a‖) := by
            refine (convex_closedBall y _).segment_subset
              (mem_closedBall_self (by positivity)) ?_ hz
            rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          rw [mem_closedBall, dist_eq_norm] at hz'
          have hb0 : 0 ≤ |h| * ‖b‖ := by positivity
          constructor
          · rw [mem_ball, dist_eq_norm]
            linarith
          · rw [mem_ball, dist_eq_norm]
            calc ‖z + h • b - y‖ = ‖(z - y) + h • b‖ := by congr 1; abel
              _ ≤ ‖z - y‖ + ‖h • b‖ := norm_add_le _ _
              _ ≤ |h| * ‖a‖ + |h| * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs]; linarith
              _ = |h| * (‖a‖ + ‖b‖) := by ring
              _ < min r δ' := hab
        have hφd : ∀ z ∈ segment ℝ y (y + h • a),
            DifferentiableAt ℝ (fun x => u (x + h • b) - u x) z := fun z hz =>
          ((differentiableAt_comp_add_right (h • b)).mpr (hdu _ (hball (hseg z hz).2))).sub
            (hdu z (hball (hseg z hz).1))
        have hφ := (convex_segment y (y + h • a)).norm_image_sub_le_of_norm_fderiv_le'
          (φ := h • A b) (C := ε * (|h| * ‖b‖)) hφd (fun z hz => ?_)
          (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
        · simp only [add_sub_cancel_left, smul_apply, map_smul, smul_smul,
            norm_smul, Real.norm_eq_abs] at hφ
          rw [pow_two]
          convert hφ using 2
        · rw [fderiv_fun_sub ((differentiableAt_comp_add_right (h • b)).mpr
            (hdu _ (hball (hseg z hz).2))) (hdu z (hball (hseg z hz).1)), fderiv_comp_add_right]
          have := hmvt z (hseg z hz).1 (z + h • b) (hseg z hz).2
          rwa [add_sub_cancel_left, map_smul, norm_smul, Real.norm_eq_abs] at this
      -- a small step `h > 0`; compare the estimates for `(v, w)` and `(w, v)`
      set h : ℝ := min r δ' / (2 * (‖v‖ + ‖w‖ + 1)) with hh
      have hvw : 0 ≤ ‖v‖ + ‖w‖ := by positivity
      have hpos : 0 < h := by positivity
      have hsmall : ∀ a b : Rn n, ‖a‖ + ‖b‖ = ‖v‖ + ‖w‖ → |h| * (‖a‖ + ‖b‖) < min r δ' := by
        intro a b hab
        rw [hab, abs_of_pos hpos, hh, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have e1 := hsecond h v w (hsmall v w rfl)
      have e2 := hsecond h w v (hsmall w v (add_comm _ _))
      rw [add_right_comm y (h • w) (h • v)] at e2
      have hdiff : (h ^ 2) • (A v w - A w v) =
          ((u (y + h • v + h • w) - u (y + h • v) - (u (y + h • w) - u y)) - (h ^ 2) • A w v) -
          ((u (y + h • v + h • w) - u (y + h • w) - (u (y + h • v) - u y)) - (h ^ 2) • A v w) := by
        rw [smul_sub]; abel
      have hle : h ^ 2 * ‖A v w - A w v‖ ≤ h ^ 2 * (2 * ε * (‖v‖ * ‖w‖)) := by
        have := norm_sub_le
          ((u (y + h • v + h • w) - u (y + h • v) - (u (y + h • w) - u y)) - (h ^ 2) • A w v)
          ((u (y + h • v + h • w) - u (y + h • w) - (u (y + h • v) - u y)) - (h ^ 2) • A v w)
        rw [← hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
        rw [abs_of_pos hpos] at e1 e2
        nlinarith
      exact le_of_mul_le_mul_left hle (by positivity)
    -- let `ε → 0`
    refine eq_of_forall_dist_le fun ε hε => ?_
    rw [dist_eq_norm]
    have hK : 0 ≤ ‖v‖ * ‖w‖ := by positivity
    calc ‖A v w - A w v‖ ≤ 2 * (ε / (2 * (‖v‖ * ‖w‖ + 1))) * (‖v‖ * ‖w‖) :=
          hbound _ (by positivity)
      _ = ε * ((‖v‖ * ‖w‖) / (‖v‖ * ‖w‖ + 1)) := by field_simp
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one (by positivity)]
          linarith
      _ = ε := mul_one ε
  -- Step 6: `Dv_e(y) = D²u(y) e`; substitute into the chain rule.
  have h3 : (fderiv ℝ (fderiv ℝ u) y).flip e = fderiv ℝ (fderiv ℝ u) y e := by
    ext w : 1
    rw [ContinuousLinearMap.flip_apply]
    exact hsymm w e
  rw [h1, h2, h3]
  rfl
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap, differentiated Euler–Lagrange
equation): uniform convergence of difference quotients.**
If `f : ℝⁿ → E` (`E` any real normed space) is `C¹` on an open `U` and `K ⊆ U` is compact, then for
every direction `e` the difference quotients `h⁻¹ (f(x + h e) − f(x))` converge to `Df(x) e`
uniformly on `K` as `h → 0`, `h ≠ 0`.
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Df` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Df(w) − Df(x)‖ < η/(‖e‖ + 1)` whenever
`w, x ∈ K_ε` and `‖w − x‖ < θ`.  For `0 < |h| < min(ε, θ)/(‖e‖ + 1)` and `x ∈ K`, the segment
`[x, x + h e]` lies in `B_{‖h e‖}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Df(x)` gives `‖f(x + h e) − f(x) − Df(x)(h e)‖ ≤ η |h| ‖e‖/(‖e‖ + 1)`; dividing by `|h|`,
`‖Df(x) e − h⁻¹ (f(x + h e) − f(x))‖ ≤ η ‖e‖/(‖e‖ + 1) < η`. -/
theorem dohr_eb_ehs_del_diffquot_uniform : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Rn n → E) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (h : ℝ) (x : Rn n) => h⁻¹ • (f (x + h • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K := by
  intro n E _ _ f U K e hU hf hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `f` is differentiable on `U` and `Df` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- Step 3: given `η > 0`, choose `θ` and restrict to `0 < |d| < min ε θ / (‖e‖ + 1)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  -- Step 4: the segment `[x, x + d • e]` lies in `closedBall x ‖d • e‖ ⊆ K_ε ⊆ U`.
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  -- Step 5: the mean value inequality with the fixed linear map `Df(x)`.
  have hmvt : ‖f (x + d • e) - f x - fderiv ℝ f x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  -- Step 6: divide by `d ≠ 0`.
  rw [dist_eq_norm]
  have hrw : fderiv ℝ f x e - d⁻¹ • (f (x + d • e) - f x) =
      -(d⁻¹ • (f (x + d • e) - f x - fderiv ℝ f x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (f (x + d • e) - f x) (d • fderiv ℝ f x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖f (x + d • e) - f x - fderiv ℝ f x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- Currying step of the proof that `f` is `C^{m+1,α}` iff `Df` is `C^{m,α}` (elliptic bootstrap
for Simon 7.1): on an open `U`, `f` is `C^{m+1}` with `D^{m+1}f` locally `α`-Hölder iff `f` is `C¹`,
`Df` is `C^m` and `D^m(Df)` is locally `α`-Hölder, with the same constants.  Indeed
`D^{m+1}f(x) = Φ (D^m(Df)(x))` for the currying linear isometry `Φ`, and `C^{m+1}` on an open set
means differentiable with `C^m` derivative. -/
theorem dohr_eb_hsif_succ_iff_curry : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (α : ℝ) (f : Rn n → E) (U : Set (Rn n)), IsOpen U → ((ContDiffOn ℝ (m + 1 : ℕ) f U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔ (ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ m (fderiv ℝ f) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ ≤ C * ‖x - y‖ ^ α)) := by
  intro n E _ _ m α f U hU
  -- Steps 1–2: `D^{m+1}f(x) = Φ (D^m(Df)(x))` with `Φ` a linear isometry, so the two Hölder
  -- differences have equal norms at every pair of points.
  have hnorm : ∀ x y : Rn n,
      ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ =
        ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ := by
    intro x y
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
  -- Step 3: hence the Hölder clauses coincide, with the same constant on each compact `K`.
  have hhol : (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔
      (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ ≤
        C * ‖x - y‖ ^ α) := by
    simp only [hnorm]
  -- Step 4: on the open set `U`, `f` is `C^{m+1}` iff it is differentiable with `C^m` derivative
  -- (the analyticity clause is vacuous since `m` is finite).
  have hsucc := contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := f) (n := (m : WithTop ℕ∞)) hU
  -- Steps 5–6: the regularity parts agree.
  have hreg : ContDiffOn ℝ (m + 1 : ℕ) f U ↔
      ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ m (fderiv ℝ f) U := by
    push_cast
    refine ⟨fun h => ⟨h.of_le le_add_self, (hsucc.1 h).2.2⟩, fun h => ?_⟩
    exact hsucc.2 ⟨h.1.differentiableOn one_ne_zero, by simp, h.2⟩
  -- Step 7: combine.
  rw [hreg, hhol, and_assoc]

/-- Columns of an operator-valued map (step 1 of the proof that `f` is `C^{m+1,α}` iff `Df` is
`C^{m,α}`, in the elliptic bootstrap for Simon 7.1): `g : ℝⁿ → L(ℝⁿ, E)` is `C^m` on a set `U` iff
every column `g_k = g(·) e_k` is.  Indeed `g_k = ev_k ∘ g` for the evaluation `ev_k T = T e_k`, and
conversely `g = ∑_k ι_k ∘ g_k` for the continuous linear reconstruction `ι_k w = (h ↦ h_k • w)`. -/
theorem dohr_eb_hsif_contDiffOn_clm_iff_columns : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (g : Rn n → (Rn n →L[ℝ] E)) (U : Set (Rn n)), ContDiffOn ℝ m g U ↔ ∀ k : Fin n, ContDiffOn ℝ m (fun x => g x (EuclideanSpace.single k (1 : ℝ))) U := by
  intro n E _ _ m g U
  -- Step 1: the reconstruction maps `ι k : w ↦ (h ↦ h_k • w)` are continuous linear.
  let ι : Fin n → E →L[ℝ] (Rn n →L[ℝ] E) := fun k =>
    ContinuousLinearMap.smulRightL ℝ (Rn n) E (EuclideanSpace.proj k)
  -- Step 2: the reconstruction `g = ∑ k, ι k ∘ g_k`, from `h = ∑ k, h_k • e_k`.
  have hrec : g = fun x => ∑ k, ι k (g x (EuclideanSpace.single k (1 : ℝ))) := by
    funext x
    ext h
    have hh : ∑ k, h k • EuclideanSpace.single k (1 : ℝ) = h := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h
    conv_lhs => rw [← hh]
    simp [ι, map_sum, map_smul]
  refine ⟨fun hg k => ?_, fun hk => ?_⟩
  -- Step 3: each column `g_k = ev_k ∘ g` is `C^m` on `U`.
  · exact hg.clm_apply contDiffOn_const
  -- Step 4: `g = ∑ k, ι k ∘ g_k` is a finite sum of `C^m` maps on `U`.
  · rw [hrec]
    exact ContDiffOn.sum fun k _ => (ι k).contDiff.comp_contDiffOn (hk k)
/-- Constants `M_B`, `L_B` for the Hessian of the integrand (step 1 of the `C^{2,α}` regularity of
`C^{1,α}` weak solutions of uniformly convex Euler–Lagrange systems, in the elliptic bootstrap for
Simon 7.1): if `Ψ : L(ℝⁿ, ℝ^ℓ) → ℝ` is `C³` and `B(P) = D²Ψ(P)`, then for `‖P‖, ‖P'‖ ≤ ε`
`|B(P)[Q][Q']| ≤ M_B ‖Q‖ ‖Q'‖` and `|B(P)[Q][Q'] - B(P')[Q][Q']| ≤ L_B ‖P - P'‖ ‖Q‖ ‖Q'‖`.
`B` is `C¹` and the closed ball `‖P‖ ≤ ε` is compact and convex, so `‖B‖` is bounded there and `B`
is Lipschitz there; `|β[Q][Q']| ≤ ‖β‖ ‖Q‖ ‖Q'‖` for a bilinear form `β` gives both estimates. -/
theorem dohr_eb_elc2_hessian_bounds : ∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ), ContDiff ℝ 3 Ψ → ∀ ε : ℝ, ∃ MB LB : ℝ, 0 ≤ MB ∧ 0 ≤ LB ∧ (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q'| ≤ MB * ‖Q‖ * ‖Q'‖) ∧ ∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ‖P'‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q' - fderiv ℝ (fderiv ℝ Ψ) P' Q Q'| ≤ LB * ‖P - P'‖ * ‖Q‖ * ‖Q'‖ := by
  -- Argue for an abstract finite-dimensional space `X = L(ℝⁿ, ℝ^ℓ)`: this keeps the instances on
  -- the bilinear forms `X →L[ℝ] X →L[ℝ] ℝ` within the default instance synthesis depth.
  suffices H : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
      (Ψ : X → ℝ), ContDiff ℝ 3 Ψ → ∀ ε : ℝ, ∃ MB LB : ℝ, 0 ≤ MB ∧ 0 ≤ LB ∧
        (∀ P : X, ‖P‖ ≤ ε → ∀ Q Q' : X, |fderiv ℝ (fderiv ℝ Ψ) P Q Q'| ≤ MB * ‖Q‖ * ‖Q'‖) ∧
        ∀ P P' : X, ‖P‖ ≤ ε → ‖P'‖ ≤ ε → ∀ Q Q' : X,
          |fderiv ℝ (fderiv ℝ Ψ) P Q Q' - fderiv ℝ (fderiv ℝ Ψ) P' Q Q'| ≤
            LB * ‖P - P'‖ * ‖Q‖ * ‖Q'‖ from
    fun n ℓ => H (Rn n →L[ℝ] Rn ℓ)
  intro X _ _ _ Ψ hΨ ε
  -- Step 1: `B = D²Ψ` is `C¹`.
  have hB : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Ψ)) :=
    (hΨ.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  -- Step 2: the closed ball `‖P‖ ≤ ε` is compact (finite dimension) and convex.
  have hK : IsCompact (closedBall (0 : X) ε) := isCompact_closedBall _ _
  -- Step 3: `‖B‖ ≤ M` on the ball.
  obtain ⟨M, hM⟩ :=
    hK.exists_bound_of_continuousOn (E := X →L[ℝ] X →L[ℝ] ℝ) hB.continuous.continuousOn
  -- Step 4: `B` is `L`-Lipschitz on the ball.
  obtain ⟨L, hL⟩ := hB.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _) hK
  refine ⟨max M 0, L, le_max_right _ _, L.coe_nonneg, ?_, ?_⟩
  -- Step 3, bound (i): `|B(P)[Q][Q']| ≤ ‖B(P)‖ ‖Q‖ ‖Q'‖`.
  · intro P hP Q Q'
    have h := (fderiv ℝ (fderiv ℝ Ψ) P).le_opNorm₂ Q Q'
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    gcongr
    exact (hM P (mem_closedBall_zero_iff.2 hP)).trans (le_max_left _ _)
  -- Step 5, bound (ii): the same estimate for the bilinear form `B(P) - B(P')`.
  · intro P P' hP hP' Q Q'
    have h := (fderiv ℝ (fderiv ℝ Ψ) P - fderiv ℝ (fderiv ℝ Ψ) P').le_opNorm₂ Q Q'
    rw [Real.norm_eq_abs] at h
    simp only [sub_apply] at h
    refine h.trans ?_
    gcongr
    exact hL.norm_sub_le (mem_closedBall_zero_iff.2 hP) (mem_closedBall_zero_iff.2 hP')

/-- **Averaged Hessian coefficient** (Steps 4–5 of the `C^{2,α}` regularity proof for uniformly
convex Euler–Lagrange systems, in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second
assertion).  Let `Ψ` be `C²` on `L = L(ℝⁿ, ℝ^ℓ)` and `B = D²Ψ`.  Assume that on the closed `ε`-ball
`B` satisfies `λ|Q|² ≤ B(P)[Q][Q]`, `|B(P)[Q][Q']| ≤ M_B|Q||Q'|` and a Lipschitz bound with constant
`L_B ≥ 0`, and that `P₀, P₁ : ℝⁿ → L` take values in that ball and are `(H, α)`-Hölder on `S`.  Then
`a(x)[P][Q] = ∫₀¹ B(P₀(x) + t(P₁(x) - P₀(x)))[P][Q] dt` defines continuous bilinear forms that are
coercive, bounded by `M_B` and `L_B H`-Hölder in `x` on `S`.
Proof: `P_t(x) = (1 - t)P₀(x) + tP₁(x)` stays in the `ε`-ball, so the bounds on `B` hold for each
`t ∈ [0, 1]` and pass to the integral.  For the Hölder bound, `‖P_t(x) - P_t(y)‖ ≤ H‖x - y‖^α` as a
convex combination of the two Hölder bounds. -/
theorem Submission.dohr_eb_elc2_averaged_hessian : ∀ (n ℓ : ℕ) (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (lam ε MB LB H α : ℝ) (S : Set (Rn n)) (P₀ P₁ : Rn n → Rn n →L[ℝ] Rn ℓ), ContDiff ℝ 2 Ψ → 0 ≤ LB → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q : Rn n →L[ℝ] Rn ℓ, lam * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ Ψ) P Q Q) → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q'| ≤ MB * ‖Q‖ * ‖Q'‖) → (∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ‖P'‖ ≤ ε → ∀ Q Q' : Rn n →L[ℝ] Rn ℓ, |fderiv ℝ (fderiv ℝ Ψ) P Q Q' - fderiv ℝ (fderiv ℝ Ψ) P' Q Q'| ≤ LB * ‖P - P'‖ * ‖Q‖ * ‖Q'‖) → (∀ x ∈ S, ‖P₀ x‖ ≤ ε) → (∀ x ∈ S, ‖P₁ x‖ ≤ ε) → (∀ x ∈ S, ∀ y ∈ S, ‖P₀ x - P₀ y‖ ≤ H * ‖x - y‖ ^ α) → (∀ x ∈ S, ∀ y ∈ S, ‖P₁ x - P₁ y‖ ≤ H * ‖x - y‖ ^ α) → ∃ a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P Q : Rn n →L[ℝ] Rn ℓ), a x P Q = ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ) (P₀ x + t • (P₁ x - P₀ x)) P Q) ∧ (∀ x ∈ S, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) ∧ (∀ x ∈ S, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ MB * ‖P‖ * ‖Q‖) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ LB * H * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
  intro n ℓ Ψ lam ε MB LB H α S P₀ P₁ hΨ hLB hLeg hMB hLip hP₀ hP₁ hH₀ hH₁
  -- Step 1: `B = D²Ψ` is continuous since `Ψ` is `C²`, so each scalar integrand
  -- `t ↦ B(P_t(x))[P][Q]` is continuous, hence interval integrable on `[0, 1]`.
  have hB := (hΨ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  set B := fderiv ℝ (fderiv ℝ Ψ)
  set Pt : Rn n → ℝ → (Rn n →L[ℝ] Rn ℓ) := fun x t => P₀ x + t • (P₁ x - P₀ x) with hPt
  have hint : ∀ (x : Rn n) (P Q : Rn n →L[ℝ] Rn ℓ),
      IntervalIntegrable (fun t : ℝ => B (Pt x t) P Q) volume 0 1 := fun x P Q =>
    Continuous.intervalIntegrable (by simp only [hPt]; fun_prop) 0 1
  -- Step 2: for fixed `x`, `(P, Q) ↦ ∫₀¹ B(P_t(x))[P][Q] dt` is bilinear; it is continuous
  -- because `L(ℝⁿ, ℝ^ℓ)` is finite-dimensional.
  let φ : Rn n → (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) →ₗ[ℝ] ℝ := fun x P =>
    { toFun := fun Q => ∫ t in (0 : ℝ)..1, B (Pt x t) P Q
      map_add' := fun Q Q' => by
        simp only [map_add]
        exact intervalIntegral.integral_add (hint x P Q) (hint x P Q')
      map_smul' := fun c Q => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact intervalIntegral.integral_const_mul c _ }
  let ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →ₗ[ℝ] ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) := fun x =>
    { toFun := fun P => LinearMap.toContinuousLinearMap (φ x P)
      map_add' := fun P P' => by
        ext Q
        change (∫ t in (0 : ℝ)..1, B (Pt x t) (P + P') Q)
          = (∫ t in (0 : ℝ)..1, B (Pt x t) P Q) + ∫ t in (0 : ℝ)..1, B (Pt x t) P' Q
        simp only [map_add, add_apply]
        exact intervalIntegral.integral_add (hint x P Q) (hint x P' Q)
      map_smul' := fun c P => by
        ext Q
        change (∫ t in (0 : ℝ)..1, B (Pt x t) (c • P) Q) = c * ∫ t in (0 : ℝ)..1, B (Pt x t) P Q
        simp only [map_smul, smul_apply, smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _ }
  -- Step 3: for `x ∈ S` and `t ∈ [0, 1]`, `P_t(x)` is a convex combination of `P₀(x)` and `P₁(x)`,
  -- so it stays in the closed `ε`-ball.
  have hball : ∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, ‖Pt x t‖ ≤ ε := by
    intro x hx t ht
    have : Pt x t = (1 - t) • P₀ x + t • P₁ x := by simp only [hPt]; module
    rw [this]
    calc ‖(1 - t) • P₀ x + t • P₁ x‖ ≤ ‖(1 - t) • P₀ x‖ + ‖t • P₁ x‖ := norm_add_le _ _
      _ = (1 - t) * ‖P₀ x‖ + t * ‖P₁ x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht.1]
      _ ≤ (1 - t) * ε + t * ε := by
          gcongr
          · linarith [ht.2]
          · exact hP₀ x hx
          · exact ht.1
          · exact hP₁ x hx
      _ = ε := by ring
  -- `a(x)` is `ψ x` as a continuous linear map.  The type arguments are explicit so that the
  -- instances on `L(L, ℝ)` are synthesized directly rather than during unification.
  refine ⟨fun x => LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
    (F' := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ψ x), ?_, ?_, ?_, ?_⟩
  -- The formula holds by definition.
  · intro x P Q
    rfl
  -- Step 4: coercivity, by monotonicity of the integral.
  · intro x hx P
    change lam * ‖P‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, B (Pt x t) P P
    have := intervalIntegral.integral_mono_on (a := 0) (b := 1) zero_le_one
      intervalIntegrable_const (hint x P P) (fun t ht => hLeg _ (hball x hx t ht) P)
    simpa using this
  -- Step 5: the bound, from the pointwise bound on `(0, 1]`.
  · intro x hx P Q
    change |∫ t in (0 : ℝ)..1, B (Pt x t) P Q| ≤ MB * ‖P‖ * ‖Q‖
    rw [← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := MB * ‖P‖ * ‖Q‖) (f := fun t => B (Pt x t) P Q) (by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        rw [Real.norm_eq_abs]
        exact hMB _ (hball x hx t ⟨ht.1.le, ht.2⟩) P Q)
    simpa using this
  -- Step 6: Hölder continuity, from `‖P_t(x) - P_t(y)‖ ≤ H‖x - y‖^α` and the Lipschitz bound on `B`.
  · intro x hx y hy P Q
    change |(∫ t in (0 : ℝ)..1, B (Pt x t) P Q) - ∫ t in (0 : ℝ)..1, B (Pt y t) P Q| ≤ _
    rw [← intervalIntegral.integral_sub (hint x P Q) (hint y P Q), ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := LB * H * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) (f := fun t => B (Pt x t) P Q - B (Pt y t) P Q) (by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        rw [Real.norm_eq_abs]
        have hdiff : ‖Pt x t - Pt y t‖ ≤ H * ‖x - y‖ ^ α := by
          have : Pt x t - Pt y t = (1 - t) • (P₀ x - P₀ y) + t • (P₁ x - P₁ y) := by
            simp only [hPt]; module
          rw [this]
          calc ‖(1 - t) • (P₀ x - P₀ y) + t • (P₁ x - P₁ y)‖
              ≤ ‖(1 - t) • (P₀ x - P₀ y)‖ + ‖t • (P₁ x - P₁ y)‖ := norm_add_le _ _
            _ = (1 - t) * ‖P₀ x - P₀ y‖ + t * ‖P₁ x - P₁ y‖ := by
                rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith [ht'.2]), abs_of_nonneg ht'.1]
            _ ≤ (1 - t) * (H * ‖x - y‖ ^ α) + t * (H * ‖x - y‖ ^ α) := by
                gcongr
                · linarith [ht'.2]
                · exact hH₀ x hx y hy
                · exact ht'.1
                · exact hH₁ x hx y hy
            _ = H * ‖x - y‖ ^ α := by ring
        calc |B (Pt x t) P Q - B (Pt y t) P Q| ≤ LB * ‖Pt x t - Pt y t‖ * ‖P‖ * ‖Q‖ :=
              hLip _ _ (hball x hx t ht') (hball y hy t ht') P Q
          _ ≤ LB * (H * ‖x - y‖ ^ α) * ‖P‖ * ‖Q‖ := by gcongr
          _ = LB * H * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by ring)
    simpa using this
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
/-- Elementary properties of the difference quotient `w = d⁻¹ (u(· + d e) - u)` of a `C¹` map `u`
whose derivative is bounded by `ε` and `α`-Hölder with constant `H` on a set `K ⊆ U` containing the
segments `x + [0, 1] d e` (`x ∈ V`): `w` is `C¹` on `V`, `Dw = d⁻¹ (Du(· + d e) - Du)` on `V`,
`‖w‖ ≤ ε ‖e‖` on `V` (mean value inequality along the segment), and `Dw` is `α`-Hölder on `V`
with constant `2 |d|⁻¹ H`. -/
theorem dohr_eb_elc2_dq_basic : ∀ (n ℓ : ℕ) (u : Rn n → Rn ℓ) (U V K : Set (Rn n)) (e : Rn n) (d ε H α : ℝ), IsOpen U → ContDiffOn ℝ 1 u U → K ⊆ U → d ≠ 0 → (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ K) → (∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ ε) → (∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ H * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 (fun z => d⁻¹ • (u (z + d • e) - u z)) V ∧ (∀ x ∈ V, fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x = d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) ∧ (∀ x ∈ V, ‖d⁻¹ • (u (x + d • e) - u x)‖ ≤ ε * ‖e‖) ∧ ∀ x ∈ V, ∀ y ∈ V, ‖fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x - fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) y‖ ≤ 2 * |d|⁻¹ * H * ‖x - y‖ ^ α := by
  intro n ℓ u U V K e d ε H α hU hu hKU hd hseg hε hH
  have hx0 : ∀ x ∈ V, x ∈ K := fun x hx => by simpa using hseg x hx 0 (by simp)
  have hx1 : ∀ x ∈ V, x + d • e ∈ K := fun x hx => by simpa using hseg x hx 1 (by simp)
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ u y := fun y hy =>
    (hu.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hD : ∀ x ∈ V, fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x =
      d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x) := by
    intro x hx
    have h1 : DifferentiableAt ℝ (fun z => u (z + d • e)) x := by
      have := hdiff _ (hKU (hx1 x hx))
      exact this.comp x (differentiableAt_id.add_const _)
    have h2 := hdiff x (hKU (hx0 x hx))
    have ha : HasFDerivAt (fun z => u (z + d • e)) (fderiv ℝ u (x + d • e)) x := by
      have := (hdiff _ (hKU (hx1 x hx))).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))
      simp only [ContinuousLinearMap.comp_id] at this
      exact this
    exact ((ha.sub h2.hasFDerivAt).const_smul d⁻¹).fderiv
  refine ⟨?_, hD, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ 1 (fun z => u (z + d • e)) V :=
      hu.comp (by fun_prop) (fun x hx => hKU (hx1 x hx))
    have h2 : ContDiffOn ℝ 1 u V := hu.mono (fun x hx => hKU (hx0 x hx))
    exact (h1.sub h2).const_smul d⁻¹
  · intro x hx
    have hmv : ‖u (x + d • e) - u x‖ ≤ ε * (|d| * ‖e‖) := by
      have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t : ℝ => u (x + (t * d) • e))
        (f' := fun t => fderiv ℝ u (x + (t * d) • e) (d • e)) (C := ε * (|d| * ‖e‖))
        (fun t ht => by
          have hp : x + (t * d) • e ∈ U := hKU (hseg x hx t ⟨ht.1, ht.2⟩)
          have hda := (hdiff _ hp).hasFDerivAt
          have hl : HasDerivAt (fun t : ℝ => x + (t * d) • e) (d • e) t := by
            have := ((hasDerivAt_id t).mul_const d).smul_const e
            simpa using this.const_add x
          exact (hda.comp_hasDerivAt t hl).hasDerivWithinAt)
        (fun t ht => by
          have hp : x + (t * d) • e ∈ K := hseg x hx t ⟨ht.1, ht.2.le⟩
          calc ‖fderiv ℝ u (x + (t * d) • e) (d • e)‖ ≤ ‖fderiv ℝ u (x + (t * d) • e)‖ * ‖d • e‖ :=
                (fderiv ℝ u _).le_opNorm _
            _ ≤ ε * ‖d • e‖ := by gcongr; exact hε _ hp
            _ = ε * (|d| * ‖e‖) := by rw [norm_smul, Real.norm_eq_abs])
      simpa using this
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have hd' : 0 < |d| := abs_pos.mpr hd
    calc |d|⁻¹ * ‖u (x + d • e) - u x‖ ≤ |d|⁻¹ * (ε * (|d| * ‖e‖)) := by gcongr
      _ = ε * ‖e‖ := by field_simp
  · intro x hx y hy
    rw [hD x hx, hD y hy]
    have hsm : d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x) - d⁻¹ • (fderiv ℝ u (y + d • e) - fderiv ℝ u y)
        = d⁻¹ • ((fderiv ℝ u (x + d • e) - fderiv ℝ u x) - (fderiv ℝ u (y + d • e) - fderiv ℝ u y)) :=
      (smul_sub _ _ _).symm
    rw [hsm, norm_smul, norm_inv, Real.norm_eq_abs]
    have h1 := hH _ (hx1 x hx) _ (hx1 y hy)
    have h2 := hH _ (hx0 x hx) _ (hx0 y hy)
    have h3 : x + d • e - (y + d • e) = x - y := by abel
    rw [h3] at h1
    have : ‖fderiv ℝ u (x + d • e) - fderiv ℝ u x - (fderiv ℝ u (y + d • e) - fderiv ℝ u y)‖ ≤
        2 * H * ‖x - y‖ ^ α := by
      calc _ = ‖(fderiv ℝ u (x + d • e) - fderiv ℝ u (y + d • e)) - (fderiv ℝ u x - fderiv ℝ u y)‖ := by
            congr 1; abel
        _ ≤ ‖fderiv ℝ u (x + d • e) - fderiv ℝ u (y + d • e)‖ + ‖fderiv ℝ u x - fderiv ℝ u y‖ :=
            norm_sub_le _ _
        _ ≤ H * ‖x - y‖ ^ α + H * ‖x - y‖ ^ α := add_le_add h1 h2
        _ = 2 * H * ‖x - y‖ ^ α := by ring
    calc |d|⁻¹ * _ ≤ |d|⁻¹ * (2 * H * ‖x - y‖ ^ α) := by gcongr
      _ = 2 * |d|⁻¹ * H * ‖x - y‖ ^ α := by ring
/-- Segment-averaged forcing (Simon Ch. 5, §7, Step 4 and (H4) of the `C^{2,α}` bootstrap): with
`G(x) = ∫₀¹ g(x + (t d) e) dt`, `Φ(x) := ⟨G(x), · e⟩` is a continuous linear form on
`L(ℝⁿ, ℝ^ℓ)`, and if every segment `x + [0, d] e`, `x ∈ S`, lies in a set `K` on which `g` is
`α`-Hölder with constant `H`, then `|Φ(x)[P] − Φ(y)[P]| ≤ H ‖e‖ ‖x − y‖^α ‖P‖` on `S`. -/
theorem dohr_eb_elc2_averaged_forcing : ∀ (n ℓ : ℕ) (α H d : ℝ) (g : Rn n → Rn ℓ) (S K : Set (Rn n)) (e : Rn n), 0 < α → (∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ K) → (∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ H * ‖x - y‖ ^ α) → ∃ Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Φ x P = inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (P e)) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ H * ‖e‖ * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α H d g S K e hα hseg hH
  -- `G(x) = ∫₀¹ g(x + (t d) e) dt` and `Φ(x) = ⟨G(x), ·⟩ ∘ (P ↦ P e)`.
  set G : Rn n → Rn ℓ := fun x => ∫ t in (0 : ℝ)..1, g (x + (t * d) • e) with hG
  refine ⟨fun x => (innerSL ℝ (G x)).comp (ContinuousLinearMap.apply ℝ (Rn ℓ) e), ?_, ?_⟩
  · intro x P
    simp [G, innerSL_apply_apply]
  · -- `g` is continuous on `K`: `‖g q − g p‖ ≤ max H 0 ‖q − p‖^α → 0` as `q → p`, since `α > 0`.
    have hgc : ContinuousOn g K := by
      intro p hp
      rw [Metric.continuousWithinAt_iff]
      intro η hη
      have hcont : Tendsto (fun r : ℝ => max H 0 * r ^ α) (𝓝[≥] 0) (𝓝 (max H 0 * 0 ^ α)) := by
        apply Tendsto.const_mul
        exact ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).mono_left
          nhdsWithin_le_nhds
      rw [Real.zero_rpow hα.ne', mul_zero] at hcont
      obtain ⟨δ, hδ, hδη⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hcont) η hη
      refine ⟨δ, hδ, fun q hq hqp => ?_⟩
      rw [dist_eq_norm] at hqp ⊢
      have h2 : max H 0 * ‖q - p‖ ^ α < η := by
        have := hδη (x := ‖q - p‖) (by simp)
          (by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hqp)
        rw [Real.dist_eq, sub_zero] at this
        exact lt_of_le_of_lt (le_abs_self _) this
      calc ‖g q - g p‖ ≤ H * ‖q - p‖ ^ α := hH q hq p hp
        _ ≤ max H 0 * ‖q - p‖ ^ α := by gcongr; exact le_max_left _ _
        _ < η := h2
    -- For `x ∈ S`, `t ↦ g(x + (t d) e)` is continuous on `[0, 1]`, hence interval integrable.
    have hint : ∀ x ∈ S, IntervalIntegrable (fun t : ℝ => g (x + (t * d) • e)) volume 0 1 := by
      intro x hx
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact hgc.comp (by fun_prop) (fun t ht => hseg x hx t ht)
    intro x hx y hy P
    -- `‖G x − G y‖ ≤ H ‖x − y‖^α`: the integrand difference is bounded pointwise on `(0, 1]`.
    have hGd : ‖G x - G y‖ ≤ H * ‖x - y‖ ^ α := by
      simp only [G]
      rw [← intervalIntegral.integral_sub (hint x hx) (hint y hy)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (C := H * ‖x - y‖ ^ α) (f := fun t => g (x + (t * d) • e) - g (y + (t * d) • e)) (by
          intro t ht
          rw [uIoc_of_le zero_le_one] at ht
          have h := hH _ (hseg x hx t ⟨ht.1.le, ht.2⟩) _ (hseg y hy t ⟨ht.1.le, ht.2⟩)
          simpa using h)
      simpa using this
    -- Cauchy–Schwarz and `‖P e‖ ≤ ‖P‖ ‖e‖`.
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply]
    rw [← inner_sub_left]
    calc |inner ℝ (G x - G y) (P e)| ≤ ‖G x - G y‖ * ‖P e‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖G x - G y‖ * (‖P‖ * ‖e‖) := by gcongr; exact P.le_opNorm e
      _ ≤ (H * ‖x - y‖ ^ α) * (‖P‖ * ‖e‖) := by gcongr
      _ = H * ‖e‖ * ‖x - y‖ ^ α * ‖P‖ := by ring
/-- Local-to-global step of the elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1
(pp. 127–128): if every point of the open set `U` has a ball `B_r(x)` on which `f` is `C¹` with
`‖Df(y) - Df(z)‖ ≤ C ‖y - z‖^α`, then `f` is `C^{1,α}` in `U`.  `f` is `C¹` on `U` by locality
(`contDiffOn_of_locally_contDiffOn`), and `D¹f` corresponds to `Df` under the linear isometry
`continuousMultilinearCurryFin1`.  A compact `K ⊆ U` is covered by finitely many of the balls; for a
Lebesgue number `δ` of this cover, pairs with `‖y - z‖ < δ` lie in one ball, while pairs with
`‖y - z‖ ≥ δ` satisfy `‖Df(y) - Df(z)‖ ≤ 2B ≤ (2B/δ^α) ‖y - z‖^α`, where `B ≥ sup_K ‖Df‖`. -/
theorem dohr_eb_elc2_local_to_global_holder : ∀ (n ℓ : ℕ) (α : ℝ) (f : Rn n → Rn ℓ) (U : Set (Rn n)), 0 < α → IsOpen U → (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 1 f (ball x r) ∧ ∃ C : ℝ, ∀ y ∈ ball x r, ∀ z ∈ ball x r, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ C * ‖y - z‖ ^ α) → IsLocallyHolderCkα 1 α f U := by
  intro n ℓ α f U hα hU hloc
  -- Step 1: `f` is `C¹` on `U`, being `C¹` on a ball around each point of `U`.
  have hC1 : ContDiffOn ℝ 1 f U := by
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨r, hr, hf, -⟩ := hloc x hx
    exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hf.mono inter_subset_right⟩
  refine ⟨by simpa using hC1, fun K hK hKU => ?_⟩
  -- Step 2: `‖D¹f x - D¹f y‖ = ‖Df x - Df y‖`, via the isometry `continuousMultilinearCurryFin1`.
  have hconv : ∀ x y : Rn n,
      ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := by
    intro x y
    have hc : ∀ z, iteratedFDeriv ℝ 1 f z =
        (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ f z) := by
      intro z
      ext m
      simp
    rw [hc, hc, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
  simp_rw [hconv]
  -- Step 3: `Df` is continuous on `U`, hence bounded on `K` by some `B ≥ 0`.
  obtain ⟨B, hB⟩ :=
    hK.exists_bound_of_continuousOn ((hC1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  -- Step 4: finitely many of the balls cover `K`; `δ > 0` is a Lebesgue number of this cover.
  choose! r hr _hfr C hC using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => ball (i : Rn n) (r i))
    (fun _ => isOpen_ball) fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr x (hKU hx))⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun i : t => ball ((i : K) : Rn n) (r (i : K))) (fun _ => isOpen_ball) fun x hx => by
      obtain ⟨i, hi, hx'⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx'⟩
  -- Step 5: `Cs = ∑_{i ∈ t} |C i|` dominates every local Hölder constant of the subcover.
  have hCs : ∀ i ∈ t, C i ≤ ∑ j ∈ t, |C j| := fun i hi =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j : K => |C j|) (fun j _ => abs_nonneg _) hi)
  have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  have hD0 : 0 ≤ 2 * max B 0 / δ ^ α := div_nonneg (mul_nonneg zero_le_two hB0) hδα.le
  refine ⟨∑ j ∈ t, |C j| + 2 * max B 0 / δ ^ α, fun y hy z hz => ?_⟩
  have hpow : 0 ≤ ‖y - z‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  by_cases hyz : ‖y - z‖ < δ
  · -- Step 6a: `y` and `z` lie in one ball `B_{r_i}(x_i)` of the subcover.
    obtain ⟨⟨i, hi⟩, hsub⟩ := hleb y hy
    have hyb : y ∈ ball (i : Rn n) (r i) := hsub (mem_ball_self hδ)
    have hzb : z ∈ ball (i : Rn n) (r i) :=
      hsub (by rwa [mem_ball, dist_eq_norm, norm_sub_rev])
    calc ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ C i * ‖y - z‖ ^ α := hC i (hKU i.2) y hyb z hzb
      _ ≤ (∑ j ∈ t, |C j| + 2 * max B 0 / δ ^ α) * ‖y - z‖ ^ α :=
        mul_le_mul_of_nonneg_right (by linarith [hCs i hi]) hpow
  · -- Step 6b: `‖y - z‖ ≥ δ`, so `‖Df y - Df z‖ ≤ 2 max B 0 ≤ (2 max B 0 / δ^α) ‖y - z‖^α`.
    have hδyz : δ ^ α ≤ ‖y - z‖ ^ α := Real.rpow_le_rpow hδ.le (not_lt.mp hyz) hα.le
    calc ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f z‖ := norm_sub_le _ _
      _ ≤ max B 0 + max B 0 :=
        add_le_add ((hB y hy).trans (le_max_left _ _)) ((hB z hz).trans (le_max_left _ _))
      _ = 2 * max B 0 / δ ^ α * δ ^ α := by rw [div_mul_cancel₀ _ hδα.ne']; ring
      _ ≤ 2 * max B 0 / δ ^ α * ‖y - z‖ ^ α := mul_le_mul_of_nonneg_left hδyz hD0
      _ ≤ (∑ j ∈ t, |C j| + 2 * max B 0 / δ ^ α) * ‖y - z‖ ^ α :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => abs_nonneg (C j))) hpow
/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (p. 127): a function that is `C^{j,α}`
locally in the open ball `B̆_r(x₀)` is `C^{j,α}`, with global constants, on `B̆_{r/2}(x₀)`.  For
`r ≤ 0` the half ball is empty.  Otherwise the closed half ball `B_{r/2}(x₀)` is a compact subset of
`B̆_r(x₀)`, on which each `D^i u`, `i ≤ j`, is continuous, hence bounded, and `D^j u` is `α`-Hölder
by the local hypothesis. -/
theorem dohr_eb_isHolderCk_half_ball : ∀ (m k j : ℕ) (α : ℝ) (u : Rn m → Rn k) (x₀ : Rn m) (r : ℝ), IsLocallyHolderCkα j α u (ball x₀ r) → IsHolderCkα j α u (ball x₀ (r / 2)) := by
  intro m k j α u x₀ r hu
  -- For `r ≤ 0` the half ball is empty and all three conditions hold vacuously.
  rcases le_or_gt r 0 with hr | hr
  · have hempty : ball x₀ (r / 2) = ∅ := ball_eq_empty.2 (by linarith)
    rw [hempty]
    exact ⟨contDiffOn_empty, ⟨0, fun _ _ x hx => hx.elim⟩, ⟨0, fun x hx => hx.elim⟩⟩
  -- The closed half ball is a compact subset of the open ball.
  have hK : closedBall x₀ (r / 2) ⊆ ball x₀ r := closedBall_subset_ball (by linarith)
  have hKc : IsCompact (closedBall x₀ (r / 2)) := isCompact_closedBall x₀ (r / 2)
  have hsub : ball x₀ (r / 2) ⊆ closedBall x₀ (r / 2) := ball_subset_closedBall
  refine ⟨hu.1.mono (hsub.trans hK), ?_, ?_⟩
  · -- Each `D^i u`, `i ≤ j`, is continuous on the open ball, hence bounded on the closed half ball.
    have hbd : ∀ i, ∃ B : ℝ, i ≤ j → ∀ x ∈ closedBall x₀ (r / 2), ‖iteratedFDeriv ℝ i u x‖ ≤ B := by
      intro i
      by_cases hi : i ≤ j
      · have hcont : ContinuousOn (iteratedFDeriv ℝ i u) (ball x₀ r) :=
          (hu.1.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi)
            isOpen_ball.uniqueDiffOn).congr (iteratedFDerivWithin_of_isOpen i isOpen_ball).symm
        obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hK)
        exact ⟨B, fun _ => hB⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose B hB using hbd
    refine ⟨∑ i ∈ Finset.range (j + 1), |B i|, fun i hi x hx => ?_⟩
    calc ‖iteratedFDeriv ℝ i u x‖ ≤ B i := hB i hi x (hsub hx)
      _ ≤ |B i| := le_abs_self _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |B i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (B i))
            (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  · -- The Hölder constant on the compact closed half ball serves on the open half ball.
    obtain ⟨C, hC⟩ := hu.2 _ hKc hK
    exact ⟨C, fun x hx y hy => hC x (hsub hx) y (hsub hy)⟩
/-- Covering step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if every
point of the open set `U` has a ball in `U` on which `F` is `C¹` with `α`-Hölder derivative, then
`F` is `C¹` on `U` and `D¹F` is `α`-Hölder on every compact `K ⊆ U`.  Pairs of points of `K` closer
than a Lebesgue number `δ` of a finite subcover lie in one ball; for the other pairs,
`‖DF(x) - DF(y)‖ ≤ 2 sup_K ‖DF‖ ≤ 2 sup_K ‖DF‖ δ^{-α} ‖x - y‖^α`. -/
theorem dohr_eb_lhr_cover_holder_one : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) (U : Set (Rn n)) (F : Rn n → E), 0 < α → IsOpen U → (∀ x ∈ U, ∃ R : ℝ, 0 < R ∧ ball x R ⊆ U ∧ ContDiffOn ℝ 1 F (ball x R) ∧ ∃ C : ℝ, ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖fderiv ℝ F y - fderiv ℝ F z‖ ≤ C * ‖y - z‖ ^ α) → ContDiffOn ℝ 1 F U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 F x - iteratedFDeriv ℝ 1 F y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n E _ _ α U F hα hU hloc
  choose! R hR hRU hRF C hC using hloc
  -- Step 1: `F` is `C¹` on `U` by locality.
  have hF : ContDiffOn ℝ 1 F U := by
    refine contDiffOn_of_locally_contDiffOn fun x hx =>
      ⟨ball x (R x), isOpen_ball, mem_ball_self (hR x hx), ?_⟩
    rw [inter_eq_right.2 (hRU x hx)]
    exact hRF x hx
  refine ⟨hF, fun K hK hKU => ?_⟩
  -- Steps 2–3: `DF` is continuous on `U`, hence bounded by `S` on `K`.
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn
    ((hF.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: finitely many hypothesis balls cover `K`; `Cs` bounds their Hölder constants.
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x => ball x (R x))
    fun x hx => ball_mem_nhds x (hR x (hKU hx))
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, ∀ i ∈ t, C i ≤ Cs :=
    ⟨∑ i ∈ t, |C i|, fun i hi => (le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) hi)⟩
  -- Step 5: a Lebesgue number `δ` of this finite cover.
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun i : t => ball (i : Rn n) (R i)) (fun _ => isOpen_ball) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hKt hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  -- Steps 6–8: the Hölder bound for `DF` on `K`.
  have hD : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤
      max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α := by
    intro x hx y hy
    have hxy : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    rcases lt_or_ge ‖x - y‖ δ with hlt | hge
    · -- Near pairs lie in one ball of the subcover.
      obtain ⟨⟨i, hi⟩, hiδ⟩ := hδK x hx
      have hxB : x ∈ ball i (R i) := hiδ (mem_ball_self hδ)
      have hyB : y ∈ ball i (R i) := hiδ (mem_ball'.2 (by rwa [dist_eq_norm]))
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ C i * ‖x - y‖ ^ α :=
            hC i (hKU (htK i hi)) x hxB y hyB
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right ((hCs i hi).trans (le_max_left _ _)) hxy
    · -- Far pairs: `‖x - y‖ ^ α ≥ δ ^ α > 0`.
      have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
      have hδα : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
      calc ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ ‖fderiv ℝ F x‖ + ‖fderiv ℝ F y‖ := norm_sub_le _ _
        _ ≤ S + S := add_le_add (hS x hx) (hS y hy)
        _ = 2 * S * (δ ^ α)⁻¹ * δ ^ α := by rw [inv_mul_cancel_right₀ hδα.ne', two_mul]
        _ ≤ 2 * S * (δ ^ α)⁻¹ * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hge hα.le) (by positivity)
        _ ≤ max Cs (2 * S * (δ ^ α)⁻¹) * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hxy
  -- Step 9: `D¹F(z)` is the image of `DF(z)` under a linear isometry equivalence.
  have hiso : ∀ z, iteratedFDeriv ℝ 1 F z =
      (continuousMultilinearCurryFin1 ℝ (Rn n) E).symm (fderiv ℝ F z) := by
    intro z
    ext m
    rw [iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_symm_apply]
  refine ⟨max Cs (2 * S * (δ ^ α)⁻¹), fun x hx y hy => ?_⟩
  rw [hiso x, hiso y, ← map_sub, LinearIsometryEquiv.norm_map]
  exact hD x hx y hy
/-- **Uniform bounds for a `C¹` scalar function on a compact convex set** (the scalar step of the
coefficient bounds in the linear higher-regularity part of Simon 7.1).  Let `0 < α ≤ 1`, `U ⊆ ℝⁿ`
open, `K ⊆ U` compact and convex, and `f` be `C¹` on `U`.  Then some `S ≥ 0` has `|f(x)| ≤ S` and
`|f(x) − f(y)| ≤ S |x − y|^α` for all `x, y ∈ K`.
Proof: `f` and `Df` are continuous, hence bounded, on the compact `K`; the mean value inequality
on the convex `K` gives `|f(x) − f(y)| ≤ S₁ |x − y|`; and with `D = diam K`,
`t = t^α t^{1−α} ≤ D^{1−α} t^α` for `0 ≤ t ≤ D`. -/
theorem dohr_eb_lhr_cub_scalar_c1_bounds : ∀ (n : ℕ) (α : ℝ) (U K : Set (Rn n)) (f : Rn n → ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → ContDiffOn ℝ 1 f U → ∃ S : ℝ, 0 ≤ S ∧ ∀ x ∈ K, ∀ y ∈ K, |f x| ≤ S ∧ |f x - f y| ≤ S * ‖x - y‖ ^ α := by
  intro n α U K f hα0 hα1 hU hK hKc hKU hf
  -- Step 1: `f` and `Df` are continuous on `K`, and `f` is differentiable at every point of `K`.
  have hfc : ContinuousOn f K := hf.continuousOn.mono hKU
  have hdfc : ContinuousOn (fderiv ℝ f) K := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  have hfd : ∀ x ∈ K, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn one_ne_zero x (hKU hx)).differentiableAt (hU.mem_nhds (hKU hx))
  -- Step 2: `|f| ≤ S0` and `‖Df‖ ≤ S1` on the compact set `K`.
  obtain ⟨S0, hS0⟩ := hK.exists_bound_of_continuousOn hfc
  obtain ⟨S1, hS1⟩ := hK.exists_bound_of_continuousOn hdfc
  -- Step 3: mean value inequality on the convex set `K`.
  have hlip : ∀ x ∈ K, ∀ y ∈ K, |f x - f y| ≤ max S1 0 * ‖x - y‖ := by
    intro x hx y hy
    have h := hKc.norm_image_sub_le_of_norm_fderiv_le (C := max S1 0) hfd
      (fun z hz => (hS1 z hz).trans (le_max_left _ _)) hy hx
    rwa [Real.norm_eq_abs] at h
  -- Step 4: `‖x - y‖ ≤ D := diam K` on `K`.
  have hdist : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ Metric.diam K := fun x hx y hy => by
    rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hK.isBounded hx hy
  -- Step 5: `t ≤ D^(1-α) t^α` for `0 ≤ t ≤ D`.
  have helem : ∀ t : ℝ, 0 ≤ t → t ≤ Metric.diam K →
      t ≤ Metric.diam K ^ (1 - α) * t ^ α := by
    intro t ht0 htD
    rcases ht0.eq_or_lt with rfl | htpos
    · rw [Real.zero_rpow hα0.ne', mul_zero]
    · have h1 : t ^ α * t ^ (1 - α) = t := by
        rw [← Real.rpow_add htpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have h2 : t ^ (1 - α) ≤ Metric.diam K ^ (1 - α) :=
        Real.rpow_le_rpow ht0 htD (by linarith)
      calc t = t ^ α * t ^ (1 - α) := h1.symm
        _ ≤ t ^ α * Metric.diam K ^ (1 - α) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht0 _)
        _ = Metric.diam K ^ (1 - α) * t ^ α := mul_comm _ _
  -- Steps 6-7: `S := max (max S0 0) (max S1 0 * D^(1-α))`.
  refine ⟨max (max S0 0) (max S1 0 * Metric.diam K ^ (1 - α)),
    (le_max_right _ _).trans (le_max_left _ _), ?_⟩
  intro x hx y hy
  constructor
  · calc |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
      _ ≤ S0 := hS0 x hx
      _ ≤ max S0 0 := le_max_left _ _
      _ ≤ _ := le_max_left _ _
  · calc |f x - f y| ≤ max S1 0 * ‖x - y‖ := hlip x hx y hy
      _ ≤ max S1 0 * (Metric.diam K ^ (1 - α) * ‖x - y‖ ^ α) :=
        mul_le_mul_of_nonneg_left (helem _ (norm_nonneg _) (hdist x hx y hy)) (le_max_right _ _)
      _ = (max S1 0 * Metric.diam K ^ (1 - α)) * ‖x - y‖ ^ α := (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)
/-- Coefficient bounds for the linear system in the proof of Simon Ch. 5, Theorem 7.1 (second
assertion, p. 127), steps 1, 2 and 6: on a finite-dimensional real normed space `L` with basis
`E₀, …, E_{N-1}`, every continuous bilinear form satisfies
`|B(P)(Q)| ≤ c (∑_{r,t} |B(E_r)(E_t)|) ‖P‖ ‖Q‖`, and likewise for the difference `B − B'` of two
forms, with `c = c₀²`, `c₀ = ∑_r ‖π_r‖` the sum of the norms of the coordinate functionals. -/
theorem dohr_eb_lhr_cub_bilinear_basis_bound : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (E : Fin N → L) (c : ℝ), 0 ≤ c ∧ (∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t)|) * ‖P‖ * ‖Q‖) ∧ ∀ (B B' : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L), |B P Q - B' P Q| ≤ c * (∑ r, ∑ t, |B (E r) (E t) - B' (E r) (E t)|) * ‖P‖ * ‖Q‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` and its continuous coordinate functionals `π r`.
  let b := Module.finBasis ℝ L
  let π : Fin (Module.finrank ℝ L) → L →L[ℝ] ℝ := fun r =>
    LinearMap.toContinuousLinearMap (b.coord r)
  have hπ : ∀ r P, π r P = b.repr P r := fun r P => by simp [π]
  -- Step 2: `|P_r| ≤ c₀ ‖P‖` with `c₀ = ∑ r, ‖π r‖`.
  let c₀ : ℝ := ∑ r, ‖π r‖
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun r _ => norm_nonneg (π r)
  have hcoord : ∀ r P, |b.repr P r| ≤ c₀ * ‖P‖ := by
    intro r P
    rw [← hπ, ← Real.norm_eq_abs]
    calc ‖π r P‖ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ c₀ * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun s _ => norm_nonneg (π s)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: `B P Q = ∑ r, ∑ t, P_r Q_t B (b r) (b t)`.
  have hexp : ∀ (B : L →L[ℝ] L →L[ℝ] ℝ) (P Q : L),
      B P Q = ∑ r, ∑ t, b.repr P r * b.repr Q t * B (b r) (b t) := by
    intro B P Q
    conv_lhs => rw [← b.sum_repr P, ← b.sum_repr Q]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  -- Step 4: `|∑ r, ∑ t, P_r Q_t β r t| ≤ c₀² (∑ r, ∑ t, |β r t|) ‖P‖ ‖Q‖` for any array `β`.
  have harr : ∀ (β : Fin (Module.finrank ℝ L) → Fin (Module.finrank ℝ L) → ℝ) (P Q : L),
      |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t| ≤
        c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
    intro β P Q
    calc |∑ r, ∑ t, b.repr P r * b.repr Q t * β r t|
        ≤ ∑ r, |∑ t, b.repr P r * b.repr Q t * β r t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, |b.repr P r * b.repr Q t * β r t| :=
          Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, ∑ t, c₀ * ‖P‖ * (c₀ * ‖Q‖) * |β r t| := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun t _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (hcoord r P) (hcoord t Q) (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = c₀ ^ 2 * (∑ r, ∑ t, |β r t|) * ‖P‖ * ‖Q‖ := by
          simp only [← Finset.mul_sum]
          ring
  -- Step 5: take `E = b` and `c = c₀²`; for `B − B'` subtract the two expansions termwise.
  refine ⟨Module.finrank ℝ L, b, c₀ ^ 2, by positivity, fun B P Q => ?_, fun B B' P Q => ?_⟩
  · rw [hexp B P Q]
    exact harr _ P Q
  · rw [hexp B P Q, hexp B' P Q]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    exact harr _ P Q
/-- Coefficient bounds in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): if every component `x ↦ a(x)[P][Q]` of a field `a` of continuous bilinear forms on
`L = L(ℝⁿ, ℝ^ℓ)` is `C¹` on the open set `U`, then on each compact convex `K ⊆ U` the forms `a(x)`
are uniformly bounded and uniformly `α`-Hölder in `x`.  A basis `E_r` of `L` controls every
bilinear form through its values `B(E_r, E_t)`, and each `C¹` component `a_rt(x) = a(x)[E_r][E_t]`
is bounded by `S_rt` and `α`-Hölder with constant `S_rt` on `K`; take `M := c Σ_{r,t} S_rt`. -/
theorem dohr_eb_lhr_coeff_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U K : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), 0 < α → α ≤ 1 → IsOpen U → IsCompact K → Convex ℝ K → K ⊆ U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ∃ M : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖ ∧ |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
  intro n ℓ α U K a hα hα1 hU hK hKc hKU ha
  -- Steps 1–2: expansion of bilinear forms on a basis `E` of `L`.
  obtain ⟨N, E, c, hc, hB, hBB'⟩ :=
    Submission.dohr_eb_lhr_cub_bilinear_basis_bound (Rn n →L[ℝ] Rn ℓ)
  -- Steps 3–5: each component `a_rt` is bounded and `α`-Hölder on `K`, with constant `S r t`.
  choose S hS0 hS using fun r t : Fin N =>
    Submission.dohr_eb_lhr_cub_scalar_c1_bounds n α U K (fun x => a x (E r) (E t)) hα hα1 hU hK
      hKc hKU (ha (E r) (E t))
  -- Steps 6–7: sum the component bounds over the basis.
  refine ⟨c * ∑ r, ∑ t, S r t, fun x hx y hy P Q => ⟨?_, ?_⟩⟩
  · calc |a x P Q| ≤ c * (∑ r, ∑ t, |a x (E r) (E t)|) * ‖P‖ * ‖Q‖ := hB (a x) P Q
      _ ≤ c * (∑ r, ∑ t, S r t) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).1
  · calc |a x P Q - a y P Q|
        ≤ c * (∑ r, ∑ t, |a x (E r) (E t) - a y (E r) (E t)|) * ‖P‖ * ‖Q‖ :=
          hBB' (a x) (a y) P Q
      _ ≤ c * (∑ r, ∑ t, S r t * ‖x - y‖ ^ α) * ‖P‖ * ‖Q‖ := by
        gcongr with r _ t _
        exact (hS r t x hx y hy).2
      _ = c * (∑ r, ∑ t, S r t) * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ := by
        simp only [← Finset.sum_mul]
        ring
/-- Continuity of a linear-form family evaluated along continuous data (in the difference-quotient
weak equation of the linear higher-regularity step of the elliptic bootstrap for Simon 7.1): if
`x ↦ Φ(x)[P]` is continuous on the open set `U` for every `P ∈ L = L(ℝⁿ, ℝ^ℓ)`, `s(x₀) ∈ U` and `s`,
`B` are continuous at `x₀`, then `x ↦ Φ(s(x))[B(x)]` is continuous at `x₀`.  Expanding `B(x)` in a
basis `(E_r)` of the finite-dimensional space `L` writes `Φ(s(x))[B(x)]` as the finite sum
`Σ_r c_r(B(x)) Φ(s(x))[E_r]` of products of functions continuous at `x₀`. -/
theorem dohr_eb_lhr_dqwe_linear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => Φ (s x) (B x)) x₀ := by
  intro n ℓ U Φ s B x₀ hU hΦ hs₀ hs hB
  -- Step 1: a basis `E_r = b r` of `L`; its coordinates `c_r = b.coord r` are continuous on `L`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: `Φ(s x)[B x] = Σ_r c_r(B x) Φ(s x)[E_r]`, by linearity of `Φ(s x)`.
  have hexp : (fun x => Φ (s x) (B x)) = fun x => ∑ r, b.repr (B x) r * Φ (s x) (b r) := by
    funext x
    conv_lhs => rw [← b.sum_repr (B x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  -- Step 3: `x ↦ c_r(B x)` is continuous at `x₀`.
  have hc : ∀ r, ContinuousAt (fun x => b.repr (B x) r) x₀ := fun r =>
    (b.coord r).continuous_of_finiteDimensional.continuousAt.comp hB
  -- Step 4: `x ↦ Φ(s x)[E_r]` is continuous at `x₀`, since `U` is a neighbourhood of `s x₀`.
  have hΦr : ∀ r, ContinuousAt (fun x => Φ (s x) (b r)) x₀ := fun r =>
    ((hΦ (b r)).continuousAt (hU.mem_nhds hs₀)).comp hs
  -- Step 5: a finite sum of products of functions continuous at `x₀` is continuous at `x₀`.
  rw [hexp]
  exact tendsto_finsetSum _ fun r _ => (hc r).mul (hΦr r)
/-- **Continuity of a bilinear-form family evaluated along continuous data.**  Let
`L = L(ℝⁿ, ℝ^ℓ)`, let `U ⊆ ℝⁿ` be open and let `a : ℝⁿ → L(L, L(L, ℝ))` be such that
`x ↦ a(x)[P][Q]` is continuous on `U` for all `P, Q ∈ L`.  If `s(x₀) ∈ U` and `s`, `A`, `B` are
continuous at `x₀`, then `x ↦ a(s(x))[A(x)][B(x)]` is continuous at `x₀`.
In a basis `(E_r)` of `L` with (continuous) coordinate functionals `c_r`,
`a(s(x))[A(x)][B(x)] = Σ_r c_r(A(x)) · a(s(x))[E_r][B(x)]`, and each `x ↦ a(s(x))[E_r][B(x)]` is
continuous at `x₀` by `dohr_eb_lhr_dqwe_linear_family_continuousAt` applied to `y ↦ a(y)[E_r]`. -/
theorem dohr_eb_lhr_dqwe_bilinear_family_continuousAt : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (s : Rn n → Rn n) (A B : Rn n → Rn n →L[ℝ] Rn ℓ) (x₀ : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → s x₀ ∈ U → ContinuousAt s x₀ → ContinuousAt A x₀ → ContinuousAt B x₀ → ContinuousAt (fun x => a (s x) (A x) (B x)) x₀ := by
  intro n ℓ U a s A B x₀ hU ha hsU hs hA hB
  -- Step 1: a basis `E_r = b r` of the finite-dimensional space `L`; its coordinate functionals
  -- `c_r = b.coord r` are continuous.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  have hc : ∀ r, Continuous fun P : Rn n →L[ℝ] Rn ℓ => b.repr P r := fun r =>
    (b.coord r).continuous_of_finiteDimensional
  -- Step 2: expanding the first slot, `a(s x)[A x][B x] = Σ_r c_r(A x) · a(s x)[E_r][B x]`.
  have hexp : ∀ x, a (s x) (A x) (B x) = ∑ r, b.repr (A x) r * a (s x) (b r) (B x) := by
    intro x
    conv_lhs => rw [← b.sum_repr (A x)]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  simp only [hexp]
  -- Steps 3–5: each summand is `c_r ∘ A` times `x ↦ a(s x)[E_r][B x]`, both continuous at `x₀`
  -- (the latter by the linear-family lemma for `y ↦ a(y)[E_r]`), and finite sums preserve this.
  refine tendsto_finsetSum _ fun r _ => ((hc r).continuousAt.comp hA).mul ?_
  exact Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U (fun y => a y (b r)) s B x₀
    hU (fun P => ha (b r) P) hsU hs hB
/-- Translated weak identity (difference-quotient step of the linear higher-regularity argument in
the elliptic bootstrap of Simon Ch. 5, Theorem 7.1).  Suppose
`∫_U a(x)[Dv(x)][Dζ(x)] dx = ∫_U Φ(x)[Dζ(x)] dx` for every `C¹` map `ζ : ℝⁿ → ℝ^ℓ` with compact
support in `U`, and let `η` be `C¹` with compact support and `x + h ∈ U` for `x ∈ spt η`.  Then
`∫ a(x + h)[Dv(x + h)][Dη(x)] dx = ∫ Φ(x + h)[Dη(x)] dx` over all of `ℝⁿ`.  Proof: test with
`ζ = η(· − h)`, which is `C¹` with compact support in `U` and `Dζ = Dη(· − h)`; both integrands
vanish off `U`, so the integrals over `U` are integrals over `ℝⁿ`; finally substitute `y = x + h`
(translation invariance of Lebesgue measure). -/
theorem dohr_eb_lhr_dqwe_shifted_weak_identity : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (h : Rn n) (η : Rn n → Rn ℓ), (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiff ℝ 1 η → HasCompactSupport η → (∀ x ∈ tsupport η, x + h ∈ U) → ∫ x, a (x + h) (fderiv ℝ v (x + h)) (fderiv ℝ η x) = ∫ x, Φ (x + h) (fderiv ℝ η x) := by
  intro n ℓ U a Φ v h η hweak hη hηc hηU
  -- Step 1: the translated test function `ζ = η(· − h)` is `C¹` with compact support.
  have hζC : ContDiff ℝ 1 (fun y => η (y - h)) := hη.comp (contDiff_id.sub contDiff_const)
  have hζc : HasCompactSupport (fun y => η (y - h)) := hηc.comp_homeomorph (Homeomorph.subRight h)
  -- Step 2: `y ∈ spt ζ ⇒ y − h ∈ spt η ⇒ y = (y − h) + h ∈ U`.
  have hζU : tsupport (fun y => η (y - h)) ⊆ U := fun y hy => by
    simpa only [sub_add_cancel] using
      hηU (y - h) (tsupport_comp_subset_preimage η (continuous_id.sub continuous_const) hy)
  -- Step 3: the weak identity for `ζ`, with `Dζ(y) = Dη(y − h)`.
  have h3 := hweak (fun y => η (y - h)) hζC hζc hζU
  simp only [fderiv_comp_sub] at h3
  -- Step 4: off `U`, `y − h ∉ spt η ⊇ spt Dη`, so `Dη(y − h) = 0` and both integrands vanish.
  have hvan : ∀ y, y ∉ U → fderiv ℝ η (y - h) = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => hy (by
      simpa only [sub_add_cancel] using hηU (y - h) (tsupport_fderiv_subset ℝ hmem))
  have hL : ∫ y in U, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) =
      ∫ y, a y (fderiv ℝ v y) (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  have hR : ∫ y in U, Φ y (fderiv ℝ η (y - h)) = ∫ y, Φ y (fderiv ℝ η (y - h)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hvan y hy, map_zero]
  -- Step 5: substitute `y = x + h` (Lebesgue measure is translation invariant), `x + h − h = x`.
  have e1 := integral_add_right_eq_self (μ := volume)
    (fun y => a y (fderiv ℝ v y) (fderiv ℝ η (y - h))) h
  have e2 := integral_add_right_eq_self (μ := volume) (fun y => Φ y (fderiv ℝ η (y - h))) h
  simp only [add_sub_cancel_right] at e1 e2
  rw [e1, e2, ← hL, ← hR]
  exact h3
/-- A function `F : ℝⁿ → ℝ` continuous at every point of a compact set `K` and vanishing off `K` is
Lebesgue integrable.  `K` is closed, so each `x ∉ K` has the open neighbourhood `ℝⁿ \ K` on which
`F = 0`, and `F` is continuous at `x`; at the points of `K` it is continuous by hypothesis.  Thus `F`
is continuous, and it has compact support since it vanishes off the compact set `K`, so it is
integrable for `volume`, which is finite on compact sets. -/
theorem dohr_eb_lhr_dqwe_integrable_of_continuousAt : ∀ (n : ℕ) (F : Rn n → ℝ) (K : Set (Rn n)), IsCompact K → (∀ x ∈ K, ContinuousAt F x) → (∀ x, x ∉ K → F x = 0) → Integrable F := by
  intro n F K hK hcont hzero
  -- Steps 1–3: `F` is continuous at every point; off `K` it agrees with `0` on the open
  -- neighbourhood `Kᶜ` of the point.
  have hF : Continuous F := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ K
    · exact hcont x hx
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 x] F := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact (hzero y hy).symm
      exact continuousAt_const.congr hev
  -- Steps 4–5: `F` vanishes off the compact set `K`, so it has compact support and is integrable.
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hK hzero)
/-- Derivative of a difference quotient (difference-quotient step of the linear higher-regularity
argument in the elliptic bootstrap of Simon Ch. 5, Theorem 7.1): if `v : ℝⁿ → ℝ^ℓ` is
differentiable at `x` and at `x + d e`, then the derivative at `x` of
`z ↦ d⁻¹ (v(z + d e) − v(z))` is `d⁻¹ (Dv(x + d e) − Dv(x))`.  For `d = 0` both sides vanish,
as `0⁻¹ = 0`.  By the chain rule `g(z) = v(z + d e)` is differentiable at `x` with
`Dg(x) = Dv(x + d e)`; the derivative of `d⁻¹ (g − v)` is then `d⁻¹ (Dg(x) − Dv(x))`. -/
theorem dohr_eb_lhr_dqwe_fderiv_diff_quot : ∀ (n ℓ : ℕ) (v : Rn n → Rn ℓ) (e x : Rn n) (d : ℝ), DifferentiableAt ℝ v x → DifferentiableAt ℝ v (x + d • e) → fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) := by
  intro n ℓ v e x d hx hxd
  have hg : DifferentiableAt ℝ (fun z => v (z + d • e)) x :=
    hxd.comp x (differentiableAt_id.add_const (d • e))
  rw [fderiv_fun_const_smul (hg.fun_sub hx) d⁻¹, fderiv_fun_sub hg hx,
    fderiv_comp_add_right (d • e)]
/-- Difference quotients of a weak solution (step 3 of the linear higher-regularity argument behind
**Simon Ch. 5, Theorem 7.1(ii)**).  If `v ∈ C¹(U)` satisfies `∫_U a(x)[Dv][Dζ] = ∫_U Φ(x)[Dζ]` for
all `ζ ∈ C¹_c(U; ℝ^ℓ)`, then `w = d⁻¹ (v(· + de) − v)` satisfies `∫_B a(x)[Dw][Dζ] = ∫_B Ψ(x)[Dζ]`
on `B = B̆_{2R}(xb)` for all `ζ ∈ C¹_c(B; ℝ^ℓ)`, where
`Ψ(x) = d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de) − a(x))[Dv(x + de)]`: test the equation with `ζ`
and with `ζ(· − de)`, subtract, and divide by `d`. -/
theorem dohr_eb_lhr_dq_weak_equation : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R d : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → d ≠ 0 → |d| < R → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContinuousOn (fun x => Φ x P) U) → ContDiffOn ℝ 1 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball xb (2 * R) → ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x) = ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v xb e R d hU hR hball he hd hdR ha hΦ hv hweak
  -- Step 1: `Ψ(x) := d⁻¹ (Φ(x + de) − Φ(x)) − d⁻¹ (a(x + de)[Q_x] − a(x)[Q_x])`,
  -- `Q_x := Dv(x + de)`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ),
      Ψ x P = d⁻¹ * (Φ (x + d • e) P - Φ x P) -
        d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P) :=
    ⟨fun x => d⁻¹ • (Φ (x + d • e) - Φ x) -
        d⁻¹ • (a (x + d • e) (fderiv ℝ v (x + d • e)) - a x (fderiv ℝ v (x + d • e))),
      fun x P => by simp only [sub_apply, smul_apply, smul_eq_mul]⟩
  refine ⟨Ψ, hΨ, fun ζ hζ hζc hζB => ?_⟩
  -- Step 2: for `x ∈ B := B̆_{2R}(xb)`, both `x` and `x + de` lie in `B_{4R}(xb) ⊆ U`.
  have hde : ‖d • e‖ < R := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
      _ < R := by rwa [mul_one]
  have hBU : ∀ x ∈ ball xb (2 * R), x ∈ U := fun x hx =>
    hball (mem_closedBall.2 (by linarith [mem_ball.1 hx]))
  have hBU' : ∀ x ∈ ball xb (2 * R), x + d • e ∈ U := by
    intro x hx
    refine hball (mem_closedBall.2 ?_)
    have h1 : dist (x + d • e) x = ‖d • e‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    linarith [dist_triangle (x + d • e) x xb, mem_ball.1 hx]
  -- Step 3: `v` is differentiable and `Dv` is continuous at every point of the open set `U`.
  have hvd : ∀ y ∈ U, DifferentiableAt ℝ v y := fun y hy =>
    (hv.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hDv : ∀ y ∈ U, ContinuousAt (fderiv ℝ v) y := fun y hy =>
    (hv.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hy)
  have hsh : ∀ x : Rn n, ContinuousAt (fun y : Rn n => y + d • e) x := fun x =>
    (continuous_id.add continuous_const).continuousAt
  -- Step 5: `K := tsupport ζ ⊆ B` is compact; `Dζ` is continuous and vanishes off `K`.
  have hK : IsCompact (tsupport ζ) := hζc
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ hx
  have hKU : ∀ x ∈ tsupport ζ, x ∈ U := fun x hx => hBU x (hζB hx)
  have hKU' : ∀ x ∈ tsupport ζ, x + d • e ∈ U := fun x hx => hBU' x (hζB hx)
  -- Step 6: the integrands `f₁, g₁, f₂, f₃, g₃` are continuous at the points of `K` and vanish
  -- off `K`, hence integrable.
  have hf1 : Integrable (fun x => a x (fderiv ℝ v x) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fderiv ℝ v) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x) (hDv x (hKU x hx))
        hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg1 : Integrable (fun x => Φ x (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ (fun y => y)
        (fderiv ℝ ζ) x hU hΦ (hKU x hx) (continuousAt_id' x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf2 : Integrable (fun x => a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a (fun y => y)
        (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU x hx) (continuousAt_id' x)
        ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hf3 : Integrable (fun x => a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_bilinear_family_continuousAt n ℓ U a
        (fun y => y + d • e) (fun y => fderiv ℝ v (y + d • e)) (fderiv ℝ ζ) x hU ha (hKU' x hx)
        (hsh x) ((hDv _ (hKU' x hx)).comp_of_eq (hsh x) rfl) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  have hg3 : Integrable (fun x => Φ (x + d • e) (fderiv ℝ ζ x)) :=
    Submission.dohr_eb_lhr_dqwe_integrable_of_continuousAt n _ _ hK
      (fun x hx => Submission.dohr_eb_lhr_dqwe_linear_family_continuousAt n ℓ U Φ
        (fun y => y + d • e) (fderiv ℝ ζ) x hU hΦ (hKU' x hx) (hsh x) hDζ.continuousAt)
      (fun x hx => by rw [hDζ0 x hx, map_zero])
  -- Steps 7–8: testing with `ζ` and with `ζ(· − de)` gives `∫ f₁ = ∫ g₁` and `∫ f₃ = ∫ g₃`.
  have h7 : ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x, Φ x (fderiv ℝ ζ x) := by
    have h := Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v 0 ζ hweak hζ hζc
      (fun x hx => by rw [add_zero]; exact hKU x hx)
    simpa only [add_zero] using h
  have h8 : ∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) =
      ∫ x, Φ (x + d • e) (fderiv ℝ ζ x) :=
    Submission.dohr_eb_lhr_dqwe_shifted_weak_identity n ℓ U a Φ v (d • e) ζ hweak hζ hζc hKU'
  -- Step 9: on `B`, `Dw = d⁻¹ (Dv(· + de) − Dv)` (step 4), so
  -- `a(x)[Dw(x)][Dζ(x)] = d⁻¹ (f₂ − f₁)(x)`; both sides become integrals over `ℝⁿ` of integrands
  -- vanishing off `K ⊆ B`.
  have hlhs : ∫ x in ball xb (2 * R), a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x)
      (fderiv ℝ ζ x) = d⁻¹ * ((∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
        ∫ x, a x (fderiv ℝ v x) (fderiv ℝ ζ x)) := by
    have hEq : EqOn
        (fun x => a x (fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x) (fderiv ℝ ζ x))
        (fun x => d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
          a x (fderiv ℝ v x) (fderiv ℝ ζ x))) (ball xb (2 * R)) := by
      intro x hx
      simp only
      rw [Submission.dohr_eb_lhr_dqwe_fderiv_diff_quot n ℓ v e x d (hvd x (hBU x hx))
        (hvd _ (hBU' x hx)), map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
    have hzero : ∀ x, x ∉ ball xb (2 * R) → d⁻¹ * (a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v x) (fderiv ℝ ζ x)) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero, map_zero, sub_zero, mul_zero]
    rw [setIntegral_congr_fun measurableSet_ball hEq,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_const_mul,
      integral_sub hf2 hf1]
  have hrhs : ∫ x in ball xb (2 * R), Ψ x (fderiv ℝ ζ x) =
      d⁻¹ * ((∫ x, Φ (x + d • e) (fderiv ℝ ζ x)) - ∫ x, Φ x (fderiv ℝ ζ x)) -
        d⁻¹ * ((∫ x, a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) -
          ∫ x, a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) := by
    have hzero : ∀ x, x ∉ ball xb (2 * R) → Ψ x (fderiv ℝ ζ x) = 0 := by
      intro x hx
      rw [hDζ0 x fun h => hx (hζB h), map_zero]
    have hI1 : Integrable fun x => d⁻¹ * (Φ (x + d • e) (fderiv ℝ ζ x) - Φ x (fderiv ℝ ζ x)) :=
      (hg3.sub hg1).const_mul _
    have hI2 : Integrable fun x => d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x) -
        a x (fderiv ℝ v (x + d • e)) (fderiv ℝ ζ x)) :=
      (hf3.sub hf2).const_mul _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp only [hΨ]
    rw [integral_sub hI1 hI2, integral_const_mul, integral_const_mul, integral_sub hg3 hg1,
      integral_sub hf3 hf2]
  -- `LHS − RHS = d⁻¹ [(∫ f₃ − ∫ g₃) − (∫ f₁ − ∫ g₁)] = 0`.
  rw [hlhs, hrhs, h7, ← h8]
  ring
/-- Steps 2–3 of the uniform difference-quotient bounds, for one function `g`: if `g` is `C¹` on
an open `U ⊇ K` with `K` compact and `D¹g = iteratedFDeriv ℝ 1 g` is `α`-Hölder on `K` with some
constant `C`, then `Dg = fderiv ℝ g` is bounded on `K` by some `S ≥ 0` and is `α`-Hölder on `K`
with some constant `H ≥ 0`.  (`D¹g(z)` is the image of `Dg(z)` under the linear isometry
`(continuousMultilinearCurryFin1 ℝ E F).symm`; no condition on `α` is needed.) -/
theorem dohr_eb_lhr_dqub_fderiv_consts : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U K : Set E) (g : E → F), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ ≤ C * ‖x - y‖ ^ α) → ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧ (∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ S) ∧ ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U K g hU hK hKU hg hC
  obtain ⟨C, hC⟩ := hC
  -- Step 1: `D¹g(z) = Ψ(Dg(z))` for the linear isometry `Ψ = (continuousMultilinearCurryFin1 ℝ E F).symm`.
  have h1 : ∀ z, iteratedFDeriv ℝ 1 g z = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g z) := by
    intro z
    ext m
    simp [iteratedFDeriv_one_apply]
  -- Step 2: `‖Dg(x) − Dg(y)‖ = ‖Ψ(Dg(x) − Dg(y))‖ = ‖D¹g(x) − D¹g(y)‖`.
  have h2 : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ = ‖iteratedFDeriv ℝ 1 g x - iteratedFDeriv ℝ 1 g y‖ := by
    intro x y
    rw [h1 x, h1 y, ← map_sub, LinearIsometryEquiv.norm_map]
  -- Step 3: `Dg` is continuous on the open `U ⊇ K`, hence bounded by some `S₀` on the compact `K`.
  obtain ⟨S₀, hS₀⟩ := hK.exists_bound_of_continuousOn
    ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  -- Step 4: `S = max S₀ 0` and `H = max C 0`, using `‖x − y‖^α ≥ 0`.
  refine ⟨max S₀ 0, max C 0, le_max_right _ _, le_max_right _ _,
    fun x hx => (hS₀ x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  rw [h2 x y]
  exact (hC x hx y hy).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference-quotient bounds.**
Let `g` be differentiable on an open `U ⊇ B_{4R}(x̄)` with `‖Dg‖ ≤ S` and
`‖Dg(z) − Dg(w)‖ ≤ H ‖z − w‖^α` on `B_{4R}(x̄)`.  If `‖e‖ ≤ 1` and `0 < |d| < R`, then on
`B̆_{2R}(x̄)` the difference quotient `d⁻¹ (g(x + d e) − g(x))` is bounded by `S` and is
`α`-Hölder with constant `H`.
Proof: for `z ∈ B̆_{2R}(x̄)` and `|s| ≤ |d|`, `z + s e ∈ B_{4R}(x̄) ⊆ U`.  The mean value inequality
on this convex ball gives `‖g(x + d e) − g(x)‖ ≤ S |d|`.  For the second bound,
`h(s) = g(x + s e) − g(y + s e)` has `‖h'(s)‖ = ‖(Dg(x + s e) − Dg(y + s e)) e‖ ≤ H ‖x − y‖^α`
for `s` between `0` and `d`, so `‖h(d) − h(0)‖ ≤ H ‖x − y‖^α |d|`; divide by `|d|`. -/
theorem dohr_eb_lhr_dqub_dq_mean_value : ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) (U : Set E) (g : E → F) (xb e : E) (R S H d : ℝ), IsOpen U → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → DifferentiableOn ℝ g U → (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ g z‖ ≤ S) → (∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R), ‖fderiv ℝ g z - fderiv ℝ g w‖ ≤ H * ‖z - w‖ ^ α) → d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖d⁻¹ • (g (x + d • e) - g x)‖ ≤ S ∧ ‖d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y)‖ ≤ H * ‖x - y‖ ^ α := by
  intro E F _ _ _ _ α U g xb e R S H d hU hKU he hg hS hH hd hdR x hx y hy
  have hdpos : 0 < |d| := abs_pos.mpr hd
  -- Step 2: for `z ∈ ball xb (2 * R)` and `|s| ≤ |d|`, `z + s • e ∈ closedBall xb (4 * R)`.
  have hgeo : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |s| * ‖e‖ ≤ |d| * 1 := mul_le_mul hs he (norm_nonneg e) (abs_nonneg d)
        _ = |d| := mul_one _
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by congr 1; abel
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith [abs_nonneg d]
  -- Step 3: `g` is differentiable at every point of `closedBall xb (4 * R) ⊆ U`.
  have hdiff : ∀ z ∈ closedBall xb (4 * R), DifferentiableAt ℝ g z := fun z hz =>
    (hg z (hKU hz)).differentiableAt (hU.mem_nhds (hKU hz))
  have hx0 : x ∈ closedBall xb (4 * R) := by
    have h := hgeo x hx 0 (by simp)
    rwa [zero_smul, add_zero] at h
  constructor
  · -- Step 4: part (a), the mean value inequality on `closedBall xb (4 * R)`.
    have hmv : ‖g (x + d • e) - g x‖ ≤ S * ‖x + d • e - x‖ :=
      (convex_closedBall xb (4 * R)).norm_image_sub_le_of_norm_fderiv_le hdiff hS hx0
        (hgeo x hx d le_rfl)
    have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx0)
    have hde : ‖d • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg d) he
    rw [add_sub_cancel_left] at hmv
    rw [norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖g (x + d • e) - g x‖ ≤ S * ‖d • e‖ := hmv
      _ ≤ S * |d| := mul_le_mul_of_nonneg_left hde hS0
      _ = |d| * S := mul_comm _ _
  · -- Steps 5–8: part (b), the mean value inequality for `s ↦ g (x + s • e) - g (y + s • e)`.
    have hI : ∀ s ∈ uIcc (0 : ℝ) d, |s| ≤ |d| := by
      intro s hs
      simpa using Set.abs_sub_left_of_mem_uIcc hs
    have hlin : ∀ (z : E) (s : ℝ), HasDerivAt (fun σ : ℝ => z + σ • e) e s := by
      intro z s
      simpa using ((hasDerivAt_id s).smul_const e).const_add z
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) d, HasDerivWithinAt
        (fun σ : ℝ => g (x + σ • e) - g (y + σ • e))
        (fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e) (uIcc (0 : ℝ) d) s := by
      intro s hs
      have hxs := hdiff _ (hgeo x hx s (hI s hs))
      have hys := hdiff _ (hgeo y hy s (hI s hs))
      exact ((hxs.hasFDerivAt.comp_hasDerivAt s (hlin x s)).sub
        (hys.hasFDerivAt.comp_hasDerivAt s (hlin y s))).hasDerivWithinAt
    have hbound : ∀ s ∈ uIcc (0 : ℝ) d,
        ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖ ≤ H * ‖x - y‖ ^ α := by
      intro s hs
      have hxy : x + s • e - (y + s • e) = x - y := add_sub_add_right_eq_sub x y (s • e)
      calc ‖fderiv ℝ g (x + s • e) e - fderiv ℝ g (y + s • e) e‖
          = ‖(fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)) e‖ := by rw [sub_apply]
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ g (x + s • e) - fderiv ℝ g (y + s • e)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) he
        _ ≤ H * ‖x + s • e - (y + s • e)‖ ^ α :=
            hH _ (hgeo x hx s (hI s hs)) _ (hgeo y hy s (hI s hs))
        _ = H * ‖x - y‖ ^ α := by rw [hxy]
    have hmv := (convex_uIcc (0 : ℝ) d).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] at hmv
    have hrw : d⁻¹ • (g (x + d • e) - g x) - d⁻¹ • (g (y + d • e) - g y) =
        d⁻¹ • ((g (x + d • e) - g (y + d • e)) - (g x - g y)) := by
      rw [← smul_sub]; congr 1; abel
    rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hdpos]
    calc ‖(g (x + d • e) - g (y + d • e)) - (g x - g y)‖ ≤ H * ‖x - y‖ ^ α * |d| := hmv
      _ = |d| * (H * ‖x - y‖ ^ α) := mul_comm _ _
/-- Difference-quotient bounds in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second
assertion (p. 127): on a finite-dimensional real normed space `L`, real linear and bilinear forms
are bounded by `C` times their largest value on finitely many test vectors `b r`.  Take a basis
`b` of `L`; its coordinates `π r` are continuous, and `c = Σ_r ‖π r‖` gives
`|b.repr P r| ≤ c ‖P‖`.  Expanding `P` in the basis gives `|f P| ≤ N c m ‖P‖`, expanding in both
arguments gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`, and `C = N c + N² c²`. -/
theorem dohr_eb_lhr_dqub_form_coords : ∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (b : Fin N → L) (C : ℝ), 0 ≤ C ∧ (∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) → ∀ P, |f P| ≤ C * m * ‖P‖) ∧ ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) → (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) → ∀ Q P, |β Q P| ≤ C * m * ‖Q‖ * ‖P‖ := by
  intro L _ _ _
  -- Step 1: a basis `b` of `L` indexed by `Fin N` (`N = finrank ℝ L`).
  obtain ⟨N, ⟨b⟩⟩ : ∃ N : ℕ, Nonempty (Module.Basis (Fin N) ℝ L) :=
    ⟨_, ⟨Module.finBasis ℝ L⟩⟩
  -- Step 2: the coordinates `π r = b.coord r` are continuous as `L` is finite-dimensional, and
  -- `c = Σ_r ‖π r‖` gives `|b.repr P r| ≤ c ‖P‖`.
  obtain ⟨c, hc0, hcoord⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ r P, |b.repr P r| ≤ c * ‖P‖ := by
    let π : Fin N → L →L[ℝ] ℝ := fun r => LinearMap.toContinuousLinearMap (b.coord r)
    refine ⟨∑ r, ‖π r‖, Finset.sum_nonneg fun r _ => norm_nonneg _, fun r P => ?_⟩
    have hπ : π r P = b.repr P r := by simp [π]
    calc |b.repr P r| = ‖π r P‖ := by rw [hπ, Real.norm_eq_abs]
      _ ≤ ‖π r‖ * ‖P‖ := (π r).le_opNorm P
      _ ≤ (∑ t, ‖π t‖) * ‖P‖ := mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun t _ => norm_nonneg (π t)) (Finset.mem_univ r)) (norm_nonneg P)
  -- Step 3: a linear `f` is determined by its basis values, `f P = Σ_r b.repr P r · f (b r)`.
  have hexp : ∀ f : L → ℝ, IsLinearMap ℝ f → ∀ P, f P = ∑ r, b.repr P r * f (b r) := by
    intro f hf P
    calc f P = IsLinearMap.mk' f hf (∑ r, b.repr P r • b r) := by
          rw [b.sum_repr, IsLinearMap.mk'_apply]
      _ = ∑ r, b.repr P r * f (b r) := by
          simp only [map_sum, map_smul, IsLinearMap.mk'_apply, smul_eq_mul]
  -- Step 4: the linear bound `|f P| ≤ N c m ‖P‖`.
  have hlin : ∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) →
      ∀ P, |f P| ≤ N * c * m * ‖P‖ := by
    intro f m hf hm hb P
    rw [hexp f hf P]
    calc |∑ r, b.repr P r * f (b r)| ≤ ∑ r, |b.repr P r * f (b r)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : Fin N, c * ‖P‖ * m := by
          gcongr with r
          rw [abs_mul]
          exact mul_le_mul (hcoord r P) (hb r) (abs_nonneg _) (by positivity)
      _ = N * c * m * ‖P‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- Steps 5–6: expanding `β` in each argument, i.e. the linear bound for each `β (b r)` and then
  -- for `Q ↦ β Q P`, gives `|β Q P| ≤ N² c² m ‖Q‖ ‖P‖`.
  have hbil : ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) →
      (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) →
      ∀ Q P, |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by
    intro β m hβ₁ hβ₂ hm hb Q P
    have hr : ∀ r, |β (b r) P| ≤ N * c * m * ‖P‖ := fun r =>
      hlin (β (b r)) m (hβ₂ (b r)) hm (hb r) P
    calc |β Q P| ≤ N * c * (N * c * m * ‖P‖) * ‖Q‖ :=
          hlin (fun Q => β Q P) (N * c * m * ‖P‖) (hβ₁ P) (by positivity) hr Q
      _ = N * c * (N * c) * m * ‖Q‖ * ‖P‖ := by ring
  -- Step 7: `C = N c + N² c²` serves for both bounds.
  refine ⟨N, b, N * c + N * c * (N * c), by positivity, fun f m hf hm hb P => ?_,
    fun β m hβ₁ hβ₂ hm hb Q P => ?_⟩
  · calc |f P| ≤ N * c * m * ‖P‖ := hlin f m hf hm hb P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖P‖ := by
          rw [add_mul, add_mul]
          exact le_add_of_nonneg_right (by positivity)
  · calc |β Q P| ≤ N * c * (N * c) * m * ‖Q‖ * ‖P‖ := hbil β m hβ₁ hβ₂ hm hb Q P
      _ ≤ (N * c + N * c * (N * c)) * m * ‖Q‖ * ‖P‖ := by
          rw [add_mul, add_mul, add_mul]
          exact le_add_of_nonneg_left (by positivity)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a locally
`C^{1,α}` map.**  Let `v` be locally `C^{1,α}` on the open set `U ⊇ B_{4R}(xb)` and `‖e‖ ≤ 1`.
There is `S` such that for every `0 < |d| < R` the difference quotient
`w_d(z) = d⁻¹ (v(z + d e) − v(z))` satisfies the following on `B̆_{2R}(xb)`: `‖w_d‖ ≤ S`, `w_d` is
`C¹`, `Dw_d(x) = d⁻¹ (Dv(x + d e) − Dv(x))`, and `Dw_d` is `α`-Hölder.
Proof: `dohr_eb_lhr_dqub_fderiv_consts` on the compact set `K₀ = B_{4R}(xb)` gives a bound `S_v`
and a Hölder constant `H_v` for `Dv` on `K₀`; put `S = S_v`.  For `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`,
`‖z + s e − xb‖ < 2R + R ≤ 4R`, so `z` and `z + d e` lie in `K₀ ⊆ U`.  The bound on `w_d` is part
(a) of `dohr_eb_lhr_dqub_dq_mean_value`.  The `C¹` property and the derivative formula follow from
the chain rule for the translation `z ↦ z + d e`.  Finally
`Dw_d(x) − Dw_d(y) = d⁻¹ ((Dv(x + d e) − Dv(y + d e)) − (Dv(x) − Dv(y)))` has norm at most
`2 H_v |d|⁻¹ ‖x − y‖^α`. -/
theorem dohr_eb_lhr_dqub_wd_props : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → IsLocallyHolderCkα 1 α v U → ∃ S : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ S) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ ∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α := by
  intro n ℓ α U v xb e R hU hR hsub he hv
  -- Step 1: `v` is `C¹` on `U`, and `D¹v` is `α`-Hölder on the compact set `K₀ = B_{4R}(xb) ⊆ U`.
  have hC1 : ContDiffOn ℝ 1 v U := by simpa using hv.1
  have hK0 : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  -- Step 2: `‖Dv‖ ≤ S_v` and `‖Dv(z) − Dv(w)‖ ≤ H_v ‖z − w‖^α` on `K₀`.  The constant
  -- `S := S_v` does not depend on `d`.
  obtain ⟨Sv, Hv, -, -, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U (closedBall xb (4 * R)) v hU hK0
      hsub hC1 (hv.2 _ hK0 hsub)
  refine ⟨Sv, fun d hd hdR => ?_⟩
  -- Step 3: `z + s e ∈ K₀` for `z ∈ B̆_{2R}(xb)` and `|s| ≤ |d|`; in particular `z, z + d e ∈ K₀`.
  have hgeom : ∀ z ∈ ball xb (2 * R), ∀ s : ℝ, |s| ≤ |d| → z + s • e ∈ closedBall xb (4 * R) := by
    intro z hz s hs
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    have hse : ‖s • e‖ ≤ |d| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg s) he).trans hs
    calc ‖z + s • e - xb‖ = ‖(z - xb) + s • e‖ := by rw [sub_add_eq_add_sub]
      _ ≤ ‖z - xb‖ + ‖s • e‖ := norm_add_le _ _
      _ ≤ 4 * R := by linarith
  have hz0 : ∀ z ∈ ball xb (2 * R), z ∈ closedBall xb (4 * R) := fun z hz => by
    simpa using hgeom z hz 0 (by simp)
  have hzd : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := fun z hz =>
    hgeom z hz d le_rfl
  -- Step 4: claim (i) is part (a) of `dohr_eb_lhr_dqub_dq_mean_value` (taking `y = x`).
  have hdiff : DifferentiableOn ℝ v U := hC1.differentiableOn one_ne_zero
  have hmv := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) (Rn ℓ) α U v xb e R Sv Hv d hU hsub
    he hdiff hSv hHv hd hdR
  -- Step 6: `w_d` has derivative `d⁻¹ (Dv(x + d e) − Dv(x))` at every `x ∈ B̆_{2R}(xb)`.
  have hderiv : ∀ x ∈ ball xb (2 * R), HasFDerivAt (fun z => d⁻¹ • (v (z + d • e) - v z))
      (d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) x := by
    intro x hx
    have hxU : x ∈ U := hsub (hz0 x hx)
    have hxdU : x + d • e ∈ U := hsub (hzd x hx)
    have hv0 : DifferentiableAt ℝ v x := (hdiff x hxU).differentiableAt (hU.mem_nhds hxU)
    have hv1 : DifferentiableAt ℝ v (x + d • e) :=
      (hdiff _ hxdU).differentiableAt (hU.mem_nhds hxdU)
    have hcomp : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (x + d • e)) x := by
      simpa [Function.comp_def] using
        hv1.hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (d • e))
    exact (hcomp.sub hv0.hasFDerivAt).const_smul d⁻¹
  refine ⟨fun x hx => (hmv x hx x hx).1, ?_, fun x hx => (hderiv x hx).fderiv, ?_⟩
  · -- Step 5: claim (ii), since `w_d = d⁻¹ • (v ∘ τ − v)` for the translation `τ z = z + d e`.
    have hτ : ContDiffOn ℝ 1 (fun z : Rn n => z + d • e) (ball xb (2 * R)) :=
      (contDiff_id.add contDiff_const).contDiffOn
    have hτU : MapsTo (fun z : Rn n => z + d • e) (ball xb (2 * R)) U := fun z hz =>
      hsub (hzd z hz)
    have h1 : ContDiffOn ℝ 1 (fun z => v (z + d • e)) (ball xb (2 * R)) := hC1.comp hτ hτU
    have h2 : ContDiffOn ℝ 1 v (ball xb (2 * R)) := hC1.mono fun z hz => hsub (hz0 z hz)
    exact (h1.sub h2).const_smul d⁻¹
  · -- Step 7: claim (iv) with `K = 2 H_v |d|⁻¹`, using the Hölder bound of `Dv` at the four points
    -- `x, y, x + d e, y + d e ∈ K₀`.
    refine ⟨2 * Hv * |d|⁻¹, fun x hx y hy => ?_⟩
    rw [(hderiv x hx).fderiv, (hderiv y hy).fderiv]
    have heq : d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x) -
        d⁻¹ • (fderiv ℝ v (y + d • e) - fderiv ℝ v y) =
        d⁻¹ • ((fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)) :=
      (smul_sub _ _ _).symm.trans (by rw [sub_sub_sub_comm])
    have h1 := hHv _ (hzd x hx) _ (hzd y hy)
    rw [add_sub_add_right_eq_sub] at h1
    have h2 := hHv _ (hz0 x hx) _ (hz0 y hy)
    rw [heq, norm_smul, norm_inv, Real.norm_eq_abs]
    calc |d|⁻¹ * ‖(fderiv ℝ v (x + d • e) - fderiv ℝ v (y + d • e)) -
          (fderiv ℝ v x - fderiv ℝ v y)‖
        ≤ |d|⁻¹ * (Hv * ‖x - y‖ ^ α + Hv * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h1 h2))
            (inv_nonneg.2 (abs_nonneg d))
      _ = 2 * Hv * |d|⁻¹ * ‖x - y‖ ^ α := by ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `d`-uniform Hölder bound for the
forcing term of the difference-quotient system.**  Let `L = L(ℝⁿ, ℝ^ℓ)`, `U ⊇ B_{4R}(xb)` open,
`‖e‖ ≤ 1`, let the coefficients `x ↦ a(x)[P][Q]` and `x ↦ Φ(x)[P]` be `C^{1,α}` in `U` and `v` be
`C^{1,α}` in `U`.  For `0 < |d| < R` put
`F_d(x, P) = d⁻¹ (Φ(x + d e)[P] − Φ(x)[P])
  − d⁻¹ (a(x + d e)[Dv(x + d e)][P] − a(x)[Dv(x + d e)][P])`.
Then `|F_d(x, P) − F_d(y, P)| ≤ M ‖x − y‖^α ‖P‖` on `B̆_{2R}(xb)` with `M` independent of `d`.
Proof: `dohr_eb_lhr_dqub_form_coords` gives a spanning family `b` of `L` and a constant `C`
bounding linear and bilinear forms by their values on `b`.  On `K₀ = B_{4R}(xb)`,
`dohr_eb_lhr_dqub_fderiv_consts` gives a common bound `S'` and a common Hölder constant `H` for
the derivatives of the scalar coefficients `a(·)[b_r][b_t]`, `Φ(·)[b_r]`, and `S_v`, `H_v` for
`Dv`; put `M = C (H + H S_v + S' H_v)`.  The mean value inequality
`dohr_eb_lhr_dqub_dq_mean_value` bounds the difference quotients of these coefficients by `S'`
and their differences at `x, y` by `H ‖x − y‖^α`.  With
`Q_x = Dv(x + d e)` and `Q_y = Dv(y + d e)`,
`F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)` for the linear form `T` and the
bilinear forms `β₁`, `β₂` built from these difference quotients, and the coordinate bounds give
`|T(P)| + |β₁(Q_x, P)| + |β₂(Q_x − Q_y, P)| ≤ M ‖x − y‖^α ‖P‖`. -/
theorem dohr_eb_lhr_dqub_forcing_holder : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R hU hR hK0U he ha hΦ hv
  -- Step 1: a spanning family `b` of `L` and the coordinate constant `C`.
  obtain ⟨N, b, C, hC, hD1, hD2⟩ :=
    Submission.dohr_eb_lhr_dqub_form_coords (Rn n →L[ℝ] Rn ℓ)
  -- Step 2: derivative bounds and Hölder constants of the components on `K₀ = B_{4R}(xb)`.
  have hK0c : IsCompact (closedBall xb (4 * R)) := isCompact_closedBall xb (4 * R)
  have hAa : ∀ r t : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => a z (b r) (b t)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => a z (b r) (b t)) z - fderiv ℝ (fun z => a z (b r) (b t)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r t =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => a z (b r) (b t)) hU hK0c
      hK0U (ha (b r) (b t)).1 ((ha (b r) (b t)).2 _ hK0c hK0U)
  have hAΦ : ∀ r : Fin N, ∃ S H : ℝ, 0 ≤ S ∧ 0 ≤ H ∧
      (∀ z ∈ closedBall xb (4 * R), ‖fderiv ℝ (fun z => Φ z (b r)) z‖ ≤ S) ∧
      ∀ z ∈ closedBall xb (4 * R), ∀ w ∈ closedBall xb (4 * R),
        ‖fderiv ℝ (fun z => Φ z (b r)) z - fderiv ℝ (fun z => Φ z (b r)) w‖ ≤
          H * ‖z - w‖ ^ α := fun r =>
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) ℝ α U _ (fun z => Φ z (b r)) hU hK0c
      hK0U (hΦ (b r)).1 ((hΦ (b r)).2 _ hK0c hK0U)
  obtain ⟨Sv, Hv, hSv0, hHv0, hSv, hHv⟩ :=
    Submission.dohr_eb_lhr_dqub_fderiv_consts (Rn n) (Rn ℓ) α U _ v hU hK0c hK0U
      (by simpa using hv.1) (hv.2 _ hK0c hK0U)
  choose Sa Ha hSa0 hHa0 hSa hHa using hAa
  choose SΦ HΦ hSΦ0 hHΦ0 hSΦ hHΦ using hAΦ
  -- Step 3: uniform constants `S'`, `H` for all components; `M` is fixed before `d`.
  set S' : ℝ := ∑ r, ∑ t, Sa r t + ∑ r, SΦ r
  set H : ℝ := ∑ r, ∑ t, Ha r t + ∑ r, HΦ r
  have hSa_sum0 : 0 ≤ ∑ r, ∑ t, Sa r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t
  have hHa_sum0 : 0 ≤ ∑ r, ∑ t, Ha r t :=
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t
  have hSΦ_sum0 : 0 ≤ ∑ r, SΦ r := Finset.sum_nonneg fun r _ => hSΦ0 r
  have hHΦ_sum0 : 0 ≤ ∑ r, HΦ r := Finset.sum_nonneg fun r _ => hHΦ0 r
  have hS'0 : 0 ≤ S' := add_nonneg hSa_sum0 hSΦ_sum0
  have hH0 : 0 ≤ H := add_nonneg hHa_sum0 hHΦ_sum0
  have hSa_le : ∀ r t, Sa r t ≤ S' := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hSa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Sa r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hSa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hSΦ_sum0))
  have hHa_le : ∀ r t, Ha r t ≤ H := fun r t =>
    le_trans (Finset.single_le_sum (fun t _ => hHa0 r t) (Finset.mem_univ t))
      (le_trans (Finset.single_le_sum (f := fun r => ∑ t, Ha r t)
        (fun r _ => Finset.sum_nonneg fun t _ => hHa0 r t) (Finset.mem_univ r))
        (le_add_of_nonneg_right hHΦ_sum0))
  have hSΦ_le : ∀ r, SΦ r ≤ S' := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hSΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hSa_sum0)
  have hHΦ_le : ∀ r, HΦ r ≤ H := fun r =>
    le_trans (Finset.single_le_sum (fun r _ => hHΦ0 r) (Finset.mem_univ r))
      (le_add_of_nonneg_left hHa_sum0)
  refine ⟨C * (H + H * Sv + S' * Hv), ?_⟩
  intro d hd hdR x hx y hy P
  -- Step 4: `x + d e, y + d e ∈ K₀`, and the bounds on `Q_x = Dv(x + d e)`, `Q_y = Dv(y + d e)`.
  have hshift : ∀ z ∈ ball xb (2 * R), z + d • e ∈ closedBall xb (4 * R) := by
    intro z hz
    rw [mem_closedBall]
    rw [mem_ball] at hz
    have h1 : dist (z + d • e) xb ≤ dist z xb + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖z + d • e - xb‖ = ‖(z - xb) + d • e‖ := by congr 1; abel
        _ ≤ ‖z - xb‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * 1 := mul_le_mul_of_nonneg_left he (abs_nonneg d)
        _ ≤ R := by linarith
    linarith
  have hxK := hshift x hx
  have hyK := hshift y hy
  set t : ℝ := ‖x - y‖ ^ α
  have ht0 : 0 ≤ t := Real.rpow_nonneg (norm_nonneg _) α
  set Qx := fderiv ℝ v (x + d • e)
  set Qy := fderiv ℝ v (y + d • e)
  have hQxb : ‖Qx‖ ≤ Sv := hSv _ hxK
  have hQxy : ‖Qx - Qy‖ ≤ Hv * t := by
    have := hHv _ hxK _ hyK
    rwa [add_sub_add_right_eq_sub] at this
  -- Step 5: the scalar difference quotients of the components, by the mean value inequality
  -- `dohr_eb_lhr_dqub_dq_mean_value` with the common constants `S'` and `H`.
  have hBa : ∀ r t', |d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ S' ∧
      |d⁻¹ * (a (x + d • e) (b r) (b t') - a x (b r) (b t')) -
        d⁻¹ * (a (y + d • e) (b r) (b t') - a y (b r) (b t'))| ≤ H * t := by
    intro r t'
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => a z (b r) (b t')) xb e R S' H d hU hK0U he
      ((ha (b r) (b t')).1.differentiableOn one_ne_zero)
      (fun z hz => (hSa r t' z hz).trans (hSa_le r t'))
      (fun z hz w hw => (hHa r t' z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHa_le r t') (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    refine ⟨?_, ?_⟩
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB y hy y hy).1
    · simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  have hBΦ : ∀ r, |d⁻¹ * (Φ (x + d • e) (b r) - Φ x (b r)) -
      d⁻¹ * (Φ (y + d • e) (b r) - Φ y (b r))| ≤ H * t := by
    intro r
    have hB := Submission.dohr_eb_lhr_dqub_dq_mean_value (Rn n) ℝ α U
      (fun z => Φ z (b r)) xb e R S' H d hU hK0U he
      ((hΦ (b r)).1.differentiableOn one_ne_zero)
      (fun z hz => (hSΦ r z hz).trans (hSΦ_le r))
      (fun z hz w hw => (hHΦ r z hz w hw).trans
        (mul_le_mul_of_nonneg_right (hHΦ_le r) (Real.rpow_nonneg (norm_nonneg _) α)))
      hd hdR
    simpa [smul_eq_mul, Real.norm_eq_abs] using (hB x hx y hy).2
  -- Step 6: the linear form `T` and the bilinear forms `β₁`, `β₂`.
  let T : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P' =>
    d⁻¹ * (Φ (x + d • e) P' - Φ x P') - d⁻¹ * (Φ (y + d • e) P' - Φ y P')
  let β1 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (x + d • e) Q P' - a x Q P') - d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  let β2 : (Rn n →L[ℝ] Rn ℓ) → (Rn n →L[ℝ] Rn ℓ) → ℝ := fun Q P' =>
    d⁻¹ * (a (y + d • e) Q P' - a y Q P')
  have hTlin : IsLinearMap ℝ T := by
    constructor
    · intro P1 P2; simp only [T, map_add]; ring
    · intro c P1; simp only [T, map_smul, smul_eq_mul]; ring
  have hβ1l : ∀ P', IsLinearMap ℝ (fun Q => β1 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β1, map_add, add_apply]; ring
    · intro c Q1; simp only [β1, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ1r : ∀ Q, IsLinearMap ℝ (β1 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β1, map_add]; ring
    · intro c P1; simp only [β1, map_smul, smul_eq_mul]; ring
  have hβ2l : ∀ P', IsLinearMap ℝ (fun Q => β2 Q P') := by
    intro P'; constructor
    · intro Q1 Q2; simp only [β2, map_add, add_apply]; ring
    · intro c Q1; simp only [β2, map_smul, smul_apply, smul_eq_mul]; ring
  have hβ2r : ∀ Q, IsLinearMap ℝ (β2 Q) := by
    intro Q; constructor
    · intro P1 P2; simp only [β2, map_add]; ring
    · intro c P1; simp only [β2, map_smul, smul_eq_mul]; ring
  -- Step 7: coordinate bounds for `T(P)`, `β₁(Q_x, P)` and `β₂(Q_x − Q_y, P)`.
  have hT : |T P| ≤ C * (H * t) * ‖P‖ :=
    hD1 T (H * t) hTlin (mul_nonneg hH0 ht0) (fun r => hBΦ r) P
  have hβ1 : |β1 Qx P| ≤ C * (H * t) * ‖Qx‖ * ‖P‖ :=
    hD2 β1 (H * t) hβ1l hβ1r (mul_nonneg hH0 ht0) (fun r t' => (hBa r t').2) Qx P
  have hβ2 : |β2 (Qx - Qy) P| ≤ C * S' * ‖Qx - Qy‖ * ‖P‖ :=
    hD2 β2 S' hβ2l hβ2r hS'0 (fun r t' => (hBa r t').1) (Qx - Qy) P
  -- Step 8: `F_d(x, P) − F_d(y, P) = T(P) − β₁(Q_x, P) − β₂(Q_x − Q_y, P)`.
  have hid : (d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) Qx P - a x Qx P)) -
      (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) Qy P - a y Qy P)) =
      T P - β1 Qx P - β2 (Qx - Qy) P := by
    simp only [T, β1, β2, map_sub, sub_apply]; ring
  -- Step 9: the triangle inequality.
  rw [hid]
  have hP0 : 0 ≤ ‖P‖ := norm_nonneg P
  have hCH : 0 ≤ C * (H * t) := mul_nonneg hC (mul_nonneg hH0 ht0)
  have hCS : 0 ≤ C * S' := mul_nonneg hC hS'0
  have e1 : |β1 Qx P| ≤ C * (H * t) * Sv * ‖P‖ :=
    hβ1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxb hCH) hP0)
  have e2 : |β2 (Qx - Qy) P| ≤ C * S' * (Hv * t) * ‖P‖ :=
    hβ2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQxy hCS) hP0)
  calc |T P - β1 Qx P - β2 (Qx - Qy) P|
      ≤ |T P - β1 Qx P| + |β2 (Qx - Qy) P| := abs_sub _ _
    _ ≤ |T P| + |β1 Qx P| + |β2 (Qx - Qy) P| := by
        gcongr; exact abs_sub _ _
    _ ≤ C * (H * t) * ‖P‖ + C * (H * t) * Sv * ‖P‖ + C * S' * (Hv * t) * ‖P‖ := by
        gcongr
    _ = C * (H + H * Sv + S' * Hv) * t * ‖P‖ := by ring
/-- Difference-quotient step in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
`d`-uniform bounds for `w_d = d⁻¹ (v(· + d e) - v)` and for the forcing term `F_d` of its system on
`B̆_{2R}(xb)`.  Claims (i)–(iv) hold with the `d`-independent bound `S` of
`dohr_eb_lhr_dqub_wd_props`, claim (v) with the `d`-independent constant `M'` of
`dohr_eb_lhr_dqub_forcing_holder`; `M := max S M'` serves both, as `‖x - y‖ ^ α * ‖P‖ ≥ 0`. -/
theorem dohr_eb_lhr_dq_uniform_bounds : ∀ (n ℓ : ℕ) (α : ℝ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (xb e : Rn n) (R : ℝ), 0 < α → α ≤ 1 → IsOpen U → 0 < R → closedBall xb (4 * R) ⊆ U → ‖e‖ ≤ 1 → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα 1 α v U → ∃ M : ℝ, ∀ d : ℝ, d ≠ 0 → |d| < R → (∀ x ∈ ball xb (2 * R), ‖d⁻¹ • (v (x + d • e) - v x)‖ ≤ M) ∧ ContDiffOn ℝ 1 (fun z => d⁻¹ • (v (z + d • e) - v z)) (ball xb (2 * R)) ∧ (∀ x ∈ ball xb (2 * R), fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x = d⁻¹ • (fderiv ℝ v (x + d • e) - fderiv ℝ v x)) ∧ (∃ K : ℝ, ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ‖fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) x - fderiv ℝ (fun z => d⁻¹ • (v (z + d • e) - v z)) y‖ ≤ K * ‖x - y‖ ^ α) ∧ ∀ x ∈ ball xb (2 * R), ∀ y ∈ ball xb (2 * R), ∀ P : Rn n →L[ℝ] Rn ℓ, |(d⁻¹ * (Φ (x + d • e) P - Φ x P) - d⁻¹ * (a (x + d • e) (fderiv ℝ v (x + d • e)) P - a x (fderiv ℝ v (x + d • e)) P)) - (d⁻¹ * (Φ (y + d • e) P - Φ y P) - d⁻¹ * (a (y + d • e) (fderiv ℝ v (y + d • e)) P - a y (fderiv ℝ v (y + d • e)) P))| ≤ M * ‖x - y‖ ^ α * ‖P‖ := by
  intro n ℓ α U a Φ v xb e R _ _ hU hR hBU he ha hΦ hv
  -- Steps 6–8: `w_d` is bounded by `S`, `C¹`, has the stated derivative, and `Dw_d` is Hölder.
  obtain ⟨S, hS⟩ := Submission.dohr_eb_lhr_dqub_wd_props n ℓ α U v xb e R hU hR hBU he hv
  -- Step 9: the forcing term is `α`-Hölder in `x` with the constant `M'`.
  obtain ⟨M', hM'⟩ :=
    Submission.dohr_eb_lhr_dqub_forcing_holder n ℓ α U a Φ v xb e R hU hR hBU he ha hΦ hv
  -- Step 10: `M := max S M'` does not depend on `d`.
  refine ⟨max S M', fun d hd hdR => ?_⟩
  obtain ⟨hw, hC1, hDw, hHol⟩ := hS d hd hdR
  refine ⟨fun x hx => (hw x hx).trans (le_max_left S M'), hC1, hDw, hHol,
    fun x hx y hy P => (hM' d hd hdR x hx y hy P).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right S M')
    (Real.rpow_nonneg (norm_nonneg (x - y)) α)) (norm_nonneg P)
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients of a `C¹` map
into a normed space.**
If `g : ℝⁿ → E` is `C¹` on an open `U` and `K ⊆ U` is compact, then for every direction `e` the
difference quotients `d⁻¹ (g(x + d e) − g(x))` converge to `Dg(x) e` uniformly on `K` as `d → 0`,
`d ≠ 0`.  The codomain `E` is an arbitrary real normed space (e.g. `L(ℝⁿ, ℝ^ℓ)` for `g = Dv`).
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Dg` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Dg(w) − Dg(x)‖ < η/(|e| + 1)` whenever
`w, x ∈ K_ε` and `|w − x| < θ`.  For `0 < |d| < min(ε, θ)/(|e| + 1)` and `x ∈ K`, the segment
`[x, x + d e]` lies in `B_{|d e|}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Dg(x)` gives `‖g(x + d e) − g(x) − Dg(x)(d e)‖ ≤ η |d| |e|/(|e| + 1)`; dividing by `|d|`,
`‖Dg(x) e − d⁻¹ (g(x + d e) − g(x))‖ ≤ η |e|/(|e| + 1) < η`. -/
theorem dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn n → E) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 g U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (g (x + d • e) - g x)) (fun x => fderiv ℝ g x e) (𝓝[≠] 0) K := by
  intro n E _ _ g U K e hU hg hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `g` is differentiable on `U` and `Dg` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ g) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- Step 3: given `η > 0`, choose `θ` and restrict to `0 < |d| < min ε θ / (‖e‖ + 1)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  -- Step 4: the segment `[x, x + d • e]` lies in `closedBall x ‖d • e‖ ⊆ K_ε ⊆ U`.
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  -- Step 5: the mean value inequality with the fixed linear map `Dg(x)`.
  have hmvt : ‖g (x + d • e) - g x - fderiv ℝ g x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  -- Step 6: divide by `d ≠ 0`.
  rw [dist_eq_norm]
  have hrw : fderiv ℝ g x e - d⁻¹ • (g (x + d • e) - g x) =
      -(d⁻¹ • (g (x + d • e) - g x - fderiv ℝ g x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (g (x + d • e) - g x) (d • fderiv ℝ g x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖g (x + d • e) - g x - fderiv ℝ g x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): difference quotients.**
If `f` is `C¹` on an open `U` and `K ⊆ U` is compact, then for every direction `e` the difference
quotients `g_d(x) = d⁻¹ (f(x + d e) − f(x))` converge to `Df(x) e` uniformly on `K` as `d → 0`,
`d ≠ 0`.
Proof: `K` has a compact closed thickening `K_ε ⊆ U`, on which `Df` is uniformly continuous
(Heine–Cantor).  Given `η > 0`, pick `θ > 0` with `‖Df(w) − Df(x)‖ < η/(|e| + 1)` whenever
`w, x ∈ K_ε` and `|w − x| < θ`.  For `0 < |d| < min(ε, θ)/(|e| + 1)` and `x ∈ K`, the segment
`[x, x + d e]` lies in `B_{|d e|}(x) ⊆ K_ε`, so the mean value inequality with the fixed linear map
`Df(x)` gives `|f(x + d e) − f(x) − Df(x)(d e)| ≤ η |d| |e|/(|e| + 1)`; dividing by `|d|`,
`|Df(x) e − g_d(x)| ≤ η |e|/(|e| + 1) < η`. -/
theorem dohr_eb_dql_diffQuot_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (f (x + d • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K := by
  intro n ℓ f U K e hU hf hK hKU
  -- Step 1: a compact closed thickening `K_ε = cthickening ε K` of `K` inside `U`.
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening ε K) := hK.cthickening
  -- Step 2: `f` is differentiable on `U` and `Df` is uniformly continuous on `K_ε`.
  have hcont : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc : UniformContinuousOn (fderiv ℝ f) (cthickening ε K) :=
    hK'.uniformContinuousOn_of_continuous (hcont.mono hεU)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- Step 3: given `η > 0`, choose `θ` and restrict to `0 < |d| < min ε θ / (‖e‖ + 1)`.
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.uniformContinuousOn_iff] at huc
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨θ, hθ, hθK⟩ := huc (η / (‖e‖ + 1)) (div_pos hη he1)
  have hpos : 0 < min ε θ / (‖e‖ + 1) := div_pos (lt_min hε hθ) he1
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < min ε θ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with d hd
    simpa [Real.dist_eq] using hd
  filter_upwards [hev, self_mem_nhdsWithin] with d hd hd0
  have hd0' : d ≠ 0 := hd0
  intro x hx
  -- Step 4: the segment `[x, x + d • e]` lies in `closedBall x ‖d • e‖ ⊆ K_ε ⊆ U`.
  have hde : ‖d • e‖ < min ε θ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
      _ < min ε θ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = min ε θ := div_mul_cancel₀ _ he1.ne'
  have hball : closedBall x ‖d • e‖ ⊆ cthickening ε K :=
    (closedBall_subset_closedBall (hde.le.trans (min_le_left _ _))).trans
      (closedBall_subset_cthickening hx ε)
  have hxde : x + d • e ∈ closedBall x ‖d • e‖ := by
    rw [mem_closedBall, dist_eq_norm]; simp
  have hseg : segment ℝ x (x + d • e) ⊆ closedBall x ‖d • e‖ :=
    (convex_closedBall x _).segment_subset (mem_closedBall_self (norm_nonneg _)) hxde
  have hxK' : x ∈ cthickening ε K := self_subset_cthickening K hx
  -- Step 5: the mean value inequality with the fixed linear map `Df(x)`.
  have hmvt : ‖f (x + d • e) - f x - fderiv ℝ f x ((x + d • e) - x)‖ ≤
      η / (‖e‖ + 1) * ‖(x + d • e) - x‖ := by
    refine (convex_segment x (x + d • e)).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hεU (hball (hseg hw)))) (fun w hw => ?_) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _)
    have hw := hseg hw
    have hwx : dist w x < θ := by
      rw [mem_closedBall] at hw
      exact hw.trans_lt (hde.trans_le (min_le_right _ _))
    have := hθK w (hball hw) x hxK' hwx
    rw [dist_eq_norm] at this
    exact this.le
  have hsub : (x + d • e) - x = d • e := by abel
  rw [hsub] at hmvt
  -- Step 6: divide by `d ≠ 0`.
  rw [dist_eq_norm]
  have hrw : fderiv ℝ f x e - d⁻¹ • (f (x + d • e) - f x) =
      -(d⁻¹ • (f (x + d • e) - f x - fderiv ℝ f x (d • e))) := by
    rw [map_smul, smul_sub d⁻¹ (f (x + d • e) - f x) (d • fderiv ℝ f x e), smul_smul,
      inv_mul_cancel₀ hd0', one_smul]; abel
  rw [hrw, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |d|⁻¹ * ‖f (x + d • e) - f x - fderiv ℝ f x (d • e)‖
      ≤ |d|⁻¹ * (η / (‖e‖ + 1) * ‖d • e‖) := by gcongr
    _ = η * (‖e‖ / (‖e‖ + 1)) := by
      rw [norm_smul, Real.norm_eq_abs]; field_simp
    _ < η * 1 := by
      gcongr
      rw [div_lt_one he1]; linarith
    _ = η := mul_one η
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): limit of the left side of the
differenced Euler–Lagrange equation.**
Let `F : ℝⁿ → L*`, `L* = L(L(ℝⁿ, ℝ^ℓ), ℝ)`, be `C¹` on an open `U`, and let
`τ : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` be continuous with compact support `K = spt τ ⊆ U`.  Then for every
direction `e`, `∫_U F(x)[h⁻¹ (τ(x) − τ(x − h e))] dx → −∫_U DF(x)e[τ(x)] dx` as `h → 0`, `h ≠ 0`.
Proof: choose `δ > 0` with `cthickening δ K ⊆ U`.  For `|h| < δ/(|e| + 1)` the integrand vanishes
off `U`, every piece is continuous on a compact set and vanishes off it (hence integrable), and the
translation `x = y + h e` (Lebesgue measure is translation invariant) gives
`∫_U F(x)[h⁻¹ (τ(x) − τ(x − h e))] dx = −∫_K Q_h(y)[τ(y)] dy`, `Q_h(y) = h⁻¹ (F(y + h e) − F(y))`.
By `dohr_eb_ehs_del_diffquot_uniform`, `Q_h → DF(·)e` uniformly on `K`, so the integrands are
eventually bounded by `(sup_K |DF(·)e| + 1) sup |τ|` on the finite-measure set `K`, and dominated
convergence gives `∫_K Q_h[τ] → ∫_K DF(·)e[τ] = ∫_U DF(·)e[τ]`. -/
theorem dohr_eb_ehs_del_lhs_tendsto : ∀ n ℓ : ℕ, ∀ (F : Rn n → ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)) (τ : Rn n → (Rn n →L[ℝ] Rn ℓ)) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 F U → Continuous τ → HasCompactSupport τ → tsupport τ ⊆ U → Tendsto (fun h : ℝ => ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e)))) (𝓝[≠] 0) (𝓝 (-∫ x in U, fderiv ℝ F x e (τ x))) := by
  intro n ℓ F τ U e hU hF hτ hτc hτU
  -- Step 1: `K = tsupport τ` is compact and has a closed thickening `cthickening δ K ⊆ U`.
  have hK : IsCompact (tsupport τ) := hτc
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hτU
  -- Step 2: `F` and `DF(·)e` are continuous on `U`; `‖τ‖ ≤ Cτ` everywhere, `‖DF(·)e‖ ≤ CD` on `K`.
  have hFc : ContinuousOn F U := hF.continuousOn
  have hDFe : ContinuousOn (fun y => fderiv ℝ F y e) U :=
    (hF.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  obtain ⟨Cτ, hCτ⟩ := hτ.bounded_above_of_compact_support hτc
  obtain ⟨CD, hCD⟩ := hK.exists_bound_of_continuousOn (f := fun y => fderiv ℝ F y e)
    (hDFe.mono hτU)
  -- Step 3: `h⁻¹ (F(y + h e) − F(y)) → DF(y)e` uniformly on `K` (sibling, with `E = L*`).
  have hUC := Submission.dohr_eb_ehs_del_diffquot_uniform n _ F U (tsupport τ) e hU hF hK hτU
  -- Step 1 (cont.): for `|h| < δ/(‖e‖ + 1)` and `y ∈ K`, `y + h e ∈ cthickening δ K ⊆ U`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  have hshift : ∀ h : ℝ, |h| < δ / (‖e‖ + 1) → ∀ y ∈ tsupport τ,
      y + h • e ∈ cthickening δ (tsupport τ) := by
    intro h hh y hy
    apply mem_cthickening_of_dist_le (y + h • e) y δ (tsupport τ) hy
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
      _ ≤ δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ he1.ne'
  have hτ0 : ∀ y, y ∉ tsupport τ → τ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  -- Step 5: the limit integral over `U` is the integral over `K`.
  have hRHS : ∫ x in U, fderiv ℝ F x e (τ x) = ∫ x in tsupport τ, fderiv ℝ F x e (τ x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hτU
      (fun x hx => by rw [hτ0 x hx.2, map_zero])
  -- Step 4: for `0 < |h| < δ/(‖e‖ + 1)` the left side is `−∫_K h⁻¹ (F(y + h e) − F(y))[τ(y)] dy`.
  have hEq : (fun h : ℝ => ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e)))) =ᶠ[𝓝[≠] 0]
      (fun h : ℝ => -∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y)) := by
    filter_upwards [hev] with h hh
    -- (b) `F(·)[τ]` and `F(· + h e)[τ]` are continuous on `K` and vanish off `K`.
    have hI1 : Integrable (fun x => F x (τ x)) := by
      apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport τ)
      · exact ((hFc.mono hτU).clm_apply hτ.continuousOn).integrableOn_compact hK
      · intro x hx; rw [hτ0 x hx, map_zero]
    have hI2 : Integrable (fun x => F (x + h • e) (τ x)) := by
      apply IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport τ)
      · apply ContinuousOn.integrableOn_compact hK
        apply ContinuousOn.clm_apply _ hτ.continuousOn
        exact hFc.comp (continuousOn_id.add continuousOn_const)
          (fun y hy => hδU (hshift h hh y hy))
      · intro x hx; rw [hτ0 x hx, map_zero]
    -- (a) the integrand vanishes off `U`, so `∫_U = ∫_{ℝⁿ}`.
    have hL : ∫ x in U, F x (h⁻¹ • (τ x - τ (x - h • e))) =
        ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e))) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hxU
      have h1 : τ x = 0 := hτ0 x (fun hx => hxU (hτU hx))
      have h2 : τ (x - h • e) = 0 := by
        apply hτ0
        intro hx
        apply hxU
        have := hshift h hh (x - h • e) hx
        rw [sub_add_cancel] at this
        exact hδU this
      simp [h1, h2]
    -- (d) translation invariance: `∫ F(x)[τ(x − h e)] dx = ∫ F(y + h e)[τ(y)] dy`.
    have hT : ∫ x, F x (τ (x - h • e)) = ∫ y, F (y + h • e) (τ y) := by
      rw [← integral_add_right_eq_self (fun x => F x (τ (x - h • e))) (h • e)]
      simp only [add_sub_cancel_right]
    have hI3 : Integrable (fun x => F x (τ (x - h • e))) := by
      have := hI2.comp_sub_right (h • e)
      simpa only [sub_add_cancel] using this
    -- (c), (e) linearity of `F(x)` and of the integral.
    have hW : ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e))) =
        -∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
      calc ∫ x, F x (h⁻¹ • (τ x - τ (x - h • e)))
          = ∫ x, h⁻¹ * (F x (τ x) - F x (τ (x - h • e))) := by
            congr 1; ext x; rw [map_smul, map_sub, smul_eq_mul]
        _ = h⁻¹ * ((∫ x, F x (τ x)) - ∫ x, F x (τ (x - h • e))) := by
            rw [integral_const_mul, integral_sub hI1 hI3]
        _ = h⁻¹ * ((∫ y, F y (τ y)) - ∫ y, F (y + h • e) (τ y)) := by rw [hT]
        _ = -∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
            rw [← integral_sub hI1 hI2, ← integral_const_mul, ← integral_neg]
            congr 1; ext y
            simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
            ring
    have hS : ∫ y, (h⁻¹ • (F (y + h • e) - F y)) (τ y) =
        ∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy; rw [hτ0 y hy, map_zero]
    rw [hL, hW, hS]
  -- Step 6: dominated convergence on `K`, with the bound `(CD + 1) Cτ` for small `h`.
  have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ y ∈ tsupport τ,
      ‖h⁻¹ • (F (y + h • e) - F y) - fderiv ℝ F y e‖ < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUC) 1 one_pos] with h hh y hy
    have := hh y hy
    rw [dist_comm, dist_eq_norm] at this
    exact this
  have hlim : Tendsto (fun h : ℝ => ∫ y in tsupport τ, (h⁻¹ • (F (y + h • e) - F y)) (τ y))
      (𝓝[≠] 0) (𝓝 (∫ y in tsupport τ, fderiv ℝ F y e (τ y))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (CD + 1) * Cτ)
    · filter_upwards [hev] with h hh
      apply ContinuousOn.aestronglyMeasurable _ hK.measurableSet
      -- The integrand is the real-valued `h⁻¹ (F(y + h e)[τ(y)] − F(y)[τ(y)])`, continuous on `K`.
      have hc : ContinuousOn (fun y => h⁻¹ * (F (y + h • e) (τ y) - F y (τ y))) (tsupport τ) :=
        continuousOn_const.mul
          (((hFc.comp (continuousOn_id.add continuousOn_const)
            (fun y hy => hδU (hshift h hh y hy))).clm_apply hτ.continuousOn).sub
            ((hFc.mono hτU).clm_apply hτ.continuousOn))
      refine hc.congr (fun y _ => ?_)
      simp only [_root_.smul_apply, _root_.sub_apply, smul_eq_mul]
    · filter_upwards [hev1] with h hh
      apply ae_restrict_of_forall_mem hK.measurableSet
      intro y hy
      have hQ : ‖h⁻¹ • (F (y + h • e) - F y)‖ ≤ CD + 1 := by
        have h1 := norm_le_insert' (E := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
          (h⁻¹ • (F (y + h • e) - F y)) (fderiv ℝ F y e)
        linarith [hh y hy, hCD y hy]
      calc ‖(h⁻¹ • (F (y + h • e) - F y)) (τ y)‖
          ≤ ‖h⁻¹ • (F (y + h • e) - F y)‖ * ‖τ y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (CD + 1) * Cτ := by
            gcongr
            · linarith [norm_nonneg (fderiv ℝ F y e), hCD y hy]
            · exact hCτ y
    · exact integrableOn_const hK.measure_lt_top.ne
    · apply ae_restrict_of_forall_mem hK.measurableSet
      intro y hy
      exact ((ContinuousLinearMap.apply ℝ ℝ (τ y)).continuous.tendsto _).comp (hUC.tendsto_at hy)
  -- Step 7: conclusion.
  rw [hRHS]
  exact hlim.neg.congr' hEq.symm
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127):
admissibility of the difference-quotient test maps `φ_h(x) = h⁻¹ (ζ(x) − ζ(x − h e))`.  For
`ζ ∈ C¹_c` with `tsupport ζ ⊆ U` (`U` open), compactness gives `δ > 0` with
`K' = cthickening δ (tsupport ζ) ⊆ U`; for `|h| < δ / (‖e‖ + 1)` we have `‖h e‖ < δ`, so
`support φ_h ⊆ K'` and `φ_h` is `C¹`, compactly supported with `tsupport φ_h ⊆ K' ⊆ U`.  The chain
rule for the translation and linearity give `Dφ_h(y) = h⁻¹ (Dζ(y) − Dζ(y − h e))`. -/
theorem dohr_eb_ehs_del_test_admissible : ∀ n ℓ : ℕ, ∀ (ζ : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∀ᶠ h in 𝓝[≠] (0 : ℝ), ContDiff ℝ 1 (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ HasCompactSupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ∧ tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ U ∧ ∀ y, fderiv ℝ (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) y = h⁻¹ • (fderiv ℝ ζ y - fderiv ℝ ζ (y - h • e)) := by
  intro n ℓ ζ U e hU hζ hζc hζU
  -- Step 1 (margin): `K' = cthickening δ (tsupport ζ) ⊆ U`; restrict to `|h| < δ / (‖e‖ + 1)`.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [hev] with h hh
  have hdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  have hhe : ‖h • e‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
      _ < δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
      _ = δ := div_mul_cancel₀ _ he1.ne'
  -- Step 2 (support): if `φ_h(x) ≠ 0` then `x ∈ tsupport ζ` or `x − h e ∈ tsupport ζ`, so `x ∈ K'`.
  have hsupp : Function.support (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆
      cthickening δ (tsupport ζ) := by
    intro x hx
    by_contra hxK
    apply hx
    have h1 : ζ x = 0 := by
      by_contra h1
      exact hxK (self_subset_cthickening _ (subset_tsupport _ h1))
    have h2 : ζ (x - h • e) = 0 := by
      by_contra h2
      apply hxK
      apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
      rw [dist_eq_norm, sub_sub_cancel]
      exact hhe.le
    simp [h1, h2]
  have htsupp : tsupport (fun x => h⁻¹ • (ζ x - ζ (x - h • e))) ⊆ cthickening δ (tsupport ζ) :=
    closure_minimal hsupp isClosed_cthickening
  refine ⟨?_, ?_, htsupp.trans hδU, ?_⟩
  -- Step 3 (`C¹`): `ζ` composed with the translation, a difference and a constant multiple.
  · exact (hζ.sub (hζ.comp (contDiff_id.sub contDiff_const))).const_smul h⁻¹
  -- Step 4 (compact support): `tsupport φ_h` is closed inside the compact set `K'`.
  · exact IsCompact.of_isClosed_subset hζc.isCompact.cthickening (isClosed_tsupport _) htsupp
  -- Step 5 (derivative): chain rule for the translation (`hasFDerivAt_comp_sub`) and linearity.
  · intro y
    have hd1 : HasFDerivAt (fun x => ζ (x - h • e)) (fderiv ℝ ζ (y - h • e)) y :=
      (hasFDerivAt_comp_sub (h • e)).mpr (hdiff (y - h • e)).hasFDerivAt
    exact ((((hdiff y).hasFDerivAt).sub hd1).const_smul h⁻¹).fderiv

/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap, differentiated Euler–Lagrange
equation): limit of the right side.**
If `ζ : ℝⁿ → ℝ^ℓ` is `C¹` with compact support, `tsupport ζ ⊆ U` for an open `U`, and `g` is
continuous on `U`, then for every direction `e`, with `φ_h = h⁻¹ (ζ − ζ(· − h e))`,
`∫_U ⟨φ_h(x), g(x)⟩ dx → ∫_U ⟨Dζ(x) e, g(x)⟩ dx` as `h → 0`, `h ≠ 0`.
Proof: some `K' = cthickening δ (tsupport ζ)` is a compact subset of `U`, on which `‖g‖ ≤ C_g`
and `‖Dζ(·) e‖ ≤ C_ζ`.  Since `x − h e = x + h (−e)`, the uniform convergence of difference
quotients in the direction `−e` (`dohr_eb_ehs_del_diffquot_uniform`) gives `φ_h → Dζ(·) e`
uniformly on `K'` and pointwise everywhere.  For `0 < |h| < δ/(‖e‖ + 1)`, `φ_h` vanishes off `K'`,
so eventually `|⟨φ_h, g⟩| ≤ (C_ζ + 1) C_g 1_{K'}`, which is integrable; the integrands are
continuous on `U`, and dominated convergence along `𝓝[≠] 0` concludes. -/
theorem dohr_eb_ehs_del_rhs_tendsto : ∀ n ℓ : ℕ, ∀ (ζ g : Rn n → Rn ℓ) (U : Set (Rn n)) (e : Rn n), IsOpen U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ContinuousOn g U → Tendsto (fun h : ℝ => ∫ x in U, inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)) (𝓝[≠] 0) (𝓝 (∫ x in U, inner ℝ (fderiv ℝ ζ x e) (g x))) := by
  intro n ℓ ζ g U e hU hζ hζc hζU hg
  -- Step 1: a compact margin `K' = cthickening δ (tsupport ζ) ⊆ U`, and bounds on `K'` for
  -- `‖g‖` and `‖Dζ(·) e‖`.
  obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
  have hK' : IsCompact (cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
  obtain ⟨Cg, hCg⟩ := hK'.exists_bound_of_continuousOn (hg.mono hδU)
  have hDζc : Continuous (fun x => fderiv ℝ ζ x e) :=
    (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨Cz, hCz⟩ := hK'.exists_bound_of_continuousOn hDζc.continuousOn
  -- Step 2: uniform convergence of the difference quotients on `K'` in the direction `-e`,
  -- rewritten via `φ_h(x) = -(h⁻¹ (ζ(x + h (-e)) - ζ(x)))` and `Dζ(x) e = -(Dζ(x) (-e))`.
  have hUC := Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ
    (cthickening δ (tsupport ζ)) (-e) isOpen_univ hζ.contDiffOn hK' (subset_univ _)
  have hφ : ∀ (h : ℝ) (x : Rn n), h⁻¹ • (ζ x - ζ (x - h • e)) =
      -(h⁻¹ • (ζ (x + h • (-e)) - ζ x)) := by
    intro h x
    rw [smul_neg, ← sub_eq_add_neg, ← smul_neg, neg_sub]
  have hDneg : ∀ x, fderiv ℝ ζ x e = -(fderiv ℝ ζ x (-e)) := by
    intro x; simp
  -- Step 3: eventually `|h| < δ/(‖e‖ + 1)` and `‖φ_h - Dζ(·) e‖ < 1` on `K'`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hpos : 0 < δ / (‖e‖ + 1) := div_pos hδ he1
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    simpa [Real.dist_eq] using hh
  have hev1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ∀ x ∈ cthickening δ (tsupport ζ),
      ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ < 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUC) 1 one_pos] with h hh x hx
    have := hh x hx
    rw [dist_eq_norm] at this
    rw [hφ, hDneg, neg_sub_neg]
    exact this
  -- Step 4: dominated convergence along `𝓝[≠] 0` with the bound `(C_ζ + 1) C_g 1_{K'}`.
  apply tendsto_integral_filter_of_dominated_convergence
    ((cthickening δ (tsupport ζ)).indicator (fun _ => (Cz + 1) * Cg))
  · -- The integrands are continuous on `U`.
    filter_upwards with h
    apply ContinuousOn.aestronglyMeasurable _ hU.measurableSet
    apply ContinuousOn.inner _ hg
    have hζ0 := hζ.continuous
    exact Continuous.continuousOn (by fun_prop)
  · -- Domination: on `K'` by the uniform estimate, off `K'` the difference quotient vanishes.
    filter_upwards [hev, hev1] with h hh hh1
    filter_upwards with x
    by_cases hx : x ∈ cthickening δ (tsupport ζ)
    · rw [indicator_of_mem hx]
      have h1 : ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ ≤ Cz + 1 := by
        have := hh1 x hx
        calc ‖h⁻¹ • (ζ x - ζ (x - h • e))‖
            = ‖(h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e) + fderiv ℝ ζ x e‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e)) - fderiv ℝ ζ x e‖ + ‖fderiv ℝ ζ x e‖ :=
              norm_add_le _ _
          _ ≤ 1 + Cz := by linarith [hCz x hx]
          _ = Cz + 1 := by ring
      calc ‖inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x)‖
          ≤ ‖h⁻¹ • (ζ x - ζ (x - h • e))‖ * ‖g x‖ := norm_inner_le_norm _ _
        _ ≤ (Cz + 1) * Cg := by
            gcongr
            · linarith [norm_nonneg (fderiv ℝ ζ x e), hCz x hx]
            · exact hCg x hx
    · rw [indicator_of_notMem hx]
      have h1 : ζ x = 0 := by
        by_contra h1
        exact hx (self_subset_cthickening _ (subset_tsupport _ h1))
      have h2 : ζ (x - h • e) = 0 := by
        by_contra h2
        apply hx
        apply mem_cthickening_of_dist_le x (x - h • e) δ (tsupport ζ) (subset_tsupport _ h2)
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs]
        calc |h| * ‖e‖ ≤ |h| * (‖e‖ + 1) := by gcongr; linarith
          _ ≤ δ / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
          _ = δ := div_mul_cancel₀ _ he1.ne'
      simp [h1, h2]
  · -- The bound is integrable: a constant on the compact set `K'`.
    rw [integrable_indicator_iff hK'.isClosed.measurableSet]
    exact integrableOn_const (ne_of_lt (lt_of_le_of_lt
      (Measure.restrict_apply_le _ _) hK'.measure_lt_top))
  · -- Pointwise convergence, from the sibling applied to the compact set `{x}`.
    filter_upwards with x
    apply Tendsto.inner _ tendsto_const_nhds
    have hx := (Submission.dohr_eb_ehs_del_diffquot_uniform n (Rn ℓ) ζ univ {x} (-e) isOpen_univ
      hζ.contDiffOn isCompact_singleton (subset_univ _)).tendsto_at (mem_singleton x)
    simp only [hφ, hDneg]
    exact hx.neg
/-- The weak Euler–Lagrange equation `∫_U DΨ(Du)[Dφ] = -∫_U ⟨φ, g⟩` (all `φ ∈ C¹_c(U; ℝ^ℓ)`),
differentiated in the direction `e`: `∫_U D²Ψ(Du)[Dv_e][Dζ] = ∫_U ⟨g, Dζ e⟩` with `v_e = Du(·) e`.
Test the equation with the difference quotients `φ_h = h⁻¹ (ζ − ζ(· − h e))`, which are admissible
for small `h ≠ 0`.  With `F = DΨ ∘ Du` (`C¹` on `U`) and `τ = Dζ`, the left side tends to
`−∫_U DF(x) e [Dζ(x)]` and the right side to `−∫_U ⟨Dζ(x) e, g(x)⟩` as `h → 0`; the limits agree, and
`DF(x) e = D²Ψ(Du(x))[Dv_e(x)]` on `U` by the chain rule and the symmetry of `D²u`. -/
theorem dohr_eb_ehs_differentiated_el : ∀ n ℓ : ℕ, ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (U : Set (Rn n)) (u g : Rn n → Rn ℓ), IsOpen U → ContDiff ℝ 2 Ψ → ContDiffOn ℝ 2 u U → ContinuousOn g U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → ∀ (e : Rn n) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x) (fderiv ℝ (fun z => fderiv ℝ u z e) x) (fderiv ℝ ζ x) = ∫ x in U, inner ℝ (g x) (fderiv ℝ ζ x e) := by
  intro n ℓ Ψ U u g hU hΨ hu hg hEL e ζ hζ hζc hζU
  -- `F = DΨ ∘ Du` is `C¹` on `U`; `τ = Dζ` is continuous with compact support inside `U`.
  have hF : ContDiffOn ℝ 1 (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) U :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).comp_contDiffOn
      (hu.fderiv_of_isOpen hU (m := 1) (by norm_num))
  have hτ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv (by norm_num)
  have hτc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv ℝ
  have hτU : tsupport (fderiv ℝ ζ) ⊆ U := (tsupport_fderiv_subset ℝ).trans hζU
  -- The two sides of the equation tested with `φ_h` and their limits as `h → 0`.
  have hL := Submission.dohr_eb_ehs_del_lhs_tendsto n ℓ (fun z => fderiv ℝ Ψ (fderiv ℝ u z))
    (fderiv ℝ ζ) U e hU hF hτ hτc hτU
  have hR := (Submission.dohr_eb_ehs_del_rhs_tendsto n ℓ ζ g U e hU hζ hζc hζU hg).neg
  -- For small `h ≠ 0`, `φ_h` is admissible and `Dφ_h = h⁻¹ (Dζ − Dζ(· − h e))`.
  have hLR : (fun h : ℝ => ∫ x in U,
        fderiv ℝ Ψ (fderiv ℝ u x) (h⁻¹ • (fderiv ℝ ζ x - fderiv ℝ ζ (x - h • e)))) =ᶠ[𝓝[≠] 0]
      fun h : ℝ => -∫ x in U, inner ℝ (h⁻¹ • (ζ x - ζ (x - h • e))) (g x) := by
    filter_upwards [Submission.dohr_eb_ehs_del_test_admissible n ℓ ζ U e hU hζ hζc hζU]
      with h ⟨h1, h2, h3, h4⟩
    have hEL_h := hEL _ h1 h2 h3
    simp only [h4] at hEL_h
    exact hEL_h
  -- Uniqueness of limits along `𝓝[≠] 0`.
  have key := neg_inj.mp (tendsto_nhds_unique_of_eventuallyEq hL hR hLR)
  calc ∫ x in U, fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x) (fderiv ℝ (fun z => fderiv ℝ u z e) x)
        (fderiv ℝ ζ x)
      = ∫ x in U, fderiv ℝ (fun z => fderiv ℝ Ψ (fderiv ℝ u z)) x e (fderiv ℝ ζ x) :=
        setIntegral_congr_fun hU.measurableSet fun x hx =>
          (DFunLike.congr_fun
            (Submission.dohr_eb_ehs_del_chain_symm n ℓ Ψ U u hU hΨ hu e x hx) _).symm
    _ = ∫ x in U, inner ℝ (fderiv ℝ ζ x e) (g x) := key
    _ = ∫ x in U, inner ℝ (g x) (fderiv ℝ ζ x e) :=
        integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if
`Ψ` is `C^∞` on `L = L(ℝⁿ, ℝ^ℓ)`, then for fixed `P, Q ∈ L` the Hessian component
`R ↦ D²Ψ(R)[P][Q]` is `C^∞`.  `A = DΨ` is `C^∞`, hence so is `a_Q(R) = A(R)[Q]` and its
derivative; `fderiv_clm_apply` with the constant `Q` gives `Da_Q(R)[P] = DA(R)[P][Q]`, so the map
is the `C^∞` derivative `Da_Q` evaluated at `P`. -/
theorem dohr_eb_ehs_hessian_apply_contDiff : ∀ n ℓ : ℕ, ∀ Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → ∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) (fun R : Rn n →L[ℝ] Rn ℓ => fderiv ℝ (fderiv ℝ Ψ) R P Q) := by
  intro n ℓ Ψ hΨ P Q
  -- Step 1: `A = DΨ` is `C^∞`.
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ).2
  -- Step 2: `a_Q(R) = A(R)[Q]` is `C^∞` (evaluation at `Q` is continuous linear), so is `Da_Q`.
  have haQ : ContDiff ℝ (⊤ : ℕ∞) (fun R => fderiv ℝ Ψ R Q) := hA.clm_apply contDiff_const
  have hDaQ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun R => fderiv ℝ Ψ R Q)) :=
    (contDiff_infty_iff_fderiv.1 haQ).2
  -- Step 3: `Da_Q(R)[P] = DA(R)[P][Q]`, by the product rule with the constant map `Q`.
  have heq : (fun R => fderiv ℝ (fderiv ℝ Ψ) R P Q)
      = fun R => fderiv ℝ (fun R' => fderiv ℝ Ψ R' Q) R P := by
    funext R
    rw [fderiv_clm_apply (hA.differentiable (by simp) R) (differentiableAt_const Q)]
    simp
  -- Step 4: the map is `Da_Q` followed by the continuous linear evaluation at `P`.
  rw [heq]
  exact hDaQ.clm_apply contDiff_const
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): pairing
with a fixed vector `w` preserves the local class `C^{m,α}`.  If `g` is `C^m` on the open set `U` and
`Dᵐg` is `α`-Hölder on every compact `K ⊆ U`, then so is `x ↦ ⟪g x, w⟫ = innerSL ℝ w ∘ g`: its
`m`-th derivative on `U` is `innerSL ℝ w` composed with `Dᵐg` (`iteratedFDeriv_comp_left`), so a
Hölder constant `C` of `Dᵐg` on `K` gives the constant `‖innerSL ℝ w‖ * C`. -/
theorem dohr_eb_ehs_inner_right_holder : ∀ (n ℓ m : ℕ) (α : ℝ) (U : Set (Rn n)) (g : Rn n → Rn ℓ) (w : Rn ℓ), IsOpen U → IsLocallyHolderCkα m α g U → ContDiffOn ℝ m (fun x => inner ℝ (g x) w) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x - iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ m α U g w hU hg
  -- Step 1: `x ↦ ⟪g x, w⟫` is `L ∘ g` for the continuous linear functional `L = ⟪w, ·⟫`.
  set L : Rn ℓ →L[ℝ] ℝ := innerSL ℝ w with hL
  have hfun : (fun z => inner ℝ (g z) w) = L ∘ g := by
    funext z; simp [hL, real_inner_comm]
  -- Step 2: on the open set `U`, `Dᵐ(L ∘ g) = L ∘ Dᵐg`.
  have hiter : ∀ x ∈ U, iteratedFDeriv ℝ m (fun z => inner ℝ (g z) w) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x) := by
    intro x hx
    rw [hfun]
    exact L.iteratedFDeriv_comp_left (hg.1.contDiffAt (hU.mem_nhds hx)) le_rfl
  -- Step 3: `L ∘ g` is `C^m` on `U`.
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact L.contDiff.comp_contDiffOn hg.1
  -- Step 4: by linearity and `‖L ∘ N‖ ≤ ‖L‖ ‖N‖`, a Hölder constant `C` of `Dᵐg` on `K`
  -- gives the Hölder constant `‖L‖ * C` of `Dᵐ(L ∘ g)`.
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hg.2 K hK hKU
    refine ⟨‖L‖ * C, fun x hx y hy => ?_⟩
    rw [hiter x (hKU hx), hiter y (hKU hy)]
    have hsub : L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x)
        - L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g y)
        = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y) := by
      ext v; simp
    rw [hsub]
    calc _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ :=
          L.norm_compContinuousMultilinearMap_le _
      _ ≤ ‖L‖ * (C * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left (hC x hx y hy) (norm_nonneg _)
      _ = ‖L‖ * C * ‖x - y‖ ^ α := by ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the derivative of a directional
derivative of a `C²` map.**
If `v : ℝⁿ → ℝ^ℓ` is `C²` on an open `U` and `e ∈ ℝⁿ`, then at every `x ∈ U` the directional
derivative `v_e(z) = Dv(z) e` has derivative `D(v_e)(x) = D(Dv)(x) e` (symmetry of the second
derivative, proved here by difference quotients since `FDeriv.Symmetric` is not imported).
Proof: choose `r > 0` with `B_r(x) ⊆ U`.  By `dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn` for the
`C¹` map `Dv`, `T_d = d⁻¹ (Dv(· + d e) − Dv) → D(Dv)(·) e` uniformly on `B_r(x)` as `d → 0`,
`d ≠ 0`.  For `|d| < (r/2)/(‖e‖ + 1)` and `z ∈ B̆_{r/2}(x)` the points `z`, `z + d e` lie in `U`, so
`w_d = d⁻¹ (v(· + d e) − v)` has derivative `T_d(z)` at `z`.  For `y ∈ U`, `w_d(y) → Dv(y) e` (slope
of `t ↦ v(y + t e)` at `0`).  The theorem on uniform limits of derivatives
(`hasFDerivAt_of_tendstoUniformlyOnFilter`) gives `D(v_e)(x) = D(Dv)(x) e`. -/
theorem dohr_eb_lhr_ds_fderiv_dirDeriv_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → ContDiffOn ℝ 2 v U → ∀ x ∈ U, fderiv ℝ (fun z => fderiv ℝ v z e) x = fderiv ℝ (fderiv ℝ v) x e := by
  intro n ℓ U v e hU hv x hx
  -- Step 1: a closed ball `B_r(x) ⊆ U`; `v` is differentiable on `U` and `Dv` is `C¹` on `U`.
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ v z := fun z hz =>
    (hv.differentiableOn two_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  -- Steps 2–3: `T_d → D(Dv)(·) e` uniformly on `B_r(x)`, hence uniformly on the filter `𝓝 x`.
  have hunif : TendstoUniformlyOn
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (closedBall x r) :=
    Submission.dohr_eb_lhr_ds_diffQuot_tendstoUniformlyOn n (Rn n →L[ℝ] Rn ℓ) (fderiv ℝ v) U
      (closedBall x r) e hU hDv (isCompact_closedBall x r) hrU
  have hunif' : TendstoUniformlyOnFilter
      (fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
      (fun z => fderiv ℝ (fderiv ℝ v) z e) (𝓝[≠] 0) (𝓝 x) :=
    hunif.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr (closedBall_mem_nhds x hr))
  -- Step 4: `w_d` has derivative `T_d(z)` at `z` for `|d| < (r/2)/(‖e‖ + 1)`, `z ∈ B̆_{r/2}(x)`.
  have he1 : 0 < ‖e‖ + 1 := by positivity
  have hρ : 0 < r / 2 / (‖e‖ + 1) := by positivity
  have hdev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < r / 2 / (‖e‖ + 1) := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with d hd
    simpa [Real.dist_eq] using hd
  have hzev : ∀ᶠ z in 𝓝 x, z ∈ ball x (r / 2) := Metric.ball_mem_nhds x (half_pos hr)
  have hderiv : ∀ᶠ p : ℝ × Rn n in 𝓝[≠] 0 ×ˢ 𝓝 x,
      HasFDerivAt (fun z => p.1⁻¹ • (v (z + p.1 • e) - v z))
        (p.1⁻¹ • (fderiv ℝ v (p.2 + p.1 • e) - fderiv ℝ v p.2)) p.2 := by
    filter_upwards [hdev.prod_mk hzev] with p hp
    obtain ⟨d, z⟩ := p
    obtain ⟨hd, hz⟩ := hp
    have hzr : dist z x < r / 2 := hz
    have hzU : z ∈ U := hrU (mem_closedBall.mpr (hzr.le.trans (half_le_self hr.le)))
    have hde : ‖d • e‖ < r / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |d| * ‖e‖ ≤ |d| * (‖e‖ + 1) := by gcongr; linarith
        _ < r / 2 / (‖e‖ + 1) * (‖e‖ + 1) := by gcongr
        _ = r / 2 := div_mul_cancel₀ _ he1.ne'
    have hzdU : z + d • e ∈ U := by
      refine hrU (mem_closedBall.mpr ?_)
      calc dist (z + d • e) x = ‖(z - x) + d • e‖ := by rw [dist_eq_norm, add_sub_right_comm]
        _ ≤ ‖z - x‖ + ‖d • e‖ := norm_add_le _ _
        _ ≤ r := by rw [← dist_eq_norm]; linarith
    -- chain rule for the translation `z ↦ z + d e`, then difference and constant multiple rules
    have htr : HasFDerivAt (fun z => v (z + d • e)) (fderiv ℝ v (z + d • e)) z :=
      (hasFDerivAt_comp_add_right (d • e)).mpr (hdiff _ hzdU).hasFDerivAt
    exact (htr.sub (hdiff z hzU).hasFDerivAt).const_smul d⁻¹
  -- Step 5: `w_d(y) → Dv(y) e` for every `y ∈ U`: slopes of `t ↦ v(y + t e)` at `t = 0`.
  have hpt : ∀ᶠ y in 𝓝 x,
      Tendsto (fun d : ℝ => d⁻¹ • (v (y + d • e) - v y)) (𝓝[≠] 0) (𝓝 (fderiv ℝ v y e)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hline : HasDerivAt (fun t : ℝ => y + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    have hvy : HasFDerivAt v (fderiv ℝ v y) (y + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]
      exact (hdiff y hy).hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => v (y + t • e)) (fderiv ℝ v y e) 0 :=
      hvy.comp_hasDerivAt (0 : ℝ) hline
    simpa using hcomp.tendsto_slope_zero
  -- Step 6: uniform limits of derivatives (`f d = w_d`, `f' d = T_d`, `g = v_e`).
  exact (hasFDerivAt_of_tendstoUniformlyOnFilter
    (f := fun (d : ℝ) (z : Rn n) => d⁻¹ • (v (z + d • e) - v z))
    (f' := fun (d : ℝ) (z : Rn n) => d⁻¹ • (fderiv ℝ v (z + d • e) - fderiv ℝ v z))
    (g := fun z => fderiv ℝ v z e) (g' := fun z => fderiv ℝ (fderiv ℝ v) z e)
    hunif' hderiv hpt).fderiv
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): families of linear forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)` and let `Φ : ℝⁿ → L* = L(L, ℝ)` be such that `x ↦ Φ(x)[P]` is `C¹` on an
open `U` for every `P ∈ L`.  Then `Φ` is `C¹` on `U` as an `L*`-valued map, and
`(DΦ(x) e)[P] = D(Φ(·)[P])(x) e` for all `x ∈ U`, `e ∈ ℝⁿ` and `P ∈ L`.
Proof: `L` is finite-dimensional; with a basis `E_r` of `L` and its continuous coordinate forms
`π_r`, linearity gives `Φ(x)[P] = Σ_r π_r(P) Φ(x)[E_r]`, so `Φ(x) = Σ_r Φ(x)[E_r] π_r` is a finite
sum of the constant forms `π_r` times `C¹` scalar functions, and `Φ` is `C¹` on `U`.  For `x ∈ U`,
`Φ` is differentiable at `x`, and the product rule for evaluation at the constant `P` gives
`D(Φ(·)[P])(x) = (DΦ(x)).flip P`. -/
theorem dohr_eb_lhr_ds_clm_family : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ), IsOpen U → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 1 Φ U ∧ ∀ x ∈ U, ∀ (e : Rn n) (P : Rn n →L[ℝ] Rn ℓ), fderiv ℝ Φ x e P = fderiv ℝ (fun z => Φ z P) x e := by
  intro n ℓ U Φ hU hΦ
  -- Step 1: a basis `b` of `L` and its continuous coordinate forms `π r`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  -- Step 2: `Φ(x) = Σ_r Φ(x)[b r] π r` in `L*`, by linearity of `Φ(x)`; the summand is written
  -- `(π r).smulRight (Φ x (b r)) : P ↦ π r P • Φ x (b r)`, so no scalar action on `L*` is needed.
  have hexp : ∀ x, Φ x = ∑ r, (π r).smulRight (Φ x (b r)) := by
    intro x
    ext P
    have hP : Φ x P = Φ x (∑ r, b.repr P r • b r) := by rw [b.sum_repr]
    rw [hP, map_sum]
    simp [map_smul, π]
  -- Step 3: each summand is `C¹` (constant form, `C¹` coefficient), hence so are the sum and `Φ`.
  have hC1 : ContDiffOn ℝ 1 Φ U := by
    have h : ContDiffOn ℝ 1 (fun x => ∑ r, (π r).smulRight (Φ x (b r))) U :=
      ContDiffOn.sum fun r _ => contDiffOn_const.smulRight (hΦ (b r))
    exact h.congr fun x _ => hexp x
  refine ⟨hC1, fun x hx e P => ?_⟩
  -- Step 4: differentiate the evaluation `z ↦ Φ(z)[P]` at the constant `P`.
  have hd : DifferentiableAt ℝ Φ x :=
    (hC1.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  rw [fderiv_clm_apply hd (differentiableAt_const P)]
  simp
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): Leibniz rule for a family of bilinear
forms.**
Let `L = L(ℝⁿ, ℝ^ℓ)`, let `a : ℝⁿ → L(L, L*)` be such that `x ↦ a(x)[P][Q]` is `C¹` on an open `U`
for all `P, Q ∈ L`, and let `w : ℝⁿ → L` be `C¹` on `U`.  Then `x ↦ a(x)[w(x)]` is `C¹` on `U` as an
`L*`-valued map, and for `x ∈ U`, `P ∈ L` and `e ∈ ℝⁿ`,
`(D(a(·)[w(·)])(x) e)[P] = a(x)[Dw(x) e][P] + D(a(·)[w(x)][P])(x) e`, with `w(x)` frozen in the
last term.
Proof: with a basis `E_r` of `L` and its continuous coordinate forms `π_r`, linearity gives
`a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.  So each evaluation `z ↦ a(z)[w(z)][P]` is a finite sum of
products of `C¹` functions, and `dohr_eb_lhr_ds_clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map
with `(D(a(·)[w(·)])(x) e)[P] = D(a(·)[w(·)][P])(x) e`.  The product and sum rules give
`D(a(·)[w(·)][P])(x) e = Σ_r π_r(w(x)) · D(a(·)[E_r][P])(x) e + Σ_r π_r(Dw(x) e) · a(x)[E_r][P]`;
by the expansion the second sum is `a(x)[Dw(x) e][P]`, and the first is `D(a(·)[w(x)][P])(x) e`. -/
theorem dohr_eb_lhr_ds_bilin_leibniz : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → (Rn n →L[ℝ] Rn ℓ)) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → ContDiffOn ℝ 1 w U → ContDiffOn ℝ 1 (fun x => a x (w x)) U ∧ ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, fderiv ℝ (fun z => a z (w z)) x e P = a x (fderiv ℝ w x e) P + fderiv ℝ (fun z => a z (w x) P) x e := by
  intro n ℓ U a w e hU ha hw
  -- Step 1: a basis `E_r = b r` of `L` with continuous coordinate forms `π r`, and the expansion
  -- `a(z)[Q][P] = Σ_r π_r(Q) · a(z)[E_r][P]`.
  let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
  let π : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ :=
    fun r => LinearMap.toContinuousLinearMap (b.coord r)
  have hexp : ∀ z Q P, a z Q P = ∑ r, π r Q * a z (b r) P := by
    intro z Q P
    have hQ : a z Q = a z (∑ r, b.repr Q r • b r) := by rw [b.sum_repr]
    rw [hQ, map_sum, sum_apply]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rfl
  -- Step 2: each evaluation `z ↦ a(z)[w(z)][P] = Σ_r π_r(w(z)) · a(z)[E_r][P]` is `C¹` on `U`, so
  -- `clm_family` makes `z ↦ a(z)[w(z)]` a `C¹` map into `L*` and reduces the derivative identity
  -- to the evaluation at `P`.
  have hπw : ∀ r, ContDiffOn ℝ 1 (fun z => π r (w z)) U := fun r =>
    (π r).contDiff.comp_contDiffOn hw
  have hC1P : ∀ P, ContDiffOn ℝ 1 (fun z => a z (w z) P) U := fun P =>
    (ContDiffOn.sum fun r _ => (hπw r).mul (ha (b r) P)).congr fun z _ => hexp z (w z) P
  obtain ⟨hC1, hcf⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (w z)) hU hC1P
  refine ⟨hC1, fun x hx P => ?_⟩
  rw [hcf x hx e P]
  -- Step 3: product and sum rules for the expansion of `z ↦ a(z)[w(z)][P]`.
  have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
  have hdw : HasFDerivAt w (fderiv ℝ w x) x :=
    ((hw.differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hdA : ∀ r, HasFDerivAt (fun z => a z (b r) P) (fderiv ℝ (fun z => a z (b r) P) x) x :=
    fun r => (((ha (b r) P).differentiableOn one_ne_zero x hx).differentiableAt hxU).hasFDerivAt
  have hD : HasFDerivAt (fun z => a z (w z) P)
      (∑ r, (π r (w x) • fderiv ℝ (fun z => a z (b r) P) x
        + a x (b r) P • (π r).comp (fderiv ℝ w x))) x := by
    rw [show (fun z => a z (w z) P) = fun z => ∑ r, π r (w z) * a z (b r) P from
      funext fun z => hexp z (w z) P]
    exact HasFDerivAt.fun_sum fun r _ => ((π r).hasFDerivAt.comp x hdw).mul (hdA r)
  -- Step 4: the derivative of `z ↦ a(z)[w(x)][P]`, with `w(x)` frozen.
  have hF : HasFDerivAt (fun z => a z (w x) P)
      (∑ r, π r (w x) • fderiv ℝ (fun z => a z (b r) P) x) x := by
    rw [show (fun z => a z (w x) P) = fun z => ∑ r, π r (w x) * a z (b r) P from
      funext fun z => hexp z (w x) P]
    exact HasFDerivAt.fun_sum fun r _ => (hdA r).const_mul (π r (w x))
  -- Step 5: by the expansion, the two sums are `a(x)[Dw(x) e][P]` and `D(a(·)[w(x)][P])(x) e`.
  rw [hD.fderiv, hF.fderiv, hexp x (fderiv ℝ w x e) P]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Finset.sum_add_distrib, mul_comm (a x (b _) P)]
  ring
/-- Differentiated system in the linear higher-regularity step of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): translating the test functions of a weak
identity.  If `∫_U ω₁(x)[Dφ(x)] dx = ∫_U ω₂(x)[Dφ(x)] dx` for every `C¹` compactly supported
`φ` with `spt φ ⊆ U`, and `ζ` is `C¹` with compact support and `spt ζ + s e ⊆ U`, then
`∫ ω₁(y + s e)[Dζ(y)] dy = ∫ ω₂(y + s e)[Dζ(y)] dy`.
Proof: test with `φ(x) = ζ(x − s e)`, which is `C¹` with compact support,
`spt φ = spt ζ + s e ⊆ U` and `Dφ(x) = Dζ(x − s e)`.  The integrands `ω_i(x)[Dφ(x)]` vanish off
`U`, so the integrals over `U` are whole-space integrals, and the substitution `x = y + s e`
(translation invariance of Lebesgue measure) turns them into `∫ ω_i(y + s e)[Dζ(y)] dy`.  No
integrability or measurability is needed. -/
theorem dohr_eb_lhr_ds_translate_weak_eq : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n) (s : ℝ) (ζ : Rn n → Rn ℓ), (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ y ∈ tsupport ζ, y + s • e ∈ U) → ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y) = ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y) := by
  intro n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc hζU
  -- Step 1: the translated test function `φ = ζ ∘ τ`, `τ x = x − s e`, is `C¹` with compact
  -- support.
  let φ : Rn n → Rn ℓ := ζ ∘ Homeomorph.subRight (s • e)
  have hφC : ContDiff ℝ 1 φ := hζ.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hζc.comp_homeomorph _
  -- Step 2: `tsupport φ = τ⁻¹(tsupport ζ) ⊆ U`.
  have hφU : tsupport φ ⊆ U := by
    intro x hx
    rw [tsupport_comp_eq_preimage] at hx
    simpa using hζU _ hx
  -- Step 3: `Dφ(x) = Dζ(x − s e)`.
  have hDφ : ∀ x, fderiv ℝ φ x = fderiv ℝ ζ (x - s • e) := fun x =>
    fderiv_comp_sub (f := ζ) (s • e)
  -- Steps 4–5: the integrand vanishes off `U`, and `x = y + s e` turns the whole-space integral
  -- into the translated one.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∫ x in U, ω x (fderiv ℝ φ x) = ∫ y, ω (y + s • e) (fderiv ℝ ζ y) := by
    intro ω
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [← integral_add_right_eq_self (fun x => ω x (fderiv ℝ φ x)) (s • e)]
      congr 1
      funext y
      rw [hDφ, add_sub_cancel_right]
    · intro x hx
      have hx' : x - s • e ∉ tsupport ζ := fun h => hx (by simpa using hζU _ h)
      rw [hDφ, fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 6: combine with the weak identity for `φ`.
  rw [← key ω₁, ← key ω₂]
  exact hweak φ hφC hφc hφU
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): differentiating a weak identity.**
Let `ω₁, ω₂ : ℝⁿ → L*` (`L = L(ℝⁿ, ℝ^ℓ)`) be `C¹` on the open set `U` and satisfy
`∫_U ω₁[Dφ] = ∫_U ω₂[Dφ]` for every `φ ∈ C¹_c(U; ℝ^ℓ)`.  Then for every direction `e` and every
`ζ ∈ C¹_c(U; ℝ^ℓ)` the functions `F_i = (Dω_i e)[Dζ]` are integrable on `U` and
`∫_U F₁ = ∫_U F₂`.
Proof: `K = spt ζ` has a compact thickening `K₁ = cthickening δ K ⊆ U`, and `y + s e ∈ K₁` for
`y ∈ K`, `|s| < ε = δ/(|e| + 1)`.  The translated integrands `ω_i(y + s e)[Dζ(y)]` and
`(Dω_i(y + s e) e)[Dζ(y)]` are continuous with support in `K`.  By the translated weak identity
(`dohr_eb_lhr_ds_translate_weak_eq`), `I_i(s) = ∫ ω_i(y + s e)[Dζ(y)] dy` satisfy `I₁ = I₂` for
`|s| < ε`.  Differentiating under the integral sign, with the integrable bound `C_i |Dζ|` where
`C_i` bounds `|Dω_i(z) e|` on `K₁`, gives `I_i'(0) = ∫ F_i` and the integrability of `F_i`;
hence `∫ F₁ = ∫ F₂`.  The `F_i` vanish off `K ⊆ U`, so the integrals over `U` agree. -/
theorem dohr_eb_lhr_ds_weak_eq_fderiv : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (ω₁ ω₂ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 ω₁ U → ContDiffOn ℝ 1 ω₂ U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, ω₁ x (fderiv ℝ φ x) = ∫ x in U, ω₂ x (fderiv ℝ φ x)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → IntegrableOn (fun x => fderiv ℝ ω₁ x e (fderiv ℝ ζ x)) U ∧ IntegrableOn (fun x => fderiv ℝ ω₂ x e (fderiv ℝ ζ x)) U ∧ ∫ x in U, fderiv ℝ ω₁ x e (fderiv ℝ ζ x) = ∫ x in U, fderiv ℝ ω₂ x e (fderiv ℝ ζ x) := by
  intro n ℓ U ω₁ ω₂ e hU hω₁ hω₂ hweak ζ hζ hζc hζU
  -- Step 1: a compact thickening `K₁ = cthickening δ K` of `K = tsupport ζ` inside `U`, and
  -- `ε = δ / (‖e‖ + 1)`, so that `y + s • e ∈ K₁` for `y ∈ K` and `|s| < ε`.
  have hK : IsCompact (tsupport ζ) := hζc
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hζU
  have hK₁ : IsCompact (cthickening δ (tsupport ζ)) := hK.cthickening
  have he1 : 0 < ‖e‖ + 1 := by positivity
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (‖e‖ + 1) = δ :=
    ⟨δ / (‖e‖ + 1), div_pos hδ he1, div_mul_cancel₀ δ he1.ne'⟩
  have hmemK₁ : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε,
      y + s • e ∈ cthickening δ (tsupport ζ) := by
    intro y hy s hs
    refine mem_cthickening_of_dist_le _ y δ _ hy ?_
    rw [mem_ball, Real.dist_eq, sub_zero] at hs
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, ← hεδ]
    exact mul_le_mul hs.le (by linarith) (norm_nonneg e) hε.le
  have hmemU : ∀ y ∈ tsupport ζ, ∀ s ∈ ball (0 : ℝ) ε, y + s • e ∈ U :=
    fun y hy s hs => hδU (hmemK₁ y hy s hs)
  -- `Dζ` is continuous, vanishes off `K`, and `‖Dζ‖` is integrable.
  have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζ0 : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy => fderiv_of_notMem_tsupport ℝ hy
  have hDζint : Integrable (fun y => ‖fderiv ℝ ζ y‖) :=
    (hDζc.integrable_of_hasCompactSupport (hζc.fderiv ℝ)).norm
  -- Integrands `y ↦ G y (Dζ y)` are supported in `K`.
  have hsupp : ∀ G : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      Function.support (fun y => G y (fderiv ℝ ζ y)) ⊆ tsupport ζ := by
    intro G y hy
    by_contra hyK
    exact hy (by simp only [hDζ0 y hyK, ContinuousLinearMap.map_zero])
  -- Step 3: for `|s| < ε` the translated integrands are continuous (with support in `K`).
  have hcont : ∀ s ∈ ball (0 : ℝ) ε, ∀ g : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContinuousOn g U →
      Continuous (fun y => g (y + s • e) (fderiv ℝ ζ y)) := by
    intro s hs g hg
    have htr : Continuous (fun y : Rn n => y + s • e) := continuous_id.add continuous_const
    refine ContinuousOn.continuous_of_tsupport_subset (s := (fun y => y + s • e) ⁻¹' U)
      ((hg.comp htr.continuousOn (fun y hy => hy)).clm_apply hDζc.continuousOn)
      (hU.preimage htr) ?_
    exact (closure_minimal (hsupp (fun y => g (y + s • e))) (isClosed_tsupport ζ)).trans
      (fun y hy => hmemU y hy s hs)
  -- Steps 2 and 5, for a single `ω`: `I(s) = ∫ ω(y + s • e)[Dζ y] dy` has derivative
  -- `∫ (Dω(y) e)[Dζ y] dy` at `0`, and this integrand is integrable.
  have key : ∀ ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ContDiffOn ℝ 1 ω U →
      Integrable (fun y => fderiv ℝ ω y e (fderiv ℝ ζ y)) ∧
      HasDerivAt (fun s : ℝ => ∫ y, ω (y + s • e) (fderiv ℝ ζ y))
        (∫ y, fderiv ℝ ω y e (fderiv ℝ ζ y)) 0 := by
    intro ω hω
    -- Step 2: `ω` and `z ↦ Dω(z) e` are continuous on `U`; `‖Dω(z) e‖ ≤ C` on `K₁`.
    have hωc : ContinuousOn ω U := hω.continuousOn
    have hDωe : ContinuousOn (fun z => fderiv ℝ ω z e) U :=
      (hω.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    obtain ⟨C, hC⟩ := hK₁.exists_bound_of_continuousOn (E := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (hDωe.mono hδU)
    have hball : ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := ball_mem_nhds 0 hε
    have h0 : (0 : ℝ) ∈ ball (0 : ℝ) ε := mem_ball_self hε
    -- (a) the pointwise derivative in `s` (chain rule, then evaluation at the constant `Dζ y`)
    have hderiv : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        HasDerivAt (fun σ : ℝ => ω (y + σ • e) (fderiv ℝ ζ y))
          (fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)) s := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have hz := ((hω.differentiableOn one_ne_zero _ (hmemU y hy s hs)).differentiableAt
          (hU.mem_nhds (hmemU y hy s hs))).hasFDerivAt
        have hline : HasDerivAt (fun σ : ℝ => y + σ • e) e s :=
          (((hasDerivAt_id' s).smul_const e).const_add y).congr_deriv (one_smul ℝ e)
        refine (HasDerivAt.clm_apply (c := fun σ : ℝ => ω (y + σ • e))
          (u := fun _ : ℝ => fderiv ℝ ζ y) (hz.comp_hasDerivAt s hline)
          (hasDerivAt_const s (fderiv ℝ ζ y))).congr_deriv ?_
        simp only [ContinuousLinearMap.map_zero, add_zero]
      · simp only [hDζ0 y hy, ContinuousLinearMap.map_zero]
        exact hasDerivAt_const s 0
    -- (b) domination by the integrable bound `C ‖Dζ‖`
    have hbound : ∀ y : Rn n, ∀ s ∈ ball (0 : ℝ) ε,
        ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖ ≤ C * ‖fderiv ℝ ζ y‖ := by
      intro y s hs
      by_cases hy : y ∈ tsupport ζ
      · have h1 := hC (y + s • e) (hmemK₁ y hy s hs)
        calc ‖fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y)‖
            ≤ ‖fderiv ℝ ω (y + s • e) e‖ * ‖fderiv ℝ ζ y‖ :=
              (fderiv ℝ ω (y + s • e) e).le_opNorm _
          _ ≤ C * ‖fderiv ℝ ζ y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      · rw [hDζ0 y hy, ContinuousLinearMap.map_zero, norm_zero, norm_zero, mul_zero]
    -- (c) differentiation under the integral sign
    obtain ⟨hint, hder⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (s : ℝ) (y : Rn n) => ω (y + s • e) (fderiv ℝ ζ y))
      (F' := fun (s : ℝ) (y : Rn n) => fderiv ℝ ω (y + s • e) e (fderiv ℝ ζ y))
      (bound := fun y => C * ‖fderiv ℝ ζ y‖) hball
      (Filter.eventually_of_mem hball fun s hs => (hcont s hs ω hωc).aestronglyMeasurable)
      ((hcont 0 h0 ω hωc).integrable_of_hasCompactSupport (hζc.mono' (hsupp _)))
      (hcont 0 h0 _ hDωe).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y s hs => hbound y s hs)
      (hDζint.const_mul C)
      (Filter.Eventually.of_forall fun y s hs => hderiv y s hs)
    simp only [zero_smul, add_zero] at hint hder
    exact ⟨hint, hder⟩
  obtain ⟨hint₁, hder₁⟩ := key ω₁ hω₁
  obtain ⟨hint₂, hder₂⟩ := key ω₂ hω₂
  -- Step 4: the translated weak identity gives `I₁ = I₂` near `0`.
  have heq : (fun s : ℝ => ∫ y, ω₁ (y + s • e) (fderiv ℝ ζ y)) =ᶠ[𝓝 0]
      (fun s : ℝ => ∫ y, ω₂ (y + s • e) (fderiv ℝ ζ y)) := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with s hs
    exact Submission.dohr_eb_lhr_ds_translate_weak_eq n ℓ U ω₁ ω₂ e s ζ hweak hζ hζc
      (fun y hy => hmemU y hy s hs)
  -- Step 6: hence the derivatives at `0` agree.
  have hD : ∫ y, fderiv ℝ ω₁ y e (fderiv ℝ ζ y) = ∫ y, fderiv ℝ ω₂ y e (fderiv ℝ ζ y) :=
    (hder₁.congr_of_eventuallyEq heq.symm).unique hder₂
  -- Step 7: the integrands vanish off `U`.
  have hzero : ∀ (ω : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (x : Rn n), x ∉ U →
      fderiv ℝ ω x e (fderiv ℝ ζ x) = 0 := by
    intro ω x hx
    rw [hDζ0 x (fun hxK => hx (hζU hxK)), ContinuousLinearMap.map_zero]
  refine ⟨hint₁.integrableOn, hint₂.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₁),
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzero ω₂)]
  exact hD
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): the differentiated system.**
Let `a(x)` be bilinear forms and `Φ(x)` linear forms on `L = L(ℝⁿ, ℝ^ℓ)`, componentwise `C¹` on
the open set `U`, and let `v ∈ C²(U)` solve `∫_U a(x)[Dv(x)][Dζ(x)] = ∫_U Φ(x)[Dζ(x)]` for all
`ζ ∈ C¹_c(U)`.  Then `v_e = Dv(·) e` solves `∫_U a(x)[Dv_e(x)][Dζ(x)] = ∫_U Ψ(x)[Dζ(x)]` with
`Ψ(x)[P] = D(Φ(·)[P])(x) e − D(a(·)[Dv(x)][P])(x) e` on `U`.
Proof: put `ω₁ = a(·)[Dv(·)]`, `ω₂ = Φ` (both `C¹` into `L*`) and
`Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e`, which has the stated values since evaluation commutes with
differentiation.  Differentiating the weak identity `∫_U ω₁[Dζ] = ∫_U ω₂[Dζ]` in the direction
`e` gives `∫_U (Dω₁ e)[Dζ] = ∫_U (DΦ e)[Dζ]`, both integrands integrable on `U`.  On `U` the
Leibniz rule and `D v_e = D(Dv) e` give `(Dω₁ e)[Dζ] = a[Dv_e][Dζ] + c` and
`(DΦ e)[Dζ] = Ψ[Dζ] + c` with `c(x) = D(a(·)[Dv(x)][Dζ(x)])(x) e`.  If `c` is integrable on `U`,
subtract `∫_U c`; otherwise neither `a[Dv_e][Dζ]` nor `Ψ[Dζ]` is integrable on `U` and both
integrals vanish. -/
theorem dohr_eb_lhr_differentiated_system : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (e : Rn n), IsOpen U → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U) → ContDiffOn ℝ 2 v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ∃ Ψ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, Ψ x P = fderiv ℝ (fun z => Φ z P) x e - fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x) = ∫ x in U, Ψ x (fderiv ℝ ζ x) := by
  intro n ℓ U a Φ v e hU ha hΦ hv hweak
  -- Step 1: `Φ` is `C¹` into `L*`, and so is the frozen family `z ↦ a(z)[Dv(x)]`; for both,
  -- evaluation at `P` commutes with differentiation.
  obtain ⟨hΦ1, hΦd⟩ := Submission.dohr_eb_lhr_ds_clm_family n ℓ U Φ hU hΦ
  have hfrozen : ∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ,
      fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e P =
        fderiv ℝ (fun z => a z (fderiv ℝ v x) P) x e := fun x hx P =>
    (Submission.dohr_eb_lhr_ds_clm_family n ℓ U (fun z => a z (fderiv ℝ v x)) hU
      (fun Q => ha (fderiv ℝ v x) Q)).2 x hx e P
  -- Step 2: `Dv` is `C¹` on `U`, so `ω₁ = a(·)[Dv(·)]` is `C¹` and obeys the Leibniz rule.
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨hω₁, hω₁d⟩ := Submission.dohr_eb_lhr_ds_bilin_leibniz n ℓ U a (fderiv ℝ v) e hU ha hDv
  -- Step 3: `Ψ(x) = DΦ(x) e − D(a(·)[Dv(x)])(x) e` has the stated values on `U`.
  refine ⟨fun x => fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e, ?_, ?_⟩
  · intro x hx P
    rw [sub_apply, hΦd x hx e P, hfrozen x hx P]
  intro ζ hζ hζc hζU
  -- Step 4: differentiate the weak identity for `(ω₁, Φ)` in the direction `e`.
  obtain ⟨hF₁, hF₂, hF⟩ := Submission.dohr_eb_lhr_ds_weak_eq_fderiv n ℓ U
    (fun x => a x (fderiv ℝ v x)) Φ e hU hω₁ hΦ1 hweak ζ hζ hζc hζU
  -- Step 5: on `U`, both integrands differ from the derivatives by the same term `c`.
  obtain ⟨c, hc⟩ : ∃ c : Rn n → ℝ,
      c = fun x => fderiv ℝ (fun z => a z (fderiv ℝ v x) (fderiv ℝ ζ x)) x e := ⟨_, rfl⟩
  have hU' : MeasurableSet U := hU.measurableSet
  have h₁ : EqOn (fun x => a x (fderiv ℝ (fun z => fderiv ℝ v z e) x) (fderiv ℝ ζ x))
      (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [hω₁d x hx (fderiv ℝ ζ x), Submission.dohr_eb_lhr_ds_fderiv_dirDeriv_eq n ℓ U v e hU hv x hx,
      add_sub_cancel_right]
  have h₂ : EqOn (fun x => (fderiv ℝ Φ x e - fderiv ℝ (fun z => a z (fderiv ℝ v x)) x e)
      (fderiv ℝ ζ x)) (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U := by
    intro x hx
    simp only [hc]
    rw [sub_apply, hfrozen x hx (fderiv ℝ ζ x)]
  rw [setIntegral_congr_fun hU' h₁, setIntegral_congr_fun hU' h₂]
  -- Step 6: subtract `∫_U c` if `c` is integrable on `U`; otherwise both sides are `0`.
  by_cases hcI : IntegrableOn c U
  · rw [integral_sub hF₁ hcI, integral_sub hF₂ hcI, hF]
  · have hn₁ : ¬ IntegrableOn
        (fun x => fderiv ℝ (fun x => a x (fderiv ℝ v x)) x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₁.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    have hn₂ : ¬ IntegrableOn (fun x => fderiv ℝ Φ x e (fderiv ℝ ζ x) - c x) U :=
      fun h => hcI ((hF₂.sub h).congr_fun (fun x _ => sub_sub_cancel _ _) hU')
    rw [integral_undef hn₁, integral_undef hn₂]
/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1 (pp. 127–128): local `C^{j,α}`
classes are closed under `h - ∑ᵢ fᵢ` and under modification outside the open set `U`.  If `h` and
every `fᵢ` are `C^j` on `U` with `Dʲ` `α`-Hölder on every compact `K ⊆ U`, and `g = h - ∑ᵢ fᵢ` on
`U`, then `g` is `C^j` on `U`; as `U` is open, `Dʲg = Dʲh - ∑ᵢ Dʲfᵢ` on `U`
(`Filter.EventuallyEq.iteratedFDeriv`), so the triangle inequality turns Hölder constants `C_h`,
`Cᵢ` on `K` into the constant `max C_h 0 + ∑ᵢ max Cᵢ 0` for `Dʲg`. -/
theorem dohr_eb_lhr_holder_loc_sub_sum : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j N : ℕ) (α : ℝ) (U : Set (Rn n)) (h g : Rn n → E) (f : Fin N → Rn n → E), IsOpen U → ContDiffOn ℝ j h U → (∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖ ≤ C * ‖x - y‖ ^ α) → (∀ i : Fin N, ContDiffOn ℝ j (f i) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ x ∈ U, g x = h x - ∑ i, f i x) → ContDiffOn ℝ j g U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n E _ _ j N α U h g f hU hh hhol hf hg
  -- Step 1: `G := h - ∑ i, f i` is `C^j` on `U`.
  have hG : ContDiffOn ℝ j (fun x => h x - ∑ i, f i x) U :=
    hh.sub (ContDiffOn.sum fun i _ => (hf i).1)
  -- Step 2: on the open set `U`, `g = G` near each point, so `Dʲg = Dʲh - ∑ i, Dʲfᵢ` there.
  have hiter : ∀ x ∈ U, iteratedFDeriv ℝ j g x
      = iteratedFDeriv ℝ j h x - ∑ i, iteratedFDeriv ℝ j (f i) x := by
    intro x hx
    have hxU : U ∈ 𝓝 x := hU.mem_nhds hx
    have heq : g =ᶠ[𝓝 x] fun z => h z - ∑ i, f i z := Filter.eventually_of_mem hxU hg
    have hfx : ∀ i ∈ (Finset.univ : Finset (Fin N)), ContDiffAt ℝ j (f i) x :=
      fun i _ => (hf i).1.contDiffAt hxU
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds,
      fun_iteratedFDeriv_sub_apply (hh.contDiffAt hxU) (ContDiffAt.sum hfx),
      iteratedFDeriv_fun_sum_apply hfx]
  refine ⟨hG.congr hg, fun K hK hKU => ?_⟩
  -- Step 3: Hölder constants of `Dʲh` and of every `Dʲfᵢ` on `K`, made nonnegative.
  obtain ⟨Ch, hCh⟩ := hhol K hK hKU
  choose Cf hCf using fun i => (hf i).2 K hK hKU
  refine ⟨max Ch 0 + ∑ i, max (Cf i) 0, fun x hx y hy => ?_⟩
  have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
  -- Step 4: the triangle inequality.
  rw [hiter x (hKU hx), hiter y (hKU hy)]
  calc ‖(iteratedFDeriv ℝ j h x - ∑ i, iteratedFDeriv ℝ j (f i) x)
        - (iteratedFDeriv ℝ j h y - ∑ i, iteratedFDeriv ℝ j (f i) y)‖
      = ‖(iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y)
          - ∑ i, (iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y)‖ := by
        rw [Finset.sum_sub_distrib]; congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ j h x - iteratedFDeriv ℝ j h y‖
          + ∑ i, ‖iteratedFDeriv ℝ j (f i) x - iteratedFDeriv ℝ j (f i) y‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ max Ch 0 * ‖x - y‖ ^ α + ∑ i, max (Cf i) 0 * ‖x - y‖ ^ α := by
        gcongr with i
        · exact (hCh x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
        · exact (hCf i x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
    _ = (max Ch 0 + ∑ i, max (Cf i) 0) * ‖x - y‖ ^ α := by
        rw [add_mul, Finset.sum_mul]
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): under the change of variables `x = y + ρ z` with `ρ > 0`, which maps `B̆_r(0)` onto
`B̆_{ρr}(y)`, the Hölder bound `‖ρ g(y + ρ z) − ρ g(y + ρ z')‖ ≤ c ‖z − z'‖^α` on `B̆_r(0)` is
equivalent to the scale-weighted bound `ρ^{1+α} ‖g(x) − g(x')‖ ≤ c ‖x − x'‖^α` on `B̆_{ρr}(y)`,
because `ρ^{1+α} = ρ ρ^α` and `‖x − x'‖^α = ρ^α ‖z − z'‖^α`. -/
theorem dohr_eb_sch_ube_holder_rescale : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (y : Rn n) (ρ r α c : ℝ), 0 < ρ → ((∀ z ∈ ball (0 : Rn n) r, ∀ z' ∈ ball (0 : Rn n) r, ‖ρ • g (y + ρ • z) - ρ • g (y + ρ • z')‖ ≤ c * ‖z - z'‖ ^ α) ↔ ∀ x ∈ ball y (ρ * r), ∀ x' ∈ ball y (ρ * r), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ c * ‖x - x'‖ ^ α) := by
  intro n ℓ g y ρ r α c hρ
  -- Step 1: `ρ^α > 0`, `ρ^{1+α} = ρ ρ^α`, `‖(y + ρ z) − (y + ρ z')‖^α = ρ^α ‖z − z'‖^α` and
  -- `‖ρ A − ρ B‖ = ρ ‖A − B‖`.
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hnorm : ∀ z z' : Rn n, ‖(y + ρ • z) - (y + ρ • z')‖ ^ α = ρ ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg _)]
  have hsm : ∀ u v : Rn n →L[ℝ] Rn ℓ, ‖ρ • u - ρ • v‖ = ρ * ‖u - v‖ := by
    intro u v
    rw [show ρ • u - ρ • v = ρ • (u - v) from (smul_sub ρ u v).symm, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
  -- Step 2: `z(x) = ρ⁻¹ (x − y)` satisfies `y + ρ z(x) = x` and maps `B̆_{ρr}(y)` into `B̆_r(0)`.
  have hback : ∀ x : Rn n, y + ρ • (ρ⁻¹ • (x - y)) = x := by
    intro x
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hinball : ∀ x ∈ ball y (ρ * r), ρ⁻¹ • (x - y) ∈ ball (0 : Rn n) r := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ,
      inv_mul_lt_iff₀ hρ]
    exact hx
  constructor
  -- Step 3: (a) ⇒ (b), multiplying the bound at `z(x), z(x')` by `ρ^α > 0`.
  · intro h x hx x' hx'
    have h1 := h _ (hinball x hx) _ (hinball x' hx')
    rw [hback, hback, hsm] at h1
    have h2 := hnorm (ρ⁻¹ • (x - y)) (ρ⁻¹ • (x' - y))
    rw [hback, hback] at h2
    rw [hsplit, h2]
    calc ρ * ρ ^ α * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by ring
      _ ≤ ρ ^ α * (c * ‖ρ⁻¹ • (x - y) - ρ⁻¹ • (x' - y)‖ ^ α) := by gcongr
      _ = c * (ρ ^ α * ‖ρ⁻¹ • (x - y) - ρ⁻¹ • (x' - y)‖ ^ α) := by ring
  -- Step 4: (b) ⇒ (a), cancelling the factor `ρ^α > 0` in the bound at `y + ρ z, y + ρ z'`.
  · intro h z hz z' hz'
    have hmap : ∀ u ∈ ball (0 : Rn n) r, y + ρ • u ∈ ball y (ρ * r) := by
      intro u hu
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      rw [mem_ball_zero_iff] at hu
      exact mul_lt_mul_of_pos_left hu hρ
    have h1 := h _ (hmap z hz) _ (hmap z' hz')
    rw [hsplit, hnorm] at h1
    rw [hsm]
    have h2 : ρ ^ α * (ρ * ‖g (y + ρ • z) - g (y + ρ • z')‖) ≤ ρ ^ α * (c * ‖z - z'‖ ^ α) := by
      calc ρ ^ α * (ρ * ‖g (y + ρ • z) - g (y + ρ • z')‖)
          = ρ * ρ ^ α * ‖g (y + ρ • z) - g (y + ρ • z')‖ := by ring
        _ ≤ c * (ρ ^ α * ‖z - z'‖ ^ α) := h1
        _ = ρ ^ α * (c * ‖z - z'‖ ^ α) := by ring
    exact le_of_mul_le_mul_left h2 hρα
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): if `ρ > 0` and `|y₀| + ρ ≤ 1`, the rescaled data `a(y₀ + ρ z)`, `ρ Φ(y₀ + ρ z)` and
`w(y₀ + ρ z)` on `B̆₁(0)` satisfy the structure conditions of `a`, `Φ`, `w` with the same
constants.  The map `z ↦ y₀ + ρ z` sends `B̆₁(0)` into itself and multiplies distances by
`ρ ≤ 1`, so the Hölder quotients acquire the factors `ρ^α ≤ 1` and `ρ ρ^α ≤ 1`. -/
theorem dohr_eb_sch_ube_rescaled_structure : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (y₀ : Rn n) (ρ α lam M : ℝ), 0 < ρ → ‖y₀‖ + ρ ≤ 1 → 0 ≤ α → 0 ≤ M → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → (∀ z ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a (y₀ + ρ • z) P P) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q| ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) ∧ (∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |(ρ • Φ (y₀ + ρ • z)) P - (ρ • Φ (y₀ + ρ • z')) P| ≤ M * ‖z - z'‖ ^ α * ‖P‖) ∧ ∀ z ∈ ball (0 : Rn n) 1, ‖w (y₀ + ρ • z)‖ ≤ M := by
  intro n ℓ a Φ w y₀ ρ α lam M hρ hyρ hα hM h1 h2 h3 h4 h5
  -- Step 1: `0 < ρ ≤ 1`, hence `ρ^α ≤ 1`.
  have hρ1 : ρ ≤ 1 := by linarith [norm_nonneg y₀]
  have hρα : ρ ^ α ≤ 1 := Real.rpow_le_one hρ.le hρ1 hα
  have hρα0 : 0 ≤ ρ ^ α := Real.rpow_nonneg hρ.le α
  -- Step 2: `z ↦ y₀ + ρ z` maps `B̆₁(0)` into `B̆₁(0)`.
  have hmap : ∀ z ∈ ball (0 : Rn n) 1, y₀ + ρ • z ∈ ball (0 : Rn n) 1 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖y₀ + ρ • z‖ ≤ ‖y₀‖ + ‖ρ • z‖ := norm_add_le _ _
      _ = ‖y₀‖ + ρ * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      _ < ‖y₀‖ + ρ * 1 := by gcongr
      _ ≤ 1 := by linarith
  -- Step 3: `|(y₀ + ρ z) − (y₀ + ρ z')|^α = ρ^α |z − z'|^α`.
  have hdiff : ∀ z z' : Rn n, ‖(y₀ + ρ • z) - (y₀ + ρ • z')‖ ^ α = ρ ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg _)]
  -- Step 4: (i), (ii), (v) hold pointwise at `y₀ + ρ z ∈ B̆₁(0)`.
  refine ⟨fun z hz P => h1 _ (hmap z hz) P, fun z hz P Q => h2 _ (hmap z hz) P Q, ?_, ?_,
    fun z hz => h5 _ (hmap z hz)⟩
  -- Step 5: (iii), discarding the factor `ρ^α ≤ 1` as `M ≥ 0`.
  · intro z hz z' hz' P Q
    have h := h3 _ (hmap z hz) _ (hmap z' hz') P Q
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _))
        (norm_nonneg _)) (norm_nonneg _)
    calc |a (y₀ + ρ • z) P Q - a (y₀ + ρ • z') P Q|
        ≤ M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = ρ ^ α * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) := mul_le_mul_of_nonneg_right hρα hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := one_mul _
  -- Step 6: (iv), as `(ρ Φ(u))[P] = ρ Φ(u)[P]`, discarding the factor `ρ ρ^α ≤ 1`.
  · intro z hz z' hz' P
    have h := h4 _ (hmap z hz) _ (hmap z' hz') P
    rw [hdiff] at h
    have hX : 0 ≤ M * ‖z - z'‖ ^ α * ‖P‖ :=
      mul_nonneg (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos hρ]
    have hρρ : ρ * ρ ^ α ≤ 1 := by nlinarith
    calc ρ * |Φ (y₀ + ρ • z) P - Φ (y₀ + ρ • z') P|
        ≤ ρ * (M * (ρ ^ α * ‖z - z'‖ ^ α) * ‖P‖) := by gcongr
      _ = (ρ * ρ ^ α) * (M * ‖z - z'‖ ^ α * ‖P‖) := by ring
      _ ≤ 1 * (M * ‖z - z'‖ ^ α * ‖P‖) := mul_le_mul_of_nonneg_right hρρ hX
      _ = M * ‖z - z'‖ ^ α * ‖P‖ := one_mul _
/-- One-step improvement of a scale-weighted Hölder bound (steps 3–5 of the absorption argument
for the interior `C^{1,α}` Schauder estimate on the unit ball, in the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1).  Let `g : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` (operator norm), `0 < α ≤ 1` and
`M, A, Q ≥ 0`; call `(y, ρ)` admissible if `ρ > 0` and `|y| + ρ ≤ 1`.  Assume
(P1) `ρ^{1+α} ‖g(x) − g(x')‖ ≤ Q |x − x'|^α` on `B̆_{ρ/2}(y)` for admissible `(y, ρ)`;
(P2) for admissible `(y, ρ)` and real `K`, if `‖g(x) − g(x')‖ ≤ K |x − x'|^α` on `B̆_ρ(y)`, then
`ρ^{1+α} ‖g(x) − g(x')‖ ≤ ((1/16) ρ^{1+α} K + A) |x − x'|^α` on `B̆_{ρ/2}(y)`;
(P3) `‖g(x)‖ ≤ 2M/t + t^α K` whenever `|x| + r ≤ 1`, `K ≥ 0`, `0 < t < r` and
`‖g(z) − g(z')‖ ≤ K |z − z'|^α` on `B̆_r(x)`.
Then for admissible `(y, ρ)`: `ρ ‖g(x)‖ ≤ 32 M + Q/4 + 16 A` on `B̆_{ρ/2}(y)`, and
`ρ^{1+α} ‖g(x) − g(x')‖ ≤ (Q/2 + 512 M + 32 A) |x − x'|^α` on `B̆_{ρ/2}(y)`. -/
theorem dohr_eb_sch_ube_holder_improvement : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A Q : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → 0 ≤ Q → (∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + Q / 4 + 16 * A) ∧ ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
  intro n ℓ g α M A Q hα0 hα1 hM hA hQ0 hP1 hP2 hP3 y ρ hρ hyρ
  -- Step 1: points `x` of `B̆_{ρ/2}(y)` have `|x| + ρ/2 < 1`.
  have hxnorm : ∀ x ∈ ball y (ρ / 2), ‖x‖ + ρ / 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    linarith
  -- Step 2: numerical facts about the powers.
  have hR : 0 < ρ ^ (1 + α) := Real.rpow_pos_of_pos hρ _
  have hsplit : ρ ^ (1 + α) = ρ * ρ ^ α := by rw [Real.rpow_add hρ, Real.rpow_one]
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have p2pos : (0:ℝ) < 2 ^ (1 + α) := by positivity
  have p4pos : (0:ℝ) < 4 ^ (1 + α) := by positivity
  have p2ne : (2:ℝ) ^ (1 + α) ≠ 0 := p2pos.ne'
  have p4ne : (4:ℝ) ^ (1 + α) ≠ 0 := p4pos.ne'
  have hRne : ρ ^ (1 + α) ≠ 0 := hR.ne'
  have p2le : (2:ℝ) ^ (1 + α) ≤ 4 := by
    calc (2:ℝ) ^ (1 + α) ≤ 2 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have p4le : (4:ℝ) ^ (1 + α) ≤ 16 := by
    calc (4:ℝ) ^ (1 + α) ≤ 4 ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 16 := by rw [Real.rpow_two]; norm_num
  have hH0 : 0 ≤ Q / 4 + 16 * A := by linarith
  -- Step 3: `ρ^{1+α} |g(z) − g(z')| ≤ (Q/4 + 16 A) |z − z'|^α` on `B̆_{ρ/8}(x)`, by (P1) at
  -- `(x, ρ/2)` and (P2) at `(x, ρ/4)`.
  have hsmall : ∀ x ∈ ball y (ρ / 2), ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
      ρ ^ (1 + α) * ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
    intro x hx z hz z' hz'
    have hx1 := hxnorm x hx
    have hρ2 : 0 < ρ / 2 := by positivity
    have hρ4 : 0 < ρ / 4 := by positivity
    have e2 : (ρ / 2) ^ (1 + α) = ρ ^ (1 + α) / 2 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have e4 : (ρ / 4) ^ (1 + α) = ρ ^ (1 + α) / 4 ^ (1 + α) :=
      Real.div_rpow hρ.le (by norm_num) _
    have hpos2 : 0 < (ρ / 2) ^ (1 + α) := Real.rpow_pos_of_pos hρ2 _
    have hHolK : ∀ u ∈ ball x (ρ / 4), ∀ u' ∈ ball x (ρ / 4),
        ‖g u - g u'‖ ≤ Q / (ρ / 2) ^ (1 + α) * ‖u - u'‖ ^ α := by
      intro u hu u' hu'
      have e : ρ / 2 / 2 = ρ / 4 := by ring
      have h := hP1 x (ρ / 2) hρ2 hx1.le u (by rwa [e]) u' (by rwa [e])
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos2]
      linarith
    have hx4 : ‖x‖ + ρ / 4 ≤ 1 := by linarith
    have e8 : ρ / 4 / 2 = ρ / 8 := by ring
    have h1 := hP2 x (ρ / 4) (Q / (ρ / 2) ^ (1 + α)) hρ4 hx4 hHolK z (by rwa [e8])
      z' (by rwa [e8])
    rw [e4, e2] at h1
    have hd : 0 ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have key : 1 / 16 * (ρ ^ (1 + α) / 4 ^ (1 + α)) * (Q / (ρ ^ (1 + α) / 2 ^ (1 + α)))
        = Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) := by
      field_simp
    rw [key] at h1
    have h2 : ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
      have h3 := mul_le_mul_of_nonneg_left h1 p4pos.le
      calc ρ ^ (1 + α) * ‖g z - g z'‖
          = 4 ^ (1 + α) * (ρ ^ (1 + α) / 4 ^ (1 + α) * ‖g z - g z'‖) := by
            field_simp
        _ ≤ 4 ^ (1 + α) * ((Q * 2 ^ (1 + α) / (16 * 4 ^ (1 + α)) + A) * ‖z - z'‖ ^ α) := h3
        _ = (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := by
            field_simp
    calc ρ ^ (1 + α) * ‖g z - g z'‖
        ≤ (Q * 2 ^ (1 + α) / 16 + A * 4 ^ (1 + α)) * ‖z - z'‖ ^ α := h2
      _ ≤ (Q / 4 + 16 * A) * ‖z - z'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd
          have q1 := mul_le_mul_of_nonneg_left p2le hQ0
          have q2 := mul_le_mul_of_nonneg_left p4le hA
          linarith
  -- Step 4: `ρ |g(x)| ≤ 32 M + (Q/4 + 16 A) / 16^α`, by (P3) with `r = ρ/8`, `t = ρ/16`.
  have hsupfine : ∀ x ∈ ball y (ρ / 2), ρ * ‖g x‖ ≤ 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
    intro x hx
    have hx1 := hxnorm x hx
    have hK0 : 0 ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) := div_nonneg hH0 hR.le
    have hHol8 : ∀ z ∈ ball x (ρ / 8), ∀ z' ∈ ball x (ρ / 8),
        ‖g z - g z'‖ ≤ (Q / 4 + 16 * A) / ρ ^ (1 + α) * ‖z - z'‖ ^ α := by
      intro z hz z' hz'
      have h := hsmall x hx z hz z' hz'
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    have h := hP3 x (ρ / 8) (ρ / 16) ((Q / 4 + 16 * A) / ρ ^ (1 + α)) (by linarith) hK0
      (by positivity) (by linarith) hHol8
    have e16 : (ρ / 16) ^ α = ρ ^ α / 16 ^ α := Real.div_rpow hρ.le (by norm_num) _
    rw [e16, hsplit] at h
    have p16 : (0:ℝ) < 16 ^ α := by positivity
    have p16ne : (16:ℝ) ^ α ≠ 0 := p16.ne'
    have hραne : ρ ^ α ≠ 0 := hρα.ne'
    have hρne : ρ ≠ 0 := hρ.ne'
    have hid : ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α)))
        = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := by
      field_simp
      ring
    calc ρ * ‖g x‖
        ≤ ρ * (2 * M / (ρ / 16) + ρ ^ α / 16 ^ α * ((Q / 4 + 16 * A) / (ρ * ρ ^ α))) :=
          mul_le_mul_of_nonneg_left h hρ.le
      _ = 32 * M + (Q / 4 + 16 * A) / 16 ^ α := hid
  have h16 : (1:ℝ) ≤ 16 ^ α := Real.one_le_rpow (by norm_num) hα0.le
  refine ⟨?_, ?_⟩
  -- Step 5: conclusion (a), since `16^α ≥ 1`.
  · intro x hx
    have h := hsupfine x hx
    have : (Q / 4 + 16 * A) / 16 ^ α ≤ Q / 4 + 16 * A := div_le_self hH0 h16
    linarith
  -- Step 6: conclusion (b), by cases `|x − x'| < ρ/8` (step 3) and `|x − x'| ≥ ρ/8` (step 4).
  · intro x hx x' hx'
    have hd : 0 ≤ ‖x - x'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hcase : ‖x - x'‖ < ρ / 8
    · have hxin : x ∈ ball x (ρ / 8) := mem_ball_self (by positivity)
      have hx'in : x' ∈ ball x (ρ / 8) := by
        rw [mem_ball, dist_comm, dist_eq_norm]; exact hcase
      have h := hsmall x hx x hxin x' hx'in
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (Q / 4 + 16 * A) * ‖x - x'‖ ^ α := h
        _ ≤ (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by
          apply mul_le_mul_of_nonneg_right _ hd; linarith
    · push Not at hcase
      have hdl : (ρ / 8) ^ α ≤ ‖x - x'‖ ^ α := Real.rpow_le_rpow (by positivity) hcase hα0.le
      have e8 : (ρ / 8) ^ α = ρ ^ α / 8 ^ α := Real.div_rpow hρ.le (by norm_num) _
      have p8 : (0:ℝ) < 8 ^ α := by positivity
      have p16 : (0:ℝ) < 16 ^ α := by positivity
      have hρα8 : ρ ^ α ≤ 8 ^ α * ‖x - x'‖ ^ α := by
        rw [e8, div_le_iff₀ p8] at hdl; linarith
      have h8 : (8:ℝ) ^ α ≤ 8 := by
        calc (8:ℝ) ^ α ≤ 8 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 8 := Real.rpow_one 8
      have h816 : (8:ℝ) ^ α ≤ 16 ^ α := Real.rpow_le_rpow (by norm_num) (by norm_num) hα0.le
      have hA1 : ρ ^ α ≤ 8 * ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h8 hd
        linarith
      have hA2 : ρ ^ α / 16 ^ α ≤ ‖x - x'‖ ^ α := by
        have := mul_le_mul_of_nonneg_right h816 hd
        rw [div_le_iff₀ p16]
        linarith
      have hsx := hsupfine x hx
      have hsx' := hsupfine x' hx'
      have htri : ‖g x - g x'‖ ≤ ‖g x‖ + ‖g x'‖ := norm_sub_le _ _
      calc ρ ^ (1 + α) * ‖g x - g x'‖ = ρ ^ α * (ρ * ‖g x - g x'‖) := by rw [hsplit]; ring
        _ ≤ ρ ^ α * (ρ * ‖g x‖ + ρ * ‖g x'‖) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            rw [← mul_add]
            exact mul_le_mul_of_nonneg_left htri hρ.le
        _ ≤ ρ ^ α * (2 * (32 * M + (Q / 4 + 16 * A) / 16 ^ α)) := by
            apply mul_le_mul_of_nonneg_left _ hρα.le
            linarith
        _ = 64 * M * ρ ^ α + 2 * (Q / 4 + 16 * A) * (ρ ^ α / 16 ^ α) := by ring
        _ ≤ 64 * M * (8 * ‖x - x'‖ ^ α) + 2 * (Q / 4 + 16 * A) * ‖x - x'‖ ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hA1 (by linarith))
              (mul_le_mul_of_nonneg_left hA2 (by linarith))
        _ = (Q / 2 + 512 * M + 32 * A) * ‖x - x'‖ ^ α := by ring
/-- Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion
(p. 127): absorption by the best scale-weighted Hölder constant.  Call `(y, ρ)` admissible if
`ρ > 0` and `|y| + ρ ≤ 1`.  Let `Q` be the supremum of `0` and of the quotients
`ρ^{1+α} ‖g x - g x'‖ / |x - x'|^α` over admissible `(y, ρ)` and `x ≠ x'` in `B̆_{ρ/2}(y)`; it is
finite because `ρ^{1+α} ≤ 1` and `g` is `α`-Hölder on `B̆₁(0)`.  The one-step improvement
`dohr_eb_sch_ube_holder_improvement` for this `Q` gives `Q ≤ Q/2 + 512 M + 32 A`, so
`Q ≤ 1024 M + 64 A`, and the admissible pair `(0, 1)` gives both bounds on `B̆_{1/2}(0)`. -/
theorem dohr_eb_sch_ube_absorption : ∀ (n ℓ : ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)) (α M A : ℝ), 0 < α → α ≤ 1 → 0 ≤ M → 0 ≤ A → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α) → (∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖g x - g x'‖ ≤ K * ‖x - x'‖ ^ α) → ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ (1 / 16 * ρ ^ (1 + α) * K + A) * ‖x - x'‖ ^ α) → (∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r → (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖g z - g z'‖ ≤ K * ‖z - z'‖ ^ α) → ‖g x‖ ≤ 2 * M / t + t ^ α * K) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖g x‖ ≤ 1024 * M + 64 * A) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖g x - g y‖ ≤ (1024 * M + 64 * A) * ‖x - y‖ ^ α := by
  intro n ℓ g α M A hα0 hα1 hM hA hK hP2 hP3
  obtain ⟨K0, hK0⟩ := hK
  -- Step 1: for admissible `(y, ρ)`, `B̆_{ρ/2}(y) ⊆ B̆₁(0)`.
  have hmem : ∀ (y : Rn n) (ρ : ℝ) (x : Rn n), 0 < ρ → ‖y‖ + ρ ≤ 1 → x ∈ ball y (ρ / 2) →
      x ∈ ball (0 : Rn n) 1 := by
    intro y ρ x hρ hyρ hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      _ < ‖y‖ + ρ / 2 := by linarith
      _ ≤ 1 := by linarith
  -- Step 2: `T` is `0` together with the scale-weighted Hölder quotients; it is bounded above
  -- by `max K0 0`, so `Q := sup T` is a real number `≥ 0`.
  let T : Set ℝ := {q | q = 0 ∨ ∃ (y : Rn n) (ρ : ℝ) (x x' : Rn n), 0 < ρ ∧ ‖y‖ + ρ ≤ 1 ∧
      x ∈ ball y (ρ / 2) ∧ x' ∈ ball y (ρ / 2) ∧ x ≠ x' ∧
      q = ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α}
  have hbdd : BddAbove T := by
    refine ⟨max K0 0, ?_⟩
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · exact le_max_right _ _
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      have hρa : ρ ^ (1 + α) ≤ 1 :=
        Real.rpow_le_one hρ.le (by linarith [norm_nonneg y]) (by linarith)
      rw [div_le_iff₀ hpow]
      calc ρ ^ (1 + α) * ‖g x - g x'‖ ≤ 1 * ‖g x - g x'‖ :=
            mul_le_mul_of_nonneg_right hρa (norm_nonneg _)
        _ ≤ K0 * ‖x - x'‖ ^ α := by
            rw [one_mul]
            exact hK0 x (hmem y ρ x hρ hyρ hx) x' (hmem y ρ x' hρ hyρ hx')
        _ ≤ max K0 0 * ‖x - x'‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  have h0T : (0 : ℝ) ∈ T := Or.inl rfl
  set Q := sSup T
  have hQ0 : 0 ≤ Q := le_csSup hbdd h0T
  -- Step 3: (P1) holds with the constant `Q`.
  have hP1 : ∀ (y : Rn n) (ρ : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 → ∀ x ∈ ball y (ρ / 2),
      ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖g x - g x'‖ ≤ Q * ‖x - x'‖ ^ α := by
    intro y ρ hρ hyρ x hx x' hx'
    by_cases hne : x = x'
    · subst hne
      simp [Real.zero_rpow hα0.ne']
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      have hq : ρ ^ (1 + α) * ‖g x - g x'‖ / ‖x - x'‖ ^ α ∈ T :=
        Or.inr ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩
      have h := le_csSup hbdd hq
      rwa [div_le_iff₀ hpow] at h
  -- Step 4: the one-step improvement for this `Q`.
  have himp := Submission.dohr_eb_sch_ube_holder_improvement n ℓ g α M A Q hα0 hα1 hM hA hQ0
    hP1 hP2 hP3
  -- Step 5: absorption, `Q ≤ Q/2 + 512 M + 32 A`, hence `Q ≤ 1024 M + 64 A`.
  have hQle : Q ≤ Q / 2 + 512 * M + 32 * A := by
    refine csSup_le ⟨0, h0T⟩ ?_
    rintro q (rfl | ⟨y, ρ, x, x', hρ, hyρ, hx, hx', hne, rfl⟩)
    · linarith
    · have hpow : 0 < ‖x - x'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hne)) α
      rw [div_le_iff₀ hpow]
      exact (himp y ρ hρ hyρ).2 x hx x' hx'
  have hQC : Q ≤ 1024 * M + 64 * A := by linarith
  -- Step 6: the admissible pair `(0, 1)`.
  have h01 : ‖(0 : Rn n)‖ + 1 ≤ 1 := by simp
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h := (himp 0 1 one_pos h01).1 x hx
    rw [one_mul] at h
    linarith
  · have h := hP1 0 1 one_pos h01 x hx y hy
    rw [Real.one_rpow, one_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hQC (Real.rpow_nonneg (norm_nonneg _) _))
/-- Affine subtraction and scaling of a `C¹` weak solution (the integral computation in the blow-up
step of the Schauder estimate used for the elliptic bootstrap in Simon Ch. 5, 7.1): if `v` is `C¹`
on the open set `D`, `∫_D b[Dv][Dζ] = ∫_D Θ[Dζ]` for all `ζ ∈ C¹_c(D)`, and `B₀[P₀][Dζ]`, `Θ₀[Dζ]`
have integral `0` over `ℝⁿ` for all `ζ ∈ C¹_c`, then `V = s (v − c − P₀)` is `C¹` on `D` with
`DV = s (Dv − P₀)` and `∫_D b[DV][Dζ] = ∫_D (s ((Θ − Θ₀) − (b[P₀] − B₀[P₀])))[Dζ]`. -/
theorem dohr_eb_sch_bu_weak_eq_sub_affine : ∀ (n ℓ : ℕ) (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ) (D : Set (Rn n)) (B₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Θ₀ : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (P₀ : Rn n →L[ℝ] Rn ℓ) (c : Rn ℓ) (s : ℝ), IsOpen D → ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => b p.1 p.2.1 p.2.2) (D ×ˢ univ) → ContinuousOn Θ D → ContDiffOn ℝ 1 v D → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in D, Θ x (fderiv ℝ ζ x)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, B₀ P₀ (fderiv ℝ ζ x) = 0) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, Θ₀ (fderiv ℝ ζ x) = 0) → ContDiffOn ℝ 1 (fun x => s • (v x - c - P₀ x)) D ∧ (∀ x ∈ D, fderiv ℝ (fun x => s • (v x - c - P₀ x)) x = s • (fderiv ℝ v x - P₀)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → ∫ x in D, b x (fderiv ℝ (fun x => s • (v x - c - P₀ x)) x) (fderiv ℝ ζ x) = ∫ x in D, (s • ((Θ x - Θ₀) - (b x P₀ - B₀ P₀))) (fderiv ℝ ζ x) := by
  intro n ℓ b Θ v D B₀ Θ₀ P₀ c s hD hb hΘ hv hweak hB₀ hΘ₀
  -- (ii) as `HasFDerivAt`: on the open set `D`, `v` is differentiable and
  -- `D(s • (v - c - P₀)) = s • (Dv - P₀)`.
  have hderiv : ∀ x ∈ D,
      HasFDerivAt (fun x => s • (v x - c - P₀ x)) (s • (fderiv ℝ v x - P₀)) x := by
    intro x hx
    have hvx : DifferentiableAt ℝ v x :=
      (hv.differentiableOn_one x hx).differentiableAt (hD.mem_nhds hx)
    exact ((hvx.hasFDerivAt.sub_const c).sub P₀.hasFDerivAt).const_smul s
  refine ⟨((hv.sub contDiffOn_const).sub P₀.contDiff.contDiffOn).const_smul s,
    fun x hx => (hderiv x hx).fderiv, ?_⟩
  intro ζ hζ hζc hζD
  -- `Dζ` is continuous and vanishes off the compact set `tsupport ζ ⊆ D`.
  have hTc : IsCompact (tsupport ζ) := hζc
  have hζ' : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx =>
    Function.notMem_support.1 fun h => hx (support_fderiv_subset ℝ h)
  -- A function continuous on `D` that vanishes where `Dζ` does is integrable.
  have hint : ∀ g : Rn n → ℝ, ContinuousOn g D → (∀ x, fderiv ℝ ζ x = 0 → g x = 0) →
      Integrable g := fun g hg hg0 =>
    ((hg.mono hζD).integrableOn_compact hTc).integrable_of_forall_notMem_eq_zero
      fun x hx => hg0 x (hζ0 x hx)
  have hvc : ContinuousOn (fderiv ℝ v) D := hv.continuousOn_fderiv_of_isOpen hD le_rfl
  have hbc : ∀ P : Rn n → (Rn n →L[ℝ] Rn ℓ), ContinuousOn P D →
      ContinuousOn (fun x => b x (P x) (fderiv ℝ ζ x)) D := fun P hP =>
    hb.comp (continuousOn_id.prodMk (hP.prodMk hζ'.continuousOn)) fun x hx => ⟨hx, mem_univ _⟩
  have i1 : Integrable fun x => b x (fderiv ℝ v x) (fderiv ℝ ζ x) :=
    hint _ (hbc _ hvc) fun x hx => by rw [hx, map_zero]
  have i2 : Integrable fun x => b x P₀ (fderiv ℝ ζ x) :=
    hint _ (hbc _ continuousOn_const) fun x hx => by rw [hx, map_zero]
  have i3 : Integrable fun x => Θ x (fderiv ℝ ζ x) :=
    hint _ (hΘ.clm_apply hζ'.continuousOn) fun x hx => by rw [hx, map_zero]
  have i4 : Integrable fun x => Θ₀ (fderiv ℝ ζ x) :=
    hint _ (Θ₀.continuous.comp hζ').continuousOn fun x hx => by rw [hx, map_zero]
  have i5 : Integrable fun x => B₀ P₀ (fderiv ℝ ζ x) :=
    hint _ ((B₀ P₀).continuous.comp hζ').continuousOn fun x hx => by rw [hx, map_zero]
  have i34 : Integrable fun x => Θ x (fderiv ℝ ζ x) - Θ₀ (fderiv ℝ ζ x) := i3.sub i4
  have i25 : Integrable fun x => b x P₀ (fderiv ℝ ζ x) - B₀ P₀ (fderiv ℝ ζ x) := i2.sub i5
  -- The integrals of `Θ₀[Dζ]` and `B₀[P₀][Dζ]` over `D` are those over `ℝⁿ`, which vanish.
  have hz4 : ∫ x in D, Θ₀ (fderiv ℝ ζ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hζ0 x fun h => hx (hζD h), map_zero]]
    exact hΘ₀ ζ hζ hζc
  have hz5 : ∫ x in D, B₀ P₀ (fderiv ℝ ζ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hζ0 x fun h => hx (hζD h), map_zero]]
    exact hB₀ ζ hζ hζc
  -- Bilinearity: on `D`, `b[DV][Dζ] = s b[Dv][Dζ] - s b[P₀][Dζ]`.
  have hL : ∫ x in D, b x (fderiv ℝ (fun x => s • (v x - c - P₀ x)) x) (fderiv ℝ ζ x) =
      ∫ x in D, (s * b x (fderiv ℝ v x) (fderiv ℝ ζ x) - s * b x P₀ (fderiv ℝ ζ x)) := by
    refine setIntegral_congr_fun hD.measurableSet fun x hx => ?_
    simp only [(hderiv x hx).fderiv, map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul,
      mul_sub]
  -- Evaluate the right-hand side pointwise, split the integrals and use the weak equation.
  simp only [smul_apply, sub_apply, smul_eq_mul]
  rw [hL, integral_sub (i1.integrableOn.const_mul s) (i2.integrableOn.const_mul s),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_sub i34.integrableOn i25.integrableOn,
    integral_sub i3.integrableOn i4.integrableOn, integral_sub i2.integrableOn i5.integrableOn,
    hweak ζ hζ hζc hζD, hz4, hz5]
  ring
/-- **Diagonal extraction with one glued limit** (Simon Ch. 5, proof of Theorem 7.1: Hölder
compactness in the Schauder blow-up argument).  Let `F k : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` and `S m ⊆ ℝⁿ`.  If, for
every `m`, every subsequence `F ∘ ψ` has a further subsequence `F ∘ ψ ∘ χ` converging uniformly on
`S m`, then a single subsequence `F ∘ φ` converges uniformly on every `S m` to one limit `V`.

Proof: iterate the extractions, `Ψ 0 = id` and `Ψ (m + 1) = Ψ m ∘ χ_m` with `F ∘ Ψ (m + 1) → g_m`
uniformly on `S m`, and take the diagonal `φ j = Ψ (j + 1) j`; it is strictly increasing because
`χ i ≥ i` for strictly increasing `χ`.  Since `Ψ (m + d) = Ψ m ∘ ρ` with `ρ` strictly increasing,
for `j ≥ m` the index `φ j` is the term of `Ψ (m + 1)` at a position `τ j ≥ j`, so `F ∘ φ → g_m`
uniformly on `S m`.  Put `V z = g_{m(z)} z` for the least `m(z)` with `z ∈ S m(z)` (and `V z = 0`
off `⋃ S m`); uniqueness of limits gives `V = g_m` on `S m`. -/
theorem dohr_eb_sch_bu_hds_diagonal_extract : ∀ (n ℓ : ℕ) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (S : ℕ → Set (Rn n)), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧ TendstoUniformlyOn (fun j => F (ψ (χ j))) g atTop (S m)) → ∃ (φ : ℕ → ℕ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono φ ∧ ∀ m : ℕ, TendstoUniformlyOn (fun j => F (φ j)) V atTop (S m) := by
  intro n ℓ F S h
  -- Step 1: choose `χ m ψ` and `g m ψ` for every `ψ`; the convergence is only claimed for
  -- strictly increasing `ψ` (otherwise take `χ = id`, `g = 0`).
  have h' : ∀ (m : ℕ) (ψ : ℕ → ℕ), ∃ (χ : ℕ → ℕ) (g : Rn n → (Rn n →L[ℝ] Rn ℓ)),
      StrictMono χ ∧ (StrictMono ψ → TendstoUniformlyOn (fun j => F (ψ (χ j))) g atTop (S m)) := by
    intro m ψ
    by_cases hψ : StrictMono ψ
    · obtain ⟨χ, g, hχ, hg⟩ := h m ψ hψ
      exact ⟨χ, g, hχ, fun _ => hg⟩
    · exact ⟨id, 0, strictMono_id, fun hψ' => absurd hψ' hψ⟩
  choose χ g hχ hg using h'
  -- Step 2: nested subsequences `Ψ 0 = id`, `Ψ (m + 1) = Ψ m ∘ χ m (Ψ m)`.
  obtain ⟨Ψ, hΨ0, hΨs⟩ : ∃ Ψ : ℕ → ℕ → ℕ, Ψ 0 = id ∧ ∀ m, Ψ (m + 1) = Ψ m ∘ χ m (Ψ m) :=
    ⟨fun m => Nat.rec (motive := fun _ => ℕ → ℕ) id (fun k ψ => ψ ∘ χ k ψ) m, rfl, fun _ => rfl⟩
  have hΨmono : ∀ m, StrictMono (Ψ m) := by
    intro m
    induction m with
    | zero => rw [hΨ0]; exact strictMono_id
    | succ m ih => rw [hΨs]; exact ih.comp (hχ m (Ψ m))
  have hconv : ∀ m, TendstoUniformlyOn (fun j => F (Ψ (m + 1) j)) (g m (Ψ m)) atTop (S m) := by
    intro m
    rw [hΨs]
    exact hg m (Ψ m) (hΨmono m)
  -- Step 3: later stages factor through earlier ones, `Ψ (m + d) = Ψ m ∘ ρ m d`.
  have hfac : ∀ m d, ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ Ψ (m + d) = Ψ m ∘ ρ := by
    intro m d
    induction d with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ d ih =>
      obtain ⟨ρ, hρ, hρe⟩ := ih
      refine ⟨ρ ∘ χ (m + d) (Ψ (m + d)), hρ.comp (hχ _ _), ?_⟩
      rw [← add_assoc, hΨs, hρe]
      rfl
  choose ρ hρ hρe using hfac
  -- Step 4: the diagonal `φ j = Ψ (j + 1) j` is strictly increasing.
  have hφ : StrictMono (fun j => Ψ (j + 1) j) := by
    apply strictMono_nat_of_lt_succ
    intro j
    show Ψ (j + 1) j < Ψ (j + 1 + 1) (j + 1)
    rw [hΨs (j + 1)]
    exact hΨmono (j + 1)
      (lt_of_lt_of_le (Nat.lt_succ_self j) ((hχ (j + 1) (Ψ (j + 1))).id_le (j + 1)))
  -- Step 5: for `j ≥ m`, `φ j = Ψ (m + 1) (τ j)` with `τ j = ρ (m + 1) (j - m) j ≥ j`, so
  -- `F ∘ φ → g m (Ψ m)` uniformly on `S m`.
  have hφconv : ∀ m, TendstoUniformlyOn (fun j => F (Ψ (j + 1) j)) (g m (Ψ m)) atTop (S m) := by
    intro m
    have hτ : ∀ j, m ≤ j → Ψ (j + 1) j = Ψ (m + 1) (ρ (m + 1) (j - m) j) := by
      intro j hj
      have hjm : j + 1 = m + 1 + (j - m) := by omega
      rw [hjm, hρe]
      rfl
    have hτt : Tendsto (fun j => ρ (m + 1) (j - m) j) atTop atTop :=
      tendsto_atTop_mono (fun j => (hρ (m + 1) (j - m)).id_le j) tendsto_id
    have h1 : TendstoUniformlyOn (fun j => F (Ψ (m + 1) (ρ (m + 1) (j - m) j))) (g m (Ψ m))
        atTop (S m) := fun u hu => hτt.eventually (hconv m u hu)
    refine h1.congr ?_
    filter_upwards [eventually_ge_atTop m] with j hj
    intro z _
    simp only [hτ j hj]
  -- Step 6: glue the limits, `V z = g m(z) (Ψ m(z)) z` for the least `m(z)` with `z ∈ S m(z)`.
  classical
  refine ⟨fun j => Ψ (j + 1) j,
    fun z => if hz : ∃ m, z ∈ S m then g (Nat.find hz) (Ψ (Nat.find hz)) z else 0, hφ,
    fun m => (hφconv m).congr_right ?_⟩
  intro z hz
  have hex : ∃ m, z ∈ S m := ⟨m, hz⟩
  simp only [dite_eq_left hex]
  exact tendsto_nhds_unique ((hφconv m).tendsto_at hz) ((hφconv _).tendsto_at (Nat.find_spec hex))
/-- Uniformly Hölder maps `F j : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` that converge on a dense subset `D` of a compact
set `S` converge uniformly on `S`.  Given `ε > 0`, pick `η > 0` with `K η^α < ε/3`; finitely many
balls `B̆_η(d)`, `d ∈ T ⊆ D`, cover `S`; from some `N` on all `F j d`, `d ∈ T`, are `ε/6`-close to
their limits; the Hölder bound and the triangle inequality then make `(F j)` uniformly Cauchy on
`S`, and completeness of `L` supplies the uniform limit. -/
theorem dohr_eb_sch_bu_hds_unif_of_dense : ∀ (n ℓ : ℕ) (α K : ℝ) (S D : Set (Rn n)) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → D ⊆ S → S ⊆ closure D → (∀ d ∈ D, ∃ v : Rn n →L[ℝ] Rn ℓ, Tendsto (fun j => F j d) atTop (𝓝 v)) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ G : Rn n → (Rn n →L[ℝ] Rn ℓ), TendstoUniformlyOn F G atTop S := by
  intro n ℓ α K S D F hα hK hS hDS hSD hconv hHol
  -- Step 1: the limits `v d` on `D`.
  choose! v hv using hconv
  -- Steps 2–5: `(F j)` is uniformly Cauchy on `S`.
  have hU : UniformCauchySeqOn F atTop S := by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_
    -- Step 2: a Hölder scale `η > 0` with `K η^α < ε/3`.
    have h0 : Tendsto (fun t : ℝ => K * t ^ α) (𝓝 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).const_mul K).tendsto
      simpa [Real.zero_rpow hα.ne'] using h
    obtain ⟨η, hηε, hη⟩ : ∃ η : ℝ, K * η ^ α < ε / 3 ∧ 0 < η :=
      (((h0.eventually (gt_mem_nhds (div_pos hε three_pos))).filter_mono
        nhdsWithin_le_nhds).and (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t)).exists
    -- Step 3: finitely many balls `B̆_η(d)`, `d ∈ T ⊆ D`, cover `S`.
    obtain ⟨T, hTD, hTfin, hST⟩ := hS.elim_finite_subcover_image (b := D)
      (c := fun d => Metric.ball d η) (fun d _ => Metric.isOpen_ball) fun z hz => by
        obtain ⟨d, hd, hzd⟩ := Metric.mem_closure_iff.1 (hSD hz) η hη
        exact Set.mem_biUnion hd (Metric.mem_ball.2 hzd)
    -- Step 4: from some `N` on, `F j d` is `ε/6`-close to `v d` for every `d ∈ T`.
    have hev : ∀ᶠ j in atTop, ∀ d ∈ T, dist (F j d) (v d) < ε / 6 :=
      hTfin.eventually_all.2 fun d hd =>
        (hv d (hTD hd)).eventually (Metric.ball_mem_nhds _ (div_pos hε (by norm_num)))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun m hm m' hm' z hz => ?_⟩
    -- Step 5: the Hölder bound and the triangle inequality.
    obtain ⟨d, hdT, hzd⟩ := Set.mem_iUnion₂.1 (hST hz)
    have hdS : d ∈ S := hDS (hTD hdT)
    have hzd' : ‖z - d‖ ^ α ≤ η ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hzd).le)
        hα.le
    have hHol' : ∀ j, dist (F j z) (F j d) < ε / 3 := fun j => by
      rw [dist_eq_norm]
      calc ‖F j z - F j d‖ ≤ K * ‖z - d‖ ^ α := hHol j z hz d hdS
        _ ≤ K * η ^ α := mul_le_mul_of_nonneg_left hzd' hK
        _ < ε / 3 := hηε
    have h1 := hHol' m
    have h2 := hHol' m'
    have h3 := hN m hm d hdT
    have h4 := hN m' hm' d hdT
    have h5 := dist_triangle4 (F m z) (F m d) (F m' d) (F m' z)
    have h6 := dist_triangle (F m d) (v d) (F m' d)
    rw [dist_comm (F m' d) (F m' z)] at h5
    rw [dist_comm (v d) (F m' d)] at h6
    linarith
  -- Step 6: pointwise limits on `S`, by completeness of `L`.
  have hlim : ∀ z ∈ S, ∃ w, Tendsto (fun j => F j z) atTop (𝓝 w) := fun z hz =>
    cauchySeq_tendsto_of_complete (hU.cauchySeq hz)
  -- Step 7: uniformly Cauchy plus pointwise convergence gives uniform convergence.
  exact ⟨fun z => limUnder atTop (fun j => F j z),
    hU.tendstoUniformlyOn_of_tendsto fun z hz => tendsto_nhds_limUnder (hlim z hz)⟩
/-- Sequential Arzelà–Ascoli on a compact set `S ⊆ ℝⁿ` for maps `g_j : ℝⁿ → L = L(ℝⁿ, ℝ^ℓ)` that
are bounded by `M` and `α`-Hölder with constant `K` on `S`, uniformly in `j`: some subsequence
`g_{χ(j)}` converges uniformly on `S`.

Proof: if `S = ∅` there is nothing to prove.  Otherwise `S`, a subspace of the second-countable
space `ℝⁿ`, has a countable subset `D ⊆ S` with `S ⊆ closure D`; `D` is nonempty, so `D = {d_m}`
for a sequence `d`.  At each `d_m` every subsequence `g_{ψ(j)}(d_m)` lies in the compact closed
`M`-ball of the finite-dimensional space `L`, so it has a convergent further subsequence, i.e. one
converging uniformly on `{d_m}`.  `dohr_eb_sch_bu_hds_diagonal_extract` with `S_m = {d_m}` gives a
single `χ` with `g_{χ(j)}` convergent at every point of `D`, and `dohr_eb_sch_bu_hds_unif_of_dense`
upgrades this to uniform convergence on `S`. -/
theorem dohr_eb_sch_bu_hds_compact_subseq : ∀ (n ℓ : ℕ) (α K M : ℝ) (S : Set (Rn n)) (g : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → IsCompact S → (∀ j, ∀ z ∈ S, ‖g j z‖ ≤ M) → (∀ j, ∀ z ∈ S, ∀ z' ∈ S, ‖g j z - g j z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ (χ : ℕ → ℕ) (G : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧ TendstoUniformlyOn (fun j => g (χ j)) G atTop S := by
  intro n ℓ α K M S g hα hK hS hM hH
  -- Step 1: the empty case.
  rcases S.eq_empty_or_nonempty with hS0 | ⟨z₀, hz₀⟩
  · subst hS0
    exact ⟨id, 0, strictMono_id, tendstoUniformlyOn_empty⟩
  -- Step 2: a countable `D ⊆ S` with `S ⊆ closure D`; it is nonempty, so `D = range d`.
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hDne : D.Nonempty := closure_nonempty_iff.mp ⟨z₀, hSD hz₀⟩
  obtain ⟨d, rfl⟩ := hDc.exists_eq_range hDne
  -- Step 3: at `d m`, every subsequence has a further subsequence converging on `{d m}`, since
  -- `g (ψ j) (d m)` stays in the closed `M`-ball of `L`, compact as `L` is finite-dimensional.
  have hpt : ∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ) (G : Rn n → (Rn n →L[ℝ] Rn ℓ)),
      StrictMono χ ∧ TendstoUniformlyOn (fun j => g (ψ (χ j))) G atTop {d m} := by
    intro m ψ _
    obtain ⟨v, -, χ, hχ, hv⟩ := (isCompact_closedBall (0 : Rn n →L[ℝ] Rn ℓ) M).tendsto_subseq
      (x := fun j => g (ψ j) (d m))
      (fun j => mem_closedBall_zero_iff.mpr (hM (ψ j) (d m) (hDS (mem_range_self m))))
    exact ⟨χ, fun _ => v, hχ, tendstoUniformlyOn_singleton_iff_tendsto.mpr hv⟩
  -- Step 4: diagonal extraction over the points `d m` of `D`.
  obtain ⟨χ, W, hχ, hW⟩ :=
    Submission.dohr_eb_sch_bu_hds_diagonal_extract n ℓ g (fun m => {d m}) hpt
  have hconv : ∀ z ∈ range d, ∃ v : Rn n →L[ℝ] Rn ℓ, Tendsto (fun j => g (χ j) z) atTop (𝓝 v) := by
    rintro _ ⟨m, rfl⟩
    exact ⟨W (d m), (hW m).tendsto_at (mem_singleton (d m))⟩
  -- Step 5: by the uniform Hölder bound, convergence on `D` upgrades to uniform convergence on `S`.
  obtain ⟨G, hG⟩ := Submission.dohr_eb_sch_bu_hds_unif_of_dense n ℓ α K S (range d)
    (fun j => g (χ j)) hα hK hS hDS hSD hconv (fun j => hH (χ j))
  exact ⟨χ, G, hχ, hG⟩

end Submission
/-- **Hölder bounds pass to pointwise limits** (steps 7b–c of the Hölder diagonal-subsequence
argument in the Schauder blow-up estimate for Simon 7.1).  If `F_j(z) → V(z)` for every `z` and,
for all `z, z'`, `‖F_j(z) − F_j(z')‖ ≤ K ‖z − z'‖^α` for all large `j`, then `V` satisfies the same
`α`-Hölder bound and, as `α > 0`, is continuous. -/
theorem Submission.dohr_eb_sch_bu_hds_holder_of_limit : ∀ (n ℓ : ℕ) (α K : ℝ) (F : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), 0 < α → 0 ≤ K → (∀ z, Tendsto (fun j => F j z) atTop (𝓝 (V z))) → (∀ z z' : Rn n, ∀ᶠ j in atTop, ‖F j z - F j z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ Continuous V := by
  intro n ℓ α K F V hα _ hF hFK
  -- Step 1: `‖F_j z − F_j z'‖ → ‖V z − V z'‖` and these norms are eventually `≤ K ‖z − z'‖^α`;
  -- `(-∞, K ‖z − z'‖^α]` is closed, so the limit satisfies the same bound.
  have hV : ∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α := fun z z' =>
    le_of_tendsto ((hF z).sub (hF z')).norm (hFK z z')
  refine ⟨hV, continuous_iff_continuousAt.mpr fun z => ?_⟩
  -- Step 2a: `t ↦ t^α` is continuous at `0` with value `0^α = 0` (`α > 0`) and `‖z' − z‖ → 0`,
  -- so `K ‖z' − z‖^α → 0` as `z' → z`.
  have hpow : Tendsto (fun t : ℝ => t ^ α) (𝓝 0) (𝓝 0) := by
    simpa [Real.zero_rpow hα.ne'] using (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
  have hK0 : Tendsto (fun z' : Rn n => K * ‖z' - z‖ ^ α) (𝓝 z) (𝓝 0) := by
    simpa using (hpow.comp (tendsto_norm_sub_self z)).const_mul K
  -- Steps 2b–c: `0 ≤ ‖V z' − V z‖ ≤ K ‖z' − z‖^α`, so `‖V z' − V z‖ → 0` by squeezing, that is,
  -- `V z' → V z`.
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun z' => norm_nonneg _) (fun z' => hV z' z) hK0)

namespace Submission

/-- **Arzelà–Ascoli with diagonal extraction for uniformly Hölder maps on growing balls**
(blow-up step of the Schauder estimate behind Simon Ch. 5, Theorem 7.1, second assertion).
Let `R_k → ∞` and let `f_k : ℝⁿ → L(ℝⁿ, ℝ^ℓ)` satisfy `f_k(0) = 0` and
`‖f_k(z) − f_k(z')‖ ≤ K|z − z'|^α` on `B̆_{R_k}(0)`.  Then a subsequence `f_{φ(j)}` converges
uniformly on every closed ball `B_r(0)` to a continuous `V` with `V(0) = 0` and
`‖V(z) − V(z')‖ ≤ K|z − z'|^α` on `ℝⁿ`: on `B_m(0)` the tail `k ≥ k_m` (`R_k > m`) is uniformly
Hölder and bounded by `K mᵅ`, so every subsequence has a further subsequence converging uniformly
on `B_m(0)` (Arzelà–Ascoli); a diagonal subsequence converges on every `B_m(0)`, and the Hölder
bound passes to the limit. -/
theorem dohr_eb_sch_bu_holder_diag_subseq : ∀ (n ℓ : ℕ) (α K : ℝ) (f : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (R : ℕ → ℝ), 0 < α → 0 ≤ K → Tendsto R atTop atTop → (∀ k, f k 0 = 0) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k), ‖f k z - f k z'‖ ≤ K * ‖z - z'‖ ^ α) → ∃ (φ : ℕ → ℕ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono φ ∧ V 0 = 0 ∧ Continuous V ∧ (∀ z z' : Rn n, ‖V z - V z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ ∀ r : ℝ, TendstoUniformlyOn (fun j => f (φ j)) V atTop (closedBall (0 : Rn n) r) := by
  intro n ℓ α K f R hα hK hR hf0 hf
  -- Step 1: for each `m` there is `k_m` with `R_k > m` for `k ≥ k_m`; for such `k` the map `f_k`
  -- is `K`-`α`-Hölder on `B_m(0)` and bounded there by `K mᵅ` (since `f_k(0) = 0`).
  have hkm : ∀ m : ℕ, ∃ km : ℕ, ∀ k ≥ km, (m : ℝ) < R k := fun m =>
    eventually_atTop.1 (hR.eventually_gt_atTop (m : ℝ))
  choose km hkm using hkm
  have hhol : ∀ m : ℕ, ∀ k ≥ km m, ∀ z ∈ closedBall (0 : Rn n) m,
      ∀ z' ∈ closedBall (0 : Rn n) m, ‖f k z - f k z'‖ ≤ K * ‖z - z'‖ ^ α :=
    fun m k hk z hz z' hz' =>
      hf k z (closedBall_subset_ball (hkm m k hk) hz) z' (closedBall_subset_ball (hkm m k hk) hz')
  have hbd : ∀ m : ℕ, ∀ k ≥ km m, ∀ z ∈ closedBall (0 : Rn n) m, ‖f k z‖ ≤ K * (m : ℝ) ^ α := by
    intro m k hk z hz
    have h := hhol m k hk z hz 0 (mem_closedBall_self (Nat.cast_nonneg m))
    rw [hf0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg z) (mem_closedBall_zero_iff.1 hz) hα.le) hK)
  -- Step 2 (Arzelà–Ascoli): along any strictly increasing `ψ`, the shifted tail
  -- `f_{ψ(k_m + j)}` satisfies the bounds of step 1 on `B_m(0)`, so a further subsequence
  -- converges uniformly on `B_m(0)`.
  have hstep2 : ∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ (χ : ℕ → ℕ)
      (g : Rn n → (Rn n →L[ℝ] Rn ℓ)), StrictMono χ ∧
        TendstoUniformlyOn (fun j => f (ψ (χ j))) g atTop (closedBall (0 : Rn n) m) := by
    intro m ψ hψ
    have hge : ∀ j, km m ≤ ψ (km m + j) := fun j =>
      (Nat.le_add_right (km m) j).trans (hψ.id_le (km m + j))
    obtain ⟨χ', G, hχ', hG⟩ := Submission.dohr_eb_sch_bu_hds_compact_subseq n ℓ α K
      (K * (m : ℝ) ^ α) (closedBall (0 : Rn n) m) (fun j => f (ψ (km m + j))) hα hK
      (isCompact_closedBall 0 m) (fun j z hz => hbd m _ (hge j) z hz)
      (fun j z hz z' hz' => hhol m _ (hge j) z hz z' hz')
    exact ⟨fun j => km m + χ' j, G, fun a b hab => Nat.add_lt_add_left (hχ' hab) (km m), hG⟩
  -- Steps 3–6: diagonal extraction over the balls `B_m(0)`, with a single limit `V`; every
  -- `B_r(0)` lies in `B_{⌈r⌉}(0)`, and pointwise convergence at `z` follows from `z ∈ B_{|z|}(0)`.
  obtain ⟨φ, V, hφ, hV⟩ := Submission.dohr_eb_sch_bu_hds_diagonal_extract n ℓ f
    (fun m => closedBall (0 : Rn n) m) hstep2
  have hVr : ∀ r : ℝ, TendstoUniformlyOn (fun j => f (φ j)) V atTop (closedBall (0 : Rn n) r) :=
    fun r => (hV ⌈r⌉₊).mono (closedBall_subset_closedBall (Nat.le_ceil r))
  have hpt : ∀ z, Tendsto (fun j => f (φ j) z) atTop (𝓝 (V z)) := fun z =>
    (hVr ‖z‖).tendsto_at (mem_closedBall_zero_iff.2 le_rfl)
  -- Step 7a: `f_{φ(j)}(0) = 0` for every `j`, so `V(0) = 0`.
  have hV0 : V 0 = 0 :=
    tendsto_nhds_unique (hpt 0) (tendsto_const_nhds.congr fun j => (hf0 (φ j)).symm)
  -- Step 7b–c: `R_{φ(j)} → ∞`, so for large `j` both `z, z'` lie in `B̆_{R_{φ(j)}}(0)` and the
  -- Hölder bound holds at `z, z'`; it passes to the limit, which is therefore continuous.
  have hev : ∀ z z' : Rn n, ∀ᶠ j in atTop, ‖f (φ j) z - f (φ j) z'‖ ≤ K * ‖z - z'‖ ^ α := by
    intro z z'
    filter_upwards [(hR.comp hφ.tendsto_atTop).eventually_gt_atTop (max ‖z‖ ‖z'‖)] with j hj
    exact hf (φ j) z (mem_ball_zero_iff.2 ((le_max_left _ _).trans_lt hj))
      z' (mem_ball_zero_iff.2 ((le_max_right _ _).trans_lt hj))
  obtain ⟨hVH, hVc⟩ := Submission.dohr_eb_sch_bu_hds_holder_of_limit n ℓ α K
    (fun j => f (φ j)) V hα hK hpt hev
  exact ⟨φ, V, hφ, hV0, hVc, hVH, hVr⟩
/-- **`C¹` limit on growing balls** (blow-up step of the Schauder estimate behind Simon 7.1).
Let `R_k → ∞`, let `W_k` be `C¹` on `B̆_{R_k}(0)` with `W_k(0) = 0`, let `V : ℝⁿ → L(ℝⁿ; ℝ^ℓ)` be
continuous, and let `DW_k → V` uniformly on every closed ball `B_r(0)`.  Then
`W(z) = ∫₀¹ V(tz) z dt` is `C¹` on `ℝⁿ` with `DW = V`: for `k` large,
`W_k(z) = ∫₀¹ DW_k(tz) z dt` by the fundamental theorem of calculus, so
`|W_k(z) − W(z)| ≤ |z| sup_{B_{|z|}(0)} ‖DW_k − V‖ → 0`, and near each point the derivatives
converge uniformly, so the theorem on uniform limits of derivatives gives `DW = V`. -/
theorem dohr_eb_sch_bu_contDiff_of_fderiv_tendsto : ∀ (n ℓ : ℕ) (W : ℕ → Rn n → Rn ℓ) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)) (R : ℕ → ℝ), Tendsto R atTop atTop → (∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k))) → (∀ k, W k 0 = 0) → Continuous V → (∀ r : ℝ, TendstoUniformlyOn (fun k => fderiv ℝ (W k)) V atTop (closedBall (0 : Rn n) r)) → ∃ W' : Rn n → Rn ℓ, ContDiff ℝ 1 W' ∧ ∀ z, fderiv ℝ W' z = V z := by
  intro n ℓ W V R hR hW hW0 hVc hV
  -- Step 1: for `k` large (`R k > r + 1`), `W k` has derivative `DW_k(y)` at every
  -- `y ∈ B̆_{r+1}(0)`, and `DW_k` is continuous there.
  have hstep1 : ∀ r : ℝ, ∀ᶠ k in atTop,
      (∀ y ∈ ball (0 : Rn n) (r + 1), HasFDerivAt (W k) (fderiv ℝ (W k) y) y) ∧
        ContinuousOn (fderiv ℝ (W k)) (ball (0 : Rn n) (r + 1)) := by
    intro r
    filter_upwards [hR.eventually_gt_atTop (r + 1)] with k hk
    have hsub : ball (0 : Rn n) (r + 1) ⊆ ball 0 (R k) := ball_subset_ball hk.le
    refine ⟨fun y hy => ?_, ((hW k).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hsub⟩
    exact (((hW k).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ball.mem_nhds (hsub hy))).hasFDerivAt
  -- Steps 2–3: for `k` large, `W_k(z) = ∫₀¹ DW_k(tz) z dt` (FTC, `W_k(0) = 0`), so with
  -- `W(z) = ∫₀¹ V(tz) z dt` we get `|W_k(z) − W(z)| ≤ |z| sup_{B_{|z|}(0)} ‖DW_k − V‖ → 0`.
  have hconv : ∀ z : Rn n,
      Tendsto (fun k => W k z) atTop (𝓝 (∫ t in (0 : ℝ)..1, V (t • z) z)) := by
    intro z
    have hmem : ∀ t ∈ uIcc (0 : ℝ) 1, t • z ∈ closedBall (0 : Rn n) ‖z‖ := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg z) ht.2
    have hmem' : ∀ t ∈ uIcc (0 : ℝ) 1, t • z ∈ ball (0 : Rn n) (‖z‖ + 1) := fun t ht =>
      closedBall_subset_ball (lt_add_one _) (hmem t ht)
    have hVint : IntervalIntegrable (fun t : ℝ => V (t • z) z) volume 0 1 :=
      ((hVc.comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const).intervalIntegrable 0 1
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (‖z‖ + 1) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((hstep1 ‖z‖).and (Metric.tendstoUniformlyOn_iff.1 (hV ‖z‖) _ hδ))
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨⟨hd, hc⟩, hu⟩ := hN k hk
    have hWint : IntervalIntegrable (fun t : ℝ => fderiv ℝ (W k) (t • z) z) volume 0 1 :=
      ContinuousOn.intervalIntegrable ((hc.comp (continuous_id.smul continuous_const).continuousOn
        hmem').clm_apply continuousOn_const)
    have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ (W k) (t • z) z = W k z := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
        (f := fun t : ℝ => W k (t • z)) (f' := fun t => fderiv ℝ (W k) (t • z) z)
        (fun t ht => by
          have h2 := (hd _ (hmem' t ht)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const z)
          rw [one_smul] at h2
          exact h2)
        hWint
      simpa [hW0] using h
    rw [dist_eq_norm, ← hftc, ← intervalIntegral.integral_sub hWint hVint]
    calc ‖∫ t in (0 : ℝ)..1, (fderiv ℝ (W k) (t • z) z - V (t • z) z)‖
        ≤ ε / (‖z‖ + 1) * ‖z‖ * |1 - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
          have hlt := hu (t • z) (hmem t (uIoc_subset_uIcc ht))
          rw [dist_eq_norm, norm_sub_rev] at hlt
          exact ((fderiv ℝ (W k) (t • z) - V (t • z)).le_opNorm z).trans
            (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg z))
      _ < ε := by
          rw [sub_zero, abs_one, mul_one, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  -- Step 4: near every `x`, `DW_k → V` uniformly and `W_k → W` pointwise, so `DW(x) = V(x)`.
  have hderiv : ∀ x : Rn n, HasFDerivAt (fun z => ∫ t in (0 : ℝ)..1, V (t • z) z) (V x) x := by
    intro x
    have hnhds : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : Rn n) (‖x‖ + 1) :=
      isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (lt_add_one _))
    exact hasFDerivAt_of_tendstoUniformlyOnFilter (l := atTop) (f := W)
      (f' := fun k => fderiv ℝ (W k)) (g' := V)
      ((hV (‖x‖ + 1)).tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.2 (mem_of_superset hnhds ball_subset_closedBall)))
      (((hstep1 ‖x‖).prod_mk hnhds).mono fun p hp => hp.1.1 p.2 hp.2)
      (Eventually.of_forall hconv)
  -- Step 5: `DW = V` is continuous, so `W` is `C¹`.
  have hfd : fderiv ℝ (fun z => ∫ t in (0 : ℝ)..1, V (t • z) z) = V :=
    funext fun x => (hderiv x).fderiv
  refine ⟨fun z => ∫ t in (0 : ℝ)..1, V (t • z) z,
    contDiff_one_iff_fderiv.2 ⟨fun x => (hderiv x).differentiableAt, ?_⟩,
    fun z => (hderiv z).fderiv⟩
  rw [hfd]
  exact hVc
/-- Localization of integrals: if `f : ℝⁿ → ℝ` is continuous on an open `O` and vanishes off a
compact `T ⊆ O`, then `f` is continuous, integrable, and `∫_O f = ∫_{ℝⁿ} f`.  At a point of `O`,
`f` is continuous because `O` is open; a point outside `O` lies in the open set `Tᶜ` (`T` is
closed), where `f = 0`.  So `f` is continuous with compact support (`HasCompactSupport.intro`),
hence integrable (`Continuous.integrable_of_hasCompactSupport`), and it vanishes off `O`
(`setIntegral_eq_integral_of_forall_compl_eq_zero`). -/
theorem dohr_eb_sch_bu_wel_localized_integral : ∀ (n : ℕ) (f : Rn n → ℝ) (O T : Set (Rn n)), IsOpen O → IsCompact T → T ⊆ O → ContinuousOn f O → (∀ z, z ∉ T → f z = 0) → Continuous f ∧ Integrable f ∧ ∫ z in O, f z = ∫ z, f z := by
  intro n f O T hO hT hTO hf hfT
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ O
    · exact hf.continuousAt (hO.mem_nhds hz)
    · -- `z ∉ T`, and `f = 0` on the open neighbourhood `Tᶜ` of `z`.
      have hzT : z ∉ T := fun h => hz (hTO h)
      have hev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 z] f :=
        Filter.mem_of_superset (hT.isClosed.isOpen_compl.mem_nhds hzT) fun w hw => (hfT w hw).symm
      exact continuousAt_const.congr hev
  refine ⟨hcont, hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hT hfT), ?_⟩
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hfT z fun h => hz (hTO h)
/-- Convergence of integrals under uniform convergence on a compact set containing the supports
(steps 4 and 5d of the weak-equation limit in the blow-up argument for the Schauder estimate): if
`K ⊆ ℝⁿ` is compact, `g` and eventually every `f k` are integrable and vanish off `K`, and
`f k → g` uniformly on `K`, then `∫ f k → ∫ g`.  For `ε > 0` put `M = 𝓛ⁿ(K) < ∞` and
`δ = ε / (M + 1)`; for large `k`, `|∫ f k - ∫ g| = |∫_K (f k - g)| ≤ δ M < ε`. -/
theorem dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn : ∀ (n : ℕ) (K : Set (Rn n)) (f : ℕ → Rn n → ℝ) (g : Rn n → ℝ), IsCompact K → (∀ᶠ k in atTop, Integrable (f k)) → Integrable g → (∀ᶠ k in atTop, ∀ z, z ∉ K → f k z = 0) → (∀ z, z ∉ K → g z = 0) → TendstoUniformlyOn f g atTop K → Tendsto (fun k => ∫ z, f k z) atTop (𝓝 (∫ z, g z)) := by
  intro n K f g hK hfi hgi hfK hgK hfg
  -- Step 1: `K` is compact, so `M = 𝓛ⁿ(K)` is finite (and `M ≥ 0`).
  have hKfin : (volume : Measure (Rn n)) K < ∞ := hK.measure_lt_top
  have hM : 0 ≤ (volume : Measure (Rn n)).real K := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 2: with `δ = ε / (M + 1) > 0`, for all large `k` the function `f k` is integrable,
  -- vanishes off `K`, and `|g - f k| < δ` on `K`.
  have hδ : 0 < ε / ((volume : Measure (Rn n)).real K + 1) := div_pos hε (by linarith)
  filter_upwards [hfi, hfK, Metric.tendstoUniformlyOn_iff.1 hfg _ hδ] with k hk1 hk2 hk3
  -- Steps 3–4: `∫ f k - ∫ g = ∫ (f k - g) = ∫_K (f k - g)`, as `f k - g` vanishes off `K`.
  have h4 : ∫ z in K, (f k z - g z) = ∫ z, (f k z - g z) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [hk2 z hz, hgK z hz, sub_zero]
  rw [dist_eq_norm, ← integral_sub hk1 hgi, ← h4]
  -- Step 5: `|∫_K (f k - g)| ≤ δ M`.
  have h5 : ‖∫ z in K, (f k z - g z)‖ ≤
      ε / ((volume : Measure (Rn n)).real K + 1) * (volume : Measure (Rn n)).real K :=
    norm_setIntegral_le_of_norm_le_const hKfin fun z hz => by
      rw [← dist_eq_norm, dist_comm]
      exact (hk3 z hz).le
  -- Step 6: `δ M = ε M / (M + 1) < ε`.
  have h6 : ε / ((volume : Measure (Rn n)).real K + 1) * (volume : Measure (Rn n)).real K < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith
  exact h5.trans_lt h6

end Submission
/-- **Uniform limits of the perturbed pairings and of the error forms** (steps 4 and 5a–c of the
weak-equation limit in the Schauder blow-up estimate for Simon 7.1).  Let `A` be a continuous
bilinear form on `L = L(ℝⁿ, ℝ^ℓ)`, let `U_k → V` uniformly on `K`, and let `‖z‖ ≤ r`, `‖Q z‖ ≤ Z`
and `‖V z‖ ≤ N` on `K`.  If `c_k → 0`, `d_k → 0` and, for all large `k` and all `z ∈ K`,
`|ah_k(z)[P][P'] − A[P][P']| ≤ c_k (1 + ‖z‖^α) ‖P‖ ‖P'‖` and `|Ψ_k(z)[P]| ≤ d_k ‖z‖^α ‖P‖`, then
`ah_k(z)[U_k(z)][Q(z)] → A[V(z)][Q(z)]` and `Ψ_k(z)[Q(z)] → 0` uniformly on `K`.  The bound
`|A[P][P']| ≤ C_A ‖P‖ ‖P'‖` comes from `ContinuousLinearMap.isBoundedBilinearMap`. -/
theorem Submission.dohr_eb_sch_bu_wel_pairing_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (α r Z N : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V Q : Rn n → (Rn n →L[ℝ] Rn ℓ)) (K : Set (Rn n)) (c d : ℕ → ℝ), 0 ≤ α → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → TendstoUniformlyOn U V atTop K → (∀ z ∈ K, ‖z‖ ≤ r) → (∀ z ∈ K, ‖Q z‖ ≤ Z) → (∀ z ∈ K, ‖V z‖ ≤ N) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P P' : Rn n →L[ℝ] Rn ℓ, |ah k z P P' - A P P'| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖P'‖) → (∀ᶠ k in atTop, ∀ z ∈ K, ∀ P : Rn n →L[ℝ] Rn ℓ, |Ψ k z P| ≤ d k * ‖z‖ ^ α * ‖P‖) → TendstoUniformlyOn (fun k z => ah k z (U k z) (Q z)) (fun z => A (V z) (Q z)) atTop K ∧ TendstoUniformlyOn (fun k z => Ψ k z (Q z)) (fun _ => (0 : ℝ)) atTop K := by
  intro n ℓ α r Z N A ah Ψ U V Q K c d hα hc hd hUV hr hZ hN hah hΨ
  -- Step 1: nonnegative bounds on `K`: `‖z‖ ^ α ≤ R := (max r 0) ^ α`, `‖Q z‖ ≤ Z₀ := max Z 0`
  -- and `‖V z‖ ≤ N₀ := max N 0` (no case split when `K` is empty).
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ K, ‖z‖ ^ α ≤ R :=
    ⟨max r 0 ^ α, Real.rpow_nonneg (le_max_right r 0) α, fun z hz =>
      Real.rpow_le_rpow (norm_nonneg z) ((hr z hz).trans (le_max_left r 0)) hα⟩
  obtain ⟨Z₀, hZ₀0, hZ₀⟩ : ∃ Z₀ : ℝ, 0 ≤ Z₀ ∧ ∀ z ∈ K, ‖Q z‖ ≤ Z₀ :=
    ⟨max Z 0, le_max_right Z 0, fun z hz => (hZ z hz).trans (le_max_left Z 0)⟩
  obtain ⟨N₀, hN₀0, hN₀⟩ : ∃ N₀ : ℝ, 0 ≤ N₀ ∧ ∀ z ∈ K, ‖V z‖ ≤ N₀ :=
    ⟨max N 0, le_max_right N 0, fun z hz => (hN z hz).trans (le_max_left N 0)⟩
  -- Step 2: the bilinear bound `‖A P P'‖ ≤ C_A ‖P‖ ‖P'‖`.
  obtain ⟨CA, hCA0, hCA⟩ : ∃ CA > 0, ∀ P P' : Rn n →L[ℝ] Rn ℓ, ‖A P P'‖ ≤ CA * ‖P‖ * ‖P'‖ :=
    A.isBoundedBilinearMap.bound
  refine ⟨?_, ?_⟩
  · -- Claim (i).  Step 3: with `C₁ = (1 + R)(N₀ + 1) Z₀` and `C₂ = C_A Z₀`, eventually
    -- `|c_k| < (ε/2)/(C₁ + 1)`, `‖U_k z − V z‖ < min 1 ((ε/2)/(C₂ + 1))` on `K`, and the
    -- coefficient bound holds on `K`.
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC₁ : 0 < (1 + R) * (N₀ + 1) * Z₀ + 1 := by positivity
    have hC₂ : 0 < CA * Z₀ + 1 := by positivity
    have hδ₁ : 0 < ε / 2 / ((1 + R) * (N₀ + 1) * Z₀ + 1) := by positivity
    have hδ₂ : 0 < min 1 (ε / 2 / (CA * Z₀ + 1)) := by positivity
    filter_upwards [Metric.tendsto_nhds.mp hc _ hδ₁, Metric.tendstoUniformlyOn_iff.mp hUV _ hδ₂,
      hah] with k hck hUk hahk z hz
    rw [Real.dist_eq, sub_zero] at hck
    have hP : ‖U k z - V z‖ < min 1 (ε / 2 / (CA * Z₀ + 1)) := by
      rw [← dist_eq_norm, dist_comm]
      exact hUk z hz
    have hP₁ : ‖U k z - V z‖ ≤ 1 := hP.le.trans (min_le_left _ _)
    have hP₂ : ‖U k z - V z‖ < ε / 2 / (CA * Z₀ + 1) := hP.trans_le (min_le_right _ _)
    -- Step 4: `‖U_k z‖ ≤ ‖V z‖ + ‖U_k z − V z‖ ≤ N₀ + 1`.
    have hUn : ‖U k z‖ ≤ N₀ + 1 :=
      calc ‖U k z‖ = ‖V z + (U k z - V z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖V z‖ + ‖U k z - V z‖ := norm_add_le _ _
        _ ≤ N₀ + 1 := add_le_add (hN₀ z hz) hP₁
    -- Step 5: `A[V][Q] − ah_k[U_k][Q] = −((ah_k − A)[U_k][Q] + A[U_k − V][Q])`.
    have hdec : A (V z) (Q z) - ah k z (U k z) (Q z) =
        -((ah k z (U k z) (Q z) - A (U k z) (Q z)) + A (U k z - V z) (Q z)) := by
      rw [map_sub, sub_apply]
      ring
    -- Step 6: the first term is `≤ |c_k| C₁ < ε/2`.
    have h₁ : |ah k z (U k z) (Q z) - A (U k z) (Q z)| < ε / 2 := by
      have hQ := hZ₀ z hz
      have hRz := hR z hz
      calc |ah k z (U k z) (Q z) - A (U k z) (Q z)|
          ≤ c k * (1 + ‖z‖ ^ α) * ‖U k z‖ * ‖Q z‖ := hahk z hz _ _
        _ ≤ |c k| * (1 + ‖z‖ ^ α) * ‖U k z‖ * ‖Q z‖ := by
            gcongr
            exact le_abs_self (c k)
        _ ≤ |c k| * (1 + R) * (N₀ + 1) * Z₀ := by gcongr
        _ ≤ |c k| * ((1 + R) * (N₀ + 1) * Z₀ + 1) := by
            nlinarith [abs_nonneg (c k)]
        _ < ε / 2 := (lt_div_iff₀ hC₁).mp hck
    -- Step 7: the second term is `≤ ‖U_k z − V z‖ C₂ < ε/2`.
    have h₂ : |A (U k z - V z) (Q z)| < ε / 2 := by
      have hQ := hZ₀ z hz
      calc |A (U k z - V z) (Q z)| = ‖A (U k z - V z) (Q z)‖ := (Real.norm_eq_abs _).symm
        _ ≤ CA * ‖U k z - V z‖ * ‖Q z‖ := hCA _ _
        _ ≤ CA * ‖U k z - V z‖ * Z₀ := by gcongr
        _ ≤ ‖U k z - V z‖ * (CA * Z₀ + 1) := by
            nlinarith [norm_nonneg (U k z - V z)]
        _ < ε / 2 := (lt_div_iff₀ hC₂).mp hP₂
    -- Step 8: the triangle inequality.
    rw [Real.dist_eq, hdec, abs_neg]
    calc |(ah k z (U k z) (Q z) - A (U k z) (Q z)) + A (U k z - V z) (Q z)|
        ≤ |ah k z (U k z) (Q z) - A (U k z) (Q z)| + |A (U k z - V z) (Q z)| := abs_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
      _ = ε := add_halves ε
  · -- Claim (ii), Step 9: with `C₃ = R Z₀`, eventually `|d_k| < ε/(C₃ + 1)` and the error bound
    -- holds on `K`, so `|Ψ_k z (Q z)| ≤ |d_k| C₃ < ε`.
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC₃ : 0 < R * Z₀ + 1 := by positivity
    have hδ : 0 < ε / (R * Z₀ + 1) := by positivity
    filter_upwards [Metric.tendsto_nhds.mp hd _ hδ, hΨ] with k hdk hΨk z hz
    rw [Real.dist_eq, sub_zero] at hdk
    have hQ := hZ₀ z hz
    have hRz := hR z hz
    rw [Real.dist_eq, zero_sub, abs_neg]
    calc |Ψ k z (Q z)| ≤ d k * ‖z‖ ^ α * ‖Q z‖ := hΨk z hz _
      _ ≤ |d k| * ‖z‖ ^ α * ‖Q z‖ := by
          gcongr
          exact le_abs_self (d k)
      _ ≤ |d k| * R * Z₀ := by gcongr
      _ ≤ |d k| * (R * Z₀ + 1) := by nlinarith [abs_nonneg (d k)]
      _ < ε := (lt_div_iff₀ hC₃).mp hdk

namespace Submission

/-- **Limit of the weak equations on growing balls** (blow-up step of the Schauder estimate behind
Simon 7.1).  Let `R_k → ∞`, `c_k, d_k → 0`, `V` continuous and `U_k → V` uniformly on every closed
ball `B_r(0)`.  Suppose that on `B̆_{R_k}(0)` the coefficients `â_k`, `Ψ_k` are continuous with
`|â_k(z)[P][Q] − A[P][Q]| ≤ c_k (1 + |z|^α) ‖P‖ ‖Q‖` and `|Ψ_k(z)[Q]| ≤ d_k |z|^α ‖Q‖`, and that
`∫_{B̆_{R_k}(0)} â_k[U_k][Dζ] = ∫_{B̆_{R_k}(0)} Ψ_k[Dζ]` for every `C¹` map `ζ` with compact support
in `B̆_{R_k}(0)`.  Then `∫ A[V][Dζ] = 0` for every compactly supported `C¹` map `ζ : ℝⁿ → ℝ^ℓ`: if
`spt ζ ⊆ B_r(0)`, then for `k` large `B_r(0) ⊆ B̆_{R_k}(0)`, the integrands vanish off `B_r(0)` and
converge uniformly on it, to `A[V][Dζ]` and to `0`, so
`∫ A[V][Dζ] = lim ∫ â_k[U_k][Dζ] = lim ∫ Ψ_k[Dζ] = 0`. -/
theorem dohr_eb_sch_bu_weak_eq_limit : ∀ (n ℓ : ℕ) (α : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ)) (V : Rn n → (Rn n →L[ℝ] Rn ℓ)) (R c d : ℕ → ℝ), 0 ≤ α → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → Continuous V → (∀ r : ℝ, TendstoUniformlyOn U V atTop (closedBall (0 : Rn n) r)) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ContinuousOn (U k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - A P Q| ≤ c k * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (U k z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (V z) (fderiv ℝ ζ z) = 0 := by
  intro n ℓ α A ah Ψ U V R c d hα hR hc hd hVc hUV hahc hΨc hUc hah hΨ hweak ζ hζ hζc
  -- Step 1: `tsupport ζ ⊆ B_r(0)`; `Z` bounds `‖Dζ‖` and `N` bounds `‖V‖` on `B_r(0)`.
  have hT : IsCompact (tsupport ζ) := hζc.isCompact
  obtain ⟨r, hTr⟩ := hT.isBounded.subset_closedBall (0 : Rn n)
  have hK : IsCompact (closedBall (0 : Rn n) r) := isCompact_closedBall 0 r
  have hDζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  obtain ⟨Z, hZ⟩ := hDζ.bounded_above_of_compact_support (hζc.fderiv ℝ)
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hVc.continuousOn
  -- `Dζ` vanishes off `tsupport ζ`, hence off `B_r(0)`.
  have hDζ0 : ∀ z, z ∉ tsupport ζ → fderiv ℝ ζ z = 0 := fun z hz =>
    Function.notMem_support.1 fun h => hz (support_fderiv_subset ℝ h)
  have hDζK : ∀ z, z ∉ closedBall (0 : Rn n) r → fderiv ℝ ζ z = 0 := fun z hz =>
    hDζ0 z fun h => hz (hTr h)
  -- Step 2: for `k` large, `r < R_k`, so `B_r(0) ⊆ B̆_{R_k}(0)`.
  have hRr : ∀ᶠ k in atTop, r < R k := hR.eventually_gt_atTop r
  -- Step 3: for `k` large both integrands are integrable, and the weak equation on `B̆_{R_k}(0)`
  -- becomes `∫ â_k[U_k][Dζ] = ∫ Ψ_k[Dζ]` over `ℝⁿ`; `A[V][Dζ]` is integrable.
  have hloc : ∀ᶠ k in atTop,
      (Integrable fun z => ah k z (U k z) (fderiv ℝ ζ z)) ∧
      (Integrable fun z => Ψ k z (fderiv ℝ ζ z)) ∧
      ∫ z, ah k z (U k z) (fderiv ℝ ζ z) = ∫ z, Ψ k z (fderiv ℝ ζ z) := by
    filter_upwards [hRr] with k hk
    have hTR : tsupport ζ ⊆ ball (0 : Rn n) (R k) := hTr.trans (closedBall_subset_ball hk)
    have hFk : (Integrable fun z => ah k z (U k z) (fderiv ℝ ζ z)) ∧
        ∫ z in ball (0 : Rn n) (R k), ah k z (U k z) (fderiv ℝ ζ z) =
          ∫ z, ah k z (U k z) (fderiv ℝ ζ z) :=
      (Submission.dohr_eb_sch_bu_wel_localized_integral n
        (fun z => ah k z (U k z) (fderiv ℝ ζ z)) _ _ isOpen_ball hT hTR
        ((hahc k).comp (continuousOn_id.prodMk ((hUc k).prodMk hDζ.continuousOn))
          fun z hz => ⟨hz, mem_univ _⟩)
        fun z hz => by simp only [hDζ0 z hz, map_zero]).2
    have hEk : (Integrable fun z => Ψ k z (fderiv ℝ ζ z)) ∧
        ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z) = ∫ z, Ψ k z (fderiv ℝ ζ z) :=
      (Submission.dohr_eb_sch_bu_wel_localized_integral n (fun z => Ψ k z (fderiv ℝ ζ z)) _ _
        isOpen_ball hT hTR ((hΨc k).clm_apply hDζ.continuousOn)
        fun z hz => by simp only [hDζ0 z hz, map_zero]).2
    exact ⟨hFk.1, hEk.1, by rw [← hFk.2, ← hEk.2]; exact hweak k ζ hζ hζc hTR⟩
  have hF0 : Integrable fun z => A (V z) (fderiv ℝ ζ z) :=
    (Submission.dohr_eb_sch_bu_wel_localized_integral n (fun z => A (V z) (fderiv ℝ ζ z)) univ _
      isOpen_univ hT (subset_univ _) ((A.continuous.comp hVc).clm_apply hDζ).continuousOn
      fun z hz => by simp only [hDζ0 z hz, map_zero]).2.1
  -- Steps 4–5, pointwise: on `B_r(0)`, `â_k[U_k][Dζ] → A[V][Dζ]` and `Ψ_k[Dζ] → 0` uniformly.
  obtain ⟨hF, hE⟩ := Submission.dohr_eb_sch_bu_wel_pairing_tendstoUniformlyOn n ℓ α r Z N A ah Ψ
    U V (fderiv ℝ ζ) (closedBall 0 r) c d hα hc hd (hUV r)
    (fun z hz => mem_closedBall_zero_iff.1 hz) (fun z _ => hZ z) hN
    (hRr.mono fun k hk z hz P P' => hah k z (closedBall_subset_ball hk hz) P P')
    (hRr.mono fun k hk z hz P => hΨ k z (closedBall_subset_ball hk hz) P)
  -- Steps 4–5, integrals: all integrands vanish off `B_r(0)`, so
  -- `∫ â_k[U_k][Dζ] → ∫ A[V][Dζ]` and `∫ Ψ_k[Dζ] → 0`.
  have hFlim := Submission.dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn n
    (closedBall 0 r) (fun k z => ah k z (U k z) (fderiv ℝ ζ z))
    (fun z => A (V z) (fderiv ℝ ζ z)) hK (hloc.mono fun k hk => hk.1) hF0
    (Eventually.of_forall fun k z hz => by simp only [hDζK z hz, map_zero])
    (fun z hz => by simp only [hDζK z hz, map_zero]) hF
  have hElim := Submission.dohr_eb_sch_bu_wel_tendsto_integral_of_tendstoUniformlyOn n
    (closedBall 0 r) (fun k z => Ψ k z (fderiv ℝ ζ z)) (fun _ => (0 : ℝ)) hK
    (hloc.mono fun k hk => hk.2.1) (integrable_zero _ _ _)
    (Eventually.of_forall fun k z hz => by simp only [hDζK z hz, map_zero])
    (fun _ _ => rfl) hE
  -- Step 6: `∫ A[V][Dζ] = lim ∫ â_k[U_k][Dζ] = lim ∫ Ψ_k[Dζ] = 0`.
  rw [integral_zero] at hElim
  exact tendsto_nhds_unique hFlim (hElim.congr' (hloc.mono fun k hk => hk.2.2.symm))
/-- **Blow-up limit for the Schauder estimate** (compactness and limit equation of the blow-up
argument).  Rescaled solutions `W_k` of `div (âₖ(z) DW_k) = div Ψ_k` on growing balls `B_{R_k}(0)`,
with `DW_k` uniformly `K`-`α`-Hölder, `DW_k(0) = 0` and `|DW_k(e_k)| = 1` at a point `|e_k| ≤ 1`,
and coefficients whose oscillation `c_k` and right sides `d_k` tend to `0`, have a subsequential
limit `W ∈ C¹(ℝⁿ)` with `DW(0) = 0`, `DW` globally `K`-`α`-Hölder, `|DW(e₀)| = 1`, solving the
constant-coefficient equation `∫ A[DW][Dζ] = 0` for a limit `A` of the frozen coefficients
`âₖ(0)`, which keeps their Legendre and boundedness constants.  This is the compactness step of
the blow-up proof of the Schauder estimates (L. Simon, *Schauder estimates by scaling*,
Calc. Var. PDE 5 (1997), 391–407). -/
theorem dohr_eb_sch_bu_blowup_limit : ∀ (n ℓ : ℕ) (α lam M K : ℝ) (W : ℕ → Rn n → Rn ℓ) (ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (e : ℕ → Rn n) (R c d : ℕ → ℝ), 0 < α → 0 ≤ K → Tendsto R atTop atTop → Tendsto c atTop (𝓝 0) → Tendsto d atTop (𝓝 0) → (∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k))) → (∀ k, W k 0 = 0) → (∀ k, fderiv ℝ (W k) 0 = 0) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k), ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ K * ‖z - z'‖ ^ α) → (∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) => ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ)) → (∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k))) → (∀ k, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ ah k 0 P P) → (∀ k, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ, |ah k z P Q - ah k 0 P Q| ≤ c k * ‖z‖ ^ α * ‖P‖ * ‖Q‖) → (∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q| ≤ d k * ‖z‖ ^ α * ‖Q‖) → (∀ k, ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) (R k) → ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) = ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z)) → (∀ k, ‖e k‖ ≤ 1) → (∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1) → ∃ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W' : Rn n → Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) ∧ (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ M * ‖P‖ * ‖Q‖) ∧ ContDiff ℝ 1 W' ∧ (∀ z z' : Rn n, ‖fderiv ℝ W' z - fderiv ℝ W' z'‖ ≤ K * ‖z - z'‖ ^ α) ∧ (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z, A (fderiv ℝ W' z) (fderiv ℝ ζ z) = 0) ∧ fderiv ℝ W' 0 = 0 ∧ ∃ e₀ : Rn n, ‖fderiv ℝ W' e₀‖ = 1 := by
  intro n ℓ α lam M K W ah Ψ e R c d hα hK hR hc hd hW hW0 hDW0 hHol hahc hΨc hell hbd hahz hΨ
    hweak he hunit
  -- At the default pending-synthesis depth, instance search does not find the operator-norm
  -- structure on the space of bilinear forms on `L(ℝⁿ, ℝ^ℓ)`, so it is supplied explicitly; this
  -- space is finite-dimensional, hence proper.
  let : NormedAddCommGroup ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  let : NormedSpace ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
  have : FiniteDimensional ℝ ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional (𝕜 := ℝ) (E := Rn n →L[ℝ] Rn ℓ)
      (F := (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
  have : ProperSpace ((Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) :=
    FiniteDimensional.proper_real _
  -- Step 1: `‖âₖ(0)‖ ≤ max M 0`, so a subsequence `â_{φA j}(0)` converges to some `A` in the
  -- finite-dimensional (hence proper) space of bilinear forms.
  obtain ⟨A, -, φA, hφA, hA⟩ :=
    (isCompact_closedBall (0 : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (max M 0)).tendsto_subseq (x := fun k => ah k 0) fun k => by
        rw [mem_closedBall_zero_iff]
        refine ContinuousLinearMap.opNorm_le_bound₂ _ (le_max_right M 0) fun P Q => ?_
        rw [Real.norm_eq_abs]
        exact (hbd k P Q).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left M 0) (norm_nonneg P)) (norm_nonneg Q))
  -- Step 2: the points `e_{φA j}` lie in `B̄₁(0)`; a further subsequence converges to `e₀`.
  obtain ⟨e₀, -, φe, hφe, he₀⟩ := (isCompact_closedBall (0 : Rn n) 1).tendsto_subseq
    (x := fun j => e (φA j)) fun j => mem_closedBall_zero_iff.mpr (he (φA j))
  -- Step 3: a diagonal subsequence along which `DW` converges locally uniformly to a continuous,
  -- globally `K`-`α`-Hölder `V` with `V(0) = 0`.
  obtain ⟨φ₂, V, hφ₂, hV0, hVc, hVHol, hVunif⟩ :=
    Submission.dohr_eb_sch_bu_holder_diag_subseq n ℓ α K (fun j => fderiv ℝ (W (φA (φe j))))
      (fun j => R (φA (φe j))) hα hK (hR.comp (hφA.comp hφe).tendsto_atTop)
      (fun j => hDW0 (φA (φe j))) (fun j => hHol (φA (φe j)))
  set ψ : ℕ → ℕ := fun i => φA (φe (φ₂ i))
  have hψ : Tendsto ψ atTop atTop := ((hφA.comp hφe).comp hφ₂).tendsto_atTop
  have hU : ∀ r : ℝ, TendstoUniformlyOn (fun i => fderiv ℝ (W (ψ i))) V atTop
      (closedBall (0 : Rn n) r) := hVunif
  -- Step 4: the limit `W'` is `C¹` on `ℝⁿ` with `DW' = V`.
  obtain ⟨W', hW'c, hW'V⟩ := Submission.dohr_eb_sch_bu_contDiff_of_fderiv_tendsto n ℓ
    (fun i => W (ψ i)) V (fun i => R (ψ i)) (hR.comp hψ) (fun i => hW (ψ i))
    (fun i => hW0 (ψ i)) hVc hU
  -- Step 5: `|âψᵢ(z)[P][Q] - A[P][Q]| ≤ (|c_{ψ i}| + ‖âψᵢ(0) - A‖)(1 + |z|^α)‖P‖‖Q‖`.
  have hAψ : Tendsto (fun i => ah (ψ i) 0) atTop (𝓝 A) := hA.comp (hφe.comp hφ₂).tendsto_atTop
  have hε : Tendsto (fun i => ‖ah (ψ i) 0 - A‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hAψ
  have hεb : ∀ i, ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah (ψ i) 0 P Q - A P Q| ≤ ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖ := fun i P Q => by
    have h := (ah (ψ i) 0 - A).le_opNorm₂ P Q
    rwa [sub_apply, sub_apply, Real.norm_eq_abs] at h
  have hc' : Tendsto (fun i => |c (ψ i)| + ‖ah (ψ i) 0 - A‖) atTop (𝓝 0) := by
    simpa using (hc.comp hψ).abs.add hε
  have hcoef : ∀ i, ∀ z ∈ ball (0 : Rn n) (R (ψ i)), ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah (ψ i) z P Q - A P Q| ≤ (|c (ψ i)| + ‖ah (ψ i) 0 - A‖) * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := by
    intro i z hz P Q
    have h1 := hahz (ψ i) z hz P Q
    have h2 := hεb i P Q
    have hzα : 0 ≤ ‖z‖ ^ α := Real.rpow_nonneg (norm_nonneg z) α
    have hPQ : 0 ≤ ‖P‖ * ‖Q‖ := mul_nonneg (norm_nonneg P) (norm_nonneg Q)
    have hε0 : 0 ≤ ‖ah (ψ i) 0 - A‖ := norm_nonneg _
    have hc0 : 0 ≤ |c (ψ i)| - c (ψ i) := sub_nonneg.mpr (le_abs_self _)
    calc |ah (ψ i) z P Q - A P Q|
        ≤ |ah (ψ i) z P Q - ah (ψ i) 0 P Q| + |ah (ψ i) 0 P Q - A P Q| := abs_sub_le _ _ _
      _ ≤ c (ψ i) * ‖z‖ ^ α * ‖P‖ * ‖Q‖ + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖ := add_le_add h1 h2
      _ ≤ (|c (ψ i)| + ‖ah (ψ i) 0 - A‖) * (1 + ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := by
        nlinarith [mul_nonneg (abs_nonneg (c (ψ i))) hPQ, mul_nonneg (mul_nonneg hc0 hzα) hPQ,
          mul_nonneg (mul_nonneg hε0 hzα) hPQ]
  -- Step 6: the weak equations pass to the limit.
  have hlim := Submission.dohr_eb_sch_bu_weak_eq_limit n ℓ α A (fun i => ah (ψ i))
    (fun i => Ψ (ψ i)) (fun i => fderiv ℝ (W (ψ i))) V (fun i => R (ψ i))
    (fun i => |c (ψ i)| + ‖ah (ψ i) 0 - A‖) (fun i => d (ψ i)) hα.le (hR.comp hψ) hc'
    (hd.comp hψ) hVc hU (fun i => hahc (ψ i)) (fun i => hΨc (ψ i))
    (fun i => (hW (ψ i)).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl) hcoef
    (fun i => hΨ (ψ i)) (fun i => hweak (ψ i))
  -- Step 7: the Legendre and boundedness constants pass to the limit `A`.
  have hellA : ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P := by
    intro P
    have hT : Tendsto (fun i => A P P + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖P‖) atTop
        (𝓝 (A P P + 0 * ‖P‖ * ‖P‖)) :=
      tendsto_const_nhds.add ((hε.mul_const ‖P‖).mul_const ‖P‖)
    rw [zero_mul, zero_mul, add_zero] at hT
    refine ge_of_tendsto' hT fun i => ?_
    have h1 := hell (ψ i) P
    have h2 := hεb i P P
    have h3 := le_abs_self (ah (ψ i) 0 P P - A P P)
    linarith
  have hbdA : ∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ M * ‖P‖ * ‖Q‖ := by
    intro P Q
    have hT : Tendsto (fun i => M * ‖P‖ * ‖Q‖ + ‖ah (ψ i) 0 - A‖ * ‖P‖ * ‖Q‖) atTop
        (𝓝 (M * ‖P‖ * ‖Q‖ + 0 * ‖P‖ * ‖Q‖)) :=
      tendsto_const_nhds.add ((hε.mul_const ‖P‖).mul_const ‖Q‖)
    rw [zero_mul, zero_mul, add_zero] at hT
    refine ge_of_tendsto' hT fun i => ?_
    have h1 := abs_le.mp (hbd (ψ i) P Q)
    have h2 := abs_le.mp (hεb i P Q)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- Step 8: `DWψᵢ(eψᵢ) → V(e₀)`, and these have norm `1` for large `i`, so `|V(e₀)| = 1`.
  have heψ : Tendsto (fun i => e (ψ i)) atTop (𝓝[closedBall (0 : Rn n) 1] e₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨he₀.comp hφ₂.tendsto_atTop,
      Eventually.of_forall fun i => mem_closedBall_zero_iff.mpr (he (ψ i))⟩
  have hVe₀ : ‖V e₀‖ = 1 :=
    tendsto_nhds_unique ((hU 1).tendsto_comp hVc.continuousWithinAt heψ).norm
      (tendsto_const_nhds.congr' ((hψ.eventually hunit).mono fun i hi => hi.symm))
  -- Step 9: conclusion.
  refine ⟨A, W', hellA, hbdA, hW'c, fun z z' => ?_, fun ζ hζ hζc => ?_, ?_, e₀, ?_⟩
  · rw [hW'V z, hW'V z']
    exact hVHol z z'
  · simp_rw [hW'V]
    exact hlim ζ hζ hζc
  · rw [hW'V 0, hV0]
  · rw [hW'V e₀]
    exact hVe₀
/-- **Zero mean of a linear form of `Dζ`** (step (1a) of the Schauder estimate in the elliptic
bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  For a continuous linear form `c` on
`L(ℝⁿ, ℝ^ℓ)` and a compactly supported `C¹` map `ζ : ℝⁿ → ℝ^ℓ`, `∫ c(Dζ(x)) dx = 0`.
Proof: `Dζ` is continuous with compact support, hence integrable, and `∫ c(Dζ) = c(∫ Dζ)`.
By translation invariance of Lebesgue measure, `y ↦ ∫ ζ(x + y) dx` is constant; differentiating
it at `0` under the integral sign (the derivatives `Dζ(x + y)`, `|y| < 1`, are bounded by a
constant times the indicator of a fixed ball) gives `∫ Dζ = 0`. -/
theorem dohr_eb_sch_integral_clm_fderiv_eq_zero : ∀ (n ℓ : ℕ) (c : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, c (fderiv ℝ ζ x) = 0 := by
  intro n ℓ c ζ hζ hcs
  -- Step 1: `Dζ` is continuous with compact support, hence integrable.
  have hcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hcsD : HasCompactSupport (fderiv ℝ ζ) := hcs.fderiv ℝ
  have hint : Integrable (fderiv ℝ ζ) := hcont.integrable_of_hasCompactSupport hcsD
  -- Step 2: pull `c` out of the integral; it suffices that `∫ Dζ = 0`.
  rw [ContinuousLinearMap.integral_comp_comm c hint]
  suffices h : ∫ x, fderiv ℝ ζ x = 0 by rw [h, map_zero]
  -- Step 3: `‖Dζ‖ ≤ C` everywhere and `tsupport Dζ ⊆ B_R(0)`.
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcsD
  obtain ⟨R, hR⟩ := hcsD.isCompact.isBounded.subset_closedBall (0 : Rn n)
  -- Step 4: differentiate `y ↦ ∫ ζ(x + y) dx` at `0` under the integral sign.
  have hderiv : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (∫ x, fderiv ℝ ζ (x + 0)) 0 := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball (0 : Rn n) 1)
      (F' := fun y x => fderiv ℝ ζ (x + y))
      (bound := (closedBall (0 : Rn n) (R + 1)).indicator fun _ => C)
      (ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun y =>
        (hζ.continuous.comp (continuous_add_const y)).aestronglyMeasurable
    · simpa using hζ.continuous.integrable_of_hasCompactSupport hcs
    · exact (hcont.comp (continuous_add_const 0)).aestronglyMeasurable
    · refine Eventually.of_forall fun x y hy => ?_
      show ‖fderiv ℝ ζ (x + y)‖ ≤ (closedBall (0 : Rn n) (R + 1)).indicator (fun _ => C) x
      by_cases hx : x ∈ closedBall (0 : Rn n) (R + 1)
      · rw [indicator_of_mem hx]
        exact hC _
      · have hxy : x + y ∉ tsupport (fderiv ℝ ζ) := fun h => hx (by
          have h1 := hR h
          rw [mem_closedBall_zero_iff] at h1 ⊢
          rw [mem_ball_zero_iff] at hy
          calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
            _ ≤ R + 1 := by linarith)
        rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hxy, norm_zero]
    · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
        measurableSet_closedBall
    · exact Eventually.of_forall fun x y _ =>
        (hasFDerivAt_comp_add_left x).2 ((hζ.differentiable one_ne_zero (x + y)).hasFDerivAt)
  -- Step 5: by translation invariance that function is constant, so its derivative is `0`.
  have hzero : HasFDerivAt (fun y : Rn n => ∫ x, ζ (x + y)) (0 : Rn n →L[ℝ] Rn ℓ) 0 :=
    (hasFDerivAt_const (∫ x, ζ x) (0 : Rn n)).congr_of_eventuallyEq
      (Eventually.of_forall fun y => integral_add_right_eq_self ζ y)
  simpa using hderiv.unique hzero

end Submission
/-- **Interpolation bound for `Dw`** (step (1b) of the Schauder estimate in the elliptic bootstrap
for Simon 7.1).  If `w` is `C¹` on `B̆_ρ(x)` with `|w| ≤ S` there and
`‖Dw(y) − Dw(z)‖ ≤ K |y − z|^α` for `y, z ∈ B̆_ρ(x)`, then `‖Dw(x)‖ ≤ 2S/t + t^α K` for every
`t ∈ (0, ρ)` (operator norm). -/
theorem Submission.dohr_eb_sch_fderiv_norm_interpolation : ∀ (n ℓ : ℕ) (w : Rn n → Rn ℓ) (x : Rn n) (ρ t α S K : ℝ), 0 ≤ α → 0 ≤ K → 0 < t → t < ρ → ContDiffOn ℝ 1 w (ball x ρ) → (∀ y ∈ ball x ρ, ‖w y‖ ≤ S) → (∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖fderiv ℝ w y - fderiv ℝ w z‖ ≤ K * ‖y - z‖ ^ α) → ‖fderiv ℝ w x‖ ≤ 2 * S / t + t ^ α * K := by
  intro n ℓ w x ρ t α S K hα hK ht htρ hw hS hH
  -- Step 1: `S ≥ |w(x)| ≥ 0`, so `B = 2S/t + t^α K ≥ 0`.
  have hxB : x ∈ ball x ρ := mem_ball_self (ht.trans htρ)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hB : 0 ≤ 2 * S / t + t ^ α * K :=
    add_nonneg (div_nonneg (mul_nonneg zero_le_two hS0) ht.le)
      (mul_nonneg (Real.rpow_nonneg ht.le α) hK)
  -- Step 2: `B_t(x) ⊆ B̆_ρ(x)`, and `w` has derivative `Dw(y)` at every `y ∈ B_t(x)`.
  have hsub : closedBall x t ⊆ ball x ρ := closedBall_subset_ball htρ
  have hdiff : ∀ y ∈ closedBall x t, HasFDerivWithinAt w (fderiv ℝ w y) (closedBall x t) y :=
    fun y hy => (((hw.differentiableOn one_ne_zero) y (hsub hy)).differentiableAt
      (isOpen_ball.mem_nhds (hsub hy))).hasFDerivAt.hasFDerivWithinAt
  -- Step 3: `‖Dw(y) − Dw(x)‖ ≤ K t^α` on `B_t(x)`.
  have hbound : ∀ y ∈ closedBall x t, ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * t ^ α := by
    intro y hy
    calc ‖fderiv ℝ w y - fderiv ℝ w x‖ ≤ K * ‖y - x‖ ^ α := hH y (hsub hy) x hxB
      _ ≤ K * t ^ α := by
        gcongr
        exact mem_closedBall_iff_norm.mp hy
  -- Steps 4–5: `|Dw(x) e| ≤ B` for every unit vector `e`.
  have hunit : ∀ e : Rn n, ‖e‖ = 1 → ‖fderiv ℝ w x e‖ ≤ 2 * S / t + t ^ α * K := by
    intro e he
    have hte : ‖t • e‖ = t := by rw [norm_smul, he, Real.norm_of_nonneg ht.le, mul_one]
    have hxe : x + t • e ∈ closedBall x t := by
      rw [mem_closedBall_iff_norm, add_sub_cancel_left, hte]
    -- Step 4: the mean value inequality for `h(y) = w(y) − Dw(x)(y − x)` on `B_t(x)` gives
    -- `|w(x + te) − w(x) − t Dw(x)e| ≤ K t^α · t`.
    have hmv := (convex_closedBall x t).norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff
      hbound (mem_closedBall_self ht.le) hxe
    rw [add_sub_cancel_left, hte, map_smul] at hmv
    -- Step 5: `t |Dw(x)e| ≤ |w(x + te) − w(x)| + |w(x + te) − w(x) − t Dw(x)e| ≤ 2S + K t^α t`.
    have h1 : ‖w (x + t • e)‖ ≤ S := hS _ (hsub hxe)
    have h2 : ‖w x‖ ≤ S := hS x hxB
    have key : t * ‖fderiv ℝ w x e‖ ≤ 2 * S + K * t ^ α * t :=
      calc t * ‖fderiv ℝ w x e‖ = ‖t • fderiv ℝ w x e‖ := by
            rw [norm_smul, Real.norm_of_nonneg ht.le]
        _ = ‖(w (x + t • e) - w x) - (w (x + t • e) - w x - t • fderiv ℝ w x e)‖ := by
            congr 1; abel
        _ ≤ ‖w (x + t • e) - w x‖ + ‖w (x + t • e) - w x - t • fderiv ℝ w x e‖ :=
            norm_sub_le _ _
        _ ≤ (‖w (x + t • e)‖ + ‖w x‖) + K * t ^ α * t := add_le_add (norm_sub_le _ _) hmv
        _ ≤ 2 * S + K * t ^ α * t := by linarith
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    linarith
  -- Step 6: `|Dw(x) v| = |v| |Dw(x)(v/|v|)| ≤ B |v|`, so `‖Dw(x)‖ ≤ B`.
  refine ContinuousLinearMap.opNorm_le_bound _ hB fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hv' : fderiv ℝ w x v = ‖v‖ • fderiv ℝ w x (‖v‖⁻¹ • v) := by
    rw [map_smul, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  rw [hv', norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
  exact (mul_le_mul_of_nonneg_left (hunit _ (norm_smul_inv_norm hv)) (norm_nonneg v)).trans_eq
    (mul_comm _ _)
namespace Submission

/-- **Affine rescaling of `C¹` weak solutions** (scaling step of the Schauder estimate in the
elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).  Let `w` be `C¹` on the open
set `U` with `∫_U a(x)[Dw][Dζ] = ∫_U Φ(x)[Dζ]` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let
`B_{ρr}(y + ρz₀) ⊆ U`, `ρ > 0`.  Then `w̃(z) = w(y + ρz)` is `C¹` on `B_r(z₀)`,
`Dw̃(z) = ρ Dw(y + ρz)` there, and `∫_{B_r(z₀)} a(y + ρz)[Dw̃][Dζ] = ∫_{B_r(z₀)} (ρΦ(y + ρz))[Dζ]`
for every `ζ ∈ C¹_c(B_r(z₀); ℝ^ℓ)`.
Proof: with `T z = y + ρz`, the test function `ζ ∘ T⁻¹` is admissible on `U`; both integrands
are `ρ²` times the original ones composed with `T` and vanish off the supports, and
`∫ H(y + ρz) dz = ρ⁻ⁿ ∫ H` holds for every `H` (no integrability needed). -/
theorem dohr_eb_sch_weak_eq_affine_rescale : ∀ (n ℓ : ℕ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (U : Set (Rn n)) (y z₀ : Rn n) (ρ r : ℝ), 0 < ρ → IsOpen U → ball (y + ρ • z₀) (ρ * r) ⊆ U → ContDiffOn ℝ 1 w U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → ContDiffOn ℝ 1 (fun z => w (y + ρ • z)) (ball z₀ r) ∧ (∀ z ∈ ball z₀ r, fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z)) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball z₀ r → ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
  intro n ℓ a Φ w U y z₀ ρ r hρ hU hball hw hweak
  have hρ0 : ρ ≠ 0 := hρ.ne'
  -- Step 0: `T z = y + ρ • z` maps `B_r(z₀)` into `B_{ρ r}(y + ρ z₀) ⊆ U`.
  have hT : MapsTo (fun z : Rn n => y + ρ • z) (ball z₀ r) U := by
    intro z hz
    apply hball
    show dist (y + ρ • z) (y + ρ • z₀) < ρ * r
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_mul_of_pos_left (mem_ball.mp hz) hρ
  -- `T` is affine with derivative `ρ • id` everywhere.
  have hTd : ∀ z : Rn n,
      HasFDerivAt (fun z : Rn n => y + ρ • z) (ρ • ContinuousLinearMap.id ℝ (Rn n)) z :=
    fun z => ((hasFDerivAt_id z).const_smul ρ).const_add y
  -- Step 1 (ii): chain rule at points of `B_r(z₀)`, where `w` is differentiable.
  have hderiv : ∀ z ∈ ball z₀ r,
      fderiv ℝ (fun z => w (y + ρ • z)) z = ρ • fderiv ℝ w (y + ρ • z) := by
    intro z hz
    have hwd : DifferentiableAt ℝ w (y + ρ • z) :=
      (hw.differentiableOn one_ne_zero _ (hT hz)).differentiableAt (hU.mem_nhds (hT hz))
    have h := hwd.hasFDerivAt.comp z (hTd z)
    rw [show (fun z => w (y + ρ • z)) = w ∘ (fun z : Rn n => y + ρ • z) from rfl, h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  have hTC : ContDiff ℝ 1 (fun z : Rn n => y + ρ • z) :=
    contDiff_const.add (contDiff_id.const_smul ρ)
  refine ⟨hw.comp hTC.contDiffOn hT, hderiv, ?_⟩
  -- Step 2: transfer the test function, `ζ' = ζ ∘ T⁻¹`.
  intro ζ hζ hζc hζs
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : Rn n → Rn ℓ, ζ' = fun x => ζ (ρ⁻¹ • (x - y)) := ⟨_, rfl⟩
  have hζ'T : ∀ z, ζ' (y + ρ • z) = ζ z := by
    intro z
    simp [hζ', inv_smul_smul₀ hρ0]
  have hζ'C : ContDiff ℝ 1 ζ' := by
    rw [hζ']
    exact hζ.comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
  have hK : IsCompact ((fun z : Rn n => y + ρ • z) '' tsupport ζ) :=
    hζc.isCompact.image hTC.continuous
  have hζ'K : ∀ x, x ∉ (fun z : Rn n => y + ρ • z) '' tsupport ζ → ζ' x = 0 := by
    intro x hx
    rw [hζ']
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hx
    refine ⟨ρ⁻¹ • (x - y), hmem, ?_⟩
    simp [smul_inv_smul₀ hρ0]
  have hζ'c : HasCompactSupport ζ' := HasCompactSupport.intro hK hζ'K
  have hζ'sK : tsupport ζ' ⊆ (fun z : Rn n => y + ρ • z) '' tsupport ζ :=
    closure_minimal (Function.support_subset_iff'.mpr hζ'K) hK.isClosed
  have hζ's : tsupport ζ' ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hζ'sK hx
    exact hT (hζs hz)
  have hweak' := hweak ζ' hζ'C hζ'c hζ's
  -- `Dζ(z) = ρ • Dζ'(T z)` for every `z`.
  have hζd : ∀ z, fderiv ℝ ζ z = ρ • fderiv ℝ ζ' (y + ρ • z) := by
    intro z
    have h := (hζ'C.differentiable one_ne_zero (y + ρ • z)).hasFDerivAt.comp z (hTd z)
    have hfun : ζ' ∘ (fun z : Rn n => y + ρ • z) = ζ := funext hζ'T
    rw [hfun] at h
    rw [h.fderiv]
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  -- Step 3: the integrands over `U` vanish off `U`.
  have hF0 : ∀ x, x ∉ U → a x (fderiv ℝ w x) (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  have hG0 : ∀ x, x ∉ U → Φ x (fderiv ℝ ζ' x) = 0 := by
    intro x hx
    have hx' : x ∉ tsupport ζ' := fun h => hx (hζ's h)
    rw [fderiv_of_notMem_tsupport ℝ hx', map_zero]
  -- Step 4: pointwise identities.
  have hFt : ∀ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) =
      ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    by_cases hz : z ∈ ball z₀ r
    · rw [hderiv z hz, hζd z]
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    · have h1 : fderiv ℝ ζ z = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h))
      have h2 : fderiv ℝ ζ' (y + ρ • z) = 0 := by
        have h3 := hζd z
        rw [h1] at h3
        exact (smul_eq_zero.mp h3.symm).resolve_left hρ0
      rw [h1, h2]
      simp
  have hGt : ∀ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) =
      ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
    intro z
    rw [hζd z]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  -- Step 5: change of variables, valid without integrability.
  have hcov : ∀ H : Rn n → ℝ,
      ∫ z, H (y + ρ • z) = |(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, H x := by
    intro H
    rw [Measure.integral_comp_smul volume (fun x => H (y + x)) ρ, integral_add_left_eq_self H y]
  -- Step 6: conclusion.
  calc ∫ z in ball z₀ r, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z)
      = ∫ z, a (y + ρ • z) (fderiv ℝ (fun z => w (y + ρ • z)) z) (fderiv ℝ ζ z) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]
    _ = ∫ z, ρ ^ 2 * a (y + ρ • z) (fderiv ℝ w (y + ρ • z)) (fderiv ℝ ζ' (y + ρ • z)) := by
        congr 1
        funext z
        exact hFt z
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| •
          ∫ x, a x (fderiv ℝ w x) (fderiv ℝ ζ' x)) := by
        rw [integral_const_mul, hcov (fun x => a x (fderiv ℝ w x) (fderiv ℝ ζ' x))]
    _ = ρ ^ 2 * (|(ρ ^ Module.finrank ℝ (Rn n))⁻¹| • ∫ x, Φ x (fderiv ℝ ζ' x)) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hF0, hweak',
          setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
    _ = ∫ z, ρ ^ 2 * Φ (y + ρ • z) (fderiv ℝ ζ' (y + ρ • z)) := by
        rw [integral_const_mul, hcov (fun x => Φ x (fderiv ℝ ζ' x))]
    _ = ∫ z, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        congr 1
        funext z
        exact (hGt z).symm
    _ = ∫ z in ball z₀ r, (ρ • Φ (y + ρ • z)) (fderiv ℝ ζ z) := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hζs h)), map_zero]
/-- Symmetry of the second derivative of a `C²` map `V : ℝⁿ → ℝ^ℓ` (Schwarz–Clairaut):
`D²V(x)(v)(w) = D²V(x)(w)(v)`.  Mathlib's `ContDiffAt.isSymmSndFDerivAt` is not imported here, so
we argue with the second difference `Δ(t) = V(x + ta + tb) − V(x + ta) − V(x + tb) + V(x)`:
continuity of `z ↦ D²V(z)(b)` and two mean value inequalities (along `[y, y + tb]`, then along
`[x, x + ta]`) give `‖Δ(t) − t² D²V(x)(b)(a)‖ ≤ δ t² ‖a‖` for small `t > 0`.  As `Δ` is symmetric
in `(a, b)`, `‖D²V(x)(w)(v) − D²V(x)(v)(w)‖ ≤ δ (‖v‖ + ‖w‖)` for every `δ > 0`. -/
theorem dohr_eb_sch_liou_snd_deriv_symm : ∀ (n ℓ : ℕ) (V : Rn n → Rn ℓ), ContDiff ℝ 2 V → ∀ x v w : Rn n, fderiv ℝ (fderiv ℝ V) x v w = fderiv ℝ (fderiv ℝ V) x w v := by
  intro n ℓ V hV x v w
  have hDV : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hDVd : Differentiable ℝ (fderiv ℝ V) := hDV.differentiable one_ne_zero
  have hVd : Differentiable ℝ V := hV.differentiable (by norm_num)
  -- z ↦ D²V(z) b is continuous (values in L)
  have hHcont : ∀ b : Rn n, Continuous (fun z => fderiv ℝ (fderiv ℝ V) z b) := fun b =>
    (hDV.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  -- inner estimate along the segment [y, y + t b], applied to a vector a
  have inner : ∀ a b : Rn n, ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ y : Rn n, ∀ t : ℝ, 0 ≤ t →
      ‖y - x‖ + t * ‖b‖ < r →
      ‖fderiv ℝ V (y + t • b) a - fderiv ℝ V y a - t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤
        δ * ‖a‖ * t := by
    intro a b δ hδ
    have hc : Continuous (fun z => ‖fderiv ℝ (fderiv ℝ V) z b - fderiv ℝ (fderiv ℝ V) x b‖) :=
      ((hHcont b).sub continuous_const).norm
    have h0 : ‖fderiv ℝ (fderiv ℝ V) x b - fderiv ℝ (fderiv ℝ V) x b‖ < δ := by
      rw [sub_self, norm_zero]; exact hδ
    have h1 : ∀ᶠ z in 𝓝 x, ‖fderiv ℝ (fderiv ℝ V) z b - fderiv ℝ (fderiv ℝ V) x b‖ < δ :=
      hc.continuousAt.eventually_lt continuousAt_const h0
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨r, hr, fun y t ht hyt => ?_⟩
    have hg : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt
        (fun s : ℝ => fderiv ℝ V (y + s • b) a - s • fderiv ℝ (fderiv ℝ V) x b a)
        (fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a) (Icc 0 t) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => y + s • b) b s := by
        simpa using ((hasDerivAt_id s).smul_const b).const_add y
      have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ V (y + s • b))
          (fderiv ℝ (fderiv ℝ V) (y + s • b) b) s :=
        (hDVd (y + s • b)).hasFDerivAt.comp_hasDerivAt s h1
      have h2a : HasDerivAt (fun s : ℝ => fderiv ℝ V (y + s • b) a)
          (fderiv ℝ (fderiv ℝ V) (y + s • b) b a) s := by
        have := h2.clm_apply (hasDerivAt_const s a)
        simpa using this
      have h3 : HasDerivAt (fun s : ℝ => s • fderiv ℝ (fderiv ℝ V) x b a)
          (fderiv ℝ (fderiv ℝ V) x b a) s := by
        simpa using (hasDerivAt_id s).smul_const (fderiv ℝ (fderiv ℝ V) x b a)
      exact (h2a.sub h3).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) t,
        ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * ‖a‖ := by
      intro s hs
      have hlt : ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b‖ < δ := by
        apply hball
        rw [dist_eq_norm]
        calc ‖y + s • b - x‖ = ‖(y - x) + s • b‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖s • b‖ := norm_add_le _ _
          _ = ‖y - x‖ + s * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
          _ ≤ ‖y - x‖ + t * ‖b‖ := by gcongr; exact hs.2.le
          _ < r := hyt
      calc ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b a - fderiv ℝ (fderiv ℝ V) x b a‖
          = ‖(fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b) a‖ := by simp
        _ ≤ ‖fderiv ℝ (fderiv ℝ V) (y + s • b) b - fderiv ℝ (fderiv ℝ V) x b‖ * ‖a‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ δ * ‖a‖ := by gcongr
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hg hbound t ⟨ht, le_rfl⟩
    simp only [zero_smul, add_zero, sub_zero] at h
    calc ‖fderiv ℝ V (y + t • b) a - fderiv ℝ V y a - t • fderiv ℝ (fderiv ℝ V) x b a‖
        = ‖fderiv ℝ V (y + t • b) a - t • fderiv ℝ (fderiv ℝ V) x b a - fderiv ℝ V y a‖ := by
          congr 1; abel
      _ ≤ δ * ‖a‖ * t := h
  -- outer estimate: the second difference is ≈ t² D²V(x)(b)(a)
  have outer : ∀ a b : Rn n, ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ t : ℝ, 0 < t →
      t * (‖a‖ + ‖b‖) < r →
      ‖(V (x + t • a + t • b) - V (x + t • a) - V (x + t • b) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * t * (t * ‖a‖) := by
    intro a b δ hδ
    obtain ⟨r, hr, hin⟩ := inner a b δ hδ
    refine ⟨r, hr, fun t ht htr => ?_⟩
    have hk : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt
        (fun s : ℝ => V (x + s • a + t • b) - V (x + s • a) -
          s • (t • fderiv ℝ (fderiv ℝ V) x b a))
        (fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
          t • fderiv ℝ (fderiv ℝ V) x b a) (Icc 0 t) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => x + s • a + t • b) a s := by
        simpa using (((hasDerivAt_id s).smul_const a).const_add x).add_const (t • b)
      have h1' : HasDerivAt (fun s : ℝ => x + s • a) a s := by
        simpa using ((hasDerivAt_id s).smul_const a).const_add x
      have h2 := (hVd (x + s • a + t • b)).hasFDerivAt.comp_hasDerivAt s h1
      have h3 := (hVd (x + s • a)).hasFDerivAt.comp_hasDerivAt s h1'
      have h4 : HasDerivAt (fun s : ℝ => s • (t • fderiv ℝ (fderiv ℝ V) x b a))
          (t • fderiv ℝ (fderiv ℝ V) x b a) s := by
        simpa using (hasDerivAt_id s).smul_const (t • fderiv ℝ (fderiv ℝ V) x b a)
      exact ((h2.sub h3).sub h4).hasDerivWithinAt
    have hbound : ∀ s ∈ Ico (0 : ℝ) t,
        ‖fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
          t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * t * ‖a‖ := by
      intro s hs
      have hy : ‖(x + s • a) - x‖ + t * ‖b‖ < r := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        have : s * ‖a‖ ≤ t * ‖a‖ := by gcongr; exact hs.2.le
        nlinarith
      have h := hin (x + s • a) t ht.le hy
      calc ‖fderiv ℝ V (x + s • a + t • b) a - fderiv ℝ V (x + s • a) a -
            t • fderiv ℝ (fderiv ℝ V) x b a‖ ≤ δ * ‖a‖ * t := h
        _ = δ * t * ‖a‖ := by ring
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hk hbound t ⟨ht.le, le_rfl⟩
    simp only [zero_smul, add_zero, sub_zero] at h
    calc ‖(V (x + t • a + t • b) - V (x + t • a) - V (x + t • b) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x b a‖
        = ‖V (x + t • a + t • b) - V (x + t • a) - t • t • fderiv ℝ (fderiv ℝ V) x b a -
            (V (x + t • b) - V x)‖ := by
          rw [mul_smul]; congr 1; abel
      _ ≤ δ * t * ‖a‖ * t := h
      _ = δ * t * (t * ‖a‖) := by ring
  -- conclusion: compare the estimates for (v, w) and (w, v), then let δ → 0
  have key : ∀ δ : ℝ, 0 < δ →
      ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤ δ * (‖v‖ + ‖w‖) := by
    intro δ hδ
    obtain ⟨r1, hr1, h1⟩ := outer v w δ hδ
    obtain ⟨r2, hr2, h2⟩ := outer w v δ hδ
    set r := min r1 r2
    have hr : 0 < r := lt_min hr1 hr2
    have hden : 0 < 2 * (‖v‖ + ‖w‖ + 1) := by positivity
    set t : ℝ := r / (2 * (‖v‖ + ‖w‖ + 1)) with ht_def
    have ht : 0 < t := div_pos hr hden
    have htr : t * (‖v‖ + ‖w‖) < r := by
      rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg v, norm_nonneg w]
    have e1 := h1 t ht (lt_of_lt_of_le htr (min_le_left _ _))
    have e2 := h2 t ht (by
      have : t * (‖w‖ + ‖v‖) = t * (‖v‖ + ‖w‖) := by ring
      rw [this]; exact lt_of_lt_of_le htr (min_le_right _ _))
    have hcomm : x + t • w + t • v = x + t • v + t • w := by abel
    rw [hcomm] at e2
    have hdiff : (t * t) • (fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w) =
        ((V (x + t • v + t • w) - V (x + t • w) - V (x + t • v) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x v w) -
        ((V (x + t • v + t • w) - V (x + t • v) - V (x + t • w) + V x) -
          (t * t) • fderiv ℝ (fderiv ℝ V) x w v) := by
      rw [smul_sub]; abel
    have htt : 0 < t * t := mul_pos ht ht
    have hbound : (t * t) * ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤
        (t * t) * (δ * (‖v‖ + ‖w‖)) := by
      have hn : (t * t) * ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ =
          ‖(t * t) • (fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos htt]
      rw [hn, hdiff]
      calc _ ≤ ‖(V (x + t • v + t • w) - V (x + t • w) - V (x + t • v) + V x) -
              (t * t) • fderiv ℝ (fderiv ℝ V) x v w‖ +
            ‖(V (x + t • v + t • w) - V (x + t • v) - V (x + t • w) + V x) -
              (t * t) • fderiv ℝ (fderiv ℝ V) x w v‖ := norm_sub_le _ _
        _ ≤ δ * t * (t * ‖w‖) + δ * t * (t * ‖v‖) := add_le_add e2 e1
        _ = (t * t) * (δ * (‖v‖ + ‖w‖)) := by ring
    exact le_of_mul_le_mul_left hbound htt
  have hle : ‖fderiv ℝ (fderiv ℝ V) x w v - fderiv ℝ (fderiv ℝ V) x v w‖ ≤ 0 := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hpos : 0 < ‖v‖ + ‖w‖ + 1 := by positivity
    have := key (ε / (‖v‖ + ‖w‖ + 1)) (div_pos hε hpos)
    calc _ ≤ ε / (‖v‖ + ‖w‖ + 1) * (‖v‖ + ‖w‖) := this
      _ < 0 + ε := by
        rw [zero_add, div_mul_eq_mul_div, div_lt_iff₀ hpos]
        nlinarith
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp hle)).symm
/-- Cutoff for the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap for
Simon Ch. 5, Theorem 7.1, second assertion (p. 127): there is `K ≥ 0` such that for every `n`,
`y ∈ ℝⁿ` and `ρ > 0` some `C¹` function `η : ℝⁿ → [0, 1]` equals `1` on `B̆_ρ(y)`, has compact
support with `tsupport η ⊆ B̆_{2ρ}(y)`, and satisfies `‖Dη(x)‖ ≤ K/ρ`.  Here
`η(x) = ψ(‖x − y‖²/ρ²)` with `ψ(s) = S((3 − s)/2)`, `S = Real.smoothTransition`, and
`K = 4 sup |ψ'|`. -/
theorem dohr_eb_sch_cacc_exists_cutoff : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (y : Rn n) (ρ : ℝ), 0 < ρ → ∃ η : Rn n → ℝ, ContDiff ℝ 1 η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ (∀ x ∈ ball y ρ, η x = 1) ∧ HasCompactSupport η ∧ tsupport η ⊆ ball y (2 * ρ) ∧ ∀ x, ‖fderiv ℝ η x‖ ≤ K / ρ := by
  -- Step 1: the profile `ψ(s) = S((3 − s)/2)` is `C¹`; `ψ = 1` for `s ≤ 1`, `ψ = 0` for `s ≥ 3`.
  set ψ : ℝ → ℝ := fun s => Real.smoothTransition ((3 - s) / 2) with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    (Real.smoothTransition.contDiff (n := 1)).comp ((contDiff_const.sub contDiff_id).div_const _)
  -- Step 2: `ψ'` is continuous and vanishes off `[1, 3]`, so `|ψ'| ≤ cψ` with `cψ ≥ 0`;
  -- `K = 4 cψ`.
  have hψ'c : Continuous (deriv ψ) := hψc.continuous_deriv le_rfl
  have hψ'0 : ∀ s, s ∉ Icc (1 : ℝ) 3 → deriv ψ s = 0 := by
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.one_of_one_le (by linarith [mem_Iio.mp ht])
      rw [hev.deriv_eq, deriv_const]
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [hψ]
        exact Real.smoothTransition.zero_of_nonpos (by linarith [mem_Ioi.mp ht])
      rw [hev.deriv_eq, deriv_const]
  obtain ⟨cψ, hcψ⟩ : ∃ cψ, ∀ s, ‖deriv ψ s‖ ≤ cψ := by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn (hψ'c.continuousOn (s := Icc (1 : ℝ) 3))
    refine ⟨max C 0, fun s => ?_⟩
    by_cases hs : s ∈ Icc (1 : ℝ) 3
    · exact (hC s hs).trans (le_max_left _ _)
    · rw [hψ'0 s hs, norm_zero]
      exact le_max_right _ _
  have hcψ0 : 0 ≤ cψ := (norm_nonneg _).trans (hcψ 0)
  refine ⟨4 * cψ, by positivity, ?_⟩
  -- Step 3: for `n`, `y` and `ρ > 0` take `η(x) = ψ(‖x − y‖²/ρ²)`.
  intro n y ρ hρ
  have hρ2 : 0 < ρ ^ 2 := by positivity
  -- Step 4: `η(x) ≠ 0` forces `‖x − y‖² < 3ρ²`, so `tsupport η ⊆ B_{7ρ/4}(y)` (closed ball).
  have hsupp : Function.support (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆
      closedBall y (7 / 4 * ρ) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [mem_closedBall, dist_eq_norm]
    by_contra hlt
    push Not at hlt
    apply hx
    simp only [hψ]
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : 3 * ρ ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith
    have h2 : 3 ≤ ‖x - y‖ ^ 2 / ρ ^ 2 := by
      rw [le_div_iff₀ hρ2]
      linarith
    linarith
  have htsupp : tsupport (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) ⊆ closedBall y (7 / 4 * ρ) :=
    closure_minimal hsupp isClosed_closedBall
  refine ⟨fun x => ψ (‖x - y‖ ^ 2 / ρ ^ 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `η` is `C¹`: `ψ` composed with the smooth map `x ↦ ‖x − y‖²/ρ²`.
  · exact hψc.comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)
  -- `0 ≤ η ≤ 1` since `0 ≤ S ≤ 1`.
  · intro x
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `η = 1` on `B̆_ρ(y)`: there `‖x − y‖²/ρ² < 1`.
  · intro x hx
    have hx' : ‖x - y‖ < ρ := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hx
    have h1 : ‖x - y‖ ^ 2 < ρ ^ 2 := by nlinarith [norm_nonneg (x - y)]
    have h2 : ‖x - y‖ ^ 2 / ρ ^ 2 < 1 := by
      rw [div_lt_one hρ2]
      exact h1
    simp only [hψ]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  -- Compact support: `tsupport η` is a closed subset of the compact `B_{7ρ/4}(y)`.
  · exact (isCompact_closedBall y (7 / 4 * ρ)).of_isClosed_subset (isClosed_tsupport _) htsupp
  -- `tsupport η ⊆ B_{7ρ/4}(y) ⊆ B̆_{2ρ}(y)`.
  · refine htsupp.trans (closedBall_subset_ball ?_)
    linarith
  -- Step 5: by the chain rule `Dη(x) = ψ'(s) (2/ρ²) ⟨x − y, ·⟩` with `s = ‖x − y‖²/ρ²`, so
  -- `‖Dη(x)‖ = |ψ'(s)| (2/ρ²) ‖x − y‖`; this is `0` if `s > 3`, and if `s ≤ 3` then
  -- `‖x − y‖ ≤ 2ρ` and `‖Dη(x)‖ ≤ cψ (2/ρ²) (2ρ) = 4 cψ/ρ`.
  · intro x
    set s := ‖x - y‖ ^ 2 / ρ ^ 2 with hs
    have hf : HasFDerivAt (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2)
        (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y)) x := by
      have h0 : HasFDerivAt (fun x : Rn n => x - y) (ContinuousLinearMap.id ℝ (Rn n)) x :=
        (hasFDerivAt_id x).sub_const y
      have := h0.norm_sq.mul_const ((ρ ^ 2)⁻¹)
      simp only [div_eq_mul_inv]
      convert this using 1
      ext v
      simp
      ring
    have hψd : HasDerivAt ψ (deriv ψ s) s :=
      ((hψc.differentiable one_ne_zero) s).hasDerivAt
    have hη := hψd.comp_hasFDerivAt x hf
    rw [show (fun x : Rn n => ψ (‖x - y‖ ^ 2 / ρ ^ 2)) =
        ψ ∘ (fun x : Rn n => ‖x - y‖ ^ 2 / ρ ^ 2) from rfl, hη.fderiv]
    by_cases h3 : 3 < s
    · rw [hψ'0 s (fun h => by linarith [h.2]), zero_smul, norm_zero]
      positivity
    · push Not at h3
      have hxy : ‖x - y‖ ≤ 2 * ρ := by
        have : ‖x - y‖ ^ 2 ≤ 3 * ρ ^ 2 := by
          have := (div_le_iff₀ hρ2).mp h3
          linarith
        nlinarith [norm_nonneg (x - y)]
      have hnorm : ‖deriv ψ s • (((ρ ^ 2)⁻¹ * 2) • innerSL ℝ (x - y))‖ =
          ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖) := by
        rw [norm_smul, norm_smul, innerSL_apply_norm,
          Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (ρ ^ 2)⁻¹ * 2)]
      rw [hnorm]
      calc ‖deriv ψ s‖ * (((ρ ^ 2)⁻¹ * 2) * ‖x - y‖)
          ≤ cψ * (((ρ ^ 2)⁻¹ * 2) * (2 * ρ)) := by
            gcongr
            exact hcψ s
        _ = 4 * cψ / ρ := by
            field_simp
            ring
/-- Test function of the Caccioppoli inequality in the Schauder estimate of the elliptic bootstrap
for Simon Ch. 5, Theorem 7.1, second assertion (p. 127): if `U ⊆ ℝⁿ` is open, `V ∈ C¹(U; ℝ^ℓ)`,
`c ∈ ℝ^ℓ` and `η ∈ C¹_c(ℝⁿ)` with `spt η ⊆ U`, then `ζ = η² (V − c)` is `C¹` on `ℝⁿ` with compact
support in `U`, and `Dζ = η² DV + 2η (V − c) ⊗ Dη` at every point of `ℝⁿ` (off `U` both sides
vanish, whatever the junk value of `DV` there). -/
theorem dohr_eb_sch_cacc_test_function : ∀ (n ℓ : ℕ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) ∧ HasCompactSupport (fun x => η x ^ 2 • (V x - c)) ∧ tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ U ∧ ∀ x, fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x = η x ^ 2 • fderiv ℝ V x + (2 * η x) • (fderiv ℝ η x).smulRight (V x - c) := by
  intro n ℓ U V η c hU hV hη hηc hηU
  -- Step 1: `support ζ ⊆ support η`, so `tsupport ζ ⊆ tsupport η ⊆ U` and `ζ` has compact support.
  -- (Bare `support` is `RectifiableVarifold.support` in this scope.)
  have hsupp : Function.support (fun x => η x ^ 2 • (V x - c)) ⊆ Function.support η := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp [h0]
  have htsupp : tsupport (fun x => η x ^ 2 • (V x - c)) ⊆ tsupport η := closure_mono hsupp
  have hcs : HasCompactSupport (fun x => η x ^ 2 • (V x - c)) := hηc.mono hsupp
  -- Step 2: `ζ` is `C¹` on `U`, as the product of `η² ∈ C¹(ℝⁿ)` and `V − c ∈ C¹(U)`.
  have h1 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) U :=
    ((hη.pow 2).contDiffOn).smul (hV.sub contDiffOn_const)
  -- Step 3: `ζ = 0` on the open set `W = (tsupport η)ᶜ`, so `ζ` is `C¹` on `W`.
  have h2 : ContDiffOn ℝ 1 (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
    have heq : EqOn (fun _ => (0 : Rn ℓ)) (fun x => η x ^ 2 • (V x - c)) (tsupport η)ᶜ := by
      intro x hx
      have : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
    exact contDiffOn_const.congr (fun x hx => (heq hx).symm)
  -- Step 4: `U ∪ W = ℝⁿ` because `tsupport η ⊆ U`; gluing the two open pieces, `ζ ∈ C¹(ℝⁿ)`.
  have hcover : U ∪ (tsupport η)ᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ tsupport η
    · exact Or.inl (hηU hx)
    · exact Or.inr hx
  have hcd : ContDiff ℝ 1 (fun x => η x ^ 2 • (V x - c)) :=
    contDiff_of_contDiffOn_union_of_isOpen h1 h2 hcover hU (isClosed_tsupport η).isOpen_compl
  refine ⟨hcd, hcs, htsupp.trans hηU, fun x => ?_⟩
  by_cases hx : x ∈ U
  -- Step 5: at `x ∈ U`, `D(η²)(x) = 2η(x) Dη(x)` and the product rule for `η² • (V − c)` give
  -- `Dζ(x) = η(x)² DV(x) + (2η(x) Dη(x)).smulRight (V(x) − c)`.
  · have hVd : HasFDerivAt V (fderiv ℝ V x) x :=
      (((hV.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hηd : HasFDerivAt η (fderiv ℝ η x) x := ((hη.differentiable one_ne_zero) x).hasFDerivAt
    have hsq : HasFDerivAt (fun x => η x ^ 2) ((2 * η x) • fderiv ℝ η x) x := by
      have := hηd.mul hηd
      convert this using 1
      · ext y; simp [sq]
      · rw [two_mul, add_smul]
    have hprod := hsq.smul (hVd.sub_const c)
    rw [show (fun x => η x ^ 2 • (V x - c)) = ((fun x => η x ^ 2) • fun x => V x - c) from rfl,
      hprod.fderiv]
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul, mul_comm]
  -- Step 6: at `x ∉ U`, `x ∉ tsupport η ⊇ tsupport ζ`, so `Dζ(x) = 0`, `Dη(x) = 0` and `η(x) = 0`;
  -- both sides vanish.
  · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
    have hxζ : x ∉ tsupport (fun x => η x ^ 2 • (V x - c)) := fun h => hx' (htsupp h)
    rw [fderiv_of_notMem_tsupport ℝ hxζ, fderiv_of_notMem_tsupport ℝ hx',
      image_eq_zero_of_notMem_tsupport hx']
    ext v
    simp
/-- Energy (Caccioppoli) estimate for a constant-coefficient elliptic system.  Let `A` satisfy the
Legendre condition `A[P][P] ≥ λ‖P‖²` and the bound `|A[P][Q]| ≤ Λ‖P‖‖Q‖`, let `V` be `C¹` on the open
set `U` with `∫ A[DV][Dζ] = 0` for every `ζ ∈ C¹_c(U; ℝ^ℓ)`, and let `η ≥ 0` be a `C¹_c` cutoff with
`tsupport η ⊆ U`.  Then `∫ η²‖DV‖² ≤ (4Λ²/λ²) ∫ ‖V − c‖²‖Dη‖²` (lower integrals, in `[0, ∞]`).
Test with `ζ = η²(V − c)` and absorb the cross term by Young's inequality. -/
theorem dohr_eb_sch_cacc_energy_estimate :
    ∀ (n ℓ : ℕ) (lam Lam : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (V : Rn n → Rn ℓ) (η : Rn n → ℝ) (c : Rn ℓ), 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → IsOpen U → ContDiffOn ℝ 1 V U → ContDiff ℝ 1 η → HasCompactSupport η → tsupport η ⊆ U → (∀ x, 0 ≤ η x) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) * ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := by
  intro n ℓ lam Lam A U V η c hlam hcoer hbdd hU hV hη hηc hηU hη0 hweak
  -- the test function `ζ = η² (V - c)` is admissible
  obtain ⟨hζ1, hζc, hζU, hζd⟩ :=
    Submission.dohr_eb_sch_cacc_test_function n ℓ U V η c hU hV hη hηc hηU
  have h0 := hweak _ hζ1 hζc hζU
  -- continuity of the ingredients
  have hDVc : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  have hVc : ContinuousOn V U := hV.continuousOn
  have hDη : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDζ : Continuous (fderiv ℝ (fun x => η x ^ 2 • (V x - c))) :=
    hζ1.continuous_fderiv one_ne_zero
  -- the three integrands
  set h : Rn n → ℝ := fun x => A (fderiv ℝ V x) (fderiv ℝ (fun x => η x ^ 2 • (V x - c)) x)
    with hh
  set g1 : Rn n → ℝ := fun x => η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2 with hg1
  set g3 : Rn n → ℝ := fun x => ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 with hg3
  have hsupp_h : Function.support h ⊆ tsupport (fun x => η x ^ 2 • (V x - c)) := by
    intro x hx
    by_contra hxs
    apply hx
    simp only [hh, fderiv_of_notMem_tsupport ℝ hxs, map_zero]
  have hsupp_g1 : Function.support g1 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg1, image_eq_zero_of_notMem_tsupport hxs]
  have hsupp_g3 : Function.support g3 ⊆ tsupport η := by
    intro x hx
    by_contra hxs
    apply hx
    simp [hg3, fderiv_of_notMem_tsupport ℝ hxs]
  -- continuous on `U` with `tsupport ⊆ U`, hence continuous with compact support
  have hcont_h : Continuous h := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_h (isClosed_tsupport _)).trans hζU)
    exact (A.continuous.comp_continuousOn hDVc).clm_apply hDζ.continuousOn
  have hcont_g1 : Continuous g1 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g1 (isClosed_tsupport _)).trans hηU)
    exact (hη.continuous.pow 2).continuousOn.mul (hDVc.norm.pow 2)
  have hcont_g3 : Continuous g3 := by
    refine ContinuousOn.continuous_of_tsupport_subset ?_ hU
      ((closure_minimal hsupp_g3 (isClosed_tsupport _)).trans hηU)
    exact ((hVc.sub continuousOn_const).norm.pow 2).mul (hDη.norm.pow 2).continuousOn
  have hint_h : Integrable h := hcont_h.integrable_of_hasCompactSupport (hζc.mono' hsupp_h)
  have hint_g1 : Integrable g1 := hcont_g1.integrable_of_hasCompactSupport (hηc.mono' hsupp_g1)
  have hint_g3 : Integrable g3 := hcont_g3.integrable_of_hasCompactSupport (hηc.mono' hsupp_g3)
  -- pointwise lower bound: Legendre condition, bound on `A`, and Young's inequality
  have hpt : ∀ x, lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x ≤ h x := by
    intro x
    have hid : h x = η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) +
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      simp only [hh, hζd x, map_add, map_smul, smul_eq_mul]
    rw [hid]
    have hc := hcoer (fderiv ℝ V x)
    have hb := hbdd (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c))
    rw [ContinuousLinearMap.norm_smulRight_apply] at hb
    have hb' := (abs_le.mp hb).1
    set a := η x * ‖fderiv ℝ V x‖ with ha
    set b := ‖V x - c‖ * ‖fderiv ℝ η x‖ with hb_def
    have e1 : lam * a ^ 2 ≤ η x ^ 2 * A (fderiv ℝ V x) (fderiv ℝ V x) := by
      rw [ha, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg (η x))]
    have e2 : -(2 * Lam * (a * b)) ≤
        2 * η x * A (fderiv ℝ V x) ((fderiv ℝ η x).smulRight (V x - c)) := by
      have h2η : 0 ≤ 2 * η x := by linarith [hη0 x]
      have := mul_le_mul_of_nonneg_left hb' h2η
      rw [ha, hb_def]
      linarith [this]
    have e3 : 2 * Lam * (a * b) ≤ lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 := by
      have key : lam / 2 * a ^ 2 + 2 * Lam ^ 2 / lam * b ^ 2 - 2 * Lam * (a * b) =
          (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * a - 2 * Lam * b) ^ 2 / (2 * lam) := by positivity
      linarith
    have hg1x : g1 x = a ^ 2 := by rw [hg1, ha, mul_pow]
    have hg3x : g3 x = b ^ 2 := by rw [hg3, hb_def, mul_pow]
    rw [hg1x, hg3x]
    linarith
  -- integrate (`∫ h = 0`) and absorb
  have hint_lhs : Integrable (fun x => lam / 2 * g1 x - 2 * Lam ^ 2 / lam * g3 x) :=
    (hint_g1.const_mul _).sub (hint_g3.const_mul _)
  have hmono := integral_mono hint_lhs hint_h hpt
  rw [h0, integral_sub (hint_g1.const_mul _) (hint_g3.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have key : ∫ x, g1 x ≤ 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by
    have h2 : lam / 2 * ∫ x, g1 x ≤ 2 * Lam ^ 2 / lam * ∫ x, g3 x := by linarith
    have hlam2 : 0 < lam / 2 := by positivity
    calc ∫ x, g1 x = (lam / 2)⁻¹ * (lam / 2 * ∫ x, g1 x) := by field_simp
      _ ≤ (lam / 2)⁻¹ * (2 * Lam ^ 2 / lam * ∫ x, g3 x) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hlam2.le)
      _ = 4 * Lam ^ 2 / lam ^ 2 * ∫ x, g3 x := by field_simp; ring
  -- pass to lower integrals
  have hg1n : 0 ≤ᵐ[volume] g1 := ae_of_all _ (fun x => by positivity)
  have hg3n : 0 ≤ᵐ[volume] g3 := ae_of_all _ (fun x => by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_g1 hg1n,
    ← ofReal_integral_eq_lintegral_ofReal hint_g3 hg3n, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal key
/-- Caccioppoli inequality for constant-coefficient Legendre systems: if `V` is `C¹` on
`B̆_{2ρ}(y)` and `∫ A[DV][Dζ] = 0` for every `ζ ∈ C¹_c(B̆_{2ρ}(y); ℝ^ℓ)`, then
`∫_{B̆_ρ(y)} |DV|² ≤ C ρ⁻² ∫_{B̆_{2ρ}(y)} |V − c|²` in `[0, ∞]`, with `C = C(λ, Λ)`.
Take the cutoff `η` of `dohr_eb_sch_cacc_exists_cutoff` (`‖Dη‖ ≤ K/ρ`), apply
`dohr_eb_sch_cacc_energy_estimate` with `U = B̆_{2ρ}(y)`, and put `C = (4Λ²/λ²) K²`. -/
theorem dohr_eb_sch_caccioppoli_const_coeff : ∀ (n ℓ : ℕ) (lam Lam : ℝ), 0 < lam → ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (y : Rn n) (ρ : ℝ) (c : Rn ℓ), (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → 0 < ρ → ContDiffOn ℝ 1 V (ball y (2 * ρ)) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball y (2 * ρ) → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
  intro n ℓ lam Lam hlam
  obtain ⟨K, hK0, hcut⟩ := Submission.dohr_eb_sch_cacc_exists_cutoff
  refine ⟨4 * Lam ^ 2 / lam ^ 2 * K ^ 2, by positivity, ?_⟩
  intro A V y ρ c hleg hbd hρ hV hweak
  obtain ⟨η, hη, hη01, hη1, hηc, hηU, hDη⟩ := hcut n y ρ hρ
  have hen := Submission.dohr_eb_sch_cacc_energy_estimate n ℓ lam Lam A (ball y (2 * ρ)) V η c
    hlam hleg hbd isOpen_ball hV hη hηc hηU (fun x => (hη01 x).1) hweak
  -- `η = 1` on `B̆_ρ(y)`
  have hL : ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤
      ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := by
    calc ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2
        = ∫⁻ x in ball y ρ, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_ball fun x hx => ?_
          rw [hη1 x hx, one_pow, one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ ∫⁻ x, ENNReal.ofReal (η x ^ 2 * ‖fderiv ℝ V x‖ ^ 2) := setLIntegral_le_lintegral _ _
  -- `‖Dη‖ ≤ K/ρ`, and `Dη = 0` off `tsupport η ⊆ B̆_{2ρ}(y)`
  have hR : ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) ≤
      ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
    calc ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2)
        ≤ ∫⁻ x, (ball y (2 * ρ)).indicator
            (fun x => ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ‖V x - c‖ₑ ^ 2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ ball y (2 * ρ)
          · rw [indicator_of_mem hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
              ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            calc ‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2 ≤ ‖V x - c‖ ^ 2 * (K / ρ) ^ 2 := by
                  gcongr
                  exact hDη x
              _ = K ^ 2 / ρ ^ 2 * ‖V x - c‖ ^ 2 := by ring
          · have hx' : x ∉ tsupport η := fun h => hx (hηU h)
            rw [fderiv_of_notMem_tsupport ℝ hx', norm_zero]
            simp
      _ = ∫⁻ x in ball y (2 * ρ), ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ‖V x - c‖ₑ ^ 2 :=
          lintegral_indicator measurableSet_ball _
      _ = ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc ∫⁻ x in ball y ρ, ‖fderiv ℝ V x‖ₑ ^ 2
      ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) *
          ∫⁻ x, ENNReal.ofReal (‖V x - c‖ ^ 2 * ‖fderiv ℝ η x‖ ^ 2) := hL.trans hen
    _ ≤ ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2) *
          (ENNReal.ofReal (K ^ 2 / ρ ^ 2) * ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (4 * Lam ^ 2 / lam ^ 2 * K ^ 2 / ρ ^ 2) *
          ∫⁻ x in ball y (2 * ρ), ‖V x - c‖ₑ ^ 2 := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_div_assoc']
/-- Interpolation bound for the derivative (step 3 of `dohr_eb_difference_quotient_limit`): if `h`
is differentiable on `B_{2r}(x)`, `Dh` is `α`-Hölder there with constant `L ≥ 0` and `‖h‖ ≤ S` on
`B_{2r}(x)`, then `‖Dh(y)‖ ≤ 2S/t + L t^α` for all `y ∈ B_r(x)` and `0 < t ≤ r`.
For `v ≠ 0` put `u = (t/‖v‖) v` and `z = y + u`; the mean value inequality on `[y, z] ⊆ B_{2r}(x)`
with the fixed map `Dh(y)` gives `‖h(z) − h(y) − Dh(y)u‖ ≤ L t^α · t`, so `‖Dh(y)u‖ ≤ 2S + L t^α t`,
and rescaling by `‖v‖/t` gives `‖Dh(y)v‖ ≤ (2S/t + L t^α)‖v‖`. -/
theorem dohr_eb_dql_interpolation_fderiv_bound : ∀ (n ℓ : ℕ) (h : Rn n → Rn ℓ) (x : Rn n) (r t α L S : ℝ), 0 < t → t ≤ r → 0 < α → 0 ≤ L → (∀ y ∈ closedBall x (2 * r), DifferentiableAt ℝ h y) → (∀ y ∈ closedBall x (2 * r), ∀ y' ∈ closedBall x (2 * r), ‖fderiv ℝ h y - fderiv ℝ h y'‖ ≤ L * ‖y - y'‖ ^ α) → (∀ y ∈ closedBall x (2 * r), ‖h y‖ ≤ S) → ∀ y ∈ closedBall x r, ‖fderiv ℝ h y‖ ≤ 2 * S / t + L * t ^ α := by
  intro n ℓ h x r t α L S ht htr hα hL hdiff hhol hS y hy
  -- Step 1: `S ≥ 0`, the bound is nonnegative, and it suffices to bound `‖Dh(y)v‖` for `v ≠ 0`.
  have hr : 0 < r := ht.trans_le htr
  have hxB : x ∈ closedBall x (2 * r) := mem_closedBall_self (by linarith)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hxB)
  have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
  have hbound0 : 0 ≤ 2 * S / t + L * t ^ α := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hbound0 (fun v => ?_)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  -- Step 2: the test point `z = y + u`, `u = (t/‖v‖) v`, and the segment `[y, z]`.
  set c : ℝ := t / ‖v‖ with hc
  have hcpos : 0 < c := div_pos ht hvpos
  set u : Rn n := c • v with hu
  have hunorm : ‖u‖ = t := by
    rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc, div_mul_cancel₀ _ hvpos.ne']
  set z := y + u with hz
  have hzy : z - y = u := by rw [hz]; abel
  have hzB : z ∈ closedBall x (2 * r) := by
    rw [mem_closedBall] at hy ⊢
    calc dist z x = ‖(y - x) + u‖ := by rw [dist_eq_norm]; congr 1; rw [hz]; abel
      _ ≤ ‖y - x‖ + ‖u‖ := norm_add_le _ _
      _ ≤ r + t := by rw [← dist_eq_norm, hunorm]; linarith
      _ ≤ 2 * r := by linarith
  have hseg : segment ℝ y z ⊆ closedBall x (2 * r) :=
    (convex_closedBall x (2 * r)).segment_subset hyB hzB
  have hseg' : segment ℝ y z ⊆ closedBall y t := by
    refine (convex_closedBall y t).segment_subset (mem_closedBall_self ht.le) ?_
    rw [mem_closedBall, dist_eq_norm, hzy, hunorm]
  -- Steps 3–4: `‖Dh(w) − Dh(y)‖ ≤ L t^α` on `[y, z]`, and the mean value inequality.
  have hmvt : ‖h z - h y - fderiv ℝ h y (z - y)‖ ≤ (L * t ^ α) * ‖z - y‖ := by
    refine (convex_segment y z).norm_image_sub_le_of_norm_fderiv_le'
      (fun w hw => hdiff w (hseg hw)) (fun w hw => ?_) (left_mem_segment ℝ y z)
      (right_mem_segment ℝ y z)
    have hwy : ‖w - y‖ ≤ t := by
      have := hseg' hw
      rwa [mem_closedBall, dist_eq_norm] at this
    calc ‖fderiv ℝ h w - fderiv ℝ h y‖ ≤ L * ‖w - y‖ ^ α := hhol w (hseg hw) y hyB
      _ ≤ L * t ^ α := by
        gcongr
  rw [hzy, hunorm] at hmvt
  -- Step 5: `‖Dh(y)u‖ ≤ 2S + L t^α t`.
  have hhzy : ‖h z - h y‖ ≤ 2 * S := by
    calc ‖h z - h y‖ ≤ ‖h z‖ + ‖h y‖ := norm_sub_le _ _
      _ ≤ S + S := add_le_add (hS z hzB) (hS y hyB)
      _ = 2 * S := by ring
  have hfu : ‖fderiv ℝ h y u‖ ≤ L * t ^ α * t + 2 * S := by
    have : fderiv ℝ h y u = (h z - h y) - (h z - h y - fderiv ℝ h y u) := by abel
    rw [this]
    calc ‖(h z - h y) - (h z - h y - fderiv ℝ h y u)‖
        ≤ ‖h z - h y‖ + ‖h z - h y - fderiv ℝ h y u‖ := norm_sub_le _ _
      _ ≤ 2 * S + L * t ^ α * t := add_le_add hhzy hmvt
      _ = L * t ^ α * t + 2 * S := by ring
  -- Step 6: rescale by `c = t/‖v‖`.
  have hfu' : ‖fderiv ℝ h y u‖ = c * ‖fderiv ℝ h y v‖ := by
    rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  rw [hfu'] at hfu
  have key : ‖fderiv ℝ h y v‖ ≤ (L * t ^ α * t + 2 * S) / c := by
    rw [le_div_iff₀ hcpos]; linarith
  calc ‖fderiv ℝ h y v‖ ≤ (L * t ^ α * t + 2 * S) / c := key
    _ = (2 * S / t + L * t ^ α) * ‖v‖ := by
      rw [hc]; field_simp; ring
/-- **Simon Ch. 5, proof of Theorem 7.1 (elliptic bootstrap): `C^{1,α}` bounds pass to limits.**
Let `B = B̆_ρ(x₀)` and let `F_i → G` uniformly on every compact `K ⊆ B` along a filter `l ≠ ⊥`.
If eventually in `l` each `F_i` is differentiable on `B` with `‖DF_i‖ ≤ M` and
`‖DF_i(x) − DF_i(y)‖ ≤ M ‖x − y‖^α` on `B` (`α > 0`), then `G` is `C¹` on `B` with the same bounds.
Proof: for `x ∈ B` choose `r > 0` with `B_{2r}(x) ⊆ B`.  Given `η > 0`, pick `t ∈ (0, r]` with
`2M t^α < η/2`; once `‖G − F_i‖ < ηt/8` on `B_{2r}(x)`, the interpolation inequality
(`dohr_eb_dql_interpolation_fderiv_bound`) applied to `F_i − F_j` (Hölder constant `2M`, sup bound
`ηt/4`) gives `‖DF_i − DF_j‖ ≤ η/2 + 2M t^α < η` on `B_r(x)`.  So `DF_i` is uniformly Cauchy on
`B_r(x)` and, `L(ℝⁿ, ℝ^ℓ)` being complete, converges uniformly there to `V := lim DF_i`.  The limit
`V` inherits the bound `M` and the Hölder constant `M`, hence is continuous on `B`, and the theorem
on uniform limits of derivatives gives `DG = V` on `B`; thus `G` is `C¹` on `B`. -/
theorem dohr_eb_dql_c1Holder_of_tendstoUniformlyOn : ∀ (n ℓ : ℕ) (ι : Type) (l : Filter ι), l.NeBot → ∀ (F : ι → Rn n → Rn ℓ) (G : Rn n → Rn ℓ) (x₀ : Rn n) (ρ α M : ℝ), 0 < α → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, DifferentiableAt ℝ (F i) x) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x‖ ≤ M) → (∀ᶠ i in l, ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (F i) x - fderiv ℝ (F i) y‖ ≤ M * ‖x - y‖ ^ α) → (∀ K : Set (Rn n), IsCompact K → K ⊆ ball x₀ ρ → TendstoUniformlyOn F G l K) → ContDiffOn ℝ 1 G (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ G x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ ι l hl F G x₀ ρ α M hα hD hB hH hU
  have := hl
  -- The good indices: eventually all three hypotheses hold at once.
  have hE := hD.and (hB.and hH)
  -- The candidate derivative of `G`: the (chosen) pointwise limit of the `DF_i`.
  set V : Rn n → (Rn n →L[ℝ] Rn ℓ) := fun y => limUnder l (fun i => fderiv ℝ (F i) y)
  -- Step 1: radii with `B_{2r}(x) ⊆ B`, and `M ≥ 0`.
  have hrad : ∀ x ∈ ball x₀ ρ, ∃ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ := by
    intro x hx
    rw [mem_ball] at hx
    refine ⟨(ρ - dist x x₀) / 4, by linarith, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z x₀ ≤ dist z x + dist x x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  have hM : ∀ x ∈ ball x₀ ρ, 0 ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := hB.exists
    exact (norm_nonneg _).trans (hi x hx)
  -- Steps 2–3: on `B_r(x)` the `DF_i` are uniformly Cauchy, hence converge uniformly to `V`.
  have hconv : ∀ x ∈ ball x₀ ρ, ∀ r > 0, closedBall x (2 * r) ⊆ ball x₀ ρ →
      TendstoUniformlyOn (fun i => fderiv ℝ (F i)) V l (closedBall x r) := by
    intro x hx r hr hsub
    have hM0 := hM x hx
    have hUC : UniformCauchySeqOn (fun i => fderiv ℝ (F i)) l (closedBall x r) := by
      intro u hu
      obtain ⟨η, hη, hηu⟩ := Metric.mem_uniformity_dist.1 hu
      -- (a) a scale `t ∈ (0, r]` with `2M t^α < η/2`.
      have ht_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * M * t ^ α < η / 2 := by
        have hc : Tendsto (fun t : ℝ => 2 * M * t ^ α) (𝓝 0) (𝓝 (2 * M * (0 : ℝ) ^ α)) :=
          ((continuousAt_id.rpow_const (Or.inr hα.le)).tendsto).const_mul _
        rw [Real.zero_rpow hα.ne', mul_zero] at hc
        exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds (by linarith)))
      have hIoc : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioc 0 r := Ioc_mem_nhdsGT hr
      obtain ⟨t, ht1, ht2⟩ := (ht_ev.and hIoc).exists
      have htpos : 0 < t := ht2.1
      have htr : t ≤ r := ht2.2
      -- (b) eventually `‖G − F_i‖ < ηt/8` on the compact set `B_{2r}(x) ⊆ B`.
      have hTU := hU (closedBall x (2 * r)) (isCompact_closedBall x _) hsub
      rw [Metric.tendstoUniformlyOn_iff] at hTU
      have hP := hE.and (hTU (η * t / 8) (by positivity))
      filter_upwards [hP.prod_mk hP] with ij hij y hy
      obtain ⟨⟨hDi, hBi, hHi⟩, hGi⟩ := hij.1
      obtain ⟨⟨hDj, hBj, hHj⟩, hGj⟩ := hij.2
      apply hηu
      rw [dist_eq_norm]
      have hyB : y ∈ closedBall x (2 * r) := closedBall_subset_closedBall (by linarith) hy
      -- (c) `h = F_i − F_j` has Hölder constant `2M` and sup bound `ηt/4` on `B_{2r}(x)`.
      set h : Rn n → Rn ℓ := fun z => F ij.1 z - F ij.2 z
      have hdh : ∀ z ∈ closedBall x (2 * r), DifferentiableAt ℝ h z := fun z hz =>
        (hDi z (hsub hz)).sub (hDj z (hsub hz))
      have hfd : ∀ z ∈ closedBall x (2 * r),
          fderiv ℝ h z = fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z := fun z hz =>
        fderiv_sub (hDi z (hsub hz)) (hDj z (hsub hz))
      -- (d) the interpolation inequality on `B_r(x)`.
      have hbd := Submission.dohr_eb_dql_interpolation_fderiv_bound n ℓ h x r t α (2 * M)
        (η * t / 4) htpos htr hα (by linarith) hdh
        (fun z hz z' hz' => by
          rw [hfd z hz, hfd z' hz']
          calc ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.2) z -
                (fderiv ℝ (F ij.1) z' - fderiv ℝ (F ij.2) z')‖
              = ‖(fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z') -
                  (fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z')‖ := by congr 1; abel
            _ ≤ ‖fderiv ℝ (F ij.1) z - fderiv ℝ (F ij.1) z'‖ +
                  ‖fderiv ℝ (F ij.2) z - fderiv ℝ (F ij.2) z'‖ := norm_sub_le _ _
            _ ≤ M * ‖z - z'‖ ^ α + M * ‖z - z'‖ ^ α :=
                add_le_add (hHi z (hsub hz) z' (hsub hz')) (hHj z (hsub hz) z' (hsub hz'))
            _ = 2 * M * ‖z - z'‖ ^ α := by ring)
        (fun z hz => by
          have h1 := hGi z hz
          have h2 := hGj z hz
          rw [dist_eq_norm] at h1 h2
          calc ‖h z‖ = ‖(G z - F ij.2 z) - (G z - F ij.1 z)‖ := by
                show ‖F ij.1 z - F ij.2 z‖ = _; congr 1; abel
            _ ≤ ‖G z - F ij.2 z‖ + ‖G z - F ij.1 z‖ := norm_sub_le _ _
            _ ≤ η * t / 4 := by linarith)
        y hy
      rw [hfd y hyB] at hbd
      calc ‖fderiv ℝ (F ij.1) y - fderiv ℝ (F ij.2) y‖
          ≤ 2 * (η * t / 4) / t + 2 * M * t ^ α := hbd
        _ = η / 2 + 2 * M * t ^ α := by field_simp; ring
        _ < η := by linarith
    -- (e)/(3) completeness: pointwise limits exist, and the convergence is uniform.
    refine hUC.tendstoUniformlyOn_of_tendsto (fun y hy => ?_)
    obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 (hUC.cauchy_map hy)
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  have hpt : ∀ y ∈ ball x₀ ρ, Tendsto (fun i => fderiv ℝ (F i) y) l (𝓝 (V y)) := by
    intro y hy
    obtain ⟨r, hr, hsub⟩ := hrad y hy
    exact (hconv y hy r hr hsub).tendsto_at (mem_closedBall_self hr.le)
  -- Step 5: the uniform-limit theorem for derivatives gives `DG = V` on `B`.
  have hG : ∀ x ∈ ball x₀ ρ, HasFDerivAt G (V x) x := by
    intro x hx
    obtain ⟨r, hr, hsub⟩ := hrad x hx
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F)
      (f' := fun i => fderiv ℝ (F i)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.1 (hconv x hx r hr hsub)).mono_right
        (le_principal_iff.2 (closedBall_mem_nhds x hr))
    · filter_upwards [hD.prod_mk (isOpen_ball.mem_nhds hx)] with p hp
      exact (hp.1 p.2 hp.2).hasFDerivAt
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hU {y} isCompact_singleton (singleton_subset_iff.2 hy)).tendsto_at rfl
  have hfG : ∀ x ∈ ball x₀ ρ, fderiv ℝ G x = V x := fun x hx => (hG x hx).fderiv
  -- Step 4: `V` inherits both bounds, so it is continuous on `B`.
  have hVb : ∀ x ∈ ball x₀ ρ, ‖V x‖ ≤ M := fun x hx =>
    le_of_tendsto (hpt x hx).norm (hB.mono fun i hi => hi x hx)
  have hVh : ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖V x - V y‖ ≤ M * ‖x - y‖ ^ α := fun x hx y hy =>
    le_of_tendsto ((hpt x hx).sub (hpt y hy)).norm (hH.mono fun i hi => hi x hx y hy)
  have hVc : ContinuousOn V (ball x₀ ρ) := by
    intro y hy
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun z => M * ‖z - y‖ ^ α) (𝓝 y) (𝓝 (M * ‖y - y‖ ^ α)) :=
      (((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
        (Or.inr hα.le)).tendsto.const_mul M
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hVh z hz y hy
  -- Step 6: conclusion.
  refine ⟨?_, fun x hx => by rw [hfG x hx]; exact hVb x hx, fun x hx y hy => by
    rw [hfG x hx, hfG y hy]; exact hVh x hx y hy⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun x hx => (hG x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hVc.congr hfG
/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (pp. 127–128), Schauder step by difference
quotients (Giaquinta–Martinazzi, §4.3, with uniform `C^{1,α}` bounds in place of `W^{1,2}` bounds):
let `f` be `C¹` on `B' = B̆_{ρ+δ|e|}(x₀)` and let the difference quotients
`g_d = d⁻¹ (f(· + d e) - f)`, `0 < |d| < δ`, satisfy `‖Dg_d‖ ≤ M` and `[Dg_d]_α ≤ M` on
`B = B̆_ρ(x₀)`.  Then `D_e f = Df(·) e` is `C¹` on `B`, `‖D(D_e f)‖ ≤ M` and `[D(D_e f)]_α ≤ M`.
For `|d| < δ` the shift `x + d e` of `x ∈ B` stays in `B'`, so `Dg_d = d⁻¹ (Df(· + d e) - Df)` on
`B` by the chain rule.  As `d → 0`, `g_d → D_e f` uniformly on compact subsets of `B`
(`dohr_eb_dql_diffQuot_tendstoUniformlyOn`), and uniform `C^{1,α}` bounds pass to such limits
(`dohr_eb_dql_c1Holder_of_tendstoUniformlyOn`). -/
theorem dohr_eb_difference_quotient_limit : ∀ (n ℓ : ℕ) (α : ℝ) (f : Rn n → Rn ℓ) (x₀ e : Rn n) (ρ δ M : ℝ), 0 < α → α ≤ 1 → 0 < δ → ContDiffOn ℝ 1 f (ball x₀ (ρ + δ * ‖e‖)) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x)‖ ≤ M) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x) - d⁻¹ • (fderiv ℝ f (y + d • e) - fderiv ℝ f y)‖ ≤ M * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 (fun x => fderiv ℝ f x e) (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x - fderiv ℝ (fun z => fderiv ℝ f z e) y‖ ≤ M * ‖x - y‖ ^ α := by
  intro n ℓ α f x₀ e ρ δ M hα _hα1 hδ hf hbd hhol
  -- `B = B̆_ρ(x₀) ⊆ B' = B̆_{ρ+δ|e|}(x₀)`, and `f` is differentiable on the open set `B'`.
  have hB'open : IsOpen (ball x₀ (ρ + δ * ‖e‖)) := isOpen_ball
  have hBB' : ball x₀ ρ ⊆ ball x₀ (ρ + δ * ‖e‖) :=
    ball_subset_ball (le_add_of_nonneg_right (mul_nonneg hδ.le (norm_nonneg e)))
  have hdiff : ∀ z ∈ ball x₀ (ρ + δ * ‖e‖), DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (hB'open.mem_nhds hz)
  -- For `|d| < δ` and `x ∈ B`: `|x + d e - x₀| ≤ |x - x₀| + |d| |e| < ρ + δ |e|`.
  have hshift : ∀ d : ℝ, |d| < δ → ∀ x ∈ ball x₀ ρ, x + d • e ∈ ball x₀ (ρ + δ * ‖e‖) := by
    intro d hd x hx
    rw [mem_ball] at hx ⊢
    have h1 : dist (x + d • e) x₀ ≤ dist x x₀ + ‖d • e‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖x + d • e - x₀‖ = ‖(x - x₀) + d • e‖ := by congr 1; abel
        _ ≤ ‖x - x₀‖ + ‖d • e‖ := norm_add_le _ _
    have h2 : ‖d • e‖ ≤ δ * ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hd.le (norm_nonneg e)
    linarith
  -- Step 1 (chain rule): `Dg_d(x) = d⁻¹ (Df(x + d e) - Df(x))` for `|d| < δ` and `x ∈ B`.
  have hFderiv : ∀ d : ℝ, |d| < δ → ∀ x ∈ ball x₀ ρ,
      HasFDerivAt (fun y => d⁻¹ • (f (y + d • e) - f y))
        (d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x)) x := by
    intro d hd x hx
    have h1 : HasFDerivAt (fun y => f (y + d • e)) (fderiv ℝ f (x + d • e)) x :=
      (hasFDerivAt_comp_add_right (d • e)).2 (hdiff _ (hshift d hd x hx)).hasFDerivAt
    have h2 : HasFDerivAt f (fderiv ℝ f x) x := (hdiff x (hBB' hx)).hasFDerivAt
    exact (h1.sub h2).const_smul d⁻¹
  -- The admissible `d` (`d ≠ 0`, `|d| < δ`) form a set of the punctured filter `𝓝[≠] 0`.
  have hev : ∀ᶠ d in 𝓝[≠] (0 : ℝ), d ≠ 0 ∧ |d| < δ := by
    have h1 : ∀ᶠ d in 𝓝[≠] (0 : ℝ), d ≠ 0 := self_mem_nhdsWithin
    have h2 : ∀ᶠ d in 𝓝[≠] (0 : ℝ), |d| < δ := by
      have : ∀ᶠ d in 𝓝 (0 : ℝ), |d| < δ := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with d hd
        simpa [Real.dist_eq] using hd
      exact nhdsWithin_le_nhds this
    exact h1.and h2
  -- Steps 2–7: `g_d → D_e f` uniformly on compact `K ⊆ B ⊆ B'` along `𝓝[≠] 0`, and the uniform
  -- bounds `‖Dg_d‖ ≤ M`, `[Dg_d]_α ≤ M` pass to the limit.
  exact Submission.dohr_eb_dql_c1Holder_of_tendstoUniformlyOn n ℓ ℝ (𝓝[≠] (0 : ℝ)) inferInstance
    (fun d y => d⁻¹ • (f (y + d • e) - f y)) (fun x => fderiv ℝ f x e) x₀ ρ α M hα
    (hev.mono fun d hd x hx => (hFderiv d hd.2 x hx).differentiableAt)
    (hev.mono fun d hd x hx => by
      rw [(hFderiv d hd.2 x hx).fderiv]; exact hbd d hd.1 hd.2 x hx)
    (hev.mono fun d hd x hx y hy => by
      rw [(hFderiv d hd.2 x hx).fderiv, (hFderiv d hd.2 y hy).fderiv]
      exact hhol d hd.1 hd.2 x hx y hy)
    (fun K hK hKB => Submission.dohr_eb_dql_diffQuot_tendstoUniformlyOn n ℓ f _ K e hB'open hf
      hK (hKB.trans hBB'))
/-- Columns of an operator-valued map (step 3, "Components", of the proof that `f` is
`C^{m+1,α}` iff `Df` is `C^{m,α}`, in the elliptic bootstrap for Simon 7.1): if
`g : ℝⁿ → L(ℝⁿ, E)` is `C^m` on the open set `U` and `g_k = g(·) e_k`, then on `U` the differences
of `D^m g_k` are bounded by those of `D^m g`, and those of `D^m g` by the sum over `k` of those of
`D^m g_k`.  Indeed `D^m g_k = ev_k ∘ D^m g` and `D^m g = ∑_k ι_k ∘ D^m g_k`, where the evaluation
`ev_k T = T e_k` and the reconstruction `ι_k w = (h ↦ h_k • w)` have norm at most one. -/
theorem dohr_eb_hsif_iteratedFDeriv_column_bounds : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (g : Rn n → (Rn n →L[ℝ] E)) (U : Set (Rn n)), IsOpen U → ContDiffOn ℝ m g U → ∀ x ∈ U, ∀ y ∈ U, (∀ k : Fin n, ‖iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) y‖ ≤ ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖) ∧ ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ ≤ ∑ k : Fin n, ‖iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) y‖ := by
  intro n E _ _ m g U hU hg x hx y hy
  -- Step 1: the evaluation maps `ev k : T ↦ T e_k` have norm at most one.
  let ev : Fin n → (Rn n →L[ℝ] E) →L[ℝ] E := fun k =>
    ContinuousLinearMap.apply ℝ E (EuclideanSpace.single k (1 : ℝ))
  have hev : ∀ k, ‖ev k‖ ≤ 1 := fun k =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => by
      simpa [ev] using T.le_opNorm (EuclideanSpace.single k (1 : ℝ))
  -- Step 2: the reconstruction maps `ι k : w ↦ (h ↦ h_k • w)` have norm at most one.
  let ι : Fin n → E →L[ℝ] (Rn n →L[ℝ] E) := fun k =>
    ContinuousLinearMap.smulRightL ℝ (Rn n) E (EuclideanSpace.proj k)
  have hι : ∀ k, ‖ι k‖ ≤ 1 := fun k =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      have hproj : ‖(EuclideanSpace.proj k : StrongDual ℝ (Rn n))‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
          simpa using PiLp.norm_apply_le h k
      show ‖(EuclideanSpace.proj k : StrongDual ℝ (Rn n)).smulRight w‖ ≤ 1 * ‖w‖
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right hproj (norm_nonneg w)
  -- Step 3: `L ∘ A - L ∘ B = L ∘ (A - B)` and `‖L ∘ A‖ ≤ ‖A‖` when `‖L‖ ≤ 1`.
  have hcomp : ∀ {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
      [NormedSpace ℝ G] (L : F →L[ℝ] G), ‖L‖ ≤ 1 →
      ∀ A B : ContinuousMultilinearMap ℝ (fun _ : Fin m => Rn n) F,
        ‖L.compContinuousMultilinearMap A - L.compContinuousMultilinearMap B‖ ≤ ‖A - B‖ := by
    intro F G _ _ _ _ L hL A B
    have : L.compContinuousMultilinearMap A - L.compContinuousMultilinearMap B =
        L.compContinuousMultilinearMap (A - B) := by
      ext v
      simp
    rw [this]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hL)
  -- Step 4: `g` and its columns are `C^m` at every point of the open set `U`.
  have hgat : ∀ z ∈ U, ContDiffAt ℝ m g z := fun z hz => hg.contDiffAt (hU.mem_nhds hz)
  have hcolat : ∀ k, ∀ z ∈ U,
      ContDiffAt ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) z := fun k z hz =>
    (hgat z hz).continuousLinearMap_comp (ev k)
  -- Step 5: the column formula `D^m g_k(z) = ev k ∘ D^m g(z)`.
  have hcol : ∀ k, ∀ z ∈ U,
      iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) z =
        (ev k).compContinuousMultilinearMap (iteratedFDeriv ℝ m g z) := fun k z hz =>
    (ev k).iteratedFDeriv_comp_left (hgat z hz) le_rfl
  -- Step 7: the reconstruction `g = ∑ k, ι k ∘ g_k`.
  have hrec : g = fun z => ∑ k, ι k (g z (EuclideanSpace.single k (1 : ℝ))) := by
    funext z
    ext h
    have hh : ∑ k, h k • EuclideanSpace.single k (1 : ℝ) = h := by
      simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h
    conv_lhs => rw [← hh]
    simp [ι, map_sum, map_smul]
  -- Step 8: the sum formula `D^m g(z) = ∑ k, ι k ∘ D^m g_k(z)`.
  have hsum : ∀ z ∈ U, iteratedFDeriv ℝ m g z = ∑ k, (ι k).compContinuousMultilinearMap
      (iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) z) := by
    intro z hz
    calc iteratedFDeriv ℝ m g z
        = iteratedFDeriv ℝ m (fun z => ∑ k, ι k (g z (EuclideanSpace.single k (1 : ℝ)))) z :=
          congrArg (iteratedFDeriv ℝ m · z) hrec
      _ = ∑ k, iteratedFDeriv ℝ m (fun z => ι k (g z (EuclideanSpace.single k (1 : ℝ)))) z :=
          iteratedFDeriv_fun_sum_apply fun k _ => (hcolat k z hz).continuousLinearMap_comp (ι k)
      _ = ∑ k, (ι k).compContinuousMultilinearMap
            (iteratedFDeriv ℝ m (fun z => g z (EuclideanSpace.single k (1 : ℝ))) z) :=
          Finset.sum_congr rfl fun k _ => (ι k).iteratedFDeriv_comp_left (hcolat k z hz) le_rfl
  refine ⟨fun k => ?_, ?_⟩
  -- Step 6: bound (i).
  · rw [hcol k x hx, hcol k y hy]
    exact hcomp (ev k) (hev k) _ _
  -- Step 9: bound (ii).
  · rw [hsum x hx, hsum y hy, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hcomp (ι k) (hι k) _ _)

/-- **`C^{m+1,α}_loc` through first derivatives**: `u ∈ C^{m+1,α}_loc` iff `Du ∈ C^{m,α}_loc` iff
every `D_k u ∈ C^{m,α}_loc`, the bookkeeping of the Schauder bootstrap in the proof of Simon Ch. 5,
Theorem 7.1 (p. 128).  For `f : ℝⁿ → E` and open `U ⊆ ℝⁿ`, write
(A) `f` is `C^{m+1}` on `U` and `D^{m+1}f` is `α`-Hölder on each compact `K ⊆ U`;
(B) `f` is `C¹` on `U`, `Df` is `C^m` on `U` and `D^m(Df)` is `α`-Hölder on each compact `K ⊆ U`;
(C) `f` is `C¹` on `U` and every partial derivative `D_k f = Df(·) e_k` is `C^m` on `U` with
`D^m(D_k f)` `α`-Hölder on each compact `K ⊆ U`.
Then `(A ↔ B) ∧ (A ↔ C)`. -/
theorem dohr_eb_holder_succ_iff_fderiv : ∀ (n : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (α : ℝ) (f : Rn n → E) (U : Set (Rn n)), IsOpen U → (((ContDiffOn ℝ (m + 1 : ℕ) f U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔ (ContDiffOn ℝ 1 f U ∧ ContDiffOn ℝ m (fderiv ℝ f) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fderiv ℝ f) x - iteratedFDeriv ℝ m (fderiv ℝ f) y‖ ≤ C * ‖x - y‖ ^ α)) ∧ ((ContDiffOn ℝ (m + 1 : ℕ) f U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ (m + 1) f x - iteratedFDeriv ℝ (m + 1) f y‖ ≤ C * ‖x - y‖ ^ α) ↔ (ContDiffOn ℝ 1 f U ∧ ∀ k : Fin n, ContDiffOn ℝ m (fun x => fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) x - iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) y‖ ≤ C * ‖x - y‖ ^ α))) := by
  intro n E _ _ m α f U hU
  -- Steps 1–2, (A ↔ B): `D^{m+1}f = Ψ ∘ D^m(Df)` for a linear isometry `Ψ`, and on the open set
  -- `U`, `f ∈ C^{m+1}` iff `f ∈ C¹` and `Df ∈ C^m`.
  have hAB := Submission.dohr_eb_hsif_succ_iff_curry n E m α f U hU
  refine ⟨hAB, hAB.trans (and_congr_right fun _ => ?_)⟩
  -- Steps 3–4, (B ↔ C) once `f ∈ C¹(U)`: `Df ∈ C^m(U)` iff every column `D_k f ∈ C^m(U)`; on `U`,
  -- `‖Δ D^m(D_k f)‖ ≤ ‖Δ D^m(Df)‖ ≤ Σ_k ‖Δ D^m(D_k f)‖` (`Δ h = h(x) - h(y)`) transfers the Hölder
  -- constants: `C` for each `D_k f`, and `Σ_k C_k` for `Df`.
  have hcols := Submission.dohr_eb_hsif_contDiffOn_clm_iff_columns n E m (fderiv ℝ f) U
  have hbds := Submission.dohr_eb_hsif_iteratedFDeriv_column_bounds n E m (fderiv ℝ f) U hU
  constructor
  · rintro ⟨hm, hH⟩ k
    refine ⟨hcols.1 hm k, fun K hK hKU => ?_⟩
    obtain ⟨C, hC⟩ := hH K hK hKU
    exact ⟨C, fun x hx y hy => ((hbds hm x (hKU hx) y (hKU hy)).1 k).trans (hC x hx y hy)⟩
  · intro hk
    have hm : ContDiffOn ℝ m (fderiv ℝ f) U := hcols.2 fun k => (hk k).1
    refine ⟨hm, fun K hK hKU => ?_⟩
    choose C hC using fun k => (hk k).2 K hK hKU
    refine ⟨∑ k, C k, fun x hx y hy => ?_⟩
    calc _ ≤ ∑ k : Fin n,
          ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) x -
            iteratedFDeriv ℝ m (fun z => fderiv ℝ f z (EuclideanSpace.single k (1 : ℝ))) y‖ :=
          (hbds hm x (hKU hx) y (hKU hy)).2
      _ ≤ ∑ k : Fin n, C k * ‖x - y‖ ^ α := Finset.sum_le_sum fun k _ => hC k x hx y hy
      _ = (∑ k : Fin n, C k) * ‖x - y‖ ^ α := (Finset.sum_mul _ _ _).symm
/-- **Bilinear products preserve `C^{m,α}_loc`** (node `holder_bilinear` of the elliptic bootstrap
for Simon Ch. 5, Theorem 7.1).  Let `B : E₂ →L E₃ →L E₄` be continuous bilinear and let
`f : E₁ → E₂`, `g : E₁ → E₃` be `C^m` on the open set `U` with `D^m f`, `D^m g` `α`-Hölder on every
compact `K ⊆ U`.  Then `x ↦ B (f x) (g x)` is `C^m` on `U` and its `m`-th derivative is `α`-Hölder
on every compact `K ⊆ U`.  The evaluation `β (y, z) = B y z` is a bounded bilinear map, hence
smooth, so `D^m β` is `α`-Hölder on compacts (`dohr_eb_holder_of_contDiffOn_succ`).  The pair
`p = (f, g)` is `C^m` on `U` with `D^m p = (D^m f).prod (D^m g)`, whose norm is the max of the two
norms, so `D^m p` is `α`-Hölder on compacts.  The composition lemma `dohr_eb_holder_comp`, with
`V = univ` and the `C¹` outer map `β` (valid also for `m = 0`), applies to
`β ∘ p = fun x => B (f x) (g x)`. -/
theorem dohr_eb_holder_bilinear : ∀ (E₁ E₂ E₃ E₄ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] (m : ℕ) (α : ℝ) (B : E₂ →L[ℝ] E₃ →L[ℝ] E₄) (f : E₁ → E₂) (g : E₁ → E₃) (U : Set E₁), 0 < α → α ≤ 1 → IsOpen U → ContDiffOn ℝ m f U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m g U → (∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y‖ ≤ C * ‖x - y‖ ^ α) → ContDiffOn ℝ m (fun x => B (f x) (g x)) U ∧ ∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun x => B (f x) (g x)) x - iteratedFDeriv ℝ m (fun x => B (f x) (g x)) y‖ ≤ C * ‖x - y‖ ^ α := by
  intro E₁ E₂ E₃ E₄ _ _ _ _ _ _ _ _ m α B f g U hα hα1 hU hf hfH hg hgH
  -- Step 1: `β (y, z) = B y z` is a bounded bilinear map, hence `C^k` on `E₂ × E₃` for every `k`;
  -- as it is `C^{m+1}`, its `m`-th derivative is `α`-Hölder on compact sets.
  have hβ : ∀ k : WithTop ℕ∞, ContDiffOn ℝ k (fun q : E₂ × E₃ => B q.1 q.2) univ := fun _ =>
    B.isBoundedBilinearMap.contDiff.contDiffOn
  have hβH := Submission.dohr_eb_holder_of_contDiffOn_succ (E₂ × E₃) E₄ m α
    (fun q : E₂ × E₃ => B q.1 q.2) univ hα hα1 isOpen_univ (hβ _)
  -- Step 2: the pair `p = (f, g)` is `C^m` on `U`, and `D^m p = (D^m f).prod (D^m g)` has norm
  -- `max ‖D^m f‖ ‖D^m g‖`, so `D^m p` is `α`-Hölder on compact subsets of `U`.
  have hpH : ∀ K : Set E₁, IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ m (fun x => (f x, g x)) x - iteratedFDeriv ℝ m (fun x => (f x, g x)) y‖ ≤
        C * ‖x - y‖ ^ α := by
    intro K hK hKU
    obtain ⟨Cf, hCf⟩ := hfH K hK hKU
    obtain ⟨Cg, hCg⟩ := hgH K hK hKU
    have hD : ∀ x ∈ K, iteratedFDeriv ℝ m (fun x => (f x, g x)) x =
        (iteratedFDeriv ℝ m f x).prod (iteratedFDeriv ℝ m g x) := fun x hx =>
      iteratedFDeriv_prodMk (hf.contDiffAt (hU.mem_nhds (hKU hx)))
        (hg.contDiffAt (hU.mem_nhds (hKU hx))) le_rfl
    refine ⟨max Cf Cg, fun x hx y hy => ?_⟩
    have hxy : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    rw [hD x hx, hD y hy, ← ContinuousMultilinearMap.sub_prod_sub,
      ContinuousMultilinearMap.opNorm_prod]
    exact max_le ((hCf x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hxy))
      ((hCg x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hxy))
  -- Step 3: the composition lemma with inner map `p`, open sets `U` and `univ`, and the `C¹` outer
  -- map `β`; here `β ∘ p = fun x => B (f x) (g x)`.
  exact Submission.dohr_eb_holder_comp E₁ (E₂ × E₃) E₄ m α (fun x => (f x, g x))
    (fun q : E₂ × E₃ => B q.1 q.2) U univ hα hα1 hU isOpen_univ (mapsTo_univ _ _)
    (Or.inr (Or.inr (hβ _))) (hf.prodMk hg) hpH (hβ _) hβH
end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

namespace Submission

/-- **Simon Ch. 5, Theorem 7.1, proof (p. 127): translation invariance (fact (Inv)).**  For
`τ(x) = x − ξ`, the translate `V' = v(τ(M), θ(· + ξ))` is a rectifiable `n`-varifold in `τ(U)` with
`μ_{V'} = τ_# μ_V` and `spt V' = τ(spt V)`; if `V` has generalized mean curvature `H` in `U`, then
`V'` has generalized mean curvature `H(· + ξ)` in `τ(U)`.

`V'` and its structure fields come from `dohr_tv_exists_translate`, the weight from
`dohr_tv_weight_eq_map`, the tangent projections `p_{T_y V'} = p_{T_{y+ξ} V}` from
`dohr_tv_tangentProj_eq`, and the first variation from `dohr_tv_gmc_transfer`.  For the support,
`spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V)` (`dohr_tv_support_map_sub`), which is
`τ(U ∩ spt μ_V)` because `τ` is injective. -/
theorem dohr_translate_varifold : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ), ∃ V' : RectifiableVarifold n ℓ ((fun x => x - ξ) '' U), V'.carrier = (fun x => x - ξ) '' V.carrier ∧ (∀ y, V'.mult y = V.mult (y + ξ)) ∧ V'.weight = V.weight.map (fun x => x - ξ) ∧ V'.support = (fun x => x - ξ) '' V.support ∧ ∀ H : Amb n ℓ → Amb n ℓ, V.HasGeneralizedMeanCurvature H → V'.HasGeneralizedMeanCurvature (fun y => H (y + ξ)) := by
  intro n ℓ U V ξ
  -- Steps 1–2: the translate `V'` in `τ(U)` with carrier `τ(M)` and multiplicity `θ(· + ξ)`.
  obtain ⟨V', hc, hm⟩ := Submission.dohr_tv_exists_translate n ℓ U V ξ
  -- Step 3: `μ_{V'} = τ_# μ_V`.
  have hw := Submission.dohr_tv_weight_eq_map n ℓ U _ V V' ξ hc hm
  -- Step 5: `p_{T_y V'} = p_{T_{y+ξ} V}` for every `y`.
  have ht := Submission.dohr_tv_tangentProj_eq n ℓ U _ V V' ξ hc hm
  -- Step 6 is `dohr_tv_gmc_transfer`; only the support (Step 4) remains.
  refine ⟨V', hc, hm, hw, ?_, Submission.dohr_tv_gmc_transfer n ℓ U V ξ V' hw ht⟩
  -- Step 4: `spt V' = τ(U) ∩ spt(τ_# μ_V) = τ(U) ∩ τ(spt μ_V) = τ(U ∩ spt μ_V)`.
  show (fun x => x - ξ) '' U ∩ V'.weight.support = (fun x => x - ξ) '' (U ∩ V.weight.support)
  rw [hw, Submission.dohr_tv_support_map_sub n ℓ V.weight ξ,
    Set.image_inter (sub_left_injective (b := ξ))]

/-- **Simon Ch. 5, Theorem 7.1, proof, first paragraph (p. 127).**  Assume Allard's theorem 5.2.
If `V` has generalized mean curvature `H` in the open set `U`, `H` is locally in `Lᵖ(μ_V)` for some
`p > n`, `θ ≥ 1` `μ_V`-a.e. and `Θⁿ(μ_V, ξ) = 1` at `ξ ∈ U`, then there are `R > 0` with
`B_R(ξ) ⊆ U`, a linear isometry `Q` and `u`, `C¹` on `B̆ⁿ_R(0)` with `(1 − n/p)`-Hölder `Du`,
`u(0) = 0` and `Du(0) = 0`, such that `Q(spt V − ξ) ∩ B̆_R(0) = graph u ∩ B̆_R(0)`. -/
theorem dohr_allard_graph_at_density_one : AllardRegularityTheorem → ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, 1 ≤ V.mult x) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∃ R > 0, ∃ (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), closedBall ξ R ⊆ U ∧ ContDiffOn ℝ 1 u (ball 0 R) ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) R, ∀ y ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K * ‖x - y‖ ^ (1 - (n : ℝ) / p)) ∧ Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R := by
  intro hAllard n ℓ hn U hU V H p hp hH hLp hθ ξ hξU hξ
  -- Step 1: Allard's constants `δ₀, γ, C` for `(n, ℓ, p)`; take `δ := δ₀`.
  obtain ⟨δ₀, γ, C, hδ₀, -, hγ, hγ1, hA⟩ := hAllard n ℓ hn p hp
  -- Steps 3–4: `ξ ∈ spt V`, and a scale `ρ` with `B_ρ(ξ) ⊆ U`, mass ratio at most `1 + δ₀` and
  -- scaled `Lᵖ` norm of `H` at most `δ₀`.
  obtain ⟨hξspt, ρ, hρ, hρU, hmass, hLpρ⟩ :=
    density_one_allard_scale V H p ξ δ₀ hU hp hLp hξU hξ hδ₀
  -- Steps 2 and 5: the translate `V'` of `V` by `−ξ`, in the open set `τ(U)`, has
  -- `spt V' = τ(spt V)` and satisfies the hypotheses 5.1 at `(p, δ₀, ρ)`; apply Theorem 5.2.
  obtain ⟨V', -, -, -, hspt, -, hAH⟩ := exists_translated_varifold_allardHypotheses V ξ
  obtain ⟨q, u, hu, hu0, hDu0, hgraph, hnorm⟩ :=
    hA _ (isOpenMap_sub_right ξ U hU) V' _ δ₀ ρ hδ₀ le_rfl
      (hAH H p δ₀ ρ hH hθ hξspt hρ hρU hmass hLpρ)
  -- Step 6: `R := γρ > 0` and `Q := q⁻¹`; the Hölder exponent `1 − n/p` is positive.
  have hR : 0 < γ * ρ := mul_pos hγ hρ
  have hα : 0 < 1 - (n : ℝ) / p := by
    rw [sub_pos, div_lt_one ((Nat.cast_nonneg n).trans_lt hp)]
    exact hp
  -- Steps 7–8: the finite scaled `C^{1,α}` norm makes `u` a `C^{1,α}` function on `B̆ⁿ_R(0)`.
  obtain ⟨hu', -, K, hK⟩ := isHolderCk_one_of_scaledC1AlphaNorm_ne_top u (closedBall 0 (γ * ρ))
    (ball 0 (γ * ρ)) (1 - (n : ℝ) / p) ρ hα hρ hu ball_subset_interior_closedBall
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm)
  -- The first iterated derivative is the derivative, up to a linear isometry.
  have hiter : ∀ z, iteratedFDeriv ℝ 1 u z =
      (continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)).symm (fderiv ℝ u z) := by
    intro z
    ext m
    simp
  -- Step 9: `|(x, y)|² = |x|² + |y|²`, so a graph point in `B̆_R(0)` lies over `B̆ⁿ_R(0)`.
  have hsq : ∀ (x : Rn n) (y : Rn ℓ), ‖graphPoint x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_add]
    simp [graphPoint]
  have hle : ∀ (x : Rn n) (y : Rn ℓ), ‖x‖ ≤ ‖graphPoint x y‖ := fun x y =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      ((le_add_of_nonneg_right (sq_nonneg ‖y‖)).trans (hsq x y).ge)
  refine ⟨γ * ρ, hR, q.symm, u, ?_, by exact_mod_cast hu', hu0, ?_, ⟨K, fun x hx y hy => ?_⟩, ?_⟩
  · -- `B_R(ξ) ⊆ B_ρ(ξ) ⊆ U`, since `γ < 1`.
    exact (closedBall_subset_closedBall (mul_le_of_le_one_left hρ.le hγ1.le)).trans hρU
  · -- `B_R(0)` is a neighbourhood of `0`, so the derivative within it is the derivative.
    rw [← fderivWithin_of_mem_nhds (closedBall_mem_nhds (0 : Rn n) hR)]
    exact hDu0
  · have h := hK x hx y hy
    rwa [hiter, hiter, ← map_sub, LinearIsometryEquiv.norm_map] at h
  · -- Rotate the closed-ball identity of 5.2 back by `Q = q⁻¹` and pass to the open ball.
    rw [← hspt]
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hz⟩
      rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map] at hz
      obtain ⟨⟨_, ⟨x, -, rfl⟩, rfl⟩, -⟩ : y ∈ q '' graphOver u (closedBall 0 (γ * ρ)) ∩
          closedBall 0 (γ * ρ) := hgraph ▸ ⟨hy, mem_closedBall_zero_iff.2 hz.le⟩
      rw [LinearIsometryEquiv.norm_map] at hz
      rw [LinearIsometryEquiv.symm_apply_apply]
      exact ⟨⟨x, mem_ball_zero_iff.2 ((hle x (u x)).trans_lt hz), rfl⟩, mem_ball_zero_iff.2 hz⟩
    · rintro ⟨⟨x, hx, rfl⟩, hz⟩
      rw [mem_ball_zero_iff] at hz
      have hq : q (graphPoint x (u x)) ∈ V'.support ∩ closedBall 0 (γ * ρ) := by
        rw [hgraph]
        exact ⟨⟨_, ⟨x, ball_subset_closedBall hx, rfl⟩, rfl⟩,
          mem_closedBall_zero_iff.2 ((q.norm_map _).trans_le hz.le)⟩
      exact ⟨⟨_, hq.1, q.symm_apply_apply _⟩, mem_ball_zero_iff.2 hz⟩
/-- **Fixed-scale comparison on a set carrying `M`.**  If `ψ` is measurable, `|ψ| ≤ K` and `ψ = 0`
off the measurable set `B`, and `Hⁿ ⌞ (M ∩ B)` is carried by `S` with `Hⁿ(S ∩ B) < ∞`, then
`|∫_M ψ θ dHⁿ - c ∫_S ψ dHⁿ| ≤ K ∫_{S ∩ B} |1_M θ - c| dHⁿ`, provided the right side is finite.
Both integrals localize to `S ∩ B`, where the difference is `∫_{S ∩ B} ψ (1_M θ - c) dHⁿ`. -/
theorem dohr_tp_wtlp_ball_comparison_le : ∀ (n ℓ : ℕ) (M S B : Set (Amb n ℓ)) (θ ψ : Amb n ℓ → ℝ) (c K : ℝ), MeasurableSet B → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ B) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ B) ≠ ⊤ → Measurable ψ → (∀ w, |ψ w| ≤ K) → (∀ w, w ∉ B → ψ w = 0) → ∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)) ≠ ⊤ → |∫ w in M, ψ w * θ w ∂(μHE[n] : Measure (Amb n ℓ)) - c * ∫ w in S, ψ w ∂(μHE[n] : Measure (Amb n ℓ))| ≤ K * (∫⁻ w in S ∩ B, ‖M.indicator θ w - c‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))).toReal := by
  intro n ℓ M S B θ ψ c K
  generalize (μHE[n] : Measure (Amb n ℓ)) = μ
  intro hB hM hθ hMBS hSB hψ hψK hψB hΛ
  have hψK' : ∀ w, ‖ψ w‖ ≤ K := fun w => by rw [Real.norm_eq_abs]; exact hψK w
  -- The `S`-integral localizes to `S ∩ B`, as `ψ = 0` off `B`.
  have h1 : ∫ w in S, ψ w ∂μ = ∫ w in S ∩ B, ψ w ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict S) hψB,
      Measure.restrict_restrict hB, inter_comm B S]
  -- The `M`-integral localizes to `M ∩ B =ᵐ M ∩ (S ∩ B)`, i.e. to the integral of `ψ · 1_M θ`
  -- over `S ∩ B`.
  have h2 : ∫ w in M, ψ w * θ w ∂μ = ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ := by
    have hae : (M ∩ B : Set (Amb n ℓ)) =ᵐ[μ] (M ∩ (S ∩ B) : Set (Amb n ℓ)) := by
      refine ae_eq_set.mpr ⟨measure_mono_null (fun w hw => ?_) hMBS, ?_⟩
      · exact ⟨hw.1, fun hS => hw.2 ⟨hw.1.1, hS, hw.1.2⟩⟩
      · rw [show (M ∩ (S ∩ B)) \ (M ∩ B) = ∅ from
          eq_empty_of_forall_notMem fun w hw => hw.2 ⟨hw.1.1, hw.1.2.2⟩, measure_empty]
    have hMν : NullMeasurableSet M (μ.restrict (S ∩ B)) := hM.mono Measure.restrict_le_self
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ.restrict M) (s := B)
        (f := fun w => ψ w * θ w) (fun w hw => by rw [hψB w hw, zero_mul]),
      Measure.restrict_restrict hB, inter_comm B M, setIntegral_congr_set hae,
      ← Measure.restrict_restrict₀ hMν, ← integral_indicator₀ hMν]
    congr 1
    funext w
    exact indicator_mul_right M ψ θ
  -- Integrability on `S ∩ B`, which has finite measure.
  have : IsFiniteMeasure (μ.restrict (S ∩ B)) := isFiniteMeasure_restrict.mpr hSB
  have hf : AEStronglyMeasurable (M.indicator θ) (μ.restrict (S ∩ B)) :=
    ((aemeasurable_indicator_iff₀ hM).mpr hθ).restrict.aestronglyMeasurable
  have hfc : Integrable (fun w => M.indicator θ w - c) (μ.restrict (S ∩ B)) :=
    ⟨hf.sub aestronglyMeasurable_const, hasFiniteIntegral_iff_enorm.mpr hΛ.lt_top⟩
  have hfi : Integrable (M.indicator θ) (μ.restrict (S ∩ B)) :=
    (hfc.add (integrable_const c)).congr (ae_of_all _ fun w => by simp)
  have hψb : ∀ᵐ w ∂(μ.restrict (S ∩ B)), ‖ψ w‖ ≤ K := ae_of_all _ hψK'
  have hψi : Integrable ψ (μ.restrict (S ∩ B)) :=
    (integrable_const K).mono' hψ.aestronglyMeasurable hψb
  have hψf : Integrable (fun w => ψ w * M.indicator θ w) (μ.restrict (S ∩ B)) :=
    hfi.bdd_mul hψ.aestronglyMeasurable hψb
  -- Linearity: the difference is `∫_{S ∩ B} ψ (1_M θ - c)`.
  have h6 : ∫ w in S ∩ B, ψ w * M.indicator θ w ∂μ - c * ∫ w in S ∩ B, ψ w ∂μ =
      ∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ := by
    rw [← integral_const_mul, ← integral_sub hψf (hψi.const_mul c)]
    congr 1
    funext w
    ring
  -- `|ψ (1_M θ - c)| ≤ K |1_M θ - c|`, and `∫ |1_M θ - c| = Λ.toReal`.
  have hle : ‖∫ w in S ∩ B, ψ w * (M.indicator θ w - c) ∂μ‖ ≤
      ∫ w in S ∩ B, K * ‖M.indicator θ w - c‖ ∂μ :=
    norm_integral_le_of_norm_le (hfc.norm.const_mul K) (ae_of_all _ fun w => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hψK' w) (norm_nonneg _))
  rw [integral_const_mul, integral_norm_eq_lintegral_enorm hfc.aestronglyMeasurable] at hle
  rw [h2, h1, h6, ← Real.norm_eq_abs]
  exact hle

/-- **Weighted approximate tangent space at a Lebesgue point** (Simon Ch. 3, 1.4 ⇒ 1.7).
Let `M` be `Hⁿ`-measurable, `θ` be `Hⁿ ⌞ M`-measurable, `Hⁿ((M ∩ B̆_ε(y)) \ S) = 0`,
`Hⁿ(S ∩ B̆_ε(y)) < ∞`, `P` the approximate tangent space of `S` at `y`, and
`r⁻ⁿ ∫_{S ∩ B_r(y)} |1_M θ − θ(y)| dHⁿ → 0`.  Then `P` is the approximate tangent space of `M`
with respect to `θ` at `y`.  For `φ ∈ C_c` vanishing off `B_ρ(0)` with `|φ| ≤ K`, undoing the
blow-up gives `I(r) − θ(y) J(r) = r⁻ⁿ (∫_M ψ θ − θ(y) ∫_S ψ)` with `ψ = φ ∘ η_{y,r}` supported in
`B_{rρ}(y)`, which is at most `K r⁻ⁿ ∫_{S ∩ B_{rρ}(y)} |1_M θ − θ(y)| dHⁿ → 0`. -/
theorem dohr_tp_weighted_tangent_of_lebesgue_point : ∀ (n ℓ : ℕ) (M S : Set (Amb n ℓ)) (θ : Amb n ℓ → ℝ) (y : Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)) (ε : ℝ), 0 < ε → NullMeasurableSet M (μHE[n] : Measure (Amb n ℓ)) → AEMeasurable θ ((μHE[n] : Measure (Amb n ℓ)).restrict M) → (μHE[n] : Measure (Amb n ℓ)) ((M ∩ ball y ε) \ S) = 0 → (μHE[n] : Measure (Amb n ℓ)) (S ∩ ball y ε) ≠ ⊤ → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S y P → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ w in S ∩ closedBall y r, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) → Poincare.SimonGMT.Chapter03.HasWeightedApproximateTangentSpaceAt n M θ y P := by
  intro n ℓ M S θ y P ε hε hM hθ hMS hSfin hS hleb
  refine ⟨hS.1, fun φ => ?_⟩
  -- `φ` vanishes outside `B_ρ(0)` for some `ρ > 0`, and `|φ| ≤ K`.
  obtain ⟨ρ, hρ, hφρ⟩ := φ.hasCompactSupport.exists_pos_le_norm
  obtain ⟨K, hK⟩ := (map_continuous φ).bounded_above_of_compact_support φ.hasCompactSupport
  -- The Lebesgue-point hypothesis along the radii `r ρ`: `L(r ρ) < ∞` and `r⁻ⁿ L(r ρ) → 0`.
  obtain ⟨hLfin, hLlim⟩ := Submission.dohr_tp_wtlp_rescaled_limit n
    (fun t => ∫⁻ w in S ∩ closedBall y t, ‖M.indicator θ w - θ y‖ₑ ∂(μHE[n] : Measure (Amb n ℓ)))
    ρ hρ hleb
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * ρ < ε :=
    (((continuous_mul_const ρ).tendsto' 0 0 (zero_mul ρ)).eventually
      (eventually_lt_nhds hε)).filter_mono nhdsWithin_le_nhds
  -- `I(r) - θ(y) J(r) → 0` for the weighted and unweighted blow-up integrals `I`, `J`.
  have key : Tendsto (fun r : ℝ =>
      (∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' M, φ z * θ (y + r • z)
          ∂(μHE[n] : Measure (Amb n ℓ))) -
        θ y * ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' S, φ z
          ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 0) := by
    have hlimK := hLlim.const_mul K
    rw [mul_zero] at hlimK
    refine squeeze_zero_norm' ?_ hlimK
    filter_upwards [self_mem_nhdsWithin, hsmall, hLfin] with r hr hrε hLr
    have hr' : (0 : ℝ) < r := hr
    have hBε : closedBall y (r * ρ) ⊆ ball y ε := closedBall_subset_ball hrε
    -- `ψ = φ ∘ η_{y,r}` is continuous, bounded by `K`, and vanishes off `B_{rρ}(y)`.
    have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap y r) :=
      show Continuous fun w : Amb n ℓ => r⁻¹ • (w - y) by fun_prop
    have hψ0 : ∀ w, w ∉ closedBall y (r * ρ) →
        φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w) = 0 := by
      intro w hw
      apply hφρ
      rw [mem_closedBall, not_le] at hw
      rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
        Real.norm_of_nonneg hr'.le, ← dist_eq_norm, le_inv_mul_iff₀ hr']
      exact hw.le
    -- The comparison on `B_{rρ}(y)`, using `Hⁿ((M ∩ B) \ S) = 0` and `Hⁿ(S ∩ B) < ∞`.
    have hcmp := Submission.dohr_tp_wtlp_ball_comparison_le n ℓ M S (closedBall y (r * ρ)) θ
      (fun w => φ (Poincare.SimonGMT.Chapter03.blowUpMap y r w)) (θ y) K measurableSet_closedBall
      hM hθ (measure_mono_null (sdiff_subset_sdiff_left (inter_subset_inter_right M hBε)) hMS)
      (ne_top_of_le_ne_top hSfin (measure_mono (inter_subset_inter_right S hBε)))
      ((map_continuous φ).comp hηc).measurable
      (fun w => by rw [← Real.norm_eq_abs]; exact hK _) hψ0 hLr
    -- Undo the blow-ups: `I(r) = r⁻ⁿ ∫_M ψ θ` and `J(r) = r⁻ⁿ ∫_S ψ`.
    have hJ := rsod_blowUp_setIntegral_eq n ℓ S φ (fun _ => 1) y r hr'
    simp only [mul_one] at hJ
    have hpos : (0 : ℝ) < (r ^ n)⁻¹ := inv_pos.mpr (pow_pos hr' n)
    rw [rsod_blowUp_setIntegral_eq n ℓ M φ θ y r hr', hJ, Real.norm_eq_abs, mul_left_comm (θ y),
      ← mul_sub, abs_mul, abs_of_pos hpos, mul_left_comm K]
    exact mul_le_mul_of_nonneg_left hcmp hpos.le
  -- `J(r) → ∫_P φ` by the tangent-space hypothesis on `S`, hence `I(r) → θ(y) ∫_P φ`.
  have h2 := key.add ((hS.2 φ).const_mul (θ y))
  rw [zero_add] at h2
  refine Tendsto.congr (fun r => ?_) h2
  exact sub_add_cancel _ _
theorem dohr_local_monotonicity : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R Λ : ℝ), 0 < R → closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → 0 < Λ → Λ ≤ 1 → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (Ioo 0 R) ∧ ∃ t : ℝ, 0 ≤ t ∧ V.HasDensity y t ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (V.weight (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
  have dohrLmonoRadialAux_hasFDerivAt_norm : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => ‖z - y‖) (‖x - y‖⁻¹ • innerSL ℝ (x - y)) x := by
    intro E _ _ y x hxy
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : HasFDerivAt (fun z : E => ‖z - y‖ ^ 2)
        (2 • (innerSL ℝ (x - y)).comp (ContinuousLinearMap.id ℝ E)) x :=
      (hasFDerivAt_sub_const (𝕜 := ℝ) y).norm_sq
    have h2 := h1.sqrt (by positivity)
    have h3 : (fun z : E => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ := by
      funext z; exact Real.sqrt_sq (norm_nonneg _)
    rw [h3] at h2
    convert h2 using 1
    ext w
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, Real.sqrt_sq hpos.le]
    rw [two_smul]
    field_simp
    ring
  have dohrLmonoRadialAux_hasFDerivAt : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (φ : ℝ → ℝ), ContDiff ℝ 1 φ → ∀ (ρ : ℝ) (y x : E), x ≠ y →
      HasFDerivAt (fun z : E => φ (‖z - y‖ / ρ) • (z - y))
        (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ E +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x := by
    intro E _ _ φ hφ ρ y x hxy
    have hsub : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x :=
      hasFDerivAt_sub_const y
    have hnorm := dohrLmonoRadialAux_hasFDerivAt_norm y x hxy
    have hφd : HasDerivAt φ (deriv φ (‖x - y‖ / ρ)) (‖x - y‖ / ρ) :=
      (hφ.differentiable one_ne_zero _).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => φ (t / ρ)) (deriv φ (‖x - y‖ / ρ) * (1 / ρ)) ‖x - y‖ :=
      hφd.comp (‖x - y‖) ((hasDerivAt_id' (‖x - y‖)).div_const ρ)
    have h2 := h1.comp_hasFDerivAt x hnorm
    exact h2.smul hsub
  have dohrLmonoRadialAux_trace : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : ℝ) (f : E →L[ℝ] ℝ) (v : E) (B : E →L[ℝ] E),
      LinearMap.trace ℝ E ((a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ
          B.toLinearMap) = a * LinearMap.trace ℝ E B.toLinearMap + f (B v) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt
    intro E _ _ _ a f v B
    have hcomp : (a • ContinuousLinearMap.id ℝ E + f.smulRight v).toLinearMap ∘ₗ B.toLinearMap =
        a • B.toLinearMap + (f.toLinearMap ∘ₗ B.toLinearMap).smulRight v := by
      ext w
      simp
    rw [hcomp, map_add, map_smul, LinearMap.trace_smulRight]
    simp
  have dohrLmonoRadialAux_trace_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E),
      LinearMap.trace ℝ E P.starProjection.toLinearMap = (Module.finrank ℝ P : ℝ) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace
    intro E _ _ _ P
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp]
    rw [LinearMap.trace_comp_comm']
    have hcomp : P.orthogonalProjectionOnto.toLinearMap.comp P.subtypeL.toLinearMap =
        LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  have dohrLmonoRadialAux_inner_starProjection : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P : Submodule ℝ E) (v : E),
      inner ℝ v (P.starProjection v) = ‖P.starProjection v‖ ^ 2 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection
    intro E _ _ _ P v
    rw [← P.inner_starProjection_left_eq_right v v]
    simpa using P.re_inner_starProjection_eq_normSq v
  have dohrLmonoRadialAux_integrable : ∀ {n ℓ : ℕ} (μ : Measure (Amb n ℓ)) (f : Amb n ℓ → ℝ), Continuous f →
      ∀ (y : Amb n ℓ) (ρ : ℝ), μ (closedBall y ρ) < ∞ → (∀ x, ρ < ‖x - y‖ → f x = 0) →
        Integrable f μ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection
    intro n ℓ μ f hf y ρ hμ h0
    obtain ⟨C, hC⟩ := (isCompact_closedBall y ρ).exists_bound_of_continuousOn hf.continuousOn
    have hon : IntegrableOn f (closedBall y ρ) μ :=
      Measure.integrableOn_of_bounded (M := C) hμ.ne hf.aestronglyMeasurable
        (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx; exact hC x hx)
    have heq : (closedBall y ρ).indicator f = f := by
      funext x
      by_cases hx : x ∈ closedBall y ρ
      · simp [hx]
      · rw [indicator_of_notMem hx, h0 x (by rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx)]
    rw [← heq]
    exact hon.integrable_indicator measurableSet_closedBall
  have dohr_lmono_radial_inequality : ∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R : ℝ), closedBall y R ⊆ U → (∀ᵐ x ∂V.weight, x ∈ ball y R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj x = P.starProjection) → AEStronglyMeasurable (fun x => V.tangentProj x) (V.weight.restrict (ball y R)) → ∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂V.weight ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm
    intro n ℓ U V H hH y R hBR htan htm φ ρ hφ hanti hφ1 hφ0 hρ hρR
    -- basic facts about `φ`
    have hd_nonpos : ∀ t, deriv φ t ≤ 0 := fun t => hanti.deriv_nonpos
    have hd_zero : ∀ t, 1 < t → deriv φ t = 0 := by
      intro t ht
      have hzero : φ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [lt_mem_nhds ht] with u hu
        exact hφ0 u hu.le
      exact hzero.deriv_eq.trans (deriv_const t 0)
    have hφc : Continuous φ := hφ.continuous
    have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- the radial vector field
    set X : Amb n ℓ → Amb n ℓ := fun z => φ (‖z - y‖ / ρ) • (z - y) with hXdef
    have hX0 : ∀ z, ρ ≤ ‖z - y‖ → X z = 0 := by
      intro z hz
      have : 1 ≤ ‖z - y‖ / ρ := by rw [le_div_iff₀ hρ]; linarith
      simp [hXdef, hφ0 _ this]
    have hXnear : X =ᶠ[𝓝 y] fun z => z - y := by
      filter_upwards [ball_mem_nhds y (half_pos hρ)] with z hz
      rw [mem_ball, dist_eq_norm] at hz
      have : ‖z - y‖ / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
      simp [hXdef, hφ1 _ this]
    have hXcd : ContDiff ℝ 1 X := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hxy : x = y
      · rw [hxy]
        exact (contDiffAt_id.sub contDiffAt_const).congr_of_eventuallyEq hXnear
      · have h1 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => ‖z - y‖) x :=
          (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hxy)
        have h2 : ContDiffAt ℝ 1 (fun z : Amb n ℓ => φ (‖z - y‖ / ρ)) x :=
          hφ.contDiffAt.comp x (h1.div_const ρ)
        exact h2.smul (contDiffAt_id.sub contDiffAt_const)
    have hXsupp : Function.support X ⊆ closedBall y ρ := by
      intro z hz
      by_contra hzB
      rw [mem_closedBall, dist_eq_norm, not_le] at hzB
      exact hz (hX0 z hzB.le)
    have hXcs : HasCompactSupport X :=
      HasCompactSupport.intro (isCompact_closedBall y ρ) fun z hz => by
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        exact hX0 z hz.le
    have hXts : tsupport X ⊆ U :=
      (closure_minimal hXsupp isClosed_closedBall).trans
        ((closedBall_subset_closedBall hρR.le).trans hBR)
    -- the generalized mean curvature identity
    have hGMC := hH.2 X hXcd hXcs hXts
    -- derivative of `X`
    have hDX : ∀ x, x ≠ y → HasFDerivAt X (φ (‖x - y‖ / ρ) • ContinuousLinearMap.id ℝ (Amb n ℓ) +
          ((deriv φ (‖x - y‖ / ρ) * (1 / ρ)) • (‖x - y‖⁻¹ • innerSL ℝ (x - y))).smulRight
            (x - y)) x :=
      fun x hxy => dohrLmonoRadialAux_hasFDerivAt φ hφ ρ y x hxy
    have hDXy : HasFDerivAt X (ContinuousLinearMap.id ℝ (Amb n ℓ)) y :=
      (hasFDerivAt_sub_const y).congr_of_eventuallyEq hXnear
    have hdiv_formula : ∀ x, x ≠ y → V.divM X x =
        φ (‖x - y‖ / ρ) * LinearMap.trace ℝ (Amb n ℓ) (V.tangentProj x).toLinearMap +
          deriv φ (‖x - y‖ / ρ) * (1 / ρ) *
            (‖x - y‖⁻¹ * inner ℝ (x - y) (V.tangentProj x (x - y))) := by
      intro x hxy
      rw [RectifiableVarifold.divM, (hDX x hxy).fderiv, dohrLmonoRadialAux_trace]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    have hdiv_zero : ∀ x, ρ < ‖x - y‖ → V.divM X x = 0 := by
      intro x hx
      have hxy : x ≠ y := by
        intro h
        rw [h, sub_self, norm_zero] at hx
        linarith
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      rw [hdiv_formula x hxy, hφ0 _ h1.le, hd_zero _ h1]
      ring
    -- the comparison functions
    set g : Amb n ℓ → ℝ := fun x =>
      (n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) with hgdef
    set k : Amb n ℓ → ℝ := fun x => (n : ℝ) * φ (‖x - y‖ / ρ) with hkdef
    have hsand : ∀ᵐ x ∂V.weight, g x ≤ V.divM X x ∧ V.divM X x ≤ k x := by
      filter_upwards [htan] with x hx
      by_cases hxR : x ∈ ball y R
      · obtain ⟨P, hPn, hPx⟩ := hx hxR
        by_cases hxy : x = y
        · rw [hxy] at hPx ⊢
          have hdy : V.divM X y = n := by
            rw [RectifiableVarifold.divM, hDXy.fderiv, hPx]
            simp [dohrLmonoRadialAux_trace_starProjection, hPn]
          rw [hdy]
          simp [hgdef, hkdef, hφ1 0 (by norm_num)]
        · have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
          have hsr : ‖P.starProjection (x - y)‖ ≤ ‖x - y‖ := P.norm_starProjection_apply_le _
          have hs0 : 0 ≤ ‖P.starProjection (x - y)‖ := norm_nonneg _
          rw [hdiv_formula x hxy, hPx, dohrLmonoRadialAux_trace_starProjection, hPn,
            dohrLmonoRadialAux_inner_starProjection]
          simp only [hgdef, hkdef]
          have hd : deriv φ (‖x - y‖ / ρ) ≤ 0 := hd_nonpos _
          have h1 : ‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2 ≤ ‖x - y‖ := by
            rw [inv_mul_le_iff₀ hr]
            calc ‖P.starProjection (x - y)‖ ^ 2
                = ‖P.starProjection (x - y)‖ * ‖P.starProjection (x - y)‖ := sq _
              _ ≤ ‖x - y‖ * ‖x - y‖ := mul_self_le_mul_self hs0 hsr
          have hq : (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) ≤ ‖x - y‖ / ρ := by
            calc (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2)
                ≤ (1 / ρ) * ‖x - y‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = ‖x - y‖ / ρ := by ring
          have hq0 : 0 ≤ (1 / ρ) * (‖x - y‖⁻¹ * ‖P.starProjection (x - y)‖ ^ 2) := by positivity
          have e1 := mul_le_mul_of_nonpos_left hq hd
          have e2 := mul_nonpos_of_nonpos_of_nonneg hd hq0
          constructor
          · linarith
          · linarith
      · have hx' : ρ < ‖x - y‖ := by
          rw [mem_ball, dist_eq_norm, not_lt] at hxR
          linarith
        rw [hdiv_zero x hx']
        have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
        simp [hgdef, hkdef, hφ0 _ h1.le, hd_zero _ h1]
    -- finiteness of the weight on `closedBall y ρ`
    have hμρ : V.weight (closedBall y ρ) < ∞ := by
      have hBρ : closedBall y ρ ⊆ U := (closedBall_subset_closedBall hρR.le).trans hBR
      rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
      exact (V.integrableOn_mult _ (isCompact_closedBall y ρ) hBρ).setLIntegral_lt_top
    -- integrability of the comparison functions
    have hgc : Continuous g := by simp only [hgdef]; fun_prop
    have hkc : Continuous k := by simp only [hkdef]; fun_prop
    have hg_int : Integrable g V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight g hgc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hgdef, hφ0 _ h1.le, hd_zero _ h1]
    have hk_int : Integrable k V.weight := by
      refine dohrLmonoRadialAux_integrable V.weight k hkc y ρ hμρ fun x hx => ?_
      have h1 : 1 < ‖x - y‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
      simp [hkdef, hφ0 _ h1.le]
    -- measurability of the tangential divergence
    have hΦ : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
        LinearMap.trace ℝ (Amb n ℓ) (p.1.toLinearMap ∘ₗ p.2.toLinearMap)) := by
      have h1 : Continuous (fun p : (Amb n ℓ →L[ℝ] Amb n ℓ) × (Amb n ℓ →L[ℝ] Amb n ℓ) =>
          p.1.comp p.2) :=
        isBoundedBilinearMap_comp.continuous
      have h2 : Continuous (fun A : Amb n ℓ →L[ℝ] Amb n ℓ =>
          LinearMap.trace ℝ (Amb n ℓ) A.toLinearMap) :=
        ((LinearMap.trace ℝ (Amb n ℓ)).comp
          (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
      exact h2.comp h1
    have hDXc : Continuous (fderiv ℝ X) := hXcd.continuous_fderiv one_ne_zero
    have hdivR : AEStronglyMeasurable (fun x => LinearMap.trace ℝ (Amb n ℓ)
        ((fderiv ℝ X x).toLinearMap ∘ₗ (V.tangentProj x).toLinearMap))
        (V.weight.restrict (ball y R)) :=
      hΦ.comp_aestronglyMeasurable (hDXc.aestronglyMeasurable.prodMk htm)
    have hdiv_meas : AEStronglyMeasurable (V.divM X) V.weight := by
      have heq : V.divM X = (ball y R).indicator (V.divM X) := by
        funext x
        by_cases hx : x ∈ ball y R
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx]
          apply hdiv_zero
          rw [mem_ball, dist_eq_norm, not_lt] at hx
          linarith
      rw [heq]
      exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr hdivR
    have hdiv_int : Integrable (V.divM X) V.weight :=
      integrable_of_le_of_le hdiv_meas (hsand.mono fun x hx => hx.1)
        (hsand.mono fun x hx => hx.2) hg_int hk_int
    calc ∫ x, g x ∂V.weight ≤ ∫ x, V.divM X x ∂V.weight :=
          integral_mono_ae hg_int hdiv_int (hsand.mono fun x hx => hx.1)
      _ = -∫ x, inner ℝ (X x) (H x) ∂V.weight := hGMC
      _ = -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂V.weight := by
          congr 1
          apply integral_congr_ae
          filter_upwards with x
          simp only [hXdef, real_inner_smul_left]
  have dohr_lmono_curvature_holder : ∀ (n ℓ : ℕ) (p : ℝ), 1 < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (ψ : Amb n ℓ → ℝ) (y : Amb n ℓ) (t : ℝ), 0 ≤ t → μ (closedBall y t) < ⊤ → IntegrableOn H (closedBall y t) μ → ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ < ⊤ → AEStronglyMeasurable ψ μ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) → (∀ x, t < ‖x - y‖ → ψ x = 0) → |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ| ≤ t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality
    intro n ℓ p hp μ H ψ y t ht hμB hH hHp hψm hψ01 hψ0
    set B : Set (Amb n ℓ) := closedBall y t with hBdef
    have hBm : MeasurableSet B := measurableSet_closedBall
    set q : ℝ := Real.conjExponent p with hqdef
    have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
    have h1q : 1 / q = 1 - 1 / p := by
      rw [one_div, one_div, hpq.one_sub_inv]
    have hq1 : 1 ≤ q := hpq.symm.lt.le
    -- `ψ` vanishes off `B`
    have hψB : ∀ x, x ∉ B → ψ x = 0 := by
      intro x hx
      apply hψ0
      simpa [hBdef, mem_closedBall, dist_eq_norm, not_le] using hx
    -- `ψ` is integrable
    have hψint : Integrable ψ μ := by
      have h1 : Integrable (B.indicator ψ) μ := by
        refine IntegrableOn.integrable_indicator ?_ hBm
        refine Measure.integrableOn_of_bounded (M := 1) hμB.ne hψm ?_
        exact Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          exact (hψ01 x).2
      have h2 : B.indicator ψ = ψ := by
        funext x
        by_cases hx : x ∈ B
        · simp [hx]
        · simp [hx, hψB x hx]
      rwa [h2] at h1
    have hIψ : 0 ≤ ∫ x, ψ x ∂μ := integral_nonneg fun x => (hψ01 x).1
    -- pointwise bound
    have hpt : ∀ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ≤
        B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x := by
      intro x
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx]
        have hxt : ‖x - y‖ ≤ t := by
          simpa [hBdef, mem_closedBall, dist_eq_norm] using hx
        have hle : ‖ψ x * inner ℝ (x - y) (H x)‖ ≤ t * (‖H x‖ * ψ x) := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hψ01 x).1]
          have h1 : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ ‖x - y‖ * ‖H x‖ := norm_inner_le_norm _ _
          have h2 : ‖x - y‖ * ‖H x‖ ≤ t * ‖H x‖ :=
            mul_le_mul_of_nonneg_right hxt (norm_nonneg _)
          nlinarith [(hψ01 x).1, norm_nonneg (H x)]
        calc ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖
            ≤ ENNReal.ofReal (t * (‖H x‖ * ψ x)) := ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) := by
            rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
      · rw [indicator_of_notMem hx, hψB x hx]
        simp
    -- Hölder on `μ.restrict B`
    have hHmeas : AEMeasurable (fun x => ‖H x‖ₑ) (μ.restrict B) := hH.aestronglyMeasurable.enorm
    have hψmeas : AEMeasurable (fun x => ENNReal.ofReal (ψ x)) (μ.restrict B) :=
      hψm.restrict.aemeasurable.ennreal_ofReal
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) hpq hHmeas hψmeas
    have hψq : (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ≤ ENNReal.ofReal (∫ x, ψ x ∂μ) := by
      calc (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ)
          ≤ ∫⁻ x in B, ENNReal.ofReal (ψ x) ∂μ := by
            apply lintegral_mono
            intro x
            apply ENNReal.rpow_le_self_of_le_one _ hq1
            exact ENNReal.ofReal_le_one.mpr (hψ01 x).2
        _ ≤ ∫⁻ x, ENNReal.ofReal (ψ x) ∂μ := setLIntegral_le_lintegral _ _
        _ = ENNReal.ofReal (∫ x, ψ x ∂μ) :=
            (ofReal_integral_eq_lintegral_ofReal hψint (Eventually.of_forall fun x => (hψ01 x).1)).symm
    set X : ℝ≥0∞ := ∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ with hXdef
    have hXne : X ≠ ⊤ := hHp.ne
    have hlint : (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ) ≤
        ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
      calc (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ)
          ≤ ∫⁻ x, B.indicator (fun x => ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x))) x ∂μ :=
            lintegral_mono hpt
        _ = ∫⁻ x in B, ENNReal.ofReal t * (‖H x‖ₑ * ENNReal.ofReal (ψ x)) ∂μ :=
            lintegral_indicator hBm _
        _ = ENNReal.ofReal t * ∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) := by
            gcongr ENNReal.ofReal t * ?_
            calc (∫⁻ x in B, ‖H x‖ₑ * ENNReal.ofReal (ψ x) ∂μ)
                ≤ (∫⁻ x in B, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) *
                    (∫⁻ x in B, ENNReal.ofReal (ψ x) ^ q ∂μ) ^ (1 / q) := hHolder
              _ ≤ X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q) := by
                  gcongr
    have hfin : ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q)) ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.one_div_nonneg hXne
      · exact ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg ENNReal.ofReal_ne_top
    calc |∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ|
        = ‖∫ x, ψ x * inner ℝ (x - y) (H x) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ (∫⁻ x, ENNReal.ofReal ‖ψ x * inner ℝ (x - y) (H x)‖ ∂μ).toReal :=
          norm_integral_le_lintegral_norm _
      _ ≤ (ENNReal.ofReal t * (X ^ (1 / p) * ENNReal.ofReal (∫ x, ψ x ∂μ) ^ (1 / q))).toReal :=
          ENNReal.toReal_mono hfin hlint
      _ = t * X.toReal ^ (1 / p) * (∫ x, ψ x ∂μ) ^ (1 - 1 / p) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
            ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hIψ, h1q, mul_assoc]
  have dohrLmonoFixedCutoffAux_phi_nonneg : ∀ {φ : ℝ → ℝ}, Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ (s : ℝ), 0 ≤ φ s := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro φ hanti hcut s
    rcases le_total 1 s with h | h
    · rw [hcut s h]
    · rw [← hcut 1 le_rfl]
      exact hanti h
  have dohrLmonoFixedCutoffAux_deriv_zero : ∀ {φ : ℝ → ℝ}, (∀ t : ℝ, 1 ≤ t → φ t = 0) → ∀ {s : ℝ}, 1 < s → deriv φ s = 0 := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hcut s hs
    have hzero : φ =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [lt_mem_nhds hs] with u hu
      exact hcut u hu.le
    exact hzero.deriv_eq.trans (deriv_const s 0)
  have dohrLmonoFixedCutoffAux_deriv_bound : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → |s * deriv φ s| ≤ C := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg
    intro φ hφ hcut
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hφ.continuous_deriv_one.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    rcases le_or_gt s 1 with h1 | h1
    · have h := hC s ⟨hs, h1⟩
      rw [Real.norm_eq_abs] at h
      rw [abs_mul, abs_of_nonneg hs]
      calc s * |deriv φ s| ≤ 1 * |deriv φ s| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |deriv φ s| := one_mul _
        _ ≤ max C 0 := h.trans (le_max_left _ _)
    · rw [dohrLmonoFixedCutoffAux_deriv_zero hcut h1, mul_zero, abs_zero]
      exact le_max_right _ _
  have dohrLmonoFixedCutoffAux_hasDerivAt : ∀ {φ : ℝ → ℝ}, ContDiff ℝ 1 φ → ∀ (c : ℝ) {t : ℝ}, t ≠ 0 →
      HasDerivAt (fun u => φ (c / u)) (-(c / t * deriv φ (c / t)) / t) t := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound
    intro φ hφ c t ht
    have h1 : HasDerivAt (fun u : ℝ => c / u) (c * -(t ^ 2)⁻¹) t := by
      have := (hasDerivAt_inv ht).const_mul c
      convert this using 1
      funext u
      exact div_eq_mul_inv c u
    have h2 := ((hφ.differentiable (by simp) (c / t)).hasDerivAt).comp t h1
    have heq : -(c / t * deriv φ (c / t)) / t = deriv φ (c / t) * (c * -(t ^ 2)⁻¹) := by
      rw [sq, mul_inv]
      ring
    rw [heq]
    exact h2
  have dohrLmonoFixedCutoffAux_npow : ∀ (n : ℕ) {ρ : ℝ}, ρ ≠ 0 → (n : ℝ) * ρ ^ (n - 1) = n * ρ ^ n / ρ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt
    intro n ρ hρ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [eq_div_iff hρ, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  have dohr_lmono_fixed_cutoff_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (φ : ℝ → ℝ) (I a : ℝ → ℝ) (R M β : ℝ), β < 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, 1 ≤ t → φ t = 0) → (∀ ρ : ℝ, 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → (∀ t : ℝ, I t = ∫ x, φ (‖x - y‖ / t) ∂μ) → (∀ t : ℝ, a t = (∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I t / t ^ n)) → (∀ t : ℝ, 0 < t → t < R → |a t| ≤ M * t ^ (-β)) → ContinuousOn a (Ioo 0 R) ∧ MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder
    intro n ℓ μ H y φ I a R M β hβ hμR hH hφ hanti hcut hrad hI ha hab
    -- the curvature integral `L`
    obtain ⟨L, hL⟩ : ∃ L : ℝ → ℝ,
        ∀ t, L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ := ⟨_, fun t => rfl⟩
    have ha' : ∀ t, a t = L t / t ^ (n + 1) / (1 + I t / t ^ n) := fun t => by
      rw [ha t, hL t]
    have hrad' : ∀ ρ : ℝ, 0 < ρ → ρ < R →
        ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -L ρ :=
      fun ρ h1 h2 => by rw [hL ρ]; exact hrad ρ h1 h2
    clear ha hrad
    set S : Set (Amb n ℓ) := closedBall y R with hSdef
    have hSm : MeasurableSet S := measurableSet_closedBall
    set ν : Measure (Amb n ℓ) := μ.restrict S with hνdef
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := hH
    have hφnn := dohrLmonoFixedCutoffAux_phi_nonneg hanti hcut
    obtain ⟨C, hC0, hC⟩ := dohrLmonoFixedCutoffAux_deriv_bound hφ hcut
    have hφc : Continuous φ := hφ.continuous
    have hdφc : Continuous (deriv φ) := hφ.continuous_deriv_one
    -- outside `S`, all the scaled profiles vanish
    have hout : ∀ t, 0 < t → t < R → ∀ x, x ∉ S → 1 < ‖x - y‖ / t := by
      intro t ht htR x hx
      have hRx : R < ‖x - y‖ := by
        simpa [hSdef, mem_closedBall, dist_eq_norm, not_le] using hx
      rw [lt_div_iff₀ ht]
      linarith
    -- conversion of the integrals to `ν`
    have hIν : ∀ t, 0 < t → t < R → I t = ∫ x, φ (‖x - y‖ / t) ∂ν := by
      intro t ht htR
      rw [hI t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hcut _ (hout t ht htR x hx).le
    have hLν : ∀ t, 0 < t → t < R →
        L t = ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro t ht htR
      rw [hL t, hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hcut _ (hout t ht htR x hx).le, zero_mul]
    -- derivative of the profile in the scale variable
    set F' : ℝ → Amb n ℓ → ℝ := fun t x => -(‖x - y‖ / t * deriv φ (‖x - y‖ / t)) / t
      with hF'eq
    have hIderiv : ∀ ρ, 0 < ρ → ρ < R → HasDerivAt I (∫ x, F' ρ x ∂ν) ρ := by
      intro ρ hρ hρR
      have hmain : HasDerivAt (fun t => ∫ x, φ (‖x - y‖ / t) ∂ν) (∫ x, F' ρ x ∂ν) ρ := by
        have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
          (F := fun t x => φ (‖x - y‖ / t)) (F' := F') (x₀ := ρ) (bound := fun _ => 2 * C / ρ)
          (Ioo_mem_nhds (half_lt_self hρ) hρR) ?_ ?_ ?_ ?_ ?_ ?_
        · exact key.2
        · exact Eventually.of_forall fun t =>
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        · refine Integrable.of_bound
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
            (φ 0) (Eventually.of_forall fun x => ?_)
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (hφnn _)]
          exact hanti (div_nonneg (norm_nonneg _) hρ.le)
        · have hcont : Continuous (F' ρ) := by
            simp only [hF'eq]
            fun_prop
          exact hcont.aestronglyMeasurable
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          simp only [hF'eq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos ht0]
          calc |‖x - y‖ / t * deriv φ (‖x - y‖ / t)| / t ≤ C / t :=
                div_le_div_of_nonneg_right (hC _ (div_nonneg (norm_nonneg _) ht0.le)) ht0.le
            _ ≤ 2 * C / ρ := by
                rw [div_le_div_iff₀ ht0 hρ]
                nlinarith [ht.1]
        · exact integrable_const _
        · refine Eventually.of_forall fun x t ht => ?_
          have ht0 : 0 < t := lt_trans (half_pos hρ) ht.1
          exact dohrLmonoFixedCutoffAux_hasDerivAt hφ ‖x - y‖ ht0.ne'
      refine hmain.congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact hIν t ht.1 ht.2
    -- continuity of `L`
    have hLcont : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt L ρ := by
      intro ρ hρ hρR
      have hmain : ContinuousAt
          (fun t => ∫ x, φ (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν) ρ := by
        apply continuousAt_of_dominated (bound := fun x => φ 0 * (R * ‖H x‖))
        · refine Eventually.of_forall fun t => ?_
          have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ (‖x - y‖ / t)) ν :=
            (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
            continuous_inner.comp_aestronglyMeasurable
              ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
                hHν.aestronglyMeasurable)
          exact h1.mul h2
        · filter_upwards [Ioi_mem_nhds hρ] with t ht
          rw [hνdef, ae_restrict_iff' hSm]
          refine Eventually.of_forall fun x hx => ?_
          have hxR : ‖x - y‖ ≤ R := by
            simpa [hSdef, mem_closedBall, dist_eq_norm] using hx
          have hσ : 0 ≤ ‖x - y‖ / t := div_nonneg (norm_nonneg _) (le_of_lt ht)
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφnn _)]
          have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
            (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
          exact mul_le_mul (hanti hσ) hinner (norm_nonneg _) (hφnn 0)
        · exact (hHν.norm.const_mul R).const_mul (φ 0)
        · refine Eventually.of_forall fun x => ?_
          exact (hφc.continuousAt.comp (continuousAt_const.div continuousAt_id hρ.ne')).mul
            continuousAt_const
      refine hmain.congr ?_
      filter_upwards [Ioo_mem_nhds hρ hρR] with t ht
      exact (hLν t ht.1 ht.2).symm
    -- the key differential inequality
    have hkey : ∀ ρ, 0 < ρ → ρ < R → L ρ ≤ ρ * (∫ x, F' ρ x ∂ν) - n * I ρ := by
      intro ρ hρ hρR
      have h1 := hrad' ρ hρ hρR
      have hconv : ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ =
          ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂ν := by
        rw [hνdef, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        have h := hout ρ hρ hρR x hx
        rw [hcut _ h.le, dohrLmonoFixedCutoffAux_deriv_zero hcut h]
        ring
      have hint1 : Integrable (fun x => φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (hφc.comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / ρ)).aestronglyMeasurable
          (φ 0) (Eventually.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (hφnn _)]
        exact hanti (div_nonneg (norm_nonneg _) hρ.le)
      have hint2 : Integrable (fun x => ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ν := by
        refine Integrable.of_bound
          (by fun_prop : Continuous fun x : Amb n ℓ =>
            ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)).aestronglyMeasurable
          C (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hC _ (div_nonneg (norm_nonneg _) hρ.le)
      rw [hconv, integral_add (hint1.const_mul _) hint2, integral_const_mul,
        ← hIν ρ hρ hρR] at h1
      have hF'int : ∫ x, F' ρ x ∂ν = -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ := by
        simp only [hF'eq]
        rw [integral_div, integral_neg]
      rw [hF'int]
      have hρne : ρ ≠ 0 := hρ.ne'
      have hsimp : ρ * (-(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) / ρ) =
          -(∫ x, ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ) ∂ν) := by
        field_simp
      rw [hsimp]
      linarith
    -- basic facts on `I`
    have hInn : ∀ ρ, 0 ≤ I ρ := fun ρ => by
      rw [hI ρ]
      exact integral_nonneg fun x => hφnn _
    have hden : ∀ ρ, 0 < ρ → 1 ≤ 1 + I ρ / ρ ^ n := fun ρ h1 => by
      have := div_nonneg (hInn ρ) (pow_pos h1 n).le
      linarith
    -- continuity of `a`
    have hacontAt : ∀ ρ, 0 < ρ → ρ < R → ContinuousAt a ρ := by
      intro ρ h1 h2
      have haeq : a = fun t => L t / t ^ (n + 1) / (1 + I t / t ^ n) := funext ha'
      rw [haeq]
      exact ((hLcont ρ h1 h2).div ((continuous_pow (n + 1)).continuousAt) (pow_ne_zero _ h1.ne')).div
        (continuousAt_const.add ((hIderiv ρ h1 h2).continuousAt.div ((continuous_pow n).continuousAt)
          (pow_ne_zero _ h1.ne')))
        (by linarith [hden ρ h1])
    have hacont : ContinuousOn a (Ioo 0 R) := fun ρ hρ =>
      (hacontAt ρ hρ.1 hρ.2).continuousWithinAt
    refine ⟨hacont, ?_⟩
    -- the fundamental theorem of calculus for `∫₀^ρ a`
    have hGderiv : ∀ ρ, 0 < ρ → ρ < R →
        HasDerivAt (fun u => ∫ t in (0)..u, a t) (a ρ) ρ := by
      intro ρ h1 h2
      apply intervalIntegral.integral_hasDerivAt_right
      · refine IntervalIntegrable.mono_fun' (g := fun t => M * t ^ (-β)) ?_ ?_ ?_
        · exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul M
        · rw [uIoc_of_le h1.le]
          exact (hacont.mono (Ioc_subset_Ioo_right h2)).aestronglyMeasurable measurableSet_Ioc
        · rw [uIoc_of_le h1.le]
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
          show ‖a t‖ ≤ M * t ^ (-β)
          rw [Real.norm_eq_abs]
          exact hab t ht.1 (lt_of_le_of_lt ht.2 h2)
      · exact hacont.stronglyMeasurableAtFilter isOpen_Ioo ρ ⟨h1, h2⟩
      · exact hacontAt ρ h1 h2
    -- derivative of the monotone quantity
    have hΨ : ∀ ρ ∈ Ioo 0 R, ∃ D : ℝ,
        HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n)) D ρ ∧ 0 ≤ D := by
      rintro ρ ⟨h1, h2⟩
      have hG := hGderiv ρ h1 h2
      have hIρ := hIderiv ρ h1 h2
      have hd := (hG.neg.exp).mul
        ((hasDerivAt_const ρ (1 : ℝ)).add (hIρ.div (hasDerivAt_pow n ρ) (pow_ne_zero n h1.ne')))
      have hd' : HasDerivAt (fun ρ => Real.exp (-∫ t in (0)..ρ, a t) * (1 + I ρ / ρ ^ n))
          (Real.exp (-∫ t in (0)..ρ, a t) * -a ρ * (1 + I ρ / ρ ^ n) +
            Real.exp (-∫ t in (0)..ρ, a t) * (0 + ((∫ x, F' ρ x ∂ν) * ρ ^ n -
              I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2)) ρ := hd
      refine ⟨_, hd', ?_⟩
      set E := Real.exp (-∫ t in (0)..ρ, a t) with hEdef
      set I' := ∫ x, F' ρ x ∂ν with hI'eq
      have hE : 0 < E := Real.exp_pos _
      have hP : 0 < ρ ^ n := pow_pos h1 n
      have hden' : 1 + I ρ / ρ ^ n ≠ 0 := by linarith [hden ρ h1]
      have haL : a ρ * (1 + I ρ / ρ ^ n) = L ρ / (ρ ^ n * ρ) := by
        rw [ha' ρ, div_mul_cancel₀ _ hden', pow_succ]
      have hq : (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2 =
          (ρ * I' - n * I ρ) / (ρ ^ n * ρ) := by
        rw [dohrLmonoFixedCutoffAux_npow n h1.ne']
        field_simp
      have hkeyρ := hkey ρ h1 h2
      have hnum : 0 ≤ (ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ) :=
        div_nonneg (by linarith) (by positivity)
      have hfinal : E * -a ρ * (1 + I ρ / ρ ^ n) +
          E * (0 + (I' * ρ ^ n - I ρ * ((n : ℝ) * ρ ^ (n - 1))) / (ρ ^ n) ^ 2) =
          E * ((ρ * I' - n * I ρ - L ρ) / (ρ ^ n * ρ)) := by
        linear_combination (-E) * haL + E * hq
      rw [hfinal]
      exact mul_nonneg hE.le hnum
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 R)
    · intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, -⟩ := hΨ ρ hρ
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro ρ hρ
      obtain ⟨D, hD, hD0⟩ := hΨ ρ hρ
      rw [hD.deriv]
      exact hD0
  have dohrLmonoOpenBallAux_cutoffs : ∃ φ : ℕ → ℝ → ℝ,
      (∀ k, ContDiff ℝ 1 (φ k)) ∧ (∀ k, Antitone (φ k)) ∧
      (∀ k (t : ℝ), t ≤ 1 / 2 → φ k t = 1) ∧ (∀ k (t : ℝ), 1 ≤ t → φ k t = 0) ∧
      (∀ k t, 0 ≤ φ k t ∧ φ k t ≤ 1) ∧
      (∀ s : ℝ, s < 1 → ∀ᶠ k in atTop, φ k s = 1) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone
    refine ⟨fun k s => 1 - Real.smoothTransition (((k : ℝ) + 3) * (s - 1) + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))
    · intro k s t hst
      have hk : (0 : ℝ) < (k : ℝ) + 3 := by positivity
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      have := Real.smoothTransition.monotone h1
      simp only
      linarith
    · intro k t ht
      have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      have h1 : ((k : ℝ) + 3) * (t - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
    · intro k t ht
      have hk : (0 : ℝ) ≤ (k : ℝ) + 3 := by positivity
      have h1 : 1 ≤ ((k : ℝ) + 3) * (t - 1) + 1 := by nlinarith
      simp only
      rw [Real.smoothTransition.one_of_one_le h1, sub_self]
    · intro k t
      have h0 := Real.smoothTransition.nonneg (((k : ℝ) + 3) * (t - 1) + 1)
      have h1 := Real.smoothTransition.le_one (((k : ℝ) + 3) * (t - 1) + 1)
      constructor <;> simp only <;> linarith
    · intro s hs
      obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 / (1 - s))
      rw [eventually_atTop]
      refine ⟨k₀, fun k hk => ?_⟩
      have hs1 : 0 < 1 - s := by linarith
      have hkk : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
      have h2 : 1 / (1 - s) < (k : ℝ) + 3 := by linarith
      have h3 : 1 < ((k : ℝ) + 3) * (1 - s) := by
        rw [div_lt_iff₀ hs1] at h2
        linarith
      have h1 : ((k : ℝ) + 3) * (s - 1) + 1 ≤ 0 := by nlinarith
      simp only
      rw [Real.smoothTransition.zero_of_nonpos h1, sub_zero]
  have dohrLmonoOpenBallAux_rpow_le : ∀ {b e : ℝ}, 0 ≤ b → 0 ≤ e → e ≤ 1 → b ^ e ≤ 1 + b := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
    intro b e hb he0 he1
    rcases le_total b 1 with h | h
    · have := Real.rpow_le_one hb h he0
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le h he1
      rw [Real.rpow_one] at this
      linarith
  have dohrLmonoOpenBallAux_abound : ∀ (n : ℕ) {p t N I L : ℝ}, 1 < p → 0 < t → 0 ≤ N → 0 ≤ I →
      |L| ≤ t * N * I ^ (1 - 1 / p) →
        |L / t ^ (n + 1) / (1 + I / t ^ n)| ≤ N * t ^ (-((n : ℝ) / p)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs
    intro n p t N I L hp ht hN hI hL
    have hp0 : 0 < p := by linarith
    have htn : 0 < t ^ n := pow_pos ht n
    set b := I / t ^ n with hbdef
    have hb : 0 ≤ b := div_nonneg hI htn.le
    have hIb : I = b * t ^ n := by
      rw [hbdef, div_mul_cancel₀ _ htn.ne']
    have he0 : 0 ≤ 1 - 1 / p := by
      have : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
      linarith
    have he1 : 1 - 1 / p ≤ 1 := by
      have : 0 < 1 / p := by positivity
      linarith
    have hpow : I ^ (1 - 1 / p) = b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p)) := by
      rw [hIb, Real.mul_rpow hb htn.le, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    have hbe := dohrLmonoOpenBallAux_rpow_le hb he0 he1
    have hden : 0 < 1 + b := by linarith
    have hT : 0 < t ^ ((n : ℝ) * (1 - 1 / p)) := Real.rpow_pos_of_pos ht _
    have hL' : |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by
      calc |L| ≤ t * N * I ^ (1 - 1 / p) := hL
        _ = t * N * (b ^ (1 - 1 / p) * t ^ ((n : ℝ) * (1 - 1 / p))) := by rw [hpow]
        _ ≤ t * N * ((1 + b) * t ^ ((n : ℝ) * (1 - 1 / p))) := by
            gcongr
        _ = N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := by ring
    have hexp : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ (-((n : ℝ) / p)) * t ^ (n + 1) := by
      rw [← Real.rpow_natCast t (n + 1), ← Real.rpow_add ht]
      have h1 : t * t ^ ((n : ℝ) * (1 - 1 / p)) = t ^ ((1 : ℝ) + (n : ℝ) * (1 - 1 / p)) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      rw [h1]
      congr 1
      push_cast
      field_simp
      ring
    rw [abs_div, abs_div, abs_of_pos (pow_pos ht (n + 1)), abs_of_pos hden, div_div,
      div_le_iff₀ (mul_pos (pow_pos ht (n + 1)) hden)]
    calc |L| ≤ N * (1 + b) * (t * t ^ ((n : ℝ) * (1 - 1 / p))) := hL'
      _ = N * t ^ (-((n : ℝ) / p)) * (t ^ (n + 1) * (1 + b)) := by rw [hexp]; ring
  have dohrLmonoOpenBallAux_small : ∀ {n : ℕ} {p R κ : ℝ} {J : ℝ≥0∞}, 0 < p → 0 < R → 0 ≤ κ →
      (ENNReal.ofReal (R ^ (p - n)) * J) ^ (1 / p) ≤ ENNReal.ofReal κ →
        J ≠ ⊤ ∧ J.toReal ^ (1 / p) * R ^ (1 - (n : ℝ) / p) ≤ κ := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound
    intro n p R κ J hp0 hR hκ h
    have hRp : 0 < R ^ (p - n) := Real.rpow_pos_of_pos hR _
    have hp1 : 0 < 1 / p := by positivity
    have hJ : J ≠ ⊤ := by
      intro hJ
      rw [hJ, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hRp).ne', ENNReal.top_rpow_of_pos hp1,
        top_le_iff] at h
      exact ENNReal.ofReal_ne_top h
    refine ⟨hJ, ?_⟩
    have hJ' : J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ).symm
    rw [hJ', ← ENNReal.ofReal_mul hRp.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hRp.le ENNReal.toReal_nonneg) hp1.le,
      ENNReal.ofReal_le_ofReal_iff hκ] at h
    rw [Real.mul_rpow hRp.le ENNReal.toReal_nonneg, ← Real.rpow_mul hR.le] at h
    have he : (p - n) * (1 / p) = 1 - (n : ℝ) / p := by
      field_simp
    rw [he] at h
    linarith
  have dohrLmonoOpenBallAux_limit : ∀ (n : ℕ) {R Λ N β : ℝ}, 0 < R → β < 1 → 0 ≤ N →
      N * R ^ (1 - β) / (1 - β) ≤ Λ / 4 → 0 < Λ → Λ ≤ 1 →
      ∀ (a : ℕ → ℝ → ℝ) (I : ℕ → ℝ → ℝ) (a₀ m : ℝ → ℝ),
      (∀ k, ContinuousOn (a k) (Ioo 0 R)) →
      (∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-β)) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t))) →
      (∀ t, 0 < t → t < R → Tendsto (fun k => I k t) atTop (𝓝 (m t))) →
      (∀ k, MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n))
        (Ioo 0 R)) →
      ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧
        (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧
        Tendsto F (𝓝[>] 0) (𝓝 1) ∧
        MonotoneOn (fun r => F r * (r ^ n)⁻¹ * m r + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small
    intro n R Λ N β hR hβ1 hN hNR hΛ hΛ1 a I a₀ m hacont hab halim hIlim hmono
    -- the dominating function is integrable near `0`
    have hgint : ∀ ρ, IntervalIntegrable (fun t => N * t ^ (-β)) volume 0 ρ := fun ρ =>
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul N
    -- the bound passes to the limit
    have ha₀b : ∀ t, 0 < t → t < R → |a₀ t| ≤ N * t ^ (-β) := by
      intro t ht htR
      exact le_of_tendsto ((continuous_abs.tendsto _).comp (halim t ht htR))
        (Eventually.of_forall fun k => hab k t ht htR)
    -- measurability
    have hameas : ∀ k ρ, ρ < R → AEStronglyMeasurable (a k) (volume.restrict (Ioc 0 ρ)) := by
      intro k ρ hρR
      exact ((hacont k).mono (fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hρR⟩)).aestronglyMeasurable
        measurableSet_Ioc
    have ha₀meas : ∀ ρ, ρ < R → AEStronglyMeasurable a₀ (volume.restrict (Ioc 0 ρ)) := by
      intro ρ hρR
      refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => hameas k ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    have ha₀int : ∀ ρ, 0 ≤ ρ → ρ < R → IntegrableOn a₀ (Ioc 0 ρ) := by
      intro ρ hρ hρR
      have hg : IntegrableOn (fun t => N * t ^ (-β)) (Ioc 0 ρ) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ).mp (hgint ρ)
      refine hg.mono' (ha₀meas ρ hρR) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        rw [Real.norm_eq_abs]
        exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
    -- convergence of the integrals
    have hGlim : ∀ ρ, 0 < ρ → ρ < R →
        Tendsto (fun k => ∫ t in (0)..ρ, a k t) atTop (𝓝 (∫ t in (0)..ρ, a₀ t)) := by
      intro ρ hρ hρR
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => N * t ^ (-β)) ?_ ?_ (hgint ρ) ?_
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => hameas k ρ hρR
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun k => Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact hab k t ht.1 (lt_of_le_of_lt ht.2 hρR)
      · rw [uIoc_of_le hρ.le]
        exact Eventually.of_forall fun t ht => halim t ht.1 (lt_of_le_of_lt ht.2 hρR)
    set G : ℝ → ℝ := fun ρ => ∫ t in (0)..ρ, a₀ t with hGdef
    -- bound on `G`
    have hGb : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ N * ρ ^ (1 - β) / (1 - β) := by
      intro ρ hρ hρR
      have h1 : ‖∫ t in (0)..ρ, a₀ t‖ ≤ ∫ t in (0)..ρ, N * t ^ (-β) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hρ.le ?_ (hgint ρ)
        exact Eventually.of_forall fun t ht => by
          rw [Real.norm_eq_abs]
          exact ha₀b t ht.1 (lt_of_le_of_lt ht.2 hρR)
      have h2 : ∫ t in (0)..ρ, N * t ^ (-β) = N * ρ ^ (1 - β) / (1 - β) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h3 : -β + 1 = 1 - β := by ring
        rw [h3, Real.zero_rpow (by linarith), sub_zero, mul_div_assoc]
      rw [h2] at h1
      rw [← Real.norm_eq_abs]
      exact h1
    have hGΛ : ∀ ρ, 0 < ρ → ρ < R → |G ρ| ≤ Λ / 4 := by
      intro ρ hρ hρR
      refine (hGb ρ hρ hρR).trans (le_trans ?_ hNR)
      have h1β : 0 < 1 - β := by linarith
      apply div_le_div_of_nonneg_right _ h1β.le
      apply mul_le_mul_of_nonneg_left _ hN
      exact Real.rpow_le_rpow hρ.le hρR.le h1β.le
    set F : ℝ → ℝ := fun ρ => Real.exp (-G ρ) with hFdef
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · -- continuity
      intro ρ hρ
      have hρ1 : ρ < (ρ + R) / 2 := by linarith [hρ.2]
      have hρ1R : (ρ + R) / 2 < R := by linarith [hρ.2]
      have hρ0 : (0 : ℝ) ≤ (ρ + R) / 2 := by linarith [hρ.1]
      have hint : IntegrableOn a₀ (uIcc 0 ((ρ + R) / 2)) := by
        rw [uIcc_of_le hρ0, integrableOn_Icc_iff_integrableOn_Ioc]
        exact ha₀int _ hρ0 hρ1R
      have hc := intervalIntegral.continuousOn_primitive_interval hint
      have hmem : uIcc 0 ((ρ + R) / 2) ∈ 𝓝 ρ := by
        rw [uIcc_of_le hρ0]
        exact Icc_mem_nhds hρ.1 hρ1
      have hcG : ContinuousAt G ρ := hc.continuousAt hmem
      exact (Real.continuous_exp.continuousAt.comp hcG.neg).continuousWithinAt
    · intro r hr
      have h := hGΛ r hr.1 hr.2
      have h' := abs_le.mp h
      refine ⟨?_, ?_, ?_⟩
      · have h1 : |-G r| ≤ 1 := by rw [abs_neg]; linarith
        have h2 := Real.abs_exp_sub_one_le h1
        rw [abs_neg] at h2
        show |Real.exp (-G r) - 1| ≤ Λ
        linarith
      · show Real.exp (-Λ) ≤ Real.exp (-G r)
        exact Real.exp_le_exp.mpr (by linarith)
      · show Real.exp (-G r) ≤ Real.exp Λ
        exact Real.exp_le_exp.mpr (by linarith)
    · -- limit at `0`
      have hG0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
        have hlim : Tendsto (fun ρ : ℝ => N * ρ ^ (1 - β) / (1 - β)) (𝓝[>] 0) (𝓝 0) := by
          have h1 : Tendsto (fun ρ : ℝ => ρ ^ (1 - β)) (𝓝 0) (𝓝 0) := by
            have := Real.continuousAt_rpow_const 0 (1 - β) (Or.inr (by linarith))
            rw [ContinuousAt, Real.zero_rpow (by linarith)] at this
            exact this
          have h2 := (h1.const_mul N).div_const (1 - β)
          rw [mul_zero, zero_div] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        refine squeeze_zero_norm' ?_ hlim
        have : Ioo (0 : ℝ) R ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hR
        filter_upwards [this] with ρ hρ
        rw [Real.norm_eq_abs]
        exact hGb ρ hρ.1 hρ.2
      have := (Real.continuous_exp.tendsto (-0)).comp hG0.neg
      rw [neg_zero, Real.exp_zero] at this
      exact this
    · -- monotonicity
      have hΨlim : ∀ ρ ∈ Ioo 0 R, Tendsto
          (fun k => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) atTop
          (𝓝 (F ρ * (1 + m ρ / ρ ^ n))) := by
        intro ρ hρ
        have h1 := (Real.continuous_exp.tendsto _).comp (hGlim ρ hρ.1 hρ.2).neg
        have h2 := (hIlim ρ hρ.1 hρ.2).div_const (ρ ^ n)
        exact h1.mul (tendsto_const_nhds.add h2)
      intro σ hσ ρ hρ hσρ
      have h := le_of_tendsto_of_tendsto' (hΨlim σ hσ) (hΨlim ρ hρ) (fun k => hmono k hσ hρ hσρ)
      have e : ∀ r, F r * (r ^ n)⁻¹ * m r + F r - 1 = F r * (1 + m r / r ^ n) - 1 := by
        intro r
        ring
      show F σ * (σ ^ n)⁻¹ * m σ + F σ - 1 ≤ F ρ * (ρ ^ n)⁻¹ * m ρ + F ρ - 1
      rw [e σ, e ρ]
      linarith
  have dohr_lmono_open_ball_monotone : ∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (y : Amb n ℓ) (R Λ : ℝ), 0 < R → 0 < Λ → Λ ≤ 1 → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → (ENNReal.ofReal (R ^ (p - n)) * ∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → (∀ (φ : ℝ → ℝ) (ρ : ℝ), ContDiff ℝ 1 φ → Antitone φ → (∀ t : ℝ, t ≤ 1 / 2 → φ t = 1) → (∀ t : ℝ, 1 ≤ t → φ t = 0) → 0 < ρ → ρ < R → ∫ x, ((n : ℝ) * φ (‖x - y‖ / ρ) + ‖x - y‖ / ρ * deriv φ (‖x - y‖ / ρ)) ∂μ ≤ -∫ x, φ (‖x - y‖ / ρ) * inner ℝ (x - y) (H x) ∂μ) → ∃ F : ℝ → ℝ, ContinuousOn F (Ioo 0 R) ∧ (∀ r ∈ Ioo 0 R, |F r - 1| ≤ Λ ∧ Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ) ∧ Tendsto F (𝓝[>] 0) (𝓝 1) ∧ MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohrLmonoOpenBallAux_rpow_le
    intro n ℓ hn p hnp μ H y R Λ hR hΛ hΛ1 hμR hH hsmall hrad
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp1 : 1 < p := by linarith
    have hp0 : 0 < p := by linarith
    have hβ1 : (n : ℝ) / p < 1 := (div_lt_one hp0).mpr hnp
    have hκ : 0 ≤ (p - n) / (4 * p) * Λ :=
      mul_nonneg (div_nonneg (by linarith) (by linarith)) hΛ.le
    obtain ⟨hJ, hNR⟩ := dohrLmonoOpenBallAux_small hp0 hR hκ hsmall
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (∫⁻ x in closedBall y R, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) :=
      ⟨_, rfl⟩
    rw [← hNdef] at hNR
    have hN0 : 0 ≤ N := by
      rw [hNdef]
      exact Real.rpow_nonneg ENNReal.toReal_nonneg _
    have hNR' : N * R ^ (1 - (n : ℝ) / p) / (1 - (n : ℝ) / p) ≤ Λ / 4 := by
      have h1 : 0 < 1 - (n : ℝ) / p := by linarith
      rw [div_le_iff₀ h1]
      calc N * R ^ (1 - (n : ℝ) / p) ≤ (p - n) / (4 * p) * Λ := hNR
        _ = Λ / 4 * (1 - (n : ℝ) / p) := by
            field_simp
    have hNt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) ≤ N := by
      intro t htR
      rw [hNdef]
      exact Real.rpow_le_rpow ENNReal.toReal_nonneg
        (ENNReal.toReal_mono hJ (lintegral_mono_set (closedBall_subset_closedBall htR)))
        (by positivity)
    have hJt : ∀ t, t ≤ R → (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ) < ⊤ := fun t htR =>
      lt_of_le_of_lt (lintegral_mono_set (closedBall_subset_closedBall htR)) hJ.lt_top
    -- the cutoffs
    obtain ⟨φ, hφC, hφanti, hφone, hφzero, hφ01, hφlim⟩ := dohrLmonoOpenBallAux_cutoffs
    have hφc : ∀ k, Continuous (φ k) := fun k => (hφC k).continuous
    -- the cutoff quantities
    obtain ⟨I, hI⟩ : ∃ I : ℕ → ℝ → ℝ, ∀ k t, I k t = ∫ x, φ k (‖x - y‖ / t) ∂μ :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ → ℝ, ∀ k t, a k t =
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) / (1 + I k t / t ^ n) :=
      ⟨_, fun _ _ => rfl⟩
    have hzero_far : ∀ k t, 0 < t → ∀ x : Amb n ℓ, t ≤ ‖x - y‖ → φ k (‖x - y‖ / t) = 0 := by
      intro k t ht x hx
      exact hφzero k _ ((one_le_div ht).mpr hx)
    have hInn : ∀ k t, 0 ≤ I k t := fun k t => by
      rw [hI]
      exact integral_nonneg fun x => (hφ01 k _).1
    -- the uniform curvature bound, from the Hölder sibling
    have hab : ∀ k t, 0 < t → t < R → |a k t| ≤ N * t ^ (-((n : ℝ) / p)) := by
      intro k t ht htR
      have hμt : μ (closedBall y t) < ⊤ :=
        lt_of_le_of_lt (measure_mono (closedBall_subset_closedBall htR.le)) hμR
      have hHt : IntegrableOn H (closedBall y t) μ :=
        hH.mono_set (closedBall_subset_closedBall htR.le)
      have hhol : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * (∫⁻ x in closedBall y t, ‖H x‖ₑ ^ p ∂μ).toReal ^ (1 / p) *
            (∫ x, φ k (‖x - y‖ / t) ∂μ) ^ (1 - 1 / p) :=
        dohr_lmono_curvature_holder n ℓ p hp1 μ H (fun x => φ k (‖x - y‖ / t)) y t ht.le hμt hHt
          (hJt t htR.le)
          ((hφc k).comp (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
          (fun x => hφ01 k (‖x - y‖ / t)) (fun x hx => hzero_far k t ht x hx.le)
      have hL : |∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ| ≤
          t * N * I k t ^ (1 - 1 / p) := by
        refine hhol.trans ?_
        rw [← hI]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hNt t htR.le) ht.le)
          (Real.rpow_nonneg (hInn k t) _)
      rw [ha]
      exact dohrLmonoOpenBallAux_abound n hp1 ht hN0 (hInn k t) hL
    -- fixed-cutoff monotonicity, from the sibling
    have hfix : ∀ k, ContinuousOn (a k) (Ioo 0 R) ∧
        MonotoneOn (fun ρ => Real.exp (-∫ t in (0)..ρ, a k t) * (1 + I k ρ / ρ ^ n)) (Ioo 0 R) :=
      fun k => dohr_lmono_fixed_cutoff_monotone n ℓ μ H y (φ k) (I k) (a k) R N ((n : ℝ) / p) hβ1
        hμR hH (hφC k) (hφanti k) (hφzero k)
        (fun ρ h1 h2 => hrad (φ k) ρ (hφC k) (hφanti k) (hφone k) (hφzero k) h1 h2) (hI k) (ha k)
        (hab k)
    -- passage to the limit `k → ∞` under the integral sign
    obtain ⟨ν, hν⟩ : ∃ ν : Measure (Amb n ℓ), ν = μ.restrict (closedBall y R) := ⟨_, rfl⟩
    have hνfin : IsFiniteMeasure ν := by
      rw [hν]
      exact isFiniteMeasure_restrict.mpr hμR.ne
    have hHν : Integrable H ν := by
      rw [hν]
      exact hH
    have hout : ∀ t, t < R → ∀ x, x ∉ closedBall y R → t ≤ ‖x - y‖ := by
      intro t htR x hx
      have : R < ‖x - y‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
      linarith
    have hIν : ∀ k t, 0 < t → t < R → I k t = ∫ x, φ k (‖x - y‖ / t) ∂ν := by
      intro k t ht htR
      rw [hI, hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      exact hzero_far k t ht x (hout t htR x hx)
    have hLν : ∀ k t, 0 < t → t < R →
        (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν := by
      intro k t ht htR
      rw [hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro x hx
      rw [hzero_far k t ht x (hout t htR x hx), zero_mul]
    have hφpt : ∀ t, 0 < t → ∀ x : Amb n ℓ, Tendsto (fun k => φ k (‖x - y‖ / t)) atTop
        (𝓝 ((ball y t).indicator (fun _ => (1 : ℝ)) x)) := by
      intro t ht x
      by_cases hx : x ∈ ball y t
      · rw [indicator_of_mem hx]
        have hlt : ‖x - y‖ / t < 1 := by
          rw [div_lt_one ht]
          simpa [mem_ball, dist_eq_norm] using hx
        exact tendsto_const_nhds.congr' ((hφlim _ hlt).mono fun k hk => hk.symm)
      · rw [indicator_of_notMem hx]
        have hle : t ≤ ‖x - y‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hx
        have : (fun k => φ k (‖x - y‖ / t)) = fun _ => 0 :=
          funext fun k => hzero_far k t ht x hle
        rw [this]
        exact tendsto_const_nhds
    have hIlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => I k t) atTop (𝓝 ((μ (ball y t)).toReal)) := by
      intro t ht htR
      have hm : ∫ x, (ball y t).indicator (fun _ => (1 : ℝ)) x ∂ν = (μ (ball y t)).toReal := by
        rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one,
          Measure.real_def, hν, Measure.restrict_apply measurableSet_ball,
          inter_eq_left.mpr (ball_subset_closedBall.trans (closedBall_subset_closedBall htR.le))]
      rw [← hm]
      have hcongr : (fun k => I k t) = fun k => ∫ x, φ k (‖x - y‖ / t) ∂ν :=
        funext fun k => hIν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1)
        ?_ ?_
      · intro k
        exact ((hφc k).comp
          (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
      · intro k
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        exact (hφ01 k _).2
      · exact Eventually.of_forall fun x => hφpt t ht x
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ → ℝ, ∀ t, a₀ t =
        (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν) / t ^ (n + 1) /
          (1 + (μ (ball y t)).toReal / t ^ n) := ⟨_, fun _ => rfl⟩
    have hLlim : ∀ t, 0 < t → t < R →
        Tendsto (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) atTop
          (𝓝 (∫ x, (ball y t).indicator (fun x => inner ℝ (x - y) (H x)) x ∂ν)) := by
      intro t ht htR
      have hcongr : (fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) =
          fun k => ∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂ν :=
        funext fun k => hLν k t ht htR
      rw [hcongr]
      refine tendsto_integral_of_dominated_convergence (fun x => R * ‖H x‖) ?_
        (hHν.norm.const_mul R) ?_ ?_
      · intro k
        have h1 : AEStronglyMeasurable (fun x : Amb n ℓ => φ k (‖x - y‖ / t)) ν :=
          ((hφc k).comp
            (by fun_prop : Continuous fun x : Amb n ℓ => ‖x - y‖ / t)).aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun x : Amb n ℓ => inner ℝ (x - y) (H x)) ν :=
          continuous_inner.comp_aestronglyMeasurable
            ((by fun_prop : Continuous fun x : Amb n ℓ => x - y).aestronglyMeasurable.prodMk
              hHν.aestronglyMeasurable)
        exact h1.mul h2
      · intro k
        rw [hν, ae_restrict_iff' measurableSet_closedBall]
        refine Eventually.of_forall fun x hx => ?_
        have hxR : ‖x - y‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ01 k _).1]
        have hinner : ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ R * ‖H x‖ :=
          (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg _))
        calc φ k (‖x - y‖ / t) * ‖(inner ℝ (x - y) (H x) : ℝ)‖ ≤ 1 * (R * ‖H x‖) :=
              mul_le_mul (hφ01 k _).2 hinner (norm_nonneg _) zero_le_one
          _ = R * ‖H x‖ := one_mul _
      · refine Eventually.of_forall fun x => ?_
        have h := (hφpt t ht x).mul_const (inner ℝ (x - y) (H x))
        by_cases hx : x ∈ ball y t
        · simpa [indicator_of_mem hx] using h
        · simpa [indicator_of_notMem hx] using h
    have halim : ∀ t, 0 < t → t < R → Tendsto (fun k => a k t) atTop (𝓝 (a₀ t)) := by
      intro t ht htR
      have hm0 : 0 ≤ (μ (ball y t)).toReal := ENNReal.toReal_nonneg
      have hden : 1 + (μ (ball y t)).toReal / t ^ n ≠ 0 := by
        have := div_nonneg hm0 (pow_pos ht n).le
        linarith
      have hcongr : (fun k => a k t) = fun k =>
          (∫ x, φ k (‖x - y‖ / t) * inner ℝ (x - y) (H x) ∂μ) / t ^ (n + 1) /
            (1 + I k t / t ^ n) :=
        funext fun k => ha k t
      rw [hcongr, ha₀]
      exact ((hLlim t ht htR).div_const _).div
        (tendsto_const_nhds.add ((hIlim t ht htR).div_const _)) hden
    exact dohrLmonoOpenBallAux_limit n hR hβ1 hN0 hNR' hΛ hΛ1 a I a₀
      (fun t => (μ (ball y t)).toReal) (fun k => (hfix k).1) hab halim hIlim (fun k => (hfix k).2)
  have dohr_lmono_closedBall_of_ball : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), μ (closedBall y R) < ⊤ → ContinuousOn F (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1) (Ioo 0 R) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone
    intro n ℓ μ y R F hfin hFc hmono
    have hlim : ∀ r ∈ Ioo 0 R, Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (ball y r)).toReal + F r - 1)
        (𝓝[>] r) (𝓝 (F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1)) := by
      intro r hr
      have hfin' : μ (ball y ((r + R) / 2)) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hr.2]))))
      have hμ : Tendsto (fun s => μ (ball y s)) (𝓝[>] r) (𝓝 (μ (closedBall y r))) := by
        have h := tendsto_measure_biInter_gt (μ := μ) (s := fun s => ball y s) (a := r)
          (fun s _ => measurableSet_ball.nullMeasurableSet)
          (fun i j _ hij => ball_subset_ball hij)
          ⟨(r + R) / 2, by linarith [hr.2], hfin'⟩
        rw [biInter_gt_ball] at h
        exact h
      have hμr : Tendsto (fun s => (μ (ball y s)).toReal) (𝓝[>] r) (𝓝 (μ (closedBall y r)).toReal) :=
        (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hfin.ne
          (measure_mono (closedBall_subset_closedBall hr.2.le)))).comp hμ
      have hF : Tendsto F (𝓝[>] r) (𝓝 (F r)) :=
        ((hFc r hr).continuousAt (isOpen_Ioo.mem_nhds hr)).tendsto.mono_left nhdsWithin_le_nhds
      have hpow : Tendsto (fun s : ℝ => (s ^ n)⁻¹) (𝓝[>] r) (𝓝 ((r ^ n)⁻¹)) :=
        (((continuous_pow n).tendsto r).inv₀ (pow_ne_zero n hr.1.ne')).mono_left nhdsWithin_le_nhds
      exact (((hF.mul hpow).mul hμr).add hF).sub_const 1
    intro a ha b hb hab
    rcases hab.lt_or_eq with hab | rfl
    · have h1 : ∀ s ∈ Ioo b R, F a * (a ^ n)⁻¹ * (μ (closedBall y a)).toReal + F a - 1 ≤
          F s * (s ^ n)⁻¹ * (μ (ball y s)).toReal + F s - 1 := by
        intro s hs
        apply le_of_tendsto (hlim a ha)
        filter_upwards [Ioo_mem_nhdsGT (hab.trans hs.1)] with u hu
        exact hmono ⟨ha.1.trans hu.1, hu.2.trans hs.2⟩ ⟨hb.1.trans hs.1, hs.2⟩ hu.2.le
      apply ge_of_tendsto (hlim b hb)
      filter_upwards [Ioo_mem_nhdsGT hb.2] with s hs
      exact h1 s hs
    · exact le_rfl
  have dohr_lmono_density_of_monotone : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (y : Amb n ℓ) (R : ℝ) (F : ℝ → ℝ), 0 < R → μ (closedBall y R) < ⊤ → (∀ r ∈ Ioo 0 R, 0 ≤ F r) → Tendsto F (𝓝[>] 0) (𝓝 1) → MonotoneOn (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (Ioo 0 R) → ∃ t : ℝ, 0 ≤ t ∧ Tendsto (fun r : ℝ => μ (closedBall y r) / ENNReal.ofReal (unitBallVolume n * r ^ n)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal t)) ∧ Tendsto (fun r => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1) (𝓝[>] 0) (𝓝 (unitBallVolume n * t)) := by
    clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_radial_inequality dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit dohr_lmono_open_ball_monotone dohr_lmono_closedBall_of_ball
    intro n ℓ μ y R F hR hfin hF0 hF1 hmono
    set Φ := fun r : ℝ => F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal + F r - 1 with hΦ
    have hne : (Ioo (0:ℝ) R).Nonempty := ⟨R / 2, half_pos hR, half_lt_self hR⟩
    have hbdd : BddBelow (Φ '' Ioo 0 R) := by
      refine ⟨-1, ?_⟩
      rintro _ ⟨r, hr, rfl⟩
      have h1 := hF0 r hr
      have h2 : 0 ≤ F r * (r ^ n)⁻¹ * (μ (closedBall y r)).toReal :=
        mul_nonneg (mul_nonneg h1 (inv_nonneg.2 (pow_nonneg hr.1.le n))) ENNReal.toReal_nonneg
      simp only [hΦ]
      linarith
    set L := sInf (Φ '' Ioo 0 R) with hL
    have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := hmono.tendsto_nhdsWithin_Ioo_right hne hbdd
    set g := fun r : ℝ => (r ^ n)⁻¹ * (μ (closedBall y r)).toReal with hg_def
    have hg : Tendsto g (𝓝[>] 0) (𝓝 L) := by
      have h := ((hΦL.sub hF1).add_const 1).div hF1 one_ne_zero
      have heq : (fun r => (Φ r - F r + 1) / F r) =ᶠ[𝓝[>] 0] g := by
        filter_upwards [hF1.eventually (lt_mem_nhds (by norm_num : (1:ℝ) / 2 < 1))] with r hr
        have hFr : F r ≠ 0 := by linarith
        simp only [hΦ, hg_def]
        field_simp
        ring
      simpa using h.congr' heq
    have hL0 : 0 ≤ L := by
      apply ge_of_tendsto hg
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_nonneg (inv_nonneg.2 (pow_nonneg (le_of_lt hr) n)) ENNReal.toReal_nonneg
    have hω : 0 < unitBallVolume n := by
      unfold unitBallVolume
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by positivity))
    refine ⟨L / unitBallVolume n, div_nonneg hL0 hω.le, ?_, ?_⟩
    · have h := ENNReal.tendsto_ofReal (hg.div_const (unitBallVolume n))
      apply h.congr'
      filter_upwards [Ioo_mem_nhdsGT hR] with r hr
      have hmr : μ (closedBall y r) ≠ ⊤ :=
        ne_top_of_le_ne_top hfin.ne (measure_mono (closedBall_subset_closedBall hr.2.le))
      have hr0 : 0 < unitBallVolume n * r ^ n := mul_pos hω (pow_pos hr.1 n)
      rw [← ENNReal.ofReal_toReal hmr, ← ENNReal.ofReal_div_of_pos hr0]
      congr 1
      simp only [hg_def]
      field_simp
    · rw [mul_div_cancel₀ _ hω.ne']
      exact hΦL
  clear dohrLmonoRadialAux_hasFDerivAt_norm dohrLmonoRadialAux_hasFDerivAt dohrLmonoRadialAux_trace dohrLmonoRadialAux_trace_starProjection dohrLmonoRadialAux_inner_starProjection dohrLmonoRadialAux_integrable dohr_lmono_curvature_holder dohrLmonoFixedCutoffAux_phi_nonneg dohrLmonoFixedCutoffAux_deriv_zero dohrLmonoFixedCutoffAux_deriv_bound dohrLmonoFixedCutoffAux_hasDerivAt dohrLmonoFixedCutoffAux_npow dohr_lmono_fixed_cutoff_monotone dohrLmonoOpenBallAux_cutoffs dohrLmonoOpenBallAux_rpow_le dohrLmonoOpenBallAux_abound dohrLmonoOpenBallAux_small dohrLmonoOpenBallAux_limit
  intro n ℓ hn U hU V H p hp hH y R Λ hR hBR hrank hmeas hΛ hΛ1 hsmall
  -- `μ_V(B_R(y)) < ∞`: `B_R(y)` is a compact subset of `U` and `θ` is integrable on `M ∩ B_R(y)`.
  have hfin : V.weight (closedBall y R) < ⊤ := by
    rw [RectifiableVarifold.weight, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact (V.integrableOn_mult _ (isCompact_closedBall y R) hBR).setLIntegral_lt_top
  -- `H` is `μ_V`-integrable on the compact set `B_R(y) ⊆ U`.
  have hHint : IntegrableOn H (closedBall y R) V.weight :=
    hH.1.integrableOn_compact_subset hBR (isCompact_closedBall y R)
  obtain ⟨F, hFc, hFb, hF1, hmono⟩ :=
    dohr_lmono_open_ball_monotone n ℓ hn p hp V.weight H y R Λ hR hΛ hΛ1 hfin hHint hsmall
      (dohr_lmono_radial_inequality n ℓ U V H hH y R hBR hrank hmeas)
  have hmono' := dohr_lmono_closedBall_of_ball n ℓ V.weight y R F hfin hFc hmono
  obtain ⟨t, ht0, hdens, hlim⟩ := dohr_lmono_density_of_monotone n ℓ V.weight y R F hR hfin
    (fun r hr => (Real.exp_pos _).le.trans (hFb r hr).2.1) hF1 hmono'
  exact ⟨F, hFb, hF1, hmono', t, ht0, hdens, hlim⟩

theorem dohr_local_multiplicity_one : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ U, V.HasDensity ξ 1 → ∀ (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < R → closedBall ξ R ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → ∃ s > 0, s ≤ R ∧ (∀ᵐ x ∂V.weight, x ∈ ball ξ s → V.mult x = 1) ∧ (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ ball ξ s) (V.support ∩ ball ξ s)) = 0 ∧ V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) ∧ (∀ y ∈ ball ξ s ∩ V.support, V.HasDensity y 1) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ s → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (Q '' ((fun x => x - ξ) '' V.carrier) ∩ ball 0 ρ) (graphOver u {x | x ∈ ball (0 : Rn n) ρ ∧ ‖graphPoint x (u x)‖ < ρ})) = 0 := by
  intro n ℓ hn U hU V H p hp hH hLp hint ξ _hξU hξ R Q u hR hBR hu hgraph
  -- Unit density of the graph, hence finiteness and unit density of `spt V` in `B̆_R(ξ)`.
  obtain ⟨hfin, hdensS⟩ :=
    Submission.dohr_lmo_graph_support_density n ℓ V.support ξ R Q u hu hgraph
      (Submission.dohr_c1_graph_density_one n ℓ hn R u hu)
  -- On `B̆_R(ξ)` the tangent projections are measurable and project onto `n`-planes.
  obtain ⟨hmeasTP, hTP⟩ :=
    Submission.dohr_graph_tangent_planes n ℓ hn U hU V ξ R R Q u hR le_rfl hBR hu hgraph
  have hrank := Submission.dohr_lmo_graph_tangent_rank n ℓ U V ξ R Q u
    (ball_subset_closedBall.trans hBR) hu.differentiableOn_one hgraph hTP
  -- The monotonicity formula with a vanishing error, uniformly near `B̆_{R/2}(ξ)`.
  obtain ⟨t₁, ht₁, Λ, hΛ, hunif⟩ :=
    Submission.dohr_lmo_uniform_monotonicity_bound n ℓ U V H p ξ R hp hR hBR
      (Submission.dohr_local_monotonicity n ℓ hn U hU V H p hp hH) hrank hmeasTP
      (hLp _ (isCompact_closedBall ξ R) hBR)
  -- Since `Θ(ξ) = 1 < 2`, every density near `ξ` is `< 2`.
  obtain ⟨d, hd, hd2⟩ :=
    Submission.dohr_lmo_density_usc n ℓ U V ξ t₁ Λ ht₁ hΛ
      (hunif ξ (mem_ball_self (half_pos hR))) 1 zero_le_one hξ 2 one_lt_two
  -- The radius `s`.
  obtain ⟨s, hs, hsR2, hsd⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ R / 2 ∧ s ≤ d :=
    ⟨min (R / 2) d, lt_min (half_pos hR) hd, min_le_left _ _, min_le_right _ _⟩
  have hsR : s ≤ R := hsR2.trans (half_le_self hR.le)
  have hBs : closedBall ξ s ⊆ U := (closedBall_subset_closedBall hsR).trans hBR
  -- `Θ = θ` `μ_V`-a.e. on `B̆_s(ξ)`, and `Θ = 0` at `Hⁿ`-a.e. point of `spt V \ M` there.
  obtain ⟨hΘθ, hΘ0⟩ :=
    Submission.dohr_lmo_density_eq_mult_ae n ℓ U V ξ s hBs
      (hfin s (hsR2.trans_lt (half_lt_self hR)))
      (fun y hy => hdensS y ⟨hy.1, ball_subset_ball hsR hy.2⟩)
  -- Densities are unique.
  have huniq : ∀ (z : Amb n ℓ) (a b : ℝ), V.HasDensity z a → V.HasDensity z b →
      ENNReal.ofReal a = ENNReal.ofReal b := fun _ _ _ ha hb => tendsto_nhds_unique ha hb
  -- `Θ ≥ 1` at every point of `spt V ∩ B̆_s(ξ)`.
  have hge1 : ∀ y ∈ V.support ∩ ball ξ s, ∃ Θ : ℝ, 1 ≤ Θ ∧ V.HasDensity y Θ := by
    rintro y ⟨hyS, hys⟩
    have hyR2 : y ∈ ball ξ (R / 2) := ball_subset_ball hsR2 hys
    obtain ⟨Θy, hΘy0, hΘy, -⟩ := hunif y hyR2 t₁ ⟨ht₁, le_rfl⟩ y (mem_closedBall_self ht₁.le)
    refine ⟨Θy, not_lt.1 fun hlt => ?_, hΘy⟩
    obtain ⟨d', hd', hd'1⟩ :=
      Submission.dohr_lmo_density_usc n ℓ U V y t₁ Λ ht₁ hΛ (hunif y hyR2) Θy hΘy0 hΘy 1 hlt
    have hpos : V.weight (ball y d' ∩ ball ξ s) ≠ 0 := by
      have hyW : y ∈ V.weight.support := (show y ∈ U ∩ V.weight.support from hyS).2
      exact ((Measure.mem_support_iff_forall y).1 hyW _
        (Filter.inter_mem (ball_mem_nhds y hd') (isOpen_ball.mem_nhds hys))).ne'
    obtain ⟨z, ⟨hzd, hzs⟩, hzΘ, k, hk, hzk⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hΘθ.and hint))
    obtain ⟨Θ, hΘ1, hΘ⟩ := hd'1 z (ball_subset_closedBall hzd)
    have heq := huniq z _ _ (hzΘ hzs) hΘ
    rw [hzk] at heq
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (k : ℝ) :=
      ENNReal.one_le_ofReal.2 (by exact_mod_cast hk)
    rw [heq] at h1
    exact absurd (ENNReal.ofReal_lt_one.2 hΘ1) (not_lt.2 h1)
  -- Carrier and support agree up to an `Hⁿ`-null set on `B̆_s(ξ)`.
  have hsymm := Submission.dohr_lmo_carrier_support_null n ℓ U V (ball ξ s) measurableSet_ball
    (ball_subset_closedBall.trans hBs) hΘ0 hge1
  -- Multiplicity one, since `θ` is an integer `≥ 1` equal to a density `< 2`.
  have hmult1 : ∀ᵐ x ∂V.weight, x ∈ ball ξ s → V.mult x = 1 := by
    filter_upwards [hΘθ, hint] with x hxΘ hxk hxs
    obtain ⟨k, hk, hxk⟩ := hxk
    obtain ⟨Θ, hΘ2, hΘ⟩ := hd2 x (ball_subset_closedBall (ball_subset_ball hsd hxs))
    have heq := huniq x _ _ (hxΘ hxs) hΘ
    rw [hxk] at heq ⊢
    have hk2 : (k : ℝ) < 2 := by
      have h : ENNReal.ofReal (k : ℝ) < ENNReal.ofReal 2 := by
        rw [heq]; exact (ENNReal.ofReal_lt_ofReal_iff two_pos).2 hΘ2
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Nat.cast_nonneg k)).1 h
    have hk1 : k = 1 := by
      have : k < 2 := by exact_mod_cast hk2
      omega
    simp [hk1]
  -- `μ_V ⌞ B̆_s(ξ) = Hⁿ ⌞ (spt V ∩ B̆_s(ξ))`.
  have hweight :=
    Submission.dohr_lmo_weight_restrict_eq n ℓ U V (ball ξ s) measurableSet_ball hmult1 hsymm
  -- Density one at every point of `spt V ∩ B̆_s(ξ)`.
  have hdens1 : ∀ y ∈ ball ξ s ∩ V.support, V.HasDensity y 1 := by
    rintro y ⟨hys, hyS⟩
    have hlim := hdensS y ⟨hyS, ball_subset_ball hsR hys⟩
    have hδ : 0 < s - dist y ξ := sub_pos.2 (mem_ball.1 hys)
    unfold RectifiableVarifold.HasDensity
    rw [ENNReal.ofReal_one]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    have hsub : closedBall y r ⊆ ball ξ s := by
      intro z hz
      rw [mem_ball]
      calc dist z ξ ≤ dist z y + dist y ξ := dist_triangle _ _ _
        _ ≤ r + dist y ξ := by gcongr; exact mem_closedBall.1 hz
        _ < s := by linarith [hr.2]
    congr 1
    rw [← Measure.restrict_eq_self V.weight hsub, hweight,
      Measure.restrict_apply measurableSet_closedBall]
    congr 1
    ext z
    constructor
    · rintro ⟨hzS, hzr⟩
      exact ⟨hzr, hzS, hsub hzr⟩
    · rintro ⟨hzr, hzS, -⟩
      exact ⟨hzS, hzr⟩
  -- Transport of the null symmetric difference to graph coordinates.
  exact ⟨s, hs, hsR, hmult1, hsymm, hweight, hdens1,
    Submission.dohr_lmo_carrier_graph_symmDiff n ℓ V.carrier V.support ξ R s Q u hsR hgraph
      hsymm⟩

end Submission

/-- Simon Ch. 5, proof of Theorem 7.1 (p. 128, system (2)), vertical first variation: if
`Q(spt V - ξ)` is the graph of a `C¹` function `u` over `B̆_R(0)` and `μ_V = Hⁿ ⌞ spt V` on
`B̆_s(ξ)`, then `u` weakly solves the Euler–Lagrange system of the area integrand
`J(P) = √det(I + PᵀP)` with right-hand side `J(Du) ⟨(0, φ), F(x, u(x))⟩`, `F = Q ∘ h ∘ (ξ + Q⁻¹ ·)`,
on a ball `B̆_r(0)`; moreover the rigidly moved data `O = Q(U - ξ)` and `F` stay open and
locally `C^{q,α}`. -/
theorem Submission.dohr_vertical_euler_lagrange : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H h : Amb n ℓ → Amb n ℓ) (q : ℕ) (α : ℝ), V.HasGeneralizedMeanCurvature H → IsLocallyHolderCkα q α h U → (∀ᵐ x ∂V.weight, H x = h x) → ∀ (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → V.weight.restrict (ball ξ s) = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ ball ξ s) → IsOpen ((fun y => Q (y - ξ)) '' U) ∧ IsLocallyHolderCkα q α (fun z => Q (h (ξ + Q.symm z))) ((fun y => Q (y - ξ)) '' U) ∧ ∃ r > 0, r ≤ R ∧ (∀ x ∈ ball (0 : Rn n) r, graphPoint x (u x) ∈ (fun y => Q (y - ξ)) '' U) ∧ ∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∫ x in ball (0 : Rn n) r, fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in ball (0 : Rn n) r, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
  intro n ℓ hn U hU V H h q α hH hh hHh ξ s R Q u hs hsR hball hu hu0 hgraph hmeas
  -- Step 1: `O = Q(U - ξ)` is open and `F = Q ∘ h ∘ (ξ + Q⁻¹ ·)` is locally `C^{q,α}` on `O`.
  obtain ⟨hO, hF⟩ := Submission.dohr_vel_holder_rigid_transport n ℓ U hU h q α ξ Q hh
  refine ⟨hO, hF, ?_⟩
  have hR : 0 < R := lt_of_lt_of_le hs hsR
  have huR : ∀ x ∈ ball (0 : Rn n) R, DifferentiableAt ℝ u x := fun x hx =>
    ((hu.differentiableOn one_ne_zero) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hgp0 : graphPoint (0 : Rn n) (0 : Rn ℓ) = 0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i <;> simp [graphPoint]
  -- `pr` is the projection of `ℝ^{n+ℓ}` onto its first `n` coordinates: `pr (x, w) = x`.
  let pr : Amb n ℓ → Rn n := fun z => WithLp.toLp 2 (fun j : Fin n => WithLp.ofLp z (Fin.castAdd ℓ j))
  have hprG : ∀ (x : Rn n) (w : Rn ℓ), pr (graphPoint x w) = x := by
    intro x w
    simp [pr, graphPoint]
  -- Step 2: `G x = (x, u x)` is continuous at `0` with `G 0 = 0`; choose `r = min δ R` with
  -- `|G x| < s` on `B̆_r(0)`.
  have hGcont0 : ContinuousAt (fun z : Rn n => graphPoint z (u z)) 0 :=
    (Submission.dohr_vel_graph_fderiv n ℓ u 0 (huR 0 (mem_ball_self hR))).1.continuousAt
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hGcont0 s hs
  have hGs : ∀ x ∈ ball (0 : Rn n) (min δ R), ‖graphPoint x (u x)‖ < s := by
    intro x hx
    have hx' : dist x 0 < δ := lt_of_lt_of_le (mem_ball.mp hx) (min_le_left _ _)
    have := hδG hx'
    simpa [hu0, hgp0, dist_zero_right] using this
  refine ⟨min δ R, lt_min hδ hR, min_le_right _ _, ?_, ?_⟩
  · -- `G x = Q ((ξ + Q⁻¹ G x) - ξ)` with `ξ + Q⁻¹ G x ∈ B_s(ξ) ⊆ U`.
    intro x hx
    refine ⟨ξ + Q.symm (graphPoint x (u x)), ?_, ?_⟩
    · apply hball
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, LinearIsometryEquiv.norm_map]
      exact (hGs x hx).le
    · simp
  · intro φ hφ1 hφc hφr
    have hrR : min δ R ≤ R := min_le_right _ _
    have hucont : ContinuousOn u (ball 0 (min δ R)) := hu.continuousOn.mono (ball_subset_ball hrR)
    -- Step 4: the vertical test field `X = Q⁻¹ ψ (0, φ ∘ pr) ∘ Q(· - ξ)`, admissible in `U`.
    obtain ⟨X, hX1, hXc, hXs, hXval, hXder⟩ :=
      Submission.dohr_vel_vertical_test_field n ℓ ξ Q s (min δ R) u φ hs hucont hGs hφ1 hφc hφr
    have hGMC := hH.2 X hX1 hXc (hXs.trans (ball_subset_closedBall.trans hball))
    -- (iii), (Iso) and (Area): `μ_V`-integrals over `B̆_s(ξ)` become integrals over
    -- `D_s = {x ∈ B̆_R(0) : |G x| < s}` with the area element `J(Du)`.
    have hE := Submission.dohr_vel_graph_area_transport n ℓ U V ξ s R Q u hsR hu hgraph hmeas
    -- Step 3: `μ_V`-a.e. on `B̆_s(ξ)` the tangent plane is `Q⁻¹` of the graph's tangent plane.
    obtain ⟨-, hTP⟩ :=
      Submission.dohr_graph_tangent_planes n ℓ hn U hU V ξ s R Q u hs hsR hball hu hgraph
    have hDs_open : IsOpen {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} := by
      have hGc : ContinuousOn (fun z : Rn n => graphPoint z (u z)) (ball 0 R) := fun x hx =>
        (Submission.dohr_vel_graph_fderiv n ℓ u x (huR x hx)).1.continuousAt.continuousWithinAt
      have := hGc.isOpen_inter_preimage isOpen_ball (isOpen_ball : IsOpen (ball (0 : Amb n ℓ) s))
      convert this using 1
      ext x
      simp
    have hrDs : ball (0 : Rn n) (min δ R) ⊆
        {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s} :=
      fun x hx => ⟨ball_subset_ball hrR hx, hGs x hx⟩
    have hφzero : ∀ x ∉ ball (0 : Rn n) (min δ R), φ x = 0 ∧ fderiv ℝ φ x = 0 := by
      intro x hx
      have hxs : x ∉ tsupport φ := fun h' => hx (hφr h')
      refine ⟨image_eq_zero_of_notMem_tsupport hxs, ?_⟩
      by_contra hne
      exact hxs (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
    -- Step 6, left side: `div_M X` vanishes off `tsupport X ⊆ B̆_s(ξ)`.
    have hL1 : ∫ y, V.divM X y ∂V.weight = ∫ y in ball ξ s, V.divM X y ∂V.weight := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      have hyX : y ∉ tsupport X := fun h' => hy (hXs h')
      have h0 : fderiv ℝ X y = 0 := by
        by_contra hne
        exact hyX (support_fderiv_subset ℝ (Function.mem_support.mpr hne))
      simp [RectifiableVarifold.divM, h0]
    have hSigmeas : MeasurableSet (V.support ∩ ball ξ s) :=
      (hU.measurableSet.inter Measure.isClosed_support.measurableSet).inter measurableSet_ball
    have hae_supp : ∀ᵐ y ∂(V.weight.restrict (ball ξ s)), y ∈ V.support ∩ ball ξ s := by
      rw [hmeas]
      exact ae_restrict_mem hSigmeas
    -- `div_M X (y) = trace (DX(y) ∘ p_{P_y})` for `μ_V`-a.e. `y ∈ B̆_s(ξ)`, where
    -- `P_y = Q⁻¹ (range DG(x))` and `x = pr (Q (y - ξ))` is the unique graph parameter of `y`.
    have hL2 : ∫ y in ball ξ s, V.divM X y ∂V.weight =
        ∫ y in ball ξ s, LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X y).toLinearMap ∘ₗ
          (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
            (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) (pr (Q (y - ξ)))).toLinearMap)).starProjection.toLinearMap)
          ∂V.weight := by
      apply integral_congr_ae
      filter_upwards [hae_supp, ae_restrict_of_ae hTP] with y hy hyTP
      obtain ⟨hySig, hyb⟩ := hy
      have hTy : Q (y - ξ) ∈ graphOver u (ball 0 R) ∩ ball 0 R := by
        rw [← hgraph]
        refine ⟨⟨y - ξ, ⟨y, hySig, rfl⟩, rfl⟩, ?_⟩
        rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map, ← dist_eq_norm]
        exact lt_of_lt_of_le (mem_ball.mp hyb) hsR
      obtain ⟨⟨x, hxR, hxG⟩, -⟩ := hTy
      have hprx : pr (Q (y - ξ)) = x := by
        rw [← hxG]
        exact hprG x (u x)
      have hproj := hyTP hyb x hxR hxG.symm
      show LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X y).toLinearMap ∘ₗ (V.tangentProj y).toLinearMap) = _
      rw [hprx, hproj]
    -- Step 5: `J(Du) · trace (DX ∘ p_{P_y}) = DJ(Du)[Dφ]` on `D_s` (Jacobi's formula).
    have hL4 : ∀ x ∈ {x : Rn n | x ∈ ball (0 : Rn n) R ∧ ‖graphPoint x (u x)‖ < s},
        Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) *
          LinearMap.trace ℝ (Amb n ℓ) ((fderiv ℝ X (ξ + Q.symm (graphPoint x (u x)))).toLinearMap ∘ₗ
            (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range
              (fderiv ℝ (fun z : Rn n => graphPoint z (u z))
                (pr (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)))).toLinearMap)).starProjection.toLinearMap) =
        fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
            (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) := by
      intro x hx
      have hA := Submission.dohr_vel_graph_fderiv n ℓ u x (huR x hx.1)
      have hTx : pr (Q (ξ + Q.symm (graphPoint x (u x)) - ξ)) = x := by
        rw [add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply, hprG]
      rw [hTx, Submission.dohr_vel_graph_projection_trace n ℓ (fderiv ℝ u x) (fderiv ℝ φ x)
        (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x) Q
        (fderiv ℝ X (ξ + Q.symm (graphPoint x (u x)))) hA.2 (hXder x),
        (Submission.dohr_vel_area_integrand_fderiv n ℓ (fderiv ℝ u x)).2 (fderiv ℝ φ x)]
    -- The integrand vanishes on `D_s \ B̆_r(0)`, where `Dφ = 0`.
    have hLHS : ∫ y, V.divM X y ∂V.weight = ∫ x in ball (0 : Rn n) (min δ R),
        fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
            (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) := by
      rw [hL1, hL2, hE, setIntegral_congr_fun hDs_open.measurableSet hL4]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hDs_open.measurableSet hrDs ?_
      intro x hx
      rw [(hφzero x hx.2).2, map_zero]
    -- Step 7, right side: `H = h` `μ_V`-a.e., `⟨X, h⟩` vanishes off `B̆_s(ξ)`, and on the graph
    -- `⟨X, h⟩ = ⟨Q⁻¹ (0, φ), h⟩ = ⟨(0, φ), Q h⟩`.
    have hR1 : ∫ y, inner ℝ (X y) (H y) ∂V.weight = ∫ y, inner ℝ (X y) (h y) ∂V.weight :=
      integral_congr_ae (hHh.mono fun y hy => by simp only [hy])
    have hR2 : ∫ y, inner ℝ (X y) (h y) ∂V.weight =
        ∫ y in ball ξ s, inner ℝ (X y) (h y) ∂V.weight := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
      intro y hy
      have hyX : y ∉ tsupport X := fun h' => hy (hXs h')
      rw [image_eq_zero_of_notMem_tsupport hyX, inner_zero_left]
    have hR4 : ∀ x : Rn n,
        inner ℝ (X (ξ + Q.symm (graphPoint x (u x)))) (h (ξ + Q.symm (graphPoint x (u x)))) =
          inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
      intro x
      rw [hXval x, LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
    have hRHS : ∫ y, inner ℝ (X y) (H y) ∂V.weight = ∫ x in ball (0 : Rn n) (min δ R),
        Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n =>
          inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ)))
            (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) *
          inner ℝ (graphPoint 0 (φ x)) (Q (h (ξ + Q.symm (graphPoint x (u x))))) := by
      rw [hR1, hR2, hE]
      simp_rw [hR4]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hDs_open.measurableSet hrDs ?_
      intro x hx
      rw [(hφzero x hx.2).1, hgp0, inner_zero_left, mul_zero]
    -- Step 8: the first variation identity `∫ div_M X dμ_V = -∫ ⟨X, H⟩ dμ_V`.
    rw [← hLHS, ← hRHS]
    exact hGMC

/-- Iterated Caccioppoli along the chain `U_j = (d_u)^j (d_w W)` inside a class `S` closed under
directional derivatives: the energy of `D U_n` on `B_ρ(0)` is `O(ρ^{2α-2-n})`, hence zero. -/
theorem dohr_eb_sch_liou_chain_vanish : ∀ (n ℓ : ℕ) (α K C : ℝ) (S : Set (Rn n → Rn ℓ)) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 ≤ K → 0 ≤ C → (∀ V ∈ S, ContDiff ℝ 1 V) → (∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S) → (∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ, ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2) → W ∈ S → (∀ x : Rn n, ‖fderiv ℝ W x - fderiv ℝ W 0‖ ≤ K * ‖x‖ ^ α) → ∀ u w y : Rn n, fderiv ℝ ((fun g : Rn n → Rn ℓ => fun z => fderiv ℝ g z u)^[n] (fun z => fderiv ℝ W z w)) y = 0 := by
  intro n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS hgrowth u w y
  set D : (Rn n → Rn ℓ) → (Rn n → Rn ℓ) := fun g z => fderiv ℝ g z u with hD
  set U : ℕ → Rn n → Rn ℓ := fun j => D^[j] (fun z => fderiv ℝ W z w) with hU
  have hUS : ∀ j, U j ∈ S := by
    intro j
    induction j with
    | zero => exact hS2 W hWS w
    | succ j ih =>
      simp only [hU] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact hS2 _ ih u
  have hUsucc : ∀ j, U (j + 1) = fun z => fderiv ℝ (U j) z u := by
    intro j
    simp only [hU]
    rw [Function.iterate_succ_apply']
  set E : ℕ → ℝ → ℝ≥0∞ := fun j ρ => ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ (U j) x‖ₑ ^ 2 with hE
  set ω : ℝ := (volume (ball (0 : Rn n) 1)).toReal with hω
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hvol : ∀ r : ℝ, 0 < r → volume (ball (0 : Rn n) r) = ENNReal.ofReal (r ^ n * ω) := by
    intro r hr
    rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin,
      ENNReal.ofReal_mul (by positivity), hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  set e0 : ℝ := (n : ℝ) + 2 * α - 2 with he0
  set M0 : ℝ := C * K ^ 2 * ‖w‖ ^ 2 * (2 : ℝ) ^ ((n : ℝ) + 2 * α) * ω with hM0
  have hM0nn : 0 ≤ M0 := by positivity
  -- base estimate (Caccioppoli with c = DW(0) w)
  have hbase : ∀ ρ : ℝ, 0 < ρ → E 0 ρ ≤ ENNReal.ofReal (M0 * ρ ^ e0) := by
    intro ρ hρ
    have h1 := hS3 (U 0) (hUS 0) ρ hρ (fderiv ℝ W 0 w)
    refine h1.trans ?_
    have hc : 0 ≤ K * (2 * ρ) ^ α * ‖w‖ := by positivity
    have h2 : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2 ≤
        ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
      apply setLIntegral_mono measurable_const
      intro x hx
      have hx' : ‖x‖ < 2 * ρ := by simpa using hx
      have hle : ‖U 0 x - fderiv ℝ W 0 w‖ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
        simp only [hU, Function.iterate_zero, id]
        calc ‖fderiv ℝ W x w - fderiv ℝ W 0 w‖ = ‖(fderiv ℝ W x - fderiv ℝ W 0) w‖ := by simp
          _ ≤ ‖fderiv ℝ W x - fderiv ℝ W 0‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ K * ‖x‖ ^ α * ‖w‖ := by gcongr; exact hgrowth x
          _ ≤ K * (2 * ρ) ^ α * ‖w‖ := by
            gcongr
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 2)
    calc ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U 0 x - fderiv ℝ W 0 w‖ₑ ^ 2
        ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) := by
          gcongr
      _ = ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal ((K * (2 * ρ) ^ α * ‖w‖) ^ 2) *
            ENNReal.ofReal ((2 * ρ) ^ n * ω)) := by
          rw [setLIntegral_const, hvol (2 * ρ) (by positivity)]
      _ = ENNReal.ofReal (C / ρ ^ 2 * ((K * (2 * ρ) ^ α * ‖w‖) ^ 2 * ((2 * ρ) ^ n * ω))) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (M0 * ρ ^ e0) := by
          congr 1
          have h2ρ : (2 * ρ) ^ α = 2 ^ α * ρ ^ α := Real.mul_rpow (by norm_num) hρ.le
          have hpow : ρ ^ e0 = ρ ^ n * (ρ ^ α) ^ 2 / ρ ^ 2 := by
            rw [he0, Real.rpow_sub hρ, Real.rpow_add hρ, Real.rpow_natCast, Real.rpow_two,
              ← Real.rpow_natCast (ρ ^ α) 2, ← Real.rpow_mul hρ.le]
            push_cast; ring_nf
          have h2pow : (2 : ℝ) ^ ((n : ℝ) + 2 * α) = 2 ^ n * (2 ^ α) ^ 2 := by
            rw [Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.rpow_natCast ((2:ℝ) ^ α) 2,
              ← Real.rpow_mul (by norm_num)]
            push_cast; ring_nf
          rw [hpow, hM0, h2pow, h2ρ, mul_pow]
          field_simp
          ring
  -- iteration (Caccioppoli with c = 0)
  have hiter : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 0 < ρ →
      E j ρ ≤ ENNReal.ofReal (M * ρ ^ (e0 - 2 * (j : ℝ))) := by
    intro j
    induction j with
    | zero => exact ⟨M0, hM0nn, fun ρ hρ => by simpa using hbase ρ hρ⟩
    | succ j ih =>
      obtain ⟨M, hM, hb⟩ := ih
      refine ⟨C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)), by positivity, fun ρ hρ => ?_⟩
      have hstep : ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 ≤
          ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ) := by
        simp only [hE]
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_mono
        intro x
        simp only [hUsucc j, sub_zero]
        calc ‖fderiv ℝ (U j) x u‖ₑ ^ 2 ≤ (‖fderiv ℝ (U j) x‖ₑ * ‖u‖ₑ) ^ 2 := by
              gcongr; exact ContinuousLinearMap.le_opENorm _ _
          _ = ENNReal.ofReal (‖u‖ ^ 2) * ‖fderiv ℝ (U j) x‖ₑ ^ 2 := by
              rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; ring
      calc E (j + 1) ρ ≤ ENNReal.ofReal (C / ρ ^ 2) *
            ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖U (j + 1) x - 0‖ₑ ^ 2 :=
            hS3 _ (hUS (j + 1)) ρ hρ 0
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) * E j (2 * ρ)) := by
            gcongr
        _ ≤ ENNReal.ofReal (C / ρ ^ 2) * (ENNReal.ofReal (‖u‖ ^ 2) *
              ENNReal.ofReal (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ)))) := by
            gcongr; exact hb (2 * ρ) (by positivity)
        _ = ENNReal.ofReal (C / ρ ^ 2 * (‖u‖ ^ 2 * (M * (2 * ρ) ^ (e0 - 2 * (j : ℝ))))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (C * ‖u‖ ^ 2 * M * 2 ^ (e0 - 2 * (j : ℝ)) *
              ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ))) := by
            congr 1
            have h2ρ : (2 * ρ) ^ (e0 - 2 * (j : ℝ)) =
                2 ^ (e0 - 2 * (j : ℝ)) * ρ ^ (e0 - 2 * (j : ℝ)) :=
              Real.mul_rpow (by norm_num) hρ.le
            have hpow : ρ ^ (e0 - 2 * ((j + 1 : ℕ) : ℝ)) = ρ ^ (e0 - 2 * (j : ℝ)) / ρ ^ 2 := by
              rw [← Real.rpow_two, ← Real.rpow_sub hρ]; push_cast; ring_nf
            rw [h2ρ, hpow]
            field_simp
  -- decay: the energy of D U_n vanishes on every ball
  obtain ⟨M, hM, hb⟩ := hiter n
  have hneg : e0 - 2 * (n : ℝ) < 0 := by rw [he0]; linarith
  have hEn : ∀ ρ0 : ℝ, 0 < ρ0 → E n ρ0 = 0 := by
    intro ρ0 hρ0
    have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (M * ρ ^ (e0 - 2 * (n : ℝ)))) atTop
        (𝓝 0) := by
      have h1 : Tendsto (fun ρ : ℝ => ρ ^ (e0 - 2 * (n : ℝ))) atTop (𝓝 0) := by
        have := tendsto_rpow_neg_atTop (y := -(e0 - 2 * (n : ℝ))) (by linarith)
        simpa using this
      have h2 := h1.const_mul M
      rw [mul_zero] at h2
      have := ENNReal.tendsto_ofReal h2
      simpa using this
    have hle : E n ρ0 ≤ 0 := by
      refine ge_of_tendsto hlim (eventually_atTop.2 ⟨ρ0, fun ρ hρ => ?_⟩)
      exact (lintegral_mono_set (ball_subset_ball hρ)).trans (hb ρ (lt_of_lt_of_le hρ0 hρ))
    exact le_antisymm hle zero_le
  -- pointwise vanishing (continuity + open sets have positive measure)
  have hcont : Continuous (fderiv ℝ (U n)) := (hS1 _ (hUS n)).continuous_fderiv one_ne_zero
  have hρy : 0 < ‖y‖ + 1 := by positivity
  have hE0 := hEn (‖y‖ + 1) hρy
  have hmeas : Measurable (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) :=
    ((ENNReal.continuous_pow 2).comp hcont.enorm).measurable
  simp only [hE] at hE0
  rw [lintegral_eq_zero_iff hmeas] at hE0
  have hEq : EqOn (fun x => ‖fderiv ℝ (U n) x‖ₑ ^ 2) 0 (ball (0 : Rn n) (‖y‖ + 1)) :=
    Measure.eqOn_open_of_ae_eq hE0 isOpen_ball
      ((ENNReal.continuous_pow 2).comp hcont.enorm).continuousOn continuousOn_const
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + 1) := by simp
  have := hEq hy
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at this
  rw [← ofReal_norm, ENNReal.ofReal_eq_zero, norm_le_zero_iff] at this
  exact this
/-- 1-D lemma: a function with an explicit derivative chain ending in `0` (a polynomial of
degree `< m`) and sublinear growth `‖G₀ t − G₀ 0‖ ≤ C |t|^α`, `α < 1`, is constant. -/
theorem dohr_eb_sch_liou_poly_sublinear_const : ∀ (ℓ m : ℕ) (α C : ℝ) (G : ℕ → ℝ → Rn ℓ), α < 1 → (∀ j < m, ∀ t : ℝ, HasDerivAt (G j) (G (j + 1) t) t) → (∀ t : ℝ, G m t = 0) → (∀ t : ℝ, ‖G 0 t - G 0 0‖ ≤ C * |t| ^ α) → ∀ t : ℝ, G 0 t = G 0 0 := by
  intro ℓ m α C G hα hder hm hgrow
  -- Step 1: Taylor formula with zero remainder, by downward induction.
  have taylor : ∀ k i, i + k = m → ∀ t : ℝ,
      G i t = ∑ j ∈ Finset.range k, (t ^ j / (j.factorial : ℝ)) • G (i + j) 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi t
      simp only [add_zero] at hi
      subst hi
      simp [hm]
    | succ k ih =>
      intro i hi t
      have hIH : ∀ s : ℝ, G (i + 1) s =
          ∑ j ∈ Finset.range k, (s ^ j / (j.factorial : ℝ)) • G (i + 1 + j) 0 :=
        fun s => ih (i + 1) (by omega) s
      set P : ℝ → Rn ℓ := fun s =>
        ∑ j ∈ Finset.range (k + 1), (s ^ j / (j.factorial : ℝ)) • G (i + j) 0 with hP_def
      have hP : ∀ s : ℝ, HasDerivAt P (G (i + 1) s) s := by
        intro s
        rw [hIH s]
        have hsplit : P = fun s => (∑ j ∈ Finset.range k,
            (s ^ (j + 1) / ((j + 1).factorial : ℝ)) • G (i + (j + 1)) 0) + G i 0 := by
          funext s
          simp only [hP_def]
          rw [Finset.sum_range_succ']
          simp
        rw [hsplit]
        apply HasDerivAt.add_const
        apply HasDerivAt.fun_sum
        intro j _
        have h1 : HasDerivAt (fun s : ℝ => s ^ (j + 1) / ((j + 1).factorial : ℝ))
            (((j + 1 : ℕ) : ℝ) * s ^ j / ((j + 1).factorial : ℝ)) s := by
          have := (hasDerivAt_pow (j + 1) s).div_const ((j + 1).factorial : ℝ)
          simpa using this
        have h2 := h1.smul_const (G (i + (j + 1)) 0)
        have heq : (((j + 1 : ℕ) : ℝ) * s ^ j / ((j + 1).factorial : ℝ)) • G (i + (j + 1)) 0 =
            (s ^ j / (j.factorial : ℝ)) • G (i + 1 + j) 0 := by
          have hidx : i + (j + 1) = i + 1 + j := by omega
          rw [hidx]
          congr 1
          rw [Nat.factorial_succ]
          push_cast
          have : (j.factorial : ℝ) ≠ 0 := by positivity
          field_simp
        rw [← heq]
        exact h2
      have hGi : ∀ s : ℝ, HasDerivAt (G i) (G (i + 1) s) s := hder i (by omega)
      have hD : ∀ s : ℝ, HasDerivAt (fun s => G i s - P s) 0 s := by
        intro s
        have := (hGi s).sub (hP s)
        rwa [sub_self] at this
      have hconst := is_const_of_deriv_eq_zero (f := fun s => G i s - P s)
        (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) t 0
      have hP0 : P 0 = G i 0 := by
        simp only [hP_def]
        rw [Finset.sum_range_succ']
        simp
      simp only [hP0, sub_self] at hconst
      exact sub_eq_zero.mp hconst
  have hT : ∀ t : ℝ, G 0 t = ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) • G j 0 := by
    intro t
    simpa using taylor m 0 (by omega) t
  set a : ℕ → Rn ℓ := fun j => G j 0 with ha
  set β : ℝ := max α 0 with hβ
  have hβ1 : β < 1 := max_lt hα one_pos
  have hβ0 : 0 ≤ β := le_max_right _ _
  set Cp : ℝ := max C 0 with hCp
  -- Step 2: the top coefficient vanishes when all higher ones do.
  have core : ∀ J, 1 ≤ J → J < m → (∀ j, J < j → j < m → a j = 0) → a J = 0 := by
    intro J hJ1 hJm hhigh
    have hT' : ∀ t : ℝ, G 0 t =
        ∑ j ∈ Finset.range (J + 1), (t ^ j / (j.factorial : ℝ)) • a j := by
      intro t
      rw [hT t]
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hj hj'
        simp only [Finset.mem_range, not_lt] at hj hj'
        rw [show a j = 0 from hhigh j (by omega) hj, smul_zero]
    set B : ℝ := ∑ j ∈ Finset.range J, ‖a j‖ with hB
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    set M : ℝ := (J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B) with hM
    have hbound : ∀ t : ℝ, 1 ≤ t → ‖a J‖ ≤ M * t ^ (β - 1) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
      have hrest : ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ ≤
          t ^ (J - 1) * B := by
        calc ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖
            ≤ ∑ j ∈ Finset.range J, ‖(t ^ j / (j.factorial : ℝ)) • a j‖ := norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.range J, t ^ (J - 1) * ‖a j‖ := by
            apply Finset.sum_le_sum
            intro j hj
            simp only [Finset.mem_range] at hj
            rw [norm_smul]
            gcongr
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            calc t ^ j / (j.factorial : ℝ) ≤ t ^ j := by
                  apply div_le_self (by positivity)
                  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
              _ ≤ t ^ (J - 1) := pow_le_pow_right₀ ht (by omega)
          _ = t ^ (J - 1) * B := by rw [hB, Finset.mul_sum]
      have hsplit : G 0 t = (t ^ J / (J.factorial : ℝ)) • a J +
          ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j := by
        rw [hT' t, Finset.sum_range_succ, add_comm]
      have hgrow' : ‖G 0 t - G 0 0‖ ≤ Cp * t ^ β := by
        calc ‖G 0 t - G 0 0‖ ≤ C * |t| ^ α := hgrow t
          _ ≤ Cp * t ^ α := by
            rw [abs_of_pos ht0]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _)
          _ ≤ Cp * t ^ β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _))
              (le_max_right _ _)
      have hmain : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ ≤
          Cp * t ^ β + ‖G 0 0‖ + t ^ (J - 1) * B := by
        have h1 : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ = ‖(t ^ J / (J.factorial : ℝ)) • a J‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [h1]
        have h2 : (t ^ J / (J.factorial : ℝ)) • a J =
            (G 0 t - G 0 0) + G 0 0 -
              ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j := by
          rw [hsplit]; abel
        rw [h2]
        calc ‖(G 0 t - G 0 0) + G 0 0 -
              ∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖
            ≤ ‖(G 0 t - G 0 0) + G 0 0‖ +
                ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ := norm_sub_le _ _
          _ ≤ ‖G 0 t - G 0 0‖ + ‖G 0 0‖ +
                ‖∑ j ∈ Finset.range J, (t ^ j / (j.factorial : ℝ)) • a j‖ := by
              gcongr; exact norm_add_le _ _
          _ ≤ Cp * t ^ β + ‖G 0 0‖ + t ^ (J - 1) * B := by gcongr
      have htJ1 : (t ^ (J - 1) : ℝ) = t ^ ((J : ℝ) - 1) := by
        rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub hJ1]; ring
      have hpowJ : (t ^ J : ℝ) = t ^ ((J : ℝ) - 1 + β) * t ^ (1 - β) := by
        rw [← Real.rpow_add ht0, ← Real.rpow_natCast]; congr 1; ring
      have hA : Cp * t ^ β ≤ Cp * t ^ ((J : ℝ) - 1 + β) := by
        have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith))
          (le_max_right _ _)
      have hB' : ‖G 0 0‖ ≤ ‖G 0 0‖ * t ^ ((J : ℝ) - 1 + β) := by
        have : 1 ≤ t ^ ((J : ℝ) - 1 + β) := Real.one_le_rpow ht (by
          have : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
          linarith)
        nlinarith [norm_nonneg (G 0 0)]
      have hC' : t ^ (J - 1) * B ≤ t ^ ((J : ℝ) - 1 + β) * B := by
        rw [htJ1]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hB0
      have hsum : (t ^ J / (J.factorial : ℝ)) * ‖a J‖ ≤
          (Cp + ‖G 0 0‖ + B) * t ^ ((J : ℝ) - 1 + β) := by
        nlinarith [hmain, hA, hB', hC']
      have hfact : (0 : ℝ) < J.factorial := by positivity
      have htpos : 0 < t ^ ((J : ℝ) - 1 + β) := Real.rpow_pos_of_pos ht0 _
      have hneg : t ^ (β - 1) * t ^ (1 - β) = 1 := by
        rw [← Real.rpow_add ht0]; simp
      rw [hpowJ] at hsum
      have : t ^ (1 - β) * ‖a J‖ ≤ (J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B) := by
        have h3 : t ^ ((J : ℝ) - 1 + β) * (t ^ (1 - β) * ‖a J‖ / (J.factorial : ℝ)) ≤
            t ^ ((J : ℝ) - 1 + β) * (Cp + ‖G 0 0‖ + B) := by
          calc t ^ ((J : ℝ) - 1 + β) * (t ^ (1 - β) * ‖a J‖ / (J.factorial : ℝ))
              = t ^ ((J : ℝ) - 1 + β) * t ^ (1 - β) / (J.factorial : ℝ) * ‖a J‖ := by ring
            _ ≤ (Cp + ‖G 0 0‖ + B) * t ^ ((J : ℝ) - 1 + β) := hsum
            _ = t ^ ((J : ℝ) - 1 + β) * (Cp + ‖G 0 0‖ + B) := by ring
        have h4 := le_of_mul_le_mul_left h3 htpos
        rw [div_le_iff₀ hfact] at h4
        linarith
      calc ‖a J‖ = t ^ (β - 1) * (t ^ (1 - β) * ‖a J‖) := by
            rw [← mul_assoc, hneg, one_mul]
        _ ≤ t ^ (β - 1) * ((J.factorial : ℝ) * (Cp + ‖G 0 0‖ + B)) := by
            gcongr
        _ = M * t ^ (β - 1) := by rw [hM]; ring
    have hlim : Tendsto (fun t : ℝ => M * t ^ (β - 1)) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := 1 - β) (by linarith)
      have h' : (fun t : ℝ => t ^ (-(1 - β))) = fun t => t ^ (β - 1) := by
        funext t; congr 1; ring
      rw [h'] at h
      simpa using h.const_mul M
    have hle : ‖a J‖ ≤ 0 :=
      ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun t ht => hbound t ht⟩)
    exact norm_le_zero_iff.mp hle
  -- Step 3: downward induction, all coefficients of positive degree vanish.
  have hall : ∀ d, ∀ j, m - d ≤ j → 1 ≤ j → j < m → a j = 0 := by
    intro d
    induction d with
    | zero => intro j hj _ hjm; omega
    | succ d ih =>
      intro j hj hj1 hjm
      by_cases hjd : m - d ≤ j
      · exact ih j hjd hj1 hjm
      · exact core j hj1 hjm (fun j' hj' hj'm => ih j' (by omega) (by omega) hj'm)
  intro t
  rw [hT t, hT 0]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; simp
  · have := hall m j (by omega) hpos hj
    simp only [ha] at this
    simp [this]

end Submission

/-- Abstract Liouville theorem.  Let `S` be a class of `C¹` maps `ℝⁿ → ℝ^ℓ` that is closed under
directional derivatives and satisfies the Caccioppoli inequality on balls centred at `0`.  If
`W ∈ S` satisfies `‖DW(x) - DW(0)‖ ≤ K |x|^α` with `0 < α < 1`, then `DW` is constant. -/
theorem Submission.dohr_eb_sch_liou_abstract : ∀ (n ℓ : ℕ) (α K C : ℝ) (S : Set (Rn n → Rn ℓ)) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 ≤ K → 0 ≤ C → (∀ V ∈ S, ContDiff ℝ 1 V) → (∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S) → (∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ, ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤ ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2) → W ∈ S → (∀ x : Rn n, ‖fderiv ℝ W x - fderiv ℝ W 0‖ ≤ K * ‖x‖ ^ α) → ∀ x : Rn n, fderiv ℝ W x = fderiv ℝ W 0 := by
  intro n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS hgrowth x
  -- It suffices to show `DW(x) w = DW(0) w` for every `w`.
  ext1 w
  -- `D g = (z ↦ Dg(z) x)` is the directional derivative along `x`.
  set D : (Rn n → Rn ℓ) → (Rn n → Rn ℓ) := fun g z => fderiv ℝ g z x with hD
  -- `U_j := D^[j] (z ↦ DW(z) w)` lies in `S` by (S2), hence is `C¹` by (S1).
  have hUS : ∀ j : ℕ, (D^[j] (fun z => fderiv ℝ W z w)) ∈ S := by
    intro j
    induction j with
    | zero => exact hS2 W hWS w
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hS2 _ ih x
  -- `G_j(t) := U_j(t x)`; by the chain rule `G_j' = G_{j+1}`.
  let G : ℕ → ℝ → Rn ℓ := fun j t => (D^[j] (fun z => fderiv ℝ W z w)) (t • x)
  have hderiv : ∀ j < n + 1, ∀ t : ℝ, HasDerivAt (G j) (G (j + 1) t) t := by
    intro j _ t
    have hdiff : DifferentiableAt ℝ (D^[j] (fun z => fderiv ℝ W z w)) (t • x) :=
      ((hS1 _ (hUS j)).differentiable one_ne_zero) _
    have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h2 := hdiff.hasFDerivAt.comp_hasDerivAt t h1
    have h3 : G (j + 1) t = fderiv ℝ (D^[j] (fun z => fderiv ℝ W z w)) (t • x) x := by
      simp only [G]
      rw [Function.iterate_succ_apply']
    rw [h3]
    exact h2
  -- `G_{n+1}(t) = DU_n(t x) x = 0` by `chain_vanish` with `u := x`.
  have hzero : ∀ t : ℝ, G (n + 1) t = 0 := by
    intro t
    simp only [G]
    rw [Function.iterate_succ_apply']
    have := Submission.dohr_eb_sch_liou_chain_vanish n ℓ α K C S W hα hα1 hK hC hS1 hS2 hS3 hWS
      hgrowth x w (t • x)
    simp only [hD] at this ⊢
    rw [this]
    rfl
  -- Growth: `|G_0(t) - G_0(0)| ≤ (K |x|^α |w|) |t|^α`.
  have hgrow : ∀ t : ℝ, ‖G 0 t - G 0 0‖ ≤ (K * ‖x‖ ^ α * ‖w‖) * |t| ^ α := by
    intro t
    simp only [G, Function.iterate_zero, id, zero_smul]
    calc ‖fderiv ℝ W (t • x) w - fderiv ℝ W 0 w‖
        = ‖(fderiv ℝ W (t • x) - fderiv ℝ W 0) w‖ := by simp
      _ ≤ ‖fderiv ℝ W (t • x) - fderiv ℝ W 0‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * ‖t • x‖ ^ α) * ‖w‖ := by gcongr; exact hgrowth _
      _ = (K * ‖x‖ ^ α * ‖w‖) * |t| ^ α := by
        rw [norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
        ring
  -- `poly_sublinear_const` with `m := n + 1` gives `G_0(1) = G_0(0)`, i.e. `DW(x) w = DW(0) w`.
  have := Submission.dohr_eb_sch_liou_poly_sublinear_const ℓ (n + 1) α (K * ‖x‖ ^ α * ‖w‖) G
    hα1 hderiv hzero hgrow 1
  simpa [G] using this

namespace Submission

/-- Directional derivatives of `C²` global weak solutions of a constant-coefficient system are
again global weak solutions: translate the test function, differentiate the (identically zero)
translated integral under the integral sign, and identify `D(d_v V)` with `D²V(·) v` using the
symmetry of `D²V` (sibling `Submission.dohr_eb_sch_liou_snd_deriv_symm`). -/
theorem dohr_eb_sch_liou_dir_deriv_solution : ∀ (n ℓ : ℕ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (V : Rn n → Rn ℓ) (v : Rn n), ContDiff ℝ 2 V → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0) → ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ (fun y => fderiv ℝ V y v) x) (fderiv ℝ ζ x) = 0 := by
  intro n ℓ A V v hV hsol ζ hζ hζc
  -- Step 0: `DV` is `C¹`, `Dζ` is continuous with compact support.
  have hDV : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hDVd : Differentiable ℝ (fderiv ℝ V) := hDV.differentiable one_ne_zero
  have hDζcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  have hDζc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv (𝕜 := ℝ)
  -- `y ↦ D²V(y) v` is continuous (values in `L`)
  have hD2v : Continuous (fun y => fderiv ℝ (fderiv ℝ V) y v) :=
    (hDV.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  -- Step 1: translated equation `∫ A[DV(x + h v)][Dζ(x)] dx = 0` for every `h`, tested with
  -- `ζ(· - h v)` and translation invariance of Lebesgue measure.
  have hF : ∀ h : ℝ, ∫ x, A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x) = 0 := by
    intro h
    have h1 := hsol (fun x => ζ (x + (-(h • v)))) (hζ.comp (contDiff_id.add contDiff_const))
      (hζc.comp_homeomorph (Homeomorph.addRight (-(h • v))))
    have h2 : ∀ x, fderiv ℝ (fun x => ζ (x + (-(h • v)))) x = fderiv ℝ ζ (x + (-(h • v))) :=
      fun x => fderiv_comp_add_right _
    simp_rw [h2] at h1
    rw [← integral_add_right_eq_self
      (fun x => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x)) (-(h • v))]
    simpa [add_assoc] using h1
  -- Step 2: differentiation under the integral sign at `h = 0`, dominated on `|h| < 1` by
  -- `M⁺ |Dζ|`, where `M` bounds `‖A[D²V(·) v]‖` on the `|v|`-thickening of `tsupport Dζ`.
  set T := tsupport (fderiv ℝ ζ) with hTdef
  have hT : IsCompact T := hDζc
  have hT' : IsCompact (cthickening ‖v‖ T) := hT.cthickening
  have hAcont : Continuous (fun y => A (fderiv ℝ (fderiv ℝ V) y v)) := A.continuous.comp hD2v
  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ cthickening ‖v‖ T, ‖A (fderiv ℝ (fderiv ℝ V) y v)‖ ≤ M :=
    hT'.exists_bound_of_continuousOn (f := fun y => A (fderiv ℝ (fderiv ℝ V) y v))
      hAcont.continuousOn
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set F : ℝ → Rn n → ℝ := fun h x => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x) with hFdef
  set F' : ℝ → Rn n → ℝ := fun h x => A (fderiv ℝ (fderiv ℝ V) (x + h • v) v) (fderiv ℝ ζ x)
    with hFdef'
  have hFcont : ∀ h, Continuous (F h) := fun h =>
    (A.continuous.comp (hDV.continuous.comp (continuous_id.add continuous_const))).clm_apply
      hDζcont
  have hF'cont : ∀ h, Continuous (F' h) := fun h =>
    (hAcont.comp (continuous_id.add continuous_const)).clm_apply hDζcont
  have hzero_out : ∀ x, x ∉ T → fderiv ℝ ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hsuppF0 : HasCompactSupport (F 0) := by
    apply HasCompactSupport.intro hT
    intro x hx
    simp [hFdef, hzero_out x hx]
  have hbound_int : Integrable (fun x => M' * ‖fderiv ℝ ζ x‖) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul hDζcont.norm
    · apply HasCompactSupport.intro hT
      intro x hx
      simp [hzero_out x hx]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F)
    (F' := F') (x₀ := 0) (s := ball (0 : ℝ) 1)
    (bound := fun x => M' * ‖fderiv ℝ ζ x‖)
    (ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun h => (hFcont h).aestronglyMeasurable)
    ((hFcont 0).integrable_of_hasCompactSupport hsuppF0)
    (hF'cont 0).aestronglyMeasurable
    (Eventually.of_forall fun x h hh => by
      by_cases hx : x ∈ T
      · have hmem : x + h • v ∈ cthickening ‖v‖ T := by
          apply mem_cthickening_of_dist_le (x + h • v) x ‖v‖ T hx
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
          have : ‖h‖ ≤ 1 := (mem_ball_zero_iff.mp hh).le
          calc ‖h‖ * ‖v‖ ≤ 1 * ‖v‖ := by gcongr
            _ = ‖v‖ := one_mul _
        calc ‖F' h x‖ ≤ ‖A (fderiv ℝ (fderiv ℝ V) (x + h • v) v)‖ * ‖fderiv ℝ ζ x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ M' * ‖fderiv ℝ ζ x‖ := by
              gcongr; exact (hM _ hmem).trans (le_max_left _ _)
      · simp [hFdef', hzero_out x hx])
    hbound_int
    (Eventually.of_forall fun x h _ => by
      have h1 : HasDerivAt (fun h : ℝ => x + h • v) v h := by
        simpa using ((hasDerivAt_id h).smul_const v).const_add x
      have h2 : HasDerivAt (fun h : ℝ => fderiv ℝ V (x + h • v))
          (fderiv ℝ (fderiv ℝ V) (x + h • v) v) h :=
        (hDVd (x + h • v)).hasFDerivAt.comp_hasDerivAt h h1
      have h3 : HasDerivAt (fun h : ℝ => A (fderiv ℝ V (x + h • v)) (fderiv ℝ ζ x))
          (A (fderiv ℝ (fderiv ℝ V) (x + h • v) v) (fderiv ℝ ζ x)) h :=
        (A.flip (fderiv ℝ ζ x)).hasFDerivAt.comp_hasDerivAt h h2
      exact h3)
  -- Step 3: the translated integral is identically `0`, so its derivative at `0` vanishes.
  have hzero : (∫ x, F' 0 x) = 0 := by
    have hconst : (fun h : ℝ => ∫ x, F h x) = fun _ => 0 := funext hF
    have := hderiv.2
    rw [hconst] at this
    exact this.unique (hasDerivAt_const 0 0)
  -- Step 4: `D(d_v V)(x) = D²V(x) v`, by the chain rule and symmetry of the second derivative.
  have hsym : ∀ x, fderiv ℝ (fun y => fderiv ℝ V y v) x = fderiv ℝ (fderiv ℝ V) x v := by
    intro x
    have hd : HasFDerivAt (fun y => fderiv ℝ V y v)
        ((ContinuousLinearMap.apply ℝ (Rn ℓ) v).comp (fderiv ℝ (fderiv ℝ V) x)) x :=
      (ContinuousLinearMap.apply ℝ (Rn ℓ) v).hasFDerivAt.comp x (hDVd x).hasFDerivAt
    rw [hd.fderiv]
    refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    exact Submission.dohr_eb_sch_liou_snd_deriv_symm n ℓ V hV x w v
  -- Step 5: conclusion.
  simp_rw [hsym]
  simpa [hFdef'] using hzero
/-- Mollification of a `C^{1,α}` global weak solution: `V = φ_ε ⋆ W` is smooth, keeps the Hölder
constant, is `Kε^α`-close in `C¹`, and is again a global weak solution. -/
theorem dohr_eb_sch_liou_mollify : ∀ (n ℓ : ℕ) (α K ε : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W : Rn n → Rn ℓ), 0 < α → 0 ≤ K → 0 < ε → ContDiff ℝ 1 W → (∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ x) = 0) → ∃ V : Rn n → Rn ℓ, ContDiff ℝ (⊤ : ℕ∞) V ∧ (∀ x y : Rn n, ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ K * ‖x - y‖ ^ α) ∧ (∀ x : Rn n, ‖fderiv ℝ V x - fderiv ℝ W x‖ ≤ K * ε ^ α) ∧ ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0 := by
  intro n ℓ α K ε A W hα hK hε hW hhol hsol
  -- Step 1: mollifier φ := (∫ b)⁻¹ • b for the smooth bump b with radii ε/2 < ε
  let b : ContDiffBump (0 : Rn n) := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hb_cont : Continuous b := b.continuous
  have hb_nonneg : ∀ z, 0 ≤ b z := fun z => b.nonneg
  have hb_cpt : HasCompactSupport b := b.hasCompactSupport
  have hb_int : Integrable b := hb_cont.integrable_of_hasCompactSupport hb_cpt
  have hb_pos : 0 < ∫ z, b z := by
    rw [integral_pos_iff_support_of_nonneg (fun z => hb_nonneg z) hb_int, b.support_eq]
    exact measure_ball_pos volume _ hε
  set c : ℝ := (∫ z, b z)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr hb_pos
  set φ : Rn n → ℝ := fun z => c * b z with hφ_def
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_const.mul b.contDiff
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_nonneg : ∀ z, 0 ≤ φ z := fun z => mul_nonneg hc_pos.le (hb_nonneg z)
  have hφ_cpt : HasCompactSupport φ := hb_cpt.mul_left
  have hφ_int1 : ∫ z, φ z = 1 := by
    simp only [hφ_def]
    rw [integral_const_mul, hc_def, inv_mul_cancel₀ hb_pos.ne']
  have hφ_integrable : Integrable φ := hφ_cont.integrable_of_hasCompactSupport hφ_cpt
  have hφ_zero : ∀ z, ε ≤ ‖z‖ → φ z = 0 := by
    intro z hz
    have : z ∉ Function.support b := by
      rw [b.support_eq, mem_ball_zero_iff]
      exact not_lt.mpr hz
    simp only [hφ_def, Function.notMem_support.mp this, mul_zero]
  have hint : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Rn n → E),
      Continuous g → Integrable (fun z => φ z • g z) := by
    intro E _ _ g hg
    exact (hφ_cont.smul hg).integrable_of_hasCompactSupport (hφ_cpt.smul_right)
  have hDW_cont : Continuous (fderiv ℝ W) := hW.continuous_fderiv one_ne_zero
  have hW_diff : Differentiable ℝ W := hW.differentiable one_ne_zero
  -- Step 2: V := φ ⋆ W
  set V : Rn n → Rn ℓ := fun x => ∫ z, φ z • W (x - z) with hV_def
  have hVconv : V = MeasureTheory.convolution φ W (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x; simp [hV_def, convolution_def]
  -- Step 3: smoothness
  have hV_smooth : ContDiff ℝ (⊤ : ℕ∞) V := by
    rw [hVconv]
    exact hφ_cpt.contDiff_convolution_left _ hφ_smooth hW.continuous.locallyIntegrable
  -- Step 4: derivative formula DV(x) = ∫ φ(z) DW(x - z) dz
  have hVderiv : ∀ x0 : Rn n, fderiv ℝ V x0 = ∫ z, φ z • fderiv ℝ W (x0 - z) := by
    intro x0
    obtain ⟨Mw, hMw⟩ : ∃ Mw, ∀ y ∈ closedBall x0 (1 + ε), ‖fderiv ℝ W y‖ ≤ Mw :=
      (isCompact_closedBall x0 (1 + ε)).exists_bound_of_continuousOn (f := fderiv ℝ W)
        hDW_cont.continuousOn
    set Mw' := max Mw 0
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
      (F := fun x z => φ z • W (x - z)) (F' := fun x z => φ z • fderiv ℝ W (x - z))
      (x₀ := x0) (s := ball x0 1) (bound := fun z => Mw' * ‖φ z‖)
      (ball_mem_nhds x0 one_pos)
      (Eventually.of_forall fun x =>
        (hφ_cont.smul (hW.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (hint _ (hW.continuous.comp (continuous_const.sub continuous_id)))
      ((hφ_cont.smul (hDW_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun z x hx => by
        by_cases hz : φ z = 0
        · simp [hz]
        · have hz' : ‖z‖ < ε := by
            by_contra h'
            exact hz (hφ_zero z (not_lt.mp h'))
          have hmem : x - z ∈ closedBall x0 (1 + ε) := by
            rw [mem_closedBall, dist_eq_norm]
            have hx' : ‖x - x0‖ < 1 := by rw [← dist_eq_norm]; exact hx
            calc ‖x - z - x0‖ = ‖(x - x0) - z‖ := by congr 1; abel
              _ ≤ ‖x - x0‖ + ‖z‖ := norm_sub_le _ _
              _ ≤ 1 + ε := by linarith
          rw [norm_smul, mul_comm]
          gcongr
          exact (hMw _ hmem).trans (le_max_left _ _))
      ((hφ_integrable.norm).const_mul Mw')
      (Eventually.of_forall fun z x _ => by
        have h2 : HasFDerivAt (fun x => W (x - z)) (fderiv ℝ W (x - z)) x :=
          (hasFDerivAt_comp_sub z).mpr (hW_diff (x - z)).hasFDerivAt
        exact h2.const_smul (φ z))
    exact h.fderiv
  have hDWint : ∀ x : Rn n, Integrable (fun z => φ z • fderiv ℝ W (x - z)) := fun x =>
    hint _ (hDW_cont.comp (continuous_const.sub continuous_id))
  -- Step 5: Hölder bound
  have hhol' : ∀ x y : Rn n, ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ K * ‖x - y‖ ^ α := by
    intro x y
    rw [hVderiv x, hVderiv y, ← integral_sub (hDWint x) (hDWint y)]
    calc ‖∫ z, (φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W (y - z))‖
        ≤ ∫ z, φ z * (K * ‖x - y‖ ^ α) := by
          apply norm_integral_le_of_norm_le (hφ_integrable.mul_const _)
          refine Eventually.of_forall fun z => ?_
          have hs : φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W (y - z) =
              φ z • (fderiv ℝ W (x - z) - fderiv ℝ W (y - z)) := (smul_sub _ _ _).symm
          rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg z)]
          have := hhol (x - z) (y - z)
          rw [sub_sub_sub_cancel_right] at this
          exact mul_le_mul_of_nonneg_left this (hφ_nonneg z)
      _ = K * ‖x - y‖ ^ α := by rw [integral_mul_const, hφ_int1, one_mul]
  -- Step 6: approximation
  have happrox : ∀ x : Rn n, ‖fderiv ℝ V x - fderiv ℝ W x‖ ≤ K * ε ^ α := by
    intro x
    have hconst : fderiv ℝ W x = ∫ z, φ z • fderiv ℝ W x := by
      rw [integral_smul_const, hφ_int1, one_smul]
    rw [hVderiv x, hconst, ← integral_sub (hDWint x) (hφ_integrable.smul_const _)]
    calc ‖∫ z, (φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W x)‖
        ≤ ∫ z, φ z * (K * ε ^ α) := by
          apply norm_integral_le_of_norm_le (hφ_integrable.mul_const _)
          refine Eventually.of_forall fun z => ?_
          have hs : φ z • fderiv ℝ W (x - z) - φ z • fderiv ℝ W x =
              φ z • (fderiv ℝ W (x - z) - fderiv ℝ W x) := (smul_sub _ _ _).symm
          rw [hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφ_nonneg z)]
          by_cases hz : φ z = 0
          · simp [hz]
          · have hz' : ‖z‖ < ε := by
              by_contra h'
              exact hz (hφ_zero z (not_lt.mp h'))
            apply mul_le_mul_of_nonneg_left _ (hφ_nonneg z)
            calc ‖fderiv ℝ W (x - z) - fderiv ℝ W x‖ ≤ K * ‖(x - z) - x‖ ^ α := hhol _ _
              _ = K * ‖z‖ ^ α := by rw [sub_sub_cancel_left, norm_neg]
              _ ≤ K * ε ^ α := by
                apply mul_le_mul_of_nonneg_left _ hK
                exact Real.rpow_le_rpow (norm_nonneg _) hz'.le hα.le
      _ = K * ε ^ α := by rw [integral_mul_const, hφ_int1, one_mul]
  -- Step 7: weak equation (Fubini + translated test functions)
  have hweak : ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0 := by
    intro ζ hζ hζc
    have hDζcont : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
    have hDζc : HasCompactSupport (fderiv ℝ ζ) := hζc.fderiv (𝕜 := ℝ)
    have ha : ∀ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) =
        ∫ z, φ z * A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) := by
      intro x
      rw [hVderiv x]
      have := (A.flip (fderiv ℝ ζ x)).integral_comp_comm (hDWint x)
      simp only [ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul] at this
      exact this.symm
    set H : Rn n → Rn n → ℝ := fun x z => φ z * A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) with hH
    have hHcont : Continuous (Function.uncurry H) :=
      (hφ_cont.comp continuous_snd).mul
        ((A.continuous.comp (hDW_cont.comp (continuous_fst.sub continuous_snd))).clm_apply
          (hDζcont.comp continuous_fst))
    have hHsupp : HasCompactSupport (Function.uncurry H) := by
      apply HasCompactSupport.intro (hDζc.prod hφ_cpt)
      intro p hp
      simp only [mem_prod, not_and_or] at hp
      rcases hp with h | h
      · simp [H, Function.uncurry, image_eq_zero_of_notMem_tsupport h]
      · simp [H, Function.uncurry, image_eq_zero_of_notMem_tsupport h]
    have hHint : Integrable (Function.uncurry H) ((volume : Measure (Rn n)).prod volume) :=
      hHcont.integrable_of_hasCompactSupport (μ := (volume : Measure (Rn n)).prod volume) hHsupp
    have hswap := integral_integral_swap hHint
    have hinner : ∀ z, ∫ x, H x z = 0 := by
      intro z
      simp only [hH]
      rw [integral_const_mul]
      have h1 := hsol (fun x => ζ (x + z)) (hζ.comp (contDiff_id.add contDiff_const))
        (hζc.comp_homeomorph (Homeomorph.addRight z))
      have h2 : ∀ x, fderiv ℝ (fun x => ζ (x + z)) x = fderiv ℝ ζ (x + z) :=
        fun x => fderiv_comp_add_right _
      simp_rw [h2] at h1
      have h3 : ∫ x, A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x) =
          ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ (x + z)) := by
        rw [← integral_add_right_eq_self (fun x => A (fderiv ℝ W (x - z)) (fderiv ℝ ζ x)) z]
        simp
      rw [h3, h1, mul_zero]
    calc ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = ∫ x, ∫ z, H x z := by
          congr 1; funext x; exact ha x
      _ = ∫ z, ∫ x, H x z := hswap
      _ = 0 := by simp [hinner]
  exact ⟨V, hV_smooth, hhol', happrox, hweak⟩

/-- **Liouville theorem for constant-coefficient Legendre-elliptic systems** (Schauder estimate in
the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion, p. 127).  Let `A` be a
bilinear form on `L = L(ℝⁿ, ℝ^ℓ)` with `A[P][P] ≥ λ‖P‖²` and `|A[P][Q]| ≤ Λ‖P‖‖Q‖`, and let
`W ∈ C¹(ℝⁿ; ℝ^ℓ)` with `‖DW(x) − DW(y)‖ ≤ K‖x − y‖^α` (`0 < α < 1`) solve `∫ A[DW][Dζ] = 0` for
every `ζ ∈ C¹_c(ℝⁿ; ℝ^ℓ)`.  Then `DW` is constant.
Proof: let `C ≥ 0` be the Caccioppoli constant for `(λ, Λ)` and `K₊ = max K 0`.  The smooth global
solutions form a class `S` of `C¹` maps that is closed under directional derivatives and satisfies
the Caccioppoli inequality at `0`.  For `ε > 0` the mollification `W_ε` lies in `S`, has Hölder
constant `K₊` and satisfies `‖DW_ε − DW‖ ≤ K₊ ε^α`; the abstract Liouville theorem makes `DW_ε`
constant, so `‖DW(x) − DW(y)‖ ≤ 2 K₊ ε^α`, which tends to `0` as `ε → 0⁺`. -/
theorem dohr_eb_sch_liouville_const_coeff : ∀ (n ℓ : ℕ) (α lam Lam K : ℝ) (A : (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (W : Rn n → Rn ℓ), 0 < α → α < 1 → 0 < lam → (∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ A P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, |A P Q| ≤ Lam * ‖P‖ * ‖Q‖) → ContDiff ℝ 1 W → (∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ x, A (fderiv ℝ W x) (fderiv ℝ ζ x) = 0) → ∀ x y : Rn n, fderiv ℝ W x = fderiv ℝ W y := by
  intro n ℓ α lam Lam K A W hα hα1 hlam hcoer hbdd hW hhol hsol x y
  -- Step 0: the Caccioppoli constant `C ≥ 0` for `(λ, Λ)`; `K₊ = max K 0` is a Hölder constant.
  obtain ⟨C, hC0, hcacc⟩ := Submission.dohr_eb_sch_caccioppoli_const_coeff n ℓ lam Lam hlam
  obtain ⟨Kp, hKp, hKKp⟩ : ∃ Kp : ℝ, 0 ≤ Kp ∧ K ≤ Kp := ⟨max K 0, le_max_right K 0, le_max_left K 0⟩
  have hholp : ∀ x y : Rn n, ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ Kp * ‖x - y‖ ^ α := fun x y =>
    (hhol x y).trans (mul_le_mul_of_nonneg_right hKKp (Real.rpow_nonneg (norm_nonneg _) α))
  -- Step 1: the class `S` of smooth global solutions.
  let S : Set (Rn n → Rn ℓ) := {V | ContDiff ℝ (⊤ : ℕ∞) V ∧
    ∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∫ x, A (fderiv ℝ V x) (fderiv ℝ ζ x) = 0}
  -- (S1): smooth maps are `C¹`.
  have hS1 : ∀ V ∈ S, ContDiff ℝ 1 V := fun V hV => contDiff_infty.1 hV.1 1
  -- (S2): `x ↦ DV(x) v` is smooth, and a global solution by `dir_deriv_solution` (`V ∈ C²`).
  have hS2 : ∀ V ∈ S, ∀ v : Rn n, (fun x => fderiv ℝ V x v) ∈ S := by
    intro V hV v
    refine ⟨?_, Submission.dohr_eb_sch_liou_dir_deriv_solution n ℓ A V v
      (contDiff_infty.1 hV.1 2) hV.2⟩
    exact (hV.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  -- (S3): the Caccioppoli inequality centred at `0`, tested with all of `C¹_c(B_{2ρ}(0))`.
  have hS3 : ∀ V ∈ S, ∀ ρ : ℝ, 0 < ρ → ∀ c : Rn ℓ,
      ∫⁻ x in ball (0 : Rn n) ρ, ‖fderiv ℝ V x‖ₑ ^ 2 ≤
        ENNReal.ofReal (C / ρ ^ 2) * ∫⁻ x in ball (0 : Rn n) (2 * ρ), ‖V x - c‖ₑ ^ 2 :=
    fun V hV ρ hρ c => hcacc A V 0 ρ c hcoer hbdd hρ (hS1 V hV).contDiffOn
      fun ζ hζ hζc _ => hV.2 ζ hζ hζc
  -- Steps 2–5: the mollification `W_ε ∈ S` has constant derivative, so
  -- `‖DW(x) − DW(y)‖ ≤ ‖DW_ε(x) − DW(x)‖ + ‖DW_ε(y) − DW(y)‖ ≤ 2 K₊ ε^α`.
  have hε : ∀ ε : ℝ, 0 < ε → ‖fderiv ℝ W x - fderiv ℝ W y‖ ≤ 2 * (Kp * ε ^ α) := by
    intro ε hε
    obtain ⟨V, hVsm, hVhol, hVW, hVsol⟩ :=
      Submission.dohr_eb_sch_liou_mollify n ℓ α Kp ε A W hα hKp hε hW hholp hsol
    have hconst := Submission.dohr_eb_sch_liou_abstract n ℓ α Kp C S V hα hα1 hKp hC0 hS1 hS2
      hS3 ⟨hVsm, hVsol⟩ fun z => by simpa only [sub_zero] using hVhol z 0
    have hxy : fderiv ℝ V x = fderiv ℝ V y := (hconst x).trans (hconst y).symm
    calc ‖fderiv ℝ W x - fderiv ℝ W y‖ = dist (fderiv ℝ W x) (fderiv ℝ W y) :=
          (dist_eq_norm _ _).symm
      _ ≤ dist (fderiv ℝ W x) (fderiv ℝ V x) + dist (fderiv ℝ V x) (fderiv ℝ V y) +
          dist (fderiv ℝ V y) (fderiv ℝ W y) := dist_triangle4 _ _ _ _
      _ = ‖fderiv ℝ V x - fderiv ℝ W x‖ + ‖fderiv ℝ V y - fderiv ℝ W y‖ := by
          rw [hxy, dist_self, add_zero, dist_comm (fderiv ℝ W x), dist_eq_norm, dist_eq_norm]
      _ ≤ Kp * ε ^ α + Kp * ε ^ α := add_le_add (hVW x) (hVW y)
      _ = 2 * (Kp * ε ^ α) := (two_mul _).symm
  -- Step 6: let `ε → 0⁺`; `ε^α → 0^α = 0` as `α > 0`.
  have hlim : Tendsto (fun ε : ℝ => 2 * (Kp * ε ^ α)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ α) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hα.ne'] using
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
    simpa only [mul_zero] using ((h0.const_mul Kp).const_mul 2).mono_left nhdsWithin_le_nhds
  exact sub_eq_zero.mp (norm_le_zero_iff.mp
    (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hε)))

/-- **Blow-up Hölder estimate on the unit ball** (L. Simon's scaling argument; step 5 of the
Schauder estimate in the elliptic bootstrap for Simon Ch. 5, Theorem 7.1, second assertion).
For `0 < α < 1`, `λ > 0`, `M` and `δ > 0` there is `C_δ ≥ 0` such that every `C¹` weak solution `w`
on `B₁ = B̆₁(0)` of `∫ a(x)[Dw][Dζ] = ∫ Φ(x)[Dζ]`, with `a` Legendre-elliptic (`λ`), bounded and
`α`-Hölder (`M`), `Φ` `α`-Hölder (`G ≥ 0`), `|w| ≤ S` and `[Dw]_{α;B₁} ≤ K`, satisfies
`‖Dw(x) − Dw(y)‖ ≤ (δK + C_δ(S + G))|x − y|^α` on `B̆_{1/2}(0)`.
Proof by contradiction: violating data for `C_δ = k` are normalized by the difference quotient
`σ_k = ‖Dw_k(x_k) − Dw_k(y_k)‖/ρ_k^α`, `ρ_k = |x_k − y_k|`; the interpolation bound gives
`‖Dw_k‖ = o(σ_k)` on `B̆_{1/2}(0)`, hence `ρ_k → 0`. The blow-ups
`W_k(z) = (σ_k ρ_k^{1+α})⁻¹ (w_k(x_k + ρ_k z) − w_k(x_k) − ρ_k Dw_k(x_k) z)` solve rescaled systems
(rescale, zero mean, affine subtraction) with `DW_k(0) = 0`, `[DW_k]_α ≤ δ⁻¹`,
`‖DW_k((y_k − x_k)/ρ_k)‖ = 1` and errors tending to `0`.  The blow-up limit is a global solution of a
constant-coefficient Legendre system with `DW(0) = 0`, `‖DW(e₀)‖ = 1` and `[DW]_α ≤ δ⁻¹`, whose
gradient is constant by the Liouville theorem: a contradiction. -/
theorem dohr_eb_sch_blowup_holder_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M δ : ℝ, 0 < lam → 0 < δ → ∃ Cδ : ℝ, 0 ≤ Cδ ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ) (K S G : ℝ), 0 ≤ G → (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ G * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ S) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ (δ * K + Cδ * (S + G)) * ‖x - y‖ ^ α := by
  -- Norms, subtraction and continuity on `L(ℝⁿ, ℝ^ℓ)` and its dual need a deeper instance search.
  set_option maxSynthPendingDepth 3 in
  intro n ℓ _hn α hα hα1 lam M δ hlam hδ
  -- Step (0b): `α`-Hölder dependence on the base point gives continuity of linear forms in
  -- operator norm, and joint continuity of `(z, P, Q) ↦ b(z)[P][Q]`.
  have hcontL : ∀ (f : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, |f z P - f z' P| ≤ C * ‖z - z'‖ ^ α * ‖P‖) →
      ContinuousOn f U := by
    intro f U C hf z₀ hz₀
    have hb : ∀ z ∈ U, ‖f z - f z₀‖ ≤ |C| * ‖z - z₀‖ ^ α := by
      intro z hz
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (norm_nonneg _) α)) fun P => ?_
      rw [sub_apply, Real.norm_eq_abs]
      calc |f z P - f z₀ P| ≤ C * ‖z - z₀‖ ^ α * ‖P‖ := hf z hz z₀ hz₀ P
        _ ≤ |C| * ‖z - z₀‖ ^ α * ‖P‖ := by gcongr; exact le_abs_self C
    have hg : Continuous fun z : Rn n => |C| * ‖z - z₀‖ ^ α :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)
    have hg0 : Tendsto (fun z : Rn n => |C| * ‖z - z₀‖ ^ α) (𝓝[U] z₀)
        (𝓝 (|C| * ‖z₀ - z₀‖ ^ α)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hg0
    exact tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (eventually_nhdsWithin_of_forall hb) hg0)
  have hcontJ : ∀ (b : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ)
      (U : Set (Rn n)) (C : ℝ),
      (∀ z ∈ U, ∀ z' ∈ U, ∀ P Q : Rn n →L[ℝ] Rn ℓ,
        |b z P Q - b z' P Q| ≤ C * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖) →
      ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2) (U ×ˢ univ) := by
    intro b U C hb p₀ hp₀
    have hfr : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p₀.1 p.2.1 p.2.2 :=
      ((b p₀.1).continuous.comp continuous_snd.fst).clm_apply continuous_snd.snd
    have hg : Continuous fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ :=
      ((continuous_const.mul ((continuous_fst.sub continuous_const).norm.rpow_const
        fun _ => Or.inr hα.le)).mul continuous_snd.fst.norm).mul continuous_snd.snd.norm
    have hg0 : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖) (𝓝[U ×ˢ univ] p₀)
        (𝓝 (|C| * ‖p₀.1 - p₀.1‖ ^ α * ‖p₀.2.1‖ * ‖p₀.2.2‖)) := hg.continuousWithinAt
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, zero_mul, zero_mul] at hg0
    have hdiff : Tendsto (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
        b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2) (𝓝[U ×ˢ univ] p₀) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg0
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [Real.norm_eq_abs]
      calc |b p.1 p.2.1 p.2.2 - b p₀.1 p.2.1 p.2.2|
          ≤ C * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := hb _ hp.1 _ hp₀.1 _ _
        _ ≤ |C| * ‖p.1 - p₀.1‖ ^ α * ‖p.2.1‖ * ‖p.2.2‖ := by gcongr; exact le_abs_self C
    have hsum := hdiff.add hfr.continuousWithinAt
    simp only [sub_add_cancel, zero_add] at hsum
    exact hsum
  -- Step 1: contradiction hypothesis; for each `k` take violating data with `C_δ = k`.
  by_contra hcon
  push Not at hcon
  choose a Φ w K S G hG hell hbd haH hΦH hwS hwC hwH hweak x hx y hy hviol using
    fun k : ℕ => hcon (k : ℝ) (Nat.cast_nonneg k)
  have h0B : (0 : Rn n) ∈ ball (0 : Rn n) 1 := mem_ball_self one_pos
  have hx1 : ∀ k, x k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hx k)
  have hy1 : ∀ k, y k ∈ ball (0 : Rn n) 1 := fun k => ball_subset_ball (by norm_num) (hy k)
  have hxn : ∀ k, ‖x k‖ < 1 / 2 := fun k => mem_ball_zero_iff.mp (hx k)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ, ∀ k, ρ k = ‖x k - y k‖ := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℝ, ∀ k,
      N k = ‖fderiv ℝ (w k) (x k) - fderiv ℝ (w k) (y k)‖ := ⟨_, fun _ => rfl⟩
  have hviol' : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α < N k := fun k => by
    rw [hρ, hN]; exact hviol k
  -- `x_k ≠ y_k`, so `ρ_k > 0`; `K_k, S_k ≥ 0` and `N_k > 0`.
  have hρpos : ∀ k, 0 < ρ k := by
    intro k
    rw [hρ]
    refine norm_pos_iff.mpr fun hxy => ?_
    have h := hviol k
    rw [sub_eq_zero.mp hxy, sub_self, sub_self, norm_zero, norm_zero,
      Real.zero_rpow hα.ne', mul_zero] at h
    exact lt_irrefl 0 h
  have hραpos : ∀ k, 0 < ρ k ^ α := fun k => Real.rpow_pos_of_pos (hρpos k) α
  have hK0 : ∀ k, 0 ≤ K k := by
    intro k
    have h := hwH k (x k) (hx1 k) (y k) (hy1 k)
    rw [← hρ, ← hN] at h
    by_contra hneg
    push Not at hneg
    have h1 : K k * ρ k ^ α < 0 := mul_neg_of_neg_of_pos hneg (hραpos k)
    have h2 : 0 ≤ N k := by rw [hN]; exact norm_nonneg _
    linarith
  have hS0 : ∀ k, 0 ≤ S k := fun k => (norm_nonneg _).trans (hwS k 0 h0B)
  have hsplit : ∀ k : ℕ, (δ * K k + k * (S k + G k)) * ρ k ^ α =
      δ * K k * ρ k ^ α + (k * S k * ρ k ^ α + k * G k * ρ k ^ α) := fun k => by ring
  have hKρ : ∀ k, 0 ≤ δ * K k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg hδ.le (hK0 k)) (hραpos k).le
  have hSρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * S k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hS0 k)) (hραpos k).le
  have hGρ : ∀ k : ℕ, 0 ≤ (k : ℝ) * G k * ρ k ^ α := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (hG k)) (hραpos k).le
  have hNpos : ∀ k, 0 < N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k, hGρ k]
  have hKN : ∀ k, δ * K k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hSρ k, hGρ k]
  have hSN : ∀ k : ℕ, (k : ℝ) * S k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hGρ k]
  have hGN : ∀ k : ℕ, (k : ℝ) * G k * ρ k ^ α ≤ N k := fun k => by
    have := hviol' k; rw [hsplit] at this; linarith [hKρ k, hSρ k]
  -- Step 3: small gradients.  The interpolation bound with `t = k^{-1/2}` on `B̆_{1/2}(z)` gives
  -- `‖Dw_k(z)‖ ρ_k^α ≤ ε_k N_k` on `B̆_{1/2}(0)`, `ε_k = 2k^{-1/2} + k^{-α/2}/δ → 0`.
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ → ℝ, ∀ k : ℕ,
      ε k = 2 / Real.sqrt k + (Real.sqrt k)⁻¹ ^ α / δ := ⟨_, fun _ => rfl⟩
  have hinterp : ∀ k : ℕ, 5 ≤ k → ∀ z ∈ ball (0 : Rn n) (1 / 2),
      ‖fderiv ℝ (w k) z‖ * ρ k ^ α ≤ ε k * N k := by
    intro k hk z hz
    have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
    have hsq2 : 2 < Real.sqrt k := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hsq : 0 < Real.sqrt k := by linarith
    have ht : 0 < (Real.sqrt k)⁻¹ := inv_pos.mpr hsq
    have ht2 : (Real.sqrt k)⁻¹ < 1 / 2 := by
      rw [one_div]; exact inv_strictAnti₀ (by norm_num) hsq2
    have hsub : ball z (1 / 2) ⊆ ball (0 : Rn n) 1 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith [mem_ball_zero_iff.mp hz])
    have hI := Submission.dohr_eb_sch_fderiv_norm_interpolation n ℓ (w k) z (1 / 2)
      (Real.sqrt k)⁻¹ α (S k) (K k) hα.le (hK0 k) ht ht2 ((hwC k).mono hsub)
      (fun y' hy' => hwS k y' (hsub hy'))
      (fun y' hy' z' hz' => hwH k y' (hsub hy') z' (hsub hz'))
    have hkk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
    have e1 : 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α ≤ 2 / Real.sqrt k * N k := by
      rw [div_inv_eq_mul, div_mul_eq_mul_div, le_div_iff₀ hsq]
      calc 2 * S k * Real.sqrt k * ρ k ^ α * Real.sqrt k
          = 2 * ((Real.sqrt k * Real.sqrt k) * S k * ρ k ^ α) := by ring
        _ = 2 * ((k : ℝ) * S k * ρ k ^ α) := by rw [hkk]
        _ ≤ 2 * N k := by linarith [hSN k]
    have e2 : (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α ≤ (Real.sqrt k)⁻¹ ^ α / δ * N k := by
      have htα : 0 ≤ (Real.sqrt k)⁻¹ ^ α := Real.rpow_nonneg ht.le α
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      calc (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α * δ
          = (Real.sqrt k)⁻¹ ^ α * (δ * K k * ρ k ^ α) := by ring
        _ ≤ (Real.sqrt k)⁻¹ ^ α * N k := mul_le_mul_of_nonneg_left (hKN k) htα
    calc ‖fderiv ℝ (w k) z‖ * ρ k ^ α
        ≤ (2 * S k / (Real.sqrt k)⁻¹ + (Real.sqrt k)⁻¹ ^ α * K k) * ρ k ^ α :=
          mul_le_mul_of_nonneg_right hI (hραpos k).le
      _ = 2 * S k / (Real.sqrt k)⁻¹ * ρ k ^ α + (Real.sqrt k)⁻¹ ^ α * K k * ρ k ^ α := by ring
      _ ≤ 2 / Real.sqrt k * N k + (Real.sqrt k)⁻¹ ^ α / δ * N k := add_le_add e1 e2
      _ = ε k * N k := by rw [hε]; ring
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have hinv : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun k : ℕ => 2 / Real.sqrt k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.const_mul 2
    have h2 : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹ ^ α / δ) atTop (𝓝 0) := by
      have h3 := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp hinv).div_const δ
      rw [Real.zero_rpow hα.ne', zero_div] at h3
      exact h3
    have h4 := h1.add h2
    rw [add_zero] at h4
    exact h4.congr fun k => (hε k).symm
  -- Step 4: the scale tends to `0`: `ρ_k^α = N_k/σ_k ≤ 2ε_k`.
  have hρα_le : ∀ k, 5 ≤ k → ρ k ^ α ≤ 2 * ε k := by
    intro k hk
    have h1 := hinterp k hk (x k) (hx k)
    have h2 := hinterp k hk (y k) (hy k)
    have h3 : N k ≤ ‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖ := by
      rw [hN]; exact norm_sub_le _ _
    have h4 : N k * ρ k ^ α ≤ N k * (2 * ε k) := by
      calc N k * ρ k ^ α
          ≤ (‖fderiv ℝ (w k) (x k)‖ + ‖fderiv ℝ (w k) (y k)‖) * ρ k ^ α :=
            mul_le_mul_of_nonneg_right h3 (hραpos k).le
        _ = ‖fderiv ℝ (w k) (x k)‖ * ρ k ^ α + ‖fderiv ℝ (w k) (y k)‖ * ρ k ^ α := by ring
        _ ≤ ε k * N k + ε k * N k := add_le_add h1 h2
        _ = N k * (2 * ε k) := by ring
    exact le_of_mul_le_mul_left h4 (hNpos k)
  have hραt : Tendsto (fun k => ρ k ^ α) atTop (𝓝 0) := by
    have h2ε : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hεt.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun k => (hραpos k).le) ?_ h2ε
    filter_upwards [eventually_ge_atTop 5] with k hk using hρα_le k hk
  have hρt : Tendsto ρ atTop (𝓝 0) := by
    have h1 := (Real.continuousAt_rpow_const 0 α⁻¹ (Or.inr (inv_nonneg.mpr hα.le))).tendsto.comp
      hραt
    rw [Real.zero_rpow (inv_ne_zero hα.ne')] at h1
    exact h1.congr fun k => Real.rpow_rpow_inv (hρpos k).le hα.ne'
  have hρhalf : ∀ᶠ k in atTop, ρ k < 1 / 2 := hρt.eventually (Iio_mem_nhds (by norm_num))
  -- Step 5: the blow-up sequence on `D_k = B̆_{R_k}(0)`, `R_k = 1/(2ρ_k)`.
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, ∀ k, s k = (ρ k * N k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ → ℝ, ∀ k, R k = (2 * ρ k)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ → (Rn n →L[ℝ] Rn ℓ), ∀ k,
      P₀ k = ρ k • fderiv ℝ (w k) (x k) := ⟨_, fun _ => rfl⟩
  obtain ⟨ah, hah⟩ : ∃ ah : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ,
      ∀ k z, ah k z = a k (x k + ρ k • z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → Rn n → Rn ℓ, ∀ k,
      W k = fun z => s k • (w k (x k + ρ k • z) - w k (x k) - P₀ k z) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, ∀ k z,
      Ψ k z = s k • ((ρ k • Φ k (x k + ρ k • z) - ρ k • Φ k (x k)) -
        (ah k z (P₀ k) - a k (x k) (P₀ k))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → Rn n, ∀ k, e k = (ρ k)⁻¹ • (y k - x k) := ⟨_, fun _ => rfl⟩
  have hspos : ∀ k, 0 < s k := fun k => by
    rw [hs]; exact inv_pos.mpr (mul_pos (hρpos k) (hNpos k))
  have hsρ : ∀ k, s k * ρ k = (N k)⁻¹ := fun k => by
    rw [hs, mul_inv, mul_comm (ρ k)⁻¹, mul_assoc, inv_mul_cancel₀ (hρpos k).ne', mul_one]
  have hRpos : ∀ k, 0 < R k := fun k => by
    rw [hR]; exact inv_pos.mpr (mul_pos two_pos (hρpos k))
  have hρR : ∀ k, ρ k * R k = 1 / 2 := fun k => by
    rw [hR, mul_inv, ← mul_assoc, mul_comm (ρ k), mul_assoc, mul_inv_cancel₀ (hρpos k).ne',
      mul_one, one_div]
  have hmap : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), x k + ρ k • z ∈ ball (0 : Rn n) 1 := by
    intro k z hz
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖x k + ρ k • z‖ ≤ ‖x k‖ + ‖ρ k • z‖ := norm_add_le _ _
      _ = ‖x k‖ + ρ k * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg (hρpos k).le]
      _ < 1 / 2 + ρ k * R k := add_lt_add (hxn k) (mul_lt_mul_of_pos_left hz (hρpos k))
      _ = 1 := by rw [hρR k]; norm_num
  have hscale : ∀ k (z z' : Rn n),
      ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α = ρ k ^ α * ‖z - z'‖ ^ α := by
    intro k z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (hρpos k).le,
      Real.mul_rpow (hρpos k).le (norm_nonneg _)]
  -- The rescaled maps `w_k(x_k + ρ_k ·)` solve the rescaled system on `D_k` (sibling rescale).
  have hres := fun k => Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ (a k) (Φ k) (w k)
    (ball 0 1) (x k) 0 (ρ k) (R k) (hρpos k) isOpen_ball
    (by
      rw [smul_zero, add_zero, hρR k]
      exact ball_subset_ball' (by rw [dist_zero_right]; linarith [hxn k]))
    (hwC k) (hweak k)
  -- Step (0b) for the rescaled coefficients.
  have hJ : ∀ k, ContinuousOn (fun p : Rn n × (Rn n →L[ℝ] Rn ℓ) × (Rn n →L[ℝ] Rn ℓ) =>
      ah k p.1 p.2.1 p.2.2) (ball (0 : Rn n) (R k) ×ˢ univ) := by
    intro k
    refine hcontJ (ah k) (ball 0 (R k)) (M * ρ k ^ α) fun z hz z' hz' P Q => ?_
    rw [hah, hah]
    calc |a k (x k + ρ k • z) P Q - a k (x k + ρ k • z') P Q|
        ≤ M * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖ * ‖Q‖ :=
          haH k _ (hmap k z hz) _ (hmap k z' hz') P Q
      _ = M * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := by rw [hscale]; ring
  have hΘc : ∀ k, ContinuousOn (fun z => ρ k • Φ k (x k + ρ k • z)) (ball (0 : Rn n) (R k)) := by
    intro k
    refine hcontL _ (ball 0 (R k)) (ρ k * G k * ρ k ^ α) fun z hz z' hz' P => ?_
    simp only [smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (hρpos k)]
    calc ρ k * |Φ k (x k + ρ k • z) P - Φ k (x k + ρ k • z') P|
        ≤ ρ k * (G k * ‖(x k + ρ k • z) - (x k + ρ k • z')‖ ^ α * ‖P‖) :=
          mul_le_mul_of_nonneg_left (hΦH k _ (hmap k z hz) _ (hmap k z' hz') P) (hρpos k).le
      _ = ρ k * G k * ρ k ^ α * ‖z - z'‖ ^ α * ‖P‖ := by rw [hscale]; ring
  -- Step 6: the blow-ups solve the rescaled system with error `Ψ_k`
  -- (sibling zero mean and child `weak_eq_sub_affine`).
  have hsub := fun k => Submission.dohr_eb_sch_bu_weak_eq_sub_affine n ℓ (ah k)
    (fun z => ρ k • Φ k (x k + ρ k • z)) (fun z => w k (x k + ρ k • z)) (ball 0 (R k))
    (a k (x k)) (ρ k • Φ k (x k)) (P₀ k) (w k (x k)) (s k) isOpen_ball (hJ k) (hΘc k)
    (hres k).1 (fun ζ hζ hζc hζs => by simpa only [hah] using (hres k).2.2 ζ hζ hζc hζs)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
    (fun ζ hζ hζc => Submission.dohr_eb_sch_integral_clm_fderiv_eq_zero n ℓ _ ζ hζ hζc)
  have hWC : ∀ k, ContDiffOn ℝ 1 (W k) (ball (0 : Rn n) (R k)) := fun k => by
    rw [hW k]; exact (hsub k).1
  have hDW : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k),
      fderiv ℝ (W k) z = s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) := by
    intro k z hz
    rw [hW k, (hsub k).2.1 z hz, (hres k).2.1 z hz]
  have hW0 : ∀ k, W k 0 = 0 := fun k => by
    rw [hW k]; simp
  have hDW0 : ∀ k, fderiv ℝ (W k) 0 = 0 := fun k => by
    rw [hDW k 0 (mem_ball_self (hRpos k)), hP₀, smul_zero, add_zero, sub_self, smul_zero]
  have hWH : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ‖fderiv ℝ (W k) z - fderiv ℝ (W k) z'‖ ≤ δ⁻¹ * ‖z - z'‖ ^ α := by
    intro k z hz z' hz'
    rw [hDW k z hz, hDW k z' hz']
    have h1 : s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z) - P₀ k) -
        s k • (ρ k • fderiv ℝ (w k) (x k + ρ k • z') - P₀ k) =
        (s k * ρ k) • (fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')) := by
      rw [← smul_sub, sub_sub_sub_cancel_right, ← smul_sub, smul_smul]
    rw [h1, norm_smul, Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ]
    have h2 := hwH k _ (hmap k z hz) _ (hmap k z' hz')
    rw [hscale] at h2
    have h3 : (N k)⁻¹ * (K k * ρ k ^ α) ≤ δ⁻¹ := by
      rw [inv_mul_le_iff₀ (hNpos k), le_mul_inv_iff₀ hδ]
      calc K k * ρ k ^ α * δ = δ * K k * ρ k ^ α := by ring
        _ ≤ N k := hKN k
    calc (N k)⁻¹ * ‖fderiv ℝ (w k) (x k + ρ k • z) - fderiv ℝ (w k) (x k + ρ k • z')‖
        ≤ (N k)⁻¹ * (K k * (ρ k ^ α * ‖z - z'‖ ^ α)) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (hNpos k).le)
      _ = (N k)⁻¹ * (K k * ρ k ^ α) * ‖z - z'‖ ^ α := by ring
      _ ≤ δ⁻¹ * ‖z - z'‖ ^ α := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) α)
  -- Bounds for the frozen and rescaled coefficients and for the error `Ψ_k`.
  have hah0 : ∀ k, ah k 0 = a k (x k) := fun k => by rw [hah, smul_zero, add_zero]
  have hell0 : ∀ k (P : Rn n →L[ℝ] Rn ℓ), lam * ‖P‖ ^ 2 ≤ ah k 0 P P := fun k P => by
    rw [hah0]; exact hell k (x k) (hx1 k) P
  have hbd0 : ∀ k (P Q : Rn n →L[ℝ] Rn ℓ), |ah k 0 P Q| ≤ M * ‖P‖ * ‖Q‖ := fun k P Q => by
    rw [hah0]; exact hbd k (x k) (hx1 k) P Q
  have hahb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ P Q : Rn n →L[ℝ] Rn ℓ,
      |ah k z P Q - ah k 0 P Q| ≤ M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by
    intro k z hz P Q
    have h := haH k _ (hmap k z hz) _ (hmap k 0 (mem_ball_self (hRpos k))) P Q
    rw [hscale, sub_zero] at h
    rw [hah k z, hah k 0]
    calc _ ≤ M * (ρ k ^ α * ‖z‖ ^ α) * ‖P‖ * ‖Q‖ := h
      _ = M * ρ k ^ α * ‖z‖ ^ α * ‖P‖ * ‖Q‖ := by ring
  have hΨd : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ z' ∈ ball (0 : Rn n) (R k),
      ∀ Q : Rn n →L[ℝ] Rn ℓ, |Ψ k z Q - Ψ k z' Q| ≤
        (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
    intro k z hz z' hz' Q
    have hΦ := hΦH k _ (hmap k z hz) _ (hmap k z' hz') Q
    have ha := haH k _ (hmap k z hz) _ (hmap k z' hz') (P₀ k) Q
    have hP : ‖P₀ k‖ = ρ k * ‖fderiv ℝ (w k) (x k)‖ := by
      rw [hP₀, norm_smul, Real.norm_of_nonneg (hρpos k).le]
    rw [hscale] at hΦ ha
    rw [hP] at ha
    have hexp : Ψ k z Q - Ψ k z' Q = s k * (ρ k * (Φ k (x k + ρ k • z) Q -
        Φ k (x k + ρ k • z') Q) - (a k (x k + ρ k • z) (P₀ k) Q -
        a k (x k + ρ k • z') (P₀ k) Q)) := by
      rw [hΨ, hΨ, hah, hah]
      simp only [smul_apply, sub_apply, smul_eq_mul]
      ring
    rw [hexp, abs_mul, abs_of_pos (hspos k)]
    have htri : |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
        (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)| ≤
        ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (hρpos k)]
      exact add_le_add (mul_le_mul_of_nonneg_left hΦ (hρpos k).le) ha
    calc s k * |ρ k * (Φ k (x k + ρ k • z) Q - Φ k (x k + ρ k • z') Q) -
          (a k (x k + ρ k • z) (P₀ k) Q - a k (x k + ρ k • z') (P₀ k) Q)|
        ≤ s k * (ρ k * (G k * (ρ k ^ α * ‖z - z'‖ ^ α) * ‖Q‖) +
          M * (ρ k ^ α * ‖z - z'‖ ^ α) * (ρ k * ‖fderiv ℝ (w k) (x k)‖) * ‖Q‖) :=
          mul_le_mul_of_nonneg_left htri (hspos k).le
      _ = (s k * ρ k) * (G k + M * ‖fderiv ℝ (w k) (x k)‖) * ρ k ^ α * ‖z - z'‖ ^ α * ‖Q‖ := by
          ring
      _ = (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z - z'‖ ^ α * ‖Q‖ := by
          rw [hsρ]; ring
  have hΨc : ∀ k, ContinuousOn (Ψ k) (ball (0 : Rn n) (R k)) := fun k => hcontL (Ψ k) _ _ (hΨd k)
  have hΨb : ∀ k, ∀ z ∈ ball (0 : Rn n) (R k), ∀ Q : Rn n →L[ℝ] Rn ℓ,
      |Ψ k z Q| ≤ (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k) * ‖z‖ ^ α * ‖Q‖ := by
    intro k z hz Q
    have h := hΨd k z hz 0 (mem_ball_self (hRpos k)) Q
    have h0 : Ψ k 0 Q = 0 := by
      rw [hΨ, hah]
      simp
    rwa [h0, sub_zero, sub_zero] at h
  have hWeq : ∀ k (ζ : Rn n → Rn ℓ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Rn n) (R k) →
      ∫ z in ball (0 : Rn n) (R k), ah k z (fderiv ℝ (W k) z) (fderiv ℝ ζ z) =
        ∫ z in ball (0 : Rn n) (R k), Ψ k z (fderiv ℝ ζ z) := by
    intro k ζ hζ hζc hζs
    rw [hW k]
    simp only [hΨ]
    exact (hsub k).2.2 ζ hζ hζc hζs
  -- The unit vectors `e_k = (y_k − x_k)/ρ_k` with `‖DW_k(e_k)‖ = 1`.
  have he1 : ∀ k, ‖e k‖ = 1 := fun k => by
    rw [he, norm_smul, norm_inv, Real.norm_of_nonneg (hρpos k).le, norm_sub_rev, ← hρ,
      inv_mul_cancel₀ (hρpos k).ne']
  have hxe : ∀ k, x k + ρ k • e k = y k := fun k => by
    rw [he, smul_smul, mul_inv_cancel₀ (hρpos k).ne', one_smul, add_sub_cancel]
  have heN : ∀ᶠ k in atTop, ‖fderiv ℝ (W k) (e k)‖ = 1 := by
    filter_upwards [hρhalf] with k hk
    have hek : e k ∈ ball (0 : Rn n) (R k) := by
      rw [mem_ball_zero_iff, he1, hR, one_lt_inv₀ (mul_pos two_pos (hρpos k))]
      linarith
    rw [hDW k (e k) hek, hxe, hP₀, ← smul_sub, smul_smul, norm_smul,
      Real.norm_of_nonneg (mul_pos (hspos k) (hρpos k)).le, hsρ, norm_sub_rev, ← hN,
      inv_mul_cancel₀ (hNpos k).ne']
  -- Limits of the scale-dependent constants.
  have hRt : Tendsto R atTop atTop := by
    have h2ρ : Tendsto (fun k => 2 * ρ k) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · simpa using hρt.const_mul 2
      · exact mul_pos two_pos (hρpos k)
    exact (tendsto_inv_nhdsGT_zero.comp h2ρ).congr fun k => (hR k).symm
  have hct : Tendsto (fun k => M * ρ k ^ α) atTop (𝓝 0) := by
    simpa using hραt.const_mul M
  have hdt : Tendsto (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k))
      atTop (𝓝 0) := by
    have hG' : Tendsto (fun k => G k * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (hG k) (div_nonneg (hραpos k).le (hNpos k).le)) ?_
        tendsto_one_div_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      rw [mul_div_assoc', div_le_div_iff₀ (hNpos k) hk', one_mul]
      calc G k * ρ k ^ α * k = k * G k * ρ k ^ α := by ring
        _ ≤ N k := hGN k
    have hD' : Tendsto (fun k => ‖fderiv ℝ (w k) (x k)‖ * (ρ k ^ α / N k)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun k =>
        mul_nonneg (norm_nonneg _) (div_nonneg (hραpos k).le (hNpos k).le)) ?_ hεt
      filter_upwards [eventually_ge_atTop 5] with k hk
      rw [mul_div_assoc', div_le_iff₀ (hNpos k)]
      exact hinterp k hk (x k) (hx k)
    have h := hG'.add (hD'.const_mul M)
    rw [mul_zero, add_zero] at h
    exact h.congr fun k => by ring
  -- Steps 7–8 (child `blowup_limit`) and step 9 (sibling Liouville theorem).
  obtain ⟨A, W', hA1, hA2, hW'C, hW'H, hW'eq, hW'0, e₀, he₀⟩ :=
    Submission.dohr_eb_sch_bu_blowup_limit n ℓ α lam M δ⁻¹ W ah Ψ e R (fun k => M * ρ k ^ α)
      (fun k => (G k + M * ‖fderiv ℝ (w k) (x k)‖) * (ρ k ^ α / N k)) hα
      (inv_nonneg.mpr hδ.le) hRt hct hdt hWC hW0 hDW0 hWH hJ hΨc hell0 hbd0 hahb hΨb hWeq
      (fun k => (he1 k).le) heN
  have hconst := Submission.dohr_eb_sch_liouville_const_coeff n ℓ α lam M δ⁻¹ A W' hα hα1 hlam
    hA1 hA2 hW'C hW'H hW'eq e₀ 0
  rw [hconst, hW'0, norm_zero] at he₀
  exact zero_ne_one he₀

end Submission

/-- **Interior `C^{1,α}` estimate on the unit ball** (the case `x₀ = 0`, `R = 1` of the Schauder
estimate in the elliptic bootstrap for Simon 7.1, second assertion).  Let `w` be `C¹` on `B̆₁(0)`
with `∫ a(x)[Dw][Dζ] = ∫ Φ(x)[Dζ]` for every `ζ ∈ C¹_c(B̆₁(0); ℝ^ℓ)`, where `a` is Legendre
elliptic with constant `lam > 0`, `a` and `Φ` are bounded and `α`-Hölder with constant `M`,
`|w| ≤ M`, and `Dw` is `α`-Hölder on `B̆₁(0)` with some constant.  Then `‖Dw‖ ≤ C` and
`‖Dw(x) − Dw(y)‖ ≤ C |x − y|^α` on `B̆_{1/2}(0)`, where `C` depends only on `n, ℓ, α, lam, M`.
Proof: take `δ = 1/16`, `C_δ` from the blow-up estimate and `C = (1024 + 128 C_δ) M`.  Rescaling
`B̆_ρ(y) ⊆ B̆₁(0)` to `B̆₁(0)` and applying the blow-up estimate there gives
`ρ^{1+α} ‖Dw(x) − Dw(x')‖ ≤ (ρ^{1+α} K / 16 + 2 C_δ M) |x − x'|^α` on `B̆_{ρ/2}(y)` whenever
`Dw` is `K`-Hölder on `B̆_ρ(y)`; with the interpolation bound for `‖Dw‖`, the absorption lemma
for the best scale-weighted Hölder constant concludes. -/
theorem Submission.dohr_eb_sch_unit_ball_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M : ℝ, 0 < lam → ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ), (∀ x ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball (0 : Rn n) 1, ‖w x‖ ≤ M) → ContDiffOn ℝ 1 w (ball (0 : Rn n) 1) → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) 1, ∀ y ∈ ball (0 : Rn n) 1, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Rn n) 1 → ∫ x in ball (0 : Rn n) 1, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball (0 : Rn n) 1, Φ x (fderiv ℝ ζ x)) → (∀ x ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball (0 : Rn n) (1 / 2), ∀ y ∈ ball (0 : Rn n) (1 / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ hn α hα hα1 lam M hlam
  -- Step 0: `C_δ` from the blow-up estimate with `δ = 1/16`; for `M < 0`, (H5) is impossible.
  obtain ⟨Cδ, hCδ0, hCδ⟩ := Submission.dohr_eb_sch_blowup_holder_estimate n ℓ hn α hα hα1 lam M
    (1 / 16) hlam (by norm_num)
  by_cases hM : 0 ≤ M
  swap
  · refine ⟨0, le_rfl, fun a Φ w _ _ _ _ hS _ _ _ => ?_⟩
    exact absurd ((norm_nonneg _).trans (hS 0 (mem_ball_self one_pos))) hM
  have hA : 0 ≤ Cδ * (M + M) := mul_nonneg hCδ0 (add_nonneg hM hM)
  refine ⟨1024 * M + 64 * (Cδ * (M + M)),
    add_nonneg (mul_nonneg (by norm_num) hM) (mul_nonneg (by norm_num) hA), ?_⟩
  intro a Φ w hlg hab haH hΦH hS hw hK hweak
  -- Step 1: the one-scale estimate on every `B̆_ρ(y) ⊆ B̆₁(0)`.  With `w̃(z) = w(y + ρz)`,
  -- `Dw̃(z) = ρ Dw(y + ρz)` is `ρ^{1+α} K`-Hölder on `B̆₁(0)`, and the blow-up estimate for the
  -- rescaled data on `B̆₁(0)` (with `S = G = M`) scales back to `B̆_{ρ/2}(y)`.
  have hstep : ∀ (y : Rn n) (ρ K : ℝ), 0 < ρ → ‖y‖ + ρ ≤ 1 →
      (∀ x ∈ ball y ρ, ∀ x' ∈ ball y ρ, ‖fderiv ℝ w x - fderiv ℝ w x'‖ ≤ K * ‖x - x'‖ ^ α) →
      ∀ x ∈ ball y (ρ / 2), ∀ x' ∈ ball y (ρ / 2), ρ ^ (1 + α) * ‖fderiv ℝ w x - fderiv ℝ w x'‖ ≤
        (1 / 16 * ρ ^ (1 + α) * K + Cδ * (M + M)) * ‖x - x'‖ ^ α := by
    intro y ρ K hρ hyρ hHol
    have hsub : ball (y + ρ • (0 : Rn n)) (ρ * 1) ⊆ ball (0 : Rn n) 1 := by
      rw [smul_zero, add_zero, mul_one]
      exact ball_subset_ball' (by rw [dist_zero_right]; linarith)
    obtain ⟨hwt, hdwt, hweakt⟩ := Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ a Φ w
      (ball (0 : Rn n) 1) y 0 ρ 1 hρ isOpen_ball hsub hw hweak
    obtain ⟨h1, h2, h3, h4, h5⟩ := Submission.dohr_eb_sch_ube_rescaled_structure n ℓ a Φ w y ρ α
      lam M hρ hyρ hα.le hM hlg hab haH hΦH hS
    have hHolt : ∀ z ∈ ball (0 : Rn n) 1, ∀ z' ∈ ball (0 : Rn n) 1,
        ‖fderiv ℝ (fun z => w (y + ρ • z)) z - fderiv ℝ (fun z => w (y + ρ • z)) z'‖ ≤
          ρ ^ (1 + α) * K * ‖z - z'‖ ^ α := by
      have h := (Submission.dohr_eb_sch_ube_holder_rescale n ℓ (fderiv ℝ w) y ρ 1 α
        (ρ ^ (1 + α) * K) hρ).mpr fun x hx x' hx' => by
          rw [mul_one] at hx hx'
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hHol x hx x' hx') (Real.rpow_nonneg hρ.le _)
      intro z hz z' hz'
      rw [hdwt z hz, hdwt z' hz']
      exact h z hz z' hz'
    have hbl := hCδ (fun z => a (y + ρ • z)) (fun z => ρ • Φ (y + ρ • z))
      (fun z => w (y + ρ • z)) (ρ ^ (1 + α) * K) M M hM h1 h2 h3 h4 h5 hwt hHolt hweakt
    have h := (Submission.dohr_eb_sch_ube_holder_rescale n ℓ (fderiv ℝ w) y ρ (1 / 2) α
      (1 / 16 * (ρ ^ (1 + α) * K) + Cδ * (M + M)) hρ).mp fun z hz z' hz' => by
        rw [← hdwt z (ball_subset_ball (by norm_num) hz),
          ← hdwt z' (ball_subset_ball (by norm_num) hz')]
        exact hbl z hz z' hz'
    intro x hx x' hx'
    rw [← mul_one_div ρ 2] at hx hx'
    rw [mul_assoc (1 / 16 : ℝ)]
    exact h x hx x' hx'
  -- Step 2: the interpolation bound `‖Dw(x)‖ ≤ 2M/t + t^α K` on every `B̆_r(x) ⊆ B̆₁(0)`.
  have hint : ∀ (x : Rn n) (r t K : ℝ), ‖x‖ + r ≤ 1 → 0 ≤ K → 0 < t → t < r →
      (∀ z ∈ ball x r, ∀ z' ∈ ball x r, ‖fderiv ℝ w z - fderiv ℝ w z'‖ ≤ K * ‖z - z'‖ ^ α) →
      ‖fderiv ℝ w x‖ ≤ 2 * M / t + t ^ α * K := by
    intro x r t K hxr hK0 ht htr hHol
    have hsub : ball x r ⊆ ball (0 : Rn n) 1 :=
      ball_subset_ball' (by rw [dist_zero_right]; linarith)
    exact Submission.dohr_eb_sch_fderiv_norm_interpolation n ℓ w x r t α M K hα.le hK0 ht htr
      (hw.mono hsub) (fun z hz => hS z (hsub hz)) hHol
  -- Step 3: absorption with `g = Dw` and `A = 2 C_δ M`.
  exact Submission.dohr_eb_sch_ube_absorption n ℓ (fderiv ℝ w) α M (Cδ * (M + M)) hα hα1.le hM
    hA hK hstep hint

namespace Submission

/-- Simon Ch. 5, proof of Theorem 7.1, second assertion (p. 127): the interior Schauder estimate
(Giaquinta–Martinazzi, Thms. 5.17/5.19) for `C^{1,α}` weak solutions `w` of the linear system
`∫_B a(x)[Dw][Dζ] = ∫_B Φ(x)[Dζ]` on `B = B̆_R(x₀)`, with `lam`-Legendre, bounded, `α`-Hölder
coefficients `a` and `α`-Hölder right side `Φ`: `‖Dw‖ ≤ C` and `[Dw]_α ≤ C` on `B̆_{R/2}(x₀)`, with
`C = C(n, ℓ, α, lam, M, R)`.  If `M < 0` the bound `‖w(x₀)‖ ≤ M` fails and any `C` works.
Otherwise `x = x₀ + R z` turns `(a, Φ, w)` into `(a(x₀ + R ·), R Φ(x₀ + R ·), w(x₀ + R ·))` on
`B̆₁(0)`, which satisfies the same hypotheses with `M (1 + R^α + R^{1+α})` in place of `M`; the
unit-ball estimate bounds `D(w(x₀ + R ·))(z) = R Dw(x₀ + R z)` on `B̆_{1/2}(0)`, and scaling back
gives the constant `C₁ (R⁻¹ + R^{-(1+α)})`. -/
theorem dohr_eb_schauder_interior_estimate : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ lam M R : ℝ, 0 < lam → 0 < R → ∃ C : ℝ, ∀ (x₀ : Rn n) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (w : Rn n → Rn ℓ), (∀ x ∈ ball x₀ R, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ x ∈ ball x₀ R, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q| ≤ M * ‖P‖ * ‖Q‖) → (∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ P Q : Rn n →L[ℝ] Rn ℓ, |a x P Q - a y P Q| ≤ M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖) → (∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ M * ‖x - y‖ ^ α * ‖P‖) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ M) → ContDiffOn ℝ 1 w (ball x₀ R) → (∃ K : ℝ, ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ K * ‖x - y‖ ^ α) → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, a x (fderiv ℝ w x) (fderiv ℝ ζ x) = ∫ x in ball x₀ R, Φ x (fderiv ℝ ζ x)) → (∀ x ∈ ball x₀ (R / 2), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  intro n ℓ hn α hα0 hα1 lam M R hlam hR
  -- Step 0: for `M < 0` hypothesis (H5) fails at `x₀`, so any constant works.
  rcases lt_or_ge M 0 with hM | hM
  · refine ⟨0, fun x₀ a Φ w _ _ _ _ hw _ _ _ => ?_⟩
    exact absurd ((norm_nonneg _).trans (hw x₀ (mem_ball_self hR))) (not_le.2 hM)
  -- Step 7: the rescaled data live on `B̆₁(0)` with `M` replaced by `M (1 + R^α + R^{1+α})`.
  have hRα : 0 < R ^ α := Real.rpow_pos_of_pos hR α
  have hR1α : R ^ (1 + α) = R * R ^ α := by rw [Real.rpow_add hR, Real.rpow_one]
  have hR1α0 : 0 < R ^ (1 + α) := Real.rpow_pos_of_pos hR _
  have hMM : M ≤ M * (1 + R ^ α + R ^ (1 + α)) := le_mul_of_one_le_right hM (by linarith)
  have hMα : M * R ^ α ≤ M * (1 + R ^ α + R ^ (1 + α)) :=
    mul_le_mul_of_nonneg_left (by linarith) hM
  have hM1α : R * (M * R ^ α) ≤ M * (1 + R ^ α + R ^ (1 + α)) := by
    rw [mul_left_comm, ← hR1α]
    exact mul_le_mul_of_nonneg_left (by linarith) hM
  obtain ⟨C₁, hC₁, hunit⟩ := Submission.dohr_eb_sch_unit_ball_estimate n ℓ hn α hα0 hα1 lam
    (M * (1 + R ^ α + R ^ (1 + α))) hlam
  refine ⟨C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹), ?_⟩
  intro x₀ a Φ w h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨K, hK⟩ := h7
  -- `z ↦ x₀ + R z` maps `B̆₁(0)` into `B̆_R(x₀)` and multiplies distances by `R`.
  have hmem : ∀ z ∈ ball (0 : Rn n) 1, x₀ + R • z ∈ ball x₀ R := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
    calc R * ‖z‖ < R * 1 := mul_lt_mul_of_pos_left hz hR
      _ = R := mul_one R
  have hdist : ∀ z z' : Rn n, ‖x₀ + R • z - (x₀ + R • z')‖ ^ α = R ^ α * ‖z - z'‖ ^ α := by
    intro z z'
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hR.le,
      Real.mul_rpow hR.le (norm_nonneg _)]
  -- Step 2 for `(y, ρ) = (x₀, R)`: `w(x₀ + R ·)` is a `C¹` weak solution on `B̆₁(0)`.
  obtain ⟨hw1, hDw, hweak⟩ := Submission.dohr_eb_sch_weak_eq_affine_rescale n ℓ a Φ w
    (ball x₀ R) x₀ 0 R 1 hR isOpen_ball (by simp) h6 h8
  -- Step 6 for the rescaled data.
  obtain ⟨hsup, hhol⟩ := hunit (fun z => a (x₀ + R • z)) (fun z => R • Φ (x₀ + R • z))
    (fun z => w (x₀ + R • z))
    (fun z hz P => h1 _ (hmem z hz) P)
    (fun z hz P Q => (h2 _ (hmem z hz) P Q).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMM (norm_nonneg P))
        (norm_nonneg Q)))
    (fun z hz z' hz' P Q => by
      have h := h3 _ (hmem z hz) _ (hmem z' hz') P Q
      rw [hdist] at h
      calc _ ≤ M * (R ^ α * ‖z - z'‖ ^ α) * ‖P‖ * ‖Q‖ := h
        _ = M * R ^ α * ‖z - z'‖ ^ α * ‖P‖ * ‖Q‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hMα (Real.rpow_nonneg (norm_nonneg _) _))
            (norm_nonneg P)) (norm_nonneg Q))
    (fun z hz z' hz' P => by
      have h := h4 _ (hmem z hz) _ (hmem z' hz') P
      rw [hdist] at h
      simp only [smul_apply, smul_eq_mul]
      rw [← mul_sub, abs_mul, abs_of_pos hR]
      calc _ ≤ R * (M * (R ^ α * ‖z - z'‖ ^ α) * ‖P‖) := mul_le_mul_of_nonneg_left h hR.le
        _ = R * (M * R ^ α) * ‖z - z'‖ ^ α * ‖P‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hM1α (Real.rpow_nonneg (norm_nonneg _) _))
            (norm_nonneg P))
    (fun z hz => (h5 _ (hmem z hz)).trans hMM)
    hw1
    ⟨R * K * R ^ α, fun z hz z' hz' => by
      rw [hDw z hz, hDw z' hz', ← smul_sub R (fderiv ℝ w (x₀ + R • z)) (fderiv ℝ w (x₀ + R • z')),
        norm_smul, Real.norm_of_nonneg hR.le]
      have h := hK _ (hmem z hz) _ (hmem z' hz')
      rw [hdist] at h
      calc _ ≤ R * (K * (R ^ α * ‖z - z'‖ ^ α)) := mul_le_mul_of_nonneg_left h hR.le
        _ = R * K * R ^ α * ‖z - z'‖ ^ α := by ring⟩
    hweak
  -- Scaling back: `x = x₀ + R z` with `z = R⁻¹ (x - x₀) ∈ B̆_{1/2}(0)` and `Dw̃(z) = R Dw(x)`.
  have hback : ∀ x ∈ ball x₀ (R / 2), R⁻¹ • (x - x₀) ∈ ball (0 : Rn n) (1 / 2) ∧
      fderiv ℝ (fun z => w (x₀ + R • z)) (R⁻¹ • (x - x₀)) = R • fderiv ℝ w x := by
    intro x hx
    have hz : R⁻¹ • (x - x₀) ∈ ball (0 : Rn n) (1 / 2) := by
      rw [mem_ball, dist_eq_norm] at hx
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
        inv_mul_lt_iff₀ hR]
      linarith
    refine ⟨hz, ?_⟩
    rw [hDw _ (ball_subset_ball (by norm_num) hz), smul_smul, mul_inv_cancel₀ hR.ne', one_smul,
      add_sub_cancel]
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨hz, hD⟩ := hback x hx
    have h := hsup _ hz
    rw [hD, norm_smul, Real.norm_of_nonneg hR.le] at h
    calc ‖fderiv ℝ w x‖ = R⁻¹ * (R * ‖fderiv ℝ w x‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      _ ≤ R⁻¹ * C₁ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hR.le)
      _ ≤ C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹) := by
          rw [mul_add, mul_comm]
          exact le_add_of_nonneg_right (mul_nonneg hC₁ (inv_nonneg.2 hR1α0.le))
  · obtain ⟨hz, hDx⟩ := hback x hx
    obtain ⟨hz', hDy⟩ := hback y hy
    have h := hhol _ hz _ hz'
    rw [hDx, hDy, ← smul_sub R (fderiv ℝ w x) (fderiv ℝ w y), norm_smul,
      Real.norm_of_nonneg hR.le, ← smul_sub R⁻¹ (x - x₀) (y - x₀), sub_sub_sub_cancel_right,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le),
      Real.mul_rpow (inv_nonneg.2 hR.le) (norm_nonneg _), Real.inv_rpow hR.le] at h
    calc ‖fderiv ℝ w x - fderiv ℝ w y‖ = R⁻¹ * (R * ‖fderiv ℝ w x - fderiv ℝ w y‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
      _ ≤ R⁻¹ * (C₁ * ((R ^ α)⁻¹ * ‖x - y‖ ^ α)) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hR.le)
      _ = C₁ * (R ^ (1 + α))⁻¹ * ‖x - y‖ ^ α := by rw [hR1α, mul_inv]; ring
      _ ≤ C₁ * (R⁻¹ + (R ^ (1 + α))⁻¹) * ‖x - y‖ ^ α := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC₁)
            (Real.rpow_nonneg (norm_nonneg _) _)
          exact le_add_of_nonneg_left (inv_nonneg.2 hR.le)

/-- **`C^{2,α}` regularity of `C^{1,α}` weak solutions of an Euler–Lagrange system** (first step
of the elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, p. 128; [GM] Proposition 8.6
and Theorem 5.19).  Let `Ψ` be smooth with `λ‖Q‖² ≤ D²Ψ(P)[Q, Q]` for `‖P‖ ≤ ε`, `g` be
`C^{0,α}_loc(U)` and `u ∈ C^{1,α}_loc(U)` with `‖Du‖ ≤ ε` solve `div DΨ(Du) = g` weakly in the open
set `U`.  Then `u ∈ C^{2,α}_loc(U)`.  The difference quotients `w_d = d⁻¹ (u(· + d e_k) − u)`
solve linear systems with averaged coefficients that satisfy the hypotheses of the Schauder
estimate uniformly in `d`; the resulting uniform `C^{1,α}` bounds pass to the limit `d → 0`, so
every `D_k u` is `C^{1,α}_loc(U)`. -/
theorem dohr_eb_el_c2alpha_regularity : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (lam ε : ℝ) (U : Set (Rn n)) (u g : Rn n → Rn ℓ), 0 < lam → IsOpen U → ContDiff ℝ (⊤ : ℕ∞) Ψ → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q : Rn n →L[ℝ] Rn ℓ, lam * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ Ψ) P Q Q) → IsLocallyHolderCkα 1 α u U → (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ ε) → IsLocallyHolderCkα 0 α g U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → IsLocallyHolderCkα 2 α u U := by
  intro n ℓ hn α hα0 hα1 Ψ lam ε U u g hlam hU hΨ hLeg hu hDu hg hweak
  -- Step 0: `Ψ` is `C³`, `u` is `C¹` and `g` is continuous on `U`.
  have hΨ3 : ContDiff ℝ 3 Ψ := hΨ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hΨ2 : ContDiff ℝ 2 Ψ := hΨ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu1 : ContDiffOn ℝ 1 u U := by simpa using hu.1
  have hg0 : ContinuousOn g U := by
    have h0 : ContDiffOn ℝ 0 g U := by simpa using hg.1
    exact contDiffOn_zero.mp h0
  -- Step 0: the Hölder differences of `D¹u` and `D⁰g` are those of `Du` and `g`, since
  -- `continuousMultilinearCurryFin1` and `continuousMultilinearCurryFin0` are linear isometries.
  have hconv1 : ∀ x y : Rn n,
      ‖iteratedFDeriv ℝ 1 u x - iteratedFDeriv ℝ 1 u y‖ = ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
    intro x y
    set c := continuousMultilinearCurryFin1 ℝ (Rn n) (Rn ℓ)
    have hc : ∀ z, c (iteratedFDeriv ℝ 1 u z) = fderiv ℝ u z := by
      intro z; ext v; simp [c, iteratedFDeriv_one_apply]
    rw [← c.norm_map, c.map_sub, hc, hc]
  have hconv0 : ∀ x y : Rn n,
      ‖iteratedFDeriv ℝ 0 g x - iteratedFDeriv ℝ 0 g y‖ = ‖g x - g y‖ := by
    intro x y
    set c := continuousMultilinearCurryFin0 ℝ (Rn n) (Rn ℓ)
    have hc : ∀ z, c (iteratedFDeriv ℝ 0 g z) = g z := by
      intro z; simp [c]
    rw [← c.norm_map, c.map_sub, hc, hc]
  -- Step 1: the bound `M_B` and the Lipschitz constant `L_B` of `D²Ψ` on the `ε`-ball.
  obtain ⟨MB, LB, hMB0, hLB0, hMB, hLB⟩ := Submission.dohr_eb_elc2_hessian_bounds n ℓ Ψ hΨ3 ε
  -- Steps 2–7: every partial derivative `D_k u = Du(·) e_k` is `C^{1,α}_loc(U)`.
  have hcol : ∀ k : Fin n,
      IsLocallyHolderCkα 1 α (fun x => fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) U := by
    intro k
    set e : Rn n := EuclideanSpace.single k (1 : ℝ)
    have he : ‖e‖ = 1 := by simp [e]
    -- Step 7: it suffices to show that `D_k u` is `C¹` with `α`-Hölder derivative on a ball
    -- around each point of `U`.
    apply Submission.dohr_eb_elc2_local_to_global_holder n ℓ α _ U hα0 hU
    intro xb hxb
    -- Step 2: localization to `K₀ = B̄_{4R}(xb) ⊆ U`, where `Du` and `g` have the Hölder
    -- constants `H1` and `H2`.
    obtain ⟨r0, hr0, hr0U⟩ := Metric.isOpen_iff.mp hU xb hxb
    set R := r0 / 5 with hR_def
    have hR : 0 < R := by positivity
    have hK0U : closedBall xb (4 * R) ⊆ U :=
      (closedBall_subset_ball (by rw [hR_def]; linarith)).trans hr0U
    obtain ⟨C1, hC1⟩ := hu.2 _ (isCompact_closedBall xb (4 * R)) hK0U
    obtain ⟨C2, hC2⟩ := hg.2 _ (isCompact_closedBall xb (4 * R)) hK0U
    set H1 := max C1 0
    set H2 := max C2 0
    have hH1 : ∀ x ∈ closedBall xb (4 * R), ∀ y ∈ closedBall xb (4 * R),
        ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ H1 * ‖x - y‖ ^ α := by
      intro x hx y hy
      rw [← hconv1]
      exact (hC1 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hH2 : ∀ x ∈ closedBall xb (4 * R), ∀ y ∈ closedBall xb (4 * R),
        ‖g x - g y‖ ≤ H2 * ‖x - y‖ ^ α := by
      intro x hx y hy
      rw [← hconv0]
      exact (hC2 x hx y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    -- Step 5: one constant `M` for all hypotheses of the Schauder estimate on `B_{2R}(xb)`, and
    -- the Schauder constant `C`, independent of `d`.
    set M := max (max MB (LB * H1)) (max H2 (max ε 0))
    have hMB_M : MB ≤ M := le_max_of_le_left (le_max_left _ _)
    have hLB_M : LB * H1 ≤ M := le_max_of_le_left (le_max_right _ _)
    have hH2_M : H2 ≤ M := le_max_of_le_right (le_max_left _ _)
    have hε_M : ε ≤ M := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    obtain ⟨C, hC⟩ := Submission.dohr_eb_schauder_interior_estimate n ℓ hn α hα0 hα1 lam M
      (2 * R) hlam (by positivity)
    -- For `|d| < R`, the segments `x + [0, d] e` with `x ∈ B_{2R}(xb)` lie in `K₀`.
    have hseg : ∀ d : ℝ, |d| < R → ∀ x ∈ ball xb (2 * R), ∀ t ∈ Icc (0 : ℝ) 1,
        x + (t * d) • e ∈ closedBall xb (4 * R) := by
      intro d hd x hx t ht
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_ball, dist_eq_norm] at hx
      have h1 : ‖(t * d) • e‖ ≤ R := by
        rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1]
        calc t * |d| ≤ 1 * |d| := by gcongr; exact ht.2
          _ ≤ R := by linarith
      calc ‖x + (t * d) • e - xb‖ = ‖(x - xb) + (t * d) • e‖ := by congr 1; abel
        _ ≤ ‖x - xb‖ + ‖(t * d) • e‖ := norm_add_le _ _
        _ ≤ 4 * R := by linarith
    -- Steps 3–5: the difference quotients `w_d = d⁻¹ (u(· + d e) − u)`, `0 < |d| < R`, are
    -- bounded in `C^{1,α}(B_R(xb))` uniformly in `d`.
    have hd_est : ∀ d : ℝ, d ≠ 0 → |d| < R →
        (∀ x ∈ ball xb R, ‖d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)‖ ≤ C) ∧
        (∀ x ∈ ball xb R, ∀ y ∈ ball xb R,
          ‖d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x) -
            d⁻¹ • (fderiv ℝ u (y + d • e) - fderiv ℝ u y)‖ ≤ C * ‖x - y‖ ^ α) := by
      intro d hd0 hdR
      have hsegK := hseg d hdR
      have hsegU : ∀ x ∈ ball xb (2 * R), ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ U :=
        fun x hx t ht => hK0U (hsegK x hx t ht)
      have hxK : ∀ x ∈ ball xb (2 * R), x ∈ closedBall xb (4 * R) := by
        intro x hx
        simpa using hsegK x hx 0 (by simp)
      have hxdK : ∀ x ∈ ball xb (2 * R), x + d • e ∈ closedBall xb (4 * R) := by
        intro x hx
        simpa using hsegK x hx 1 (by simp)
      -- Step 3, (H5)–(H7): `w_d` is `C¹` on `B_{2R}(xb)`, `Dw_d = d⁻¹ (Du(· + d e) − Du)`,
      -- `‖w_d‖ ≤ ε` and `Dw_d` is `α`-Hölder.
      obtain ⟨hw1, hwD, hwB, hwH⟩ := Submission.dohr_eb_elc2_dq_basic n ℓ u U (ball xb (2 * R))
        (closedBall xb (4 * R)) e d ε H1 α hU hu1 hK0U hd0 hsegK (fun x hx => hDu x (hK0U hx))
        hH1
      -- Step 4, (H1)–(H3): the averaged coefficients `a_d(x) = ∫₀¹ D²Ψ(P_t(x)) dt`.
      obtain ⟨a, ha_eq, ha1, ha2, ha3⟩ := Submission.dohr_eb_elc2_averaged_hessian n ℓ Ψ lam ε
        MB LB H1 α (ball xb (2 * R)) (fderiv ℝ u) (fun x => fderiv ℝ u (x + d • e)) hΨ2 hLB0
        hLeg hMB hLB (fun x hx => hDu x (hK0U (hxK x hx)))
        (fun x hx => hDu _ (hK0U (hxdK x hx))) (fun x hx y hy => hH1 x (hxK x hx) y (hxK y hy))
        (fun x hx y hy => by simpa using hH1 _ (hxdK x hx) _ (hxdK y hy))
      -- Step 4, (H4): the averaged right-hand side `Φ_d(x)[P] = ⟪∫₀¹ g(x + t d e) dt, P e⟫`.
      obtain ⟨Φ, hΦ_eq, hΦH⟩ := Submission.dohr_eb_elc2_averaged_forcing n ℓ α H2 d g
        (ball xb (2 * R)) (closedBall xb (4 * R)) e hα0 hsegK hH2
      -- Step 4, (H8): `w_d` solves the linear system with coefficients `a_d` and right side `Φ_d`.
      have hweq := Submission.dohr_eb_elc2_dq_weak_equation n ℓ Ψ U (ball xb (2 * R)) u g e d
        hΨ2 hU isOpen_ball hu1 hg0 hd0 hsegU hweak
      -- Step 5: the Schauder estimate on `B_{2R}(xb)`.
      have hS := hC xb a Φ (fun z => d⁻¹ • (u (z + d • e) - u z)) ha1
        (fun x hx P Q => (ha2 x hx P Q).trans (by gcongr))
        (fun x hx y hy P Q => (ha3 x hx y hy P Q).trans (by
          rw [show LB * H1 * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ =
              (LB * H1) * (‖x - y‖ ^ α * ‖P‖ * ‖Q‖) by ring,
            show M * ‖x - y‖ ^ α * ‖P‖ * ‖Q‖ = M * (‖x - y‖ ^ α * ‖P‖ * ‖Q‖) by ring]
          gcongr))
        (fun x hx y hy P => (hΦH x hx y hy P).trans (by rw [he, mul_one]; gcongr))
        (fun x hx => (hwB x hx).trans (by rw [he, mul_one]; exact hε_M))
        hw1 ⟨2 * |d|⁻¹ * H1, hwH⟩
        (by
          intro ζ hζ1 hζc hζs
          have e1 : ∫ x in ball xb (2 * R),
                a x (fderiv ℝ (fun z => d⁻¹ • (u (z + d • e) - u z)) x) (fderiv ℝ ζ x) =
              ∫ x in ball xb (2 * R), (∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ Ψ)
                (fderiv ℝ u x + t • (fderiv ℝ u (x + d • e) - fderiv ℝ u x))
                (d⁻¹ • (fderiv ℝ u (x + d • e) - fderiv ℝ u x)) (fderiv ℝ ζ x)) := by
            apply setIntegral_congr_fun measurableSet_ball
            intro x hx
            simp only [hwD x hx, ha_eq]
          have e2 : ∫ x in ball xb (2 * R), Φ x (fderiv ℝ ζ x) =
              ∫ x in ball xb (2 * R), inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e))
                (fderiv ℝ ζ x e) := by
            simp only [hΦ_eq]
          rw [e1, e2]
          exact hweq ζ hζ1 hζc hζs)
      rw [show 2 * R / 2 = R by ring] at hS
      refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
      · rw [← hwD x (ball_subset_ball (by linarith) hx)]
        exact hS.1 x hx
      · rw [← hwD x (ball_subset_ball (by linarith) hx),
          ← hwD y (ball_subset_ball (by linarith) hy)]
        exact hS.2 x hx y hy
    -- Step 6: letting `d → 0`, `D_k u` is `C¹` on `B_R(xb)` with `α`-Hölder derivative.
    have hu2R : ContDiffOn ℝ 1 u (ball xb (R + R * ‖e‖)) := by
      rw [he, mul_one]
      exact hu1.mono ((ball_subset_ball (by linarith)).trans (ball_subset_closedBall.trans hK0U))
    obtain ⟨hv1, -, hvH⟩ := Submission.dohr_eb_difference_quotient_limit n ℓ α u xb e R R C hα0
      hα1.le hR hu2R (fun d hd0 hdR => (hd_est d hd0 hdR).1)
      (fun d hd0 hdR => (hd_est d hd0 hdR).2)
    exact ⟨R, hR, hv1, C, hvH⟩
  -- Step 8: `u` is `C¹` on `U` and every `D_k u` is `C^{1,α}_loc(U)`, so `u` is `C^{2,α}_loc(U)`.
  exact (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) 1 α u U hU).2.2
    ⟨hu1, fun k => ⟨(hcol k).1, (hcol k).2⟩⟩
/-- **Higher interior regularity for linear elliptic systems** (node `linear_higher_regularity` of
the elliptic bootstrap for Simon Ch. 5, Theorem 7.1; [GM] Theorem 5.20).  Let `a` be Legendre
elliptic with constant `lam > 0` on the open set `U`, let the scalar components `x ↦ a x P Q` and
`x ↦ Φ x P` be `C^{m,α}_loc` on `U` (`m ≥ 1`, `0 < α < 1`), and let `v ∈ C^{m,α}_loc(U)` be a weak
solution of `div (a Dv) = div Φ`.  Then `v ∈ C^{m+1,α}_loc(U)`.  Induction on `m`, for all data:
* `m = 1`: near `xb ∈ U` the difference quotients `w_d` of `v` in a coordinate direction solve the
  same system with right side `Ψ_d` (`dohr_eb_lhr_dq_weak_equation`), with bounds uniform in `d`
  (`dohr_eb_lhr_dq_uniform_bounds`, `dohr_eb_lhr_coeff_uniform_bounds`); the Schauder estimate
  (`dohr_eb_schauder_interior_estimate`) bounds `Dw_d` in `C^{0,α}` uniformly, the limit `d → 0`
  (`dohr_eb_difference_quotient_limit`) gives `D_k v ∈ C^{1,α}` near `xb`, and covering
  (`dohr_eb_lhr_cover_holder_one`) and `dohr_eb_holder_succ_iff_fderiv` give `v ∈ C^{2,α}_loc`.
* `m → m + 1`: `D_s v` solves the system with right side `Ψ = D_s Φ - (D_s a)[Dv]`
  (`dohr_eb_lhr_differentiated_system`); expanding `Dv` in a basis of `L(ℝⁿ, ℝ^ℓ)` shows that the
  components of `Ψ` are `C^{m,α}_loc` (`dohr_eb_holder_bilinear`, `dohr_eb_lhr_holder_loc_sub_sum`),
  so the order-`m` case and `dohr_eb_holder_succ_iff_fderiv` conclude. -/
theorem dohr_eb_linear_higher_regularity : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ m : ℕ, 1 ≤ m → ∀ (U : Set (Rn n)) (lam : ℝ) (a : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ) (v : Rn n → Rn ℓ), IsOpen U → 0 < lam → (∀ x ∈ U, ∀ P : Rn n →L[ℝ] Rn ℓ, lam * ‖P‖ ^ 2 ≤ a x P P) → (∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ m (fun x => a x P Q) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => a z P Q) x - iteratedFDeriv ℝ m (fun z => a z P Q) y‖ ≤ C * ‖x - y‖ ^ α) → (∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ m (fun x => Φ x P) U ∧ ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖iteratedFDeriv ℝ m (fun z => Φ z P) x - iteratedFDeriv ℝ m (fun z => Φ z P) y‖ ≤ C * ‖x - y‖ ^ α) → IsLocallyHolderCkα m α v U → (∀ ζ : Rn n → Rn ℓ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∫ x in U, a x (fderiv ℝ v x) (fderiv ℝ ζ x) = ∫ x in U, Φ x (fderiv ℝ ζ x)) → IsLocallyHolderCkα (m + 1) α v U := by
  intro n ℓ hn α hα hα1 m hm
  induction m, hm using Nat.le_induction with
  | base =>
    -- Base case `m = 1` (steps 1–6 of the proof).
    intro U lam a Φ v hU hlam hell ha hΦ hv hweak
    have ha1 : ∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U ∧
        ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ 1 (fun z => a z P Q) x - iteratedFDeriv ℝ 1 (fun z => a z P Q) y‖ ≤
            C * ‖x - y‖ ^ α := fun P Q => ⟨by exact_mod_cast (ha P Q).1, (ha P Q).2⟩
    have hΦ1 : ∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U ∧
        ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ 1 (fun z => Φ z P) x - iteratedFDeriv ℝ 1 (fun z => Φ z P) y‖ ≤
            C * ‖x - y‖ ^ α := fun P => ⟨by exact_mod_cast (hΦ P).1, (hΦ P).2⟩
    have hvC1 : ContDiffOn ℝ 1 v U := by exact_mod_cast hv.1
    -- Step 6: it suffices that every partial derivative `D_k v` is `C^{1,α}_loc` on `U`.
    refine (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) 1 α v U hU).2.2
      ⟨hvC1, fun k => ?_⟩
    -- Steps 1–5: `D_k v` is `C^{1,α}` on a ball around every point of `U`.
    have hloc : ∀ xb ∈ U, ∃ R : ℝ, 0 < R ∧ ball xb R ⊆ U ∧
        ContDiffOn ℝ 1 (fun x => fderiv ℝ v x (EuclideanSpace.single k (1 : ℝ))) (ball xb R) ∧
        ∃ C : ℝ, ∀ y ∈ ball xb R, ∀ z ∈ ball xb R,
          ‖fderiv ℝ (fun x => fderiv ℝ v x (EuclideanSpace.single k (1 : ℝ))) y -
            fderiv ℝ (fun x => fderiv ℝ v x (EuclideanSpace.single k (1 : ℝ))) z‖ ≤
            C * ‖y - z‖ ^ α := by
      intro xb hxb
      -- Step 1: `closedBall xb (4 * R) ⊆ U`.
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU xb hxb
      obtain ⟨R, hR, hball⟩ : ∃ R : ℝ, 0 < R ∧ closedBall xb (4 * R) ⊆ U :=
        ⟨ε / 8, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
      have h2R : ball xb (2 * R) ⊆ closedBall xb (4 * R) :=
        ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
      have hR2R : ball xb R ⊆ ball xb (2 * R) := ball_subset_ball (by linarith)
      have he : ‖(EuclideanSpace.single k (1 : ℝ) : Rn n)‖ = 1 := by simp
      -- Steps 2 and 4: bounds on the difference quotients `w_d` and the data, uniform in `d`.
      obtain ⟨M₁, hM₁⟩ := Submission.dohr_eb_lhr_dq_uniform_bounds n ℓ α U a Φ v xb
        (EuclideanSpace.single k (1 : ℝ)) R hα hα1.le hU hR hball he.le ha1 hΦ1 hv
      obtain ⟨M₂, hM₂⟩ := Submission.dohr_eb_lhr_coeff_uniform_bounds n ℓ α U
        (closedBall xb (4 * R)) a hα hα1.le hU (isCompact_closedBall _ _) (convex_closedBall _ _)
        hball fun P Q => (ha1 P Q).1
      -- Step 4: one Schauder constant `C` for the data `(lam, max M₁ M₂)` on balls of radius `2R`.
      obtain ⟨C, hC⟩ := Submission.dohr_eb_schauder_interior_estimate n ℓ hn α hα hα1 lam
        (max M₁ M₂) (2 * R) hlam (by positivity)
      have hdq : ∀ d : ℝ, d ≠ 0 → |d| < R →
          (∀ x ∈ ball xb R, ‖d⁻¹ • (fderiv ℝ v (x + d • EuclideanSpace.single k (1 : ℝ)) -
            fderiv ℝ v x)‖ ≤ C) ∧
          ∀ x ∈ ball xb R, ∀ y ∈ ball xb R,
            ‖d⁻¹ • (fderiv ℝ v (x + d • EuclideanSpace.single k (1 : ℝ)) - fderiv ℝ v x) -
              d⁻¹ • (fderiv ℝ v (y + d • EuclideanSpace.single k (1 : ℝ)) - fderiv ℝ v y)‖ ≤
              C * ‖x - y‖ ^ α := by
        intro d hd hdR
        obtain ⟨hw, hwC1, hwD, hwH, hΨH⟩ := hM₁ d hd hdR
        -- Step 3: `w_d` is a weak solution on `ball xb (2 * R)` with right side `Ψ`.
        obtain ⟨Ψ, hΨ, hΨweak⟩ := Submission.dohr_eb_lhr_dq_weak_equation n ℓ U a Φ v xb
          (EuclideanSpace.single k (1 : ℝ)) R d hU hR hball he.le hd hdR
          (fun P Q => (ha1 P Q).1.continuousOn) (fun P => (hΦ1 P).1.continuousOn) hvC1 hweak
        -- Step 4: the Schauder estimate for `w_d` on `ball xb (2 * R)`.
        obtain ⟨hS1, hS2⟩ := hC xb a Ψ
          (fun z => d⁻¹ • (v (z + d • EuclideanSpace.single k (1 : ℝ)) - v z))
          (fun x hx P => hell x (hball (h2R hx)) P)
          (fun x hx P Q => (hM₂ x (h2R hx) x (h2R hx) P Q).1.trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
              (norm_nonneg _)) (norm_nonneg _)))
          (fun x hx y hy P Q => (hM₂ x (h2R hx) y (h2R hy) P Q).2.trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _))
              (norm_nonneg _)))
          (fun x hx y hy P => by
            rw [hΨ x P, hΨ y P]
            exact (hΨH x hx y hy P).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)))
          (fun x hx => (hw x hx).trans (le_max_left _ _)) hwC1 hwH hΨweak
        rw [show 2 * R / 2 = R by ring] at hS1 hS2
        refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
        · rw [← hwD x (hR2R hx)]
          exact hS1 x hx
        · rw [← hwD x (hR2R hx), ← hwD y (hR2R hy)]
          exact hS2 x hx y hy
      -- Step 5: letting `d → 0`, `D_k v` is `C^{1,α}` on `ball xb R`.
      have hvB :
          ContDiffOn ℝ 1 v (ball xb (R + R * ‖(EuclideanSpace.single k (1 : ℝ) : Rn n)‖)) :=
        hvC1.mono ((ball_subset_ball (by rw [he]; linarith)).trans
          (ball_subset_closedBall.trans hball))
      obtain ⟨hk1, -, hk3⟩ := Submission.dohr_eb_difference_quotient_limit n ℓ α v xb
        (EuclideanSpace.single k (1 : ℝ)) R R C hα hα1.le hR hvB
        (fun d hd hdR => (hdq d hd hdR).1) (fun d hd hdR => (hdq d hd hdR).2)
      exact ⟨R, hR, hR2R.trans (h2R.trans hball), hk1, C, hk3⟩
    -- Step 6: covering.
    obtain ⟨hk1, hk2⟩ := Submission.dohr_eb_lhr_cover_holder_one n (Rn ℓ) α U
      (fun x => fderiv ℝ v x (EuclideanSpace.single k (1 : ℝ))) hα hU hloc
    exact ⟨by exact_mod_cast hk1, hk2⟩
  | succ m hm IH =>
    -- Inductive step `m → m + 1` (steps 7–10 of the proof).
    intro U lam a Φ v hU hlam hell ha hΦ hv hweak
    have h1 : (1 : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_add_left 1 m
    have h2 : (2 : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.succ_le_succ hm
    have hmm : ((m : ℕ) : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast Nat.le_succ m
    -- Step 7: `v` is `C²` and the data are `C¹` on `U`.
    have hvC1 : ContDiffOn ℝ 1 v U := hv.1.of_le h1
    have hvC2 : ContDiffOn ℝ 2 v U := hv.1.of_le h2
    have ha1 : ∀ P Q : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => a x P Q) U := fun P Q =>
      (ha P Q).1.of_le h1
    have hΦ1 : ∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ 1 (fun x => Φ x P) U := fun P =>
      (hΦ P).1.of_le h1
    -- `Dv` and every `D_s v` are `C^{m,α}_loc` on `U`.
    obtain ⟨-, hDv, hDvH⟩ :=
      (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) m α v U hU).1.1 hv
    have hvs := ((Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) m α v U hU).2.1 hv).2
    -- Step 10: it suffices that every `D_s v` is `C^{m+1,α}_loc` on `U`.
    refine (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) (m + 1) α v U hU).2.2
      ⟨hvC1, fun s => ?_⟩
    -- Step 8: `D_s v` is a weak solution with right side `Ψ = D_s Φ - (D_s a)[Dv]`.
    obtain ⟨Ψ, hΨ, hΨweak⟩ := Submission.dohr_eb_lhr_differentiated_system n ℓ U a Φ v
      (EuclideanSpace.single s (1 : ℝ)) hU ha1 hΦ1 hvC2 hweak
    -- Step 9 (iii): the components of `Ψ` are `C^{m,α}_loc` on `U`.  With a basis `b` of
    -- `L(ℝⁿ, ℝ^ℓ)`, `Ψ x P = D_s(Φ(·)P)(x) - ∑ᵣ b.repr (Dv x) r * D_s(a(·)(b r)P)(x)` on `U`;
    -- each summand is a product of two scalar `C^{m,α}_loc` functions.
    have hΨm : ∀ P : Rn n →L[ℝ] Rn ℓ, ContDiffOn ℝ m (fun x => Ψ x P) U ∧
        ∀ K : Set (Rn n), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
          ‖iteratedFDeriv ℝ m (fun z => Ψ z P) x - iteratedFDeriv ℝ m (fun z => Ψ z P) y‖ ≤
            C * ‖x - y‖ ^ α := by
      intro P
      let b := Module.finBasis ℝ (Rn n →L[ℝ] Rn ℓ)
      let B : Fin (Module.finrank ℝ (Rn n →L[ℝ] Rn ℓ)) →
          (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ →L[ℝ] ℝ := fun r =>
        (ContinuousLinearMap.mul ℝ ℝ).comp (LinearMap.toContinuousLinearMap (b.coord r))
      have hB : ∀ r Q t, B r Q t = b.repr Q r * t := fun r Q t => by simp [B]
      have hΦs := ((Submission.dohr_eb_holder_succ_iff_fderiv n ℝ m α (fun z => Φ z P) U hU).2.1
        (hΦ P)).2 s
      have has := fun r => ((Submission.dohr_eb_holder_succ_iff_fderiv n ℝ m α
        (fun z => a z (b r) P) U hU).2.1 (ha (b r) P)).2 s
      refine Submission.dohr_eb_lhr_holder_loc_sub_sum n ℝ m _ α U
        (fun x => fderiv ℝ (fun z => Φ z P) x (EuclideanSpace.single s (1 : ℝ))) (fun x => Ψ x P)
        (fun r x => B r (fderiv ℝ v x)
          (fderiv ℝ (fun z => a z (b r) P) x (EuclideanSpace.single s (1 : ℝ))))
        hU hΦs.1 hΦs.2 (fun r => Submission.dohr_eb_holder_bilinear (Rn n) (Rn n →L[ℝ] Rn ℓ) ℝ ℝ
          m α (B r) (fderiv ℝ v) _ U hα hα1.le hU hDv hDvH (has r).1 (has r).2) fun x hx => ?_
      rw [hΨ x hx P]
      congr 1
      -- `D_s(a(·)(Dv x)P)(x) = ∑ᵣ b.repr (Dv x) r * D_s(a(·)(b r)P)(x)`, by linearity in `Dv x`.
      have hfun : (fun z => a z (fderiv ℝ v x) P) =
          fun z => ∑ r, b.repr (fderiv ℝ v x) r * a z (b r) P := by
        funext z
        conv_lhs => rw [← b.sum_repr (fderiv ℝ v x)]
        simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
          FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      have hsum : HasFDerivAt (fun z => a z (fderiv ℝ v x) P)
          (∑ r, b.repr (fderiv ℝ v x) r • fderiv ℝ (fun z => a z (b r) P) x) x := by
        rw [hfun]
        exact HasFDerivAt.fun_sum fun r _ =>
          ((((ha1 (b r) P).differentiableOn one_ne_zero) x hx).differentiableAt
            (hU.mem_nhds hx)).hasFDerivAt.const_mul _
      rw [hsum.fderiv]
      simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
        Pi.smul_apply, smul_eq_mul, hB]
    -- Step 10: the order-`m` case for the data `(U, lam, a, Ψ, D_s v)`.
    exact IH U lam a Ψ (fun z => fderiv ℝ v z (EuclideanSpace.single s (1 : ℝ))) hU hlam hell
      (fun P Q => ⟨(ha P Q).1.of_le hmm, Submission.dohr_eb_holder_of_contDiffOn_succ (Rn n) ℝ m α
        _ U hα hα1.le hU (ha P Q).1⟩) hΨm (hvs s) hΨweak

/-- Elliptic bootstrap in the proof of Simon Ch. 5, Theorem 7.1, second assertion (p. 127): one
Schauder step for the Euler–Lagrange system `∫_U DΨ(Du)[Dφ] = -∫_U ⟨φ, g⟩`.  Let `Ψ` be smooth
with `D²Ψ(P)` `lam`-Legendre for `‖P‖ ≤ ε`, `u ∈ C^{m+1,α}_loc(U)` with `‖Du‖ ≤ ε` on `U`
(`m ≥ 1`) and `g ∈ C^{m,α}_loc(U)`.  Each column `v_k = Du(·) e_k` is `C^{m,α}_loc` and solves the
differentiated system `∫_U D²Ψ(Du)[Dv_k][Dζ] = ∫_U ⟨g, Dζ e_k⟩`, whose coefficient `D²Ψ(Du)` is
`lam`-Legendre and `C^{m,α}_loc` (a smooth function of `Du`) and whose right side is a linear image
of `g`.  Linear Schauder theory gives `v_k ∈ C^{m+1,α}_loc` for every `k`, so
`u ∈ C^{m+2,α}_loc`. -/
theorem dohr_eb_el_higher_regularity_step : ∀ n ℓ : ℕ, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 → ∀ m : ℕ, 1 ≤ m → ∀ (Ψ : (Rn n →L[ℝ] Rn ℓ) → ℝ) (lam ε : ℝ) (U : Set (Rn n)) (u g : Rn n → Rn ℓ), 0 < lam → IsOpen U → ContDiff ℝ (⊤ : ℕ∞) Ψ → (∀ P : Rn n →L[ℝ] Rn ℓ, ‖P‖ ≤ ε → ∀ Q : Rn n →L[ℝ] Rn ℓ, lam * ‖Q‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ Ψ) P Q Q) → IsLocallyHolderCkα (m + 1) α u U → (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ ε) → IsLocallyHolderCkα m α g U → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x in U, fderiv ℝ Ψ (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x)) → IsLocallyHolderCkα (m + 2) α u U := by
  intro n ℓ hn α hα0 hα1 m hm Ψ lam ε U u g hlam hU hΨ hLeg hu hDu hg hEL
  -- Steps 0 and 5: `u` is `C¹` on `U` and every column `v_k = Du(·) e_k` is `C^{m,α}_loc`;
  -- moreover `Du` is `C^m` on `U` with `Dᵐ(Du)` `α`-Hölder on compact subsets of `U`.
  obtain ⟨hu1, hcols⟩ := (dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) m α u U hU).2.1 hu
  obtain ⟨-, hDuC, hDuH⟩ := (dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) m α u U hU).1.1 hu
  -- Step 1: `Ψ` is `C²` and `u` is `C²` on `U` (`m + 1 ≥ 2`), so the weak Euler–Lagrange
  -- system can be differentiated in every direction `e`.
  have hΨ2 : ContDiff ℝ 2 Ψ := hΨ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hD := dohr_eb_ehs_differentiated_el n ℓ Ψ U u g hU hΨ2 hu2 hg.1.continuousOn hEL
  -- Step 6: linear Schauder theory for `v_k`, with coefficient `a(x) = D²Ψ(Du(x))` and right
  -- side `Φ_k(x) = ⟨g(x), (·) e_k⟩`.
  have hk : ∀ k : Fin n, IsLocallyHolderCkα (m + 1) α
      (fun z => fderiv ℝ u z (EuclideanSpace.single k (1 : ℝ))) U := by
    intro k
    refine dohr_eb_linear_higher_regularity n ℓ hn α hα0 hα1 m hm U lam
      (fun x => fderiv ℝ (fderiv ℝ Ψ) (fderiv ℝ u x))
      (fun x => (innerSL ℝ (g x)).comp
        (ContinuousLinearMap.apply ℝ (Rn ℓ) (EuclideanSpace.single k (1 : ℝ))))
      (fun z => fderiv ℝ u z (EuclideanSpace.single k (1 : ℝ))) hU hlam ?_ ?_ ?_ (hcols k) ?_
    · -- Step 4: the Legendre condition holds on `U`, where `‖Du‖ ≤ ε`.
      intro x hx P
      exact hLeg _ (hDu x hx) P
    · -- Step 2: `x ↦ D²Ψ(Du(x))[P][Q]` is a smooth function of `Du`, hence `C^{m,α}_loc`.
      intro P Q
      have hsm := dohr_eb_ehs_hessian_apply_contDiff n ℓ Ψ hΨ P Q
      exact dohr_eb_holder_comp (Rn n) (Rn n →L[ℝ] Rn ℓ) ℝ m α (fderiv ℝ u)
        (fun R : Rn n →L[ℝ] Rn ℓ => fderiv ℝ (fderiv ℝ Ψ) R P Q) U univ hα0 hα1.le hU
        isOpen_univ (mapsTo_univ _ _) (Or.inl hm) hDuC hDuH
        (hsm.contDiffOn.of_le (by exact_mod_cast le_top))
        (dohr_eb_holder_of_contDiffOn_succ (Rn n →L[ℝ] Rn ℓ) ℝ m α _ univ hα0 hα1.le
          isOpen_univ (hsm.contDiffOn.of_le (by exact_mod_cast le_top)))
    · -- Step 3: `x ↦ Φ_k(x)[P] = ⟨g(x), P e_k⟩` is a linear image of `g`, hence `C^{m,α}_loc`.
      intro P
      simpa using
        dohr_eb_ehs_inner_right_holder n ℓ m α U g (P (EuclideanSpace.single k (1 : ℝ))) hU hg
    · -- Step 1 with `e = e_k`: `v_k` solves the system with coefficient `a` and right side `Φ_k`.
      intro ζ hζ1 hζc hζU
      simpa using hD (EuclideanSpace.single k (1 : ℝ)) ζ hζ1 hζc hζU
  -- Step 7: `u` is `C¹` on `U` and every `v_k` is `C^{m+1,α}_loc`, so `u` is `C^{m+2,α}_loc`.
  exact (dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) (m + 1) α u U hU).2.2 ⟨hu1, hk⟩

/-- **Schauder bootstrap for the prescribed-mean-curvature graph system** (Simon Ch. 5, proof of
Theorem 7.1, p. 128: "by the Schauder theory for elliptic equations we see that `h ∈ C^{q,α}`
implies `u ∈ C^{q+2,α}`").  Let `J(P) = det(I + (⟨Pe_a, Pe_b⟩)_{ab})^{1/2}` be the area integrand.
If `u` is `C^{1,β}` on `B̆_r(0)` (`α ≤ β ≤ 1`) with `Du(0) = 0`, `(x, u(x)) ∈ O` there, and `u`
weakly solves `∫ DJ(Du)[Dφ] = −∫ J(Du) ⟨(0, φ), F(x, u(x))⟩` for `F ∈ C^{q,α}_loc(O)`, then `u` is
`C^{q+2,α}` (`IsHolderCkα`) on some ball `B̆_{r'}(0)`, `0 < r' ≤ r`.  On a small-gradient ball the
system is Legendre-elliptic; its right side `J(Du) pv(F(x, u))` (`pv` = last `ℓ` coordinates) is
`C^{m,α}_loc` once `u` is `C^{m+1,α}_loc` (`m ≤ q`); Schauder theory then gives `C^{2,α}_loc` and,
inductively, `C^{q+2,α}_loc`, and global bounds follow on the half ball. -/
theorem dohr_elliptic_bootstrap : ∀ n ℓ : ℕ, 1 ≤ n → ∀ (q : ℕ) (α β : ℝ), 0 < α → α < 1 → α ≤ β → β ≤ 1 → ∀ (r : ℝ) (u : Rn n → Rn ℓ) (F : Amb n ℓ → Amb n ℓ) (O : Set (Amb n ℓ)), 0 < r → IsOpen O → IsLocallyHolderCkα q α F O → (∀ x ∈ ball (0 : Rn n) r, graphPoint x (u x) ∈ O) → ContDiffOn ℝ 1 u (ball 0 r) → fderiv ℝ u 0 = 0 → (∃ K : ℝ, ∀ x ∈ ball (0 : Rn n) r, ∀ y ∈ ball (0 : Rn n) r, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K * ‖x - y‖ ^ β) → (∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 r → ∫ x in ball (0 : Rn n) r, fderiv ℝ (fun P : Rn n →L[ℝ] Rn ℓ => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ))) (P (EuclideanSpace.single b (1 : ℝ)))))) (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in ball (0 : Rn n) r, Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ u x (EuclideanSpace.single a (1 : ℝ))) (fderiv ℝ u x (EuclideanSpace.single b (1 : ℝ))))) * inner ℝ (graphPoint 0 (φ x)) (F (graphPoint x (u x)))) → ∃ r' > 0, r' ≤ r ∧ IsHolderCkα (q + 2) α u (ball 0 r') := by
  intro n ℓ hn q α β hα0 hα1 hαβ hβ1 r u F O hr hO hF hGO hu hDu0 hβ hweak
  -- Step 1: the area integrand `J` is smooth and Legendre-elliptic (constant `1/2`) for `‖P‖ ≤ ε`.
  obtain ⟨hJs, ε, hε, hJleg⟩ := Submission.dohr_eb_area_integrand_legendre n ℓ
  set J : (Rn n →L[ℝ] Rn ℓ) → ℝ := fun P => Real.sqrt (Matrix.det ((1 : Matrix (Fin n) (Fin n) ℝ) +
    Matrix.of fun a b : Fin n => inner ℝ (P (EuclideanSpace.single a (1 : ℝ)))
      (P (EuclideanSpace.single b (1 : ℝ)))))
  -- A small-gradient ball `U = B̆_{r₁}(0)`, `r₁ ≤ r`, with `‖Du‖ ≤ ε` on `U` (`Du` is continuous
  -- at `0` and `Du(0) = 0`).
  have hcont : ContinuousAt (fderiv ℝ u) 0 :=
    (hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hcont ε hε
  set r₁ := min δ r
  have hr₁0 : 0 < r₁ := lt_min hδ hr
  have hr₁r : r₁ ≤ r := min_le_right _ _
  set U := ball (0 : Rn n) r₁
  have hUo : IsOpen U := isOpen_ball
  have hUr : U ⊆ ball 0 r := ball_subset_ball hr₁r
  have hDuε : ∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ ε := by
    intro x hx
    have h := hδε (lt_of_lt_of_le (mem_ball.mp hx) (min_le_left δ r))
    rw [hDu0, dist_zero_right] at h
    exact h.le
  have hu1 : ContDiffOn ℝ 1 u U := hu.mono hUr
  -- Step 2a: `u ∈ C^{1,α}_loc(U)`: `‖x − y‖^β ≤ (2r₁)^{β−α} ‖x − y‖^α` on `U`.
  obtain ⟨K₀, hK₀⟩ := hβ
  have hu1α : IsLocallyHolderCkα 1 α u U := by
    refine (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) 0 α u U hUo).1.mpr ⟨hu1, ?_, ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      exact hu1.continuousOn_fderiv_of_isOpen hUo le_rfl
    · intro K _ hKU
      refine ⟨max K₀ 0 * (2 * r₁) ^ (β - α), fun x hx y hy => ?_⟩
      have hxU := hKU hx
      have hyU := hKU hy
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply, ← map_sub,
        LinearIsometryEquiv.norm_map]
      have hxy : ‖x - y‖ ≤ 2 * r₁ := by
        have h1 := mem_ball_zero_iff.mp hxU
        have h2 := mem_ball_zero_iff.mp hyU
        linarith [norm_sub_le x y]
      have hsplit : ‖x - y‖ ^ β = ‖x - y‖ ^ (β - α) * ‖x - y‖ ^ α := by
        rw [← Real.rpow_add' (norm_nonneg _) (by linarith : (0 : ℝ) < β - α + α).ne',
          sub_add_cancel]
      have hpow : ‖x - y‖ ^ (β - α) ≤ (2 * r₁) ^ (β - α) :=
        Real.rpow_le_rpow (norm_nonneg _) hxy (sub_nonneg.mpr hαβ)
      calc ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ K₀ * ‖x - y‖ ^ β := hK₀ x (hUr hxU) y (hUr hyU)
        _ ≤ max K₀ 0 * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = max K₀ 0 * (‖x - y‖ ^ (β - α) * ‖x - y‖ ^ α) := by rw [hsplit]
        _ ≤ max K₀ 0 * ((2 * r₁) ^ (β - α) * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (norm_nonneg _) _))
            (le_max_right _ _)
        _ = max K₀ 0 * (2 * r₁) ^ (β - α) * ‖x - y‖ ^ α := by ring
  -- Step 2b: the vertical projection `pv` with `⟨(0, w), z⟩ = ⟨w, pv z⟩`.
  obtain ⟨pv, hpv⟩ : ∃ pv : Amb n ℓ →L[ℝ] Rn ℓ, ∀ (w : Rn ℓ) (z : Amb n ℓ),
      inner ℝ (graphPoint 0 w) z = inner ℝ w (pv z) := by
    let pvₗ : Amb n ℓ →ₗ[ℝ] Rn ℓ :=
      { toFun := fun z => WithLp.toLp 2 (fun j : Fin ℓ => z (Fin.natAdd n j))
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl }
    refine ⟨LinearMap.toContinuousLinearMap pvₗ, fun w z => ?_⟩
    simp only [graphPoint, PiLp.inner_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      WithLp.ofLp_zero, Pi.zero_apply, inner_zero_left, Finset.sum_const_zero, zero_add,
      LinearMap.coe_toContinuousLinearMap', pvₗ]
    rfl
  -- Step 2c: the graph map `G(x) = (x, u(x))` is as smooth as `u`.
  set G : Rn n → Amb n ℓ := fun x => graphPoint x (u x)
  have hGU : MapsTo G U O := fun x hx => hGO x (hUr hx)
  have hGcd : ∀ k : WithTop ℕ∞, ContDiffOn ℝ k u U → ContDiffOn ℝ k G U := by
    intro k hk
    refine (contDiffOn_piLp 2).2 fun i => ?_
    induction i using Fin.addCases with
    | left j =>
      simp only [G, graphPoint, WithLp.ofLp_toLp, Fin.append_left]
      exact (contDiff_piLp_apply 2).contDiffOn
    | right j =>
      simp only [G, graphPoint, WithLp.ofLp_toLp, Fin.append_right]
      exact (contDiff_piLp_apply 2).comp_contDiffOn hk
  -- The right-hand side `g(x) = J(Du(x)) pv(F(x, u(x)))` of the weak system.
  set g : Rn n → Rn ℓ := fun x => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Rn ℓ →L[ℝ] Rn ℓ)
    ((J ∘ fderiv ℝ u) x) (((pv ∘ F) ∘ G) x)
  -- Step 2d / 5: `g ∈ C^{m,α}_loc(U)` whenever `m ≤ q` and `u ∈ C^{m+1,α}_loc(U)`.
  obtain ⟨hFc, hFh⟩ := hF
  have hgreg : ∀ m : ℕ, m ≤ q → IsLocallyHolderCkα (m + 1) α u U → IsLocallyHolderCkα m α g U := by
    intro m hmq hum
    obtain ⟨-, hDum, hDuh⟩ :=
      (Submission.dohr_eb_holder_succ_iff_fderiv n (Rn ℓ) m α u U hUo).1.mp hum
    have hJm : ∀ k : ℕ, ContDiffOn ℝ k J univ := fun k => (contDiff_infty.mp hJs k).contDiffOn
    have hJ1 : ContDiffOn ℝ 1 J univ := by exact_mod_cast hJm 1
    have h1 := Submission.dohr_eb_holder_comp (Rn n) (Rn n →L[ℝ] Rn ℓ) ℝ m α (fderiv ℝ u) J U univ
      hα0 hα1.le hUo isOpen_univ (mapsTo_univ _ _) (Or.inr (Or.inr hJ1)) hDum hDuh (hJm m)
      (Submission.dohr_eb_holder_of_contDiffOn_succ (Rn n →L[ℝ] Rn ℓ) ℝ m α J univ hα0 hα1.le
        isOpen_univ (hJm (m + 1)))
    have hFm : ContDiffOn ℝ m F O := hFc.of_le (by exact_mod_cast hmq)
    have hFmh : ∀ K : Set (Amb n ℓ), IsCompact K → K ⊆ O → ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K,
        ‖iteratedFDeriv ℝ m F x - iteratedFDeriv ℝ m F y‖ ≤ C * ‖x - y‖ ^ α := by
      rcases Nat.lt_or_eq_of_le hmq with hlt | heq
      · exact Submission.dohr_eb_holder_of_contDiffOn_succ (Amb n ℓ) (Amb n ℓ) m α F O hα0 hα1.le
          hO (hFc.of_le (by exact_mod_cast Nat.succ_le_of_lt hlt))
      · rw [heq]
        exact hFh
    have hpv : ∀ k : WithTop ℕ∞, ContDiffOn ℝ k pv univ := fun k => pv.contDiff.contDiffOn
    have h2 := Submission.dohr_eb_holder_comp (Amb n ℓ) (Amb n ℓ) (Rn ℓ) m α F pv O univ hα0 hα1.le
      hO isOpen_univ (mapsTo_univ _ _) (Or.inr (Or.inr (hpv 1))) hFm hFmh (hpv m)
      (Submission.dohr_eb_holder_of_contDiffOn_succ (Amb n ℓ) (Rn ℓ) m α pv univ hα0 hα1.le
        isOpen_univ (hpv _))
    have hGm1 : ContDiffOn ℝ (m + 1 : ℕ) G U := hGcd _ hum.1
    have h3 := Submission.dohr_eb_holder_comp (Rn n) (Amb n ℓ) (Rn ℓ) m α G (pv ∘ F) U O hα0
      hα1.le hUo hO hGU (Or.inr (Or.inl (hGcd 1 hu1)))
      (hGm1.of_le (by exact_mod_cast Nat.le_succ m))
      (Submission.dohr_eb_holder_of_contDiffOn_succ (Rn n) (Amb n ℓ) m α G U hα0 hα1.le hUo hGm1)
      h2.1 h2.2
    exact Submission.dohr_eb_holder_bilinear (Rn n) ℝ (Rn ℓ) (Rn ℓ) m α
      (ContinuousLinearMap.lsmul ℝ ℝ) (J ∘ fderiv ℝ u) ((pv ∘ F) ∘ G) U hα0 hα1.le hUo h1.1 h1.2
      h3.1 h3.2
  -- Step 3: the weak system on `U`, with right-hand side `g`.
  have hweakU : ∀ φ : Rn n → Rn ℓ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, fderiv ℝ J (fderiv ℝ u x) (fderiv ℝ φ x) = -∫ x in U, inner ℝ (φ x) (g x) := by
    intro φ hφ hφc hφU
    have hout : ∀ x ∈ ball (0 : Rn n) r \ U, x ∉ tsupport φ := fun x hx h' => hx.2 (hφU h')
    have h := hweak φ hφ hφc (hφU.trans hUr)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hUr fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ (hout x hx), map_zero]] at h
    rw [h, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hUr fun x hx => by
      rw [hpv, image_eq_zero_of_notMem_tsupport (hout x hx), inner_zero_left, mul_zero]]
    congr 1
    refine setIntegral_congr_fun hUo.measurableSet fun x _ => ?_
    simp only [g, Function.comp_apply, ContinuousLinearMap.lsmul_apply, real_inner_smul_right,
      ← hpv, G, J]
  -- Steps 4–5: `C^{2,α}_loc` (Schauder) and the bootstrap up to `C^{q+2,α}_loc` on `U`.
  have hmain : ∀ m : ℕ, m ≤ q → IsLocallyHolderCkα (m + 2) α u U := by
    intro m
    induction m with
    | zero =>
      intro _
      exact Submission.dohr_eb_el_c2alpha_regularity n ℓ hn α hα0 hα1 J (1 / 2) ε U u g
        (by norm_num) hUo hJs hJleg hu1α hDuε (hgreg 0 (Nat.zero_le q) hu1α) hweakU
    | succ k ih =>
      intro hk
      have hk2 : IsLocallyHolderCkα (k + 2) α u U := ih (Nat.le_of_succ_le hk)
      exact Submission.dohr_eb_el_higher_regularity_step n ℓ hn α hα0 hα1 (k + 1) (Nat.succ_pos k)
        J (1 / 2) ε U u g (by norm_num) hUo hJs hJleg hk2 hDuε (hgreg (k + 1) hk hk2) hweakU
  -- Step 6: global `C^{q+2,α}` bounds on the half ball `B̆_{r₁/2}(0)`.
  exact ⟨r₁ / 2, half_pos hr₁0, (half_le_self hr₁0.le).trans hr₁r,
    Submission.dohr_eb_isHolderCk_half_ball n ℓ (q + 2) α u 0 r₁ (hmain q le_rfl)⟩

end Submission

end GMT.Ch05

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

/-- **Mollifications of a weakly harmonic function are harmonic** (step 2 of the proof of
Weyl's lemma, used for Simon Ch. 5, Lemma 3.1).  Let `w` be integrable on `B = B̆₁(0)` with
`∫_B w Δζ = 0` for every `ζ ∈ C^∞_c(B)`, and let `κ` be `C^∞` with `κ(z) = 0` whenever `|z| ≥ ε`.
Then `v(x) = ∫_B κ(x - y) w(y) dy` is `C^∞` on `ℝⁿ` and `Δv = 0` on `B̆_{1-ε}(0)`.

With `W = 1_B w`, `v = W ⋆ κ` is the convolution of an integrable function with a smooth
compactly supported kernel, so `v` is smooth and its derivatives fall on the kernel; summing over
an orthonormal basis gives `Δv(x) = ∫_B Δκ(x - t) w(t) dt`.  For `|x| < 1 - ε`,
`ζ(y) = κ(x - y)` is a test function with `tsupport ζ ⊆ B̄_ε(x) ⊆ B` and `Δζ(y) = Δκ(x - y)`, so
`Δv(x) = ∫_B w Δζ = 0`. -/
theorem ball_convolution_contDiff_laplacian_eq_zero : ∀ n : ℕ, 1 ≤ n → ∀ w : Rn n → ℝ, IntegrableOn w (ball (0 : Rn n) 1) → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 1 → ∫ x in ball (0 : Rn n) 1, w x * Laplacian.laplacian ζ x = 0) → ∀ (κ : Rn n → ℝ) (ε : ℝ), ContDiff ℝ (⊤ : ℕ∞) κ → (∀ z : Rn n, ε ≤ ‖z‖ → κ z = 0) → ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) ∧ ∀ x ∈ ball (0 : Rn n) (1 - ε), Laplacian.laplacian (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) x = 0 := by
  intro n _hn w hw hharm κ ε hκ hκε
  -- Step 1: `W = 1_B w` is integrable and `v = W ⋆ κ` (convolution with `L = lsmul`).
  set W : Rn n → ℝ := (ball (0 : Rn n) 1).indicator w with hWdef
  have hWloc : LocallyIntegrable W :=
    ((integrable_indicator_iff measurableSet_ball).2 hw).locallyIntegrable
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hv : (fun x => ∫ y in ball (0 : Rn n) 1, κ (x - y) * w y) =
      convolution (𝕜 := ℝ) W κ L volume := by
    funext x
    rw [convolution_def, ← integral_indicator measurableSet_ball]
    congr 1
    funext t
    by_cases ht : t ∈ ball (0 : Rn n) 1
    · simp [hWdef, hLdef, Set.indicator_of_mem ht, mul_comm]
    · simp [hWdef, hLdef, Set.indicator_of_notMem ht]
  -- Step 2: `κ = 0` off `B̄_ε(0)`, so `κ`, `Dκ` and `D²κ` are smooth with compact support.
  have hκc : HasCompactSupport κ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) ε) (fun z hz => hκε z ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hκ1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ κ) := (contDiff_infty_iff_fderiv.1 hκ).2
  have hκ2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ κ)) := (contDiff_infty_iff_fderiv.1 hκ1).2
  have hκ1c : HasCompactSupport (fderiv ℝ κ) := hκc.fderiv ℝ
  have hκ2c : HasCompactSupport (fderiv ℝ (fderiv ℝ κ)) := hκ1c.fderiv ℝ
  have hκ2cont : Continuous (fderiv ℝ (fderiv ℝ κ)) := hκ2.continuous
  -- Step 3: `v = W ⋆ κ` is smooth.
  refine ⟨?_, ?_⟩
  · rw [hv]
    exact hκc.contDiff_convolution_right L hWloc hκ
  -- Steps 4–5: derivatives fall on the kernel, `D²v(x)[e, e] = ∫ W(t) D²κ(x - t)[e, e] dt`.
  have hD2 : fderiv ℝ (fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume)) =
      convolution (𝕜 := ℝ) W (fderiv ℝ (fderiv ℝ κ)) ((L.precompR (Rn n)).precompR (Rn n))
        volume := by
    have hD1 : fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume) =
        convolution (𝕜 := ℝ) W (fderiv ℝ κ) (L.precompR (Rn n)) volume := by
      funext x
      exact (hκc.hasFDerivAt_convolution_right L hWloc (hκ.of_le (mod_cast le_top)) x).fderiv
    rw [hD1]
    funext x
    exact (hκ1c.hasFDerivAt_convolution_right (L.precompR (Rn n)) hWloc
      (hκ1.of_le (mod_cast le_top)) x).fderiv
  have hD2v : ∀ x e : Rn n, fderiv ℝ (fderiv ℝ (convolution (𝕜 := ℝ) W κ L volume)) x e e =
      ∫ t, W t * fderiv ℝ (fderiv ℝ κ) (x - t) e e := by
    intro x e
    rw [hD2, convolution_precompR_apply (L.precompR (Rn n)) hWloc hκ2c hκ2cont x e,
      convolution_precompR_apply L hWloc (hκ1c.fderiv_apply ℝ e)
        (hκ2cont.clm_apply continuous_const) x e, convolution_def]
    simp [hLdef]
  -- Each `t ↦ W(t) D²κ(x - t)[e, e]` is integrable: `D²κ(·)[e, e]` is continuous with compact
  -- support.
  have hint : ∀ x e : Rn n, Integrable (fun t => W t * fderiv ℝ (fderiv ℝ κ) (x - t) e e) := by
    intro x e
    have hc : HasCompactSupport (fun a => fderiv ℝ (fderiv ℝ κ) a e e) :=
      (hκ1c.fderiv_apply ℝ e).comp_left (g := fun T : Rn n →L[ℝ] ℝ => T e) (by simp)
    exact hc.convolutionExists_right L hWloc
      ((hκ2cont.clm_apply continuous_const).clm_apply continuous_const) x
  -- Step 6: `Δf(x) = ∑ᵢ D²f(x)[bᵢ, bᵢ]` for the standard orthonormal basis `b`.
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hlap : ∀ (f : Rn n → ℝ) (x : Rn n),
      Laplacian.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
    intro f x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    simp [iteratedFDeriv_two_apply]
  -- Step 7: for `|x| < 1 - ε`, `ζ(y) = κ(x - y)` is a test function with `tsupport ζ ⊆ B`.
  intro x hx
  set ζ : Rn n → ℝ := fun y => κ (x - y) with hζdef
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := hκ.comp (contDiff_const.sub contDiff_id)
  have hζsupp : Function.support ζ ⊆ closedBall x ε := by
    intro y hy
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra h
    exact hy (hκε _ (not_le.1 h).le)
  have hζc : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall x ε)
      (fun y hy => by_contra (fun h => hy (hζsupp h)))
  have hζB : tsupport ζ ⊆ ball 0 1 := by
    refine (closure_minimal hζsupp isClosed_closedBall).trans (closedBall_subset_ball' ?_)
    rw [mem_ball] at hx
    linarith
  -- Step 8: `Δζ(t) = Δκ(x - t)`, writing `ζ = κ(x + ·) ∘ (-id)`.
  have hκx : ContDiff ℝ (⊤ : ℕ∞) (fun z => κ (x + z)) := hκ.comp (contDiff_const.add contDiff_id)
  have hcomp : ζ = (fun z => κ (x + z)) ∘ (-(ContinuousLinearMap.id ℝ (Rn n))) := by
    funext y
    simp [hζdef, sub_eq_add_neg]
  have hlapζ : ∀ t,
      Laplacian.laplacian ζ t = ∑ i, fderiv ℝ (fderiv ℝ κ) (x - t) (b i) (b i) := by
    intro t
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ζ b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (i := 2) _ hκx t
        (WithTop.coe_le_coe.2 le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left,
      iteratedFDeriv_two_apply]
    simp [sub_eq_add_neg]
  -- Steps 6 and 9: `Δv(x) = ∑ᵢ ∫ W(t) D²κ(x - t)[bᵢ, bᵢ] dt = ∫_B w(t) Δζ(t) dt = 0`.
  rw [hv, hlap]
  simp_rw [hD2v]
  rw [← integral_finsetSum _ (fun i _ => hint x (b i)), ← hharm ζ hζ hζc hζB,
    ← integral_indicator measurableSet_ball]
  congr 1
  funext t
  by_cases ht : t ∈ ball (0 : Rn n) 1
  · rw [Set.indicator_of_mem ht, hlapζ t, Finset.mul_sum]
    simp [hWdef, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    simp [hWdef, Set.indicator_of_notMem ht]
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), Weyl's lemma for the weak limit `w`: the mean-value
kernel.  With `E(σ) = expNegInvGlue (1 − σ)` (`C^∞`, `≥ 0`, `0` for `σ ≥ 1`, `> 0` for `σ < 1`),
`ρ(z) = c E(|z|²)` with `c = (∫ E(|z|²) dz)⁻¹` is `C^∞`, even, zero for `|z| ≥ 1` and of mass `1`;
`Ψ(z) = (c/2) P(|z|²)` with `P(σ) = ∫_1^σ E` is `C^∞` (`P' = E` by FTC), zero for `|z| ≥ 1`, and
`DΨ(z)[v] = (c/2) E(|z|²) 2⟨z, v⟩ = ρ(z)⟨z, v⟩` by the chain rule. -/
theorem mvk_exists_kernel_potential : ∀ n : ℕ, ∃ ρ Ψ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) ∧ (∀ z : Rn n, ρ (-z) = ρ z) ∧ ∫ z, ρ z = 1 ∧ ∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v := by
  intro n
  -- The profile `E(σ) = expNegInvGlue (1 - σ)`: `C^∞`, `≥ 0`, `0` for `σ ≥ 1`, `> 0` for `σ < 1`.
  set E : ℝ → ℝ := fun σ => expNegInvGlue (1 - σ)
  have hE_smooth : ContDiff ℝ (⊤ : ℕ∞) E :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
  have hE_cont : Continuous E := hE_smooth.continuous
  have hE_nonneg : ∀ σ, 0 ≤ E σ := fun σ => expNegInvGlue.nonneg _
  have hE_zero : ∀ σ, 1 ≤ σ → E σ = 0 := fun σ hσ =>
    expNegInvGlue.zero_of_nonpos (by linarith)
  have hE_pos : ∀ σ, σ < 1 → 0 < E σ := fun σ hσ =>
    expNegInvGlue.pos_of_pos (by linarith)
  -- The unnormalized kernel `ρ₀(z) = E(‖z‖²)`: `C^∞`, zero for `‖z‖ ≥ 1`, of positive mass.
  set ρ₀ : Rn n → ℝ := fun z => E (‖z‖ ^ 2) with hρ₀_def
  have hρ₀_smooth : ContDiff ℝ (⊤ : ℕ∞) ρ₀ := hE_smooth.comp (contDiff_norm_sq ℝ)
  have hρ₀_zero : ∀ z : Rn n, 1 ≤ ‖z‖ → ρ₀ z = 0 := fun z hz =>
    hE_zero _ (one_le_pow₀ hz)
  have hρ₀_supp : HasCompactSupport ρ₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) 1) fun z hz =>
      hρ₀_zero z (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)
  have hρ₀_int : Integrable ρ₀ := hρ₀_smooth.continuous.integrable_of_hasCompactSupport hρ₀_supp
  have hI₀_pos : 0 < ∫ z, ρ₀ z := by
    rw [integral_pos_iff_support_of_nonneg (fun z => hE_nonneg _) hρ₀_int]
    refine (measure_ball_pos volume (0 : Rn n) one_pos).trans_le (measure_mono fun z hz => ?_)
    rw [mem_ball_zero_iff] at hz
    exact (hE_pos _ (pow_lt_one₀ (norm_nonneg z) hz two_ne_zero)).ne'
  set c : ℝ := (∫ z, ρ₀ z)⁻¹ with hc_def
  -- The primitive `P(σ) = ∫_1^σ E`: `P' = E` (FTC), so `P` is `C^∞`; `P = 0` on `[1, ∞)`.
  set P : ℝ → ℝ := fun σ => ∫ s in (1 : ℝ)..σ, E s with hP_def
  have hP_deriv : ∀ σ, HasDerivAt P (E σ) σ := fun σ =>
    (hE_cont.integral_hasStrictDerivAt 1 σ).hasDerivAt
  have hP_smooth : ContDiff ℝ (⊤ : ℕ∞) P :=
    contDiff_infty_iff_deriv.2 ⟨fun σ => (hP_deriv σ).differentiableAt,
      (funext fun σ => (hP_deriv σ).deriv : deriv P = E) ▸ hE_smooth⟩
  have hP_zero : ∀ σ, 1 ≤ σ → P σ = 0 := fun σ hσ => by
    simp only [hP_def]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [uIcc_of_le hσ] at hs
      exact hE_zero s hs.1
  -- `ρ = c ρ₀` and `Ψ(z) = (c/2) P(‖z‖²)`.
  refine ⟨fun z => c * ρ₀ z, fun z => c / 2 * P (‖z‖ ^ 2), contDiff_const.mul hρ₀_smooth,
    contDiff_const.mul (hP_smooth.comp (contDiff_norm_sq ℝ)), fun z hz => ?_, fun z hz => ?_,
    fun z => ?_, ?_, fun z v => ?_⟩
  · show c * ρ₀ z = 0
    rw [hρ₀_zero z hz, mul_zero]
  · show c / 2 * P (‖z‖ ^ 2) = 0
    rw [hP_zero _ (one_le_pow₀ hz), mul_zero]
  · simp only [hρ₀_def, norm_neg]
  · rw [integral_const_mul, hc_def, inv_mul_cancel₀ hI₀_pos.ne']
  · -- Chain rule: `DΨ(z)[v] = (c/2) E(‖z‖²) 2⟨z, v⟩ = ρ(z) ⟨z, v⟩`.
    have h : HasFDerivAt (fun z : Rn n => c / 2 * P (‖z‖ ^ 2))
        ((c / 2) • (E (‖z‖ ^ 2) • (2 • innerSL ℝ z))) z :=
      ((hP_deriv _).comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_mul _
    rw [h.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, hρ₀_def]
    push_cast
    ring
/-- Fundamental theorem of calculus along rays, averaged against a kernel (used for the mean value
kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): for continuous `ρ` vanishing where
`‖z‖ ≥ 1`, `h ∈ C¹` and `t ≥ 0`,
`∫ ρ(z) h(x₀ + t z) dz = (∫ ρ) h(x₀) + ∫₀ᵗ ∫ ρ(z) Dh(x₀ + σ z)[z] dz dσ`.  Raywise FTC, then
Fubini for the continuous integrand, which vanishes off `[0, t] × B₁(0)`. -/
theorem mvk_integral_ray_fubini : ∀ (n : ℕ) (ρ h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 ≤ t → Continuous ρ → (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) → ContDiff ℝ 1 h → ∫ z, ρ z * h (x₀ + t • z) = (∫ z, ρ z) * h x₀ + ∫ σ in (0 : ℝ)..t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z := by
  intro n ρ h x₀ t ht hρ hρ0 hh
  -- `ρ` vanishes off the compact closed unit ball, so it has compact support.
  have hρs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) 1) fun z hz => hρ0 z ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hDh : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  -- Products of `ρ` with continuous functions are integrable.
  have hint : ∀ g : Rn n → ℝ, Continuous g → Integrable fun z => ρ z * g z := fun g hg =>
    (hρ.mul hg).integrable_of_hasCompactSupport hρs.mul_right
  -- FTC along the ray `σ ↦ x₀ + σ • z`, multiplied by the constant `ρ z`.
  have hftc : ∀ z : Rn n, ∫ σ in (0 : ℝ)..t, ρ z * fderiv ℝ h (x₀ + σ • z) z =
      ρ z * h (x₀ + t • z) - ρ z * h x₀ := by
    intro z
    have hderiv : ∀ σ : ℝ,
        HasDerivAt (fun σ : ℝ => h (x₀ + σ • z)) (fderiv ℝ h (x₀ + σ • z) z) σ := by
      intro σ
      have hray : HasDerivAt (fun σ : ℝ => x₀ + σ • z) z σ := by
        simpa using ((hasDerivAt_id σ).smul_const z).const_add x₀
      exact (hhd (x₀ + σ • z)).hasFDerivAt.comp_hasDerivAt σ hray
    have hcont : Continuous fun σ : ℝ => fderiv ℝ h (x₀ + σ • z) z := by fun_prop
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
        (hcont.intervalIntegrable _ _), zero_smul, add_zero, mul_sub]
  -- The integrand is integrable on `(0, t] × ℝⁿ`: it is continuous and vanishes off the compact
  -- set `[0, t] × B₁(0)`.
  have hF : Integrable
      (Function.uncurry fun (σ : ℝ) (z : Rn n) => ρ z * fderiv ℝ h (x₀ + σ • z) z)
      ((volume.restrict (uIoc (0 : ℝ) t)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hK : IntegrableOn
        (Function.uncurry fun (σ : ℝ) (z : Rn n) => ρ z * fderiv ℝ h (x₀ + σ • z) z)
        (Icc (0 : ℝ) t ×ˢ closedBall (0 : Rn n) 1) (volume.prod volume) :=
      (Continuous.continuousOn (by fun_prop)).integrableOn_compact
        (isCompact_Icc.prod (isCompact_closedBall _ _))
    refine hK.of_forall_sdiff_eq_zero (measurableSet_uIoc.prod MeasurableSet.univ) ?_
    rintro ⟨σ, z⟩ ⟨⟨hσ, -⟩, hnot⟩
    rw [uIoc_of_le ht] at hσ
    have hz : z ∉ closedBall (0 : Rn n) 1 := fun hz => hnot ⟨Ioc_subset_Icc_self hσ, hz⟩
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    simp [hρ0 z hz.le]
  -- Fubini, then integrate the raywise identity over `z`.
  rw [MeasureTheory.intervalIntegral_integral_swap hF]
  simp_rw [hftc]
  rw [integral_sub (hint (fun z => h (x₀ + t • z)) (by fun_prop))
    (hint (fun _ => h x₀) continuous_const), integral_mul_const]
  ring
/-- Green's first identity on `ℝⁿ` against a compactly supported `C¹` function (used for the mean
value kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): if `H` is `C²`, `Ψ` is `C¹` with
compact support and `w = ∇Ψ`, then `∫ DH(z)[w(z)] dz = -∫ ΔH(z) Ψ(z) dz`.  Each coordinate
integration by parts reduces to `∫ DG(z)[v] dz = 0` for a compactly supported `C¹` function `G`,
which holds because `t ↦ ∫ G(z + t v) dz` is constant by translation invariance. -/
theorem mvk_integral_fderiv_grad_eq_neg_laplacian : ∀ (n : ℕ) (H Ψ : Rn n → ℝ) (w : Rn n → Rn n), ContDiff ℝ 2 H → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → (∀ z v : Rn n, fderiv ℝ Ψ z v = inner ℝ (w z) v) → ∫ z, fderiv ℝ H z (w z) = -∫ z, Laplacian.laplacian H z * Ψ z := by
  intro n H Ψ w hH hΨ hΨc hw
  -- For a compactly supported `C¹` function `G` and a direction `v`, `∫ DG(z)[v] dz = 0`:
  -- `t ↦ ∫ G(z + t v) dz` is constant by translation invariance, and its derivative at `0` is
  -- `∫ DG(z)[v] dz` by differentiation under the integral sign.
  have key : ∀ G : Rn n → ℝ, ContDiff ℝ 1 G → HasCompactSupport G → ∀ v : Rn n,
      ∫ z, fderiv ℝ G z v = 0 := by
    intro G hG hGc v
    have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
    have hG' : Continuous fun y => fderiv ℝ G y v :=
      (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨C, hC⟩ := hG'.bounded_above_of_compact_support (hGc.fderiv_apply ℝ v)
    obtain ⟨R, -, hR⟩ := (hGc.fderiv_apply ℝ v).exists_pos_le_norm
    -- For `|t| < 1`, `|DG(z + t v)[v]|` is bounded by `C` times the indicator of `B_{R + |v|}(0)`.
    have hbound : Integrable ((closedBall (0 : Rn n) (R + ‖v‖)).indicator fun _ => C) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    have hb : ∀ z : Rn n, ∀ t ∈ ball (0 : ℝ) 1,
        ‖fderiv ℝ G (z + t • v) v‖ ≤ (closedBall (0 : Rn n) (R + ‖v‖)).indicator (fun _ => C) z := by
      intro z t ht
      by_cases hz : z ∈ closedBall (0 : Rn n) (R + ‖v‖)
      · rw [indicator_of_mem hz]
        exact hC _
      · rw [mem_closedBall, dist_zero_right, not_le] at hz
        rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
        have h1 : ‖t • v‖ ≤ ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.le
        have h2 : ‖z‖ ≤ ‖z + t • v‖ + ‖t • v‖ := by
          calc ‖z‖ = ‖(z + t • v) - t • v‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖z + t • v‖ + ‖t • v‖ := norm_sub_le _ _
        have hRz : R ≤ ‖z + t • v‖ := by linarith
        rw [hR _ hRz, norm_zero]
        exact indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hC 0)) _
    have hdiff : ∀ z : Rn n, ∀ t ∈ ball (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => G (z + t • v)) (fderiv ℝ G (z + t • v) v) t := by
      intro z t _
      have h1 : HasDerivAt (fun t : ℝ => z + t • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add z
      exact (hGd (z + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have hd : HasDerivAt (fun t : ℝ => ∫ z, G (z + t • v)) (∫ z, fderiv ℝ G (z + (0 : ℝ) • v) v) 0 :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
        (F := fun (t : ℝ) (z : Rn n) => G (z + t • v))
        (F' := fun (t : ℝ) (z : Rn n) => fderiv ℝ G (z + t • v) v)
        (x₀ := 0) (ball_mem_nhds (0 : ℝ) one_pos)
        (Eventually.of_forall fun t =>
          (hG.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
        (by simpa using hG.continuous.integrable_of_hasCompactSupport hGc)
        ((hG'.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
        (Eventually.of_forall hb) hbound (Eventually.of_forall hdiff)).2
    have hd0 : HasDerivAt (fun t : ℝ => ∫ z, G (z + t • v)) 0 0 := by
      have hconst : (fun t : ℝ => ∫ z, G (z + t • v)) = fun _ => ∫ z, G z :=
        funext fun t => integral_add_right_eq_self G (t • v)
      rw [hconst]
      exact hasDerivAt_const _ _
    simpa using hd.unique hd0
  -- Integration by parts in the direction `v` against `Ψ`, applying `key` to `f Ψ`.
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable one_ne_zero
  have ibp : ∀ f : Rn n → ℝ, ContDiff ℝ 1 f → ∀ v : Rn n,
      Integrable (fun z => fderiv ℝ f z v * Ψ z) ∧ Integrable (fun z => f z * fderiv ℝ Ψ z v) ∧
        ∫ z, f z * fderiv ℝ Ψ z v = -∫ z, fderiv ℝ f z v * Ψ z := by
    intro f hf v
    have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
    have h1 : Integrable (fun z => fderiv ℝ f z v * Ψ z) :=
      (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hΨ.continuous).integrable_of_hasCompactSupport hΨc.mul_left
    have h2 : Integrable (fun z => f z * fderiv ℝ Ψ z v) :=
      (hf.continuous.mul ((hΨ.continuous_fderiv one_ne_zero).clm_apply
        continuous_const)).integrable_of_hasCompactSupport (hΨc.fderiv_apply ℝ v).mul_left
    refine ⟨h1, h2, ?_⟩
    have h3 := key (fun z => f z * Ψ z) (hf.mul hΨ) hΨc.mul_left v
    have h4 : ∀ z, fderiv ℝ (fun z => f z * Ψ z) z v =
        fderiv ℝ f z v * Ψ z + f z * fderiv ℝ Ψ z v := by
      intro z
      rw [show (fun z => f z * Ψ z) = f * Ψ from rfl, fderiv_mul (hfd z) (hΨd z)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    simp only [h4] at h3
    rw [integral_add h1 h2] at h3
    linarith
  -- Second derivatives: `D(DH(·)[v])(z)[v] = D²H(z)[v, v]`.
  have hH1 : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hd2 : ∀ v z : Rn n,
      fderiv ℝ (fun y => fderiv ℝ H y v) z v = iteratedFDeriv ℝ 2 H z ![v, v] := by
    intro v z
    rw [iteratedFDeriv_two_apply,
      fderiv_clm_apply ((hH1.differentiable one_ne_zero) z) (differentiableAt_const v)]
    simp
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  -- `DH(z)[w(z)] = Σᵢ ∂ᵢH(z) ∂ᵢΨ(z)`, expanding `w(z)` in the standard orthonormal basis.
  have hexp : ∀ z, fderiv ℝ H z (w z) = ∑ i, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) := by
    intro z
    conv_lhs => rw [← e.sum_repr' (w z)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, hw, real_inner_comm (w z) (e i)]
    ring
  -- `ΔH(z) = Σᵢ D²H(z)[eᵢ, eᵢ]`.
  have hlap : ∀ z, Laplacian.laplacian H z * Ψ z =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z := by
    intro z
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis H e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hd2]
  have hfC : ∀ i, ContDiff ℝ 1 (fun y => fderiv ℝ H y (e i)) := fun i => hH1.clm_apply contDiff_const
  calc ∫ z, fderiv ℝ H z (w z) = ∫ z, ∑ i, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) := by
        simp only [hexp]
    _ = ∑ i, ∫ z, fderiv ℝ H z (e i) * fderiv ℝ Ψ z (e i) :=
        integral_finsetSum _ fun i _ => (ibp _ (hfC i) (e i)).2.1
    _ = ∑ i, -∫ z, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z :=
        Finset.sum_congr rfl fun i _ => (ibp _ (hfC i) (e i)).2.2
    _ = -∫ z, ∑ i, fderiv ℝ (fun y => fderiv ℝ H y (e i)) z (e i) * Ψ z := by
        rw [integral_finsetSum _ fun i _ => (ibp _ (hfC i) (e i)).1, Finset.sum_neg_distrib]
    _ = -∫ z, Laplacian.laplacian H z * Ψ z := by
        simp only [hlap]
/-- **Laplacian of an affinely rescaled `C²` function** (scaling step in the mean value property
behind Weyl's lemma, used for Simon Ch. 5, Lemma 3.1, p. 114).  If `h : ℝⁿ → ℝ` is `C²`, then
`Δ(y ↦ h(x₀ + σ y))(z) = σ² Δh(x₀ + σ z)` for all `x₀, z ∈ ℝⁿ` and `σ ∈ ℝ`.
Proof: `y ↦ h(x₀ + σ y) = h₀ ∘ L` with `h₀ = h(x₀ + ·)` of class `C²` and `L = σ • id`.  Expanding
both Laplacians in the standard orthonormal basis `(eᵢ)`, it suffices that
`D²(h₀ ∘ L)(z)[eᵢ, eᵢ] = D²h₀(σ z)[σ eᵢ, σ eᵢ] = σ² D²h₀(σ z)[eᵢ, eᵢ]` (composition with a linear
map on the right, then multilinearity) and `D²h₀(σ z) = D²h(x₀ + σ z)` (translation). -/
theorem mvk_laplacian_comp_add_smul : ∀ (n : ℕ) (h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), ContDiff ℝ 2 h → ∀ z : Rn n, Laplacian.laplacian (fun y => h (x₀ + σ • y)) z = σ ^ 2 * Laplacian.laplacian h (x₀ + σ • z) := by
  intro n h x₀ σ hh z
  -- Step 1: `y ↦ h (x₀ + σ • y) = h₀ ∘ L`, where `h₀ y = h (x₀ + y)` is `C²` and `L = σ • id`.
  have h₀ : ContDiff ℝ 2 (fun y : Rn n => h (x₀ + y)) := hh.comp (contDiff_const.add contDiff_id)
  set L : Rn n →L[ℝ] Rn n := σ • ContinuousLinearMap.id ℝ (Rn n)
  have hcomp : (fun y => h (x₀ + σ • y)) = (fun y => h (x₀ + y)) ∘ L := by
    ext y
    simp [L]
  -- Step 2: expand both Laplacians in the standard orthonormal basis `eᵢ`.
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e, Finset.mul_sum, hcomp]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Step 3: `D²(h₀ ∘ L)(z)[eᵢ, eᵢ] = D²h₀(σ z)[σ eᵢ, σ eᵢ] = σ² D²h₀(σ z)[eᵢ, eᵢ]`.
  rw [L.iteratedFDeriv_comp_right h₀ z le_rfl, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hsmul : (fun j => L (![e i, e i] j)) = fun j => σ • ![e i, e i] j := by
    ext1 j
    simp [L]
  rw [hsmul, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  -- Step 4: `D²h₀(σ z) = D²h(x₀ + σ z)`.
  rw [iteratedFDeriv_comp_add_left]
  simp [L]
/-- Rescaling and reflection of the convolution integral for an even kernel (used for the mean
value kernel in Weyl's lemma, Simon Ch. 5, proof of Lemma 3.1): for `t > 0` and `ρ` even,
`∫ t⁻ⁿ ρ(t⁻¹ y) h(x₀ − y) dy = ∫ ρ(z) h(x₀ + t z) dz`.  No integrability is needed: the Haar
scaling formula, constant factors and the reflection `z ↦ −z` hold for the Bochner integral of an
arbitrary function. -/
theorem mvk_integral_rescale_reflect : ∀ (n : ℕ) (ρ h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 < t → (∀ z : Rn n, ρ (-z) = ρ z) → ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y) = ∫ z, ρ z * h (x₀ + t • z) := by
  intro n ρ h x₀ t ht hρ
  -- The integrand is `f (t⁻¹ • y)` for `f z = t⁻ⁿ ρ(z) h(x₀ − t z)`, since `t • t⁻¹ • y = y`.
  calc ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y)
      = ∫ y, (fun z : Rn n => t⁻¹ ^ n * (ρ z * h (x₀ - t • z))) (t⁻¹ • y) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [smul_inv_smul₀ ht.ne', mul_assoc]
    -- Scaling of Lebesgue measure: `∫ f (t⁻¹ • y) dy = tⁿ ∫ f`, since `finrank ℝ ℝⁿ = n`.
    _ = t ^ n • ∫ z, t⁻¹ ^ n * (ρ z * h (x₀ - t • z)) := by
        have hs := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Rn n))
          (fun z : Rn n => t⁻¹ ^ n * (ρ z * h (x₀ - t • z))) ht.le
        rw [finrank_euclideanSpace_fin] at hs
        exact hs
    -- Pull out the constant `t⁻ⁿ` and cancel `tⁿ t⁻ⁿ = 1`.
    _ = ∫ z, ρ z * h (x₀ - t • z) := by
        rw [integral_const_mul, smul_eq_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht.ne',
          one_pow, one_mul]
    -- `ρ` is even and `t • -z = -(t • z)`.
    _ = ∫ z, ρ (-z) * h (x₀ + t • -z) := by
        congr 1
        ext z
        rw [hρ, smul_neg, sub_eq_add_neg]
    -- Lebesgue measure is invariant under `z ↦ -z`.
    _ = ∫ z, ρ z * h (x₀ + t • z) := integral_neg_eq_self (fun z => ρ z * h (x₀ + t • z)) volume
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), mean value step of Weyl's lemma: integration by parts
of the radial derivative against the kernel potential.  If `h` is `C²`, `σ ≠ 0`, and the `C¹`
function `Ψ` vanishes for `‖z‖ ≥ 1` and has `DΨ(z)[v] = ρ(z) ⟨z, v⟩`, then
`∫ ρ(z) Dh(x₀ + σ z)[z] dz = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz`.  For `H(y) = h(x₀ + σ y)` the chain rule
gives `ρ(z) Dh(x₀ + σ z)[z] = σ⁻¹ DH(z)[ρ(z) z]`.  Green's first identity
(`mvk_integral_fderiv_grad_eq_neg_laplacian`, applied to the compactly supported `Ψ` with
gradient `ρ(z) z`) gives `∫ DH(z)[ρ(z) z] dz = -∫ ΔH(z) Ψ(z) dz`, and
`ΔH(z) = σ² Δh(x₀ + σ z)` (`mvk_laplacian_comp_add_smul`). -/
theorem mvk_integral_radial_fderiv_eq_neg_laplacian : ∀ (n : ℕ) (ρ Ψ h : Rn n → ℝ) (x₀ : Rn n) (σ : ℝ), σ ≠ 0 → ContDiff ℝ 2 h → ContDiff ℝ 1 Ψ → (∀ z : Rn n, 1 ≤ ‖z‖ → Ψ z = 0) → (∀ z v : Rn n, fderiv ℝ Ψ z v = ρ z * inner ℝ z v) → ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = -σ * ∫ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z := by
  intro n ρ Ψ h x₀ σ hσ hh hΨ hΨ1 hdΨ
  -- Step 1: `H(y) = h(x₀ + σ y)` is `C²`, with `DH(z)[v] = σ Dh(x₀ + σ z)[v]`.
  have hH : ContDiff ℝ 2 (fun y : Rn n => h (x₀ + σ • y)) :=
    hh.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have hdH : ∀ z v : Rn n,
      fderiv ℝ (fun y => h (x₀ + σ • y)) z v = σ * fderiv ℝ h (x₀ + σ • z) v := by
    intro z v
    have hA : HasFDerivAt (fun y : Rn n => x₀ + σ • y) (σ • ContinuousLinearMap.id ℝ (Rn n)) z :=
      ((hasFDerivAt_id z).const_smul σ).const_add x₀
    have hc : HasFDerivAt (fun y => h (x₀ + σ • y))
        ((fderiv ℝ h (x₀ + σ • z)).comp (σ • ContinuousLinearMap.id ℝ (Rn n))) z :=
      (hh.differentiable (by norm_num) (x₀ + σ • z)).hasFDerivAt.comp z hA
    rw [hc.fderiv]
    simp
  -- Step 2: `Ψ` vanishes off the closed unit ball, so it has compact support.
  have hΨc : HasCompactSupport Ψ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
      hΨ1 z (le_of_lt (by simpa using hz))
  -- Step 3: `w(z) = ρ(z) z` is the gradient of `Ψ`.
  have hw : ∀ z v : Rn n, fderiv ℝ Ψ z v = inner ℝ (ρ z • z) v := fun z v => by
    rw [hdΨ, real_inner_smul_left]
  -- Step 4: `ρ(z) Dh(x₀ + σ z)[z] = σ⁻¹ DH(z)[w(z)]`.
  have hpt : ∀ z, ρ z * fderiv ℝ h (x₀ + σ • z) z =
      σ⁻¹ * fderiv ℝ (fun y => h (x₀ + σ • y)) z (ρ z • z) := fun z => by
    rw [hdH, map_smul, smul_eq_mul, inv_mul_cancel_left₀ hσ]
  -- Steps 5–6: Green's first identity for `H`, `Ψ`, `w`, and `ΔH(z) = σ² Δh(x₀ + σ z)`.
  have hG := Submission.mvk_integral_fderiv_grad_eq_neg_laplacian n
    (fun y => h (x₀ + σ • y)) Ψ (fun z => ρ z • z) hH hΨ hΨc hw
  have hL := Submission.mvk_laplacian_comp_add_smul n h x₀ σ hh
  -- Step 7: pull out the constants.
  calc ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z
      = ∫ z, σ⁻¹ * fderiv ℝ (fun y => h (x₀ + σ • y)) z (ρ z • z) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = σ⁻¹ * -∫ z, Laplacian.laplacian (fun y => h (x₀ + σ • y)) z * Ψ z := by
        rw [integral_const_mul, hG]
    _ = σ⁻¹ * -∫ z, σ ^ 2 * (Laplacian.laplacian h (x₀ + σ • z) * Ψ z) := by
        simp only [hL, mul_assoc]
    _ = -σ * ∫ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z := by
        rw [integral_const_mul]
        field_simp
/-- Simon Ch. 5, proof of Lemma 3.1 (p. 114), mean value step of Weyl's lemma: there is a smooth
kernel `ρ` vanishing off the open unit ball with `∫ t⁻ⁿ ρ(t⁻¹ y) h(x₀ - y) dy = h(x₀)` for every
`t > 0` and every `C²` function `h` with `Δh = 0` on `B_t(x₀)`.  Take `ρ` (even, `∫ ρ = 1`) and
its potential `Ψ` (`DΨ(z)[v] = ρ(z) ⟨z, v⟩`, `Ψ = 0` off the unit ball); rescaling and reflecting
turn the left side into `∫ ρ(z) h(x₀ + t z) dz`, the fundamental theorem of calculus along rays
and Fubini give `h(x₀) + ∫₀ᵗ I(σ) dσ` with `I(σ) = ∫ ρ(z) Dh(x₀ + σ z)[z] dz`, and integration by
parts against `Ψ` gives `I(σ) = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz = 0` for `0 < σ ≤ t`. -/
theorem exists_smooth_mean_value_kernel : ∀ n : ℕ, 1 ≤ n → ∃ ρ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z : Rn n, 1 ≤ ‖z‖ → ρ z = 0) ∧ ∀ (h : Rn n → ℝ) (x₀ : Rn n) (t : ℝ), 0 < t → ContDiff ℝ 2 h → (∀ y ∈ closedBall x₀ t, Laplacian.laplacian h y = 0) → ∫ y, t⁻¹ ^ n * ρ (t⁻¹ • y) * h (x₀ - y) = h x₀ := by
  intro n _
  -- Step 1: the kernel `ρ` and its potential `Ψ`.
  obtain ⟨ρ, Ψ, hρ, hΨ, hρ1, hΨ1, hρneg, hρint, hdΨ⟩ := Submission.mvk_exists_kernel_potential n
  refine ⟨ρ, hρ, hρ1, fun h x₀ t ht hh hΔ => ?_⟩
  -- Step 2: `I(σ) = -σ ∫ Δh(x₀ + σ z) Ψ(z) dz = 0` for `0 < σ ≤ t`, since `Ψ(z) = 0` for
  -- `‖z‖ ≥ 1` and `x₀ + σ z ∈ B_t(x₀)` for `‖z‖ < 1`.
  have hI : ∀ σ ∈ Ioc (0 : ℝ) t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = 0 := by
    rintro σ ⟨hσ, hσt⟩
    rw [Submission.mvk_integral_radial_fderiv_eq_neg_laplacian n ρ Ψ h x₀ σ hσ.ne' hh
      (hΨ.of_le (by exact_mod_cast le_top)) hΨ1 hdΨ]
    have hzero : ∀ z, Laplacian.laplacian h (x₀ + σ • z) * Ψ z = 0 := by
      intro z
      rcases le_or_gt 1 ‖z‖ with hz | hz
      · rw [hΨ1 z hz, mul_zero]
      · have hmem : x₀ + σ • z ∈ closedBall x₀ t := by
          rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg hσ.le]
          nlinarith [norm_nonneg z]
        rw [hΔ _ hmem, zero_mul]
    simp only [hzero, integral_zero, mul_zero]
  -- Step 3: so `∫₀ᵗ I(σ) dσ = 0`, the endpoint `σ = 0` being outside `(0, t]`.
  have hint : ∫ σ in (0 : ℝ)..t, ∫ z, ρ z * fderiv ℝ h (x₀ + σ • z) z = 0 :=
    intervalIntegral.integral_zero_ae (Eventually.of_forall fun σ hσ =>
      hI σ (by rwa [uIoc_of_le ht.le] at hσ))
  -- Step 4: rescale and reflect, then integrate along rays:
  -- `∫ ρ(z) h(x₀ + t z) dz = (∫ ρ) h(x₀) + ∫₀ᵗ I(σ) dσ = h(x₀)`.
  rw [Submission.mvk_integral_rescale_reflect n ρ h x₀ t ht hρneg,
    Submission.mvk_integral_ray_fubini n ρ h x₀ t ht.le hρ.continuous hρ1
      (hh.of_le (by norm_num)), hρint, one_mul, hint, add_zero]

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

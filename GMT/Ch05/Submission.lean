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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

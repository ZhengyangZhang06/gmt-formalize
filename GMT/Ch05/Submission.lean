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

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

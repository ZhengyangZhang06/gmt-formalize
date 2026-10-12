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

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

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

/-- **Affine approximation of almost-harmonic Lipschitz maps** (Simon Ch. 5, proof of
Theorem 4.5, steps (17)–(19)).  Assume the Harmonic Approximation Lemma 3.1.  For `n ≥ 1` and `ℓ`
there is `C = C(n, ℓ) > 0` such that for every `ε ∈ (0, 1)` there is `δ_ε > 0` with the following
property: if `f : ℝⁿ → ℝ^ℓ` is Lipschitz on `B_r(0)`, `|f| ≤ h` on `B̆_r(0)`,
`∫_{B̆_r} |Df|² ≤ E rⁿ` and `|∫_{B̆_r} ∇fʲ · ∇ζ| ≤ δ_ε √E sup|∇ζ| rⁿ` for all `ζ ∈ C^∞_c(B̆_r)`,
then there are `a ∈ ℝ^ℓ` and a linear `A` with `|A| ≤ C √E`, `|a| ≤ C (h + r √(εE))` and
`∫_{B̆_{er}} |f - (a + A x)|² ≤ C (ε + e^{n+4}) E r^{n+2}` for `e ∈ (0, 1/4]`.

Proof: rescale each component to `F_j(z) = fʲ(rz)/(r√E)`, apply Lemma 3.1 to get harmonic `u_j`,
and use interior estimates for harmonic functions, proved here from the mean value property
`∫ u(x + y) φ(y) dy = (∫ φ) u(x)` for a smooth radial kernel `φ` (scaling argument plus Lipschitz
integration by parts), to define `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0) · x)_j`. -/
theorem ted_harmonic_affine_approx : HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δε : ℝ, 0 < δε ∧ ∀ (r E h : ℝ) (f : Rn n → Rn ℓ) (L : ℝ≥0), 0 < r → 0 < E → 0 ≤ h → LipschitzOnWith L f (closedBall 0 r) → (∀ x ∈ ball (0 : Rn n) r, ‖f x‖ ≤ h) → ∫ x in ball (0 : Rn n) r, hsNormSq (fderiv ℝ f x) ≤ E * r ^ n → (∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball 0 r → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) → ∀ j : Fin ℓ, |∫ x in ball (0 : Rn n) r, inner ℝ (gradient (fun y => f y j) x) (gradient ζ x)| ≤ δε * Real.sqrt E * M * r ^ n) → ∃ (a : Rn ℓ) (A : Rn n →L[ℝ] Rn ℓ), hsNorm A ≤ C * Real.sqrt E ∧ ‖a‖ ≤ C * (h + r * Real.sqrt (ε * E)) ∧ ∀ e : ℝ, 0 < e → e ≤ 1 / 4 → ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
  intro hHAL n ℓ hn
  -- elementary inequalities, proved once in the small initial context
  have hsq2 : ∀ X Y D : ℝ, Y ^ 2 ≤ D ^ 2 → (X + Y) ^ 2 ≤ 2 * (X ^ 2 + D ^ 2) := fun X Y D h =>
    add_sq_le.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h) zero_le_two)
  have hKP : ∀ K P ε : ℝ, 0 ≤ K → 0 ≤ P → 0 ≤ ε → ε + K * P ≤ (1 + K) * (ε + P) :=
    fun K P ε hK hP hε => by
      calc ε + K * P ≤ ε + K * P + (P + K * ε) :=
            le_add_of_nonneg_right (add_nonneg hP (mul_nonneg hK hε))
        _ = (1 + K) * (ε + P) := by ring
  have hab : ∀ a b x y : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ x → 0 ≤ y → a * y + b * x ≤ (a + b) * (x + y) :=
    fun a b x y ha hb hx hy => by
      calc a * y + b * x ≤ a * y + b * x + (a * x + b * y) :=
            le_add_of_nonneg_right (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy))
        _ = (a + b) * (x + y) := by ring
  -- the Hilbert–Schmidt norm is controlled by the operator norm
  have hHS : ∀ A : Rn n →L[ℝ] Rn ℓ, hsNormSq A ≤ n * ‖A‖ ^ 2 := fun A => by
    unfold hsNormSq
    calc ∑ i : Fin n, ‖A (EuclideanSpace.single i 1)‖ ^ 2 ≤ ∑ _i : Fin n, ‖A‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            ((A.le_opNorm _).trans (by rw [EuclideanSpace.norm_single, norm_one, mul_one])) 2)
      _ = n * ‖A‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  /- Steps 1–5 (interior estimates for harmonic functions, Simon 3.2–3.4), proved from the mean
  value property for a smooth radial kernel. -/
  obtain ⟨C₁, C₃, hC₁, hC₃, HE⟩ : ∃ C₁ C₃ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₃ ∧
      ∀ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) →
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖u x‖ₑ ≤ ENNReal.ofReal M → |u 0| ≤ C₁ * M) ∧
      (∀ M : ℝ, 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ≤ ENNReal.ofReal M →
        ‖gradient u 0‖ ≤ C₁ * M ∧
        ∀ z : Rn n, ‖z‖ ≤ 1/4 → |u z - u 0 - inner ℝ (gradient u 0) z| ≤ C₃ * M * ‖z‖ ^ 2) := by
    /- Step 1 (kernel).  `φ(y) = -64 τ'(1 - 32|y|²)` and its potential `Ψ(y) = τ(1 - 32|y|²)`
    (`τ` = `Real.smoothTransition`), so that `∂_v Ψ(y) = φ(y) ⟪y, v⟫`; both vanish off `B_{1/5}`. -/
    obtain ⟨φ, Ψ, Lφ, LΨ, Φ, hφc, hφ0, hφcs, hφL, hΦ, hc0, hΨL, hΨcs, hΨl, hΨ0⟩ :
        ∃ (φ Ψ : Rn n → ℝ) (Lφ LΨ : ℝ≥0) (Φ : ℝ), Continuous φ ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → φ y = 0) ∧ HasCompactSupport φ ∧ LipschitzWith Lφ φ ∧
          (∀ y, ‖φ y‖ ≤ Φ) ∧
          (∫ y, φ y) ≠ 0 ∧ LipschitzWith LΨ Ψ ∧ HasCompactSupport Ψ ∧
          (∀ y v : Rn n, HasLineDerivAt ℝ Ψ (φ y * inner ℝ y v) y v) ∧
          (∀ y : Rn n, 1/5 ≤ ‖y‖ → Ψ y = 0) := by
      have hτ : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
      have hτd : ∀ s, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition s) s :=
        fun s => ((hτ.differentiable (by simp)) s).hasDerivAt
      have hτ'0 : ∀ s : ℝ, s < 0 → deriv Real.smoothTransition s = 0 := fun s hs => by
        rw [(Filter.eventuallyEq_of_mem (Iio_mem_nhds hs)
          (fun z hz => Real.smoothTransition.zero_of_nonpos (le_of_lt hz))).deriv_eq]
        exact deriv_const s 0
      have hq : ∀ y : Rn n, 1/5 ≤ ‖y‖ → 1 - 32 * ‖y‖ ^ 2 < 0 := fun y hy => by nlinarith
      have hnsq : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => 1 - 32 * ‖y‖ ^ 2) :=
        contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
      have hφs : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Rn n => -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        contDiff_const.mul (((contDiff_infty_iff_deriv.1 hτ).2).comp hnsq)
      have hΨs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Rn n => Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
        hτ.comp hnsq
      have hφ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ →
          -64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => by rw [hτ'0 _ (hq y hy), mul_zero]
      have hΨ0 : ∀ y : Rn n, 1/5 ≤ ‖y‖ → Real.smoothTransition (1 - 32 * ‖y‖ ^ 2) = 0 :=
        fun y hy => Real.smoothTransition.zero_of_nonpos (hq y hy).le
      have hcs : ∀ g : Rn n → ℝ, (∀ y : Rn n, 1/5 ≤ ‖y‖ → g y = 0) → HasCompactSupport g :=
        fun g hg => HasCompactSupport.intro (isCompact_closedBall (0 : Rn n) (1/5)) (fun y hy =>
          hg y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le))
      have hφcs := hcs _ hφ0
      have hΨcs := hcs _ hΨ0
      obtain ⟨Lφ, hφL⟩ := hφs.lipschitzWith_of_hasCompactSupport hφcs (by simp)
      obtain ⟨LΨ, hΨL⟩ := hΨs.lipschitzWith_of_hasCompactSupport hΨcs (by simp)
      obtain ⟨Φ, hΦ⟩ := hφcs.exists_bound_of_continuous hφs.continuous
      refine ⟨_, _, Lφ, LΨ, Φ, hφs.continuous, hφ0, hφcs, hφL, hΦ, ?_, hΨL, hΨcs, fun y v => ?_, hΨ0⟩
      · -- `∫ φ < 0`, since `-φ ≥ 0` and `τ'(c) = 1` for some `c ∈ (0, 1)`
        obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.smoothTransition
          (deriv Real.smoothTransition) (zero_lt_one' ℝ) hτ.continuous.continuousOn
          (fun x _ => hτd x)
        simp only [Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero, div_one] at hcd
        have hy1 : ‖Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ ^ 2
            = (1 - c) / 32 := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith [hc.2])]
        have hpos : 0 < ∫ y : Rn n, -(-64 * deriv Real.smoothTransition (1 - 32 * ‖y‖ ^ 2)) :=
          Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
          (μ := (volume : Measure (Rn n)))
          (x := Real.sqrt ((1 - c) / 32) • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ))
          hφs.continuous.neg hφcs.neg
          (fun y => neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
            (Real.smoothTransition.monotone.deriv_nonneg)))
          (by
            show -(-64 * deriv Real.smoothTransition (1 - 32 * _)) ≠ 0
            rw [hy1, show (1:ℝ) - 32 * ((1 - c) / 32) = c by ring, hcd]
            norm_num)
        rw [integral_neg] at hpos
        exact (neg_pos.1 hpos).ne
      · -- the line derivative of `Ψ`
        refine HasDerivAt.congr_deriv (((hτd _).comp_hasFDerivAt y
          (((hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_mul (32:ℝ)).const_sub 1)).hasLineDerivAt
            v) ?_
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
          innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        ring
    have hc0' : 0 < |∫ y, φ y| := abs_pos.2 hc0
    have hΦ0 : 0 ≤ Φ := (norm_nonneg _).trans (hΦ 0)
    refine ⟨|∫ y, φ y|⁻¹ * Φ, |∫ y, φ y|⁻¹ * Lφ, mul_nonneg (inv_nonneg.2 hc0'.le) hΦ0,
      mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2, fun u hu => ?_⟩
    /- Step 2: smoothness of `u`, `Δu = 0`, and a bound for `Du` on `B_{9/10}`. -/
    have hC2 : ContDiffOn ℝ 2 u (ball 0 1) := hu.contDiffOn
    have hdiff : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt u (fderiv ℝ u z) z := fun z hz =>
      ((hC2.differentiableOn (by norm_num)) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
        |>.hasFDerivAt
    have hD1 : ContDiffOn ℝ 1 (fderiv ℝ u) (ball 0 1) :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) isOpen_ball).1 hC2).2.2
    have hD1c : ContinuousOn (fderiv ℝ u) (ball 0 1) := hD1.continuousOn
    have hD2 : ∀ z ∈ ball (0 : Rn n) 1, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
      fun z hz => ((hD1.differentiableOn one_ne_zero) z hz).differentiableAt
        (isOpen_ball.mem_nhds hz) |>.hasFDerivAt
    set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
    have hlap : ∀ z ∈ ball (0 : Rn n) 1, ∑ i, fderiv ℝ (fderiv ℝ u) z (b i) (b i) = 0 := by
      intro z hz
      have h0 : Laplacian.laplacian u z = 0 := (hu z hz).2.eq_of_nhds
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b] at h0
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] using h0
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ z ∈ closedBall (0 : Rn n) (9/10), ‖fderiv ℝ u z‖ ≤ M1 :=
      (isCompact_closedBall 0 (9/10)).exists_bound_of_continuousOn
        (hD1c.mono (closedBall_subset_ball (by norm_num)))
    have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (mem_closedBall_self (by norm_num)))
    have huc : ContinuousOn u (ball 0 1) := hC2.continuousOn
    set B := closedBall (0 : Rn n) (1/5) with hB
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    have hφB : ∀ y ∉ B, φ y = 0 := fun y hy =>
      hφ0 y (by rw [hB, mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
    have h910 : closedBall (0 : Rn n) (9/10) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
    have hgeo : ∀ x : Rn n, ‖x‖ < 1/2 → ∀ s : ℝ, |s| ≤ 2 → ∀ y ∈ B,
        x + s • y ∈ closedBall (0 : Rn n) (9/10) := by
      intro x hx s hs y hy
      rw [hB, mem_closedBall, dist_zero_right] at hy
      rw [mem_closedBall, dist_zero_right]
      calc ‖x + s • y‖ ≤ ‖x‖ + |s| * ‖y‖ := by
            rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
        _ ≤ 1/2 + 2 * (1/5) := add_le_add hx.le (mul_le_mul hs hy (norm_nonneg _) zero_le_two)
        _ = 9/10 := by norm_num
    have hpath1 : ∀ x : Rn n, ‖x‖ < 1/2 → MapsTo (fun y : Rn n => x + y) B (ball 0 1) :=
      fun x hx y hy => h910 (by have h := hgeo x hx 1 (by norm_num) y hy; rwa [one_smul] at h)
    have hsr : ∀ (L : Rn n →L[ℝ] ℝ) (w : Rn n), L w = ∑ i, inner ℝ (b i) w * L (b i) := by
      intro L w
      conv_lhs => rw [← b.sum_repr' w]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hpc1 : ∀ x' : Rn n, Continuous (fun y : Rn n => x' + y) := fun x' =>
      continuous_const.add continuous_id
    /- Step 3 (mean value property): `∫ φ(y) u(x + y) dy = (∫ φ) u(x)` for `‖x‖ < 1/2`.  The
    derivative of `t ↦ ∫_B φ(y) u(x + t y) dy` is `∫_B φ(y) Du(x + t y)[y] dy`, which vanishes by
    Lipschitz integration by parts against `Ψ` (`∂_v Ψ = φ ⟪·, v⟫`) and `Δu = 0`. -/
    have hMVP : ∀ x : Rn n, ‖x‖ < 1/2 → ∫ y, φ y * u (x + y) = (∫ y, φ y) * u x := by
      intro x hx
      have hpath : ∀ s : ℝ, |s| ≤ 2 → MapsTo (fun y : Rn n => x + s • y) B (ball 0 1) :=
        fun s hs y hy => h910 (hgeo x hx s hs y hy)
      have hpc : ∀ s : ℝ, ContDiff ℝ 1 (fun y : Rn n => x + s • y) := fun s =>
        contDiff_const.add (contDiff_id.const_smul s)
      have hcF : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * u (x + s • y)) B := fun s hs =>
        hφc.continuousOn.mul (huc.comp (hpc s).continuous.continuousOn (hpath s hs))
      have hcF' : ∀ s : ℝ, |s| ≤ 2 → ContinuousOn (fun y => φ y * fderiv ℝ u (x + s • y) y) B :=
        fun s hs => hφc.continuousOn.mul ((hD1c.comp (hpc s).continuous.continuousOn
          (hpath s hs)).clm_apply continuousOn_id)
      -- the radial derivative vanishes
      have hzero : ∀ t : ℝ, |t| ≤ 2 → ∫ y in B, φ y * fderiv ℝ u (x + t • y) y = 0 := by
        intro t ht
        have hin : ∀ y : Rn n, ‖y‖ ≤ 1/4 → x + t • y ∈ ball (0 : Rn n) 1 := fun y hy => by
          rw [mem_ball, dist_zero_right]
          calc ‖x + t • y‖ ≤ ‖x‖ + |t| * ‖y‖ := by
                rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
            _ ≤ ‖x‖ + 2 * (1/4) := add_le_add le_rfl (mul_le_mul ht hy (norm_nonneg _) zero_le_two)
            _ < 1 := by linarith
        have hext : ∀ i : Fin n, ∃ (K : ℝ≥0) (W : Rn n → ℝ), LipschitzWith K W ∧
            EqOn (fun y => fderiv ℝ u (x + t • y) (b i)) W (closedBall 0 (1/4)) := by
          intro i
          have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u (x + t • y) (b i)) (closedBall 0 (1/4)) :=
            (hD1.comp (hpc t).contDiffOn (fun y hy => hin y (mem_closedBall_zero_iff.1 hy))).clm_apply
              contDiffOn_const
          obtain ⟨K, hK⟩ := h2.exists_lipschitzOnWith (by norm_num) (convex_closedBall _ _)
            (isCompact_closedBall _ _)
          obtain ⟨W, hW, hEq⟩ := hK.extend_real
          exact ⟨_, W, hW, hEq⟩
        choose K W hWL hWeq using hext
        have hibp : ∀ i, ∫ y, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, lineDeriv ℝ Ψ y (-(b i)) * W i y :=
          fun i => (hWL i).integral_lineDeriv_mul_eq hΨL hΨcs (b i)
        have hL : ∀ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y = 0 := by
          intro y
          by_cases hy : ‖y‖ < 1/4
          · have hz := hin y hy.le
            have hnhd : closedBall (0 : Rn n) (1/4) ∈ 𝓝 y :=
              closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 hy)
            have hline : ∀ i, lineDeriv ℝ (W i) y (b i) =
                t * fderiv ℝ (fderiv ℝ u) (x + t • y) (b i) (b i) := by
              intro i
              have hc := ((hD2 _ hz).comp y (((hasFDerivAt_id y).const_smul t).const_add x)).clm_apply
                (hasFDerivAt_const (b i) y)
              rw [((hc.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem hnhd
                (fun z hz => (hWeq i hz).symm))).hasLineDerivAt (b i)).lineDeriv]
              simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply,
                ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
            simp only [hline]
            rw [← Finset.sum_mul, ← Finset.mul_sum, hlap _ hz, mul_zero, zero_mul]
          · simp only [hΨ0 y (le_trans (by norm_num) (not_lt.1 hy)), mul_zero, Finset.sum_const_zero]
        have hR : ∀ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y = -(φ y * fderiv ℝ u (x + t • y) y) := by
          intro y
          have hl : ∀ i, lineDeriv ℝ Ψ y (-(b i)) = -(φ y * inner ℝ y (b i)) := fun i => by
            rw [(hΨl y _).lineDeriv, inner_neg_right, mul_neg]
          simp only [hl]
          by_cases hy : ‖y‖ ≤ 1/4
          · have hWy : ∀ i, W i y = fderiv ℝ u (x + t • y) (b i) := fun i =>
              (hWeq i (mem_closedBall_zero_iff.2 hy)).symm
            simp only [hWy]
            rw [hsr (fderiv ℝ u (x + t • y)) y, Finset.mul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [real_inner_comm]
            ring
          · simp only [hφ0 y (le_trans (by norm_num) (not_le.1 hy).le), zero_mul, neg_zero,
              Finset.sum_const_zero]
        have hΨi : Integrable Ψ := hΨL.continuous.integrable_of_hasCompactSupport hΨcs
        have hLi : ∀ i, Integrable (fun y => lineDeriv ℝ (W i) y (b i) * Ψ y) :=
          fun i => hΨi.mul_of_top_right ((hWL i).memLp_lineDeriv (b i))
        have hRi : ∀ i, Integrable (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) := by
          intro i
          have hfun : (fun y => lineDeriv ℝ Ψ y (-(b i)) * W i y) =
              fun y => φ y * (inner ℝ y (-(b i)) * W i y) := by
            funext y; rw [(hΨl y _).lineDeriv, mul_assoc]
          rw [hfun]
          exact (hφc.mul ((continuous_id.inner continuous_const).mul (hWL i).continuous)
            ).integrable_of_hasCompactSupport hφcs.mul_right
        have h1 : ∫ y, ∑ i, lineDeriv ℝ (W i) y (b i) * Ψ y =
            ∫ y, ∑ i, lineDeriv ℝ Ψ y (-(b i)) * W i y := by
          rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
          exact Finset.sum_congr rfl (fun i _ => hibp i)
        simp only [hL, hR, integral_zero, integral_neg] at h1
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact neg_eq_zero.1 h1.symm
      -- differentiation under the integral sign
      have hIoo : ∀ s ∈ Ioo (-2:ℝ) 2, |s| ≤ 2 := fun s hs => abs_le.2 ⟨hs.1.le, hs.2.le⟩
      have hderiv : ∀ t ∈ Ioo (-2:ℝ) 2, HasDerivAt (fun t => ∫ y in B, φ y * u (x + t • y))
          (∫ y in B, φ y * fderiv ℝ u (x + t • y) y) t := by
        intro t ht
        refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
          (F := fun t y => φ y * u (x + t • y)) (F' := fun t y => φ y * fderiv ℝ u (x + t • y) y)
          (bound := fun _ => Φ * (M1 * (1/5))) ?_
          ((hcF t (hIoo t ht)).integrableOn_compact (isCompact_closedBall _ _))
          ((hcF' t (hIoo t ht)).aestronglyMeasurable measurableSet_closedBall) ?_
          (integrable_const _) ?_).2
        · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact (hcF s (hIoo s hs)).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          rw [norm_mul]
          exact mul_le_mul (hΦ y) ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hM1 _ (hgeo x hx s (hIoo s hs) y hy)) (mem_closedBall_zero_iff.1 hy)
              (norm_nonneg _) hM1')) (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy s hs
          exact ((hdiff _ (hpath s (hIoo s hs) hy)).comp_hasDerivAt s
            ((((hasDerivAt_id s).smul_const y).const_add x).congr_deriv (one_smul ℝ y))).const_mul
              (φ y)
      -- mean value theorem in `t`
      obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t => ∫ y in B, φ y * u (x + t • y))
        (fun t => ∫ y in B, φ y * fderiv ℝ u (x + t • y) y) (zero_lt_one' ℝ)
        (fun t ht => (hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
        (fun t ht => hderiv t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hcd
      rw [hzero c (abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩), integral_mul_const,
        setIntegral_eq_integral_of_forall_compl_eq_zero hφB,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])] at hcd
      exact sub_eq_zero.1 hcd.symm
    /- Step 4: differentiating the mean value identity, `(∫ φ) Du(x) = ∫ φ(y) Du(x + y) dy`. -/
    have hdMVP : ∀ x : Rn n, ‖x‖ < 1/2 →
        (∫ y, φ y) • fderiv ℝ u x = ∫ y, φ y • fderiv ℝ u (x + y) := by
      intro x hx
      have hδ : 0 < 1/2 - ‖x‖ := by linarith
      have hsm : ∀ x' ∈ ball x (1/2 - ‖x‖), ‖x'‖ < 1/2 := fun x' hx' => by
        rw [mem_ball, dist_eq_norm] at hx'
        linarith [norm_sub_norm_le x' x]
      have hcF : ∀ x' : Rn n, ‖x'‖ < 1/2 → ContinuousOn (fun y => φ y * u (x' + y)) B :=
        fun x' hx' => hφc.continuousOn.mul (huc.comp (hpc1 x').continuousOn (hpath1 x' hx'))
      have hP : HasFDerivAt (fun x' => ∫ y in B, φ y * u (x' + y))
          (∫ y in B, φ y • fderiv ℝ u (x + y)) x := by
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => Φ * M1)
          (F := fun x' y => φ y * u (x' + y)) (F' := fun x' y => φ y • fderiv ℝ u (x' + y))
          (ball_mem_nhds x hδ) ?_ ((hcF x hx).integrableOn_compact (isCompact_closedBall _ _)) ?_ ?_
          (integrable_const _) ?_
        · filter_upwards [ball_mem_nhds x hδ] with x' hx'
          exact (hcF x' (hsm x' hx')).aestronglyMeasurable measurableSet_closedBall
        · exact (hφc.continuousOn.smul (hD1c.comp (hpc1 x).continuousOn
            (hpath1 x hx))).aestronglyMeasurable measurableSet_closedBall
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          rw [norm_smul]
          exact mul_le_mul (hΦ y) (hM1 _ (by
            have h := hgeo x' (hsm x' hx') 1 (by norm_num) y hy; rwa [one_smul] at h))
            (norm_nonneg _) hΦ0
        · filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy x' hx'
          have h := ((hdiff _ (hpath1 x' (hsm x' hx') hy)).comp x'
            ((hasFDerivAt_id x').add_const y)).const_mul (φ y)
          rwa [ContinuousLinearMap.comp_id] at h
      have heq : (fun x' => ∫ y in B, φ y * u (x' + y)) =ᶠ[𝓝 x] fun x' => (∫ y, φ y) * u x' := by
        filter_upwards [ball_mem_nhds x hδ] with x' hx'
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hφB y hy, zero_mul])]
        exact hMVP x' (hsm x' hx')
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (f := fun y => φ y • fderiv ℝ u (x + y)) (fun y hy => by rw [hφB y hy, zero_smul])]
      exact ((hdiff x (mem_ball_zero_iff.2 (by linarith))).const_mul (∫ y, φ y)).unique
        (hP.congr_of_eventuallyEq heq.symm)
    /- Step 5: the estimates. -/
    have hgen : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (ψ : Rn n → ℝ) (K : ℝ),
        0 ≤ K → (∀ y, ‖ψ y‖ ≤ K) → (∀ y ∉ ball (0 : Rn n) 1, ψ y = 0) →
        ∀ (G : Rn n → X) (M : ℝ), 0 ≤ M → ∫⁻ x in ball (0 : Rn n) 1, ‖G x‖ₑ ≤ ENNReal.ofReal M →
        ‖∫ y, ψ y • G y‖ ≤ K * M := by
      intro X _ _ ψ K hK hψ hψ0 G M hM hGM
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : Rn n) 1)
        (fun y hy => by rw [hψ0 y hy, zero_smul])]
      refine (norm_integral_le_lintegral_norm _).trans
        (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK hM) ?_)
      calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ‖ψ y • G y‖
          ≤ ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal K * ‖G y‖ₑ := by
            refine lintegral_mono (fun y => ?_)
            rw [norm_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm (G y)]
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hψ y)) _
        _ = ENNReal.ofReal K * ∫⁻ y in ball (0 : Rn n) 1, ‖G y‖ₑ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal M := mul_le_mul_right hGM _
        _ = ENNReal.ofReal (K * M) := (ENNReal.ofReal_mul hK).symm
    have hφ1 : ∀ y ∉ ball (0 : Rn n) 1, φ y = 0 := fun y hy =>
      hφ0 y (le_trans (by norm_num) (not_lt.1 (mt mem_ball_zero_iff.2 hy)))
    have h00 : ‖(0 : Rn n)‖ < 1/2 := by rw [norm_zero]; norm_num
    refine ⟨fun M hM huM => ?_, fun M hM huM => ?_⟩
    · -- the value at the origin
      have h1 := hMVP 0 h00
      have h2 := hgen φ Φ hΦ0 hΦ hφ1 u M hM huM
      simp only [zero_add, smul_eq_mul] at h1 h2
      rw [h1, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h2
      rw [mul_assoc, le_inv_mul_iff₀ hc0']
      exact h2
    · have hgn : ∀ x, ‖gradient u x‖ₑ = ‖fderiv ℝ u x‖ₑ := fun x => by
        rw [← ofReal_norm, ← ofReal_norm]
        exact congrArg ENNReal.ofReal ((InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _)
      simp only [hgn] at huM
      have hDu0 : ‖fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Φ * M := by
        have h1 := hdMVP 0 h00
        have h2 := hgen φ Φ hΦ0 hΦ hφ1 (fderiv ℝ u) M hM huM
        simp only [zero_add] at h1
        rw [← h1, norm_smul, Real.norm_eq_abs] at h2
        rw [mul_assoc, le_inv_mul_iff₀ hc0']
        exact h2
      have hint : ∀ z : Rn n, ‖z‖ < 1/2 → Integrable (fun w => φ (w - z) • fderiv ℝ u w) := by
        intro z hz
        have hc : ContinuousOn (fun y => φ y • fderiv ℝ u (z + y)) B :=
          hφc.continuousOn.smul (hD1c.comp (hpc1 z).continuousOn (hpath1 z hz))
        have h := (hc.integrableOn_compact (μ := volume) (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero
            (fun y hy => by rw [hφB y hy, zero_smul])
        simpa only [add_sub_cancel] using h.comp_sub_right z
      have hshift : ∀ z : Rn n, ∫ y, φ y • fderiv ℝ u (z + y) = ∫ w, φ (w - z) • fderiv ℝ u w := by
        intro z
        have h := integral_add_left_eq_self (μ := (volume : Measure (Rn n)))
          (fun w => φ (w - z) • fderiv ℝ u w) z
        simp only [add_sub_cancel_left] at h
        exact h
      have hLipD : ∀ z : Rn n, ‖z‖ ≤ 1/4 →
          ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ := by
        intro z hz
        have hz2 : ‖z‖ < 1/2 := by linarith
        have h1 := hdMVP z hz2
        have h0 := hdMVP 0 h00
        rw [hshift] at h1 h0
        have hdiffeq : (∫ y, φ y) • (fderiv ℝ u z - fderiv ℝ u 0) =
            ∫ w, (φ (w - z) - φ (w - 0)) • fderiv ℝ u w := by
          rw [smul_sub, h1, h0, ← integral_sub (hint z hz2) (hint 0 h00)]
          simp only [sub_smul]
        have hb := hgen (fun w => φ (w - z) - φ (w - 0)) (Lφ * ‖z‖)
          (mul_nonneg Lφ.2 (norm_nonneg _))
          (fun w => by
            have h := hφL.dist_le_mul (w - z) (w - 0)
            rwa [dist_eq_norm, dist_sub_left, dist_zero_right] at h)
          (fun w hw => by
            have hw1 : 1 ≤ ‖w‖ := not_lt.1 (mt mem_ball_zero_iff.2 hw)
            rw [hφ0 (w - z) (by linarith [norm_sub_norm_le w z]), sub_zero,
              hφ0 w (by linarith), sub_self])
          (fderiv ℝ u) M hM huM
        rw [← hdiffeq, norm_smul, Real.norm_eq_abs] at hb
        rw [show |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖ = |∫ y, φ y|⁻¹ * (Lφ * ‖z‖ * M) by ring,
          le_inv_mul_iff₀ hc0']
        exact hb
      refine ⟨(InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _ ▸ hDu0, fun z hz => ?_⟩
      rw [show inner ℝ (gradient u 0) z = fderiv ℝ u 0 z from
        InnerProductSpace.toDual_symm_apply]
      have hK0 : 0 ≤ |∫ y, φ y|⁻¹ * Lφ * M := mul_nonneg (mul_nonneg (inv_nonneg.2 hc0'.le) Lφ.2) hM
      have hs : closedBall (0 : Rn n) ‖z‖ ⊆ ball 0 1 := closedBall_subset_ball (by linarith)
      have hmvt := (convex_closedBall (0 : Rn n) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := fun y => u y - fderiv ℝ u 0 y) (f' := fun y => fderiv ℝ u y - fderiv ℝ u 0)
        (C := |∫ y, φ y|⁻¹ * Lφ * M * ‖z‖)
        (fun y hy => ((hdiff y (hs hy)).sub (fderiv ℝ u 0).hasFDerivAt).hasFDerivWithinAt)
        (fun y hy => (hLipD y ((mem_closedBall_zero_iff.1 hy).trans hz)).trans
          (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) hK0))
        (mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.2 le_rfl)
      simp only [map_zero, sub_zero, Real.norm_eq_abs] at hmvt
      rw [sub_right_comm, sq, ← mul_assoc]
      exact hmvt
  /- Step 6 (Cauchy–Schwarz on `B₁`): `∫_{B₁} g ≤ (ω_n S)^{1/2}` when `∫_{B₁} g² ≤ S`. -/
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (ball (0 : Rn n) 1)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := hVdef ▸ ENNReal.toReal_nonneg
  have CS : ∀ g : Rn n → ℝ≥0∞, AEMeasurable g (volume.restrict (ball (0 : Rn n) 1)) →
      ∀ S : ℝ, 0 ≤ S → ∫⁻ x in ball (0 : Rn n) 1, g x ^ 2 ≤ ENNReal.ofReal S →
      ∫⁻ x in ball (0 : Rn n) 1, g x ≤ ENNReal.ofReal (Real.sqrt V * Real.sqrt S) := by
    intro g hg S hS hgS
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball (0 : Rn n) 1))
      Real.HolderConjugate.two_two hg aemeasurable_const (f := g) (g := fun _ => (1 : ℝ≥0∞))
    simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ,
      ENNReal.rpow_two, one_pow, one_mul] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_comm (ENNReal.ofReal _)]
    gcongr
    · calc (∫⁻ x in ball (0 : Rn n) 1, g x ^ 2) ^ (1 / (2 : ℝ))
          ≤ (ENNReal.ofReal S) ^ (1 / (2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal (Real.sqrt S) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hS (by norm_num), Real.sqrt_eq_rpow]
    · rw [hVdef, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by norm_num), ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  /- Step 7: the constant `C` (depending on `n, ℓ` only) and `δ_ε` (from Lemma 3.1). -/
  obtain ⟨C, hCpos, hC1, hC2, hC3⟩ : ∃ C : ℝ, 0 < C ∧
      Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) ≤ C ∧ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) ≤ C ∧
      2 * ℓ * (1 + C₃ ^ 2 * V ^ 2) ≤ C := by
    have h1 : 0 ≤ Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) := mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ (Real.sqrt_nonneg _)))
    have h2 : 0 ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₁) (add_nonneg (Real.sqrt_nonneg _) hV0)
    have h3 : 0 ≤ 2 * (ℓ : ℝ) * (1 + C₃ ^ 2 * V ^ 2) :=
      mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _))
        (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact ⟨1 + Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) + Real.sqrt ℓ * C₁ * (Real.sqrt V + V) +
        2 * ℓ * (1 + C₃ ^ 2 * V ^ 2),
      add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg one_pos h1) h2) h3,
      ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right h2)).trans
        (le_add_of_nonneg_right h3),
      (le_add_of_nonneg_left (add_nonneg zero_le_one h1)).trans (le_add_of_nonneg_right h3),
      le_add_of_nonneg_left (add_nonneg (add_nonneg zero_le_one h1) h2)⟩
  refine ⟨C, hCpos, ?_⟩
  intro ε hε _hε1
  obtain ⟨δ, hδ, hHA⟩ := hHAL n hn ε hε
  refine ⟨δ, hδ, ?_⟩
  intro r E h f L hr hE hh hLip hbound henergy halmost
  /- Step 8: for each component `j`, `F_j(z) = f(rz)_j / (r√E)` (extended from `B₁` as a
  Lipschitz function) satisfies the hypotheses of Lemma 3.1 (`W^{1,2}` with weak gradient,
  energy `≤ 1`, `δ`-almost harmonic), giving a harmonic `u_j` with `∫_{B₁}|∇u_j|² ≤ 1` and
  `∫_{B₁}|u_j - F_j|² ≤ ε`. -/
  have hcomp : ∀ j : Fin ℓ, ∃ u : Rn n → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖gradient u x‖ₑ ^ 2 ≤ 1 ∧
      ∫⁻ x in ball (0 : Rn n) 1, ‖u x - (r * Real.sqrt E)⁻¹ * f (r • x) j‖ₑ ^ 2 ≤
        ENNReal.ofReal ε := by
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
    have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
    have hcr : c * r = (Real.sqrt E)⁻¹ := by
      rw [hc, mul_inv, mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]
    have hsB : ∀ z ∈ closedBall (0 : Rn n) 1, r • z ∈ closedBall (0 : Rn n) r := fun z hz => by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.1 hz)
    have hsB' : ∀ z ∈ ball (0 : Rn n) 1, r • z ∈ ball (0 : Rn n) r := fun z hz => by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)
    have hgmeas : ∀ g : Rn n → ℝ, Measurable (gradient g) := fun g =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have hng : ∀ (g : Rn n → ℝ) (z : Rn n), ‖gradient g z‖ = ‖fderiv ℝ g z‖ := fun g z =>
      (InnerProductSpace.toDual ℝ (Rn n)).symm.norm_map _
    have hig : ∀ (g : Rn n → ℝ) (z w : Rn n), inner ℝ (gradient g z) w = fderiv ℝ g z w :=
      fun g z w => InnerProductSpace.toDual_symm_apply
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) r)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    -- `|Df|²_{HS}` is integrable on `B_r` (it is bounded by `n L²`)
    have hHSint : IntegrableOn (fun x => hsNormSq (fderiv ℝ f x)) (ball (0 : Rn n) r) := by
      have hcont : Continuous (fun A : Rn n →L[ℝ] Rn ℓ => hsNormSq A) :=
        continuous_finsetSum _ (fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2)
      refine Integrable.of_bound (hcont.measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable
        (n * L ^ 2) ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall
          (fun x hx => ?_)))
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      exact (hHS _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_fderiv_le_of_lipschitzOn ℝ (closedBall_mem_nhds_of_mem hx) hLip) 2) (Nat.cast_nonneg _))
    -- `f` is differentiable a.e. on `B_r` (Rademacher)
    have hfdiff : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)), DifferentiableAt ℝ f x := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := volume)] with x hx hxB
      exact (hx (ball_subset_closedBall hxB)).differentiableAt (closedBall_mem_nhds_of_mem hxB)
    intro j
    obtain ⟨fj, hfj⟩ : ∃ g : Rn n → ℝ, g = fun y => f y j := ⟨_, rfl⟩
    have hcoord : ∀ v : Rn ℓ, |v j| ≤ ‖v‖ := fun v => by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    -- `F z = c fʲ(r z)` is Lipschitz on the closed unit ball; `Ft` is a Lipschitz extension
    have hK0 : 0 ≤ c * L * r := mul_nonneg (mul_nonneg hcpos.le L.2) hr.le
    have hFL : LipschitzOnWith ⟨c * L * r, hK0⟩ (fun z : Rn n => c * fj (r • z)) (closedBall 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul (fun x hx y hy => ?_)
      have h1 := hLip.dist_le_mul _ (hsB x hx) _ (hsB y hy)
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm] at h1
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hcpos, hfj]
      show c * |f (r • x) j - f (r • y) j| ≤ c * L * r * dist x y
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hcoord (f (r • x) - f (r • y))).trans h1) hcpos.le
    obtain ⟨Ft, hFtL, hFtEq⟩ := hFL.extend_real
    have hFtE : ∀ z ∈ closedBall (0 : Rn n) 1, Ft z = c * fj (r • z) := fun z hz => (hFtEq hz).symm
    have hFtc : Continuous Ft := hFtL.continuous
    -- gradient of `Ft` on the open ball
    have hgFt : ∀ z ∈ ball (0 : Rn n) 1, gradient Ft z = (Real.sqrt E)⁻¹ • gradient fj (r • z) := by
      intro z hz
      have heq : Ft =ᶠ[𝓝 z] fun z => c * fj (r • z) :=
        Filter.eventuallyEq_of_mem (closedBall_mem_nhds_of_mem hz) hFtE
      have h1 : fderiv ℝ (fun z : Rn n => c * fj (r • z)) z = (c * r) • fderiv ℝ fj (r • z) := by
        rw [show (fun z : Rn n => c * fj (r • z)) = c • fun z => fj (r • z) from rfl,
          fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul]
      rw [gradient, gradient, heq.fderiv_eq, h1, hcr, map_smul]
    have hFtb : ∀ z ∈ ball (0 : Rn n) 1, ‖Ft z‖ ≤ c * h := fun z hz => by
      rw [hFtE z (ball_subset_closedBall hz), hfj, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hcpos]
      exact mul_le_mul_of_nonneg_left ((hcoord _).trans (hbound _ (hsB' z hz))) hcpos.le
    have hgFtb : ∀ z, ‖gradient Ft z‖ ≤ c * L * r := fun z =>
      (hng Ft z).trans_le (norm_fderiv_le_of_lipschitz ℝ hFtL)
    -- `Ft ∈ W^{1,2}(B)` with weak gradient `∇Ft` (Lipschitz integration by parts)
    have hW12 : IsW12WithGradient Ft (gradient Ft) (ball 0 1) := by
      refine ⟨MemLp.of_bound hFtc.aestronglyMeasurable (c * h)
          ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hFtb)),
        MemLp.of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
          (Filter.Eventually.of_forall hgFtb), fun ζ hζ hζcs hζsupp => ?_⟩
      obtain ⟨Lζ, hζL⟩ := hζ.lipschitzWith_of_hasCompactSupport hζcs (by simp)
      have hζd : Differentiable ℝ ζ := hζ.differentiable (by simp)
      have hζout : ∀ x ∉ ball (0 : Rn n) 1, ζ x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hζsupp h))
      have hdζout : ∀ x ∉ ball (0 : Rn n) 1, fderiv ℝ ζ x = 0 := fun x hx =>
        fderiv_of_notMem_tsupport ℝ (fun h => hx (hζsupp h))
      have hgζ : Continuous (gradient ζ) :=
        (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp (hζ.continuous_fderiv (by simp))
      have hgζcs : HasCompactSupport (gradient ζ) :=
        (hζcs.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ (Rn n)).symm) (map_zero _)
      have hI1 : Integrable (fun x => Ft x • gradient ζ x) :=
        (hFtc.smul hgζ).integrable_of_hasCompactSupport hgζcs.smul_left
      have hI2 : Integrable (fun x => ζ x • gradient Ft x) :=
        (hζ.continuous.integrable_of_hasCompactSupport hζcs).smul_of_top_left
          (memLp_top_of_bound (hgmeas Ft).aestronglyMeasurable (c * L * r)
            (Filter.Eventually.of_forall hgFtb))
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [gradient, hdζout x hx, map_zero, smul_zero]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hζout x hx, zero_smul])]
      refine ext_inner_left ℝ (fun w => ?_)
      rw [inner_neg_right, ← innerSL_apply_apply (𝕜 := ℝ), ← innerSL_apply_apply (𝕜 := ℝ),
        ← (innerSL ℝ w).integral_comp_comm hI1, ← (innerSL ℝ w).integral_comp_comm hI2]
      simp only [innerSL_apply_apply, inner_smul_right]
      have hibp := hFtL.integral_lineDeriv_mul_eq (μ := volume) hζL hζcs w
      have hA : ∀ x, lineDeriv ℝ ζ x (-w) * Ft x = -(Ft x * inner ℝ w (gradient ζ x)) := fun x => by
        rw [(hζd x).lineDeriv_eq_fderiv, map_neg, real_inner_comm, hig, neg_mul, mul_comm]
      have hB : (fun x => lineDeriv ℝ Ft x w * ζ x) =ᵐ[volume]
          fun x => ζ x * inner ℝ w (gradient Ft x) := by
        filter_upwards [hFtL.ae_differentiableAt] with x hx
        rw [hx.lineDeriv_eq_fderiv, real_inner_comm, hig, mul_comm]
      rw [integral_congr_ae hB] at hibp
      simp only [hA, integral_neg] at hibp
      rw [hibp, neg_neg]
    -- energy: `∫_{B} |∇Ft|² = E⁻¹ r⁻ⁿ ∫_{B_r} |∇fʲ|² ≤ E⁻¹ r⁻ⁿ ∫_{B_r} |Df|² ≤ 1`
    have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) r)),
        ‖gradient fj x‖ ^ 2 ≤ hsNormSq (fderiv ℝ f x) := by
      filter_upwards [hfdiff] with x hdx
      have hh : HasFDerivAt (fun y => f y j) ((EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).comp
          (fderiv ℝ f x)) x := (EuclideanSpace.proj j : Rn ℓ →L[ℝ] ℝ).hasFDerivAt.comp x hdx.hasFDerivAt
      have hfd : ∀ v, fderiv ℝ fj x v = (fderiv ℝ f x v) j := fun v => by
        rw [hfj, hh.fderiv]
        rfl
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have h1 : (gradient fj x) i = fderiv ℝ fj x (EuclideanSpace.single i 1) := by
        rw [← hig, EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real]
      rw [Real.norm_eq_abs, sq_abs, h1, hfd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord _) 2
    have henergyF : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 ≤ 1 := by
      have hint1 : Integrable (fun x => ‖gradient Ft x‖ ^ 2) (volume.restrict (ball (0 : Rn n) 1)) :=
        Integrable.of_bound ((hgmeas Ft).norm.pow_const 2).aestronglyMeasurable ((c * L * r) ^ 2)
          (Filter.Eventually.of_forall (fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (norm_nonneg _) (hgFtb x) 2))
      have heq : ∫⁻ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ₑ ^ 2 =
          ENNReal.ofReal (∫ x in ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint1
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
        refine lintegral_congr (fun x => ?_)
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
      rw [heq, ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ∀ x ∈ ball (0 : Rn n) 1, ‖gradient Ft x‖ ^ 2 = E⁻¹ * ‖gradient fj (r • x)‖ ^ 2 :=
        fun x hx => by
          rw [hgFt x hx, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hsE, inv_pow,
            Real.sq_sqrt hE.le]
      rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
        Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖gradient fj x‖ ^ 2) _ hr,
        smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul]
      have h3 := (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        hHSint hpt).trans henergy
      have hrn : 0 < r ^ n := pow_pos hr n
      calc E⁻¹ * ((r ^ n)⁻¹ * ∫ x in ball (0 : Rn n) r, ‖gradient fj x‖ ^ 2)
          ≤ E⁻¹ * ((r ^ n)⁻¹ * (E * r ^ n)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hrn.le))
              (inv_nonneg.2 hE.le)
        _ = 1 := by rw [mul_comm E, ← mul_assoc (r ^ n)⁻¹, inv_mul_cancel₀ hrn.ne', one_mul,
            inv_mul_cancel₀ hE.ne']
    -- almost harmonicity, by scaling `ζ₀ = ζ(r⁻¹ ·)`
    have halmostF : ∀ ζ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball 0 1 → ∀ M : ℝ, (∀ x, ‖gradient ζ x‖ ≤ M) →
        |∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x)| ≤ δ * M := by
      intro ζ hζ hζcs hζsupp M hM
      have hζ0s : ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ (r⁻¹ • x)) := hζ.comp (contDiff_const_smul _)
      have hζ0cs : HasCompactSupport (fun x => ζ (r⁻¹ • x)) := hζcs.comp_smul (inv_ne_zero hr.ne')
      have hζ0supp : tsupport (fun x => ζ (r⁻¹ • x)) ⊆ ball 0 r := by
        rw [show (fun x => ζ (r⁻¹ • x)) = ζ ∘ (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
          from rfl, tsupport_comp_eq_preimage]
        intro x hx
        have hx' := mem_ball_zero_iff.1 (hζsupp hx)
        rw [Homeomorph.smulOfNeZero_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
          inv_mul_lt_iff₀ hr, mul_one] at hx'
        exact mem_ball_zero_iff.2 hx'
      have hgζ0 : ∀ x, gradient (fun x => ζ (r⁻¹ • x)) x = r⁻¹ • gradient ζ (r⁻¹ • x) := fun x => by
        rw [gradient, gradient, fderiv_comp_smul, map_smul]
      have hM0 : ∀ x, ‖gradient (fun x => ζ (r⁻¹ • x)) x‖ ≤ r⁻¹ * M := fun x => by
        rw [hgζ0, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
        exact mul_le_mul_of_nonneg_left (hM _) (inv_nonneg.2 hr.le)
      have hA := halmost _ hζ0s hζ0cs hζ0supp (r⁻¹ * M) hM0 j
      rw [← hfj] at hA
      have h1 : ∀ z ∈ ball (0 : Rn n) 1, inner ℝ (gradient Ft z) (gradient ζ z) =
          ((Real.sqrt E)⁻¹ * r) * inner ℝ (gradient fj (r • z))
            (gradient (fun x => ζ (r⁻¹ • x)) (r • z)) := fun z hz => by
        rw [hgFt z hz, hgζ0, smul_smul, inv_mul_cancel₀ hr.ne', one_smul, real_inner_smul_left,
          real_inner_smul_right, mul_assoc, ← mul_assoc r, mul_inv_cancel₀ hr.ne', one_mul]
      have hrel : ∫ x in ball (0 : Rn n) 1, inner ℝ (gradient Ft x) (gradient ζ x) =
          (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            ∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x) := by
        rw [setIntegral_congr_fun measurableSet_ball h1, integral_const_mul,
          Measure.setIntegral_comp_smul_of_pos volume
            (fun x => inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)) _ hr,
          smul_unitBall_of_pos hr, finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
          mul_comm ((Real.sqrt E)⁻¹ * r)]
      have hk0 : 0 ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) :=
        mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) (mul_nonneg (inv_nonneg.2 hsE.le) hr.le)
      rw [hrel, abs_mul, abs_of_nonneg hk0]
      calc (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) *
            |∫ x in ball (0 : Rn n) r, inner ℝ (gradient fj x) (gradient (fun x => ζ (r⁻¹ • x)) x)|
          ≤ (r ^ n)⁻¹ * ((Real.sqrt E)⁻¹ * r) * (δ * Real.sqrt E * (r⁻¹ * M) * r ^ n) :=
            mul_le_mul_of_nonneg_left hA hk0
        _ = δ * M := by
            field_simp
    obtain ⟨u, hu1, hu2, hu3⟩ := hHA Ft (gradient Ft) hW12 henergyF halmostF
    refine ⟨u, hu1, hu2, le_of_eq_of_le (setLIntegral_congr_fun measurableSet_ball (fun x hx => ?_)) hu3⟩
    rw [hFtE x (ball_subset_closedBall hx), hfj, ← hc]
  /- Step 9: `a = (r√E u_j(0))_j`, `A x = (√E ∇u_j(0)·x)_j`, and the three estimates. -/
  choose u hu_harm hu_en hu_cl using hcomp
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (r * Real.sqrt E)⁻¹ := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ inv_pos.2 (mul_pos hr hsE)
  have hrc : r * Real.sqrt E * c = 1 := by rw [hc]; exact mul_inv_cancel₀ (mul_pos hr hsE).ne'
  simp only [← hc] at hu_cl
  have hsV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have hfc : ∀ k : Fin ℓ, ContinuousOn (fun z : Rn n => c * f (r • z) k) (ball 0 1) := fun k =>
    continuousOn_const.mul ((EuclideanSpace.proj k : Rn ℓ →L[ℝ] ℝ).continuous.comp_continuousOn
      (hLip.continuousOn.comp (continuous_const_smul r).continuousOn (fun z hz => by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        exact mul_le_of_le_one_right hr.le (mem_ball_zero_iff.1 hz).le)))
  have hdm : ∀ k : Fin ℓ, AEStronglyMeasurable (fun z => u k z - c * f (r • z) k)
      (volume.restrict (ball (0 : Rn n) 1)) := fun k =>
    ((hu_harm k).continuousOn.sub (hfc k)).aestronglyMeasurable measurableSet_ball
  -- interior estimates for each `u k`
  have hest : ∀ k : Fin ℓ, ‖gradient (u k) 0‖ ≤ C₁ * Real.sqrt V ∧
      (∀ z : Rn n, ‖z‖ ≤ 1/4 →
        |u k z - u k 0 - inner ℝ (gradient (u k) 0) z| ≤ C₃ * Real.sqrt V * ‖z‖ ^ 2) ∧
      |u k 0| ≤ C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
    intro k
    have hg := CS (fun x => ‖gradient (u k) x‖ₑ)
      ((InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (u k))).enorm.aemeasurable 1 zero_le_one
        (by rw [ENNReal.ofReal_one]; exact hu_en k)
    rw [Real.sqrt_one, mul_one] at hg
    have h1 := CS _ (hdm k).enorm ε hε.le (hu_cl k)
    have h2 : ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ ≤ ENNReal.ofReal (V * (c * h)) := by
      calc ∫⁻ x in ball (0 : Rn n) 1, ‖c * f (r • x) k‖ₑ
          ≤ ∫⁻ _ in ball (0 : Rn n) 1, ENNReal.ofReal (c * h) := by
            refine setLIntegral_mono measurable_const (fun z hz => ?_)
            rw [← ofReal_norm, norm_mul, Real.norm_eq_abs, abs_of_pos hcpos]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hcpos.le)
            exact (PiLp.norm_apply_le (f (r • z)) k).trans (hbound _ (by
              rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
              exact mul_lt_of_lt_one_right hr (mem_ball_zero_iff.1 hz)))
        _ = ENNReal.ofReal (V * (c * h)) := by
          rw [setLIntegral_const, ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← hVdef,
            ← ENNReal.ofReal_mul (mul_nonneg hcpos.le hh), mul_comm (c * h) V]
    have hu1 : ∫⁻ x in ball (0 : Rn n) 1, ‖u k x‖ₑ ≤
        ENNReal.ofReal (Real.sqrt V * Real.sqrt ε + V * (c * h)) := by
      rw [ENNReal.ofReal_add (mul_nonneg hsV (Real.sqrt_nonneg _))
        (mul_nonneg hV0 (mul_nonneg hcpos.le hh))]
      refine le_trans (lintegral_mono (fun x => ?_))
        ((lintegral_add_left' (hdm k).enorm _).trans_le (add_le_add h1 h2))
      calc ‖u k x‖ₑ = ‖(u k x - c * f (r • x) k) + c * f (r • x) k‖ₑ := by rw [sub_add_cancel]
        _ ≤ _ := enorm_add_le _ _
    obtain ⟨hg0, hT⟩ := (HE (u k) (hu_harm k)).2 _ hsV hg
    exact ⟨hg0, hT, (HE (u k) (hu_harm k)).1 _
      (add_nonneg (mul_nonneg hsV (Real.sqrt_nonneg _)) (mul_nonneg hV0 (mul_nonneg hcpos.le hh)))
      hu1⟩
  -- the affine map
  obtain ⟨a, ha⟩ : ∃ a : Rn ℓ, a = WithLp.toLp 2 (fun k => r * Real.sqrt E * u k 0) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Rn n →L[ℝ] Rn ℓ, A = ∑ k : Fin ℓ,
      (Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight (EuclideanSpace.single k (1:ℝ)) :=
    ⟨_, rfl⟩
  have haapply : ∀ k, a k = r * Real.sqrt E * u k 0 := fun k => by rw [ha]
  have hAapply : ∀ (x : Rn n) (k : Fin ℓ), (A x) k = Real.sqrt E * inner ℝ (gradient (u k) 0) x :=
    fun x k => by
      rw [hA]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.smul_apply, innerSL_apply_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Pi.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨a, A, ?_, ?_, ?_⟩
  · -- `|A| ≤ C √E`
    have hAn : ‖A‖ ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
      rw [hA]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ k : Fin ℓ, ‖(Real.sqrt E • innerSL ℝ (gradient (u k) 0)).smulRight
            (EuclideanSpace.single k (1:ℝ))‖
          ≤ ∑ _k : Fin ℓ, (C₁ * Real.sqrt V) * Real.sqrt E := Finset.sum_le_sum (fun k _ => by
            rw [ContinuousLinearMap.norm_smulRight_apply, EuclideanSpace.norm_single, norm_one,
              mul_one, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_pos hsE, mul_comm]
            exact mul_le_mul_of_nonneg_right (hest k).1 hsE.le)
        _ = ℓ * (C₁ * Real.sqrt V) * Real.sqrt E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
    have h0 : 0 ≤ ℓ * (C₁ * Real.sqrt V) * Real.sqrt E :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hC₁ hsV)) hsE.le
    calc hsNorm A ≤ Real.sqrt (n * (ℓ * (C₁ * Real.sqrt V) * Real.sqrt E) ^ 2) :=
          Real.sqrt_le_sqrt ((hHS A).trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) hAn 2) (Nat.cast_nonneg _)))
      _ = Real.sqrt n * (ℓ * (C₁ * Real.sqrt V)) * Real.sqrt E := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0, ← mul_assoc]
      _ ≤ C * Real.sqrt E := mul_le_mul_of_nonneg_right hC1 hsE.le
  · -- `|a| ≤ C (h + r √(εE))`
    have hB0 : 0 ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) :=
      mul_nonneg hC₁ (add_nonneg (mul_nonneg hsV (mul_nonneg hr.le (Real.sqrt_nonneg _)))
        (mul_nonneg hV0 hh))
    have hak : ∀ k, |a k| ≤ C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h) := fun k => by
      rw [haapply, abs_mul, abs_of_pos (mul_pos hr hsE), Real.sqrt_mul hε.le]
      calc r * Real.sqrt E * |u k 0| ≤ r * Real.sqrt E *
            (C₁ * (Real.sqrt V * Real.sqrt ε + V * (c * h))) :=
            mul_le_mul_of_nonneg_left (hest k).2.2 (mul_pos hr hsE).le
        _ = C₁ * (Real.sqrt V * (r * (Real.sqrt ε * Real.sqrt E)) +
            V * h * (r * Real.sqrt E * c)) := by ring
        _ = _ := by rw [hrc, mul_one]
    calc ‖a‖ = Real.sqrt (∑ k : Fin ℓ, ‖a k‖ ^ 2) := EuclideanSpace.norm_eq a
      _ ≤ Real.sqrt (∑ _k : Fin ℓ, (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hak k) 2))
      _ = Real.sqrt ℓ * (C₁ * (Real.sqrt V * (r * Real.sqrt (ε * E)) + V * h)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB0]
      _ ≤ Real.sqrt ℓ * C₁ * (Real.sqrt V + V) * (h + r * Real.sqrt (ε * E)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hab _ _ _ _ hsV hV0 hh
            (mul_nonneg hr.le (Real.sqrt_nonneg _))) hC₁) (Real.sqrt_nonneg _)
      _ ≤ C * (h + r * Real.sqrt (ε * E)) :=
          mul_le_mul_of_nonneg_right hC2 (add_nonneg hh (mul_nonneg hr.le (Real.sqrt_nonneg _)))
  · -- the `L²` estimate
    intro e he he4
    have he1 : e ≤ 1 := he4.trans (by norm_num)
    have hrn : 0 < r ^ n := pow_pos hr n
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) e)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hcv : ∫ x in ball (0 : Rn n) (e * r), ‖f x - (a + A x)‖ ^ 2 =
        r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 := by
      have h := Measure.setIntegral_comp_smul_of_pos volume (fun x => ‖f x - (a + A x)‖ ^ 2)
        (ball (0 : Rn n) e) hr
      rw [smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_comm r e,
        finrank_euclideanSpace_fin, smul_eq_mul] at h
      rw [h, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
    rw [hcv]
    -- integrability and size of `(u_k - F_k)²`
    have hsq : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) ∧
        ∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2 ≤ ε := by
      intro k
      have hfi : ∫⁻ z in ball (0 : Rn n) 1, ‖(u k z - c * f (r • z) k) ^ 2‖ₑ =
          ∫⁻ z in ball (0 : Rn n) 1, ‖u k z - c * f (r • z) k‖ₑ ^ 2 :=
        lintegral_congr (fun z => enorm_pow _ _)
      have hi : IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2) (ball (0 : Rn n) 1) :=
        ⟨(hdm k).pow 2, by rw [HasFiniteIntegral, hfi]; exact (hu_cl k).trans_lt ENNReal.ofReal_lt_top⟩
      refine ⟨hi, (setIntegral_mono_set hi (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        (Filter.Eventually.of_forall (ball_subset_ball he1))).trans ?_⟩
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _))
        ((hdm k).pow 2)]
      refine ENNReal.toReal_le_of_le_ofReal hε.le (le_trans (le_of_eq ?_) (hu_cl k))
      refine lintegral_congr (fun z => ?_)
      rw [← enorm_pow, Real.enorm_eq_ofReal (sq_nonneg _)]
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = C₃ * Real.sqrt V * e ^ 2 := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := hD ▸ mul_nonneg (mul_nonneg hC₃ hsV) (sq_nonneg e)
    -- pointwise bound on `B_e`
    have hpt : ∀ z ∈ ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2 ≤
        2 * (r ^ 2 * E) * ∑ k : Fin ℓ, ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by
      intro z hz
      have hz' : ‖z‖ ≤ 1/4 := (mem_ball_zero_iff.1 hz).le.trans he4
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hcomp : (f (r • z) - (a + A (r • z))) k = r * Real.sqrt E *
          (-(u k z - c * f (r • z) k) + (u k z - u k 0 - inner ℝ (gradient (u k) 0) z)) := by
        rw [WithLp.ofLp_sub, WithLp.ofLp_add, Pi.sub_apply, Pi.add_apply, haapply, hAapply,
          real_inner_smul_right]
        linear_combination (-(f (r • z) k)) * hrc
      have hY : (u k z - u k 0 - inner ℝ (gradient (u k) 0) z) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs, hD]
        exact pow_le_pow_left₀ (abs_nonneg _) (((hest k).2.1 z hz').trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z)
            (mem_ball_zero_iff.1 hz).le 2) (mul_nonneg hC₃ hsV))) 2
      rw [Real.norm_eq_abs, sq_abs, hcomp, mul_pow, mul_pow, Real.sq_sqrt hE.le]
      calc r ^ 2 * E * (-(u k z - c * f (r • z) k) + (u k z - u k 0 -
            inner ℝ (gradient (u k) 0) z)) ^ 2
          ≤ r ^ 2 * E * (2 * ((-(u k z - c * f (r • z) k)) ^ 2 + D ^ 2)) :=
            mul_le_mul_of_nonneg_left (hsq2 _ _ _ hY) (mul_nonneg (sq_nonneg r) hE.le)
        _ = 2 * (r ^ 2 * E) * ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) := by ring
    have hint : ∀ k, IntegrableOn (fun z => (u k z - c * f (r • z) k) ^ 2 + D ^ 2)
        (ball (0 : Rn n) e) := fun k =>
      ((hsq k).1.mono_set (ball_subset_ball he1)).add (integrable_const _)
    have hvol : ∫ _ in ball (0 : Rn n) e, D ^ 2 = e ^ n * V * D ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, Measure.addHaar_ball_of_pos volume _ he,
        finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg he.le n),
        ← hVdef]
    have hP : e ^ n * V * D ^ 2 = C₃ ^ 2 * V ^ 2 * (e ^ n * e ^ 4) := by
      rw [hD, mul_pow, mul_pow, Real.sq_sqrt hV0]; ring
    have h2rE : 0 ≤ 2 * (r ^ 2 * E) := mul_nonneg zero_le_two (mul_nonneg (sq_nonneg r) hE.le)
    calc r ^ n * ∫ z in ball (0 : Rn n) e, ‖f (r • z) - (a + A (r • z))‖ ^ 2
        ≤ r ^ n * ∫ z in ball (0 : Rn n) e, 2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((u k z - c * f (r • z) k) ^ 2 + D ^ 2) :=
          mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _))
            ((integrable_finsetSum _ (fun k _ => hint k)).const_mul _)
            ((ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall hpt))) hrn.le
      _ = r ^ n * (2 * (r ^ 2 * E) * ∑ k : Fin ℓ,
          ((∫ z in ball (0 : Rn n) e, (u k z - c * f (r • z) k) ^ 2) + e ^ n * V * D ^ 2)) := by
          rw [integral_const_mul, integral_finsetSum _ (fun k _ => hint k)]
          congr 2
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [integral_add ((hsq k).1.mono_set (ball_subset_ball he1)) (integrable_const _), hvol]
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ, (ε + e ^ n * V * D ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => add_le_add (hsq k).2 le_rfl)) h2rE) hrn.le
      _ ≤ r ^ n * (2 * (r ^ 2 * E) * ∑ _k : Fin ℓ,
          ((1 + C₃ ^ 2 * V ^ 2) * (ε + e ^ n * e ^ 4))) := by
          rw [hP]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum
            (fun k _ => hKP _ _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
              (mul_nonneg (pow_nonneg he.le n) (pow_nonneg he.le 4)) hε.le)) h2rE) hrn.le
      _ = (2 * ℓ * (1 + C₃ ^ 2 * V ^ 2)) * (ε + e ^ (n + 4)) * E * r ^ (n + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add,
            pow_add]
          ring
      _ ≤ C * (ε + e ^ (n + 4)) * E * r ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3
            (add_nonneg hε.le (pow_nonneg he.le _))) hE.le) (pow_nonneg hr.le _)

end Submission

theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧ LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧ TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧ ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧ RegularSetOpenDense := by sorry

end GMT.Ch05

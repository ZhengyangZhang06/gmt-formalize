import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 6 "Currents" (pp. 131–180)

Frozen contract.  Currents, boundary, mass and weak convergence are the clean SimonGMT
objects (`Poincare.SimonGMT.Chapter06`):

* `GeometricCurrentOn U n`: sequentially continuous linear functionals on `𝒟ⁿ(U)` (Simon 2.1);
* `T.boundary` (2.3), `T.massOn W` (2.5, Euclidean coefficient norm of Remark 2.6),
  `T.mass = T.massOn U` (2.4), `T.support` (2.11), `WeaklyConvergesOn` (2.13).

Integer multiplicity currents `τ(M, θ, ξ)` (3.1), restriction `T ⌞ A` (2.9), slices (4.6),
the Lipschitz push-forward (3.6), lattice polyhedral chains (§5) and the flat pseudometric
`d_W` (7.1) are defined below from primitive data.  Hausdorff measure `Hⁿ` is Mathlib's
normalized `μHE[n]` (equal to Lebesgue measure on `ℝⁿ`).

**Degree convention.**  `GeometricCurrentOn.boundary` is defined on degree `m + 1`.  Whenever
the book's statement involves `∂T` for an `n`-current with `n ≥ 1`, the Lean statement writes
the book's `n` as `m + 1`.  The ambient space is `ℝ^P` (book: `ℝ^P` in §2, §8, `ℝ^{n+ℓ}`
elsewhere); in §5–§6, where constants are `c(n, ℓ)`, the ambient space is `ℝ^{(m+1)+ℓ}`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace GMT.Ch06

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt)
open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity)

noncomputable section

/-- Euclidean space `ℝ^P`. -/
abbrev Eucl (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Basic notions -/

/-- Simon's `W ⊂⊂ U` for open `W`: `W` is open and `closure W` is a compact subset of `U`. -/
def CompactlyContainedOpen (W U : Set (Eucl P)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- Simon Ch. 6, 3.1 (p. 146) and 8.1 (p. 173): the conditions on the triple `(M, θ, ξ)`.

* `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable (Ch. 3, 1.1);
* `θ` is positive on `M` and locally `Hⁿ`-integrable on `M` in `U`;
* `ξ : M → Λₙ(ℝ^P)` is `Hⁿ`-measurable and for `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an
  orthonormal basis `τ` of the approximate tangent space `TₓM` of `M` (w.r.t. `θ`, Ch. 3, 1.7).

`n`-vectors are `NVector (ℝ^P) n` (the dual of `n`-covectors), so `⟨ω, ξ⟩ = ξ ω` and
`τ₁ ∧ ⋯ ∧ τₙ = simpleNVector τ`.  The sign `±` (as printed in 8.1) is only needed for `n = 0`,
where there is no frame to flip. -/
structure IsRectifiableTriple (U : Set (Eucl P)) (n : ℕ) (M : Set (Eucl P))
    (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) : Prop where
  subset : M ⊆ U
  nullMeasurableSet : NullMeasurableSet M (μHE[n] : Measure (Eucl P))
  countablyRectifiable : CountablyRectifiable n M
  pos : ∀ x ∈ M, 0 < θ x
  integrableOn : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
    IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))
  aestronglyMeasurable : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M)
  orients : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∃ τ : Fin n → Eucl P,
    Orthonormal ℝ τ ∧
    HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
    (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)

/-- Simon Ch. 6, 3.1 (‡) (p. 146): `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`. -/
def tauAction (n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (ω : DifferentialForm (Eucl P) n) : ℝ :=
  ∫ x in M, θ x * ξ x (ω x) ∂(μHE[n] : Measure (Eucl P))

/-- Simon Ch. 6, 8.1 (p. 173): `T` is *rectifiable*, `T = τ(M, θ, ξ)` with `θ` real-valued
(positive, locally `Hⁿ`-integrable; footnote 4). -/
def IsRectifiableCurrent {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Simon Ch. 6, 3.1 (p. 146): `T ∈ 𝒟ₙ(U)` is an *integer multiplicity (rectifiable) current*:
`T = τ(M, θ, ξ)` with `θ` positive integer-valued. -/
def IsIntegerMultiplicity {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
    ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Integral current (the hypothesis of Simon Ch. 6, 8.2, p. 176): `T` and `∂T` are both integer
multiplicity (both then have locally finite mass). -/
def IsIntegralCurrent {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) : Prop :=
  IsIntegerMultiplicity T ∧ IsIntegerMultiplicity T.boundary

/-! ## Measure representation, restriction, slices -/

/-- Simon Ch. 6, (2.7) (p. 136): `T(ω) = ∫ ⟨ω, v⟩ dμ`, with `⟨ω, v⟩` `μ`-integrable for every
test form `ω` (testing with `φ dx^α`, `φ = 1` on a compact `K ⊆ U`, this is equivalent to `v`
being locally `μ`-integrable on `U`).  No normalization of `v` is required: such `(μ, v)` exists
iff `T` has locally finite mass (Riesz, Ch. 1, 4.14), and the vector measure `v μ` on `U` is
then uniquely determined by `T`. -/
def IsMeasureRepresentation {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) : Prop :=
  ∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ ∧
    T ω = ∫ x, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.9) (p. 136): `S = T ⌞ A` for a Borel set `A`, i.e.
`S(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`.  Defined through any representation of `T` as in (2.7); the result
does not depend on the representation (uniqueness of the vector measure `T⃗ μ_T`). -/
def IsRestriction {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) (A : Set (Eucl P))
    (S : GeometricCurrentOn U n) : Prop :=
  MeasurableSet A ∧ ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
    IsMeasureRepresentation T μ v ∧
    ∀ ω : TestFormOn U n, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.8) (p. 136): `μ` is the total variation (mass) measure `μ_T` of `T`:
`μ_T(W) = M_W(T)` for every open `W ⊂⊂ U`, and `μ_T` lives on `U`. -/
def IsMassMeasure {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) : Prop :=
  μ Uᶜ = 0 ∧ ∀ W, CompactlyContainedOpen W U → μ W = T.massOn W

/-- Simon Ch. 6, (4.6) (p. 157): the slice `⟨T, f, t₋⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}`
(sets taken inside `U`), for `T` with `M_W(T) + M_W(∂T) < ∞`. -/
def IsSlice {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ)
    (t : ℝ) (S : GeometricCurrentOn U m) : Prop :=
  ∃ (A : GeometricCurrentOn U (m + 1)) (B : GeometricCurrentOn U m),
    IsRestriction T {x | x ∈ U ∧ f x < t} A ∧
    IsRestriction T.boundary {x | x ∈ U ∧ f x < t} B ∧
    ∀ ω : TestFormOn U m, S ω = A.boundary ω - B ω

/-! ## Lipschitz push-forward -/

/-- Simon Ch. 6, (3.6) (p. 147) and Ch. 3, 2.1–2.2: `S = f_# T` for `T = τ(M, θ, ξ)` and `f`
locally Lipschitz, `f_# T(ω) = ∫_M ⟨ω(f(x)), (d^M f_x)_# ξ(x)⟩ θ(x) dHⁿ(x)`.

`L x` is any linear map agreeing with `d^M f_x` on `TₓM`; by Ch. 3, §2 (p. 76),
`d^M f_x(τ) = (d/dt) f(x + tτ)|_{t=0}` for `τ ∈ TₓM`, `Hⁿ`-a.e. `x ∈ M`.  As `ξ(x) ∈ Λₙ(TₓM)`,
the integrand only depends on `L x` restricted to `TₓM`, so `S` is uniquely determined. -/
def IsLipschitzPushforward {Q n : ℕ} {U : Set (Eucl P)} {V : Set (Eucl Q)}
    (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q) (S : GeometricCurrentOn V n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)),
    IsRectifiableTriple U n M θ ξ ∧ (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) ∧
    (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt n M θ x Tx →
        ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) ∧
    ∀ ω : TestFormOn V n, S ω =
      ∫ x in M, θ x * nVectorPushforward n (L x) (ξ x)
        ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))

/-! ## Lattice polyhedral chains (§5) -/

/-- Index of an `n`-face of the cubical lattice in `ℝ^N` (Simon Ch. 6, §5, p. 159): a lattice
point `z ∈ ℤ^N` and the increasing multi-index `α` of the `n` coordinate directions spanned. -/
abbrev LatticeFaceIndex (n N : ℕ) := (Fin N → ℤ) × SimonMultiIndex n N

/-- The closed face `ρ (z + F_α) ∈ 𝓛ₙ(ρ)`, `F_α = {x : xᵢ ∈ [0,1] (i ∈ α), xᵢ = 0 (i ∉ α)}`.
Every closed `n`-face of the decomposition `⋃_z ρ(z + C)` arises from exactly one index. -/
def latticeFace {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N) : Set (Eucl N) :=
  {x | ∀ i : Fin N,
    (i ∈ range F.2 → ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)) ∧
    (i ∉ range F.2 → x i = ρ * (F.1 i : ℝ))}

/-- `[[F]](ω) = ∫_F ⟨ω, e_{α₁} ∧ ⋯ ∧ e_{αₙ}⟩ dHⁿ` (2.2), `F` oriented by its coordinate
directions in increasing order. -/
def latticeFaceAction {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N)
    (ω : DifferentialForm (Eucl N) n) : ℝ :=
  ∫ x in latticeFace ρ F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
    ∂(μHE[n] : Measure (Eucl N))

/-- `Pc = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]` as a current in `U` (the sum is locally finite). -/
def IsLatticeChain {n N : ℕ} {U : Set (Eucl N)} (ρ : ℝ) (β : LatticeFaceIndex n N → ℝ)
    (Pc : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, Pc ω = ∑' F, β F * latticeFaceAction ρ F ω

/-! ## Flat pseudometric (§7) -/

/-- Simon Ch. 6, (7.1) (p. 170): `d_W(T₁, T₂) = inf {M_W(S) + M_W(R) : T₁ − T₂ = ∂R + S,
R ∈ 𝒟ₙ₊₁(U), S ∈ 𝒟ₙ(U) integer multiplicity}`. -/
def flatDistance {U : Set (Eucl P)} {n : ℕ} (W : Set (Eucl P))
    (T₁ T₂ : GeometricCurrentOn U n) : ℝ≥0∞ :=
  ⨅ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n)
    (_ : IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
      ∀ ω : TestFormOn U n, T₁ ω - T₂ ω = R.boundary ω + S ω),
    S.massOn W + R.massOn W

/-! ## Headline results -/

/-- **Simon Ch. 6, Lemma 2.15 (p. 137).**  If `T_q ∈ 𝒟ₙ(U)` and `sup_q M_W(T_q) < ∞` for each
`W ⊂⊂ U`, there are a subsequence `T_{q'}` and `T ∈ 𝒟ₙ(U)` with `T_{q'} ⇀ T` and
`∫ ⟨ω, T⃗_{q'}⟩ dμ_{T_{q'}} → ∫ ⟨ω, T⃗⟩ dμ_T` for every continuous compactly supported `n`-form
`ω` on `U` (for all representations (2.7) of the `T_{q'}` and of `T`). -/
def CompactnessUnderMassBounds : Prop :=
  ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U n,
    (∀ W, CompactlyContainedOpen W U → (⨆ q, (T q).massOn W) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U n), StrictMono φ ∧
      WeaklyConvergesOn (fun q => T (φ q)) T₀ ∧
      ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U →
        ∀ (μ : ℕ → Measure (Eucl P)) (v : ℕ → Eucl P → NVector (Eucl P) n)
          (μ₀ : Measure (Eucl P)) (v₀ : Eucl P → NVector (Eucl P) n),
          (∀ q, IsMeasureRepresentation (T (φ q)) (μ q) (v q)) →
          IsMeasureRepresentation T₀ μ₀ v₀ →
          Tendsto (fun q => ∫ x, v q x (ω x) ∂(μ q)) atTop (𝓝 (∫ x, v₀ x (ω x) ∂μ₀))

/-- **Simon Ch. 6, Theorem 2.34 (Constancy Theorem, p. 142).**  If `U ⊆ ℝⁿ` is open and
connected, `T ∈ 𝒟ₙ(U)` and `∂T = 0`, then `T = c [[U]]` for a constant `c`, where
`[[U]](ω) = ∫_U ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.  (Book `n = m + 1`.) -/
def ConstancyTheorem : Prop :=
  ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U →
    ∀ T : GeometricCurrentOn U (m + 1), T.boundary = 0 →
      ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1),
        T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume

/-- **Simon Ch. 6, Lemma 3.9 (p. 148).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity,
`f : U → V` (`V ⊆ ℝ^Q` open) is locally Lipschitz and `f | spt T` is proper, then the
push-forward `f_# T` of (3.6) exists in `𝒟ₙ(V)` and is integer multiplicity. -/
def LipschitzPushforwardIntegerMultiplicity : Prop :=
  ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
    ∀ (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q),
      IsIntegerMultiplicity T → LocallyLipschitzOn U f → MapsTo f U V →
      (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) →
      ∃ S : GeometricCurrentOn V n, IsLipschitzPushforward T f S ∧ IsIntegerMultiplicity S

/-- **Simon Ch. 6, Theorem 3.11 (Federer–Fleming Compactness Theorem, p. 149).**  If
`T_j ∈ 𝒟ₙ(U)` are integer multiplicity and `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all
`W ⊂⊂ U`, then some subsequence converges weakly in `U` to an integer multiplicity
`T ∈ 𝒟ₙ(U)`.  (Book `n = m + 1`.) -/
def FedererFlemingCompactness : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U (m + 1),
    (∀ j, IsIntegerMultiplicity (T j)) →
    (∀ W, CompactlyContainedOpen W U → (⨆ j, ((T j).massOn W + (T j).boundary.massOn W)) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U (m + 1)), StrictMono φ ∧
      IsIntegerMultiplicity T₀ ∧ WeaklyConvergesOn (fun j => T (φ j)) T₀

/-- **Simon Ch. 6, §4 Slicing (4.4–4.10, pp. 153–158).**  Let `T ∈ 𝒟ₙ(U)` with
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, and `f` Lipschitz on `U` (constant `L`).  Then the
slices `⟨T, f, t⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` (4.6) exist for every `t`, satisfy
`spt ⟨T, f, t⟩ ⊆ spt T ∩ {f = t}` (4.8); if `T` is integer multiplicity they are integer
multiplicity for `L¹`-a.e. `t` (4.4, 4.5(2)); and for every open `W ⊆ U`, every `L_W` with
`|Df| ≤ L_W` a.e. on `W` (i.e. `L_W ≥ ess sup_W |Df|`) and `a < b` (4.10, upper integral):
`∫*_a^b M_W(⟨T, f, t⟩) dt ≤ L_W · M_W(T ⌞ {a < f < b})`.
The book prints `M(T ⌞ {a < f < b})` on the right of 4.10; its proof (4.9) gives the stronger
`M_W`, stated here.  (Book `n = m + 1`.) -/
def SlicingTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∃ S : ℝ → GeometricCurrentOn U m,
      (∀ t, IsSlice T f t (S t)) ∧
      (∀ t, (S t).support ⊆ T.support ∩ {x | f x = t}) ∧
      (IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), IsIntegerMultiplicity (S t)) ∧
      ∀ W, IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ a b : ℝ, a < b →
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R →
          ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧
            ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W

/-- **Simon Ch. 6, 5.3 (Deformation Theorem, scaled version, p. 160); `ρ = 1` is 5.1 (p. 159).**
For `n, ℓ ≥ 1` there is `C = C(n, ℓ)` such that for every `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`M(T) + M(∂T) < ∞` and every `ρ > 0`, `T − P = ∂R + S` where `P = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]`,
`M(P) ≤ C M(T)`, `M(∂P) ≤ C M(∂T)`, `M(R) ≤ C ρ M(T)`, `M(S) ≤ C ρ M(∂T)`,
`spt P ∪ spt R ⊆ {dist(·, spt T) < 2√(n+ℓ) ρ}`, `spt ∂P ∪ spt S ⊆ {dist(·, spt ∂T) < 2√(n+ℓ) ρ}`;
if `T` is integer multiplicity, `P, R` are integer multiplicity with `β_F ∈ ℤ`, and if moreover
`∂T` is integer multiplicity then so is `S`.
Errata: the book prints `n, k ∈ {1,2,…}` and `C(n, k)` for `n, ℓ`; `𝓛_j(ρ)` for `𝓛ₙ(ρ)`;
"so is s" for "so is S".  (Book `n = m + 1`.) -/
def DeformationTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ (T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
    T.mass + T.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ →
    ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1))
      (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ)
      (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2))
      (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
      IsLatticeChain ρ β Pc ∧
      (∀ ω, T ω - Pc ω = R.boundary ω + S ω) ∧
      Pc.mass ≤ C * T.mass ∧ Pc.boundary.mass ≤ C * T.boundary.mass ∧
      R.mass ≤ C * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ C * ENNReal.ofReal ρ * T.boundary.mass ∧
      Pc.support ∪ R.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.support ∧
      Pc.boundary.support ∪ S.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.boundary.support ∧
      (IsIntegerMultiplicity T →
        (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity R) ∧
      (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)

/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem, p. 168).**  For `n ≥ 2`, `ℓ ≥ 1` there is
`c = c(n, ℓ)` such that every integer multiplicity `T ∈ 𝒟ₙ₋₁(ℝ^{n+ℓ})` with compact support and
`∂T = 0` bounds an integer multiplicity `R ∈ 𝒟ₙ(ℝ^{n+ℓ})` with compact support and
`M(R)^{(n−1)/n} ≤ c M(T)`.  (Book `n = m + 2`.) -/
def IsoperimetricTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 1),
    IsIntegerMultiplicity T → IsCompact T.support → T.boundary = 0 →
    ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
      R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ c * T.mass

/-- **Simon Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem, p. 169).**  For integer
multiplicity `T ∈ 𝒟ₙ(U)`, `U ⊆ ℝ^{n+ℓ}` open, with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U`,
there are `ρ_k ↓ 0` and `P_k = ∑_{F ∈ 𝓛ₙ(ρ_k)} β^{(k)}_F [[F]]` with `β^{(k)}_F ∈ ℤ` and
`P_k ⇀ T` in `U`.  (Printed `F_n(ρ_k)`, `β_R^{(k)}` mean `𝓛ₙ(ρ_k)`, `β_F^{(k)}`.  Book `n = m + 1`.) -/
def PolyhedralApproximation : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ U : Set (Eucl (m + 1 + ℓ)), IsOpen U →
    ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ)
        (Pk : ℕ → GeometricCurrentOn U (m + 1)),
        (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧
        WeaklyConvergesOn Pk T

/-- **Simon Ch. 6, 6.3 (Boundary Rectifiability Theorem, p. 170).**  If `T ∈ 𝒟ₙ(U)` is integer
multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U` (printed `M(∂T)`), then `∂T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def BoundaryRectifiability : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) →
    IsIntegerMultiplicity T.boundary

/-- **Simon Ch. 6, Theorem 7.2 (p. 170).**  Let `T, T_j ∈ 𝒟ₙ(U)` be integer multiplicity with
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`.  Then `T_j ⇀ T` iff `d_W(T_j, T) → 0`
for every `W ⊂⊂ U`.  (Book `n = m + 1`.) -/
def FlatConvergenceIffWeakConvergence : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      (WeaklyConvergesOn Tj T ↔
        ∀ W, CompactlyContainedOpen W U →
          Tendsto (fun j => flatDistance W (Tj j) T) atTop (𝓝 0))

/-- **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  If `T ∈ 𝒟ₙ(U)` has
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and the upper density `Θ*ⁿ(μ_T, x) > 0` for `μ_T`-a.e.
`x ∈ U`, then `T = τ(M, θ, ξ)` is rectifiable (with real `θ`).  (Book `n = m + 1`.) -/
def RectifiabilityTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
    (∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧
      ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) →
    IsRectifiableCurrent T

/-- **Simon Ch. 6, Theorem 8.2 (p. 176).**  If `T_j, ∂T_j` are integer multiplicity,
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U` and `T_j ⇀ T ∈ 𝒟ₙ(U)`, then `T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def IntegralityOfWeakLimits : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
      (∀ j, IsIntegralCurrent (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      WeaklyConvergesOn Tj T → IsIntegerMultiplicity T

end

/-- Coordinate expansion of an `n`-covector on `ℝ^P` in the wedge basis:
`α = ∑_β α(e_{β(0)}, …, e_{β(n-1)}) dx^β` over the increasing multi-indices `β`. -/
theorem Submission.cmb_covector_eq_sum_coord_smul_wedge :
    ∀ (P n : ℕ) (α : Covector (Eucl P) n), α = ∑ β : SimonMultiIndex n P,
      euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) := by
  intro P n α
  classical
  -- `e v = (e_{v 0}, …, e_{v (n - 1)})` for a tuple `v` of coordinate indices.
  set e : (Fin n → Fin P) → Fin n → Eucl P := fun v j => EuclideanSpace.single (v j) 1
  set R : Covector (Eucl P) n := ∑ β : SimonMultiIndex n P,
    euclideanCovectorCoordinate α β • wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) with hR
  -- Kronecker property: `dx^β (e_γ) = δ_{βγ}`.
  have hK : ∀ β γ : SimonMultiIndex n P,
      wedgeCovectors n (fun j => EuclideanSpace.proj (β j)) (e γ) = if β = γ then 1 else 0 := by
    intro β γ
    rw [wedgeCovectors_apply_det]
    split_ifs with hβγ
    · -- the matrix `[δ_{β i, β j}]` is the identity
      subst hβγ
      convert Matrix.det_one (n := Fin n) (R := ℝ)
      ext i j
      simp [e, Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
    · -- some `β i` is not among the `γ j`, so row `i` vanishes
      obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
        by_contra! h
        apply hβγ
        rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
        have hsub : Set.range β ⊆ Set.range γ := by
          rintro _ ⟨i, rfl⟩
          obtain ⟨j, hj⟩ := h i
          exact ⟨j, hj.symm⟩
        refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.finite_range γ)
        rw [Set.ncard_range_of_injective γ.injective, Set.ncard_range_of_injective β.injective]
      exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [e, PiLp.single_apply, hi j]
  -- `R` agrees with `α` on increasing tuples of basis vectors.
  have h1 : ∀ γ : SimonMultiIndex n P, R (e γ) = α (e γ) := by
    intro γ
    rw [hR, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, hK, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  -- `R` agrees with `α` on injective tuples: sort them and use `map_perm`.
  have h2 : ∀ v : Fin n → Fin P, Function.Injective v → R (e v) = α (e v) := by
    intro v hv
    have hsm : StrictMono (v ∘ Tuple.sort v) :=
      (Tuple.monotone_sort v).strictMono_of_injective (hv.comp (Tuple.sort v).injective)
    have hγ := h1 (OrderEmbedding.ofStrictMono _ hsm)
    have heq : e (OrderEmbedding.ofStrictMono _ hsm) = e v ∘ Tuple.sort v := rfl
    rw [heq, ← ContinuousAlternatingMap.coe_toAlternatingMap R,
      ← ContinuousAlternatingMap.coe_toAlternatingMap α, AlternatingMap.map_perm,
      AlternatingMap.map_perm] at hγ
    exact smul_left_cancel _ hγ
  -- Conclude by extensionality on the standard basis.
  symm
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin P) ℝ).toBasis fun v hv => ?_
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap]
  exact h2 v hv
/-- Mass estimate: if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ C` everywhere
(Euclidean covector norm), then `|T(ω)| ≤ B · C`. -/
theorem Submission.cmb_abs_apply_le_of_massOn_le :
    ∀ (P n : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (B C : ℝ),
      0 ≤ B → T.massOn W ≤ ENNReal.ofReal B → tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) →
      |T ω| ≤ B * C := by
  intro P n U W T ω B C hB hM hW hC
  -- Homogeneity of the Euclidean coefficient norm: `|t α| = |t| |α|`.
  have hsmul : ∀ (t : ℝ) (α : Covector (Eucl P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  -- `C ≥ 0`, by evaluating the pointwise bound at `0`.
  have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
  -- For every `c > C`, both `±c⁻¹ ω` are mass-admissible for `W`, hence `|T ω| ≤ B c`.
  have key : ∀ c, C < c → |T ω| ≤ B * c := by
    intro c hc
    have hc0 : 0 < c := hC0.trans_lt hc
    have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * T ω ≤ B := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hW, fun x => ?_⟩
        change covectorEuclideanNorm (s • (ω : DifferentialForm (Eucl P) n) x) ≤ 1
        rw [hsmul, hs, inv_mul_le_iff₀ hc0, mul_one]
        exact (hC x).trans hc.le
      have hle := (T.le_massOn hadm).trans hM
      rw [ENNReal.ofReal_le_ofReal_iff hB] at hle
      have hlin : T (s • ω) = s * T ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at hle
    have h1 := hbound c⁻¹ (abs_of_pos (inv_pos.mpr hc0))
    have h2 := hbound (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc0)])
    have e1 : c * (c⁻¹ * T ω) = T ω := by field_simp
    have e2 : c * (-c⁻¹ * T ω) = -T ω := by field_simp
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left h2 hc0.le
      rw [e2] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h1 hc0.le
      rw [e1] at this
      linarith
  -- Let `c ↓ C`: take `c = C + ε / (B + 1)`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ε / (B + 1) := div_pos hε hB1
  have hBδ : B * (ε / (B + 1)) ≤ ε := by
    calc B * (ε / (B + 1)) ≤ (B + 1) * (ε / (B + 1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε := by field_simp
  have := key (C + ε / (B + 1)) (by linarith)
  calc |T ω| ≤ B * (C + ε / (B + 1)) := this
    _ = B * C + B * (ε / (B + 1)) := by ring
    _ ≤ B * C + ε := by linarith
/-- The `n`-dimensional coordinate box `{x : c_i + a ≤ x_i ≤ c_i + b (i ∈ range α), x_i = c_i
(i ∉ range α)}` in `ℝ^N` has `μHE[n]`-measure `(b - a)^n`.  The map
`ι(y)_i = c_i + ∑_j [α j = i] y_j` is an isometry `ℝⁿ → ℝ^N` carrying the cube `[a, b]ⁿ` onto the
box; `μHE[n]` is invariant under isometries and equals Lebesgue measure on `ℝⁿ`. -/
theorem Submission.isoperimetric_coord_box_measure :
    ∀ (n N : ℕ) (α : SimonMultiIndex n N) (c : Fin N → ℝ) (a b : ℝ), a ≤ b →
      (μHE[n] : Measure (Eucl N)) {x : Eucl N | ∀ i : Fin N,
        (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧ (i ∉ range α → x i = c i)} =
        ENNReal.ofReal ((b - a) ^ n) := by
  intro n N α c a b hab
  classical
  -- The parametrization `ι(y)_i = c_i + ∑_j [α j = i] y_j` of the box.
  set ι : EuclideanSpace ℝ (Fin n) → Eucl N :=
    fun y => WithLp.toLp 2 (fun i => c i + ∑ j, if α j = i then y j else 0) with hι
  have hι_on : ∀ y j, ι y (α j) = c (α j) + y j := by
    intro y j
    simp only [hι, PiLp.toLp_apply, α.inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hι_off : ∀ y i, i ∉ range α → ι y i = c i := by
    intro y i hi
    have hne : ∀ j, α j ≠ i := fun j hj => hi ⟨j, hj⟩
    simp [hι, hne]
  -- `ι` is an isometry: coordinates off `range α` agree, the others reindex along `α`.
  have hiso : Isometry ι := by
    refine Isometry.of_dist_eq fun y y' => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image α)) ?_,
      Finset.sum_image (fun j _ j' _ h => α.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hι_on, hι_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range α := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem α (Finset.mem_univ j))
      rw [hι_off y i hi', hι_off y' i hi', dist_self]
      ring
  -- `ι` maps the cube `[a, b]ⁿ` onto the box, with preimage `y_j = x_{α j} - c_{α j}`.
  have himage : ι '' {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      {x : Eucl N | ∀ i : Fin N, (i ∈ range α → c i + a ≤ x i ∧ x i ≤ c i + b) ∧
        (i ∉ range α → x i = c i)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨?_, hι_off y i⟩
      rintro ⟨j, rfl⟩
      rw [hι_on]
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    · intro hx
      refine ⟨WithLp.toLp 2 (fun j => x (α j) - c (α j)), fun j => ?_, ?_⟩
      · have h := (hx (α j)).1 ⟨j, rfl⟩
        constructor <;> dsimp only <;> linarith [h.1, h.2]
      · ext i
        by_cases hi : i ∈ range α
        · obtain ⟨j, rfl⟩ := hi
          rw [hι_on]
          simp
        · rw [hι_off _ i hi, (hx i).2 hi]
  rw [← himage, hiso.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- The cube is the preimage of `Icc` under the volume-preserving `WithLp.ofLp`.
  have hQ : {y : EuclideanSpace ℝ (Fin n) | ∀ j, a ≤ y j ∧ y j ≤ b} =
      WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => a) (fun _ => b) := by
    ext y
    simp [Pi.le_def, forall_and]
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow (sub_nonneg.2 hab)]
/-- Compact inner approximation: a `μ`-null-measurable `A ⊆ ℝ^P` with `μ ⌞ A` σ-finite is,
up to a `μ`-null set, the union of countably many compact subsets of `A`. -/
theorem Submission.lpf_lli_inner_compact_approx : ∀ (P : ℕ) (μ : Measure (Eucl P)) (A : Set (Eucl P)), NullMeasurableSet A μ → SigmaFinite (μ.restrict A) → ∃ C : ℕ → Set (Eucl P), (∀ k, IsCompact (C k)) ∧ (∀ k, C k ⊆ A) ∧ μ (A \ ⋃ k, C k) = 0 := by
  intro P μ A hA hσ
  -- Step 1: a Borel set `A' ⊆ A` with `μ (A \ A') = 0`.
  obtain ⟨A', hA'A, hA'm, hA'ae⟩ := hA.exists_measurable_subset_ae_eq
  have hAA' : μ (A \ A') = 0 := (ae_eq_set.1 hA'ae).2
  -- Step 2: the Borel pieces `B m = A' ∩ S m`, `S = spanningSets (μ ⌞ A)`, have finite measure.
  set S := spanningSets (μ.restrict A) with hS
  set B : ℕ → Set (Eucl P) := fun m => A' ∩ S m
  have hBA : ∀ m, B m ⊆ A := fun m => inter_subset_left.trans hA'A
  have hBm : ∀ m, MeasurableSet (B m) := fun m => hA'm.inter (measurableSet_spanningSets _ m)
  have hBfin : ∀ m, μ (B m) ≠ ∞ := by
    intro m
    have h : μ.restrict A (B m) = μ (B m) := by
      rw [Measure.restrict_apply (hBm m), inter_eq_left.2 (hBA m)]
    rw [← h]
    exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top _ m)).ne
  -- Step 3: the finite measure `μ ⌞ B m` on `ℝ^P` is regular, so there are compact
  -- `K m j ⊆ B m` with `μ (B m \ K m j) < (j + 1)⁻¹`.
  have hK : ∀ m j : ℕ, ∃ K, K ⊆ B m ∧ IsCompact K ∧ μ (B m \ K) < ((j : ℝ≥0∞) + 1)⁻¹ := by
    intro m j
    have : IsFiniteMeasure (μ.restrict (B m)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hBfin m).lt_top⟩
    have : (μ.restrict (B m)).Regular :=
      Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
    obtain ⟨K, hKB, hKc, hKlt⟩ := (hBm m).exists_isCompact_sdiff_lt (μ := μ.restrict (B m))
      (measure_ne_top _ _) (ε := ((j : ℝ≥0∞) + 1)⁻¹) (by simp)
    refine ⟨K, hKB, hKc, ?_⟩
    rwa [Measure.restrict_apply ((hBm m).diff hKc.measurableSet),
      inter_eq_left.2 sdiff_subset] at hKlt
  choose K hKB hKc hKlt using hK
  -- Step 4: `μ (B m \ ⋃ j, K m j) < (j + 1)⁻¹` for every `j`, hence it vanishes.
  have hnull : ∀ m, μ (B m \ ⋃ j, K m j) = 0 := by
    intro m
    by_contra h
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h
    have h1 : μ (B m \ ⋃ j, K m j) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      (measure_mono (sdiff_subset_sdiff_right (subset_iUnion _ n))).trans_lt (hKlt m n)
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact lt_irrefl _ ((h1.trans_le h2).trans hn)
  -- Steps 5 and 6: re-index `K m j` along `Nat.unpair`; the rest of `A` lies in the null set
  -- `(A \ A') ∪ ⋃ m, (B m \ ⋃ j, K m j)`.
  refine ⟨fun k => K (Nat.unpair k).1 (Nat.unpair k).2, fun k => hKc _ _,
    fun k => (hKB _ _).trans (hBA _), measure_mono_null ?_
      (measure_union_null hAA' (measure_iUnion_null hnull))⟩
  rintro x ⟨hxA, hxC⟩
  by_cases hx : x ∈ A'
  · have hxS : x ∈ ⋃ m, S m := by rw [hS, iUnion_spanningSets]; exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxS
    refine Or.inr (mem_iUnion.2 ⟨m, ⟨hx, hm⟩, fun hxK => hxC ?_⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.1 hxK
    exact mem_iUnion.2 ⟨Nat.pair m j, by simpa only [Nat.unpair_pair] using hj⟩
  · exact Or.inl ⟨hxA, hx⟩
/-- Exhaustion of an open `U ⊆ ℝ^P` by open sets `W i ⊂⊂ U` such that every compact `K ⊆ U`
lies in some `W i`: `W i = {x : |x| < i, (i + 1)⁻¹ < infEDist x (ℝ^P ∖ U)}`. -/
theorem Submission.cmb_exists_compactly_contained_exhaustion :
    ∀ (P : ℕ) (U : Set (Eucl P)), IsOpen U → ∃ W : ℕ → Set (Eucl P),
      (∀ i, CompactlyContainedOpen (W i) U) ∧
      ∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ i, K ⊆ W i := by
  intro P U hU
  -- `d x = infEDist x Uᶜ` is continuous and positive exactly on `U`.
  have hd : Continuous fun x : Eucl P => infEDist x Uᶜ := continuous_infEDist
  have hpos : ∀ x ∈ U, 0 < infEDist x Uᶜ := fun x hx => by
    rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq, notMem_compl_iff]
    exact hx
  refine ⟨fun i => {x | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}, fun i => ?_,
    fun K hK hKU => ?_⟩
  · -- `closure (W i) ⊆ closedBall 0 i ∩ {(i + 1)⁻¹ ≤ d}`, a compact subset of `U`.
    have hcl : closure ({x : Eucl P | ‖x‖ < i} ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ}) ⊆
        closedBall 0 i ∩ {x | ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ} :=
      closure_minimal (fun x hx => ⟨mem_closedBall_zero_iff.2 hx.1.le,
        show ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ from hx.2.le⟩)
        (isClosed_closedBall.inter (isClosed_le continuous_const hd))
    refine ⟨(isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd),
      (isCompact_closedBall 0 _).of_isClosed_subset isClosed_closure (hcl.trans inter_subset_left),
      fun x hx => ?_⟩
    by_contra hxU
    have h : ((i : ℝ≥0∞) + 1)⁻¹ ≤ infEDist x Uᶜ := (hcl hx).2
    rw [infEDist_zero_of_mem hxU, nonpos_iff_eq_zero, ENNReal.inv_eq_zero] at h
    exact ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top i, ENNReal.one_ne_top⟩ h
  · -- A compact `K ⊆ U` is bounded and `d` has a positive minimum on it.
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, empty_subset _⟩
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    obtain ⟨i₁, hi₁⟩ := exists_nat_gt R
    obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hd.continuousOn
    obtain ⟨i₂, hi₂⟩ := ENNReal.exists_inv_nat_lt (hpos x₀ (hKU hx₀K)).ne'
    refine ⟨max i₁ i₂, fun x hx => ⟨?_, ?_⟩⟩
    · show ‖x‖ < ((max i₁ i₂ : ℕ) : ℝ)
      calc ‖x‖ ≤ R := hR x hx
        _ < i₁ := hi₁
        _ ≤ (max i₁ i₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
    · show (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ < infEDist x Uᶜ
      calc (((max i₁ i₂ : ℕ) : ℝ≥0∞) + 1)⁻¹ ≤ (i₂ : ℝ≥0∞)⁻¹ :=
            ENNReal.inv_le_inv.2 (by exact_mod_cast (le_max_right i₁ i₂).trans (Nat.le_succ _))
        _ < infEDist x₀ Uᶜ := hi₂
        _ ≤ infEDist x Uᶜ := isMinOn_iff.1 hx₀ x hx
/-- Simon Ch. 6, proof of Theorem 2.34 (p. 142): `D^β (φ ∗ g) = (D^β φ) ∗ g`, so every derivative
of a mollification is bounded by the `L¹` norm of the mollified function.  By induction on `q`,
for a vector-valued smooth compactly supported kernel `f` and a bilinear `L` with
`‖L u t‖ ≤ B ‖u‖ |t|`: `‖D^q (f ∗_L g)(x)‖ ≤ B · sup ‖D^q f‖ · ∫ |g|`, using
`D (f ∗_L g) = (D f) ∗_{L.precompL} g` and `‖D^{q+1} h‖ = ‖D^q (D h)‖`. -/
theorem Submission.constancy_mollifier_iteratedFDeriv_norm_le_integral :
    ∀ (n : ℕ) (φ : Eucl n → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      ∀ q : ℕ, ∃ C : ℝ, ∀ g : Eucl n → ℝ, Integrable g volume → ∀ x : Eucl n,
        ‖iteratedFDeriv ℝ q (convolution φ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤
          C * ∫ y, |g y| ∂volume := by
  intro n φ hφ hφc q
  -- The generalized claim `P(k)`, by induction on `k`.
  have key : ∀ (k : ℕ) (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] ℝ →L[ℝ] F) (B : ℝ), 0 ≤ B →
      (∀ u t, ‖L u t‖ ≤ B * ‖u‖ * |t|) → ∀ f : Eucl n → E,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∀ S : ℝ,
      (∀ t, ‖iteratedFDeriv ℝ k f t‖ ≤ S) → ∀ g : Eucl n → ℝ, Integrable g volume →
      ∀ x, ‖iteratedFDeriv ℝ k (convolution f g L volume) x‖ ≤ B * S * ∫ y, |g y| ∂volume := by
    intro k
    induction k with
    | zero =>
      intro E F _ _ _ _ L B hB hL f hf hfc S hS g hg x
      rw [norm_iteratedFDeriv_zero, convolution_def]
      have hS' : ∀ t, ‖f t‖ ≤ S := fun t => by simpa using hS t
      calc ‖∫ t, L (f t) (g (x - t)) ∂volume‖
          ≤ ∫ t, B * S * |g (x - t)| ∂volume := by
            apply norm_integral_le_of_norm_le
            · exact (hg.comp_sub_left x).abs.const_mul (B * S)
            · refine Filter.Eventually.of_forall fun t => ?_
              calc ‖L (f t) (g (x - t))‖ ≤ B * ‖f t‖ * |g (x - t)| := hL _ _
                _ ≤ B * S * |g (x - t)| := by gcongr; exact hS' t
        _ = B * S * ∫ y, |g y| ∂volume := by
            rw [integral_const_mul]
            congr 1
            exact integral_sub_left_eq_self (fun y => |g y|) volume x
    | succ k ih =>
      intro E F _ _ _ _ L B hB hL f hf hfc S hS g hg x
      have hderiv : fderiv ℝ (convolution f g L volume) =
          convolution (fderiv ℝ f) g (ContinuousLinearMap.precompL (Eucl n) L) volume := by
        funext y
        exact (hfc.hasFDerivAt_convolution_left L (hf.of_le (mod_cast le_top))
          hg.locallyIntegrable y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hderiv]
      refine ih (Eucl n →L[ℝ] E) (Eucl n →L[ℝ] F) (ContinuousLinearMap.precompL (Eucl n) L) B hB
        ?_ (fderiv ℝ f) (contDiff_infty_iff_fderiv.mp hf).2 (hfc.fderiv ℝ) S ?_ g hg x
      · intro u t
        refine ContinuousLinearMap.opNorm_le_bound _
          (mul_nonneg (mul_nonneg hB (norm_nonneg u)) (abs_nonneg t)) fun v => ?_
        rw [ContinuousLinearMap.precompL_apply]
        calc ‖L (u v) t‖ ≤ B * ‖u v‖ * |t| := hL _ _
          _ ≤ B * (‖u‖ * ‖v‖) * |t| := by gcongr; exact u.le_opNorm v
          _ = B * ‖u‖ * |t| * ‖v‖ := by ring
      · intro t
        rw [norm_iteratedFDeriv_fderiv]
        exact hS t
  obtain ⟨S, -, hS⟩ := hφc.exists_bound_iteratedFDeriv hφ q
  refine ⟨1 * S, fun g hg x => key q ℝ ℝ (ContinuousLinearMap.lsmul ℝ ℝ) 1 zero_le_one ?_ φ hφ
    hφc S (fun t => hS q le_rfl t) g hg x⟩
  intro u t
  simp [Real.norm_eq_abs]
/-- Diagonal extraction from nested infinite index sets (Simon Ch. 6, proof of 7.2): with
`J 0 = ℕ` and infinite `J (r + 1) ⊆ J r` on which `Q r` holds for all pairs, an increasing
choice `φ r ∈ J (r + 1)` puts both `φ r` and `φ (r + 1)` in `J (r + 1)`. -/
theorem Submission.fiw_fcl_nested_subseq :
    ∀ (Q : ℕ → ℕ → ℕ → Prop),
      (∀ r : ℕ, ∀ J : Set ℕ, J.Infinite → ∃ J' ⊆ J, J'.Infinite ∧ ∀ i ∈ J', ∀ j ∈ J', Q r i j) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r : ℕ, Q r (φ r) (φ (r + 1)) := by
  intro Q h
  choose F hFsub hFinf hFQ using h
  -- The nested infinite sets: `J 0 = ℕ` and `J (r + 1) = F r (J r)`.
  let J : ℕ → {A : Set ℕ // A.Infinite} := fun r =>
    Nat.rec (motive := fun _ => {A : Set ℕ // A.Infinite}) ⟨Set.univ, Set.infinite_univ⟩
      (fun r A => ⟨F r A.1 A.2, hFinf r A.1 A.2⟩) r
  -- `g r m ∈ J (r + 1)` with `m < g r m`.
  choose g hgJ hgm using fun r => (J (r + 1)).2.exists_gt
  -- `φ 0 = g 0 0` and `φ (r + 1) = g (r + 1) (φ r)`, so `φ r ∈ J (r + 1)` and `φ r < φ (r + 1)`.
  let φ : ℕ → ℕ := fun r => Nat.rec (motive := fun _ => ℕ) (g 0 0) (fun r m => g (r + 1) m) r
  have hφJ : ∀ r, φ r ∈ (J (r + 1)).1 := by
    intro r
    cases r with
    | zero => exact hgJ 0 0
    | succ s => exact hgJ (s + 1) (φ s)
  refine ⟨φ, strictMono_nat_of_lt_succ fun r => hgm (r + 1) (φ r), fun r => ?_⟩
  -- `φ r ∈ J (r + 1)` and `φ (r + 1) ∈ J (r + 2) ⊆ J (r + 1)`, where `J (r + 1) = F r (J r)`.
  exact hFQ r (J r).1 (J r).2 (φ r) (hφJ r) (φ (r + 1))
    (hFsub (r + 1) (J (r + 1)).1 (J (r + 1)).2 (hφJ (r + 1)))
/-- **Step 4 of the uniqueness of the representation (2.7), Simon Ch. 6 (p. 136).**  If `g₁ μ₁`
and `g₂ μ₂` (`gᵢ` `μᵢ`-integrable) agree on smooth compactly supported functions `φ` with
`tsupport φ ⊆ O`, `O` open, they agree on continuous compactly supported functions `φ` with
`tsupport φ ⊆ O`.  The approximants are `χ (ψ ⋆ φ)`: `ψ ⋆ φ` is the convolution of `φ` with a
normalized smooth bump `ψ` supported in a ball whose radius is a uniform-continuity modulus of
`φ`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to `1` exactly on `tsupport φ`,
whose support `V` has compact closure in `O`.  Dominated convergence passes to the limit. -/
theorem Submission.slicing_ru_smooth_to_continuous : ∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ → Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ φ : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂) → ∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂ := by
  intro P μ₁ μ₂ g₁ g₂ hg₁ hg₂ O hO hsmooth φ hφ hφc hφO
  -- Step 1: for every `ε > 0` there is a smooth `η` with compact support, `tsupport η ⊆ O` and
  -- `|η - φ| ≤ ε`.
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ η : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧
      HasCompactSupport η ∧ tsupport η ⊆ O ∧ ∀ x, dist (η x) (φ x) ≤ ε := by
    intro ε hε
    -- An open `V` with `tsupport φ ⊆ V` and `closure V ⊆ O` compact, and a smooth cutoff
    -- `χ : ℝ^P → [0, 1]` with `support χ = V` and `χ = 1` exactly on `tsupport φ`.
    obtain ⟨V, hVo, hKV, hVO, hVc⟩ :=
      exists_open_between_and_isCompact_closure hφc.isCompact hO hφO
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo (isClosed_tsupport φ) hKV
    -- Mollification: `φ` is uniformly continuous with modulus `δ` at accuracy `ε`; `ψ` is a smooth
    -- bump `≥ 0` with `∫ ψ = 1` and `support ψ ⊆ ball 0 δ`, so `f = ψ ⋆ φ` is smooth and
    -- `dist (f x) (φ x) ≤ ε`.
    obtain ⟨δ, hδ, hφδ⟩ :=
      Metric.uniformContinuous_iff.mp (hφc.uniformContinuous_of_continuous hφ) ε hε
    obtain ⟨ψ₀, hψ₀s, hψ₀c, hψ₀d, hψ₀r, hψ₀0⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) (ball_mem_nhds (0 : Eucl P) hδ)
    have hψ₀nn : ∀ y, 0 ≤ ψ₀ y := fun y => (hψ₀r (mem_range_self y)).1
    have hψ₀int : 0 < ∫ y, ψ₀ y :=
      hψ₀d.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψ₀c (fun y => hψ₀nn y)
        (hψ₀0.symm ▸ one_ne_zero : ψ₀ 0 ≠ 0)
    set ψ : Eucl P → ℝ := fun y => (∫ z, ψ₀ z)⁻¹ * ψ₀ y with hψ_def
    have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := contDiff_const.mul hψ₀d
    have hψc : HasCompactSupport ψ := hψ₀c.mul_left
    have hψnn : ∀ y, 0 ≤ ψ y := fun y => mul_nonneg (inv_nonneg.mpr hψ₀int.le) (hψ₀nn y)
    have hψs : Function.support ψ ⊆ ball 0 δ :=
      (Function.support_mul_subset_right _ _).trans ((subset_tsupport ψ₀).trans hψ₀s)
    have hψ1 : ∫ y, ψ y = 1 := by
      rw [hψ_def, integral_const_mul, inv_mul_cancel₀ hψ₀int.ne']
    obtain ⟨f, hf, hfd⟩ : ∃ f : Eucl P → ℝ,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ x, dist (f x) (φ x) ≤ ε :=
      ⟨convolution ψ φ (ContinuousLinearMap.lsmul ℝ ℝ) volume,
        hψc.contDiff_convolution_left _ hψd hφ.locallyIntegrable,
        fun x => dist_convolution_le hε.le hψs hψnn hψ1 hφ.aestronglyMeasurable
          fun y hy => (hφδ (mem_ball.mp hy)).le⟩
    -- `η = χ f` is smooth with `tsupport η ⊆ closure V ⊆ O`; on `tsupport φ`, `η = f`, and off
    -- it, `φ = 0` and `0 ≤ χ ≤ 1`.
    have hηs : tsupport (fun x => χ x * f x) ⊆ closure V := by
      refine tsupport_mul_subset_left.trans ?_
      rw [tsupport, hχs]
    refine ⟨fun x => χ x * f x, hχ.mul hf, hVc.of_isClosed_subset (isClosed_tsupport _) hηs,
      hηs.trans hVO, fun x => ?_⟩
    show dist (χ x * f x) (φ x) ≤ ε
    by_cases hx : x ∈ tsupport φ
    · rw [(hχ1 x).1 hx, one_mul]
      exact hfd x
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hχx := hχr (mem_range_self x)
      have hfx : |f x| ≤ ε := by simpa [h0, Real.dist_eq] using hfd x
      rw [h0, Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hχx.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) hχx.2).trans hfx
  -- Step 2: approximants `η n` with `|η n - φ| ≤ 1 / (n + 1)`, and a bound `|φ| ≤ M`.
  choose η hηd hηc hηO hηφ using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  -- Step 3: dominated convergence with bound `(M + 1) |g|`: `∫ η n g dμ → ∫ φ g dμ`.
  have hlim : ∀ (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ →
      Tendsto (fun n => ∫ x, η n x * g x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)) := by
    intro μ g hg
    refine tendsto_integral_of_dominated_convergence (fun x => (M + 1) * ‖g x‖)
      (fun n => (hηd n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (hg.norm.const_mul _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 : dist (η n x) (φ x) ≤ 1 := (hηφ n x).trans <| by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc ‖η n x‖ ≤ ‖φ x‖ + ‖η n x - φ x‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ M + 1 := add_le_add (hM x) (by rwa [← dist_eq_norm])
    · refine Tendsto.mul_const _ (tendsto_iff_dist_tendsto_zero.mpr ?_)
      exact squeeze_zero (fun n => dist_nonneg) (fun n => hηφ n x)
        tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 4: the two sequences coincide termwise by the smooth hypothesis.
  exact tendsto_nhds_unique
    ((hlim μ₁ g₁ hg₁).congr fun n => hsmooth _ (hηd n) (hηc n) (hηO n)) (hlim μ₂ g₂ hg₂)
/-- Simon Ch. 6, (2.7)–(2.9): uniqueness step for representations of currents.  If `g₁ μ₁` and
`g₂ μ₂` agree on continuous compactly supported functions with support in the open set `O`, then
they agree on bounded Borel functions vanishing off `O`.  With `g⁺ = max g 0`, `g⁻ = max (-g) 0`,
the finite measures `m₁ = g₁⁺ μ₁ + g₂⁻ μ₂`, `m₂ = g₁⁻ μ₁ + g₂⁺ μ₂` satisfy
`∫ f dm₁ - ∫ f dm₂ = ∫ f g₁ dμ₁ - ∫ f g₂ dμ₂` for bounded measurable `f`, so they agree on
`C_c(O)`.  Urysohn functions and inner regularity give `m₁ V = m₂ V` for open `V ⊆ O`; by the
π–λ theorem `m₁ ⌞ O = m₂ ⌞ O`, and the claim follows. -/
theorem Submission.slicing_ru_continuous_to_bounded : ∀ (P : ℕ) (μ₁ μ₂ : Measure (Eucl P)) (g₁ g₂ : Eucl P → ℝ), Integrable g₁ μ₁ → Integrable g₂ μ₂ → ∀ O : Set (Eucl P), IsOpen O → (∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → ∫ x, φ x * g₁ x ∂μ₁ = ∫ x, φ x * g₂ x ∂μ₂) → ∀ h : Eucl P → ℝ, Measurable h → (∃ C : ℝ, ∀ x, |h x| ≤ C) → (∀ x, x ∉ O → h x = 0) → ∫ x, h x * g₁ x ∂μ₁ = ∫ x, h x * g₂ x ∂μ₂ := by
  intro P μ₁ μ₂ g₁ g₂ hg₁ hg₂ O hO H h hh ⟨C, hC⟩ hhO
  -- Step 1: `∫ f d(g⁺ μ) - ∫ f d(g⁻ μ) = ∫ f g dμ` for bounded measurable `f`.
  have split : ∀ (μ : Measure (Eucl P)) (g : Eucl P → ℝ), Integrable g μ →
      ∀ f : Eucl P → ℝ, Measurable f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (g x)) -
          ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (-g x)) = ∫ x, f x * g x ∂μ := by
    intro μ g hg f hf D hD
    have hb : ∀ {ρ : Measure (Eucl P)}, ∀ᵐ x ∂ρ, ‖f x‖ ≤ D :=
      Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hD x
    have hmax : ∀ t : ℝ, ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
      intro t
      rcases le_total t 0 with ht | ht
      · rw [max_eq_right ht, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos ht]
      · rw [max_eq_left ht]
    have hpos : ∀ u : Eucl P → ℝ, Integrable u μ →
        ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) = ∫ x, max (u x) 0 * f x ∂μ := by
      intro u hu
      have : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (u x)) :=
        isFiniteMeasure_withDensity_ofReal hu.2
      have hρ : AEMeasurable (fun x => ENNReal.ofReal (u x)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable hu.aemeasurable
      have e₁ : ∫⁻ x, ENNReal.ofReal (f x) ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) =
          ∫⁻ x, ENNReal.ofReal (max (u x) 0 * f x) ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul₀ hρ hf.ennreal_ofReal.aemeasurable]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ENNReal.ofReal_mul (le_max_right _ _), hmax]
      have e₂ : ∫⁻ x, ENNReal.ofReal (-f x) ∂(μ.withDensity fun x => ENNReal.ofReal (u x)) =
          ∫⁻ x, ENNReal.ofReal (-(max (u x) 0 * f x)) ∂μ := by
        have hnf : AEMeasurable (fun x => ENNReal.ofReal (-f x)) μ :=
          hf.neg.ennreal_ofReal.aemeasurable
        rw [lintegral_withDensity_eq_lintegral_mul₀ hρ hnf]
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, ← mul_neg, ENNReal.ofReal_mul (le_max_right _ _), hmax]
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
          (Integrable.of_bound hf.aestronglyMeasurable D hb),
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part
          (hu.pos_part.mul_bdd hf.aestronglyMeasurable hb), e₁, e₂]
    rw [hpos g hg, hpos (fun x => -g x) hg.neg,
      ← integral_sub (hg.pos_part.mul_bdd hf.aestronglyMeasurable hb)
        (hg.neg_part.mul_bdd hf.aestronglyMeasurable hb)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := max_zero_sub_max_neg_zero_eq_self (g x)
    simp only
    linear_combination (f x) * this
  -- Step 2: the finite measures `m₁ = g₁⁺ μ₁ + g₂⁻ μ₂` and `m₂ = g₁⁻ μ₁ + g₂⁺ μ₂`.
  set m₁ : Measure (Eucl P) := (μ₁.withDensity fun x => ENNReal.ofReal (g₁ x)) +
    μ₂.withDensity fun x => ENNReal.ofReal (-g₂ x) with hm₁
  set m₂ : Measure (Eucl P) := (μ₁.withDensity fun x => ENNReal.ofReal (-g₁ x)) +
    μ₂.withDensity fun x => ENNReal.ofReal (g₂ x) with hm₂
  have : IsFiniteMeasure (μ₁.withDensity fun x => ENNReal.ofReal (g₁ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₁.2
  have : IsFiniteMeasure (μ₁.withDensity fun x => ENNReal.ofReal (-g₁ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₁.neg.2
  have : IsFiniteMeasure (μ₂.withDensity fun x => ENNReal.ofReal (g₂ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₂.2
  have : IsFiniteMeasure (μ₂.withDensity fun x => ENNReal.ofReal (-g₂ x)) :=
    isFiniteMeasure_withDensity_ofReal hg₂.neg.2
  have : IsFiniteMeasure m₁ := by rw [hm₁]; infer_instance
  have : IsFiniteMeasure m₂ := by rw [hm₂]; infer_instance
  -- (★) `∫ f dm₁ - ∫ f dm₂ = ∫ f g₁ dμ₁ - ∫ f g₂ dμ₂` for bounded measurable `f`.
  have star : ∀ f : Eucl P → ℝ, Measurable f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
      ∫ x, f x ∂m₁ - ∫ x, f x ∂m₂ = ∫ x, f x * g₁ x ∂μ₁ - ∫ x, f x * g₂ x ∂μ₂ := by
    intro f hf D hD
    have hb : ∀ {ρ : Measure (Eucl P)}, ∀ᵐ x ∂ρ, ‖f x‖ ≤ D :=
      Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hD x
    have i : ∀ (ρ : Measure (Eucl P)) [IsFiniteMeasure ρ], Integrable f ρ :=
      fun ρ _ => Integrable.of_bound hf.aestronglyMeasurable D hb
    rw [hm₁, hm₂, integral_add_measure (i _) (i _), integral_add_measure (i _) (i _),
      ← split μ₁ g₁ hg₁ f hf D hD, ← split μ₂ g₂ hg₂ f hf D hD]
    ring
  -- Step 3: `m₁` and `m₂` agree on `C_c(O)`.
  have agree : ∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O →
      ∫ x, φ x ∂m₁ = ∫ x, φ x ∂m₂ := by
    intro φ hφ hφc hφO
    obtain ⟨D, hD⟩ := hφ.bounded_above_of_compact_support hφc
    have := star φ hφ.measurable D fun x => by simpa [Real.norm_eq_abs] using hD x
    rw [H φ hφ hφc hφO, sub_self, sub_eq_zero] at this
    exact this
  -- Step 4: finite measures agreeing on `C_c(O)` agree on open subsets of `O`
  -- (inner regularity and Urysohn's lemma).
  have le_of_agree : ∀ (ρ₁ ρ₂ : Measure (Eucl P)) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      (∀ φ : Eucl P → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O →
        ∫ x, φ x ∂ρ₁ = ∫ x, φ x ∂ρ₂) →
      ∀ V : Set (Eucl P), IsOpen V → V ⊆ O → ρ₁ V ≤ ρ₂ V := by
    intro ρ₁ ρ₂ _ _ hρ V hV hVO
    rw [hV.measure_eq_iSup_isCompact ρ₁]
    refine iSup_le fun K => iSup_le fun hKV => iSup_le fun hK => ?_
    obtain ⟨φ, hφK, hφc, hφV, hφ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hV hKV
    have hφi : ∀ (ρ : Measure (Eucl P)) [IsFiniteMeasure ρ], Integrable φ ρ := by
      intro ρ _
      refine Integrable.of_bound φ.continuous.aestronglyMeasurable 1
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hφ01 x).1], (hφ01 x).2⟩
    have h₁ : ρ₁.real K ≤ ∫ x, φ x ∂ρ₁ := by
      rw [← integral_indicator_one hK.measurableSet]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator hK.measurableSet) (hφi ρ₁)
        fun x => ?_
      by_cases hx : x ∈ K
      · simp [Set.indicator_of_mem hx, hφK hx]
      · simp [Set.indicator_of_notMem hx, (hφ01 x).1]
    have h₂ : ∫ x, φ x ∂ρ₂ ≤ ρ₂.real V := by
      rw [← integral_indicator_one hV.measurableSet]
      refine integral_mono (hφi ρ₂) ((integrable_const (1 : ℝ)).indicator hV.measurableSet)
        fun x => ?_
      by_cases hx : x ∈ V
      · simp [Set.indicator_of_mem hx, (hφ01 x).2]
      · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' => hx (hφV hx')
        simp [Set.indicator_of_notMem hx, this]
    have := h₁.trans ((hρ φ φ.continuous hφc (hφV.trans hVO)).le.trans h₂)
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  have eq_open : ∀ V : Set (Eucl P), IsOpen V → V ⊆ O → m₁ V = m₂ V := fun V hV hVO =>
    le_antisymm (le_of_agree m₁ m₂ agree V hV hVO)
      (le_of_agree m₂ m₁ (fun φ hφ hφc hφO => (agree φ hφ hφc hφO).symm) V hV hVO)
  -- Step 5: π–λ: `m₁ ⌞ O = m₂ ⌞ O`.
  have hrestr : m₁.restrict O = m₂.restrict O := by
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen
      (fun s hs => ?_) ?_
    · have hs' : IsOpen s := hs
      rw [Measure.restrict_apply hs'.measurableSet, Measure.restrict_apply hs'.measurableSet]
      exact eq_open _ (hs'.inter hO) inter_subset_right
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact eq_open O hO subset_rfl
  -- Step 6: conclusion.
  have hint : ∫ x, h x ∂m₁ = ∫ x, h x ∂m₂ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := m₁) hhO,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := m₂) hhO, hrestr]
  have := star h hh C hC
  rw [hint, sub_self] at this
  linarith
/-- Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the
proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to
`Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets, `V ∋ x` open.  If `B_δ(x) ⊆ V` and
`f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off
`W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and
`(M', θ')` agree for all small `r`. -/
theorem Submission.br_weightedTangent_congr :
    ∀ (P k : ℕ) (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P) (V : Set (Eucl P)),
      IsOpen V → x ∈ V → (μHE[k] : Measure (Eucl P)) (symmDiff M M' ∩ V) = 0 →
      (∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (M ∩ V)), θ y = θ' y) → θ x = θ' x →
      ∀ L : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x L →
        HasWeightedApproximateTangentSpaceAt k M' θ' x L := by
  open Poincare.SimonGMT.Chapter03 (blowUpMap) in
  intro P k M M' θ θ' x V hV hxV hMM' hθθ' hθx L hL
  -- `η_r(y) = r⁻¹ (y - x)` maps `Hᵏ`-null sets to `Hᵏ`-null sets: `Hᵏ(η_r Z) = r⁻ᵏ Hᵏ(Z)`.
  have hnull : ∀ r : ℝ, r ≠ 0 → ∀ Z : Set (Eucl P), (μHE[k] : Measure (Eucl P)) Z = 0 →
      (μHE[k] : Measure (Eucl P)) (blowUpMap x r '' Z) = 0 := by
    open scoped Pointwise in
    intro r hr Z hZ
    have himage : blowUpMap x r '' Z = r⁻¹ • (IsometryEquiv.subRight x '' Z) := by
      rw [← Set.image_smul, Set.image_image]
      rfl
    rw [himage, Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero hr),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image, hZ, smul_zero]
  -- `y ↦ x + r • y` inverts `η_r`.
  have hinv : ∀ r : ℝ, r ≠ 0 → ∀ z : Eucl P, x + r • blowUpMap x r z = z := by
    intro r hr z
    simp only [blowUpMap, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  -- A measurable `N ⊇ {θ ≠ θ'}` with `Hᵏ(N ∩ M ∩ V) = 0`.
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hθθ')
  rw [Measure.restrict_apply hNmeas] at hN0
  refine ⟨hL.1, fun f => ?_⟩
  rw [← hθx]
  refine (hL.2 f).congr' ?_
  -- `f = 0` off `B_R(0)` and `B_δ(x) ⊆ V`; the blow-up integrals agree for `0 < r < δ / R`.
  obtain ⟨R, hR, hfR⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV x hxV
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  have hcont : Continuous fun y : Eucl P => x + r • y :=
    continuous_const.add (continuous_const_smul r)
  -- `W = η_r(V)` is open and the integrands `f(y) g(x + r y)` vanish off `W`.
  set W : Set (Eucl P) := (fun y => x + r • y) ⁻¹' V with hW
  have hWmeas : MeasurableSet W := (hV.preimage hcont).measurableSet
  have hvan : ∀ g : Eucl P → ℝ, ∀ y, y ∉ W → f y * g (x + r • y) = 0 := by
    intro g y hy
    have hfy : f y = 0 := by
      apply hfR
      have h1 : x + r • y ∉ ball x δ := fun h => hy (hδV h)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr0, not_lt] at h1
      rw [lt_div_iff₀ hR] at hrR
      exact le_of_lt (lt_of_mul_lt_mul_left (hrR.trans_le h1) hr0.le)
    rw [hfy, zero_mul]
  -- Cutting by `W`: `∫_{η_r(S)} = ∫_{W ∩ η_r(S)}`.
  have hcut : ∀ (S : Set (Eucl P)) (g : Eucl P → ℝ),
      ∫ y in blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) =
        ∫ y in W ∩ blowUpMap x r '' S, f y * g (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
    intro S g
    rw [← Measure.restrict_restrict hWmeas,
      setIntegral_eq_integral_of_forall_compl_eq_zero (hvan g)]
  -- `W ∩ η_r(M) = W ∩ η_r(M')` up to the null set `η_r((M ∆ M') ∩ V)`.
  have hset : W ∩ blowUpMap x r '' M =ᵐ[(μHE[k] : Measure (Eucl P))] W ∩ blowUpMap x r '' M' := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inl ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
    · refine measure_mono_null ?_ (hnull r hr0.ne' _ hMM')
      rintro y ⟨⟨hyW, z, hzM, rfl⟩, hy⟩
      refine ⟨z, ⟨Or.inr ⟨hzM, fun hzM' => hy ⟨hyW, z, hzM', rfl⟩⟩, ?_⟩, rfl⟩
      simpa [hW, hinv r hr0.ne' z] using hyW
  -- `θ(x + r y) = θ'(x + r y)` a.e. on `W ∩ η_r(M)`, off the null set `η_r(N ∩ M ∩ V)`.
  have hae : ∀ᵐ y ∂((μHE[k] : Measure (Eucl P)).restrict (W ∩ blowUpMap x r '' M)),
      f y * θ (x + r • y) = f y * θ' (x + r • y) := by
    have hN'meas : MeasurableSet ((fun y => x + r • y) ⁻¹' N) :=
      hNmeas.preimage hcont.measurable
    rw [ae_iff]
    refine measure_mono_null (t := (fun y => x + r • y) ⁻¹' N) ?_ ?_
    · intro y hy
      by_contra hyN
      apply hy
      have hθy : θ (x + r • y) = θ' (x + r • y) := by
        by_contra hne
        exact hyN (hNsub hne)
      rw [hθy]
    · rw [Measure.restrict_apply hN'meas]
      refine measure_mono_null ?_ (hnull r hr0.ne' _ hN0)
      rintro y ⟨hyN, hyW, z, hzM, rfl⟩
      refine ⟨z, ⟨?_, hzM, ?_⟩, rfl⟩
      · simpa [hinv r hr0.ne' z] using hyN
      · simpa [hW, hinv r hr0.ne' z] using hyW
  calc ∫ y in blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P))
      = ∫ y in W ∩ blowUpMap x r '' M, f y * θ (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        hcut M θ
    _ = ∫ y in W ∩ blowUpMap x r '' M, f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        integral_congr_ae hae
    _ = ∫ y in W ∩ blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) := by
        rw [Measure.restrict_congr_set hset]
    _ = ∫ y in blowUpMap x r '' M', f y * θ' (x + r • y) ∂(μHE[k] : Measure (Eucl P)) :=
        (hcut M' θ').symm
/-- **Simple `n`-vectors (step (P1) of Simon Ch. 6, Lemma 3.9).**  The operator norm of
`v₁ ∧ ⋯ ∧ vₙ = simpleNVector v` is the square root of the Gram determinant `det (⟪vᵢ, vⱼ⟫)`, and a
change of frame `τ ↦ Bτ` multiplies `simpleNVector τ` by `det B`.  The second identity is the
uniqueness of alternating forms on `ℝⁿ` (`AlternatingMap.eq_smul_basis_det`).  A dependent `v`
makes both sides of the first vanish.  An independent `v` is `Bτ` for an orthonormal basis `τ` of
`span v`, so `G(v) = B Bᵀ`; `|α τ| ≤ ‖α‖` and the covector `u ↦ det (⟪τᵢ, uⱼ⟫)` (norm `≤ 1` by
Hadamard's and Bessel's inequalities, value `1` at `τ`) give `‖simpleNVector v‖ = |det B|`. -/
theorem Submission.lpf_simple_nvector_algebra : (∀ (P n : ℕ) (v : Fin n → Eucl P), ‖simpleNVector v‖ ^ 2 = (Matrix.of fun i j => inner ℝ (v i) (v j)).det) ∧ ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P), simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
  -- Change of frame: `α(Bτ) = det B · α(τ)` for every `n`-covector `α`, since
  -- `B ↦ α(Bτ)` is alternating in the rows of `B` (`AlternatingMap.eq_smul_basis_det`).
  have hframe : ∀ (P n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (τ : Fin n → Eucl P),
      simpleNVector (fun i => ∑ j, B i j • τ j) = B.det • simpleNVector τ := by
    intro P n B τ
    ext α
    simp only [simpleNVector_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    set f : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ :=
      α.toAlternatingMap.compLinearMap (Fintype.linearCombination ℝ τ) with hf
    have h1 : f (fun i j => B i j) = α (fun i => ∑ j, B i j • τ j) := by
      simp [hf, Fintype.linearCombination_apply]
    have h2 : f (Pi.basisFun ℝ (Fin n)) = α τ := by
      simp [hf, Fintype.linearCombination_apply_single]
    rw [← h1, AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) f,
      AlternatingMap.smul_apply, h2, Pi.basisFun_det, smul_eq_mul, mul_comm]
    rfl
  refine ⟨fun P n v => ?_, hframe⟩
  by_cases hv : LinearIndependent ℝ v
  · -- Independent family: `v = Bτ` for an orthonormal basis `τ` of `W = span v`,
    -- `B i j = ⟪v i, τ j⟫`, so `G(v) = B Bᵀ` and `simpleNVector v = det B • simpleNVector τ`.
    set W := Submodule.span ℝ (Set.range v) with hW_def
    have hW : Module.finrank ℝ W = n := by rw [finrank_span_eq_card hv, Fintype.card_fin]
    set b : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
    set τ : Fin n → Eucl P := fun j => (b j : Eucl P) with hτ_def
    have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hvW : ∀ i, v i ∈ W := fun i => Submodule.subset_span (Set.mem_range_self i)
    set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => inner ℝ (v i) (τ j) with hB_def
    have hvB : (fun i => ∑ j, B i j • τ j) = v := by
      funext i
      have h := congrArg Subtype.val (b.sum_repr' ⟨v i, hvW i⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
      simpa [hB_def, hτ_def, real_inner_comm] using h
    have hgram : (Matrix.of fun i j => inner ℝ (v i) (v j)) = B * B.transpose := by
      ext i k
      have h := b.sum_inner_mul_inner ⟨v i, hvW i⟩ ⟨v k, hvW k⟩
      simp only [Submodule.coe_inner] at h
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hB_def]
      rw [← h]
      simp [hτ_def, real_inner_comm]
    have hsv : ∀ α : Covector (Eucl P) n, simpleNVector v α = B.det * α τ := by
      intro α
      rw [← hvB, hframe]
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, simpleNVector_apply]
    -- Upper bound: `|α τ| ≤ ‖α‖ ∏ ‖τ i‖ = ‖α‖`.
    have hup : ∀ α : Covector (Eucl P) n, |α τ| ≤ ‖α‖ := by
      intro α
      have h := α.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    -- Lower bound: the calibrating covector `α₀(u) = det (⟪τ i, u j⟫)` has `α₀ τ = 1` and
    -- `‖α₀‖ ≤ 1` by Hadamard's inequality for the columns `c j = (⟪τ i, u j⟫)ᵢ` together with
    -- Bessel's inequality `‖c j‖ ≤ ‖u j‖`.
    set α₀ : Covector (Eucl P) n := wedgeCovectors n fun i => innerSL ℝ (τ i) with hα₀_def
    have hα₀τ : α₀ τ = 1 := by
      rw [hα₀_def, wedgeCovectors_apply_det]
      have h : (Matrix.of fun i j => innerSL ℝ (τ i) (τ j)) = 1 := by
        ext i j
        simp [Matrix.one_apply, orthonormal_iff_ite.mp hτ i j]
      rw [h, Matrix.det_one]
    have hα₀ : ‖α₀‖ ≤ 1 := by
      refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one fun u => ?_
      rw [one_mul, hα₀_def, wedgeCovectors_apply_det, Real.norm_eq_abs]
      set c : Fin n → EuclideanSpace ℝ (Fin n) :=
        fun j => WithLp.toLp 2 fun i => inner ℝ (τ i) (u j) with hc
      set e := EuclideanSpace.basisFun (Fin n) ℝ
      have hdet : (Matrix.of fun i j => innerSL ℝ (τ i) (u j)).det = e.toBasis.det c := by
        rw [Module.Basis.det_apply]
        congr 1
      have hHad : |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := by
        have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) :=
          ⟨finrank_euclideanSpace_fin⟩
        rw [← e.toBasis.orientation.volumeForm_robust' e c]
        exact e.toBasis.orientation.abs_volumeForm_apply_le c
      have hBessel : ∀ j, ‖c j‖ ≤ ‖u j‖ := by
        intro j
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (u j))]
        apply Real.sqrt_le_sqrt
        simpa [hc] using hτ.sum_inner_products_le (u j) (s := Finset.univ)
      rw [hdet]
      calc |e.toBasis.det c| ≤ ∏ j, ‖c j‖ := hHad
        _ ≤ ∏ j, ‖u j‖ := by gcongr with j; exact hBessel j
    -- Hence `‖simpleNVector v‖ = |det B|`.
    have hnorm : ‖simpleNVector v‖ = |B.det| := by
      apply le_antisymm
      · refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun α => ?_
        rw [hsv, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hup α) (abs_nonneg _)
      · calc |B.det| = ‖simpleNVector v α₀‖ := by rw [hsv, hα₀τ, mul_one, Real.norm_eq_abs]
          _ ≤ ‖simpleNVector v‖ * ‖α₀‖ := (simpleNVector v).le_opNorm α₀
          _ ≤ ‖simpleNVector v‖ * 1 :=
            mul_le_mul_of_nonneg_left hα₀ (ContinuousLinearMap.opNorm_nonneg _)
          _ = ‖simpleNVector v‖ := mul_one _
    rw [hnorm, hgram, Matrix.det_mul, Matrix.det_transpose, sq_abs, sq]
  · -- Dependent family: every alternating map vanishes on `v`, and `G(v) g = 0` for a
    -- nontrivial relation `∑ g j • v j = 0`, so both sides vanish.
    have h0 : ‖simpleNVector v‖ = 0 := by
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun α => ?_)
        (ContinuousLinearMap.opNorm_nonneg _)
      have hα : α v = 0 := α.toAlternatingMap.map_linearDependent v hv
      rw [simpleNVector_apply, hα, norm_zero, zero_mul]
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
    have hdet : (Matrix.of fun i j => inner ℝ (v i) (v j)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨g, fun h => hi₀ (congrFun h i₀), ?_⟩
      funext i
      have h := congrArg (inner ℝ (v i)) hg
      simp only [inner_sum, inner_smul_right, inner_zero_right] at h
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    rw [h0, hdet, sq, mul_zero]
/-- Antilipschitz charts pull back `Hⁿ`-null sets to `Lⁿ`-null sets (Simon Ch. 3, proof of 2.6;
used for Ch. 6, 3.9): if `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω` with `c > 0`, then `Φ` has a
`c⁻¹`-Lipschitz inverse `Ψ` on `Φ(Ω)` with `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, so `Hⁿ(Z) = 0` gives
`Lⁿ(Ω ∩ Φ⁻¹(Z)) = Hⁿ(Ω ∩ Φ⁻¹(Z)) = 0`. -/
theorem Submission.lpf_raf_chart_preimage_null : ∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (c : ℝ), 0 < c → (∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ Z : Set (Eucl P), (μHE[n] : Measure (Eucl P)) Z = 0 → (volume : Measure (Eucl n)) (Ω ∩ Φ ⁻¹' Z) = 0 := by
  intro P n Φ Ω c hc hΦ Z hZ
  -- `Φ` is injective on `Ω`, so `Ψ := invFunOn Φ Ω` is a left inverse of `Φ` on `Ω`.
  have hinj : InjOn Φ Ω := by
    intro w hw w' hw' h
    have h1 := hΦ w hw w' hw'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖w - w'‖ ≤ 0 := by
      by_contra h3
      exact absurd h1 (not_le.mpr (mul_pos hc (lt_of_not_ge h3)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  set Ψ := Function.invFunOn Φ Ω
  have hleft : LeftInvOn Ψ Φ Ω := hinj.leftInvOn_invFunOn
  -- `Ψ` is `c⁻¹`-Lipschitz on `Φ '' Ω`.
  have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) Ψ (Φ '' Ω) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [hleft hw, hleft hw', dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hΦ w hw w' hw'
  -- `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, and the latter is `Hⁿ`-null by the Lipschitz image bound.
  have hsub : Ω ∩ Φ ⁻¹' Z ⊆ Ψ '' (Φ '' Ω ∩ Z) := by
    rintro w ⟨hw, hwZ⟩
    exact ⟨Φ w, ⟨⟨w, hw, rfl⟩, hwZ⟩, hleft hw⟩
  have himg : (μHE[n] : Measure (Eucl n)) (Ψ '' (Φ '' Ω ∩ Z)) = 0 := by
    have h1 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
      (A := Φ '' Ω ∩ Z) n (hlip.mono fun _ hy => hy.1)
    have h2 : (μHE[n] : Measure (Eucl P)) (Φ '' Ω ∩ Z) = 0 :=
      measure_mono_null (fun _ hy => hy.2) hZ
    rw [h2, mul_zero] at h1
    exact nonpos_iff_eq_zero.mp h1
  -- On `ℝⁿ`, `Hⁿ = Lⁿ`.
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact measure_mono_null hsub himg
set_option maxHeartbeats 3200000 in
/-- Replacing a tangential skeleton current by a lattice chain (Simon Ch. 6, proof of 5.1,
printed displays (26)–(37)).  Let `n = m + 1` and `Q ∈ 𝒟ₙ(ℝ^{n+ℓ})` with `M(Q) + M(∂Q) < ∞`,
supported in the `n`-skeleton `⋃_F F` of the unit lattice and tangential near each face.  Then
`Q − P = S` with `P = ∑_F β_F [[F]]`, `M(P) ≤ C M(Q)`, `M(∂P) ≤ C M(∂Q)`, `M(S) ≤ C M(∂Q)`,
`spt P` in the closed `√n`-neighbourhood of `spt Q`, `spt ∂P ∪ spt S` in that of `spt ∂Q`, and
`β_F ∈ ℤ` with `P` integer multiplicity when `Q` is integer multiplicity.

Proof (every auxiliary fact is a local `have`).  Write `Q` and `∂Q` through the measure
representations of `deformation_mass_restriction`.  Finite boundary mass forces the
`dx^γ`-coefficient of `Q` to vanish a.e. on every hyperplane `{x_{γ i} = c}`, so `Q` does not
charge the `(n-1)`-skeleton and is the sum over the open faces `F` of `∫_F ω(e_F) v_F dμ`; in
particular the tangentiality hypothesis is not needed.  On the open unit cube a Poincaré
inequality (via a smooth divergence solver built from line integrals) and a trace inequality
bound `Q⌞F − b_F [[F]]` by `M(∂Q)` near `F`, where `b_F` is a weighted mean of the density.
Take `β_F = b_F`, or `β_F = round b_F` when `Q` is integer multiplicity (the density is then
integer valued on `F`, so `|b_F − round b_F|` obeys the same bound).  A lattice chain with
integer coefficients is integer multiplicity.  Each local lemma starts with
`clear * - …; revert …; refine id ?_; intro …`, which makes its proof term closed so that the
long chain of local lemmas is elaborated and kernel-checked in linear memory. -/
theorem Submission.deformation_skeleton_polyhedral :
    ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ Q : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), Q.mass + Q.boundary.mass < ∞ → Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F → (∀ (F : LatticeFaceIndex (m + 1) (m + 1 + ℓ)) (y : Eucl (m + 1 + ℓ)) (r : ℝ), ball y r ∩ (⋃ G : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 G) ⊆ latticeFace 1 F → ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) ⊆ ball y r → (∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0) → Q ω = 0) → ∃ (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ) (P S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), IsLatticeChain 1 β P ∧ (∀ ω, Q ω - P ω = S ω) ∧ P.mass ≤ C * Q.mass ∧ P.boundary.mass ≤ C * Q.boundary.mass ∧ S.mass ≤ C * Q.boundary.mass ∧ P.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.support ∧ P.boundary.support ∪ S.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.boundary.support ∧ (IsIntegerMultiplicity Q → (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity P) := by
  have hMR : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k), X.mass < ∞ → ∃ (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) k), IsFiniteMeasure μ ∧ IsMeasureRepresentation X μ v ∧ μ X.supportᶜ = 0 ∧ (∀ (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ' v' → ∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v' x α ∂μ' = ∫ x in A, v x α ∂μ) ∧ ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y ∧ (∀ ω : TestFormOn (univ : Set (Eucl N)) k, Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) k) x) ∂μ) ∧ (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧ (∀ Y' : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y' → Y' = Y) ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) :=
    Submission.deformation_mass_restriction
  have skp_coord_le_cnorm : ∀ {N k : ℕ} (a : Covector (Eucl N) k) (γ : SimonMultiIndex k N), |a (fun j => EuclideanSpace.single (γ j) (1 : ℝ))| ≤ covectorEuclideanNorm a := by
    clear * -
    intro N k a γ
    classical
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have hγ : StrictMono (γ : Fin k → Fin N) := γ.strictMono
    calc (a fun j => EuclideanSpace.single (γ j) (1 : ℝ)) ^ 2
        = (fun I : Fin k → Fin N => if StrictMono I then
            (a fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i)) ^ 2 else 0) (γ : Fin k → Fin N) := by
          simp [hγ, EuclideanSpace.basisFun_apply]
      _ ≤ _ := Finset.single_le_sum (f := fun I : Fin k → Fin N => if StrictMono I then
            (a fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i)) ^ 2 else 0)
          (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ _)
  have skp_cnorm_le_of_coord_le : ∀ {N k : ℕ} (a : Covector (Eucl N) k) (B : ℝ) (hB : 0 ≤ B) (h : ∀ I : Fin k → Fin N, StrictMono I →
        |a (fun i => EuclideanSpace.single (I i) (1 : ℝ))| ≤ B), covectorEuclideanNorm a ≤ (Fintype.card (Fin k → Fin N) : ℝ) * B := by
    clear * -
    intro N k a B hB h
    classical
    unfold covectorEuclideanNorm
    set c : ℝ := (Fintype.card (Fin k → Fin N) : ℝ) with hc_def
    have hc : 0 ≤ c := Nat.cast_nonneg _
    have hcc : c ≤ c ^ 2 := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Fin k → Fin N)) with h0 | h0
      · simp [hc_def, h0]
      · have : (1 : ℝ) ≤ c := by rw [hc_def]; exact_mod_cast h0
        nlinarith
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : ∀ I ∈ (Finset.univ : Finset (Fin k → Fin N)),
        (if StrictMono I then (a fun i => EuclideanSpace.basisFun (Fin N) ℝ (I i)) ^ 2 else 0)
          ≤ B ^ 2 := by
      intro I _
      split_ifs with hI
      · have h2 := h I hI
        simp only [EuclideanSpace.basisFun_apply]
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      · positivity
    calc _ ≤ ∑ _I : Fin k → Fin N, B ^ 2 := Finset.sum_le_sum h1
      _ = c * B ^ 2 := by simp [hc_def, Finset.card_univ]
      _ ≤ (c * B) ^ 2 := by nlinarith [sq_nonneg B]
  have skp_cnorm_smul : ∀ {N k : ℕ} (t : ℝ) (a : Covector (Eucl N) k), covectorEuclideanNorm (t • a) = |t| * covectorEuclideanNorm a := by
    clear * -
    intro N k t a
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · simp
  have skp_mass_tool : ∀ {N k : ℕ} (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (hX : X.mass < ∞), ∃ (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) k), IsFiniteMeasure μ ∧
        IsMeasureRepresentation X μ v ∧ μ X.supportᶜ = 0 ∧
        (∀ W : Set (Eucl N), IsOpen W → X.massOn W = μ W) ∧
        (∀ (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k),
          IsMeasureRepresentation X μ' v' → ∀ A : Set (Eucl N), MeasurableSet A →
            Bornology.IsBounded A → ∀ α : Covector (Eucl N) k,
              ∫ x in A, v' x α ∂μ' = ∫ x in A, v x α ∂μ) ∧
        ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k,
          (∀ ω : TestFormOn (univ : Set (Eucl N)) k,
            Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) k) x) ∂μ) ∧
          (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧
          (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) := by
    clear * - hMR
    revert hMR
    refine id ?_
    intro hMR N k X hX
    obtain ⟨μ, v, hfin, hrep, hsupp, huniq, hres⟩ := hMR N k X hX
    refine ⟨μ, v, hfin, hrep, hsupp, ?_, huniq, ?_⟩
    · obtain ⟨Y, _, _, hYm, hYu, _⟩ := hres univ MeasurableSet.univ
      have hXY : X = Y := hYu X ⟨MeasurableSet.univ, μ, v, hrep, fun ω => by
        rw [Measure.restrict_univ]; exact (hrep ω).2⟩
      intro W hW
      rw [hXY, hYm W hW, inter_univ]
    · intro A hA
      obtain ⟨Y, _, hYω, hYm, _, hYi⟩ := hres A hA
      exact ⟨Y, hYω, hYm, hYi⟩
  have skp_abs_le : ∀ {N k : ℕ} (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ : Measure (Eucl N)) [IsFiniteMeasure μ] (hmass : ∀ W : Set (Eucl N), IsOpen W → X.massOn W = μ W) (W : Set (Eucl N)) (hW : IsOpen W) (ω : TestFormOn (univ : Set (Eucl N)) k) (hω : tsupport (ω : DifferentialForm (Eucl N) k) ⊆ W) (C : ℝ) (hC : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) k) x) ≤ C), |X ω| ≤ (μ W).toReal * C := by
    clear * -
    intro N k X μ _ hmass W hW ω hω C hC
    exact Submission.cmb_abs_apply_le_of_massOn_le N k univ W X ω (μ W).toReal C ENNReal.toReal_nonneg
          (by rw [hmass W hW, ENNReal.ofReal_toReal (measure_ne_top μ W)]) hω hC
  have skp_mem_face : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), x ∈ latticeFace 1 F ↔ ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) ≤ x i ∧ x i ≤ F.1 i + 1) ∧
        (i ∉ range F.2 → x i = F.1 i) := by
    clear * -
    intro n N F x
    simp only [latticeFace, Set.mem_setOf_eq, one_mul]
  obtain ⟨skpOFace, hskpOFace⟩ : ∃ f : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Set (Eucl N), ∀ {n N : ℕ} (F : LatticeFaceIndex n N), f F = {x : Eucl N | ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
      (i ∉ range F.2 → x i = F.1 i)} :=
      ⟨fun {n N : ℕ} (F : LatticeFaceIndex n N) => {x : Eucl N | ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
      (i ∉ range F.2 → x i = F.1 i)}, fun _ => rfl⟩
  have skpOFace_mem : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), x ∈ skpOFace F ↔ ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
        (i ∉ range F.2 → x i = F.1 i) := by
    clear * - skpOFace hskpOFace
    revert skpOFace hskpOFace
    refine id ?_
    intro skpOFace hskpOFace n N F x
    simp only [hskpOFace, Set.mem_setOf_eq]
  obtain ⟨skpNbhd, hskpNbhd⟩ : ∃ f : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Set (Eucl N), ∀ {n N : ℕ} (F : LatticeFaceIndex n N), f F = {x : Eucl N | ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
      (i ∉ range F.2 → |x i - F.1 i| < 1)} :=
      ⟨fun {n N : ℕ} (F : LatticeFaceIndex n N) => {x : Eucl N | ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
      (i ∉ range F.2 → |x i - F.1 i| < 1)}, fun _ => rfl⟩
  have skpNbhd_mem : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), x ∈ skpNbhd F ↔ ∀ i : Fin N, (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
        (i ∉ range F.2 → |x i - F.1 i| < 1) := by
    clear * - skpNbhd hskpNbhd
    revert skpNbhd hskpNbhd
    refine id ?_
    intro skpNbhd hskpNbhd n N F x
    simp only [hskpNbhd, Set.mem_setOf_eq]
  have skp_coord_continuous : ∀ {N : ℕ} (i : Fin N), Continuous fun x : Eucl N => x i := by
    clear * -
    intro N i
    exact (EuclideanSpace.proj i : Eucl N →L[ℝ] ℝ).continuous
  have skp_eq_of_range_subset : ∀ {n N : ℕ} (α β : SimonMultiIndex n N) (h : range α ⊆ range β), α = β := by
    clear * -
    intro n N α β h
    rw [← OrderEmbedding.range_inj_of_wellFoundedLT]
    refine Set.eq_of_subset_of_ncard_le h ?_ (Set.finite_range β)
    rw [Set.ncard_range_of_injective β.injective, Set.ncard_range_of_injective α.injective]
  have skp_oface_subset_face : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), skpOFace F ⊆ latticeFace 1 F := by
    clear * - skp_mem_face skpOFace skpOFace_mem
    revert skp_mem_face skpOFace skpOFace_mem
    refine id ?_
    intro skp_mem_face skpOFace skpOFace_mem n N F x hx
    rw [skpOFace_mem] at hx
    rw [skp_mem_face]
    intro i
    exact ⟨fun hi => ⟨((hx i).1 hi).1.le, ((hx i).1 hi).2.le⟩, (hx i).2⟩
  have skp_oface_subset_nbhd : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), skpOFace F ⊆ skpNbhd F := by
    clear * - skpOFace skpOFace_mem skpNbhd skpNbhd_mem
    revert skpOFace skpOFace_mem skpNbhd skpNbhd_mem
    refine id ?_
    intro skpOFace skpOFace_mem skpNbhd skpNbhd_mem n N F x hx
    rw [skpOFace_mem] at hx
    rw [skpNbhd_mem]
    intro i
    refine ⟨(hx i).1, fun hi => ?_⟩
    rw [(hx i).2 hi, sub_self, abs_zero]
    exact one_pos
  have skp_nbhd_face : ∀ {n N : ℕ} (F G : LatticeFaceIndex n N) (x : Eucl N) (hx : x ∈ skpNbhd F) (hG : x ∈ latticeFace 1 G), G = F ∧ x ∈ skpOFace F := by
    clear * - skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_eq_of_range_subset
    revert skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_eq_of_range_subset
    refine id ?_
    intro skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_eq_of_range_subset n N F G x hx hG
    rw [skpNbhd_mem] at hx
    rw [skp_mem_face] at hG
    have hnotint : ∀ i, i ∈ range F.2 → ∀ c : ℤ, x i ≠ c := by
      intro i hi c hc
      obtain ⟨h1, h2⟩ := (hx i).1 hi
      rw [hc] at h1 h2
      have e1 : F.1 i < c := by exact_mod_cast h1
      have e2 : c < F.1 i + 1 := by
        have h2' : ((c : ℤ) : ℝ) < ((F.1 i + 1 : ℤ) : ℝ) := by push_cast; linarith
        exact_mod_cast h2'
      omega
    have hsub : range F.2 ⊆ range G.2 := by
      intro i hi
      by_contra hiG
      exact hnotint i hi (G.1 i) ((hG i).2 hiG)
    have h2 : G.2 = F.2 := (skp_eq_of_range_subset F.2 G.2 hsub).symm
    have h1 : G.1 = F.1 := by
      funext i
      by_cases hi : i ∈ range F.2
      · have hiG : i ∈ range G.2 := by rw [h2]; exact hi
        obtain ⟨a1, a2⟩ := (hG i).1 hiG
        obtain ⟨b1, b2⟩ := (hx i).1 hi
        have e1 : (G.1 i : ℝ) < F.1 i + 1 := lt_of_le_of_lt a1 b2
        have e2 : (F.1 i : ℝ) < G.1 i + 1 := lt_of_lt_of_le b1 a2
        have e1' : G.1 i < F.1 i + 1 := by exact_mod_cast e1
        have e2' : F.1 i < G.1 i + 1 := by exact_mod_cast e2
        omega
      · have hiG : i ∉ range G.2 := by rw [h2]; exact hi
        have a := (hG i).2 hiG
        have b := (hx i).2 hi
        rw [a] at b
        have b' : |((G.1 i - F.1 i : ℤ) : ℝ)| < 1 := by push_cast; exact b
        have b'' : |G.1 i - F.1 i| < 1 := by exact_mod_cast b'
        rw [abs_lt] at b''
        omega
    have hGF : G = F := Prod.ext h1 h2
    refine ⟨hGF, ?_⟩
    rw [skpOFace_mem]
    intro i
    refine ⟨(hx i).1, fun hi => ?_⟩
    have hiG : i ∉ range G.2 := by rw [h2]; exact hi
    rw [(hG i).2 hiG, h1]
  have skp_oface_face : ∀ {n N : ℕ} (F G : LatticeFaceIndex n N) (x : Eucl N) (hx : x ∈ skpOFace F) (hG : x ∈ latticeFace 1 G), G = F := by
    clear * - skpOFace skpNbhd skp_oface_subset_nbhd skp_nbhd_face
    revert skpOFace skpNbhd skp_oface_subset_nbhd skp_nbhd_face
    refine id ?_
    intro skpOFace skpNbhd skp_oface_subset_nbhd skp_nbhd_face n N F G x hx hG
    exact (skp_nbhd_face F G x (skp_oface_subset_nbhd F hx) hG).1
  have skp_oface_disjoint : ∀ {n N : ℕ} (F G : LatticeFaceIndex n N) (h : F ≠ G), Disjoint (skpOFace F) (skpOFace G) := by
    clear * - skpOFace skp_oface_subset_face skp_oface_face
    revert skpOFace skp_oface_subset_face skp_oface_face
    refine id ?_
    intro skpOFace skp_oface_subset_face skp_oface_face n N F G h
    rw [Set.disjoint_left]
    intro x hxF hxG
    exact h (skp_oface_face G F x hxG (skp_oface_subset_face F hxF))
  have skp_isOpen_nbhd : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), IsOpen (skpNbhd F) := by
    clear * - skpNbhd skpNbhd_mem skp_coord_continuous
    revert skpNbhd skpNbhd_mem skp_coord_continuous
    refine id ?_
    intro skpNbhd skpNbhd_mem skp_coord_continuous n N F
    have : skpNbhd F = ⋂ i : Fin N, {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧
        x i < F.1 i + 1) ∧ (i ∉ range F.2 → |x i - F.1 i| < 1)} := by
      ext x; simp only [skpNbhd_mem, mem_iInter, Set.mem_setOf_eq]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases hi : i ∈ range F.2
    · have : {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
          (i ∉ range F.2 → |x i - F.1 i| < 1)} = {x : Eucl N | (F.1 i : ℝ) < x i} ∩ {x : Eucl N | x i < (F.1 i : ℝ) + 1} := by
        ext x; simp [hi]
      rw [this]
      exact (isOpen_lt continuous_const (skp_coord_continuous i)).inter
        (isOpen_lt (skp_coord_continuous i) continuous_const)
    · have : {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) < x i ∧ x i < F.1 i + 1) ∧
          (i ∉ range F.2 → |x i - F.1 i| < 1)} = {x : Eucl N | |x i - (F.1 i : ℝ)| < 1} := by
        ext x; simp [hi]
      rw [this]
      exact isOpen_lt (((skp_coord_continuous i).sub continuous_const).abs) continuous_const
  have skp_isClosed_face : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), IsClosed (latticeFace 1 F) := by
    clear * - skp_mem_face skp_coord_continuous
    revert skp_mem_face skp_coord_continuous
    refine id ?_
    intro skp_mem_face skp_coord_continuous n N F
    have : latticeFace 1 F = ⋂ i : Fin N, {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) ≤ x i ∧
        x i ≤ F.1 i + 1) ∧ (i ∉ range F.2 → x i = F.1 i)} := by
      ext x; simp only [skp_mem_face, mem_iInter, Set.mem_setOf_eq]
    rw [this]
    refine isClosed_iInter fun i => ?_
    by_cases hi : i ∈ range F.2
    · have : {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) ≤ x i ∧ x i ≤ F.1 i + 1) ∧
          (i ∉ range F.2 → x i = F.1 i)} = {x : Eucl N | (F.1 i : ℝ) ≤ x i} ∩ {x : Eucl N | x i ≤ (F.1 i : ℝ) + 1} := by
        ext x; simp [hi]
      rw [this]
      exact (isClosed_le continuous_const (skp_coord_continuous i)).inter
        (isClosed_le (skp_coord_continuous i) continuous_const)
    · have : {x : Eucl N | (i ∈ range F.2 → (F.1 i : ℝ) ≤ x i ∧ x i ≤ F.1 i + 1) ∧
          (i ∉ range F.2 → x i = F.1 i)} = {x : Eucl N | x i = (F.1 i : ℝ)} := by
        ext x; simp [hi]
      rw [this]
      exact isClosed_eq (skp_coord_continuous i) continuous_const
  have skp_abs_coord_le : ∀ {N : ℕ} (x y : Eucl N) (i : Fin N), |x i - y i| ≤ dist x y := by
    clear * -
    intro N x y i
    rw [EuclideanSpace.dist_eq]
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j => dist (x j) (y j) ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    simpa [Real.dist_eq, sq_abs] using this
  have skp_locallyFinite : ∀ {n N : ℕ}, LocallyFinite (fun F : LatticeFaceIndex n N => latticeFace 1 F) := by
    clear * - skp_mem_face skp_abs_coord_le
    revert skp_mem_face skp_abs_coord_le
    refine id ?_
    intro skp_mem_face skp_abs_coord_le n N x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
    have key : ∀ F : LatticeFaceIndex n N, (latticeFace 1 F ∩ ball x 1).Nonempty →
        ∀ i, F.1 i ∈ Finset.Icc (⌊x i⌋ - 2) (⌊x i⌋ + 1) := by
      rintro F ⟨y, hyF, hyB⟩ i
      rw [skp_mem_face] at hyF
      have hyi : |y i - x i| < 1 := lt_of_le_of_lt (skp_abs_coord_le y x i) (mem_ball.1 hyB)
      rw [abs_lt] at hyi
      have hfl1 := Int.floor_le (x i)
      have hfl2 := Int.lt_floor_add_one (x i)
      rw [Finset.mem_Icc]
      by_cases hi : i ∈ range F.2
      · obtain ⟨a1, a2⟩ := (hyF i).1 hi
        have c1 : (F.1 i : ℝ) < ⌊x i⌋ + 2 := by linarith
        have c2 : ((⌊x i⌋ : ℤ) : ℝ) - 2 < F.1 i + 1 := by linarith
        constructor
        · have : ⌊x i⌋ - 2 < F.1 i + 1 := by exact_mod_cast c2
          omega
        · have : F.1 i < ⌊x i⌋ + 2 := by exact_mod_cast c1
          omega
      · have a := (hyF i).2 hi
        rw [a] at hyi
        have c1 : (F.1 i : ℝ) < ⌊x i⌋ + 2 := by linarith
        have c2 : ((⌊x i⌋ : ℤ) : ℝ) - 2 < F.1 i + 1 := by linarith
        constructor
        · have : ⌊x i⌋ - 2 < F.1 i + 1 := by exact_mod_cast c2
          omega
        · have : F.1 i < ⌊x i⌋ + 2 := by exact_mod_cast c1
          omega
    apply Set.Finite.subset ((Fintype.piFinset fun i => Finset.Icc (⌊x i⌋ - 2) (⌊x i⌋ + 1)) ×ˢ
      (Finset.univ : Finset (SimonMultiIndex n N))).finite_toSet
    intro F hF
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_univ, and_true]
    exact key F hF
  have skp_face_dist : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x y : Eucl N) (hx : x ∈ latticeFace 1 F) (hy : y ∈ latticeFace 1 F), dist x y ≤ Real.sqrt n := by
    clear * - skp_mem_face
    revert skp_mem_face
    refine id ?_
    intro skp_mem_face n N F x y hx hy
    classical
    rw [EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    rw [skp_mem_face] at hx hy
    have hcard : (Finset.univ.filter fun i : Fin N => i ∈ range F.2).card = n := by
      have : (Finset.univ.filter fun i : Fin N => i ∈ range F.2) = Finset.univ.image F.2 := by
        ext i; simp
      rw [this, Finset.card_image_of_injective _ F.2.injective, Finset.card_univ, Fintype.card_fin]
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ i : Fin N, (if i ∈ range F.2 then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs with hi
          · obtain ⟨a1, a2⟩ := (hx i).1 hi
            obtain ⟨b1, b2⟩ := (hy i).1 hi
            rw [Real.dist_eq, sq_abs]
            nlinarith
          · rw [(hx i).2 hi, (hy i).2 hi]
            simp
      _ = n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one, hcard]
  have skp_bdry_int : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (hx : x ∈ latticeFace 1 F) (hx' : x ∉ skpOFace F) (γ : SimonMultiIndex n N), ∃ i0 : Fin n, ∃ c : ℤ, x (γ i0) = c := by
    clear * - skp_mem_face skpOFace skpOFace_mem
    revert skp_mem_face skpOFace skpOFace_mem
    refine id ?_
    intro skp_mem_face skpOFace skpOFace_mem n N F x hx hx' γ
    classical
    rw [skp_mem_face] at hx
    rw [skpOFace_mem] at hx'
    simp only [not_forall] at hx'
    obtain ⟨i, hi⟩ := hx'
    have hir : i ∈ range F.2 := by
      by_contra h
      exact hi ⟨fun h' => absurd h' h, fun _ => (hx i).2 h⟩
    have hint : x i = F.1 i ∨ x i = F.1 i + 1 := by
      obtain ⟨a1, a2⟩ := (hx i).1 hir
      by_contra hne
      have hne' := not_or.1 hne
      exact hi ⟨fun _ => ⟨lt_of_le_of_ne a1 (Ne.symm hne'.1), lt_of_le_of_ne a2 hne'.2⟩,
        fun h => absurd hir h⟩
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ.image γ) ⊆ (Finset.univ.image F.2).erase i := by
      intro j hj
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
      obtain ⟨a, rfl⟩ := hj
      rw [Finset.mem_erase, Finset.mem_image]
      constructor
      · intro hai
        rcases hint with h | h
        · exact hno a (F.1 i) (by rw [hai]; exact h)
        · exact hno a (F.1 i + 1) (by rw [hai, h]; push_cast; ring)
      · by_contra hnr
        have hnr' : γ a ∉ range F.2 := by
          rintro ⟨b, hb⟩
          exact hnr ⟨b, Finset.mem_univ _, hb⟩
        exact hno a (F.1 (γ a)) ((hx (γ a)).2 hnr')
    have hcardle := Finset.card_le_card hsub
    have hmem : i ∈ Finset.univ.image F.2 := by
      obtain ⟨j, hj⟩ := hir
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    rw [Finset.card_image_of_injective _ γ.injective, Finset.card_erase_of_mem hmem,
      Finset.card_image_of_injective _ F.2.injective, Finset.card_univ, Fintype.card_fin] at hcardle
    obtain ⟨j, _⟩ := hir
    have := j.pos
    omega
  have skp_oface_coord : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (hx : x ∈ skpOFace F) (γ : SimonMultiIndex n N) (hγ : γ ≠ F.2), ∃ i0 : Fin n, x (γ i0) = F.1 (γ i0) := by
    clear * - skpOFace skpOFace_mem skp_eq_of_range_subset
    revert skpOFace skpOFace_mem skp_eq_of_range_subset
    refine id ?_
    intro skpOFace skpOFace_mem skp_eq_of_range_subset n N F x hx γ hγ
    rw [skpOFace_mem] at hx
    by_contra h
    push Not at h
    apply hγ
    apply skp_eq_of_range_subset
    rintro _ ⟨a, rfl⟩
    by_contra hr
    exact h a ((hx (γ a)).2 hr)
  obtain ⟨skpChart, hskpChart⟩ : ∃ f : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n), Eucl N, ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n), f F u = WithLp.toLp 2 (fun i => (F.1 i : ℝ) + ∑ j, if F.2 j = i then u j else 0) :=
      ⟨fun {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n) => WithLp.toLp 2 (fun i => (F.1 i : ℝ) + ∑ j, if F.2 j = i then u j else 0), fun _ _ => rfl⟩
  obtain ⟨skpProj, hskpProj⟩ : ∃ f : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), Eucl n, ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), f F x = WithLp.toLp 2 (fun j => x (F.2 j) - F.1 (F.2 j)) :=
      ⟨fun {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) => WithLp.toLp 2 (fun j => x (F.2 j) - F.1 (F.2 j)), fun _ _ => rfl⟩
  have skpChart_on : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n) (j : Fin n), skpChart F u (F.2 j) = F.1 (F.2 j) + u j := by
    clear * - skpChart hskpChart
    revert skpChart hskpChart
    refine id ?_
    intro skpChart hskpChart n N F u j
    rw [hskpChart]
    simp only [F.2.inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have skpChart_off : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n) (i : Fin N) (hi : i ∉ range F.2), skpChart F u i = F.1 i := by
    clear * - skpChart hskpChart
    revert skpChart hskpChart
    refine id ?_
    intro skpChart hskpChart n N F u i hi
    rw [hskpChart]
    have hne : ∀ j, F.2 j ≠ i := fun j hj => hi ⟨j, hj⟩
    simp [hne]
  have skpProj_apply : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (j : Fin n), skpProj F x j = x (F.2 j) - F.1 (F.2 j) := by
    clear * - skpProj hskpProj
    revert skpProj hskpProj
    refine id ?_
    intro skpProj hskpProj n N F x j
    simp [hskpProj]
  have skpProj_chart : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n), skpProj F (skpChart F u) = u := by
    clear * - skpChart skpProj skpChart_on skpProj_apply
    revert skpChart skpProj skpChart_on skpProj_apply
    refine id ?_
    intro skpChart skpProj skpChart_on skpProj_apply n N F u
    ext j
    rw [skpProj_apply, skpChart_on]
    ring
  have skpChart_proj : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (hx : ∀ i, i ∉ range F.2 → x i = F.1 i), skpChart F (skpProj F x) = x := by
    clear * - skpChart skpProj skpChart_on skpChart_off skpProj_apply
    revert skpChart skpProj skpChart_on skpChart_off skpProj_apply
    refine id ?_
    intro skpChart skpProj skpChart_on skpChart_off skpProj_apply n N F x hx
    ext i
    by_cases hi : i ∈ range F.2
    · obtain ⟨j, rfl⟩ := hi
      rw [skpChart_on, skpProj_apply]
      ring
    · rw [skpChart_off F _ i hi, hx i hi]
  have skpChart_isometry : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Isometry (skpChart F) := by
    clear * - skpChart skpChart_on skpChart_off
    revert skpChart skpChart_on skpChart_off
    refine id ?_
    intro skpChart skpChart_on skpChart_off n N F
    classical
    refine Isometry.of_dist_eq fun y y' => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image F.2)) ?_,
      Finset.sum_image (fun j _ j' _ h => F.2.injective h)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [skpChart_on, skpChart_on, dist_add_left]
    · intro i _ hi
      have hi' : i ∉ range F.2 := by
        rintro ⟨j, rfl⟩
        exact hi (Finset.mem_image_of_mem F.2 (Finset.mem_univ j))
      rw [skpChart_off F y i hi', skpChart_off F y' i hi', dist_self]
      ring
  have skp_oface_iff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), x ∈ skpOFace F ↔ (∀ i, i ∉ range F.2 → x i = F.1 i) ∧
        ∀ j, 0 < skpProj F x j ∧ skpProj F x j < 1 := by
    clear * - skpOFace skpOFace_mem skpProj skpProj_apply
    revert skpOFace skpOFace_mem skpProj skpProj_apply
    refine id ?_
    intro skpOFace skpOFace_mem skpProj skpProj_apply n N F x
    rw [skpOFace_mem]
    constructor
    · intro h
      refine ⟨fun i hi => (h i).2 hi, fun j => ?_⟩
      obtain ⟨a1, a2⟩ := (h (F.2 j)).1 ⟨j, rfl⟩
      rw [skpProj_apply]
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ i
      refine ⟨?_, h1 i⟩
      rintro ⟨j, rfl⟩
      have := h2 j
      rw [skpProj_apply] at this
      constructor <;> linarith [this.1, this.2]
  have skp_face_iff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), x ∈ latticeFace 1 F ↔ (∀ i, i ∉ range F.2 → x i = F.1 i) ∧
        ∀ j, 0 ≤ skpProj F x j ∧ skpProj F x j ≤ 1 := by
    clear * - skp_mem_face skpProj skpProj_apply
    revert skp_mem_face skpProj skpProj_apply
    refine id ?_
    intro skp_mem_face skpProj skpProj_apply n N F x
    rw [skp_mem_face]
    constructor
    · intro h
      refine ⟨fun i hi => (h i).2 hi, fun j => ?_⟩
      obtain ⟨a1, a2⟩ := (h (F.2 j)).1 ⟨j, rfl⟩
      rw [skpProj_apply]
      constructor <;> linarith
    · rintro ⟨h1, h2⟩ i
      refine ⟨?_, h1 i⟩
      rintro ⟨j, rfl⟩
      have := h2 j
      rw [skpProj_apply] at this
      constructor <;> linarith [this.1, this.2]
  have skpChart_mem_oface : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n), skpChart F u ∈ skpOFace F ↔ ∀ j, 0 < u j ∧ u j < 1 := by
    clear * - skpOFace skpChart skpProj skpChart_off skpProj_chart skp_oface_iff
    revert skpOFace skpChart skpProj skpChart_off skpProj_chart skp_oface_iff
    refine id ?_
    intro skpOFace skpChart skpProj skpChart_off skpProj_chart skp_oface_iff n N F u
    rw [skp_oface_iff, skpProj_chart]
    exact ⟨fun h => h.2, fun h => ⟨fun i hi => skpChart_off F u i hi, h⟩⟩
  have skpChart_mem_face : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n), skpChart F u ∈ latticeFace 1 F ↔ ∀ j, 0 ≤ u j ∧ u j ≤ 1 := by
    clear * - skpChart skpProj skpChart_off skpProj_chart skp_face_iff
    revert skpChart skpProj skpChart_off skpProj_chart skp_face_iff
    refine id ?_
    intro skpChart skpProj skpChart_off skpProj_chart skp_face_iff n N F u
    rw [skp_face_iff, skpProj_chart]
    exact ⟨fun h => h.2, fun h => ⟨fun i hi => skpChart_off F u i hi, h⟩⟩
  have skp_scalar_form_mem : ∀ {N k : ℕ} (g : Eucl N → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) (W : Covector (Eucl N) k), (fun x => g x • W) ∈ (TestFormOn (univ : Set (Eucl N)) k) := by
    clear * -
    intro N k g hg hgc W
    refine ⟨⟨?_, ?_⟩, subset_univ _⟩
    · exact hg.smul contDiff_const
    · exact hgc.smul_right (f' := fun _ => W)
  have skp_extDeriv_smul_const : ∀ {N k : ℕ} (g : Eucl N → ℝ) (W : Covector (Eucl N) k) (x : Eucl N) (hg : DifferentiableAt ℝ g x), extDeriv (fun y => g y • W) x =
        ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight W) := by
    clear * -
    intro N k g W x hg
    unfold extDeriv
    rw [fderiv_smul_const hg]
  have skp_smulRight_add : ∀ {N k : ℕ} (a b : Eucl N →L[ℝ] ℝ) (W : Covector (Eucl N) k), (a + b).smulRight W = a.smulRight W + b.smulRight W := by
    clear * -
    intro N k a b W
    ext v w
    simp [add_smul]
  have skp_smulRight_smul : ∀ {N k : ℕ} (t : ℝ) (a : Eucl N →L[ℝ] ℝ) (W : Covector (Eucl N) k), (t • a).smulRight W = t • a.smulRight W := by
    clear * -
    intro N k t a W
    ext v w
    simp [smul_smul]
  have skp_wedge_perm : ∀ {N n : ℕ} (α : Fin n → (Eucl N →L[ℝ] ℝ)) (σ : Equiv.Perm (Fin n)), wedgeCovectors n (α ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℝ) • wedgeCovectors n α := by
    clear * -
    intro N n α σ
    ext v
    rw [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply_det, wedgeCovectors_apply_det,
      smul_eq_mul]
    have : (Matrix.of fun i j => (α ∘ σ) i (v j)) =
        (Matrix.of fun i j => α i (v j)).submatrix σ id := by
      ext i j; rfl
    rw [this, Matrix.det_permute]
  have skp_sigma_hasDerivAt : ∀ (ε c t : ℝ) (hε : ε ≠ 0), HasDerivAt (fun t => ε * Real.arctan ((t - c) / ε)) (1 / (1 + ((t - c) / ε) ^ 2)) t := by
    clear * -
    intro ε c t hε
    have h1 : HasDerivAt (fun t => (t - c) / ε) (1 / ε) t := by
      simpa using ((hasDerivAt_id t).sub_const c).div_const ε
    have h2 : HasDerivAt (fun t => Real.arctan ((t - c) / ε))
        (1 / (1 + ((t - c) / ε) ^ 2) * (1 / ε)) t := h1.arctan
    have h3 := h2.const_mul ε
    convert h3 using 1
    field_simp
  have skp_sigma_contDiff : ∀ (ε c : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ε * Real.arctan ((t - c) / ε)) := by
    clear * -
    intro ε c
    exact contDiff_const.mul (Real.contDiff_arctan.comp ((contDiff_id.sub contDiff_const).div_const ε))
  have skp_sigma_abs_le : ∀ (ε c t : ℝ) (hε : 0 < ε), |ε * Real.arctan ((t - c) / ε)| ≤ ε * (Real.pi / 2) := by
    clear * -
    intro ε c t hε
    rw [abs_mul, abs_of_pos hε]
    gcongr
    rw [abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
  have skp_sigma'_le_one : ∀ (ε c t : ℝ), 0 ≤ 1 / (1 + ((t - c) / ε) ^ 2) ∧ 1 / (1 + ((t - c) / ε) ^ 2) ≤ 1 := by
    clear * -
    intro ε c t
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg ((t - c) / ε)]
  have skp_sigma'_tendsto : ∀ (c t : ℝ), Tendsto (fun k : ℕ => 1 / (1 + ((t - c) / (1 / ((k : ℝ) + 1))) ^ 2)) atTop
        (𝓝 (if t = c then 1 else 0)) := by
    clear * -
    intro c t
    split_ifs with h
    · subst h; simp
    · have hne : t - c ≠ 0 := sub_ne_zero.2 h
      have h1 : Tendsto (fun k : ℕ => ((t - c) / (1 / ((k : ℝ) + 1))) ^ 2) atTop atTop := by
        have : (fun k : ℕ => ((t - c) / (1 / ((k : ℝ) + 1))) ^ 2) =
            fun k : ℕ => (t - c) ^ 2 * ((k : ℝ) + 1) ^ 2 := by
          funext k; field_simp
        rw [this]
        apply Tendsto.const_mul_atTop (by positivity)
        exact (tendsto_pow_atTop two_ne_zero).comp
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h2 : Tendsto (fun k : ℕ => 1 + ((t - c) / (1 / ((k : ℝ) + 1))) ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ _ h1
      refine (h2.inv_tendsto_atTop).congr' (Eventually.of_forall fun k => ?_)
      simp [one_div]
  -- Smooth compactly supported functions give a.e. vanishing.
  have skp_ae_zero_of_smooth : ∀ {N : ℕ} (μ₀ : Measure (Eucl N)) (g : Eucl N → ℝ) (S : Set (Eucl N)) (hS : MeasurableSet S) (hloc : ∀ R : ℝ, IntegrableOn g (closedBall 0 R) μ₀) (h : ∀ f : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        ∫ x, S.indicator 1 x * (f x * g x) ∂μ₀ = 0), ∀ᵐ x ∂μ₀, x ∈ S → g x = 0 := by
    clear * -
    intro N μ₀ g S hS hloc h
    have hR : ∀ R : ℕ, ∀ᵐ x ∂μ₀, x ∈ S ∩ ball (0 : Eucl N) R → g x = 0 := by
      intro R
      set U : Set (Eucl N) := S ∩ ball (0 : Eucl N) R with hU
      have hUm : MeasurableSet U := hS.inter measurableSet_ball
      set g₁ := U.indicator g with hg₁_def
      have hg₁ : Integrable g₁ μ₀ :=
        ((hloc R).mono_set ((inter_subset_right).trans ball_subset_closedBall)).integrable_indicator
          hUm
      have hsmooth : ∀ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ ball (0 : Eucl N) R → ∫ x, φ x * g₁ x ∂μ₀ = ∫ x, φ x * (0 : Eucl N → ℝ) x ∂μ₀ := by
        intro φ hφ hφc hφs
        simp only [Pi.zero_apply, mul_zero, integral_zero]
        rw [← h φ hφ hφc]
        congr 1
        funext x
        by_cases hx : x ∈ ball (0 : Eucl N) R
        · by_cases hxS : x ∈ S
          · simp [hg₁_def, hU, Set.indicator_of_mem (show x ∈ S ∩ ball 0 R from ⟨hxS, hx⟩), hxS]
          · have : x ∉ U := fun h' => hxS h'.1
            simp [hg₁_def, Set.indicator_of_notMem this, Set.indicator_of_notMem hxS]
        · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hφs h'))
          simp [this]
      have hcont := Submission.slicing_ru_smooth_to_continuous N μ₀ μ₀ g₁ 0 hg₁
        (integrable_zero _ _ _) (ball 0 R) isOpen_ball hsmooth
      have hbdd := Submission.slicing_ru_continuous_to_bounded N μ₀ μ₀ g₁ 0 hg₁
        (integrable_zero _ _ _) (ball 0 R) isOpen_ball hcont
      -- a measurable version of `g₁`
      set g₂ := hg₁.aestronglyMeasurable.mk g₁ with hg₂_def
      have hg₂m : Measurable g₂ := hg₁.aestronglyMeasurable.stronglyMeasurable_mk.measurable
      have hg₁₂ : g₁ =ᵐ[μ₀] g₂ := hg₁.aestronglyMeasurable.ae_eq_mk
      set hh : Eucl N → ℝ := (ball (0 : Eucl N) R ∩ {x | 0 < g₂ x}).indicator 1 -
        (ball (0 : Eucl N) R ∩ {x | g₂ x < 0}).indicator 1 with hh_def
      have hhm : Measurable hh := by
        refine Measurable.sub ?_ ?_
        · exact (measurable_one.indicator (measurableSet_ball.inter (measurableSet_lt measurable_const hg₂m)))
        · exact (measurable_one.indicator (measurableSet_ball.inter (measurableSet_lt hg₂m measurable_const)))
      have hhb : ∃ C : ℝ, ∀ x, |hh x| ≤ C := by
        refine ⟨1, fun x => ?_⟩
        simp only [hh_def, Pi.sub_apply]
        by_cases h1 : x ∈ ball (0 : Eucl N) R ∩ {x | 0 < g₂ x}
        · have h2 : x ∉ ball (0 : Eucl N) R ∩ {x | g₂ x < 0} := fun h' => by
            have := h1.2; have := h'.2; simp only [mem_setOf_eq] at *; linarith
          simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        · by_cases h2 : x ∈ ball (0 : Eucl N) R ∩ {x | g₂ x < 0}
          · simp [Set.indicator_of_mem h2, Set.indicator_of_notMem h1]
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hhO : ∀ x, x ∉ ball (0 : Eucl N) R → hh x = 0 := by
        intro x hx
        have h1 : x ∉ ball (0 : Eucl N) R ∩ {x | 0 < g₂ x} := fun h' => hx h'.1
        have h2 : x ∉ ball (0 : Eucl N) R ∩ {x | g₂ x < 0} := fun h' => hx h'.1
        simp [hh_def, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hint := hbdd hh hhm hhb hhO
      simp only [Pi.zero_apply, mul_zero, integral_zero] at hint
      -- `hh * g₁ = |g₁|` a.e.
      have habs : (fun x => hh x * g₁ x) =ᵐ[μ₀] fun x => |g₁ x| := by
        filter_upwards [hg₁₂] with x hx
        by_cases hxb : x ∈ ball (0 : Eucl N) R
        · rcases lt_trichotomy (g₂ x) 0 with hneg | hzero | hpos
          · have h1 : x ∉ ball (0 : Eucl N) R ∩ {x | 0 < g₂ x} := fun h' => by
              have := h'.2; simp only [mem_setOf_eq] at this; linarith
            have h2 : x ∈ ball (0 : Eucl N) R ∩ {x | g₂ x < 0} := ⟨hxb, hneg⟩
            simp only [hh_def, Pi.sub_apply, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Pi.one_apply]
            rw [hx, abs_of_neg hneg]; ring
          · rw [hx, hzero]; simp
          · have h1 : x ∈ ball (0 : Eucl N) R ∩ {x | 0 < g₂ x} := ⟨hxb, hpos⟩
            have h2 : x ∉ ball (0 : Eucl N) R ∩ {x | g₂ x < 0} := fun h' => by
              have := h'.2; simp only [mem_setOf_eq] at this; linarith
            simp only [hh_def, Pi.sub_apply, Set.indicator_of_notMem h2, Set.indicator_of_mem h1,
              Pi.one_apply]
            rw [hx, abs_of_pos hpos]; ring
        · have hxU : x ∉ U := fun h' => hxb h'.2
          have : g₁ x = 0 := by simp [hg₁_def, Set.indicator_of_notMem hxU]
          rw [this, hhO x hxb]; simp
      have hzero : ∫ x, |g₁ x| ∂μ₀ = 0 := by
        rw [← integral_congr_ae habs, hint]
      have hae : (fun x => |g₁ x|) =ᵐ[μ₀] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hg₁.abs).1 hzero
      filter_upwards [hae] with x hx hxU
      have : |g₁ x| = 0 := hx
      rw [abs_eq_zero] at this
      simpa [hg₁_def, Set.indicator_of_mem hxU] using this
    rw [← ae_all_iff] at hR
    filter_upwards [hR] with x hx hxS
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    exact hx R ⟨hxS, by rw [mem_ball, dist_zero_right]; exact hR⟩
  -- Local integrability of `v₀ · W` for a measure representation.
  have skp_rep_integrableOn : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ₀ : Measure (Eucl N)) (v₀ : Eucl N → NVector (Eucl N) k) (hrep : IsMeasureRepresentation T μ₀ v₀) (W : Covector (Eucl N) k) (R : ℝ), IntegrableOn (fun x => v₀ x W) (closedBall 0 R) μ₀ := by
    clear * - skp_scalar_form_mem
    revert skp_scalar_form_mem
    refine id ?_
    intro skp_scalar_form_mem N k T μ₀ v₀ hrep W R
    -- a smooth bump equal to `1` on `closedBall 0 R`
    obtain ⟨φ, hφ1, hφ2, hφ3, hφ4⟩ : ∃ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
        (∀ x ∈ closedBall (0 : Eucl N) R, φ x = 1) ∧ True := by
      by_cases hR : 0 < R
      · let b : ContDiffBump (0 : Eucl N) := ⟨R, R + 1, hR, by linarith⟩
        exact ⟨b, b.contDiff, b.hasCompactSupport, fun x hx => b.one_of_mem_closedBall hx, trivial⟩
      · let b : ContDiffBump (0 : Eucl N) := ⟨1, 2, one_pos, by norm_num⟩
        refine ⟨b, b.contDiff, b.hasCompactSupport, fun x hx => b.one_of_mem_closedBall ?_, trivial⟩
        exact closedBall_subset_closedBall (by linarith) hx
    have hmem := skp_scalar_form_mem φ hφ1 hφ2 W
    have hint := (hrep ⟨_, hmem⟩).1
    have hint' : Integrable (fun x => φ x * v₀ x W) μ₀ := by
      refine hint.congr (Eventually.of_forall fun x => ?_)
      simp [map_smul]
    refine (hint'.integrableOn).congr_fun (fun x hx => ?_) measurableSet_closedBall
    simp [hφ3 x hx]
  have skp_hyperplane : ∀ {N m : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbT : T.boundary.mass < ∞) (μ₀ : Measure (Eucl N)) (v₀ : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation T μ₀ v₀) (j : Fin N) (c : ℝ) (β : Fin m → (Eucl N →L[ℝ] ℝ)), ∀ᵐ x ∂μ₀, x j = c →
        v₀ x (wedgeCovectors (m + 1) (Fin.cons (EuclideanSpace.proj j) β)) = 0 := by
    clear * - skp_cnorm_smul skp_coord_continuous skp_scalar_form_mem skp_extDeriv_smul_const skp_smulRight_add skp_smulRight_smul skp_sigma_hasDerivAt skp_sigma_contDiff skp_sigma_abs_le skp_sigma'_le_one skp_sigma'_tendsto skp_ae_zero_of_smooth skp_rep_integrableOn
    revert skp_cnorm_smul skp_coord_continuous skp_scalar_form_mem skp_extDeriv_smul_const skp_smulRight_add skp_smulRight_smul skp_sigma_hasDerivAt skp_sigma_contDiff skp_sigma_abs_le skp_sigma'_le_one skp_sigma'_tendsto skp_ae_zero_of_smooth skp_rep_integrableOn
    refine id ?_
    intro skp_cnorm_smul skp_coord_continuous skp_scalar_form_mem skp_extDeriv_smul_const skp_smulRight_add skp_smulRight_smul skp_sigma_hasDerivAt skp_sigma_contDiff skp_sigma_abs_le skp_sigma'_le_one skp_sigma'_tendsto skp_ae_zero_of_smooth skp_rep_integrableOn N m T hbT μ₀ v₀ hrep j c β
    set B := wedgeCovectors (m + 1) (Fin.cons (EuclideanSpace.proj j) β) with hB
    set B' := wedgeCovectors m β with hB'
    have hBalt : B = ContinuousAlternatingMap.alternatizeUncurryFin
        ((EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ).smulRight B') := by
      rw [hB, hB']
      rfl
    set S : Set (Eucl N) := {y | y j = c} with hS
    have hSm : MeasurableSet S := measurableSet_eq_fun (skp_coord_continuous j).measurable measurable_const
    refine skp_ae_zero_of_smooth μ₀ (fun x => v₀ x B) S hSm
      (fun R => skp_rep_integrableOn T μ₀ v₀ hrep B R) ?_
    intro f hf hfc
    -- the forms
    have hfd : ∀ x, DifferentiableAt ℝ f x := fun x => (hf.differentiable (by simp)) x
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ → ℝ, ∀ ε t, σ ε t = ε * Real.arctan ((t - c) / ε) :=
      ⟨_, fun _ _ => rfl⟩
    obtain ⟨σ', hσ'⟩ : ∃ σ' : ℝ → ℝ → ℝ, ∀ ε t, σ' ε t = 1 / (1 + ((t - c) / ε) ^ 2) :=
      ⟨_, fun _ _ => rfl⟩
    have hσfun : ∀ ε, σ ε = fun t => ε * Real.arctan ((t - c) / ε) := fun ε => funext (hσ ε)
    have hσ'fun : ∀ ε, σ' ε = fun t => 1 / (1 + ((t - c) / ε) ^ 2) := fun ε => funext (hσ' ε)
    have hσs : ∀ ε, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (σ ε) := fun ε => by
      rw [hσfun]; exact skp_sigma_contDiff ε c
    have hσ's : ∀ ε, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (σ' ε) := fun ε => by
      rw [hσ'fun]
      exact contDiff_const.div (contDiff_const.add ((((contDiff_id.sub contDiff_const).div_const ε)).pow 2))
        (fun t => by positivity)
    -- `G ε = (σ ε (x j) * f x) • B'`
    have hGsmooth : ∀ ε, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl N => σ ε (x j) * f x) := fun ε =>
      ((hσs ε).comp (EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ).contDiff).mul hf
    have hGc : ∀ ε, HasCompactSupport (fun x : Eucl N => σ ε (x j) * f x) := fun ε =>
      hfc.mul_left
    have hω₁smooth : ∀ ε, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Eucl N => f x * σ' ε (x j)) := by
      intro ε
      exact hf.mul ((hσ's ε).comp (EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ).contDiff)
    have hω₁c : ∀ ε, HasCompactSupport (fun x : Eucl N => f x * σ' ε (x j)) := fun ε =>
      hfc.mul_right
    let G : ℝ → TestFormOn (univ : Set (Eucl N)) m := fun ε =>
      ⟨fun x => (σ ε (x j) * f x) • B', skp_scalar_form_mem _ (hGsmooth ε) (hGc ε) B'⟩
    let ω₁ : ℝ → TestFormOn (univ : Set (Eucl N)) (m + 1) := fun ε =>
      ⟨fun x => (f x * σ' ε (x j)) • B, skp_scalar_form_mem _ (hω₁smooth ε) (hω₁c ε) B⟩
    let G₀ : TestFormOn (univ : Set (Eucl N)) m := ⟨fun x => f x • B', skp_scalar_form_mem _ hf hfc B'⟩
    let ω₃ : TestFormOn (univ : Set (Eucl N)) (m + 1) := exteriorDerivativeTestOn univ m G₀
    have hω₃ : ∀ x, (ω₃ : DifferentialForm (Eucl N) (m + 1)) x =
        ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ f x).smulRight B') := by
      intro x
      exact skp_extDeriv_smul_const f B' x (hfd x)
    -- the key identity `dG = ω₁ + σ ω₃`
    have hdG : ∀ ε, ε ≠ 0 → ∀ x, ((exteriorDerivativeTestOn univ m (G ε) :
        TestFormOn (univ : Set (Eucl N)) (m + 1)) : DifferentialForm (Eucl N) (m + 1)) x =
        (f x * σ' ε (x j)) • B + σ ε (x j) • (ω₃ : DifferentialForm (Eucl N) (m + 1)) x := by
      intro ε hε x
      have hσd : HasDerivAt (σ ε) (σ' ε (x j)) (x j) := by
        rw [hσfun, hσ']; exact skp_sigma_hasDerivAt ε c (x j) hε
      have hcomp : HasFDerivAt (fun y : Eucl N => σ ε (y j))
          (σ' ε (x j) • (EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ)) x :=
        hσd.comp_hasFDerivAt x (EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ).hasFDerivAt
      have hprod : HasFDerivAt (fun y : Eucl N => σ ε (y j) * f y)
          (σ ε (x j) • fderiv ℝ f x + f x • (σ' ε (x j) • (EuclideanSpace.proj j : Eucl N →L[ℝ] ℝ)))
          x := hcomp.mul (hfd x).hasFDerivAt
      change extDeriv (fun y => (σ ε (y j) * f y) • B') x = _
      rw [skp_extDeriv_smul_const _ B' x hprod.differentiableAt, hprod.fderiv, hω₃,
        skp_smulRight_add, skp_smulRight_smul, skp_smulRight_smul, skp_smulRight_smul, smul_smul,
        ContinuousAlternatingMap.alternatizeUncurryFin_add,
        ContinuousAlternatingMap.alternatizeUncurryFin_smul,
        ContinuousAlternatingMap.alternatizeUncurryFin_smul, ← hBalt]
      exact add_comm _ _
    -- representation formula for the pieces
    have hrepω₁ : ∀ ε, T (ω₁ ε) = ∫ x, f x * σ' ε (x j) * v₀ x B ∂μ₀ := by
      intro ε
      rw [(hrep (ω₁ ε)).2]
      congr 1; funext x
      change v₀ x ((f x * σ' ε (x j)) • B) = _
      rw [map_smul, smul_eq_mul]
    have hω₃int : Integrable (fun x => v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)) μ₀ :=
      (hrep ω₃).1
    -- the main estimate: `|∫ f σ' v₀ B| ≤ ε K`
    obtain ⟨Kf, hKf⟩ : ∃ K : ℝ, ∀ x, |f x| ≤ K := by
      obtain ⟨K, hK⟩ := hfc.exists_bound_of_continuous hf.continuous
      exact ⟨K, fun x => by simpa [Real.norm_eq_abs] using hK x⟩
    have hKf0 : 0 ≤ Kf := (abs_nonneg _).trans (hKf 0)
    have hbound : ∀ ε, 0 < ε → |∫ x, f x * σ' ε (x j) * v₀ x B ∂μ₀| ≤
        ε * ((T.boundary.mass.toReal * (Kf * (Real.pi / 2) * covectorEuclideanNorm B')) +
          (Real.pi / 2) * ∫ x, |v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀) := by
      intro ε hε
      have hdecomp : exteriorDerivativeTestOn univ m (G ε) = ω₁ ε + (exteriorDerivativeTestOn univ m (G ε) - ω₁ ε) := by
        abel
      have hT1 : T.boundary (G ε) = T (ω₁ ε) + T (exteriorDerivativeTestOn univ m (G ε) - ω₁ ε) := by
        rw [GeometricCurrentOn.boundary_apply]
        conv_lhs => rw [hdecomp]
        rw [map_add]
      have hrest : T (exteriorDerivativeTestOn univ m (G ε) - ω₁ ε) =
          ∫ x, σ ε (x j) * v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x) ∂μ₀ := by
        rw [(hrep _).2]
        congr 1; funext x
        have := hdG ε hε.ne' x
        change v₀ x (((exteriorDerivativeTestOn univ m (G ε) : TestFormOn (univ : Set (Eucl N)) (m + 1)) :
          DifferentialForm (Eucl N) (m + 1)) x - (f x * σ' ε (x j)) • B) = _
        rw [this, add_sub_cancel_left, map_smul, smul_eq_mul]
      -- bound on the boundary term
      have hGnorm : ∀ x, covectorEuclideanNorm (((G ε : TestFormOn (univ : Set (Eucl N)) m) :
          DifferentialForm (Eucl N) m) x) ≤ ε * (Kf * (Real.pi / 2) * covectorEuclideanNorm B') := by
        intro x
        change covectorEuclideanNorm ((σ ε (x j) * f x) • B') ≤ _
        rw [skp_cnorm_smul, abs_mul]
        have h1 : |σ ε (x j)| ≤ ε * (Real.pi / 2) := by
          rw [hσ]; exact skp_sigma_abs_le ε c (x j) hε
        have h2 := hKf x
        have h3 := covectorEuclideanNorm_nonneg B'
        calc |σ ε (x j)| * |f x| * covectorEuclideanNorm B'
            ≤ (ε * (Real.pi / 2)) * Kf * covectorEuclideanNorm B' := by gcongr
          _ = ε * (Kf * (Real.pi / 2) * covectorEuclideanNorm B') := by ring
      have hbT' : T.boundary.massOn univ ≤ ENNReal.ofReal T.boundary.mass.toReal := by
        rw [ENNReal.ofReal_toReal hbT.ne]; rfl
      have hB1 := Submission.cmb_abs_apply_le_of_massOn_le N m univ univ T.boundary (G ε)
        T.boundary.mass.toReal _ ENNReal.toReal_nonneg hbT' (subset_univ _) hGnorm
      -- bound on the rest
      have hB2 : |∫ x, σ ε (x j) * v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x) ∂μ₀| ≤
          ε * ((Real.pi / 2) * ∫ x, |v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀) := by
        calc _ ≤ ∫ x, |σ ε (x j) * v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀ :=
              abs_integral_le_integral_abs
          _ ≤ ∫ x, (ε * (Real.pi / 2)) * |v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀ := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
                (hω₃int.abs.const_mul _) (Eventually.of_forall fun x => ?_)
              dsimp only
              rw [abs_mul]
              gcongr
              rw [hσ]; exact skp_sigma_abs_le ε c (x j) hε
          _ = ε * ((Real.pi / 2) * ∫ x, |v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀) := by
              rw [integral_const_mul]; ring
      have : ∫ x, f x * σ' ε (x j) * v₀ x B ∂μ₀ = T.boundary (G ε) -
          ∫ x, σ ε (x j) * v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x) ∂μ₀ := by
        rw [hT1, hrest, ← hrepω₁]; ring
      rw [this]
      calc _ ≤ |T.boundary (G ε)| + |∫ x, σ ε (x j) * v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x) ∂μ₀| :=
            abs_sub _ _
        _ ≤ _ := by
            have := add_le_add hB1 hB2
            linarith
    -- pass to the limit `ε = 1/(k+1) → 0`
    set K := (T.boundary.mass.toReal * (Kf * (Real.pi / 2) * covectorEuclideanNorm B')) +
          (Real.pi / 2) * ∫ x, |v₀ x ((ω₃ : DifferentialForm (Eucl N) (m + 1)) x)| ∂μ₀ with hK
    have hfB : Integrable (fun x => f x * v₀ x B) μ₀ := by
      have := (hrep ⟨_, skp_scalar_form_mem f hf hfc B⟩).1
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [map_smul]
    have hlim : Tendsto (fun k : ℕ => ∫ x, f x * σ' (1 / ((k : ℝ) + 1)) (x j) * v₀ x B ∂μ₀) atTop
        (𝓝 (∫ x, S.indicator 1 x * (f x * v₀ x B) ∂μ₀)) := by
      have hre : ∀ k : ℕ, (fun x => f x * σ' (1 / ((k : ℝ) + 1)) (x j) * v₀ x B) =
          fun x => σ' (1 / ((k : ℝ) + 1)) (x j) * (f x * v₀ x B) := by
        intro k; funext x; ring
      simp_rw [hre]
      refine tendsto_integral_of_dominated_convergence (fun x => |f x * v₀ x B|) ?_ hfB.abs ?_ ?_
      · intro k
        exact (((hσ's _).continuous.comp (skp_coord_continuous j)).aestronglyMeasurable).mul
          hfB.aestronglyMeasurable
      · intro k
        refine Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_mul]
        have h : 0 ≤ σ' (1 / ((k : ℝ) + 1)) (x j) ∧ σ' (1 / ((k : ℝ) + 1)) (x j) ≤ 1 := by
          rw [hσ']; exact skp_sigma'_le_one (1 / ((k : ℝ) + 1)) c (x j)
        rw [abs_of_nonneg h.1]
        calc _ ≤ 1 * |f x * v₀ x B| := by gcongr; exact h.2
          _ = _ := one_mul _
      · refine Eventually.of_forall fun x => ?_
        have h := (skp_sigma'_tendsto c (x j)).mul_const (f x * v₀ x B)
        simp only [← hσ'] at h
        convert h using 2
        by_cases hx : x j = c
        · simp [hS, Set.indicator_of_mem (show x ∈ S from hx), hx]
        · simp [hS, Set.indicator_of_notMem (show x ∉ S from hx), hx]
    have hlim0 : Tendsto (fun k : ℕ => ∫ x, f x * σ' (1 / ((k : ℝ) + 1)) (x j) * v₀ x B ∂μ₀)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero (fun k => abs_nonneg _) (fun k => hbound _ (by positivity)) ?_
      have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this.mul_const K
    exact tendsto_nhds_unique hlim hlim0
  have skp_line_apply : ∀ {n : ℕ} (u : Eucl n) (t : ℝ) (k j : Fin n), (u + t • EuclideanSpace.single k (1 : ℝ)) j = u j + if j = k then t else 0 := by
    clear * -
    intro n u t k j
    simp [EuclideanSpace.single_apply]
  have skp_line_apply_self : ∀ {n : ℕ} (u : Eucl n) (t : ℝ) (k : Fin n), (u + t • EuclideanSpace.single k (1 : ℝ)) k = u k + t := by
    clear * - skp_line_apply
    revert skp_line_apply
    refine id ?_
    intro skp_line_apply n u t k
    rw [skp_line_apply]; simp
  have skp_line_apply_ne : ∀ {n : ℕ} (u : Eucl n) (t : ℝ) {k j : Fin n} (h : j ≠ k), (u + t • EuclideanSpace.single k (1 : ℝ)) j = u j := by
    clear * - skp_line_apply
    revert skp_line_apply
    refine id ?_
    intro skp_line_apply n u t k j h
    rw [skp_line_apply]; simp [h]
  have skp_line_add : ∀ {n : ℕ} (u : Eucl n) (s t : ℝ) (k : Fin n), u + s • EuclideanSpace.single k (1 : ℝ) + t • EuclideanSpace.single k (1 : ℝ) =
        u + (s + t) • EuclideanSpace.single k (1 : ℝ) := by
    clear * -
    intro n u s t k
    rw [add_smul, add_assoc]
  have skp_line_hasDerivAt : ∀ {n : ℕ} (G : Eucl n → ℝ) (u v : Eucl n) (hG : DifferentiableAt ℝ G u), HasDerivAt (fun t : ℝ => G (u + t • v)) (fderiv ℝ G u v) 0 := by
    clear * -
    intro n G u v hG
    have hline : HasDerivAt (fun t : ℝ => u + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
    have hG' : HasFDerivAt G (fderiv ℝ G u) (u + (0 : ℝ) • v) := by
      simpa using hG.hasFDerivAt
    exact hG'.comp_hasDerivAt (0 : ℝ) hline
  have skp_indicator_one_mul : ∀ {α : Type} (S : Set α) (f : α → ℝ) (x : α), S.indicator 1 x * f x = S.indicator f x := by
    clear * -
    intro α S f x
    by_cases h : x ∈ S <;> simp [h]
  have skp_abs_coord_le_norm : ∀ {n : ℕ} (u : Eucl n) (j : Fin n), |u j| ≤ ‖u‖ := by
    clear * - skp_abs_coord_le
    revert skp_abs_coord_le
    refine id ?_
    intro skp_abs_coord_le n u j
    have := skp_abs_coord_le u 0 j
    simpa [dist_zero_right] using this
  have skp_norm_smul_single : ∀ {n : ℕ} (c : ℝ) (k : Fin n), ‖c • EuclideanSpace.single k (1 : ℝ)‖ = |c| := by
    clear * -
    intro n c k
    rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  have skp_isCompact_box : ∀ {n : ℕ} (lo hi : Fin n → ℝ), IsCompact {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} := by
    clear * -
    intro n lo hi
    have : {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} =
        WithLp.toLp 2 '' Set.pi univ (fun j => Icc (lo j) (hi j)) := by
      ext u
      constructor
      · intro hu
        exact ⟨WithLp.ofLp u, fun j _ => hu j, by simp⟩
      · rintro ⟨v, hv, rfl⟩ j
        exact hv j (mem_univ j)
    rw [this]
    exact (isCompact_univ_pi fun j => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have skp_isClosed_box : ∀ {n : ℕ} (lo hi : Fin n → ℝ), IsClosed {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} := by
    clear * - skp_isCompact_box
    revert skp_isCompact_box
    refine id ?_
    intro skp_isCompact_box n lo hi
    exact (skp_isCompact_box lo hi).isClosed
  have skp_isOpen_cube : ∀ (n : ℕ), IsOpen {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skp_coord_continuous
    revert skp_coord_continuous
    refine id ?_
    intro skp_coord_continuous n
    have : {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} =
        ⋂ j : Fin n, ({u : Eucl n | 0 < u j} ∩ {u | u j < 1}) := by
      ext u; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j =>
      (isOpen_lt continuous_const (skp_coord_continuous j)).inter
        (isOpen_lt (skp_coord_continuous j) continuous_const)
  have skp_measurableSet_cube : ∀ (n : ℕ), MeasurableSet {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skp_isOpen_cube
    revert skp_isOpen_cube
    refine id ?_
    intro skp_isOpen_cube n
    exact (skp_isOpen_cube n).measurableSet
  have skp_volume_cube : ∀ (n : ℕ), volume {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} = 1 := by
    clear * -
    intro n
    have hQ : {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} =
        WithLp.ofLp ⁻¹' Set.pi univ (fun _ : Fin n => Ioo (0 : ℝ) 1) := by
      ext u; simp
    rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have skp_cube_finite : ∀ (n : ℕ), IsFiniteMeasure (volume.restrict {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) := by
    clear * - skp_volume_cube
    revert skp_volume_cube
    refine id ?_
    intro skp_volume_cube n
    exact ⟨by rw [Measure.restrict_apply_univ, skp_volume_cube]; exact ENNReal.one_lt_top⟩
  -- Per-coordinate margins of a compact subset of the open cube.
  have skp_compact_in_cube : ∀ {n : ℕ} (K : Set (Eucl n)) (hK : IsCompact K) (hKc : K ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) (j : Fin n), ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ 1 / 4 ∧ 3 / 4 ≤ hi ∧ hi < 1 ∧ ∀ u ∈ K, lo ≤ u j ∧ u j ≤ hi := by
    clear * - skp_coord_continuous skp_cube_finite
    revert skp_coord_continuous skp_cube_finite
    refine id ?_
    intro skp_coord_continuous skp_cube_finite n K hK hKc j
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨1 / 4, 3 / 4, by norm_num, le_rfl, le_rfl, by norm_num, by simp [hK0]⟩
    obtain ⟨a, haK, ha⟩ := hK.exists_isMinOn hKne (skp_coord_continuous j).continuousOn
    obtain ⟨b, hbK, hb⟩ := hK.exists_isMaxOn hKne (skp_coord_continuous j).continuousOn
    refine ⟨min (a j) (1 / 4), max (b j) (3 / 4), lt_min (hKc haK j).1 (by norm_num),
      min_le_right _ _, le_max_right _ _, max_lt (hKc hbK j).2 (by norm_num), fun u hu => ?_⟩
    exact ⟨(min_le_left _ _).trans (ha hu), (hb hu).trans (le_max_left _ _)⟩
  let skpH : ∀ (t : ℝ), ℝ :=
      fun (t : ℝ) => Real.smoothTransition (4 * t - 1)
  have skpH_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) skpH := by
    clear * - skp_cube_finite skpH
    revert skp_cube_finite skpH
    refine id ?_
    intro skp_cube_finite skpH
    exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
          ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have skpH_zero : ∀ {t : ℝ} (ht : t ≤ 1 / 4), skpH t = 0 := by
    clear * - skp_cube_finite skpH
    revert skp_cube_finite skpH
    refine id ?_
    intro skp_cube_finite skpH t ht
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have skpH_one : ∀ {t : ℝ} (ht : 1 / 2 ≤ t), skpH t = 1 := by
    clear * - skp_cube_finite skpH
    revert skp_cube_finite skpH
    refine id ?_
    intro skp_cube_finite skpH t ht
    exact Real.smoothTransition.one_of_one_le (by linarith)
  have skpH_nonneg : ∀ (t : ℝ), 0 ≤ skpH t := by
    clear * - skp_cube_finite skpH
    revert skp_cube_finite skpH
    refine id ?_
    intro skp_cube_finite skpH t
    exact Real.smoothTransition.nonneg _
  have skpH_le_one : ∀ (t : ℝ), skpH t ≤ 1 := by
    clear * - skp_cube_finite skpH
    revert skp_cube_finite skpH
    refine id ?_
    intro skp_cube_finite skpH t
    exact Real.smoothTransition.le_one _
  have skpH_differentiable : Differentiable ℝ skpH := by
    clear * - skp_cube_finite skpH skpH_contDiff
    revert skp_cube_finite skpH skpH_contDiff
    refine id ?_
    intro skp_cube_finite skpH skpH_contDiff
    exact skpH_contDiff.differentiable (by simp)
  have skpH_deriv_continuous : Continuous (deriv skpH) := by
    clear * - skp_cube_finite skpH skpH_contDiff
    revert skp_cube_finite skpH skpH_contDiff
    refine id ?_
    intro skp_cube_finite skpH skpH_contDiff
    exact skpH_contDiff.continuous_deriv (by simp)
  have skpH_deriv_zero : ∀ {t : ℝ} (ht : t < 1 / 4 ∨ 1 / 2 < t), deriv skpH t = 0 := by
    clear * - skp_cube_finite skpH skpH_zero skpH_one
    revert skp_cube_finite skpH skpH_zero skpH_one
    refine id ?_
    intro skp_cube_finite skpH skpH_zero skpH_one t ht
    rcases ht with ht | ht
    · have : skpH =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs using skpH_zero (le_of_lt hs)
      rw [this.deriv_eq]; simp
    · have : skpH =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs using skpH_one (le_of_lt hs)
      rw [this.deriv_eq]; simp
  have skpH_deriv_hasCompactSupport : HasCompactSupport (deriv skpH) := by
    clear * - skp_cube_finite skpH skpH_deriv_zero
    revert skp_cube_finite skpH skpH_deriv_zero
    refine id ?_
    intro skp_cube_finite skpH skpH_deriv_zero
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1 / 2)) fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    exact skpH_deriv_zero ht
  have skpH_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv skpH t| ≤ M := by
    clear * - skp_cube_finite skpH skpH_deriv_continuous skpH_deriv_hasCompactSupport
    revert skp_cube_finite skpH skpH_deriv_continuous skpH_deriv_hasCompactSupport
    refine id ?_
    intro skp_cube_finite skpH skpH_deriv_continuous skpH_deriv_hasCompactSupport
    obtain ⟨M, hM⟩ := skpH_deriv_hasCompactSupport.exists_bound_of_continuous
      skpH_deriv_continuous
    exact ⟨M, (norm_nonneg _).trans (hM 0), fun t => by simpa [Real.norm_eq_abs] using hM t⟩
  -- The one-dimensional cut-off `χ_ε` on `(0, 1)`.
  let skpChi : ∀ (ε t : ℝ), ℝ :=
      fun (ε t : ℝ) => skpH (t / ε) * skpH ((1 - t) / ε)
  have skpChi_contDiff : ∀ (ε : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (skpChi ε) := by
    clear * - skp_cube_finite skpH skpH_contDiff skpChi
    revert skp_cube_finite skpH skpH_contDiff skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_contDiff skpChi ε
    unfold skpChi
    exact (skpH_contDiff.comp (contDiff_id.div_const ε)).mul
      (skpH_contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))
  have skpChi_nonneg : ∀ (ε t : ℝ), 0 ≤ skpChi ε t := by
    clear * - skp_cube_finite skpH skpH_nonneg skpChi
    revert skp_cube_finite skpH skpH_nonneg skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_nonneg skpChi ε t
    exact mul_nonneg (skpH_nonneg _) (skpH_nonneg _)
  have skpChi_le_one : ∀ (ε t : ℝ), skpChi ε t ≤ 1 := by
    clear * - skp_cube_finite skpH skpH_nonneg skpH_le_one skpChi
    revert skp_cube_finite skpH skpH_nonneg skpH_le_one skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_nonneg skpH_le_one skpChi ε t
    unfold skpChi
    calc skpH (t / ε) * skpH ((1 - t) / ε) ≤ 1 * 1 :=
          mul_le_mul (skpH_le_one _) (skpH_le_one _) (skpH_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have skpChi_zero : ∀ {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ ε / 4 ∨ 1 - ε / 4 ≤ t), skpChi ε t = 0 := by
    clear * - skp_cube_finite skpH skpH_zero skpChi
    revert skp_cube_finite skpH skpH_zero skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_zero skpChi ε t hε ht
    unfold skpChi
    rcases ht with ht | ht
    · rw [skpH_zero (t := t / ε) (by rw [div_le_iff₀ hε]; linarith), zero_mul]
    · rw [skpH_zero (t := (1 - t) / ε) (by rw [div_le_iff₀ hε]; linarith), mul_zero]
  have skpChi_one : ∀ {ε t : ℝ} (hε : 0 < ε) (h1 : ε / 2 ≤ t) (h2 : t ≤ 1 - ε / 2), skpChi ε t = 1 := by
    clear * - skp_cube_finite skpH skpH_one skpChi
    revert skp_cube_finite skpH skpH_one skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_one skpChi ε t hε h1 h2
    unfold skpChi
    rw [skpH_one (t := t / ε) (by rw [le_div_iff₀ hε]; linarith),
      skpH_one (t := (1 - t) / ε) (by rw [le_div_iff₀ hε]; linarith), mul_one]
  have skpChi_deriv_zero : ∀ {ε t : ℝ} (hε : 0 < ε) (h1 : ε / 2 < t) (h2 : t < 1 - ε / 2), deriv (skpChi ε) t = 0 := by
    clear * - skp_cube_finite skpH skpChi skpChi_one
    revert skp_cube_finite skpH skpChi skpChi_one
    refine id ?_
    intro skp_cube_finite skpH skpChi skpChi_one ε t hε h1 h2
    have : skpChi ε =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds h1 h2] with s hs using skpChi_one hε hs.1.le hs.2.le
    rw [this.deriv_eq]; simp
  have skpChi_deriv_bound : ∀ {ε : ℝ} (hε : 0 < ε) (M : ℝ) (hM : ∀ t, |deriv skpH t| ≤ M) (t : ℝ), |deriv (skpChi ε) t| ≤ 2 * M / ε := by
    clear * - skp_cube_finite skpH skpH_nonneg skpH_le_one skpH_differentiable skpChi
    revert skp_cube_finite skpH skpH_nonneg skpH_le_one skpH_differentiable skpChi
    refine id ?_
    intro skp_cube_finite skpH skpH_nonneg skpH_le_one skpH_differentiable skpChi ε hε M hM t
    have h1 : HasDerivAt (fun s => skpH (s / ε)) (deriv skpH (t / ε) * (1 / ε)) t :=
      (skpH_differentiable _).hasDerivAt.comp t ((hasDerivAt_id t).div_const ε |>.congr_deriv
        (by simp))
    have h2 : HasDerivAt (fun s => skpH ((1 - s) / ε)) (deriv skpH ((1 - t) / ε) * (-1 / ε)) t :=
      (skpH_differentiable _).hasDerivAt.comp t
        (((hasDerivAt_id t).const_sub 1).div_const ε |>.congr_deriv (by simp [neg_div]))
    have h3 : HasDerivAt (fun s => skpH (s / ε) * skpH ((1 - s) / ε))
        (deriv skpH (t / ε) * (1 / ε) * skpH ((1 - t) / ε) +
          skpH (t / ε) * (deriv skpH ((1 - t) / ε) * (-1 / ε))) t := h1.mul h2
    have hderiv : deriv (skpChi ε) t = deriv skpH (t / ε) * (1 / ε) * skpH ((1 - t) / ε) +
        skpH (t / ε) * (deriv skpH ((1 - t) / ε) * (-1 / ε)) := by
      have : skpChi ε = fun s => skpH (s / ε) * skpH ((1 - s) / ε) := rfl
      rw [this, h3.deriv]
    rw [hderiv]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have a1 := hM (t / ε)
    have a2 := hM ((1 - t) / ε)
    have b1 := skpH_nonneg ((1 - t) / ε)
    have b2 := skpH_le_one ((1 - t) / ε)
    have b3 := skpH_nonneg (t / ε)
    have b4 := skpH_le_one (t / ε)
    have hεinv : 0 < 1 / ε := by positivity
    calc |deriv skpH (t / ε) * (1 / ε) * skpH ((1 - t) / ε) +
          skpH (t / ε) * (deriv skpH ((1 - t) / ε) * (-1 / ε))|
        ≤ |deriv skpH (t / ε) * (1 / ε) * skpH ((1 - t) / ε)| +
          |skpH (t / ε) * (deriv skpH ((1 - t) / ε) * (-1 / ε))| := abs_add_le _ _
      _ ≤ M * (1 / ε) * 1 + 1 * (M * (1 / ε)) := by
          gcongr
          · rw [abs_mul, abs_mul, abs_of_pos hεinv, abs_of_nonneg b1]
            gcongr
          · rw [abs_mul, abs_mul, abs_of_nonneg b3, neg_div, abs_neg, abs_of_pos hεinv]
            gcongr
      _ = 2 * M / ε := by field_simp; ring
  -- The cube cut-off `ψ_ε(u) = ∏_j χ_ε(u_j)`.
  let skpPsi : ∀ {n : ℕ} (ε : ℝ) (u : Eucl n), ℝ :=
      fun {n : ℕ} (ε : ℝ) (u : Eucl n) => ∏ j, skpChi ε (u j)
  have skpPsi_contDiff : ∀ {n : ℕ} (ε : ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (skpPsi (n := n) ε) := by
    clear * - skp_cube_finite skpH skpChi skpChi_contDiff skpPsi
    revert skp_cube_finite skpH skpChi skpChi_contDiff skpPsi
    refine id ?_
    intro skp_cube_finite skpH skpChi skpChi_contDiff skpPsi n ε
    unfold skpPsi
    exact contDiff_prod fun j _ =>
      (skpChi_contDiff ε).comp (EuclideanSpace.proj j : Eucl n →L[ℝ] ℝ).contDiff
  have skpPsi_nonneg : ∀ {n : ℕ} (ε : ℝ) (u : Eucl n), 0 ≤ skpPsi ε u := by
    clear * - skp_cube_finite skpH skpChi skpChi_nonneg skpPsi
    revert skp_cube_finite skpH skpChi skpChi_nonneg skpPsi
    refine id ?_
    intro skp_cube_finite skpH skpChi skpChi_nonneg skpPsi n ε u
    exact Finset.prod_nonneg fun j _ => skpChi_nonneg ε _
  have skpPsi_le_one : ∀ {n : ℕ} (ε : ℝ) (u : Eucl n), skpPsi ε u ≤ 1 := by
    clear * - skp_cube_finite skpH skpChi skpChi_nonneg skpChi_le_one skpPsi
    revert skp_cube_finite skpH skpChi skpChi_nonneg skpChi_le_one skpPsi
    refine id ?_
    intro skp_cube_finite skpH skpChi skpChi_nonneg skpChi_le_one skpPsi n ε u
    exact Finset.prod_le_one₀ (fun j _ => skpChi_nonneg ε _) (fun j _ => skpChi_le_one ε _)
  have skpPsi_support : ∀ {n : ℕ} {ε : ℝ} (hε : 0 < ε), tsupport (skpPsi (n := n) ε) ⊆ {u : Eucl n | ∀ j, ε / 4 ≤ u j ∧ u j ≤ 1 - ε / 4} := by
    clear * - skp_isClosed_box skp_cube_finite skpH skpChi skpChi_zero skpPsi
    revert skp_isClosed_box skp_cube_finite skpH skpChi skpChi_zero skpPsi
    refine id ?_
    intro skp_isClosed_box skp_cube_finite skpH skpChi skpChi_zero skpPsi n ε hε
    apply closure_minimal _ (skp_isClosed_box _ _)
    intro u hu j
    by_contra hj
    apply hu
    unfold skpPsi
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply skpChi_zero hε
    rcases not_and_or.1 hj with h | h
    · left; exact (not_le.1 h).le
    · right; exact (not_le.1 h).le
  have skpPsi_hasCompactSupport : ∀ {n : ℕ} {ε : ℝ} (hε : 0 < ε), HasCompactSupport (skpPsi (n := n) ε) := by
    clear * - skp_isCompact_box skp_cube_finite skpH skpChi skpPsi skpPsi_support
    revert skp_isCompact_box skp_cube_finite skpH skpChi skpPsi skpPsi_support
    refine id ?_
    intro skp_isCompact_box skp_cube_finite skpH skpChi skpPsi skpPsi_support n ε hε
    exact IsCompact.of_isClosed_subset (skp_isCompact_box (fun _ => ε / 4) (fun _ => 1 - ε / 4))
          (isClosed_tsupport _) (skpPsi_support hε)
  have skpPsi_support_cube : ∀ {n : ℕ} {ε : ℝ} (hε : 0 < ε), tsupport (skpPsi (n := n) ε) ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skp_cube_finite skpH skpChi skpPsi skpPsi_support
    revert skp_cube_finite skpH skpChi skpPsi skpPsi_support
    refine id ?_
    intro skp_cube_finite skpH skpChi skpPsi skpPsi_support n ε hε u hu j
    have := skpPsi_support hε hu j
    constructor <;> linarith [this.1, this.2]
  have skpPsi_eventually_one : ∀ {n : ℕ} (ε : ℕ → ℝ) (hε0 : ∀ i, 0 < ε i) (hε : Tendsto ε atTop (𝓝 0)) (u : Eucl n) (hu : ∀ j, 0 < u j ∧ u j < 1), ∀ᶠ i : ℕ in atTop, skpPsi (ε i) u = 1 := by
    clear * - skp_cube_finite skpH skpChi skpChi_one skpPsi
    revert skp_cube_finite skpH skpChi skpChi_one skpPsi
    refine id ?_
    intro skp_cube_finite skpH skpChi skpChi_one skpPsi n ε hε0 hε u hu
    have hj : ∀ j, ∀ᶠ i : ℕ in atTop, skpChi (ε i) (u j) = 1 := by
      intro j
      have hm : 0 < min (u j) (1 - u j) := lt_min (hu j).1 (by linarith [(hu j).2])
      filter_upwards [hε.eventually (gt_mem_nhds hm)] with i hi
      apply skpChi_one (hε0 i)
      · have := min_le_left (u j) (1 - u j); linarith [hε0 i]
      · have := min_le_right (u j) (1 - u j); linarith [hε0 i]
    filter_upwards [(eventually_all.2 hj)] with i hi
    unfold skpPsi
    exact Finset.prod_eq_one fun j _ => hi j
  have skpPsi_line : ∀ {n : ℕ} (ε : ℝ) (u : Eucl n) (k : Fin n) (t : ℝ), skpPsi ε (u + t • EuclideanSpace.single k (1 : ℝ)) =
        skpChi ε (u k + t) * ∏ j ∈ Finset.univ.erase k, skpChi ε (u j) := by
    clear * - skp_line_apply_self skp_line_apply_ne skp_cube_finite skpH skpChi skpPsi
    revert skp_line_apply_self skp_line_apply_ne skp_cube_finite skpH skpChi skpPsi
    refine id ?_
    intro skp_line_apply_self skp_line_apply_ne skp_cube_finite skpH skpChi skpPsi n ε u k t
    classical
    unfold skpPsi
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), skp_line_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [skp_line_apply_ne u t (Finset.ne_of_mem_erase hj)]
  have skpPsi_fderiv : ∀ {n : ℕ} (ε : ℝ) (u : Eucl n) (k : Fin n), fderiv ℝ (skpPsi ε) u (EuclideanSpace.single k (1 : ℝ)) =
        deriv (skpChi ε) (u k) * ∏ j ∈ Finset.univ.erase k, skpChi ε (u j) := by
    clear * - skp_line_hasDerivAt skp_cube_finite skpH skpChi skpChi_contDiff skpPsi skpPsi_contDiff skpPsi_line
    revert skp_line_hasDerivAt skp_cube_finite skpH skpChi skpChi_contDiff skpPsi skpPsi_contDiff skpPsi_line
    refine id ?_
    intro skp_line_hasDerivAt skp_cube_finite skpH skpChi skpChi_contDiff skpPsi skpPsi_contDiff skpPsi_line n ε u k
    have h1 := skp_line_hasDerivAt (skpPsi ε) u (EuclideanSpace.single k (1 : ℝ))
      ((skpPsi_contDiff ε).differentiable (by simp) u)
    have h2 : HasDerivAt (fun t : ℝ => skpChi ε (u k + t) * ∏ j ∈ Finset.univ.erase k, skpChi ε (u j))
        (deriv (skpChi ε) (u k) * ∏ j ∈ Finset.univ.erase k, skpChi ε (u j)) 0 := by
      have := (((skpChi_contDiff ε).differentiable (by simp) (u k + 0)).hasDerivAt.comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).const_add (u k)))
      simp only [add_zero, mul_one] at this
      exact this.mul_const _
    have h3 : (fun t : ℝ => skpPsi ε (u + t • EuclideanSpace.single k (1 : ℝ))) =
        fun t => skpChi ε (u k + t) * ∏ j ∈ Finset.univ.erase k, skpChi ε (u j) := by
      funext t; exact skpPsi_line ε u k t
    rw [h3] at h1
    exact h1.unique h2
  -- An unnormalized bump on `(1/4, 3/4)`, equal to `1` on `[3/8, 5/8]`.
  let skpEta0 : ∀ (t : ℝ), ℝ :=
      fun (t : ℝ) => Real.smoothTransition (8 * t - 2) * Real.smoothTransition (6 - 8 * t)
  have skpEta0_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) skpEta0 := by
    clear * - skp_cube_finite skpEta0
    revert skp_cube_finite skpEta0
    refine id ?_
    intro skp_cube_finite skpEta0
    unfold skpEta0
    exact ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
        (contDiff_const.sub (contDiff_const.mul contDiff_id)))
  have skpEta0_nonneg : ∀ (t : ℝ), 0 ≤ skpEta0 t := by
    clear * - skp_cube_finite skpEta0
    revert skp_cube_finite skpEta0
    refine id ?_
    intro skp_cube_finite skpEta0 t
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have skpEta0_zero : ∀ {t : ℝ} (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t), skpEta0 t = 0 := by
    clear * - skp_cube_finite skpEta0
    revert skp_cube_finite skpEta0
    refine id ?_
    intro skp_cube_finite skpEta0 t ht
    unfold skpEta0
    rcases ht with ht | ht
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (x := 6 - 8 * t) (by linarith), mul_zero]
  have skpEta0_one : ∀ {t : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 5 / 8), skpEta0 t = 1 := by
    clear * - skp_cube_finite skpEta0
    revert skp_cube_finite skpEta0
    refine id ?_
    intro skp_cube_finite skpEta0 t h1 h2
    unfold skpEta0
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), mul_one]
  have skpEta0_hasCompactSupport : HasCompactSupport skpEta0 := by
    clear * - skp_cube_finite skpEta0 skpEta0_zero
    revert skp_cube_finite skpEta0 skpEta0_zero
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_zero
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 3 / 4)) fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact skpEta0_zero (Or.inl ht.le)
    · exact skpEta0_zero (Or.inr ht.le)
  have skpEta0_integrable : Integrable skpEta0 := by
    clear * - skp_cube_finite skpEta0 skpEta0_contDiff skpEta0_hasCompactSupport
    revert skp_cube_finite skpEta0 skpEta0_contDiff skpEta0_hasCompactSupport
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_contDiff skpEta0_hasCompactSupport
    exact skpEta0_contDiff.continuous.integrable_of_hasCompactSupport skpEta0_hasCompactSupport
  have skpEta0_integral_pos : 0 < ∫ t, skpEta0 t := by
    clear * - skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_one skpEta0_integrable
    revert skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_one skpEta0_integrable
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_one skpEta0_integrable
    have h1 : ∫ t in Icc (3 / 8 : ℝ) (5 / 8), skpEta0 t ≤ ∫ t, skpEta0 t :=
      setIntegral_le_integral skpEta0_integrable (Eventually.of_forall skpEta0_nonneg)
    have h2 : ∫ t in Icc (3 / 8 : ℝ) (5 / 8), skpEta0 t = 1 / 4 := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => skpEta0_one ht.1 ht.2),
        setIntegral_const, Real.volume_real_Icc_of_le (by norm_num)]
      norm_num
    linarith
  -- The normalized bump `η` on `(1/4, 3/4)`.
  let skpEta : ∀ (t : ℝ), ℝ :=
      fun (t : ℝ) => (∫ s, skpEta0 s)⁻¹ * skpEta0 t
  have skpEta_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) skpEta := by
    clear * - skp_cube_finite skpEta0 skpEta0_contDiff skpEta
    revert skp_cube_finite skpEta0 skpEta0_contDiff skpEta
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_contDiff skpEta
    exact contDiff_const.mul skpEta0_contDiff
  have skpEta_nonneg : ∀ (t : ℝ), 0 ≤ skpEta t := by
    clear * - skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_integral_pos skpEta
    revert skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_integral_pos skpEta
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_nonneg skpEta0_integral_pos skpEta t
    exact mul_nonneg (inv_nonneg.2 skpEta0_integral_pos.le) (skpEta0_nonneg t)
  have skpEta_integral : ∫ t, skpEta t = 1 := by
    clear * - skp_cube_finite skpEta0 skpEta0_integral_pos skpEta
    revert skp_cube_finite skpEta0 skpEta0_integral_pos skpEta
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_integral_pos skpEta
    unfold skpEta
    rw [integral_const_mul, inv_mul_cancel₀ skpEta0_integral_pos.ne']
  have skpEta_zero : ∀ {t : ℝ} (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t), skpEta t = 0 := by
    clear * - skp_cube_finite skpEta0 skpEta0_zero skpEta
    revert skp_cube_finite skpEta0 skpEta0_zero skpEta
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_zero skpEta t ht
    unfold skpEta
    rw [skpEta0_zero ht, mul_zero]
  have skpEta_hasCompactSupport : HasCompactSupport skpEta := by
    clear * - skp_cube_finite skpEta0 skpEta0_hasCompactSupport skpEta
    revert skp_cube_finite skpEta0 skpEta0_hasCompactSupport skpEta
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta0_hasCompactSupport skpEta
    exact skpEta0_hasCompactSupport.mul_left
  have skpEta_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |skpEta t| ≤ M := by
    clear * - skp_cube_finite skpEta0 skpEta skpEta_contDiff skpEta_hasCompactSupport
    revert skp_cube_finite skpEta0 skpEta skpEta_contDiff skpEta_hasCompactSupport
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta skpEta_contDiff skpEta_hasCompactSupport
    obtain ⟨M, hM⟩ := skpEta_hasCompactSupport.exists_bound_of_continuous skpEta_contDiff.continuous
    exact ⟨M, (norm_nonneg _).trans (hM 0), fun t => by simpa [Real.norm_eq_abs] using hM t⟩
  have skpEta_integral_shift : ∀ (c : ℝ), ∫ t, skpEta (c + t) = 1 := by
    clear * - skp_cube_finite skpEta0 skpEta skpEta_integral
    revert skp_cube_finite skpEta0 skpEta skpEta_integral
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta skpEta_integral c
    rw [integral_add_left_eq_self (fun t => skpEta t) c, skpEta_integral]
  have skpEtaBar_contDiff : ∀ (n : ℕ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => ∏ j, skpEta (u j)) := by
    clear * - skp_cube_finite skpEta0 skpEta skpEta_contDiff
    revert skp_cube_finite skpEta0 skpEta skpEta_contDiff
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta skpEta_contDiff n
    exact contDiff_prod fun j _ => skpEta_contDiff.comp (EuclideanSpace.proj j : Eucl n →L[ℝ] ℝ).contDiff
  have skpEtaBar_integral : ∀ (n : ℕ), ∫ u : Eucl n, ∏ j, skpEta (u j) = 1 := by
    clear * - skp_cube_finite skpEta0 skpEta skpEta_integral
    revert skp_cube_finite skpEta0 skpEta skpEta_integral
    refine id ?_
    intro skp_cube_finite skpEta0 skpEta skpEta_integral n
    have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
      (fun y : Fin n → ℝ => ∏ j, skpEta (y j))
    rw [show (fun u : Eucl n => ∏ j, skpEta (u j)) =
        fun u => (fun y : Fin n → ℝ => ∏ j, skpEta (y j))
          ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm u) from rfl, h, volume_pi,
      integral_fintype_prod_eq_prod (fun _ => skpEta)]
    simp [skpEta_integral]
  have skp_lineInt_contDiff : ∀ {n : ℕ} (k : Fin n) (G : Eucl n → ℝ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hGk : ∀ u : Eucl n, (u k < 0 ∨ 1 < u k) → G u = 0) (f : ℝ → ℝ) (hf : LocallyIntegrable f volume), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => ∫ t, f t * G (u + t • EuclideanSpace.single k (1 : ℝ))) := by
    clear * - skp_abs_coord_le_norm skp_cube_finite
    revert skp_abs_coord_le_norm skp_cube_finite
    refine id ?_
    intro skp_abs_coord_le_norm skp_cube_finite n k G hG hGk f hf
    set e := EuclideanSpace.single k (1 : ℝ) with he
    rw [contDiff_iff_contDiffAt]
    intro u0
    set R : ℝ := ‖u0‖ + 1 with hR
    have hgs : ∀ p : Eucl n, ∀ x : ℝ, p ∈ ball (0 : Eucl n) R → x ∉ Icc (-R - 1) (R + 1) →
        (fun (p : Eucl n) (s : ℝ) => G (p - s • e)) p x = 0 := by
      intro p x hp hx
      apply hGk
      have hpk : |p k| < R := by
        have := skp_abs_coord_le_norm p k
        rw [mem_ball, dist_zero_right] at hp
        linarith
      have hcoord : (p - x • e) k = p k - x := by simp [he]
      rw [hcoord]
      simp only [mem_Icc, not_and_or, not_le] at hx
      rw [abs_lt] at hpk
      rcases hx with hx | hx
      · right; linarith
      · left; linarith
    have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (↿(fun (p : Eucl n) (s : ℝ) => G (p - s • e))) (ball (0 : Eucl n) R ×ˢ univ) := by
      apply ContDiff.contDiffOn
      exact hG.comp (contDiff_fst.sub (contDiff_snd.smul contDiff_const))
    have key := contDiffOn_convolution_right_with_param_comp (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : Eucl n => (0 : ℝ)) contDiffOn_const isOpen_ball
      (isCompact_Icc (a := -R - 1) (b := R + 1)) hgs hf hg
    have hu0 : u0 ∈ ball (0 : Eucl n) R := by simp [hR]
    have heq : (fun x : Eucl n => (convolution f (fun s => G (x - s • e))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) ((fun _ : Eucl n => (0 : ℝ)) x)) =
        fun u => ∫ t, f t * G (u + t • e) := by
      funext u
      simp only [convolution, zero_sub, neg_smul, sub_neg_eq_add, ContinuousLinearMap.lsmul_apply,
        smul_eq_mul]
    rw [← heq]
    exact key.contDiffAt (isOpen_ball.mem_nhds hu0)
  have skp_line_integrable : ∀ {n : ℕ} (k : Fin n) (G : Eucl n → ℝ) (hG : Continuous G) (hGk : ∀ u : Eucl n, (u k < 0 ∨ 1 < u k) → G u = 0) (u : Eucl n), Integrable (fun t : ℝ => G (u + t • EuclideanSpace.single k (1 : ℝ))) := by
    clear * - skp_line_apply_self skp_cube_finite
    revert skp_line_apply_self skp_cube_finite
    refine id ?_
    intro skp_line_apply_self skp_cube_finite n k G hG hGk u
    refine Continuous.integrable_of_hasCompactSupport (hG.comp (continuous_const.add
      (continuous_id.smul continuous_const))) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -u k) (b := 1 - u k)) fun t ht => ?_
    apply hGk
    rw [skp_line_apply_self]
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · left; linarith
    · right; linarith
  have skp_line_int_bound : ∀ {n : ℕ} (k : Fin n) (G : Eucl n → ℝ) (hG : Continuous G) (hGk : ∀ u : Eucl n, (u k < 0 ∨ 1 < u k) → G u = 0) (B : ℝ) (hB : ∀ u, |G u| ≤ B) (f : ℝ → ℝ) (hf : ∀ t, |f t| ≤ 1) (hfm : Measurable f) (u : Eucl n), |∫ t, f t * G (u + t • EuclideanSpace.single k (1 : ℝ))| ≤ B := by
    clear * - skp_line_apply_self skp_cube_finite
    revert skp_line_apply_self skp_cube_finite
    refine id ?_
    intro skp_line_apply_self skp_cube_finite n k G hG hGk B hB f hf hfm u
    have hsupp : ∀ t ∉ Icc (-u k) (1 - u k),
        f t * G (u + t • EuclideanSpace.single k (1 : ℝ)) = 0 := by
      intro t ht
      rw [hGk _ ?_, mul_zero]
      rw [skp_line_apply_self]
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · left; linarith
      · right; linarith
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-u k) (1 - u k))
      (C := B) (f := fun t => f t * G (u + t • EuclideanSpace.single k (1 : ℝ)))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |f t| * |G (u + t • EuclideanSpace.single k 1)| ≤ 1 * B :=
              mul_le_mul (hf t) (hB _) (abs_nonneg _) zero_le_one
          _ = B := one_mul B)
    rw [Real.volume_real_Icc_of_le (by linarith)] at this
    rw [Real.norm_eq_abs] at this
    calc _ ≤ B * (1 - u k - -u k) := this
      _ = B := by ring
  -- Translation invariance of the full line integral along its own direction.
  have skp_lineInt_shift : ∀ {n : ℕ} (k : Fin n) (G : Eucl n → ℝ) (u : Eucl n) (s : ℝ), ∫ t : ℝ, G (u + s • EuclideanSpace.single k (1 : ℝ) + t • EuclideanSpace.single k (1 : ℝ)) =
        ∫ t : ℝ, G (u + t • EuclideanSpace.single k (1 : ℝ)) := by
    clear * - skp_line_add skp_cube_finite
    revert skp_line_add skp_cube_finite
    refine id ?_
    intro skp_line_add skp_cube_finite n k G u s
    simp_rw [skp_line_add]
    exact integral_add_left_eq_self (fun t => G (u + t • EuclideanSpace.single k (1 : ℝ))) s
  -- Fundamental theorem of calculus for the half-line integral.
  have skp_halfInt_fderiv : ∀ {n : ℕ} (k : Fin n) (G : Eucl n → ℝ) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hGk : ∀ u : Eucl n, (u k < 0 ∨ 1 < u k) → G u = 0) (u : Eucl n), fderiv ℝ (fun v : Eucl n => ∫ t in Iic (0 : ℝ), G (v + t • EuclideanSpace.single k (1 : ℝ)))
        u (EuclideanSpace.single k (1 : ℝ)) = G u := by
    clear * - skp_line_apply_self skp_line_hasDerivAt skp_indicator_one_mul skp_cube_finite skp_lineInt_contDiff skp_line_integrable
    revert skp_line_apply_self skp_line_hasDerivAt skp_indicator_one_mul skp_cube_finite skp_lineInt_contDiff skp_line_integrable
    refine id ?_
    intro skp_line_apply_self skp_line_hasDerivAt skp_indicator_one_mul skp_cube_finite skp_lineInt_contDiff skp_line_integrable n k G hG hGk u
    set e := EuclideanSpace.single k (1 : ℝ) with he
    set F := fun v : Eucl n => ∫ t in Iic (0 : ℝ), G (v + t • e) with hF
    have hFeq : F = fun v : Eucl n => ∫ t, (Iic (0 : ℝ)).indicator 1 t * G (v + t • e) := by
      funext v
      rw [hF]
      simp only
      rw [← integral_indicator measurableSet_Iic]
      congr 1; funext t
      exact (skp_indicator_one_mul _ _ _).symm
    have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
      rw [hFeq]
      exact skp_lineInt_contDiff k G hG hGk _ ((locallyIntegrable_const 1).indicator measurableSet_Iic)
    have hline := skp_line_hasDerivAt F u e (hFs.differentiable (by simp) u)
    -- the line restriction of `G`
    set φ : ℝ → ℝ := fun s => G (u + s • e) with hφ
    have hφc : Continuous φ := hG.continuous.comp (continuous_const.add
      (continuous_id.smul continuous_const))
    have hφint : Integrable φ := skp_line_integrable k G hG.continuous hGk u
    have hφ0 : ∀ s, s < -u k → φ s = 0 := by
      intro s hs; apply hGk; left; rw [skp_line_apply_self]; linarith
    set a : ℝ := min (-u k - 1) (-1) with ha
    have ha0 : a < 0 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hloc : ∀ s, a < s → F (u + s • e) = ∫ t in a..s, φ t := by
      intro s hs
      have h1 : F (u + s • e) = ∫ t in Iic s, φ t := by
        have hadd : ∀ t : ℝ, u + s • e + t • e = u + (s + t) • e := fun t => by
          rw [add_smul, add_assoc]
        rw [hF]
        simp_rw [hadd]
        rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
        rw [← integral_add_left_eq_self (fun t => (Iic s).indicator φ t) s]
        congr 1; funext t
        by_cases ht : t ≤ 0
        · rw [Set.indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht),
            Set.indicator_of_mem (show s + t ∈ Iic s from by simp only [mem_Iic]; linarith)]
        · rw [Set.indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht),
            Set.indicator_of_notMem (show s + t ∉ Iic s from by
              simp only [mem_Iic, not_le]; push_neg at ht; linarith)]
      rw [h1]
      have h2 := intervalIntegral.integral_Iic_sub_Iic (f := φ) (a := a) (b := s)
        hφint.integrableOn hφint.integrableOn
      have h3 : ∫ t in Iic a, φ t = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro t ht
        exact hφ0 t (by
          simp only [mem_Iic] at ht
          have := min_le_left (-u k - 1) (-1)
          linarith)
      linarith
    have hderiv : HasDerivAt (fun s => ∫ t in a..s, φ t) (φ 0) 0 :=
      (hφc.integral_hasStrictDerivAt a 0).hasDerivAt
    have hev : (fun s => F (u + s • e)) =ᶠ[𝓝 0] fun s => ∫ t in a..s, φ t := by
      filter_upwards [Ioi_mem_nhds ha0] with s hs using hloc s hs
    have := hderiv.congr_of_eventuallyEq hev
    rw [hline.unique this]
    show G (u + (0 : ℝ) • e) = G u
    simp
  have skp_integral_fderiv_eq_zero : ∀ {n : ℕ} (f : Eucl n → ℝ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) (v : Eucl n), ∫ u, fderiv ℝ f u v = 0 := by
    clear * - skp_line_hasDerivAt skp_cube_finite
    revert skp_line_hasDerivAt skp_cube_finite
    refine id ?_
    intro skp_line_hasDerivAt skp_cube_finite n f hf hfc v
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hcont : Continuous fun u => fderiv ℝ f u v :=
      (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs : HasCompactSupport fun u => fderiv ℝ f u v :=
      (hfc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Eucl n →L[ℝ] ℝ => L v) (by simp)
    obtain ⟨L, hL⟩ := hcs.exists_bound_of_continuous hcont
    obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
    -- mean value bound along `v`
    have hmvt : ∀ u (t : ℝ), |f (u + t • v) - f u| ≤ L * |t| := by
      intro u t
      have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (u + s • v)) (fderiv ℝ f (u + s • v) v) s := by
        intro s
        have hline : HasDerivAt (fun s : ℝ => u + s • v) v s := by
          simpa using ((hasDerivAt_id s).smul_const v).const_add u
        exact (hfd (u + s • v)).hasFDerivAt.comp_hasDerivAt s hline
      have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := fun s : ℝ => f (u + s • v))
        (C := L) (fun s _ => (hd s).differentiableAt) (fun s _ => by
          rw [(hd s).deriv]; exact hL _) (mem_univ 0) (mem_univ t)
      simpa [Real.norm_eq_abs] using this
    set h : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hh
    have hpos : ∀ j, 0 < h j := fun j => by positivity
    have hle : ∀ j, h j ≤ 1 := fun j => by
      simp only [hh]
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    -- each difference quotient integrates to zero
    have hq : ∀ j, ∫ u, (f (u + h j • v) - f u) / h j = 0 := by
      intro j
      rw [integral_div, integral_sub (hfi.comp_add_right (h j • v)) hfi,
        integral_add_right_eq_self (fun u => f u) (h j • v), sub_self, zero_div]
    -- pointwise convergence of the difference quotients
    have hlim : ∀ u, Tendsto (fun j => (f (u + h j • v) - f u) / h j) atTop
        (𝓝 (fderiv ℝ f u v)) := by
      intro u
      have hderiv := skp_line_hasDerivAt f u v (hfd u)
      rw [hasDerivAt_iff_tendsto_slope_zero] at hderiv
      have hh0 : Tendsto h atTop (𝓝[≠] 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun j => (hpos j).ne')
      refine (hderiv.comp hh0).congr fun j => ?_
      simp [div_eq_inv_mul]
    -- domination
    have hdom : ∀ j, ∀ u, ‖(f (u + h j • v) - f u) / h j‖ ≤
        (closedBall (0 : Eucl n) (R + ‖v‖)).indicator (fun _ => L) u := by
      intro j u
      by_cases hu : u ∈ closedBall (0 : Eucl n) (R + ‖v‖)
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs, abs_div, abs_of_pos (hpos j),
          div_le_iff₀ (hpos j)]
        have := hmvt u (h j)
        rwa [abs_of_pos (hpos j)] at this
      · rw [Set.indicator_of_notMem hu]
        have h1 : f u = 0 := image_eq_zero_of_notMem_tsupport fun h' => hu (by
          have := hR h'
          rw [mem_closedBall, dist_zero_right] at this ⊢
          linarith [norm_nonneg v])
        have h2 : f (u + h j • v) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hu (by
          have := hR h'
          rw [mem_closedBall, dist_zero_right] at this ⊢
          have h3 : ‖h j • v‖ ≤ ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos j)]
            exact mul_le_of_le_one_left (norm_nonneg _) (hle j)
          calc ‖u‖ = ‖(u + h j • v) - h j • v‖ := by abel_nf
            _ ≤ ‖u + h j • v‖ + ‖h j • v‖ := norm_sub_le _ _
            _ ≤ R + ‖v‖ := add_le_add this h3)
        rw [h1, h2]; simp
    have hbint : Integrable ((closedBall (0 : Eucl n) (R + ‖v‖)).indicator fun _ => L) :=
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : Eucl n))).ne).integrable_indicator
        measurableSet_closedBall
    have hT := tendsto_integral_of_dominated_convergence _
      (fun j => (((hf.continuous.comp (continuous_id.add continuous_const)).sub
        hf.continuous).div_const _).aestronglyMeasurable) hbint
      (fun j => Eventually.of_forall (hdom j)) (Eventually.of_forall hlim)
    refine tendsto_nhds_unique hT ?_
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
    funext j
    exact hq j
  -- The telescoping right inverse of the divergence on the cube.
  have skp_div_solve : ∀ (n : ℕ), ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} →
      ∀ B : ℝ, 0 ≤ B → (∀ u, |g u| ≤ B) →
      ∃ Φ : Fin n → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) ∧ (∀ k, HasCompactSupport (Φ k)) ∧
        (∀ k, tsupport (Φ k) ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) ∧
        (∀ k u, |Φ k u| ≤ c₀ * B) ∧
        ∀ u, ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) =
          g u - (∫ v, g v) * ∏ j, skpEta (u j) := by
    clear * - skp_line_apply_self skp_line_apply_ne skp_line_hasDerivAt skp_isCompact_box skp_isClosed_box skp_cube_finite skp_compact_in_cube skpEta0 skpEta skpEta_contDiff skpEta_zero skpEta_hasCompactSupport skpEta_bound skpEta_integral_shift skpEtaBar_contDiff skpEtaBar_integral skp_lineInt_contDiff skp_line_integrable skp_line_int_bound skp_lineInt_shift skp_halfInt_fderiv skp_integral_fderiv_eq_zero
    revert skp_line_apply_self skp_line_apply_ne skp_line_hasDerivAt skp_isCompact_box skp_isClosed_box skp_cube_finite skp_compact_in_cube skpEta0 skpEta skpEta_contDiff skpEta_zero skpEta_hasCompactSupport skpEta_bound skpEta_integral_shift skpEtaBar_contDiff skpEtaBar_integral skp_lineInt_contDiff skp_line_integrable skp_line_int_bound skp_lineInt_shift skp_halfInt_fderiv skp_integral_fderiv_eq_zero
    refine id ?_
    intro skp_line_apply_self skp_line_apply_ne skp_line_hasDerivAt skp_isCompact_box skp_isClosed_box skp_cube_finite skp_compact_in_cube skpEta0 skpEta skpEta_contDiff skpEta_zero skpEta_hasCompactSupport skpEta_bound skpEta_integral_shift skpEtaBar_contDiff skpEtaBar_integral skp_lineInt_contDiff skp_line_integrable skp_line_int_bound skp_lineInt_shift skp_halfInt_fderiv skp_integral_fderiv_eq_zero n
    classical
    obtain ⟨Mη, hMη0, hMη⟩ := skpEta_bound
    set M := max 1 Mη with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hMη' : Mη ≤ M := le_max_right _ _
    refine ⟨M ^ n * (1 + Mη), by positivity, ?_⟩
    intro g hg hgc hgs B hB hgB
    set e : Fin n → Eucl n := fun k => EuclideanSpace.single k (1 : ℝ) with he
    -- margins
    choose lo hi hlo0 hlo1 hhi0 hhi1 hbox using fun j => skp_compact_in_cube (tsupport g) hgc hgs j
    have hg0 : ∀ u, (∃ j, u j < lo j ∨ hi j < u j) → g u = 0 := by
      rintro u ⟨j, hj⟩
      apply image_eq_zero_of_notMem_tsupport
      intro hu
      have := hbox j u hu
      rcases hj with hj | hj <;> linarith [this.1, this.2]
    have hη0 : ∀ j : Fin n, ∀ t, (t < lo j ∨ hi j < t) → skpEta t = 0 := by
      intro j t ht
      apply skpEta_zero
      rcases ht with ht | ht
      · left; linarith [hlo1 j]
      · right; linarith [hhi0 j]
    -- the sequence `H`
    obtain ⟨H, hH0, hHs⟩ : ∃ H : ℕ → Eucl n → ℝ, H 0 = g ∧
        ∀ k (hk : k < n), H (k + 1) = fun u => ∫ t : ℝ, H k (u + t • e ⟨k, hk⟩) :=
      ⟨fun k => Nat.rec (motive := fun _ => Eucl n → ℝ) g
        (fun k Hk => if hk : k < n then (fun u => ∫ t : ℝ, Hk (u + t • e ⟨k, hk⟩)) else Hk) k,
        rfl, fun k hk => by simp only [dif_pos hk]⟩
    have hHprop : ∀ k, k ≤ n → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (H k) ∧
        (∀ u, (∃ j : Fin n, k ≤ (j : ℕ) ∧ (u j < lo j ∨ hi j < u j)) → H k u = 0) ∧
        (∀ u, |H k u| ≤ B) ∧
        (∀ j : Fin n, (j : ℕ) < k → ∀ u (s : ℝ), H k (u + s • e j) = H k u) := by
      intro k
      induction k with
      | zero =>
        intro _
        rw [hH0]
        exact ⟨hg, fun u ⟨j, _, hj⟩ => hg0 u ⟨j, hj⟩, hgB,
          fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      | succ k ih =>
        intro hk1
        have hk : k < n := hk1
        obtain ⟨ihs, ihz, ihb, iht⟩ := ih hk.le
        rw [hHs k hk]
        set kk : Fin n := ⟨k, hk⟩ with hkk
        have hzk : ∀ u : Eucl n, (u kk < 0 ∨ 1 < u kk) → H k u = 0 := by
          intro u hu
          apply ihz u ⟨kk, le_rfl, ?_⟩
          rcases hu with hu | hu
          · left; linarith [hlo0 kk]
          · right; linarith [hhi1 kk]
        refine ⟨?_, ?_, ?_, ?_⟩
        · have := skp_lineInt_contDiff kk (H k) ihs hzk (fun _ => 1) (locallyIntegrable_const 1)
          simpa using this
        · rintro u ⟨j, hj1, hj2⟩
          have hjk : j ≠ kk := by
            intro h; rw [h] at hj1; simp [hkk] at hj1
          have : ∀ t : ℝ, H k (u + t • e kk) = 0 := by
            intro t
            apply ihz _ ⟨j, by omega, ?_⟩
            simp only [he]
            rw [skp_line_apply_ne u t hjk]
            exact hj2
          simp only [this, integral_zero]
        · intro u
          have := skp_line_int_bound kk (H k) ihs.continuous hzk B ihb (fun _ => 1) (by simp)
            measurable_const u
          simpa using this
        · intro j hj u s
          by_cases hjk : (j : ℕ) < k
          · show ∫ t : ℝ, H k (u + s • e j + t • e kk) = ∫ t : ℝ, H k (u + t • e kk)
            congr 1; funext t
            rw [show u + s • e j + t • e kk = (u + t • e kk) + s • e j by abel]
            exact iht j hjk _ s
          · have hjeq : j = kk := by ext; simp only [hkk]; omega
            rw [hjeq]
            exact skp_lineInt_shift kk (H k) u s
    -- `H n` is constant
    have hHconst : ∀ u, H n u = H n 0 := by
      intro u
      have ht := (hHprop n le_rfl).2.2.2
      have hsum : ∀ s : Finset (Fin n), H n (∑ j ∈ s, u j • e j) = H n 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s has ih =>
          rw [Finset.sum_insert has, add_comm, ht a a.isLt]
          exact ih
      have hu : ∑ j, u j • e j = u := by
        ext i
        simp [he, EuclideanSpace.single_apply, Pi.single_apply, mul_ite]
      rw [← hu]
      exact hsum Finset.univ
    -- the products `E`
    set E : ℕ → Eucl n → ℝ := fun k u =>
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), skpEta (u j) with hE
    have hE0 : ∀ u, E 0 u = 1 := by intro u; simp [hE]
    have hEs : ∀ k (hk : k < n) u, E (k + 1) u = E k u * skpEta (u ⟨k, hk⟩) := by
      intro k hk u
      simp only [hE]
      have : Finset.univ.filter (fun j : Fin n => (j : ℕ) < k + 1) =
          insert ⟨k, hk⟩ (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [this, Finset.prod_insert (by simp), mul_comm]
    have hEn : ∀ u, E n u = ∏ j, skpEta (u j) := by
      intro u
      simp only [hE]
      congr 1
      ext j
      simp [j.isLt]
    have hEsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (E k) := fun k =>
      contDiff_prod fun j _ => skpEta_contDiff.comp (EuclideanSpace.proj j : Eucl n →L[ℝ] ℝ).contDiff
    have hEline : ∀ k (kk : Fin n), k ≤ (kk : ℕ) → ∀ u (t : ℝ), E k (u + t • e kk) = E k u := by
      intro k kk hkk u t
      simp only [hE]
      refine Finset.prod_congr rfl fun j hj => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have : j ≠ kk := by intro h; rw [h] at hj; omega
      rw [he]; simp only
      rw [skp_line_apply_ne u t this]
    have hEbound : ∀ k u, |E k u| ≤ M ^ n := by
      intro k u
      simp only [hE]
      rw [Finset.abs_prod]
      calc ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), |skpEta (u j)|
          ≤ ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), M :=
            Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => (hMη _).trans hMη')
        _ = M ^ (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).card := Finset.prod_const _
        _ ≤ M ^ n := by
            apply pow_le_pow_right₀ hM1
            calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
              _ = n := by simp
    have hEzero : ∀ k u (j : Fin n), (j : ℕ) < k → (u j < lo j ∨ hi j < u j) → E k u = 0 := by
      intro k u j hj hu
      simp only [hE]
      apply Finset.prod_eq_zero (i := j) (by simp [hj])
      exact hη0 j (u j) hu
    -- the differences `D` and the fields `Φ`
    set D : Fin n → Eucl n → ℝ := fun kk u => H kk u - skpEta (u kk) * H (kk + 1) u with hD
    have hDsmooth : ∀ kk : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (D kk) := by
      intro kk
      have h1 := (hHprop kk kk.isLt.le).1
      have h2 := (hHprop (kk + 1) kk.isLt).1
      exact h1.sub ((skpEta_contDiff.comp (EuclideanSpace.proj kk : Eucl n →L[ℝ] ℝ).contDiff).mul h2)
    have hDzk : ∀ (kk : Fin n) u, (u kk < lo kk ∨ hi kk < u kk) → D kk u = 0 := by
      intro kk u hu
      simp only [hD]
      rw [(hHprop kk kk.isLt.le).2.1 u ⟨kk, le_rfl, hu⟩, hη0 kk (u kk) hu]
      ring
    have hDz01 : ∀ (kk : Fin n) u, (u kk < 0 ∨ 1 < u kk) → D kk u = 0 := by
      intro kk u hu
      apply hDzk
      rcases hu with hu | hu
      · left; linarith [hlo0 kk]
      · right; linarith [hhi1 kk]
    have hDzj : ∀ (kk : Fin n) u (j : Fin n), (kk : ℕ) < j → (u j < lo j ∨ hi j < u j) →
        D kk u = 0 := by
      intro kk u j hj hu
      simp only [hD]
      rw [(hHprop kk kk.isLt.le).2.1 u ⟨j, hj.le, hu⟩,
        (hHprop (kk + 1) kk.isLt).2.1 u ⟨j, hj, hu⟩]
      ring
    have hDbound : ∀ (kk : Fin n) u, |D kk u| ≤ (1 + Mη) * B := by
      intro kk u
      simp only [hD]
      have h1 := (hHprop kk kk.isLt.le).2.2.1 u
      have h2 := (hHprop (kk + 1) kk.isLt).2.2.1 u
      calc |H kk u - skpEta (u kk) * H (kk + 1) u| ≤ |H kk u| + |skpEta (u kk)| * |H (kk + 1) u| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ B + Mη * B := by gcongr; exact hMη _
        _ = (1 + Mη) * B := by ring
    -- the total line integral of `D kk` vanishes
    have hDint : ∀ (kk : Fin n) u, ∫ t : ℝ, D kk (u + t • e kk) = 0 := by
      intro kk u
      have hHk := hHprop kk kk.isLt.le
      have hHk1 := hHprop (kk + 1) kk.isLt
      have hzk : ∀ v : Eucl n, (v kk < 0 ∨ 1 < v kk) → H kk v = 0 := by
        intro v hv
        apply hHk.2.1 v ⟨kk, le_rfl, ?_⟩
        rcases hv with hv | hv
        · left; linarith [hlo0 kk]
        · right; linarith [hhi1 kk]
      have i1 : Integrable fun t : ℝ => H kk (u + t • e kk) :=
        skp_line_integrable kk (H kk) hHk.1.continuous hzk u
      have hshift : ∀ t, H (kk + 1) (u + t • e kk) = H (kk + 1) u :=
        fun t => hHk1.2.2.2 kk (Nat.lt_succ_self _) u t
      have hcoord : ∀ t, (u + t • e kk) kk = u kk + t := fun t => skp_line_apply_self u t kk
      have i2 : Integrable fun t : ℝ => skpEta ((u + t • e kk) kk) * H (kk + 1) (u + t • e kk) := by
        simp_rw [hcoord, hshift]
        refine Integrable.mul_const ?_ _
        have : Integrable (fun t => skpEta t) :=
          skpEta_contDiff.continuous.integrable_of_hasCompactSupport skpEta_hasCompactSupport
        exact this.comp_add_left (u kk)
      simp only [hD]
      rw [integral_sub i1 i2]
      simp_rw [hcoord, hshift]
      rw [integral_mul_const, skpEta_integral_shift, one_mul]
      rw [hHs kk kk.isLt]
      simp
    -- the fields
    set Φ : Fin n → Eucl n → ℝ := fun kk u =>
      E kk u * ∫ t in Iic (0 : ℝ), D kk (u + t • e kk) with hΦ
    have hIeq : ∀ kk : Fin n, (fun u : Eucl n => ∫ t in Iic (0 : ℝ), D kk (u + t • e kk)) =
        fun u => ∫ t, (Iic (0 : ℝ)).indicator 1 t * D kk (u + t • e kk) := by
      intro kk
      funext u
      rw [← integral_indicator measurableSet_Iic]
      congr 1; funext t
      by_cases ht : t ∈ Iic (0 : ℝ)
      · simp [Set.indicator_of_mem ht]
      · simp [Set.indicator_of_notMem ht]
    have hIsmooth : ∀ kk : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => ∫ t in Iic (0 : ℝ), D kk (u + t • e kk)) := by
      intro kk
      rw [hIeq kk]
      exact skp_lineInt_contDiff kk (D kk) (hDsmooth kk) (hDz01 kk) _
        ((locallyIntegrable_const 1).indicator measurableSet_Iic)
    have hΦsmooth : ∀ kk, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ kk) := fun kk => (hEsmooth kk).mul (hIsmooth kk)
    have hIbound : ∀ (kk : Fin n) u, |∫ t in Iic (0 : ℝ), D kk (u + t • e kk)| ≤ (1 + Mη) * B := by
      intro kk u
      have := congrFun (hIeq kk) u
      rw [this]
      refine skp_line_int_bound kk (D kk) (hDsmooth kk).continuous (hDz01 kk) _ (hDbound kk) _
        (fun t => ?_) (measurable_one.indicator measurableSet_Iic) u
      by_cases ht : t ∈ Iic (0 : ℝ)
      · simp [Set.indicator_of_mem ht]
      · simp [Set.indicator_of_notMem ht]
    have hΦbound : ∀ kk u, |Φ kk u| ≤ M ^ n * (1 + Mη) * B := by
      intro kk u
      simp only [hΦ]
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hEbound kk u) (hIbound kk u) (abs_nonneg _) (by positivity)
    -- supports
    have hΦzero : ∀ kk u, u ∉ {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} → Φ kk u = 0 := by
      intro kk u hu
      simp only [mem_setOf_eq, not_forall, not_and_or, not_le] at hu
      obtain ⟨j, hj⟩ := hu
      have hj' : u j < lo j ∨ hi j < u j := hj
      simp only [hΦ]
      rcases lt_trichotomy (j : ℕ) kk with hlt | heq | hgt
      · rw [hEzero kk u j hlt hj', zero_mul]
      · have hjk : j = kk := Fin.ext heq
        subst hjk
        rcases hj' with hj' | hj'
        · -- left of the box: the integrand vanishes on `t ≤ 0`
          rw [setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_), mul_zero]
          apply hDzk
          left
          rw [skp_line_apply_self]
          simp only [mem_Iic] at ht
          linarith
        · -- right of the box: the half-line integral is the full one, which vanishes
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_), hDint, mul_zero]
          apply hDzk
          right
          rw [skp_line_apply_self]
          simp only [mem_Iic, not_le] at ht
          linarith
      · rw [setIntegral_eq_zero_of_forall_eq_zero (fun t _ => ?_), mul_zero]
        apply hDzj kk _ j hgt
        have hne : j ≠ kk := by intro h; rw [h] at hgt; exact lt_irrefl _ hgt
        rw [skp_line_apply_ne u t hne]
        exact hj'
    have hboxcube : {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} ⊆
        {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
      intro u hu j
      exact ⟨lt_of_lt_of_le (hlo0 j) (hu j).1, lt_of_le_of_lt (hu j).2 (hhi1 j)⟩
    have hΦtsupp : ∀ kk, tsupport (Φ kk) ⊆ {u : Eucl n | ∀ j, lo j ≤ u j ∧ u j ≤ hi j} := by
      intro kk
      apply closure_minimal _ (skp_isClosed_box lo hi)
      intro u hu
      by_contra h
      exact hu (hΦzero kk u h)
    -- the derivative identity
    have hΦderiv : ∀ (kk : Fin n) u, fderiv ℝ (Φ kk) u (e kk) = E kk u * D kk u := by
      intro kk u
      have h1 := skp_line_hasDerivAt (Φ kk) u (e kk) ((hΦsmooth kk).differentiable (by simp) u)
      have h2 := skp_line_hasDerivAt (fun v : Eucl n => ∫ t in Iic (0 : ℝ), D kk (v + t • e kk))
        u (e kk) ((hIsmooth kk).differentiable (by simp) u)
      have h3 : (fun t : ℝ => Φ kk (u + t • e kk)) =
          fun t => E kk u * (fun v : Eucl n => ∫ t in Iic (0 : ℝ), D kk (v + t • e kk))
            (u + t • e kk) := by
        funext t
        simp only [hΦ]
        rw [hEline kk kk le_rfl u t]
      rw [h3] at h1
      rw [h1.unique (h2.const_mul (E kk u)), skp_halfInt_fderiv kk (D kk) (hDsmooth kk) (hDz01 kk) u]
    -- telescoping
    set gseq : ℕ → Eucl n → ℝ := fun k u => E k u * H k u with hgseq
    have hstep : ∀ (kk : Fin n) u, E kk u * D kk u = gseq kk u - gseq (kk + 1) u := by
      intro kk u
      simp only [hgseq, hD]
      rw [hEs kk kk.isLt u]
      ring
    have hdiv0 : ∀ u, ∑ kk : Fin n, fderiv ℝ (Φ kk) u (e kk) = g u - H n 0 * ∏ j, skpEta (u j) := by
      intro u
      simp_rw [hΦderiv, hstep]
      rw [Fin.sum_univ_eq_sum_range (fun k => gseq k u - gseq (k + 1) u) n,
        Finset.sum_range_sub']
      simp only [hgseq]
      rw [hE0, hH0, hEn, hHconst]
      ring
    -- the constant is the integral of `g`
    have hconst : H n 0 = ∫ v, g v := by
      have hint0 : ∫ u, ∑ kk : Fin n, fderiv ℝ (Φ kk) u (e kk) = 0 := by
        rw [integral_finset_sum]
        · refine Finset.sum_eq_zero fun kk _ => ?_
          exact skp_integral_fderiv_eq_zero (Φ kk) (hΦsmooth kk)
            (IsCompact.of_isClosed_subset (skp_isCompact_box lo hi) (isClosed_tsupport _)
              (hΦtsupp kk)) (e kk)
        · intro kk _
          have hcs : HasCompactSupport (Φ kk) :=
            IsCompact.of_isClosed_subset (skp_isCompact_box lo hi) (isClosed_tsupport _) (hΦtsupp kk)
          exact ((hΦsmooth kk).continuous_fderiv (by simp)).clm_apply continuous_const
            |>.integrable_of_hasCompactSupport
              ((hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Eucl n →L[ℝ] ℝ => L (e kk)) (by simp))
      simp_rw [hdiv0] at hint0
      have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
      have hηi : Integrable (fun u : Eucl n => H n 0 * ∏ j, skpEta (u j)) := by
        refine Integrable.const_mul ?_ _
        refine (skpEtaBar_contDiff n).continuous.integrable_of_hasCompactSupport ?_
        refine IsCompact.of_isClosed_subset (skp_isCompact_box (fun _ => (0 : ℝ)) (fun _ => 1))
          (isClosed_tsupport _) ?_
        apply closure_minimal _ (skp_isClosed_box _ _)
        intro u hu j
        by_contra hj
        apply hu
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        apply skpEta_zero
        simp only [not_and_or, not_le] at hj
        rcases hj with hj | hj
        · left; linarith
        · right; linarith
      rw [integral_sub hgi hηi, integral_const_mul, skpEtaBar_integral, mul_one] at hint0
      linarith
    refine ⟨Φ, hΦsmooth, fun kk => IsCompact.of_isClosed_subset (skp_isCompact_box lo hi)
      (isClosed_tsupport _) (hΦtsupp kk), fun kk => (hΦtsupp kk).trans hboxcube,
      fun kk u => by simpa [mul_assoc] using hΦbound kk u, fun u => ?_⟩
    rw [← hconst]
    exact hdiv0 u
  have skp_eps_pos : ∀ (i : ℕ), (0 : ℝ) < 1 / ((i : ℝ) + 2) := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite i
    positivity
  have skp_eps_le : ∀ (i : ℕ), 1 / ((i : ℝ) + 2) ≤ 1 / 2 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite i
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have skp_eps_tendsto : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 2)) atTop (𝓝 0) := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun i => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  -- Dominated convergence for the two parts of the cube functional.
  have skp_lam_tendsto : ∀ {n : ℕ} {X : Type} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ] (π : X → Eucl n) (hπ : Measurable π) (hπc : ∀ᵐ x ∂ρ, π x ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) (w : X → ℝ) (hw : Integrable w ρ) (G : ℕ → Eucl n → ℝ) (G' : Eucl n → ℝ) (hGc : ∀ i, Continuous (G i)) (C : ℝ) (hC : ∀ i u, u ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} → |G i u| ≤ C) (hlim : ∀ u ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1},
        Tendsto (fun i => G i u) atTop (𝓝 (G' u))), Tendsto (fun i => ∫ x, G i (π x) * w x ∂ρ) atTop (𝓝 (∫ x, G' (π x) * w x ∂ρ)) ∧
      Tendsto (fun i => ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, G i u) atTop
        (𝓝 (∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, G' u)) := by
    clear * - skp_measurableSet_cube skp_cube_finite
    revert skp_measurableSet_cube skp_cube_finite
    refine id ?_
    intro skp_measurableSet_cube skp_cube_finite n X _ ρ _ π hπ hπc w hw G G' hGc C hC hlim
    constructor
    · refine tendsto_integral_of_dominated_convergence (fun x => C * |w x|) (fun i => ?_)
        (hw.abs.const_mul C) (fun i => ?_) ?_
      · exact ((hGc i).measurable.comp hπ).aestronglyMeasurable.mul hw.aestronglyMeasurable
      · filter_upwards [hπc] with x hx
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hC i _ hx) (abs_nonneg _)
      · filter_upwards [hπc] with x hx
        exact (hlim _ hx).mul_const _
    · refine tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun i => (hGc i).aestronglyMeasurable) (integrable_const C) (fun i => ?_) ?_
      · rw [ae_restrict_iff' (skp_measurableSet_cube n)]
        exact Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hC i u hu
      · rw [ae_restrict_iff' (skp_measurableSet_cube n)]
        exact Eventually.of_forall fun u hu => hlim u hu
  have skp_lam_integrable : ∀ {n : ℕ} {X : Type} [MeasurableSpace X] (ρ : Measure X) (π : X → Eucl n) (hπ : Measurable π) (w : X → ℝ) (hw : Integrable w ρ) (G : Eucl n → ℝ) (hG : Continuous G) (C : ℝ) (hC : ∀ u, |G u| ≤ C), Integrable (fun x => G (π x) * w x) ρ := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite n X _ ρ π hπ w hw G hG C hC
    refine Integrable.bdd_mul (c := C) hw (hG.measurable.comp hπ).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hC _
  have skp_cube_integrable : ∀ {n : ℕ} (G : Eucl n → ℝ) (hG : Continuous G) (C : ℝ) (hC : ∀ u ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, |G u| ≤ C), IntegrableOn G {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skp_measurableSet_cube skp_volume_cube skp_cube_finite
    revert skp_measurableSet_cube skp_volume_cube skp_cube_finite
    refine id ?_
    intro skp_measurableSet_cube skp_volume_cube skp_cube_finite n G hG C hC
    refine Measure.integrableOn_of_bounded (M := C) (skp_volume_cube n ▸ ENNReal.one_ne_top)
      hG.aestronglyMeasurable ?_
    rw [ae_restrict_iff' (skp_measurableSet_cube n)]
    exact Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hC u hu
  -- (P): the Poincaré estimate with the weighted mean `b = ⟨η̄⟩`.
  have skp_cubeP : ∀ (n : ℕ), ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ {X : Type} [MeasurableSpace X]
      (ρ : Measure X) [IsFiniteMeasure ρ] (π : X → Eucl n), Measurable π →
      (∀ᵐ x ∂ρ, π x ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) →
      ∀ (w : X → ℝ), Integrable w ρ → ∀ K : ℝ,
      (∀ Φ : Fin n → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) → (∀ k, HasCompactSupport (Φ k)) →
        (∀ k, tsupport (Φ k) ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) → ∀ B : ℝ, 0 ≤ B →
        (∀ k u, |Φ k u| ≤ B) →
        |∫ x, (∑ k, fderiv ℝ (Φ k) (π x) (EuclideanSpace.single k (1 : ℝ))) * w x ∂ρ| ≤ K * B) →
      ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
        (∀ u, |g u| ≤ B) →
        |∫ x, g (π x) * w x ∂ρ - (∫ x, (∏ j, skpEta (π x j)) * w x ∂ρ) *
          ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤ c₁ * K * B := by
    clear * - skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skpEta0 skpEta skpEta_bound skpEtaBar_contDiff skp_div_solve skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_lam_integrable
    revert skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skpEta0 skpEta skpEta_bound skpEtaBar_contDiff skp_div_solve skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_lam_integrable
    refine id ?_
    intro skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skpEta0 skpEta skpEta_bound skpEtaBar_contDiff skp_div_solve skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_lam_integrable n
    obtain ⟨c₀, hc₀, hdiv⟩ := skp_div_solve n
    refine ⟨c₀, hc₀, ?_⟩
    intro X _ ρ _ π hπ hπc w hw K hK g hg hgc B hB hgB
    set cube := {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} with hcube
    set b := ∫ x, (∏ j, skpEta (π x j)) * w x ∂ρ with hb
    obtain ⟨Mη, hMη0, hMη⟩ := skpEta_bound
    have hηbar : ∀ u : Eucl n, |∏ j, skpEta (u j)| ≤ Mη ^ n := by
      intro u
      rw [Finset.abs_prod]
      calc ∏ j, |skpEta (u j)| ≤ ∏ _j : Fin n, Mη :=
            Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hMη _)
        _ = Mη ^ n := by simp
    -- Step 1: test functions supported in the cube
    have step1 : ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → tsupport g ⊆ cube →
        ∀ B : ℝ, 0 ≤ B → (∀ u, |g u| ≤ B) →
        |∫ x, g (π x) * w x ∂ρ - b * ∫ u in cube, g u| ≤ c₀ * K * B := by
      intro g hg hgc hgs B hB hgB
      obtain ⟨Φ, hΦs, hΦc, hΦt, hΦb, hΦd⟩ := hdiv g hg hgc hgs B hB hgB
      have h1 := hK Φ hΦs hΦc hΦt (c₀ * B) (by positivity) hΦb
      have hcube_int : ∫ u in cube, g u = ∫ u, g u := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro u hu
        exact image_eq_zero_of_notMem_tsupport (fun h => hu (hgs h))
      have hint1 : Integrable (fun x => g (π x) * w x) ρ :=
        skp_lam_integrable ρ π hπ w hw g hg.continuous B hgB
      have hint2 : Integrable (fun x => (∫ v, g v) * (∏ j, skpEta (π x j)) * w x) ρ := by
        have := skp_lam_integrable ρ π hπ w hw (fun u => ∏ j, skpEta (u j))
          (skpEtaBar_contDiff n).continuous _ hηbar
        simpa [mul_assoc] using this.const_mul (∫ v, g v)
      have h2 : ∫ x, (∑ k, fderiv ℝ (Φ k) (π x) (EuclideanSpace.single k (1 : ℝ))) * w x ∂ρ =
          ∫ x, g (π x) * w x ∂ρ - b * ∫ u in cube, g u := by
        simp_rw [hΦd, sub_mul]
        rw [integral_sub hint1 hint2, hcube_int, hb]
        congr 1
        simp_rw [mul_assoc]
        rw [integral_const_mul, mul_comm]
      rw [← h2]
      calc _ ≤ K * (c₀ * B) := h1
        _ = c₀ * K * B := by ring
    -- Step 2: cut off near the boundary of the cube
    have hK0 : 0 ≤ K := by
      have := hK (fun _ _ => 0) (fun _ => contDiff_const) (fun _ => HasCompactSupport.zero)
        (fun _ => by simp) 1 zero_le_one (fun _ _ => by simp)
      rw [mul_one] at this
      exact (abs_nonneg _).trans this
    set ε : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2) with hε
    set G : ℕ → Eucl n → ℝ := fun i u => g u * skpPsi (ε i) u with hG
    have hGb : ∀ i u, |G i u| ≤ B := by
      intro i u
      simp only [hG]
      rw [abs_mul, abs_of_nonneg (skpPsi_nonneg _ _)]
      calc |g u| * skpPsi (ε i) u ≤ B * 1 :=
            mul_le_mul (hgB u) (skpPsi_le_one _ _) (skpPsi_nonneg _ _) hB
        _ = B := mul_one B
    have hGi : ∀ i, |∫ x, G i (π x) * w x ∂ρ - b * ∫ u in cube, G i u| ≤ c₀ * K * B := by
      intro i
      refine step1 (G i) (hg.mul (skpPsi_contDiff _)) (hgc.mul_right) ?_ B hB (hGb i)
      exact (tsupport_mul_subset_right).trans (skpPsi_support_cube (skp_eps_pos i))
    have hlim := skp_lam_tendsto ρ π hπ hπc w hw G g
      (fun i => hg.continuous.mul (skpPsi_contDiff _).continuous) B (fun i u _ => hGb i u)
      (fun u hu => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [skpPsi_eventually_one ε skp_eps_pos skp_eps_tendsto u hu] with i hi
        simp [hG, hi])
    have hlim' := (hlim.1.sub (hlim.2.const_mul b)).abs
    exact le_of_tendsto hlim' (Eventually.of_forall hGi)
  -- (T): the trace estimate for the extension by zero.
  have skp_cubeT : ∀ (n : ℕ), ∃ c₂ : ℝ, 0 ≤ c₂ ∧ ∀ {X : Type} [MeasurableSpace X]
      (ρ : Measure X) [IsFiniteMeasure ρ] (π : X → Eucl n), Measurable π →
      (∀ᵐ x ∂ρ, π x ∈ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) →
      ∀ (w : X → ℝ), Integrable w ρ → ∀ K K₁ β : ℝ,
      (∀ Φ : Fin n → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) → (∀ k, HasCompactSupport (Φ k)) →
        (∀ k, tsupport (Φ k) ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) → ∀ B : ℝ, 0 ≤ B →
        (∀ k u, |Φ k u| ≤ B) →
        |∫ x, (∑ k, fderiv ℝ (Φ k) (π x) (EuclideanSpace.single k (1 : ℝ))) * w x ∂ρ| ≤ K * B) →
      (∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
        (∀ u, |g u| ≤ B) →
        |∫ x, g (π x) * w x ∂ρ - β * ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤
          K₁ * B) →
      ∀ Φ : Fin n → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) → (∀ k, HasCompactSupport (Φ k)) →
        ∀ B : ℝ, 0 ≤ B → (∀ k u, |Φ k u| ≤ B) →
        |∫ x, (∑ k, fderiv ℝ (Φ k) (π x) (EuclideanSpace.single k (1 : ℝ))) * w x ∂ρ -
          β * ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1},
            ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))| ≤ c₂ * (K + K₁) * B := by
    clear * - skp_coord_continuous skp_line_apply_self skp_line_hasDerivAt skp_norm_smul_single skp_cube_finite skpH skpH_contDiff skpH_zero skpH_one skpH_nonneg skpH_le_one skpH_differentiable skpH_deriv_zero skpH_deriv_bound skpChi skpChi_nonneg skpChi_le_one skpChi_deriv_zero skpChi_deriv_bound skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_hasCompactSupport skpPsi_support_cube skpPsi_eventually_one skpPsi_fderiv skp_integral_fderiv_eq_zero skp_eps_pos skp_eps_le skp_eps_tendsto skp_lam_tendsto skp_lam_integrable skp_cube_integrable
    revert skp_coord_continuous skp_line_apply_self skp_line_hasDerivAt skp_norm_smul_single skp_cube_finite skpH skpH_contDiff skpH_zero skpH_one skpH_nonneg skpH_le_one skpH_differentiable skpH_deriv_zero skpH_deriv_bound skpChi skpChi_nonneg skpChi_le_one skpChi_deriv_zero skpChi_deriv_bound skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_hasCompactSupport skpPsi_support_cube skpPsi_eventually_one skpPsi_fderiv skp_integral_fderiv_eq_zero skp_eps_pos skp_eps_le skp_eps_tendsto skp_lam_tendsto skp_lam_integrable skp_cube_integrable
    refine id ?_
    intro skp_coord_continuous skp_line_apply_self skp_line_hasDerivAt skp_norm_smul_single skp_cube_finite skpH skpH_contDiff skpH_zero skpH_one skpH_nonneg skpH_le_one skpH_differentiable skpH_deriv_zero skpH_deriv_bound skpChi skpChi_nonneg skpChi_le_one skpChi_deriv_zero skpChi_deriv_bound skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_hasCompactSupport skpPsi_support_cube skpPsi_eventually_one skpPsi_fderiv skp_integral_fderiv_eq_zero skp_eps_pos skp_eps_le skp_eps_tendsto skp_lam_tendsto skp_lam_integrable skp_cube_integrable n
    obtain ⟨Mh, hMh0, hMh⟩ := skpH_deriv_bound
    refine ⟨n * (3 + 2 * Mh), by positivity, ?_⟩
    intro X _ ρ _ π hπ hπc w hw K K₁ β hK hK₁ Φ hΦs hΦc B hB hΦb
    set cube := {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} with hcube
    have hK0 : 0 ≤ K := by
      have := hK (fun _ _ => 0) (fun _ => contDiff_const) (fun _ => HasCompactSupport.zero)
        (fun _ => by simp) 1 zero_le_one (fun _ _ => by simp)
      rw [mul_one] at this
      exact (abs_nonneg _).trans this
    have hK₁0 : 0 ≤ K₁ := by
      have := hK₁ (fun _ => 0) contDiff_const HasCompactSupport.zero 1 zero_le_one (fun _ => by simp)
      rw [mul_one] at this
      exact (abs_nonneg _).trans this
    -- the functional `λ`
    set lam : (Eucl n → ℝ) → ℝ := fun G => ∫ x, G (π x) * w x ∂ρ - β * ∫ u in cube, G u with hlam
    have hlam_add : ∀ G₁ G₂ : Eucl n → ℝ, Continuous G₁ → Continuous G₂ →
        (∃ C, ∀ u, |G₁ u| ≤ C) → (∃ C, ∀ u, |G₂ u| ≤ C) →
        lam (fun u => G₁ u + G₂ u) = lam G₁ + lam G₂ := by
      intro G₁ G₂ h1 h2 ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩
      simp only [hlam]
      have i1 := skp_lam_integrable ρ π hπ w hw G₁ h1 C₁ hC₁
      have i2 := skp_lam_integrable ρ π hπ w hw G₂ h2 C₂ hC₂
      have j1 := skp_cube_integrable G₁ h1 C₁ (fun u _ => hC₁ u)
      have j2 := skp_cube_integrable G₂ h2 C₂ (fun u _ => hC₂ u)
      simp_rw [add_mul]
      rw [integral_add i1 i2, integral_add j1 j2]
      ring
    -- bounded continuity data for each partial derivative
    have hderb : ∀ k, ∃ L, 0 ≤ L ∧ ∀ u, |fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))| ≤ L := by
      intro k
      have hcont : Continuous fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) :=
        ((hΦs k).continuous_fderiv (by simp)).clm_apply continuous_const
      have hcs : HasCompactSupport fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) :=
        ((hΦc k).fderiv (𝕜 := ℝ)).comp_left
          (g := fun L : Eucl n →L[ℝ] ℝ => L (EuclideanSpace.single k (1 : ℝ))) (by simp)
      obtain ⟨L, hL⟩ := hcs.exists_bound_of_continuous hcont
      exact ⟨L, (norm_nonneg _).trans (hL 0), fun u => by simpa [Real.norm_eq_abs] using hL u⟩
    -- the estimate for one partial derivative
    have hone : ∀ k : Fin n,
        |lam (fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)))| ≤
          (3 + 2 * Mh) * (K + K₁) * B := by
      intro k
      set e := EuclideanSpace.single k (1 : ℝ) with he
      obtain ⟨L, hL0, hL⟩ := hderb k
      have hΦd : Differentiable ℝ (Φ k) := (hΦs k).differentiable (by simp)
      set A : Eucl n → ℝ := fun u => Φ k u - (1 - skpH (u k)) * Φ k (u + (0 - u k) • e) -
        skpH (u k) * Φ k (u + (1 - u k) • e) with hA
      set gk : Eucl n → ℝ := fun u => deriv skpH (u k) *
        (Φ k (u + (1 - u k) • e) - Φ k (u + (0 - u k) • e)) with hgk
      have hcoordk : Continuous fun u : Eucl n => u k := skp_coord_continuous k
      have hshift : ∀ c : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => Φ k (u + (c - u k) • e)) := by
        intro c
        exact (hΦs k).comp (contDiff_id.add (((contDiff_const.sub
          (EuclideanSpace.proj k : Eucl n →L[ℝ] ℝ).contDiff)).smul contDiff_const))
      have hAs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
        have hHk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => skpH (u k)) :=
          skpH_contDiff.comp (EuclideanSpace.proj k : Eucl n →L[ℝ] ℝ).contDiff
        exact ((hΦs k).sub ((contDiff_const.sub hHk).mul (hshift 0))).sub (hHk.mul (hshift 1))
      have hAb : ∀ u, |A u| ≤ 3 * B := by
        intro u
        simp only [hA]
        have h1 := hΦb k u
        have h2 := hΦb k (u + (0 - u k) • e)
        have h3 := hΦb k (u + (1 - u k) • e)
        have hH0 := skpH_nonneg (u k)
        have hH1 := skpH_le_one (u k)
        calc |Φ k u - (1 - skpH (u k)) * Φ k (u + (0 - u k) • e) - skpH (u k) * Φ k (u + (1 - u k) • e)|
            ≤ |Φ k u| + |1 - skpH (u k)| * |Φ k (u + (0 - u k) • e)| +
              |skpH (u k)| * |Φ k (u + (1 - u k) • e)| := by
              rw [← abs_mul, ← abs_mul]
              exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
          _ ≤ B + 1 * B + 1 * B := by
              gcongr
              · rw [abs_of_nonneg (by linarith)]; linarith
              · rw [abs_of_nonneg hH0]; exact hH1
          _ = 3 * B := by ring
      -- derivative of `A` along `e`
      have hline_shift : ∀ (c t : ℝ) (u : Eucl n),
          u + t • e + (c - (u + t • e) k) • e = u + (c - u k) • e := by
        intro c t u
        rw [he, skp_line_apply_self]
        rw [← he]
        module
      have hAderiv : ∀ u, fderiv ℝ A u e = fderiv ℝ (Φ k) u e - gk u := by
        intro u
        have h1 := skp_line_hasDerivAt A u e (hAs.differentiable (by simp) u)
        have h2 : HasDerivAt (fun t : ℝ => Φ k (u + t • e) - (1 - skpH (u k + t)) *
            Φ k (u + (0 - u k) • e) - skpH (u k + t) * Φ k (u + (1 - u k) • e))
            (fderiv ℝ (Φ k) u e - (-(deriv skpH (u k))) * Φ k (u + (0 - u k) • e) -
              deriv skpH (u k) * Φ k (u + (1 - u k) • e)) 0 := by
          have hH : HasDerivAt (fun t : ℝ => skpH (u k + t)) (deriv skpH (u k)) 0 := by
            have := HasDerivAt.comp_const_add (u k) 0 (skpH_differentiable (u k + 0)).hasDerivAt
            rwa [add_zero] at this
          have hΦl := skp_line_hasDerivAt (Φ k) u e (hΦd u)
          refine (hΦl.sub ((hH.const_sub 1).mul_const _)).sub (hH.mul_const _) |>.congr_deriv ?_
          ring
        have h3 : (fun t : ℝ => A (u + t • e)) = fun t : ℝ => Φ k (u + t • e) -
            (1 - skpH (u k + t)) * Φ k (u + (0 - u k) • e) - skpH (u k + t) * Φ k (u + (1 - u k) • e) := by
          funext t
          simp only [hA]
          rw [hline_shift 0 t u, hline_shift 1 t u, he, skp_line_apply_self]
        rw [h3] at h1
        rw [h1.unique h2]
        simp only [hgk]
        ring
      -- smoothness and support of `gk`
      have hgks : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) gk := by
        have hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Eucl n => deriv skpH (u k)) := by
          have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv skpH) := (contDiff_infty_iff_deriv.1 skpH_contDiff).2
          exact this.comp (EuclideanSpace.proj k : Eucl n →L[ℝ] ℝ).contDiff
        exact hd.mul ((hshift 1).sub (hshift 0))
      have hgkc : HasCompactSupport gk := by
        obtain ⟨R, hR⟩ := (hΦc k).isCompact.isBounded.subset_closedBall 0
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl n) (R + 2)) fun u hu => ?_
        simp only [hgk]
        by_cases huk : 1 / 4 ≤ u k ∧ u k ≤ 1 / 2
        · have h1 : Φ k (u + (1 - u k) • e) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            intro hmem
            apply hu
            have := hR hmem
            rw [mem_closedBall, dist_zero_right] at this ⊢
            have hn : ‖(1 - u k) • e‖ ≤ 1 := by
              rw [he, skp_norm_smul_single, abs_le]; constructor <;> linarith [huk.1, huk.2]
            calc ‖u‖ = ‖u + (1 - u k) • e - (1 - u k) • e‖ := by abel_nf
              _ ≤ ‖u + (1 - u k) • e‖ + ‖(1 - u k) • e‖ := norm_sub_le _ _
              _ ≤ R + 1 := add_le_add this hn
              _ ≤ R + 2 := by linarith
          have h0 : Φ k (u + (0 - u k) • e) = 0 := by
            apply image_eq_zero_of_notMem_tsupport
            intro hmem
            apply hu
            have := hR hmem
            rw [mem_closedBall, dist_zero_right] at this ⊢
            have hn : ‖(0 - u k) • e‖ ≤ 1 := by
              rw [he, skp_norm_smul_single, abs_le]; constructor <;> linarith [huk.1, huk.2]
            calc ‖u‖ = ‖u + (0 - u k) • e - (0 - u k) • e‖ := by abel_nf
              _ ≤ ‖u + (0 - u k) • e‖ + ‖(0 - u k) • e‖ := norm_sub_le _ _
              _ ≤ R + 1 := add_le_add this hn
              _ ≤ R + 2 := by linarith
          rw [h1, h0]; ring
        · rw [skpH_deriv_zero (by
            simp only [not_and_or, not_le] at huk
            rcases huk with h | h
            · left; exact h
            · right; exact h), zero_mul]
      have hgkb : ∀ u, |gk u| ≤ 2 * Mh * B := by
        intro u
        simp only [hgk]
        rw [abs_mul]
        have h1 := hΦb k (u + (1 - u k) • e)
        have h2 := hΦb k (u + (0 - u k) • e)
        calc |deriv skpH (u k)| * |Φ k (u + (1 - u k) • e) - Φ k (u + (0 - u k) • e)|
            ≤ Mh * (B + B) := mul_le_mul (hMh _) ((abs_sub _ _).trans (add_le_add h1 h2))
              (abs_nonneg _) hMh0
          _ = 2 * Mh * B := by ring
      -- (c3): `|λ(∂_e A)| ≤ 3 K B`
      set ε : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 2) with hε
      set F : ℕ → Eucl n → ℝ := fun i u => A u * skpPsi (ε i) u with hF
      have hFs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F i) := fun i => hAs.mul (skpPsi_contDiff _)
      have hFt : ∀ i, tsupport (F i) ⊆ cube := fun i =>
        (tsupport_mul_subset_right).trans (skpPsi_support_cube (skp_eps_pos i))
      have hFc : ∀ i, HasCompactSupport (F i) := fun i =>
        (skpPsi_hasCompactSupport (n := n) (skp_eps_pos i)).mul_left
      have hFb : ∀ i u, |F i u| ≤ 3 * B := by
        intro i u
        simp only [hF]
        rw [abs_mul, abs_of_nonneg (skpPsi_nonneg _ _)]
        calc |A u| * skpPsi (ε i) u ≤ 3 * B * 1 :=
              mul_le_mul (hAb u) (skpPsi_le_one _ _) (skpPsi_nonneg _ _) (by positivity)
          _ = 3 * B := mul_one _
      have hFd : ∀ i u, fderiv ℝ (F i) u e =
          fderiv ℝ A u e * skpPsi (ε i) u + A u * fderiv ℝ (skpPsi (ε i)) u e := by
        intro i u
        have h1 : HasFDerivAt (fun v => A v * skpPsi (ε i) v)
            (A u • fderiv ℝ (skpPsi (ε i)) u + skpPsi (ε i) u • fderiv ℝ A u) u :=
          (hAs.differentiable (by simp) u).hasFDerivAt.mul
            ((skpPsi_contDiff (ε i)).differentiable (by simp) u).hasFDerivAt
        simp only [hF]
        rw [h1.fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have hFbound : ∀ i, |lam (fun u => fderiv ℝ (F i) u e)| ≤ 3 * K * B := by
        intro i
        have h1 := hK (fun j => if j = k then F i else 0)
          (fun j => by split_ifs; exacts [hFs i, contDiff_const])
          (fun j => by split_ifs; exacts [hFc i, HasCompactSupport.zero])
          (fun j => by split_ifs; exacts [hFt i, by simp])
          (3 * B) (by positivity)
          (fun j u => by split_ifs; exacts [hFb i u, by simp; positivity])
        have hsum : ∀ v : Eucl n, ∑ j, fderiv ℝ (if j = k then F i else 0) v
            (EuclideanSpace.single j (1 : ℝ)) = fderiv ℝ (F i) v e := by
          intro v
          rw [Finset.sum_eq_single k]
          · simp [he]
          · intro j _ hj; simp [hj]
          · simp
        simp_rw [hsum] at h1
        have h0 : ∫ u in cube, fderiv ℝ (F i) u e = 0 := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
          · exact skp_integral_fderiv_eq_zero (F i) (hFs i) (hFc i) e
          · intro u hu
            have : u ∉ tsupport (F i) := fun h => hu (hFt i h)
            have hev : F i =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.1 this
            rw [hev.fderiv_eq]
            simp
        simp only [hlam]
        rw [h0, mul_zero, sub_zero]
        calc _ ≤ K * (3 * B) := h1
          _ = 3 * K * B := by ring
      -- the mean value bound along `e`
      have hmvt : ∀ u (s : ℝ), |Φ k (u + s • e) - Φ k u| ≤ L * |s| := by
        intro u s
        have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Φ k (u + t • e)) (fderiv ℝ (Φ k) (u + t • e) e) t := by
          intro t
          have hline : HasDerivAt (fun t : ℝ => u + t • e) e t := by
            simpa using ((hasDerivAt_id t).smul_const e).const_add u
          exact (hΦd (u + t • e)).hasFDerivAt.comp_hasDerivAt t hline
        have := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := fun t : ℝ => Φ k (u + t • e))
          (C := L) (fun t _ => (hd t).differentiableAt) (fun t _ => by
            rw [(hd t).deriv, Real.norm_eq_abs]; exact hL _) (mem_univ 0) (mem_univ s)
        simpa [Real.norm_eq_abs] using this
      have hAψ : ∀ i u, u ∈ cube → |A u * fderiv ℝ (skpPsi (ε i)) u e| ≤ L * Mh := by
        intro i u hu
        have hεi := skp_eps_pos i
        have hεle := skp_eps_le i
        rw [he, skpPsi_fderiv]
        set P := ∏ j ∈ Finset.univ.erase k, skpChi (ε i) (u j)
        have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => skpChi_nonneg _ _
        have hP1 : P ≤ 1 := Finset.prod_le_one₀ (fun j _ => skpChi_nonneg _ _)
          (fun j _ => skpChi_le_one _ _)
        have hχ := skpChi_deriv_bound hεi Mh hMh (u k)
        by_cases h1 : u k ≤ ε i / 2
        · have hH : skpH (u k) = 0 := skpH_zero (by linarith)
          have hAu : A u = -(Φ k (u + (0 - u k) • e) - Φ k u) := by
            simp only [hA, hH]; ring
          have hAb' : |A u| ≤ L * (ε i / 2) := by
            rw [hAu, abs_neg]
            calc _ ≤ L * |0 - u k| := hmvt u _
              _ ≤ L * (ε i / 2) := by
                  gcongr
                  rw [zero_sub, abs_neg, abs_of_pos (hu k).1]
                  exact h1
          calc |A u * (deriv (skpChi (ε i)) (u k) * P)|
              = |A u| * |deriv (skpChi (ε i)) (u k)| * P := by
                rw [abs_mul, abs_mul, abs_of_nonneg hP0, mul_assoc]
            _ ≤ (L * (ε i / 2)) * (2 * Mh / ε i) * 1 := by gcongr
            _ = L * Mh := by field_simp [hεi.ne']; rw [mul_right_comm, mul_div_assoc, div_self hεi.ne', mul_one]
        · by_cases h2 : 1 - ε i / 2 ≤ u k
          · have hH : skpH (u k) = 1 := skpH_one (by linarith)
            have hAu : A u = -(Φ k (u + (1 - u k) • e) - Φ k u) := by
              simp only [hA, hH]; ring
            have hAb' : |A u| ≤ L * (ε i / 2) := by
              rw [hAu, abs_neg]
              calc _ ≤ L * |1 - u k| := hmvt u _
                _ ≤ L * (ε i / 2) := by
                    gcongr
                    rw [abs_of_pos (by linarith [(hu k).2])]
                    linarith
            calc |A u * (deriv (skpChi (ε i)) (u k) * P)|
                = |A u| * |deriv (skpChi (ε i)) (u k)| * P := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hP0, mul_assoc]
              _ ≤ (L * (ε i / 2)) * (2 * Mh / ε i) * 1 := by gcongr
              _ = L * Mh := by field_simp [hεi.ne']; rw [mul_right_comm, mul_div_assoc, div_self hεi.ne', mul_one]
          · push_neg at h1 h2
            rw [skpChi_deriv_zero hεi h1 h2]
            simp only [zero_mul, mul_zero, abs_zero]
            positivity
      have hψlim : ∀ u ∈ cube, ∀ᶠ i in atTop, fderiv ℝ (skpPsi (ε i)) u e = 0 := by
        intro u hu
        have hm : 0 < min (u k) (1 - u k) := lt_min (hu k).1 (by linarith [(hu k).2])
        filter_upwards [skp_eps_tendsto.eventually (gt_mem_nhds hm)] with i hi
        rw [he, skpPsi_fderiv]
        have h1 := min_le_left (u k) (1 - u k)
        have h2 := min_le_right (u k) (1 - u k)
        rw [skpChi_deriv_zero (skp_eps_pos i) (by linarith [skp_eps_pos i])
          (by linarith [skp_eps_pos i]), zero_mul]
      -- boundedness of the pieces on all of `Eucl n`
      have hdAc : Continuous fun u => fderiv ℝ A u e :=
        (hAs.continuous_fderiv (by simp)).clm_apply continuous_const
      have hdAb : ∀ u, |fderiv ℝ A u e| ≤ L + 2 * Mh * B := by
        intro u
        rw [hAderiv]
        exact (abs_sub _ _).trans (add_le_add (hL u) (hgkb u))
      have hψdc : ∀ i, Continuous fun u => fderiv ℝ (skpPsi (n := n) (ε i)) u e := fun i =>
        ((skpPsi_contDiff (ε i)).continuous_fderiv (by simp)).clm_apply continuous_const
      have hψdb : ∀ i u, |fderiv ℝ (skpPsi (n := n) (ε i)) u e| ≤ 2 * Mh / ε i := by
        intro i u
        rw [he, skpPsi_fderiv, abs_mul]
        have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase k, skpChi (ε i) (u j) :=
          Finset.prod_nonneg fun j _ => skpChi_nonneg _ _
        have hP1 : ∏ j ∈ Finset.univ.erase k, skpChi (ε i) (u j) ≤ 1 :=
          Finset.prod_le_one₀ (fun j _ => skpChi_nonneg _ _) (fun j _ => skpChi_le_one _ _)
        rw [abs_of_nonneg hP0]
        calc _ ≤ 2 * Mh / ε i * 1 := mul_le_mul (skpChi_deriv_bound (skp_eps_pos i) Mh hMh _) hP1
              hP0 (by have := skp_eps_pos i; positivity)
          _ = _ := mul_one _
      have hsplit : ∀ i, lam (fun u => fderiv ℝ (F i) u e) =
          lam (fun u => fderiv ℝ A u e * skpPsi (ε i) u) +
            lam (fun u => A u * fderiv ℝ (skpPsi (ε i)) u e) := by
        intro i
        simp_rw [hFd]
        exact hlam_add (fun u => fderiv ℝ A u e * skpPsi (ε i) u)
          (fun u => A u * fderiv ℝ (skpPsi (ε i)) u e) (hdAc.mul (skpPsi_contDiff _).continuous)
          ((hAs.continuous).mul (hψdc i))
          ⟨L + 2 * Mh * B, fun u => by
            rw [abs_mul, abs_of_nonneg (skpPsi_nonneg _ _)]
            calc _ ≤ (L + 2 * Mh * B) * 1 := mul_le_mul (hdAb u) (skpPsi_le_one _ _)
                  (skpPsi_nonneg _ _) (by positivity)
              _ = _ := mul_one _⟩
          ⟨3 * B * (2 * Mh / ε i), fun u => by
            rw [abs_mul]
            exact mul_le_mul (hAb u) (hψdb i u) (abs_nonneg _) (by positivity)⟩
      have hlim1 := skp_lam_tendsto ρ π hπ hπc w hw (fun i u => fderiv ℝ A u e * skpPsi (ε i) u)
        (fun u => fderiv ℝ A u e) (fun i => hdAc.mul (skpPsi_contDiff _).continuous)
        (L + 2 * Mh * B) (fun i u _ => by
          rw [abs_mul, abs_of_nonneg (skpPsi_nonneg _ _)]
          calc _ ≤ (L + 2 * Mh * B) * 1 := mul_le_mul (hdAb u) (skpPsi_le_one _ _)
                (skpPsi_nonneg _ _) (by positivity)
            _ = _ := mul_one _)
        (fun u hu => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [skpPsi_eventually_one ε skp_eps_pos skp_eps_tendsto u hu] with i hi
          simp [hi])
      have hlim2 := skp_lam_tendsto ρ π hπ hπc w hw (fun i u => A u * fderiv ℝ (skpPsi (ε i)) u e)
        (fun _ => 0) (fun i => hAs.continuous.mul (hψdc i)) (L * Mh) (fun i u hu => hAψ i u hu)
        (fun u hu => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hψlim u hu] with i hi
          simp [hi])
      have hl1 : Tendsto (fun i => lam (fun u => fderiv ℝ A u e * skpPsi (ε i) u)) atTop
          (𝓝 (lam (fun u => fderiv ℝ A u e))) := hlim1.1.sub (hlim1.2.const_mul β)
      have hl2 : Tendsto (fun i => lam (fun u => A u * fderiv ℝ (skpPsi (ε i)) u e)) atTop
          (𝓝 0) := by
        have := hlim2.1.sub (hlim2.2.const_mul β)
        simpa using this
      have hbnd : ∀ i, |lam (fun u => fderiv ℝ A u e * skpPsi (ε i) u)| ≤
          3 * K * B + |lam (fun u => A u * fderiv ℝ (skpPsi (ε i)) u e)| := by
        intro i
        have h := hsplit i
        have h' := hFbound i
        calc _ = |lam (fun u => fderiv ℝ (F i) u e) - lam (fun u => A u * fderiv ℝ (skpPsi (ε i)) u e)| := by
              rw [h]; ring_nf
          _ ≤ _ := (abs_sub _ _).trans (add_le_add h' le_rfl)
      have hA3 : |lam (fun u => fderiv ℝ A u e)| ≤ 3 * K * B := by
        have := le_of_tendsto_of_tendsto hl1.abs ((tendsto_const_nhds (x := 3 * K * B)).add hl2.abs)
          (Eventually.of_forall hbnd)
        simpa using this
      -- conclusion for one coordinate
      have hgkK := hK₁ gk hgks hgkc (2 * Mh * B) (by positivity) hgkb
      have hdecomp : (fun u => fderiv ℝ (Φ k) u e) = fun u => fderiv ℝ A u e + gk u := by
        funext u; rw [hAderiv]; ring
      rw [hdecomp, hlam_add _ _ hdAc hgks.continuous ⟨_, hdAb⟩ ⟨_, hgkb⟩]
      calc |lam (fun u => fderiv ℝ A u e) + lam gk| ≤ 3 * K * B + K₁ * (2 * Mh * B) :=
            (abs_add_le _ _).trans (add_le_add hA3 hgkK)
        _ ≤ (3 + 2 * Mh) * (K + K₁) * B := by
            nlinarith [mul_nonneg hK0 hB, mul_nonneg hK₁0 hB, mul_nonneg (mul_nonneg hMh0 hK0) hB,
              mul_nonneg (mul_nonneg hMh0 hK₁0) hB]
    -- sum over the coordinates
    have hcontk : ∀ k, Continuous fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) :=
      fun k => ((hΦs k).continuous_fderiv (by simp)).clm_apply continuous_const
    have hsum : lam (fun u => ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))) =
        ∑ k, lam (fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))) := by
      simp only [hlam]
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum, integral_finset_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      · intro k _
        obtain ⟨L, _, hL⟩ := hderb k
        exact skp_cube_integrable _ (hcontk k) L (fun u _ => hL u)
      · intro k _
        obtain ⟨L, _, hL⟩ := hderb k
        exact skp_lam_integrable ρ π hπ w hw _ (hcontk k) L hL
    change |lam (fun u => ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)))| ≤ _
    rw [hsum]
    calc |∑ k, lam (fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)))|
        ≤ ∑ k, |lam (fun u => fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, (3 + 2 * Mh) * (K + K₁) * B := Finset.sum_le_sum fun k _ => hone k
      _ = n * (3 + 2 * Mh) * (K + K₁) * B := by simp; ring
  have skp_dx_kron_self : ∀ {k N : ℕ} (β : SimonMultiIndex k N), wedgeCovectors k (fun j => EuclideanSpace.proj (β j))
        (fun j => EuclideanSpace.single (β j) (1 : ℝ)) = 1 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite k N β
    rw [wedgeCovectors_apply_det]
    convert Matrix.det_one (n := Fin k) (R := ℝ)
    ext i j
    simp [Matrix.one_apply, PiLp.single_apply, β.injective.eq_iff]
  have skp_dx_kron_ne : ∀ {k N : ℕ} (β γ : SimonMultiIndex k N) (hβγ : β ≠ γ), wedgeCovectors k (fun j => EuclideanSpace.proj (β j))
        (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) = 0 := by
    clear * - skp_eq_of_range_subset skp_cube_finite
    revert skp_eq_of_range_subset skp_cube_finite
    refine id ?_
    intro skp_eq_of_range_subset skp_cube_finite k N β γ hβγ
    rw [wedgeCovectors_apply_det]
    obtain ⟨i, hi⟩ : ∃ i, ∀ j, β i ≠ γ j := by
      by_contra! h
      apply hβγ
      apply skp_eq_of_range_subset
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := h i
      exact ⟨j, hj.symm⟩
    exact Matrix.det_eq_zero_of_row_eq_zero i fun j => by simp [PiLp.single_apply, hi j]
  have skp_dx_coord_le : ∀ {k N : ℕ} (β : SimonMultiIndex k N) (I : Fin k → Fin N) (hI : StrictMono I), |wedgeCovectors k (fun j => EuclideanSpace.proj (β j))
        (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ 1 := by
    clear * - skp_cube_finite skp_dx_kron_self skp_dx_kron_ne
    revert skp_cube_finite skp_dx_kron_self skp_dx_kron_ne
    refine id ?_
    intro skp_cube_finite skp_dx_kron_self skp_dx_kron_ne k N β I hI
    by_cases h : β = OrderEmbedding.ofStrictMono I hI
    · have := skp_dx_kron_self β
      rw [h] at this ⊢
      simp only [OrderEmbedding.coe_ofStrictMono] at this ⊢
      rw [this]; simp
    · have := skp_dx_kron_ne β (OrderEmbedding.ofStrictMono I hI) h
      simp only [OrderEmbedding.coe_ofStrictMono] at this
      rw [this]; simp
  have skp_cnorm_dx_le : ∀ {k N : ℕ} (β : SimonMultiIndex k N), covectorEuclideanNorm (wedgeCovectors k (fun j => EuclideanSpace.proj (β j))) ≤
        (Fintype.card (Fin k → Fin N) : ℝ) := by
    clear * - skp_cnorm_le_of_coord_le skp_cube_finite skp_dx_coord_le
    revert skp_cnorm_le_of_coord_le skp_cube_finite skp_dx_coord_le
    refine id ?_
    intro skp_cnorm_le_of_coord_le skp_cube_finite skp_dx_coord_le k N β
    exact by simpa using skp_cnorm_le_of_coord_le _ 1 zero_le_one (fun I hI => skp_dx_coord_le β I hI)
  have skpChart_line : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (u : Eucl n) (t : ℝ) (i : Fin n), skpChart F (u + t • EuclideanSpace.single i (1 : ℝ)) =
        skpChart F u + t • EuclideanSpace.single (F.2 i) (1 : ℝ) := by
    clear * - skpChart skpChart_on skpChart_off skp_cube_finite
    revert skpChart skpChart_on skpChart_off skp_cube_finite
    refine id ?_
    intro skpChart skpChart_on skpChart_off skp_cube_finite n N F u t i
    ext l
    by_cases hl : l ∈ range F.2
    · obtain ⟨j, rfl⟩ := hl
      simp only [PiLp.add_apply, PiLp.smul_apply, skpChart_on, EuclideanSpace.single_apply,
        F.2.injective.eq_iff, smul_eq_mul]
      split_ifs <;> ring
    · have : l ≠ F.2 i := fun h => hl ⟨i, h.symm⟩
      simp only [PiLp.add_apply, PiLp.smul_apply, skpChart_off F _ l hl, EuclideanSpace.single_apply,
        this, if_false, smul_eq_mul, mul_zero, add_zero]
  have skpProj_line : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (t : ℝ) (i : Fin n), skpProj F (x + t • EuclideanSpace.single (F.2 i) (1 : ℝ)) =
        skpProj F x + t • EuclideanSpace.single i (1 : ℝ) := by
    clear * - skpProj skpProj_apply skp_cube_finite
    revert skpProj skpProj_apply skp_cube_finite
    refine id ?_
    intro skpProj skpProj_apply skp_cube_finite n N F x t i
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, skpProj_apply, EuclideanSpace.single_apply,
      F.2.injective.eq_iff, smul_eq_mul]
    split_ifs <;> ring
  have skpProj_line_off : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (t : ℝ) (l : Fin N) (hl : l ∉ range F.2), skpProj F (x + t • EuclideanSpace.single l (1 : ℝ)) = skpProj F x := by
    clear * - skpProj skpProj_apply skp_cube_finite
    revert skpProj skpProj_apply skp_cube_finite
    refine id ?_
    intro skpProj skpProj_apply skp_cube_finite n N F x t l hl
    ext j
    have : F.2 j ≠ l := fun h => hl ⟨j, h⟩
    simp only [skpProj_apply, PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply, this,
      if_false, smul_eq_mul, mul_zero, add_zero]
  have skpChart_contDiff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (skpChart F) := by
    clear * - skpChart hskpChart skp_cube_finite
    revert skpChart hskpChart skp_cube_finite
    refine id ?_
    intro skpChart hskpChart skp_cube_finite n N F
    have : skpChart F = fun u : Eucl n => WithLp.toLp 2 (fun i : Fin N =>
        (F.1 i : ℝ) + ∑ j, if F.2 j = i then u j else 0) := by
      funext u; simp only [hskpChart]
    rw [this, contDiff_piLp]
    intro i
    simp only [PiLp.toLp_apply]
    refine contDiff_const.add (ContDiff.sum fun j _ => ?_)
    split_ifs
    · exact (EuclideanSpace.proj j : Eucl n →L[ℝ] ℝ).contDiff
    · exact contDiff_const
  have skpProj_contDiff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (skpProj F) := by
    clear * - skpProj hskpProj skp_cube_finite
    revert skpProj hskpProj skp_cube_finite
    refine id ?_
    intro skpProj hskpProj skp_cube_finite n N F
    have : skpProj F = fun x : Eucl N => WithLp.toLp 2 (fun j : Fin n =>
        x (F.2 j) - F.1 (F.2 j)) := by
      funext x; simp only [hskpProj]
    rw [this, contDiff_piLp]
    intro j
    simp only [PiLp.toLp_apply]
    exact (EuclideanSpace.proj (F.2 j) : Eucl N →L[ℝ] ℝ).contDiff.sub contDiff_const
  have skpProj_measurable : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Measurable (skpProj F) := by
    clear * - skpProj skp_cube_finite skpProj_contDiff
    revert skpProj skp_cube_finite skpProj_contDiff
    refine id ?_
    intro skpProj skp_cube_finite skpProj_contDiff n N F
    exact (skpProj_contDiff F).continuous.measurable
  have skp_face_eq_image : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), latticeFace 1 F = skpChart F '' {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} := by
    clear * - skpChart skpProj skpChart_proj skp_face_iff skpChart_mem_face skp_cube_finite
    revert skpChart skpProj skpChart_proj skp_face_iff skpChart_mem_face skp_cube_finite
    refine id ?_
    intro skpChart skpProj skpChart_proj skp_face_iff skpChart_mem_face skp_cube_finite n N F
    ext x
    constructor
    · intro hx
      rw [skp_face_iff] at hx
      exact ⟨skpProj F x, hx.2, skpChart_proj F x hx.1⟩
    · rintro ⟨u, hu, rfl⟩
      exact (skpChart_mem_face F u).2 hu
  have skp_oface_eq_image : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), skpOFace F = skpChart F '' {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skpOFace skpChart skpProj skpChart_proj skp_oface_iff skpChart_mem_oface skp_cube_finite
    revert skpOFace skpChart skpProj skpChart_proj skp_oface_iff skpChart_mem_oface skp_cube_finite
    refine id ?_
    intro skpOFace skpChart skpProj skpChart_proj skp_oface_iff skpChart_mem_oface skp_cube_finite n N F
    ext x
    constructor
    · intro hx
      rw [skp_oface_iff] at hx
      exact ⟨skpProj F x, hx.2, skpChart_proj F x hx.1⟩
    · rintro ⟨u, hu, rfl⟩
      exact (skpChart_mem_oface F u).2 hu
  have skp_isCompact_face : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), IsCompact (latticeFace 1 F) := by
    clear * - skpChart skp_isCompact_box skp_cube_finite skpChart_contDiff skp_face_eq_image
    revert skpChart skp_isCompact_box skp_cube_finite skpChart_contDiff skp_face_eq_image
    refine id ?_
    intro skpChart skp_isCompact_box skp_cube_finite skpChart_contDiff skp_face_eq_image n N F
    rw [skp_face_eq_image]
    exact (skp_isCompact_box (fun _ => 0) (fun _ => 1)).image (skpChart_contDiff F).continuous
  have skp_measurableSet_oface : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), MeasurableSet (skpOFace F) := by
    clear * - skpOFace skp_coord_continuous skpProj skp_oface_iff skp_measurableSet_cube skp_cube_finite skpProj_measurable
    revert skpOFace skp_coord_continuous skpProj skp_oface_iff skp_measurableSet_cube skp_cube_finite skpProj_measurable
    refine id ?_
    intro skpOFace skp_coord_continuous skpProj skp_oface_iff skp_measurableSet_cube skp_cube_finite skpProj_measurable n N F
    have : skpOFace F = (⋂ l ∈ (Finset.univ.filter fun l : Fin N => l ∉ range F.2),
        {x : Eucl N | x l = F.1 l}) ∩ skpProj F ⁻¹' {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
      ext x
      rw [skp_oface_iff]
      simp
    rw [this]
    refine MeasurableSet.inter ?_ ((skp_measurableSet_cube n).preimage (skpProj_measurable F))
    refine Finset.measurableSet_biInter _ fun l _ => ?_
    exact measurableSet_eq_fun (skp_coord_continuous l).measurable measurable_const
  have skp_oface_bounded : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Bornology.IsBounded (skpOFace F) := by
    clear * - skpOFace skp_oface_subset_face skp_cube_finite skp_isCompact_face
    revert skpOFace skp_oface_subset_face skp_cube_finite skp_isCompact_face
    refine id ?_
    intro skpOFace skp_oface_subset_face skp_cube_finite skp_isCompact_face n N F
    exact (skp_isCompact_face F).isBounded.subset (skp_oface_subset_face F)
  let skpKappa : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), ℝ :=
      fun {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) =>
    ∏ l ∈ Finset.univ.filter (fun l => l ∉ range F.2), skpH (1 - 4 * (x l - F.1 l) ^ 2)
  have skpKappa_contDiff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (skpKappa F) := by
    clear * - skp_cube_finite skpH skpH_contDiff skpKappa
    revert skp_cube_finite skpH skpH_contDiff skpKappa
    refine id ?_
    intro skp_cube_finite skpH skpH_contDiff skpKappa n N F
    unfold skpKappa
    refine contDiff_prod fun l _ => skpH_contDiff.comp ?_
    exact contDiff_const.sub (contDiff_const.mul
      (((EuclideanSpace.proj l : Eucl N →L[ℝ] ℝ).contDiff.sub contDiff_const).pow 2))
  have skpKappa_nonneg : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), 0 ≤ skpKappa F x := by
    clear * - skp_cube_finite skpH skpH_nonneg skpKappa
    revert skp_cube_finite skpH skpH_nonneg skpKappa
    refine id ?_
    intro skp_cube_finite skpH skpH_nonneg skpKappa n N F x
    exact Finset.prod_nonneg fun l _ => skpH_nonneg _
  have skpKappa_le_one : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N), skpKappa F x ≤ 1 := by
    clear * - skp_cube_finite skpH skpH_nonneg skpH_le_one skpKappa
    revert skp_cube_finite skpH skpH_nonneg skpH_le_one skpKappa
    refine id ?_
    intro skp_cube_finite skpH skpH_nonneg skpH_le_one skpKappa n N F x
    exact Finset.prod_le_one₀ (fun l _ => skpH_nonneg _) (fun l _ => skpH_le_one _)
  have skpKappa_one : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (hx : ∀ l, l ∉ range F.2 → x l = F.1 l), skpKappa F x = 1 := by
    clear * - skp_cube_finite skpH skpH_one skpKappa
    revert skp_cube_finite skpH skpH_one skpKappa
    refine id ?_
    intro skp_cube_finite skpH skpH_one skpKappa n N F x hx
    unfold skpKappa
    refine Finset.prod_eq_one fun l hl => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [hx l hl, sub_self]
    exact skpH_one (by norm_num)
  have skpKappa_tsupport : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), tsupport (skpKappa F) ⊆ {x : Eucl N | ∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2} := by
    clear * - skp_coord_continuous skp_cube_finite skpH skpH_zero skpKappa
    revert skp_coord_continuous skp_cube_finite skpH skpH_zero skpKappa
    refine id ?_
    intro skp_coord_continuous skp_cube_finite skpH skpH_zero skpKappa n N F
    have hclosed : IsClosed {x : Eucl N | ∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2} := by
      have : {x : Eucl N | ∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2} =
          ⋂ l ∈ (Finset.univ.filter fun l : Fin N => l ∉ range F.2), {x : Eucl N | |x l - F.1 l| ≤ 1 / 2} := by
        ext x; simp
      rw [this]
      exact isClosed_biInter fun l _ =>
        isClosed_le ((skp_coord_continuous l).sub continuous_const).abs continuous_const
    apply closure_minimal _ hclosed
    intro x hx l hl
    by_contra h
    apply hx
    unfold skpKappa
    apply Finset.prod_eq_zero (i := l) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩)
    apply skpH_zero
    have : 1 / 4 < (x l - F.1 l) ^ 2 := by
      have h' : (1 / 2 : ℝ) < |x l - F.1 l| := not_le.1 h
      nlinarith [sq_abs (x l - F.1 l), abs_nonneg (x l - F.1 l)]
    linarith
  have skpKappa_line : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (t : ℝ) (i : Fin n), skpKappa F (x + t • EuclideanSpace.single (F.2 i) (1 : ℝ)) = skpKappa F x := by
    clear * - skp_cube_finite skpH skpKappa
    revert skp_cube_finite skpH skpKappa
    refine id ?_
    intro skp_cube_finite skpH skpKappa n N F x t i
    unfold skpKappa
    refine Finset.prod_congr rfl fun l hl => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have : l ≠ F.2 i := fun h => hl ⟨i, h.symm⟩
    rw [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    simp [this]
  -- The closed slab around a face, a compact set.
  have skp_isCompact_slab : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), IsCompact {x : Eucl N | (∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2) ∧
        ∀ j, 0 ≤ skpProj F x j ∧ skpProj F x j ≤ 1} := by
    clear * - skpProj skpProj_apply skp_isCompact_box skp_cube_finite
    revert skpProj skpProj_apply skp_isCompact_box skp_cube_finite
    refine id ?_
    intro skpProj skpProj_apply skp_isCompact_box skp_cube_finite n N F
    have : {x : Eucl N | (∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2) ∧
        ∀ j, 0 ≤ skpProj F x j ∧ skpProj F x j ≤ 1} =
        {x : Eucl N | ∀ l, (fun l => if l ∈ range F.2 then (F.1 l : ℝ) else F.1 l - 1 / 2) l ≤ x l ∧
          x l ≤ (fun l => if l ∈ range F.2 then (F.1 l : ℝ) + 1 else F.1 l + 1 / 2) l} := by
      ext x
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩ l
        by_cases hl : l ∈ range F.2
        · obtain ⟨j, rfl⟩ := hl
          have := h2 j
          rw [skpProj_apply] at this
          simp only [mem_range_self, ite_true]
          constructor <;> linarith [this.1, this.2]
        · have := h1 l hl
          rw [abs_le] at this
          simp only [hl, ite_false]
          constructor <;> linarith [this.1, this.2]
      · intro h
        refine ⟨fun l hl => ?_, fun j => ?_⟩
        · have := h l
          simp only [hl, ite_false] at this
          rw [abs_le]
          constructor <;> linarith [this.1, this.2]
        · have := h (F.2 j)
          simp only [mem_range_self, ite_true] at this
          rw [skpProj_apply]
          constructor <;> linarith [this.1, this.2]
    rw [this]
    exact skp_isCompact_box _ _
  have skp_hyperplane_dx : ∀ {N m : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbT : T.boundary.mass < ∞) (μ₀ : Measure (Eucl N)) (v₀ : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation T μ₀ v₀) (γ : SimonMultiIndex (m + 1) N) (i0 : Fin (m + 1)) (c : ℝ), ∀ᵐ x ∂μ₀, x (γ i0) = c →
        v₀ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
    clear * - skp_wedge_perm skp_hyperplane skp_cube_finite
    revert skp_wedge_perm skp_hyperplane skp_cube_finite
    refine id ?_
    intro skp_wedge_perm skp_hyperplane skp_cube_finite N m T hbT μ₀ v₀ hrep γ i0 c
    -- the permutation `cons i0 (succAbove i0)`
    have hinj : Function.Injective (Fin.cons i0 i0.succAbove : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.cons_injective_iff]
      exact ⟨fun ⟨j, hj⟩ => Fin.succAbove_ne i0 j hj, Fin.succAbove_right_injective⟩
    set σ : Equiv.Perm (Fin (m + 1)) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    have hcomp : (fun j => (EuclideanSpace.proj (γ j) : Eucl N →L[ℝ] ℝ)) ∘ σ =
        Fin.cons (EuclideanSpace.proj (γ i0)) (fun j => EuclideanSpace.proj (γ (i0.succAbove j))) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [σ]
      · simp [σ]
    have hperm := skp_wedge_perm (fun j => (EuclideanSpace.proj (γ j) : Eucl N →L[ℝ] ℝ)) σ
    rw [hcomp] at hperm
    filter_upwards [skp_hyperplane T hbT μ₀ v₀ hrep (γ i0) c
      (fun j => EuclideanSpace.proj (γ (i0.succAbove j)))] with x hx hxc
    have h := hx hxc
    rw [hperm, map_smul] at h
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    exact (smul_eq_zero.1 h).resolve_left hs
  have skp_int_hyperplane : ∀ {N m : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbT : T.boundary.mass < ∞) (μ₀ : Measure (Eucl N)) (v₀ : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation T μ₀ v₀), ∀ᵐ x ∂μ₀, ∀ γ : SimonMultiIndex (m + 1) N, (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
        v₀ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
    clear * - skp_cube_finite skp_hyperplane_dx
    revert skp_cube_finite skp_hyperplane_dx
    refine id ?_
    intro skp_cube_finite skp_hyperplane_dx N m T hbT μ₀ v₀ hrep
    have h : ∀ (γ : SimonMultiIndex (m + 1) N) (i0 : Fin (m + 1)) (c : ℤ), ∀ᵐ x ∂μ₀,
        x (γ i0) = (c : ℝ) → v₀ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 :=
      fun γ i0 c => skp_hyperplane_dx T hbT μ₀ v₀ hrep γ i0 c
    have h' : ∀ᵐ x ∂μ₀, ∀ (γ : SimonMultiIndex (m + 1) N) (i0 : Fin (m + 1)) (c : ℤ),
        x (γ i0) = (c : ℝ) → v₀ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
      simp only [ae_all_iff]
      exact h
    filter_upwards [h'] with x hx γ ⟨i0, c, hc⟩
    exact hx γ i0 c hc
  have skp_rep_integrableOn_bdd : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ₀ : Measure (Eucl N)) (v₀ : Eucl N → NVector (Eucl N) k) (hrep : IsMeasureRepresentation T μ₀ v₀) (W : Covector (Eucl N) k) (A : Set (Eucl N)) (hA : Bornology.IsBounded A), IntegrableOn (fun x => v₀ x W) A μ₀ := by
    clear * - skp_rep_integrableOn skp_cube_finite
    revert skp_rep_integrableOn skp_cube_finite
    refine id ?_
    intro skp_rep_integrableOn skp_cube_finite N k T μ₀ v₀ hrep W A hA
    obtain ⟨R, hR⟩ := hA.subset_closedBall 0
    exact (skp_rep_integrableOn T μ₀ v₀ hrep W R).mono_set hR
  have skp_eval_continuous : ∀ {N k : ℕ} {E : Type} [TopologicalSpace E] (ω : E → Covector (Eucl N) k) (hω : Continuous ω) (w : Fin k → Eucl N), Continuous fun x => ω x w := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k E _ ω hω w
    exact (continuous_eval_const w).comp hω
  have skp_eval_bound : ∀ {N k : ℕ} (ω : TestFormOn (univ : Set (Eucl N)) k) (w : Fin k → Eucl N), ∃ C, ∀ x, |(ω : DifferentialForm (Eucl N) k) x w| ≤ C := by
    clear * - skp_cube_finite skp_eval_continuous
    revert skp_cube_finite skp_eval_continuous
    refine id ?_
    intro skp_cube_finite skp_eval_continuous N k ω w
    have hcont := skp_eval_continuous _ ω.property.1.1.continuous w
    have hcs : HasCompactSupport fun x => (ω : DifferentialForm (Eucl N) k) x w :=
      ω.property.1.2.comp_left (g := fun a : Covector (Eucl N) k => a w) (by simp)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  have skp_face_decomp : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)) (S : Finset (LatticeFaceIndex (m + 1) N)) (hS : ∀ F, (skpOFace F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty → F ∈ S), Q ω = ∑ F ∈ S, ∫ x in skpOFace F, (ω : DifferentialForm (Eucl N) (m + 1)) x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ := by
    clear * - skpOFace skp_oface_subset_face skp_oface_face skp_bdry_int skp_oface_coord skp_cube_finite skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_eval_continuous skp_eval_bound
    revert skpOFace skp_oface_subset_face skp_oface_face skp_bdry_int skp_oface_coord skp_cube_finite skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_eval_continuous skp_eval_bound
    refine id ?_
    intro skpOFace skp_oface_subset_face skp_oface_face skp_bdry_int skp_oface_coord skp_cube_finite skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_eval_continuous skp_eval_bound N m Q μ v hrep hL hdx ω S hS
    classical
    set ω' := (ω : DifferentialForm (Eucl N) (m + 1)) with hω'
    rw [(hrep ω).2]
    have hωc : Continuous ω' := ω.property.1.1.continuous
    set f : LatticeFaceIndex (m + 1) N → Eucl N → ℝ := fun F x => ω' x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) with hf
    have hint : ∀ F : LatticeFaceIndex (m + 1) N, IntegrableOn (f F) (skpOFace F) μ := by
      intro F
      obtain ⟨C, hC⟩ := skp_eval_bound ω (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
      have hv := skp_rep_integrableOn_bdd Q μ v hrep
        (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) _ (skp_oface_bounded F)
      exact Integrable.bdd_mul (c := C) hv
        (skp_eval_continuous ω' hωc _).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
    have hsum : ∑ F ∈ S, ∫ x in skpOFace F, f F x ∂μ =
        ∫ x, ∑ F ∈ S, (skpOFace F).indicator (f F) x ∂μ := by
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun F _ => ?_
        rw [integral_indicator (skp_measurableSet_oface F)]
      · intro F _
        exact (hint F).integrable_indicator (skp_measurableSet_oface F)
    change ∫ x, v x (ω' x) ∂μ = ∑ F ∈ S, ∫ x in skpOFace F, f F x ∂μ
    rw [hsum]
    apply integral_congr_ae
    filter_upwards [hL, hdx] with x hxL hxd
    have hexp : v x (ω' x) = ∑ γ : SimonMultiIndex (m + 1) N,
        ω' x (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) := by
      conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge N (m + 1) (ω' x)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [map_smul, smul_eq_mul]
      rfl
    rw [hexp]
    by_cases hA : ∃ F0 : LatticeFaceIndex (m + 1) N, x ∈ skpOFace F0
    · obtain ⟨F0, hF0⟩ := hA
      have hred : ∑ γ : SimonMultiIndex (m + 1) N,
          ω' x (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) *
            v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = f F0 x := by
        rw [Finset.sum_eq_single F0.2]
        · intro γ _ hγ
          obtain ⟨i0, hi0⟩ := skp_oface_coord F0 x hF0 γ hγ
          rw [hxd γ ⟨i0, F0.1 (γ i0), hi0⟩, mul_zero]
        · simp
      rw [hred]
      by_cases hF0S : F0 ∈ S
      · rw [Finset.sum_eq_single F0]
        · rw [Set.indicator_of_mem hF0]
        · intro F _ hF
          rw [Set.indicator_of_notMem]
          intro hxF
          exact hF (skp_oface_face F0 F x hF0 (skp_oface_subset_face F hxF))
        · intro h; exact absurd hF0S h
      · have hx0 : ω' x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hx
          exact hF0S (hS F0 ⟨x, hF0, hx⟩)
        have : f F0 x = 0 := by simp [hf, hx0]
        rw [this]
        symm
        apply Finset.sum_eq_zero
        intro F _
        by_cases hxF : x ∈ skpOFace F
        · have hFF0 : F = F0 := skp_oface_face F0 F x hF0 (skp_oface_subset_face F hxF)
          rw [Set.indicator_of_mem hxF, hFF0, this]
        · rw [Set.indicator_of_notMem hxF]
    · push_neg at hA
      obtain ⟨F1, hF1⟩ := mem_iUnion.1 hxL
      have hzero : ∀ γ : SimonMultiIndex (m + 1) N,
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
        intro γ
        obtain ⟨i0, c, hc⟩ := skp_bdry_int F1 x hF1 (hA F1) γ
        exact hxd γ ⟨i0, c, hc⟩
      simp only [hzero, mul_zero, Finset.sum_const_zero]
      symm
      apply Finset.sum_eq_zero
      intro F _
      rw [Set.indicator_of_notMem (hA F)]
  -- The face functional of a form through the chart.
  have skp_face_integral_chart : ∀ {N m : ℕ} (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (F : LatticeFaceIndex (m + 1) N) (ω : Eucl N → Covector (Eucl N) (m + 1)), ∫ x in skpOFace F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ =
        ∫ x in skpOFace F, (fun u => ω (skpChart F u) (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)))
          (skpProj F x) * v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ := by
    clear * - skpOFace skpChart skpProj skpChart_proj skp_oface_iff skp_cube_finite skp_measurableSet_oface
    revert skpOFace skpChart skpProj skpChart_proj skp_oface_iff skp_cube_finite skp_measurableSet_oface
    refine id ?_
    intro skpOFace skpChart skpProj skpChart_proj skp_oface_iff skp_cube_finite skp_measurableSet_oface N m μ v F ω
    refine setIntegral_congr_fun (skp_measurableSet_oface F) fun x hx => ?_
    simp only
    rw [skpChart_proj F x ((skp_oface_iff F x).1 hx).1]
  have skp_tsupport_comp_proj : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (g : Eucl n → ℝ), tsupport (fun x => g (skpProj F x)) ⊆ skpProj F ⁻¹' tsupport g := by
    clear * - skpProj skp_cube_finite skpProj_contDiff
    revert skpProj skp_cube_finite skpProj_contDiff
    refine id ?_
    intro skpProj skp_cube_finite skpProj_contDiff n N F g
    exact tsupport_comp_subset_preimage g (skpProj_contDiff F).continuous
  have skp_slab_scalar : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (g : Eucl n → ℝ) (hgt : tsupport g ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}), tsupport (fun x => skpKappa F x * g (skpProj F x)) ⊆
        {x : Eucl N | (∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2) ∧
          ∀ j, 0 ≤ skpProj F x j ∧ skpProj F x j ≤ 1} ∩ skpNbhd F := by
    clear * - skpNbhd skpNbhd_mem skpProj skpProj_apply skp_cube_finite skpH skpKappa skpKappa_tsupport skp_tsupport_comp_proj
    revert skpNbhd skpNbhd_mem skpProj skpProj_apply skp_cube_finite skpH skpKappa skpKappa_tsupport skp_tsupport_comp_proj
    refine id ?_
    intro skpNbhd skpNbhd_mem skpProj skpProj_apply skp_cube_finite skpH skpKappa skpKappa_tsupport skp_tsupport_comp_proj n N F g hgt x hx
    have h1 := skpKappa_tsupport F (tsupport_mul_subset_left hx)
    have h2 := hgt (skp_tsupport_comp_proj F g (tsupport_mul_subset_right hx))
    refine ⟨⟨h1, fun j => ⟨(h2 j).1.le, (h2 j).2.le⟩⟩, ?_⟩
    rw [skpNbhd_mem]
    intro l
    constructor
    · rintro ⟨j, rfl⟩
      have := h2 j
      rw [skpProj_apply] at this
      constructor <;> linarith [this.1, this.2]
    · intro hl
      exact lt_of_le_of_lt (h1 l hl) (by norm_num)
  -- `n`-forms on a face from scalar functions.
  have skp_face_nform : ∀ {N m : ℕ} (F : LatticeFaceIndex (m + 1) N) (g : Eucl (m + 1) → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgt : tsupport g ⊆ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}), (fun x => (skpKappa F x * g (skpProj F x)) •
          wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∈
        (TestFormOn (univ : Set (Eucl N)) (m + 1)) ∧
      tsupport (fun x => (skpKappa F x * g (skpProj F x)) •
          wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ⊆ skpNbhd F := by
    clear * - skpNbhd skpProj skp_scalar_form_mem skp_cube_finite skpH skpProj_contDiff skpKappa skpKappa_contDiff skp_isCompact_slab skp_slab_scalar
    revert skpNbhd skpProj skp_scalar_form_mem skp_cube_finite skpH skpProj_contDiff skpKappa skpKappa_contDiff skp_isCompact_slab skp_slab_scalar
    refine id ?_
    intro skpNbhd skpProj skp_scalar_form_mem skp_cube_finite skpH skpProj_contDiff skpKappa skpKappa_contDiff skp_isCompact_slab skp_slab_scalar N m F g hg hgt
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => skpKappa F x * g (skpProj F x)) :=
      (skpKappa_contDiff F).mul (hg.comp (skpProj_contDiff F))
    have ht := skp_slab_scalar F g hgt
    have hc : HasCompactSupport (fun x => skpKappa F x * g (skpProj F x)) :=
      IsCompact.of_isClosed_subset (skp_isCompact_slab F) (isClosed_tsupport _)
        (ht.trans inter_subset_left)
    refine ⟨skp_scalar_form_mem _ hs hc _, ?_⟩
    exact (tsupport_smul_subset_left _ _).trans (ht.trans inter_subset_right)
  -- `(m)`-forms on a face from vector fields.
  have skp_face_mform : ∀ {N m : ℕ} (F : LatticeFaceIndex (m + 1) N) (Φ : Fin (m + 1) → Eucl (m + 1) → ℝ) (hΦs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) (hΦt : ∀ k, tsupport (Φ k) ⊆ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}) (φ : Eucl N → Covector (Eucl N) m) (hφ : φ = fun x => ∑ i : Fin (m + 1), (((-1 : ℝ) ^ (i : ℕ)) * skpKappa F x *
        Φ i (skpProj F x)) • wedgeCovectors m (fun j => EuclideanSpace.proj (F.2 (i.succAbove j)))), φ ∈ (TestFormOn (univ : Set (Eucl N)) m) ∧ tsupport φ ⊆ skpNbhd F ∧
      (∀ B : ℝ, 0 ≤ B → (∀ k u, |Φ k u| ≤ B) → ∀ x,
        covectorEuclideanNorm (φ x) ≤ (Fintype.card (Fin m → Fin N) : ℝ) * ((m + 1) * B)) ∧
      ∀ x ∈ skpOFace F, extDeriv φ x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
        ∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ)) := by
    clear * - skp_cnorm_le_of_coord_le skpOFace skpNbhd skpProj skp_oface_iff skp_scalar_form_mem skp_line_hasDerivAt skp_cube_finite skpH skp_dx_kron_self skp_dx_kron_ne skp_dx_coord_le skpProj_line skpProj_contDiff skpKappa skpKappa_contDiff skpKappa_nonneg skpKappa_le_one skpKappa_one skpKappa_line skp_isCompact_slab skp_slab_scalar
    revert skp_cnorm_le_of_coord_le skpOFace skpNbhd skpProj skp_oface_iff skp_scalar_form_mem skp_line_hasDerivAt skp_cube_finite skpH skp_dx_kron_self skp_dx_kron_ne skp_dx_coord_le skpProj_line skpProj_contDiff skpKappa skpKappa_contDiff skpKappa_nonneg skpKappa_le_one skpKappa_one skpKappa_line skp_isCompact_slab skp_slab_scalar
    refine id ?_
    intro skp_cnorm_le_of_coord_le skpOFace skpNbhd skpProj skp_oface_iff skp_scalar_form_mem skp_line_hasDerivAt skp_cube_finite skpH skp_dx_kron_self skp_dx_kron_ne skp_dx_coord_le skpProj_line skpProj_contDiff skpKappa skpKappa_contDiff skpKappa_nonneg skpKappa_le_one skpKappa_one skpKappa_line skp_isCompact_slab skp_slab_scalar N m F Φ hΦs hΦt φ hφ
    classical
    set β : Fin (m + 1) → SimonMultiIndex m N := fun i => (Fin.succAboveOrderEmb i).trans F.2
      with hβ
    have hβapp : ∀ i j, β i j = F.2 (i.succAbove j) := fun i j => rfl
    have hβinj : ∀ i i', β i' = β i → i' = i := by
      intro i i' h
      have : ∀ j, i'.succAbove j = i.succAbove j := fun j => F.2.injective (by
        have := congrArg (fun b : SimonMultiIndex m N => b j) h
        simpa [hβapp] using this)
      exact Fin.succAbove_left_injective (funext this)
    set c : Fin (m + 1) → Eucl N → ℝ := fun i x =>
      ((-1 : ℝ) ^ (i : ℕ)) * skpKappa F x * Φ i (skpProj F x) with hc
    have hcs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c i) := fun i =>
      (contDiff_const.mul (skpKappa_contDiff F)).mul ((hΦs i).comp (skpProj_contDiff F))
    have hct : ∀ i, tsupport (c i) ⊆ {x : Eucl N | (∀ l, l ∉ range F.2 → |x l - F.1 l| ≤ 1 / 2) ∧
          ∀ j, 0 ≤ skpProj F x j ∧ skpProj F x j ≤ 1} ∩ skpNbhd F := by
      intro i
      have : c i = fun x => ((-1 : ℝ) ^ (i : ℕ)) * (skpKappa F x * Φ i (skpProj F x)) := by
        funext x; simp only [hc]; ring
      rw [this]
      exact (tsupport_mul_subset_right).trans (skp_slab_scalar F (Φ i) (hΦt i))
    have hcc : ∀ i, HasCompactSupport (c i) := fun i =>
      IsCompact.of_isClosed_subset (skp_isCompact_slab F) (isClosed_tsupport _)
        ((hct i).trans inter_subset_left)
    have hφ' : φ = fun x => ∑ i, c i x • wedgeCovectors m (fun j => EuclideanSpace.proj (β i j)) := by
      rw [hφ]
      rfl
    -- membership
    have hmem : φ ∈ (TestFormOn (univ : Set (Eucl N)) m) := by
      rw [hφ']
      have : (fun x => ∑ i, c i x • wedgeCovectors m (fun j => EuclideanSpace.proj (β i j))) =
          ∑ i, (fun x => c i x • wedgeCovectors m (fun j => EuclideanSpace.proj (β i j))) := by
        funext x; simp
      rw [this]
      exact Submodule.sum_mem _ fun i _ => skp_scalar_form_mem _ (hcs i) (hcc i) _
    refine ⟨hmem, ?_, ?_, ?_⟩
    · -- support
      rw [hφ']
      intro x hx
      have hsub : tsupport (fun x => ∑ i, c i x • wedgeCovectors m
          (fun j => EuclideanSpace.proj (β i j))) ⊆ ⋃ i, tsupport (c i) := by
        apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
        intro y hy
        by_contra h
        simp only [mem_iUnion, not_exists] at h
        apply hy
        simp only
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [image_eq_zero_of_notMem_tsupport (h i), zero_smul]
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hsub hx)
      exact ((hct i) hi).2
    · -- the covector norm
      intro B hB hΦb x
      rw [hφ']
      apply skp_cnorm_le_of_coord_le _ _ (by positivity)
      intro I hI
      simp only [ContinuousAlternatingMap.sum_apply,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      calc |∑ i, c i x * wedgeCovectors m (fun j => EuclideanSpace.proj (β i j))
            (fun j => EuclideanSpace.single (I j) (1 : ℝ))|
          ≤ ∑ i, |c i x| * 1 := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (skp_dx_coord_le (β i) I hI) (abs_nonneg _)
        _ ≤ ∑ _i : Fin (m + 1), B := by
            refine Finset.sum_le_sum fun i _ => ?_
            simp only [hc, mul_one, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            rw [abs_of_nonneg (skpKappa_nonneg F x)]
            calc skpKappa F x * |Φ i (skpProj F x)| ≤ 1 * B :=
                  mul_le_mul (skpKappa_le_one F x) (hΦb i _) (abs_nonneg _) zero_le_one
              _ = B := one_mul B
        _ = (m + 1) * B := by simp
    · -- the exterior derivative
      intro x hx
      have hφd : DifferentiableAt ℝ φ x :=
        (hmem.1.1.differentiable (by simp)) x
      rw [extDeriv_apply hφd]
      refine Finset.sum_congr rfl fun i _ => ?_
      -- the coefficient function
      have hcoef : (fun y => φ y (i.removeNth fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) =
          c i := by
        funext y
        rw [hφ']
        simp only [ContinuousAlternatingMap.sum_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        have hrm : (i.removeNth fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
            fun j => EuclideanSpace.single (β i j) (1 : ℝ) := by
          funext j; rfl
        rw [hrm, Finset.sum_eq_single i]
        · rw [skp_dx_kron_self, mul_one]
        · intro i' _ hi'
          rw [skp_dx_kron_ne _ _ (fun h => hi' (hβinj i i' h)), mul_zero]
        · simp
      rw [hcoef]
      -- derivative along the tangential direction
      have hline := skp_line_hasDerivAt (c i) x (EuclideanSpace.single (F.2 i) (1 : ℝ))
        ((hcs i).differentiable (by simp) x)
      have hκ : skpKappa F x = 1 := skpKappa_one F x ((skp_oface_iff F x).1 hx).1
      have h2 : HasDerivAt (fun t : ℝ => c i (x + t • EuclideanSpace.single (F.2 i) (1 : ℝ)))
          (((-1 : ℝ) ^ (i : ℕ)) * fderiv ℝ (Φ i) (skpProj F x) (EuclideanSpace.single i (1 : ℝ))) 0 := by
        have h3 : (fun t : ℝ => c i (x + t • EuclideanSpace.single (F.2 i) (1 : ℝ))) =
            fun t => ((-1 : ℝ) ^ (i : ℕ)) * Φ i (skpProj F x + t • EuclideanSpace.single i (1 : ℝ)) := by
          funext t
          simp only [hc]
          rw [skpKappa_line, hκ, skpProj_line, mul_one]
        rw [h3]
        exact (skp_line_hasDerivAt (Φ i) (skpProj F x) _
          ((hΦs i).differentiable (by simp) _)).const_mul _
      rw [hline.unique h2]
      simp only [zsmul_eq_mul]
      push_cast
      rw [← mul_assoc, ← mul_pow]
      norm_num
  have skp_nbhd_measure : ∀ {N n : ℕ} (μ : Measure (Eucl N)) (hL : μ (⋃ F : LatticeFaceIndex n N, latticeFace 1 F)ᶜ = 0) (F : LatticeFaceIndex n N), μ (skpNbhd F) ≤ μ (skpOFace F) := by
    clear * - skpOFace skpNbhd skp_nbhd_face skp_cube_finite
    revert skpOFace skpNbhd skp_nbhd_face skp_cube_finite
    refine id ?_
    intro skpOFace skpNbhd skp_nbhd_face skp_cube_finite N n μ hL F
    calc μ (skpNbhd F) ≤ μ (skpOFace F ∪ (⋃ F' : LatticeFaceIndex n N, latticeFace 1 F')ᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hxL : x ∈ ⋃ F' : LatticeFaceIndex n N, latticeFace 1 F'
          · obtain ⟨F', hF'⟩ := mem_iUnion.1 hxL
            exact Or.inl (skp_nbhd_face F F' x hx hF').2
          · exact Or.inr hxL
      _ ≤ μ (skpOFace F) + μ (⋃ F' : LatticeFaceIndex n N, latticeFace 1 F')ᶜ :=
          measure_union_le _ _
      _ = μ (skpOFace F) := by rw [hL, add_zero]
  -- The hypothesis `(H_K)` of the cube lemma on a face.
  have skp_face_HK : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (μ' : Measure (Eucl N)) [IsFiniteMeasure μ'] (hμ' : ∀ W : Set (Eucl N), IsOpen W → Q.boundary.massOn W = μ' W) (hμ'L : μ' (⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F)ᶜ = 0) (F : LatticeFaceIndex (m + 1) N) (Φ : Fin (m + 1) → Eucl (m + 1) → ℝ) (hΦs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) (hΦt : ∀ k, tsupport (Φ k) ⊆ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}) (B : ℝ) (hB : 0 ≤ B) (hΦb : ∀ k u, |Φ k u| ≤ B), |∫ x in skpOFace F, (∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ))) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ| ≤
        ((Fintype.card (Fin m → Fin N) : ℝ) * (m + 1) * (μ' (skpOFace F)).toReal) * B := by
    clear * - skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_cube_finite skpH skp_measurableSet_oface skpKappa skp_face_decomp skp_face_mform skp_nbhd_measure
    revert skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_cube_finite skpH skp_measurableSet_oface skpKappa skp_face_decomp skp_face_mform skp_nbhd_measure
    refine id ?_
    intro skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_cube_finite skpH skp_measurableSet_oface skpKappa skp_face_decomp skp_face_mform skp_nbhd_measure N m Q μ v hrep hL hdx μ' _ hμ' hμ'L F Φ hΦs hΦt B hB hΦb
    set φ : Eucl N → Covector (Eucl N) m := fun x => ∑ i : Fin (m + 1),
      (((-1 : ℝ) ^ (i : ℕ)) * skpKappa F x * Φ i (skpProj F x)) •
        wedgeCovectors m (fun j => EuclideanSpace.proj (F.2 (i.succAbove j))) with hφ
    obtain ⟨hmem, hsupp, hnorm, hd⟩ := skp_face_mform F Φ hΦs hΦt φ hφ
    set φT : TestFormOn (univ : Set (Eucl N)) m := ⟨φ, hmem⟩
    have h1 : Q.boundary φT = Q (exteriorDerivativeTestOn univ m φT) :=
      GeometricCurrentOn.boundary_apply _ _
    have hdsupp : tsupport ((exteriorDerivativeTestOn univ m φT :
        TestFormOn (univ : Set (Eucl N)) (m + 1)) : DifferentialForm (Eucl N) (m + 1)) ⊆
        skpNbhd F :=
      (tsupport_exteriorDerivative_subset φ).trans hsupp
    have h2 := skp_face_decomp Q μ v hrep hL hdx (exteriorDerivativeTestOn univ m φT) {F} (by
      rintro F' ⟨x, hx1, hx2⟩
      have := skp_nbhd_face F F' x (hdsupp hx2) (skp_oface_subset_face F' hx1)
      simp [this.1])
    rw [Finset.sum_singleton] at h2
    have h3 : ∫ x in skpOFace F, ((exteriorDerivativeTestOn univ m φT :
        TestFormOn (univ : Set (Eucl N)) (m + 1)) : DifferentialForm (Eucl N) (m + 1)) x
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ =
        ∫ x in skpOFace F, (∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ))) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ := by
      refine setIntegral_congr_fun (skp_measurableSet_oface F) fun x hx => ?_
      change extDeriv φ x _ * _ = _
      rw [hd x hx]
    rw [← h3, ← h2, ← h1]
    have h4 := skp_abs_le Q.boundary μ' hμ' (skpNbhd F) (skp_isOpen_nbhd F) φT hsupp _
      (hnorm B hB hΦb)
    calc |Q.boundary φT| ≤ (μ' (skpNbhd F)).toReal *
          ((Fintype.card (Fin m → Fin N) : ℝ) * ((m + 1) * B)) := h4
      _ ≤ (μ' (skpOFace F)).toReal * ((Fintype.card (Fin m → Fin N) : ℝ) * ((m + 1) * B)) :=
          mul_le_mul_of_nonneg_right (ENNReal.toReal_mono (measure_ne_top _ _)
            (skp_nbhd_measure μ' hμ'L F)) (by positivity)
      _ = _ := by ring
  have skpEtaBar_tsupport : ∀ (n : ℕ), tsupport (fun u : Eucl n => ∏ j, skpEta (u j)) ⊆ {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skp_isClosed_box skp_cube_finite skpEta0 skpEta skpEta_zero
    revert skp_isClosed_box skp_cube_finite skpEta0 skpEta skpEta_zero
    refine id ?_
    intro skp_isClosed_box skp_cube_finite skpEta0 skpEta skpEta_zero n
    have : tsupport (fun u : Eucl n => ∏ j, skpEta (u j)) ⊆
        {u : Eucl n | ∀ j, 1 / 4 ≤ u j ∧ u j ≤ 3 / 4} := by
      apply closure_minimal _ (skp_isClosed_box _ _)
      intro u hu j
      by_contra hj
      apply hu
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      apply skpEta_zero
      simp only [not_and_or, not_le] at hj
      rcases hj with hj | hj
      · left; linarith
      · right; linarith
    intro u hu j
    have := this hu j
    constructor <;> linarith [this.1, this.2]
  have skp_face_b_bound : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (μ : Measure (Eucl N)) [IsFiniteMeasure μ] (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (hμ : ∀ W : Set (Eucl N), IsOpen W → Q.massOn W = μ W) (hμL : μ (⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F)ᶜ = 0) (F : LatticeFaceIndex (m + 1) N) (Mη : ℝ) (hMη0 : 0 ≤ Mη) (hMη : ∀ t, |skpEta t| ≤ Mη), |∫ x in skpOFace F, (∏ j, skpEta (skpProj F x j)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ| ≤
        ((Fintype.card (Fin (m + 1) → Fin N) : ℝ) * Mη ^ (m + 1)) * (μ (skpOFace F)).toReal := by
    clear * - skp_cnorm_smul skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_oface_iff skp_cube_finite skpH skpEta0 skpEta skpEtaBar_contDiff skp_dx_kron_self skp_cnorm_dx_le skp_measurableSet_oface skpKappa skpKappa_nonneg skpKappa_le_one skpKappa_one skp_face_decomp skp_face_nform skp_nbhd_measure skpEtaBar_tsupport
    revert skp_cnorm_smul skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_oface_iff skp_cube_finite skpH skpEta0 skpEta skpEtaBar_contDiff skp_dx_kron_self skp_cnorm_dx_le skp_measurableSet_oface skpKappa skpKappa_nonneg skpKappa_le_one skpKappa_one skp_face_decomp skp_face_nform skp_nbhd_measure skpEtaBar_tsupport
    refine id ?_
    intro skp_cnorm_smul skp_abs_le skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skp_isOpen_nbhd skpProj skp_oface_iff skp_cube_finite skpH skpEta0 skpEta skpEtaBar_contDiff skp_dx_kron_self skp_cnorm_dx_le skp_measurableSet_oface skpKappa skpKappa_nonneg skpKappa_le_one skpKappa_one skp_face_decomp skp_face_nform skp_nbhd_measure skpEtaBar_tsupport N m Q μ _ v hrep hL hdx hμ hμL F Mη hMη0 hMη
    set g : Eucl (m + 1) → ℝ := fun u => ∏ j, skpEta (u j) with hg
    obtain ⟨hmem, hsupp⟩ := skp_face_nform (N := N) F g (skpEtaBar_contDiff _)
      (skpEtaBar_tsupport _)
    set ω : TestFormOn (univ : Set (Eucl N)) (m + 1) := ⟨_, hmem⟩
    have h2 := skp_face_decomp Q μ v hrep hL hdx ω {F} (by
      rintro F' ⟨x, hx1, hx2⟩
      have := skp_nbhd_face F F' x (hsupp hx2) (skp_oface_subset_face F' hx1)
      simp [this.1])
    rw [Finset.sum_singleton] at h2
    have h3 : ∫ x in skpOFace F, (ω : DifferentialForm (Eucl N) (m + 1)) x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ =
        ∫ x in skpOFace F, (∏ j, skpEta (skpProj F x j)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ := by
      refine setIntegral_congr_fun (skp_measurableSet_oface F) fun x hx => ?_
      change ((skpKappa F x * g (skpProj F x)) •
        wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) _ * _ = _
      rw [ContinuousAlternatingMap.smul_apply, skp_dx_kron_self,
        skpKappa_one F x ((skp_oface_iff F x).1 hx).1]
      simp [hg]
    rw [← h3, ← h2]
    have hbd : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) (m + 1)) x) ≤
        (Fintype.card (Fin (m + 1) → Fin N) : ℝ) * Mη ^ (m + 1) := by
      intro x
      change covectorEuclideanNorm ((skpKappa F x * g (skpProj F x)) •
        wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ≤ _
      rw [skp_cnorm_smul]
      have hgb : |g (skpProj F x)| ≤ Mη ^ (m + 1) := by
        simp only [hg]
        rw [Finset.abs_prod]
        calc ∏ j, |skpEta (skpProj F x j)| ≤ ∏ _j : Fin (m + 1), Mη :=
              Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hMη _)
          _ = Mη ^ (m + 1) := by simp
      have hk : |skpKappa F x| ≤ 1 := by
        rw [abs_of_nonneg (skpKappa_nonneg F x)]; exact skpKappa_le_one F x
      calc |skpKappa F x * g (skpProj F x)| *
            covectorEuclideanNorm (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)))
          ≤ (1 * Mη ^ (m + 1)) * (Fintype.card (Fin (m + 1) → Fin N) : ℝ) := by
            rw [abs_mul]
            exact mul_le_mul (mul_le_mul hk hgb (abs_nonneg _) zero_le_one) (skp_cnorm_dx_le _)
              (covectorEuclideanNorm_nonneg _) (by positivity)
        _ = _ := by ring
    have h4 := skp_abs_le Q μ hμ (skpNbhd F) (skp_isOpen_nbhd F) ω hsupp _ hbd
    calc |Q ω| ≤ (μ (skpNbhd F)).toReal *
          ((Fintype.card (Fin (m + 1) → Fin N) : ℝ) * Mη ^ (m + 1)) := h4
      _ ≤ (μ (skpOFace F)).toReal *
          ((Fintype.card (Fin (m + 1) → Fin N) : ℝ) * Mη ^ (m + 1)) :=
          mul_le_mul_of_nonneg_right (ENNReal.toReal_mono (measure_ne_top _ _)
            (skp_nbhd_measure μ hμL F)) (by positivity)
      _ = _ := by ring
  have skp_eval_contDiff : ∀ {N k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ω : E → Covector (Eucl N) k) (hω : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω) (w : Fin k → Eucl N), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => ω x w := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k E _ _ ω hω w
    let ev : Covector (Eucl N) k →L[ℝ] ℝ :=
      { toFun := fun a => a w
        map_add' := fun a b => rfl
        map_smul' := fun c a => rfl
        cont := continuous_eval_const w }
    exact ev.contDiff.comp hω
  have skp_chart_field : ∀ {N m : ℕ} (F : LatticeFaceIndex (m + 1) N) (φ : TestFormOn (univ : Set (Eucl N)) m) (Φ : Fin (m + 1) → Eucl (m + 1) → ℝ) (hΦ : Φ = fun (i : Fin (m + 1)) u => ((-1 : ℝ) ^ (i : ℕ)) * (φ : DifferentialForm (Eucl N) m) (skpChart F u)
        (fun j => EuclideanSpace.single (F.2 (i.succAbove j)) (1 : ℝ))), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) ∧ (∀ k, HasCompactSupport (Φ k)) ∧
      (∀ k u, |Φ k u| ≤ covectorEuclideanNorm ((φ : DifferentialForm (Eucl N) m) (skpChart F u))) ∧
      ∀ u, extDeriv (φ : DifferentialForm (Eucl N) m) (skpChart F u)
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
        ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) := by
    clear * - skp_coord_le_cnorm skpChart skpChart_isometry skp_line_hasDerivAt skp_cube_finite skpChart_line skpChart_contDiff skp_eval_contDiff
    revert skp_coord_le_cnorm skpChart skpChart_isometry skp_line_hasDerivAt skp_cube_finite skpChart_line skpChart_contDiff skp_eval_contDiff
    refine id ?_
    intro skp_coord_le_cnorm skpChart skpChart_isometry skp_line_hasDerivAt skp_cube_finite skpChart_line skpChart_contDiff skp_eval_contDiff N m F φ Φ hΦ
    set φ' := (φ : DifferentialForm (Eucl N) m) with hφ'
    have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ' := φ.property.1.1
    have hcomp : ∀ i : Fin (m + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => φ' (skpChart F u)
        (fun j => EuclideanSpace.single (F.2 (i.succAbove j)) (1 : ℝ))) := fun i =>
      skp_eval_contDiff _ (hφs.comp (skpChart_contDiff F)) _
    have hs : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k) := fun k => by rw [hΦ]; exact contDiff_const.mul (hcomp k)
    refine ⟨hs, fun k => ?_, fun k u => ?_, fun u => ?_⟩
    · -- compact support through the isometric chart
      have hK : IsCompact (skpChart F ⁻¹' tsupport φ') :=
        (skpChart_isometry F).isClosedEmbedding.isCompact_preimage φ.property.1.2
      refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
      apply closure_minimal _ (isClosed_tsupport _ |>.preimage (skpChart_contDiff F).continuous)
      intro u hu
      by_contra h
      apply hu
      rw [hΦ]
      simp only
      rw [image_eq_zero_of_notMem_tsupport h]
      simp
    · rw [hΦ]
      simp only
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact skp_coord_le_cnorm _ ((Fin.succAboveOrderEmb k).trans F.2)
    · have hφd : DifferentiableAt ℝ φ' (skpChart F u) := (hφs.differentiable (by simp)) _
      rw [extDeriv_apply hφd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hrm : (i.removeNth fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) =
          fun j => EuclideanSpace.single (F.2 (i.succAbove j)) (1 : ℝ) := by
        funext j; rfl
      rw [hrm]
      have hd1 := skp_line_hasDerivAt (fun y => φ' y (fun j => EuclideanSpace.single
        (F.2 (i.succAbove j)) (1 : ℝ))) (skpChart F u) (EuclideanSpace.single (F.2 i) (1 : ℝ))
        ((skp_eval_contDiff _ hφs _).differentiable (by simp) _)
      have hd2 := skp_line_hasDerivAt (Φ i) u (EuclideanSpace.single i (1 : ℝ))
        ((hs i).differentiable (by simp) u)
      have h3 : (fun t : ℝ => Φ i (u + t • EuclideanSpace.single i (1 : ℝ))) =
          fun t => ((-1 : ℝ) ^ (i : ℕ)) * (fun y => φ' y (fun j => EuclideanSpace.single
            (F.2 (i.succAbove j)) (1 : ℝ))) (skpChart F u + t • EuclideanSpace.single (F.2 i) (1 : ℝ)) := by
        funext t
        rw [hΦ]
        simp only
        rw [skpChart_line]
      rw [h3] at hd2
      rw [hd2.unique (hd1.const_mul _)]
      simp only [zsmul_eq_mul]
      push_cast
      ring
  have skp_box01_ae : ∀ {n : ℕ}, {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} =ᵐ[volume] {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} := by
    clear * - skp_measurableSet_cube skp_volume_cube skp_cube_finite
    revert skp_measurableSet_cube skp_volume_cube skp_cube_finite
    refine id ?_
    intro skp_measurableSet_cube skp_volume_cube skp_cube_finite n
    have hsub : {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} ⊆ {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} :=
      fun u hu j => ⟨(hu j).1.le, (hu j).2.le⟩
    have hvol : volume {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} = 1 := by
      have hQ : {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} =
          WithLp.ofLp ⁻¹' Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => 1) := by
        ext u; simp [Pi.le_def, forall_and]
      rw [hQ, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
        measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
      simp
    refine ae_eq_of_subset_of_measure_ge hsub ?_ (skp_measurableSet_cube n).nullMeasurableSet
      (by rw [hvol]; exact ENNReal.one_ne_top)
    rw [hvol, skp_volume_cube]
  have skp_face_integral : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (f : Eucl N → ℝ), ∫ x in latticeFace 1 F, f x ∂(μHE[n] : Measure (Eucl N)) =
        ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, f (skpChart F u) := by
    clear * - skpChart skpChart_isometry skp_isClosed_box skp_cube_finite skp_face_eq_image skp_box01_ae
    revert skpChart skpChart_isometry skp_isClosed_box skp_cube_finite skp_face_eq_image skp_box01_ae
    refine id ?_
    intro skpChart skpChart_isometry skp_isClosed_box skp_cube_finite skp_face_eq_image skp_box01_ae n N F f
    have hiso := skpChart_isometry F
    have hemb : MeasurableEmbedding (skpChart F) := hiso.isClosedEmbedding.measurableEmbedding
    set C : Set (Eucl n) := {u : Eucl n | ∀ j, 0 ≤ u j ∧ u j ≤ 1} with hC
    have hCm : MeasurableSet C := (skp_isClosed_box _ _).measurableSet
    rw [skp_face_eq_image, setIntegral_congr_set skp_box01_ae]
    have hmap : (μHE[n] : Measure (Eucl N)).restrict (range (skpChart F)) =
        Measure.map (skpChart F) volume := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    have hsub : skpChart F '' C ⊆ range (skpChart F) := image_subset_range _ _
    calc ∫ x in skpChart F '' C, f x ∂(μHE[n] : Measure (Eucl N))
        = ∫ x in skpChart F '' C, f x ∂((μHE[n] : Measure (Eucl N)).restrict (range (skpChart F))) := by
          rw [Measure.restrict_restrict_of_subset hsub]
      _ = ∫ x in skpChart F '' C, f x ∂(Measure.map (skpChart F) volume) := by rw [hmap]
      _ = ∫ u in C, f (skpChart F u) := by
          rw [hemb.restrict_map, hemb.integral_map,
            preimage_image_eq _ hiso.injective]
  -- `|[[F]](ω)| ≤ sup |ω(·)(e_F)|`.
  have skp_face_action_bound : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (ω : Eucl N → Covector (Eucl N) n) (hω : Continuous ω) (C : ℝ) (hC : ∀ x, |ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))| ≤ C), |latticeFaceAction 1 F ω| ≤ C := by
    clear * - skpChart skp_volume_cube skp_cube_finite skp_face_integral
    revert skpChart skp_volume_cube skp_cube_finite skp_face_integral
    refine id ?_
    intro skpChart skp_volume_cube skp_cube_finite skp_face_integral n N F ω hω C hC
    unfold latticeFaceAction
    rw [skp_face_integral]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) (C := C)
      (f := fun u => ω (skpChart F u) (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)))
      (by rw [skp_volume_cube]; exact ENNReal.one_lt_top) (fun u _ => by
        rw [Real.norm_eq_abs]; exact hC _)
    rw [measureReal_def, skp_volume_cube, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at this
    exact this
  -- Faces meeting a compact set: a finite set.
  have skp_faces_finite : ∀ {n N : ℕ} (K : Set (Eucl N)) (hK : IsCompact K), {F : LatticeFaceIndex n N | (latticeFace 1 F ∩ K).Nonempty}.Finite := by
    clear * - skp_locallyFinite skp_cube_finite
    revert skp_locallyFinite skp_cube_finite
    refine id ?_
    intro skp_locallyFinite skp_cube_finite n N K hK
    exact skp_locallyFinite.finite_nonempty_inter_compact hK
  have skp_action_zero : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (ω : Eucl N → Covector (Eucl N) n) (h : ¬ (latticeFace 1 F ∩ tsupport ω).Nonempty), latticeFaceAction 1 F ω = 0 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite n N F ω h
    unfold latticeFaceAction
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have : ω x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => h ⟨x, hx, h'⟩)
    simp [this]
  have skp_action_add : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (ω η : Eucl N → Covector (Eucl N) n) (hω : Continuous ω) (hη : Continuous η), latticeFaceAction 1 F (ω + η) = latticeFaceAction 1 F ω + latticeFaceAction 1 F η := by
    clear * - skpChart skp_isCompact_box skp_cube_finite skp_cube_integrable skpChart_contDiff skp_eval_continuous skp_face_integral
    revert skpChart skp_isCompact_box skp_cube_finite skp_cube_integrable skpChart_contDiff skp_eval_continuous skp_face_integral
    refine id ?_
    intro skpChart skp_isCompact_box skp_cube_finite skp_cube_integrable skpChart_contDiff skp_eval_continuous skp_face_integral n N F ω η hω hη
    unfold latticeFaceAction
    rw [skp_face_integral, skp_face_integral, skp_face_integral]
    simp only [Pi.add_apply, ContinuousAlternatingMap.add_apply]
    have hint : ∀ ζ : Eucl N → Covector (Eucl N) n, Continuous ζ →
        IntegrableOn (fun u => ζ (skpChart F u) (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)))
          {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
      intro ζ hζ
      have hc : Continuous fun u => ζ (skpChart F u) (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) :=
        skp_eval_continuous _ (hζ.comp (skpChart_contDiff F).continuous) _
      obtain ⟨C, hC⟩ := (skp_isCompact_box (fun _ : Fin n => (0 : ℝ)) (fun _ => 1)).exists_bound_of_continuousOn
        hc.continuousOn
      refine skp_cube_integrable _ hc C fun u hu => ?_
      have := hC u (fun j => ⟨(hu j).1.le, (hu j).2.le⟩)
      rwa [Real.norm_eq_abs] at this
    exact integral_add (hint ω hω) (hint η hη)
  have skp_action_smul : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (c : ℝ) (ω : Eucl N → Covector (Eucl N) n), latticeFaceAction 1 F (c • ω) = c * latticeFaceAction 1 F ω := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite n N F c ω
    unfold latticeFaceAction
    simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  -- The lattice chain current `∑ β_F [[F]]`.
  have skp_chain_exists : ∀ {N m : ℕ} (β : LatticeFaceIndex (m + 1) N → ℝ), ∃ P : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1), IsLatticeChain 1 β P ∧
        ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)) (S : Finset (LatticeFaceIndex (m + 1) N)),
          (∀ F, (latticeFace 1 F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty →
            F ∈ S) →
          P ω = ∑ F ∈ S, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1)) := by
    clear * - skp_cube_finite skp_face_action_bound skp_faces_finite skp_action_zero skp_action_add skp_action_smul
    revert skp_cube_finite skp_face_action_bound skp_faces_finite skp_action_zero skp_action_add skp_action_smul
    refine id ?_
    intro skp_cube_finite skp_face_action_bound skp_faces_finite skp_action_zero skp_action_add skp_action_smul N m β
    classical
    set fin : TestFormOn (univ : Set (Eucl N)) (m + 1) → Finset (LatticeFaceIndex (m + 1) N) :=
      fun ω => (skp_faces_finite (n := m + 1) _ ω.property.1.2).toFinset with hfin
    have hfin_mem : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)) F,
        (latticeFace 1 F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty →
        F ∈ fin ω := by
      intro ω F h
      simp [hfin, h]
    have htsum : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)) (S : Finset (LatticeFaceIndex (m + 1) N)),
        (∀ F, (latticeFace 1 F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty → F ∈ S) →
        ∑' F, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1)) =
          ∑ F ∈ S, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1)) := by
      intro ω S hS
      apply tsum_eq_sum
      intro F hF
      rw [skp_action_zero F _ (fun h => hF (hS F h)), mul_zero]
    set L : TestFormOn (univ : Set (Eucl N)) (m + 1) →ₗ[ℝ] ℝ :=
      { toFun := fun ω => ∑' F, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1))
        map_add' := by
          intro ω η
          set S := fin ω ∪ fin η ∪ fin (ω + η)
          rw [htsum ω S (fun F h => Finset.mem_union.2 (Or.inl (Finset.mem_union.2
              (Or.inl (hfin_mem ω F h))))),
            htsum η S (fun F h => Finset.mem_union.2 (Or.inl (Finset.mem_union.2
              (Or.inr (hfin_mem η F h))))),
            htsum (ω + η) S (fun F h => Finset.mem_union.2 (Or.inr (hfin_mem (ω + η) F h))),
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun F _ => ?_
          rw [← mul_add]
          congr 1
          exact skp_action_add F _ _ ω.property.1.1.continuous η.property.1.1.continuous
        map_smul' := by
          intro c ω
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [← tsum_mul_left]
          congr 1
          funext F
          change β F * latticeFaceAction 1 F (c • (ω : DifferentialForm (Eucl N) (m + 1))) = _
          rw [skp_action_smul]
          ring } with hL
    refine ⟨⟨L, ?_⟩, fun ω => rfl, fun ω S hS => htsum ω S hS⟩
    -- sequential continuity
    intro ωs hconv
    obtain ⟨K, hK, _, hsupp, _, hunif⟩ := hconv
    set S := (skp_faces_finite (n := m + 1) K hK).toFinset
    have hS : ∀ j F, (latticeFace 1 F ∩ tsupport ((ωs j : TestFormOn (univ : Set (Eucl N)) (m + 1)) :
        DifferentialForm (Eucl N) (m + 1))).Nonempty → F ∈ S := by
      intro j F ⟨x, hx1, hx2⟩
      simp only [S, Set.Finite.mem_toFinset, mem_setOf_eq]
      exact ⟨x, hx1, hsupp j hx2⟩
    have heq : ∀ j, L (ωs j) = ∑ F ∈ S, β F * latticeFaceAction 1 F
        ((ωs j : TestFormOn (univ : Set (Eucl N)) (m + 1)) : DifferentialForm (Eucl N) (m + 1)) :=
      fun j => htsum (ωs j) S (hS j)
    simp_rw [heq]
    rw [show (0 : ℝ) = ∑ F ∈ S, β F * 0 by simp]
    refine tendsto_finset_sum _ fun F _ => (tendsto_const_nhds.mul ?_)
    -- each face action tends to zero
    have h0 := hunif 0
    rw [Metric.tendstoUniformlyOn_iff] at h0
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨J, hJ⟩ := (h0 (ε / 2) (by positivity)).exists_forall_of_atTop
    refine ⟨J, fun j hj => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hbound : ∀ x, |((ωs j : TestFormOn (univ : Set (Eucl N)) (m + 1)) :
        DifferentialForm (Eucl N) (m + 1)) x (fun i => EuclideanSpace.single (F.2 i) (1 : ℝ))| ≤ ε / 2 := by
      intro x
      by_cases hx : x ∈ K
      · have := hJ j hj x hx
        simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero_fun, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at this
        calc _ ≤ ‖((ωs j : TestFormOn (univ : Set (Eucl N)) (m + 1)) :
              DifferentialForm (Eucl N) (m + 1)) x‖ * ∏ i : Fin (m + 1),
                ‖EuclideanSpace.single (F.2 i) (1 : ℝ)‖ :=
              ContinuousAlternatingMap.le_opNorm _ _
          _ ≤ ε / 2 := by simpa using this.le
      · have : ((ωs j : TestFormOn (univ : Set (Eucl N)) (m + 1)) :
            DifferentialForm (Eucl N) (m + 1)) x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h))
        simp [this]; positivity
    calc |latticeFaceAction 1 F _| ≤ ε / 2 :=
          skp_face_action_bound F _ (ωs j).property.1.1.continuous _ hbound
      _ < ε := by linarith
  -- Difference of two currents.
  have skp_sub_current : ∀ {N k : ℕ} (A B : GeometricCurrentOn (univ : Set (Eucl N)) k), ∃ S : GeometricCurrentOn (univ : Set (Eucl N)) k, ∀ ω, S ω = A ω - B ω := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k A B
    exact ⟨⟨A.toCurrent - B.toCurrent, fun ωs h => by
          simpa using (A.continuous' ωs h).sub (B.continuous' ωs h)⟩, fun ω => rfl⟩
  -- Upper bounds on mass from bounds on admissible evaluations.
  have skp_massOn_le : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (W : Set (Eucl N)) (c : ℝ≥0∞) (h : ∀ ω : TestFormOn (univ : Set (Eucl N)) k, ω ∈ massAdmissibleOn univ k W →
        ENNReal.ofReal (T ω) ≤ c), T.massOn W ≤ c := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k T W c h
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    exact h ω hω
  -- `|T ω| ≤ M(T)` for admissible `ω`.
  have skp_abs_le_mass : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (hT : T.mass < ∞) (ω : TestFormOn (univ : Set (Eucl N)) k) (hω : ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) k) x) ≤ 1), |T ω| ≤ T.mass.toReal := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k T hT ω hω
    have := Submission.cmb_abs_apply_le_of_massOn_le N k univ univ T ω T.mass.toReal 1
      ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal hT.ne]; rfl) (subset_univ _) hω
    simpa using this
  -- Supports: a current vanishing near `x` (on a ball) does not contain `x` in its support.
  have skp_notMem_support : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (x : Eucl N) (r : ℝ) (hr : 0 < r) (h : ∀ ω : TestFormOn (univ : Set (Eucl N)) k,
        tsupport (ω : DifferentialForm (Eucl N) k) ⊆ ball x r → T ω = 0), x ∉ T.support := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k T x r hr h hx
    apply hx.2
    refine mem_sUnion.2 ⟨ball x r, ⟨isOpen_ball, ?_, subset_univ _, h⟩, mem_ball_self hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  -- Vanishing near points outside the support.
  have skp_vanish_of_notMem_support : ∀ {N k : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) k) (x : Eucl N) (hx : x ∉ T.support), ∃ r > 0, ∀ ω : TestFormOn (univ : Set (Eucl N)) k,
        tsupport (ω : DifferentialForm (Eucl N) k) ⊆ ball x r → T ω = 0 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k T x hx
    have hz : x ∈ T.zeroRegion := by
      by_contra h
      exact hx ⟨mem_univ x, h⟩
    obtain ⟨W, ⟨hWo, _, _, hWv⟩, hxW⟩ := mem_sUnion.1 hz
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo x hxW
    exact ⟨r, hr, fun ω hω => hWv ω (hω.trans hrW)⟩
  -- `spt ∂T ⊆ spt T`.
  have skp_support_boundary : ∀ {N m : ℕ} (T : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), T.boundary.support ⊆ T.support := by
    clear * - skp_cube_finite skp_notMem_support skp_vanish_of_notMem_support
    revert skp_cube_finite skp_notMem_support skp_vanish_of_notMem_support
    refine id ?_
    intro skp_cube_finite skp_notMem_support skp_vanish_of_notMem_support N m T x hx
    by_contra h
    obtain ⟨r, hr, hT⟩ := skp_vanish_of_notMem_support T x h
    refine skp_notMem_support T.boundary x r hr ?_ hx
    intro φ hφ
    rw [GeometricCurrentOn.boundary_apply]
    exact hT _ ((tsupport_exteriorDerivative_subset _).trans hφ)
  -- Scalar functions of a test form along a chart.
  have skp_form_chart_fun : ∀ {N m : ℕ} (F : LatticeFaceIndex (m + 1) N) (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) ∧
      HasCompactSupport (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) ∧
      ∀ u, |(ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))| ≤
        covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)) := by
    clear * - skp_coord_le_cnorm skpChart skpChart_isometry skp_cube_finite skpChart_contDiff skp_eval_contDiff
    revert skp_coord_le_cnorm skpChart skpChart_isometry skp_cube_finite skpChart_contDiff skp_eval_contDiff
    refine id ?_
    intro skp_coord_le_cnorm skpChart skpChart_isometry skp_cube_finite skpChart_contDiff skp_eval_contDiff N m F ω
    set ω' := (ω : DifferentialForm (Eucl N) (m + 1))
    refine ⟨skp_eval_contDiff _ (ω.property.1.1.comp (skpChart_contDiff F)) _, ?_,
      fun u => skp_coord_le_cnorm _ F.2⟩
    have hK : IsCompact (skpChart F ⁻¹' tsupport ω') :=
      (skpChart_isometry F).isClosedEmbedding.isCompact_preimage ω.property.1.2
    refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
    apply closure_minimal _ (isClosed_tsupport _ |>.preimage (skpChart_contDiff F).continuous)
    intro u hu
    by_contra h
    apply hu
    simp only
    rw [image_eq_zero_of_notMem_tsupport h]
    simp
  have skp_disjoint_sum : ∀ {N m : ℕ} (ν : Measure (Eucl N)) [IsFiniteMeasure ν] (S : Finset (LatticeFaceIndex (m + 1) N)), ∑ F ∈ S, (ν (skpOFace F)).toReal ≤ (ν univ).toReal := by
    clear * - skpOFace skp_oface_disjoint skp_cube_finite skp_measurableSet_oface
    revert skpOFace skp_oface_disjoint skp_cube_finite skp_measurableSet_oface
    refine id ?_
    intro skpOFace skp_oface_disjoint skp_cube_finite skp_measurableSet_oface N m ν _ S
    classical
    rw [← ENNReal.toReal_sum (fun F _ => measure_ne_top ν _)]
    apply ENNReal.toReal_mono (measure_ne_top ν _)
    rw [← measure_biUnion_finset (fun F _ G _ h => skp_oface_disjoint F G h)
      (fun F _ => skp_measurableSet_oface F)]
    exact measure_mono (subset_univ _)
  have skp_faces_finset : ∀ {N k : ℕ} (K : Set (Eucl N)) (hK : IsCompact K), ∃ S : Finset (LatticeFaceIndex k N), ∀ F, (latticeFace 1 F ∩ K).Nonempty → F ∈ S := by
    clear * - skp_cube_finite skp_faces_finite
    revert skp_cube_finite skp_faces_finite
    refine id ?_
    intro skp_cube_finite skp_faces_finite N k K hK
    exact ⟨(skp_faces_finite K hK).toFinset, fun F h => by simp [h]⟩
  have skp_ofReal_le_mul : ∀ {a t : ℝ} (ha : 0 ≤ a) (T : ℝ≥0∞) (hT : T < ∞) (h : t ≤ a * T.toReal), ENNReal.ofReal t ≤ ENNReal.ofReal a * T := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite a t ha T hT h
    calc ENNReal.ofReal t ≤ ENNReal.ofReal (a * T.toReal) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal a * T := by rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal hT.ne]
  -- The assembly lemma.
  have skp_assemble : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hQ : Q.mass < ∞) (hbQ : Q.boundary.mass < ∞) (μ : Measure (Eucl N)) [IsFiniteMeasure μ] (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hμ : ∀ W : Set (Eucl N), IsOpen W → Q.massOn W = μ W) (hμS : μ Q.supportᶜ = 0) (μ' : Measure (Eucl N)) [IsFiniteMeasure μ'] (hμ' : ∀ W : Set (Eucl N), IsOpen W → Q.boundary.massOn W = μ' W) (hμ'S : μ' Q.boundary.supportᶜ = 0) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (a₁ a₂ a₃ : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (β : LatticeFaceIndex (m + 1) N → ℝ) (hβ1 : ∀ F (g : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
        (∀ u, |g u| ≤ B) →
        |∫ x in skpOFace F, g (skpProj F x) *
            v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
          β F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤
          (a₁ * (μ' (skpOFace F)).toReal) * B) (hβ3 : ∀ F (Φ : Fin (m + 1) → Eucl (m + 1) → ℝ), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) →
        (∀ k, HasCompactSupport (Φ k)) → ∀ B : ℝ, 0 ≤ B → (∀ k u, |Φ k u| ≤ B) →
        |∫ x in skpOFace F, (∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ))) *
            v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
          β F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1},
            ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))| ≤
          (a₃ * (μ' (skpOFace F)).toReal) * B) (hβ2 : ∀ F, |β F| ≤ a₂ * (μ (skpOFace F)).toReal), ∃ (P S : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)), IsLatticeChain 1 β P ∧
        (∀ ω, Q ω - P ω = S ω) ∧ P.mass ≤ ENNReal.ofReal a₂ * Q.mass ∧
        P.boundary.mass ≤ ENNReal.ofReal (1 + a₃) * Q.boundary.mass ∧
        S.mass ≤ ENNReal.ofReal a₁ * Q.boundary.mass ∧
        P.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.support ∧
        P.boundary.support ∪ S.support ⊆
          cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.boundary.support := by
    clear * - skp_coord_le_cnorm skpOFace skp_oface_subset_face skp_isClosed_face skp_locallyFinite skp_face_dist skpChart skpProj skp_oface_iff skpChart_mem_oface skp_cube_finite skp_face_decomp skp_face_integral_chart skp_chart_field skp_face_integral skp_face_action_bound skp_action_zero skp_chain_exists skp_sub_current skp_massOn_le skp_abs_le_mass skp_notMem_support skp_vanish_of_notMem_support skp_form_chart_fun skp_disjoint_sum skp_faces_finset skp_ofReal_le_mul
    revert skp_coord_le_cnorm skpOFace skp_oface_subset_face skp_isClosed_face skp_locallyFinite skp_face_dist skpChart skpProj skp_oface_iff skpChart_mem_oface skp_cube_finite skp_face_decomp skp_face_integral_chart skp_chart_field skp_face_integral skp_face_action_bound skp_action_zero skp_chain_exists skp_sub_current skp_massOn_le skp_abs_le_mass skp_notMem_support skp_vanish_of_notMem_support skp_form_chart_fun skp_disjoint_sum skp_faces_finset skp_ofReal_le_mul
    refine id ?_
    intro skp_coord_le_cnorm skpOFace skp_oface_subset_face skp_isClosed_face skp_locallyFinite skp_face_dist skpChart skpProj skp_oface_iff skpChart_mem_oface skp_cube_finite skp_face_decomp skp_face_integral_chart skp_chart_field skp_face_integral skp_face_action_bound skp_action_zero skp_chain_exists skp_sub_current skp_massOn_le skp_abs_le_mass skp_notMem_support skp_vanish_of_notMem_support skp_form_chart_fun skp_disjoint_sum skp_faces_finset skp_ofReal_le_mul N m Q hQ hbQ μ _ v hrep hμ hμS μ' _ hμ' hμ'S hL hdx a₁ a₂ a₃ ha₁ ha₂ ha₃ β hβ1 hβ3 hβ2
    classical
    obtain ⟨P, hPchain, hPsum⟩ := skp_chain_exists (N := N) (m := m) β
    obtain ⟨S, hS⟩ := skp_sub_current Q P
    set cube := {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1} with hcube
    set w : LatticeFaceIndex (m + 1) N → Eucl N → ℝ := fun F x =>
      v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) with hw
    set lam : LatticeFaceIndex (m + 1) N → (Eucl (m + 1) → ℝ) → ℝ := fun F g =>
      ∫ x in skpOFace F, g (skpProj F x) * w F x ∂μ - β F * ∫ u in cube, g u with hlam
    set gf : LatticeFaceIndex (m + 1) N → Eucl N → Covector (Eucl N) (m + 1) → ℝ := fun F _ a =>
      a (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) with hgf
    -- the key formula for `S`
    have hSformula : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1))
        (T : Finset (LatticeFaceIndex (m + 1) N)),
        (∀ F, (latticeFace 1 F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty →
          F ∈ T) →
        S ω = ∑ F ∈ T, lam F (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)
          (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) := by
      intro ω T hT
      rw [hS, skp_face_decomp Q μ v hrep hL hdx ω T (fun F ⟨x, hx1, hx2⟩ =>
        hT F ⟨x, skp_oface_subset_face F hx1, hx2⟩), hPsum ω T hT, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun F _ => ?_
      simp only [hlam]
      rw [skp_face_integral_chart]
      congr 1
      unfold latticeFaceAction
      rw [skp_face_integral]
    -- the scalar functions of forms along charts
    have hgω := fun F ω => skp_form_chart_fun (N := N) (m := m) F ω
    have hmassS : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) (m + 1)) x) ≤ 1) →
        |S ω| ≤ a₁ * Q.boundary.mass.toReal := by
      intro ω hω
      obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
      rw [hSformula ω T hT]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ F ∈ T, (a₁ * (μ' (skpOFace F)).toReal) * 1 := by
            refine Finset.sum_le_sum fun F _ => ?_
            obtain ⟨h1, h2, h3⟩ := hgω F ω
            exact hβ1 F _ h1 h2 1 zero_le_one fun u => (h3 u).trans (hω _)
        _ = a₁ * ∑ F ∈ T, (μ' (skpOFace F)).toReal := by rw [Finset.mul_sum]; simp
        _ ≤ a₁ * (μ' univ).toReal := mul_le_mul_of_nonneg_left (skp_disjoint_sum μ' T) ha₁
        _ = a₁ * Q.boundary.mass.toReal := by
            rw [← hμ' univ isOpen_univ]; rfl
    -- boundary of `S`
    have hmassbS : ∀ (φ : TestFormOn (univ : Set (Eucl N)) m),
        (∀ x, covectorEuclideanNorm ((φ : DifferentialForm (Eucl N) m) x) ≤ 1) →
        |S (exteriorDerivativeTestOn univ m φ)| ≤ a₃ * Q.boundary.mass.toReal := by
      intro φ hφ
      obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _
        (exteriorDerivativeTestOn univ m φ).property.1.2
      rw [hSformula _ T hT]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ F ∈ T, (a₃ * (μ' (skpOFace F)).toReal) * 1 := by
            refine Finset.sum_le_sum fun F _ => ?_
            set Φ : Fin (m + 1) → Eucl (m + 1) → ℝ := fun i u => ((-1 : ℝ) ^ (i : ℕ)) *
              (φ : DifferentialForm (Eucl N) m) (skpChart F u)
                (fun j => EuclideanSpace.single (F.2 (i.succAbove j)) (1 : ℝ)) with hΦ
            obtain ⟨hs, hc, hb, hd⟩ := skp_chart_field F φ Φ hΦ
            have heq : (fun u => ((exteriorDerivativeTestOn univ m φ :
                TestFormOn (univ : Set (Eucl N)) (m + 1)) : DifferentialForm (Eucl N) (m + 1))
                (skpChart F u) (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) =
                fun u => ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ)) := by
              funext u; exact hd u
            rw [heq]
            exact hβ3 F Φ hs hc 1 zero_le_one fun k u => (hb k u).trans (hφ _)
        _ = a₃ * ∑ F ∈ T, (μ' (skpOFace F)).toReal := by rw [Finset.mul_sum]; simp
        _ ≤ a₃ * (μ' univ).toReal := mul_le_mul_of_nonneg_left (skp_disjoint_sum μ' T) ha₃
        _ = a₃ * Q.boundary.mass.toReal := by
            rw [← hμ' univ isOpen_univ]; rfl
    -- mass of `P`
    have hmassP : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl N) (m + 1)) x) ≤ 1) →
        |P ω| ≤ a₂ * Q.mass.toReal := by
      intro ω hω
      obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
      rw [hPsum ω T hT]
      calc |∑ F ∈ T, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1))|
          ≤ ∑ F ∈ T, |β F| * 1 := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact skp_face_action_bound F _ ω.property.1.1.continuous 1 fun x =>
              (skp_coord_le_cnorm _ F.2).trans (hω x)
        _ ≤ ∑ F ∈ T, a₂ * (μ (skpOFace F)).toReal := by
            refine Finset.sum_le_sum fun F _ => ?_
            rw [mul_one]; exact hβ2 F
        _ = a₂ * ∑ F ∈ T, (μ (skpOFace F)).toReal := by rw [Finset.mul_sum]
        _ ≤ a₂ * (μ univ).toReal := mul_le_mul_of_nonneg_left (skp_disjoint_sum μ T) ha₂
        _ = a₂ * Q.mass.toReal := by rw [← hμ univ isOpen_univ]; rfl
    refine ⟨P, S, hPchain, fun ω => (hS ω).symm, ?_, ?_, ?_, ?_, ?_⟩
    · -- `M(P) ≤ a₂ M(Q)`
      apply skp_massOn_le
      intro ω hω
      exact skp_ofReal_le_mul ha₂ _ hQ ((le_abs_self _).trans (hmassP ω hω.2))
    · -- `M(∂P) ≤ (1 + a₃) M(∂Q)`
      apply skp_massOn_le
      intro φ hφ
      apply skp_ofReal_le_mul (by linarith) _ hbQ
      have h1 : P.boundary φ = Q.boundary φ - S (exteriorDerivativeTestOn univ m φ) := by
        rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hS]; ring
      rw [h1]
      have h2 := skp_abs_le_mass Q.boundary hbQ φ hφ.2
      have h3 := hmassbS φ hφ.2
      calc Q.boundary φ - S (exteriorDerivativeTestOn univ m φ)
          ≤ |Q.boundary φ| + |S (exteriorDerivativeTestOn univ m φ)| := by
            have := le_abs_self (Q.boundary φ)
            have := neg_abs_le (S (exteriorDerivativeTestOn univ m φ))
            linarith
        _ ≤ Q.boundary.mass.toReal + a₃ * Q.boundary.mass.toReal := add_le_add h2 h3
        _ = (1 + a₃) * Q.boundary.mass.toReal := by ring
    · -- `M(S) ≤ a₁ M(∂Q)`
      apply skp_massOn_le
      intro ω hω
      exact skp_ofReal_le_mul ha₁ _ hbQ ((le_abs_self _).trans (hmassS ω hω.2))
    · -- support of `P`
      have hPsupp : P.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.support := by
        intro x hx
        by_contra hxt
        have hlf : LocallyFinite (fun F : LatticeFaceIndex (m + 1) N =>
            if β F ≠ 0 then latticeFace 1 F else ∅) :=
          skp_locallyFinite.subset fun F => by split_ifs <;> simp
        have hUc : IsClosed (⋃ F : LatticeFaceIndex (m + 1) N,
            if β F ≠ 0 then latticeFace 1 F else ∅) :=
          hlf.isClosed_iUnion fun F => by
            split_ifs
            · exact skp_isClosed_face F
            · exact isClosed_empty
        have hxU : x ∉ ⋃ F : LatticeFaceIndex (m + 1) N,
            if β F ≠ 0 then latticeFace 1 F else ∅ := by
          intro hxU
          obtain ⟨F, hF⟩ := mem_iUnion.1 hxU
          split_ifs at hF with hβF
          · apply hxt
            have hμF : μ (skpOFace F) ≠ 0 := by
              intro h0
              have := hβ2 F
              rw [h0, ENNReal.toReal_zero, mul_zero] at this
              exact hβF (abs_nonpos_iff.1 this)
            have hne : (skpOFace F ∩ Q.support).Nonempty := by
              by_contra hem
              rw [not_nonempty_iff_eq_empty] at hem
              apply hμF
              refine measure_mono_null (fun y hy => ?_) hμS
              intro hyS
              have : y ∈ skpOFace F ∩ Q.support := ⟨hy, hyS⟩
              rw [hem] at this
              exact this
            obtain ⟨y, hy1, hy2⟩ := hne
            exact mem_cthickening_of_dist_le x y _ _ hy2
              (skp_face_dist F x y hF (skp_oface_subset_face F hy1))
          · exact hF
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUc.isOpen_compl x hxU
        refine skp_notMem_support P x r hr ?_ hx
        intro ω hω
        obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
        rw [hPsum ω T hT]
        refine Finset.sum_eq_zero fun F _ => ?_
        by_cases hβF : β F = 0
        · rw [hβF, zero_mul]
        · rw [skp_action_zero F _ ?_, mul_zero]
          rintro ⟨y, hy1, hy2⟩
          have hyU := hrU (hω hy2)
          apply hyU
          exact mem_iUnion.2 ⟨F, by rw [if_pos hβF]; exact hy1⟩
      exact hPsupp
    · -- supports of `S` and `∂P`
      have hSsupp : S.support ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ)) Q.boundary.support := by
        intro x hx
        by_contra hxt
        have hlf : LocallyFinite (fun F : LatticeFaceIndex (m + 1) N =>
            if μ' (skpOFace F) ≠ 0 then latticeFace 1 F else ∅) :=
          skp_locallyFinite.subset fun F => by split_ifs <;> simp
        have hUc : IsClosed (⋃ F : LatticeFaceIndex (m + 1) N,
            if μ' (skpOFace F) ≠ 0 then latticeFace 1 F else ∅) :=
          hlf.isClosed_iUnion fun F => by
            split_ifs
            · exact skp_isClosed_face F
            · exact isClosed_empty
        have hxU : x ∉ ⋃ F : LatticeFaceIndex (m + 1) N,
            if μ' (skpOFace F) ≠ 0 then latticeFace 1 F else ∅ := by
          intro hxU
          obtain ⟨F, hF⟩ := mem_iUnion.1 hxU
          split_ifs at hF with hμF
          · apply hxt
            have hne : (skpOFace F ∩ Q.boundary.support).Nonempty := by
              by_contra hem
              rw [not_nonempty_iff_eq_empty] at hem
              apply hμF
              refine measure_mono_null (fun y hy => ?_) hμ'S
              intro hyS
              have : y ∈ skpOFace F ∩ Q.boundary.support := ⟨hy, hyS⟩
              rw [hem] at this
              exact this
            obtain ⟨y, hy1, hy2⟩ := hne
            exact mem_cthickening_of_dist_le x y _ _ hy2
              (skp_face_dist F x y hF (skp_oface_subset_face F hy1))
          · exact hF
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUc.isOpen_compl x hxU
        refine skp_notMem_support S x r hr ?_ hx
        intro ω hω
        obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
        rw [hSformula ω T hT]
        refine Finset.sum_eq_zero fun F _ => ?_
        obtain ⟨h1, h2, h3⟩ := hgω F ω
        by_cases hμF : μ' (skpOFace F) = 0
        · obtain ⟨B, hB⟩ := h2.exists_bound_of_continuous h1.continuous
          have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
          have := hβ1 F _ h1 h2 B hB0 (fun u => by simpa [Real.norm_eq_abs] using hB u)
          rw [hμF, ENNReal.toReal_zero, mul_zero, zero_mul] at this
          exact abs_nonpos_iff.1 this
        · have hzero : ∀ u ∈ cube, (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u)
              (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0 := by
            intro u hu
            have hmem : skpChart F u ∈ latticeFace 1 F :=
              skp_oface_subset_face F ((skpChart_mem_oface F u).2 hu)
            have : (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) = 0 := by
              apply image_eq_zero_of_notMem_tsupport
              intro hsupp
              have hyU := hrU (hω hsupp)
              exact hyU (mem_iUnion.2 ⟨F, by rw [if_pos hμF]; exact hmem⟩)
            rw [this]; rfl
          simp only [hlam]
          rw [setIntegral_eq_zero_of_forall_eq_zero (fun y hy => by
              rw [hzero _ ((skp_oface_iff F y).1 hy).2, zero_mul]),
            setIntegral_eq_zero_of_forall_eq_zero hzero]
          ring
      refine union_subset ?_ hSsupp
      intro x hx
      by_contra hxt
      have hx1 : x ∉ Q.boundary.support := fun h => hxt (self_subset_cthickening _ h)
      have hx2 : x ∉ S.support := fun h => hxt (hSsupp h)
      obtain ⟨r₁, hr₁, hv₁⟩ := skp_vanish_of_notMem_support Q.boundary x hx1
      obtain ⟨r₂, hr₂, hv₂⟩ := skp_vanish_of_notMem_support S x hx2
      refine skp_notMem_support P.boundary x (min r₁ r₂) (lt_min hr₁ hr₂) ?_ hx
      intro φ hφ
      have hb1 := hv₁ φ (hφ.trans (ball_subset_ball (min_le_left _ _)))
      have hb2 := hv₂ (exteriorDerivativeTestOn univ m φ)
        ((tsupport_exteriorDerivative_subset _).trans (hφ.trans (ball_subset_ball (min_le_right _ _))))
      rw [GeometricCurrentOn.boundary_apply] at hb1 ⊢
      rw [hS] at hb2
      linarith
  have skp_simple_norm_one : ∀ {N k : ℕ} (τ : Fin k → Eucl N) (hτ : Orthonormal ℝ τ), ‖simpleNVector τ‖ = 1 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k τ hτ
    have h := (Submission.lpf_simple_nvector_algebra).1 N k τ
    have hG : (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      ext i j
      rw [Matrix.of_apply, orthonormal_iff_ite.1 hτ i j, Matrix.one_apply]
    rw [hG, Matrix.det_one] at h
    have h0 := norm_nonneg (simpleNVector τ)
    nlinarith [sq_nonneg (‖simpleNVector τ‖ - 1), sq_nonneg (‖simpleNVector τ‖ + 1)]
  have skp_eF_orthonormal : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), Orthonormal ℝ (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite n N F
    rw [orthonormal_iff_ite]
    intro i j
    by_cases h : i = j
    · subst h; simp [EuclideanSpace.inner_single_left]
    · simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, h,
        F.2.injective.ne h]
  have skp_nvector_expand : ∀ {N k : ℕ} (w : NVector (Eucl N) k) (α : Covector (Eucl N) k), w α = ∑ γ : SimonMultiIndex k N, α (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) *
        w (wedgeCovectors k (fun j => EuclideanSpace.proj (γ j))) := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k w α
    conv_lhs => rw [Submission.cmb_covector_eq_sum_coord_smul_wedge N k α]
    rw [map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  -- If all the coordinates of an `n`-vector except one vanish, it is a multiple of the simple `n`-vector of that coordinate direction.
  have skp_nvector_single : ∀ {N k : ℕ} (w : NVector (Eucl N) k) (γ₀ : SimonMultiIndex k N) (h : ∀ γ, γ ≠ γ₀ → w (wedgeCovectors k (fun j => EuclideanSpace.proj (γ j))) = 0), w = w (wedgeCovectors k (fun j => EuclideanSpace.proj (γ₀ j))) •
        simpleNVector (fun j => EuclideanSpace.single (γ₀ j) (1 : ℝ)) := by
    clear * - skp_cube_finite skp_nvector_expand
    revert skp_cube_finite skp_nvector_expand
    refine id ?_
    intro skp_cube_finite skp_nvector_expand N k w γ₀ h
    ext α
    rw [skp_nvector_expand, Finset.sum_eq_single γ₀ (fun γ _ hγ => by rw [h γ hγ, mul_zero])
      (by simp)]
    simp only [ContinuousLinearMap.smul_apply, simpleNVector_apply, smul_eq_mul]
    ring
  -- Smooth tests supported in an open set give a.e. vanishing there.
  have skp_ae_zero_of_smooth_open : ∀ {N : ℕ} (μ₀ : Measure (Eucl N)) (g : Eucl N → ℝ) (O : Set (Eucl N)) (hO : IsOpen O) (hloc : ∀ R : ℝ, IntegrableOn g (closedBall 0 R) μ₀) (h : ∀ f : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ O →
        ∫ x, f x * g x ∂μ₀ = 0), ∀ᵐ x ∂μ₀, x ∈ O → g x = 0 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N μ₀ g O hO hloc h
    have hR : ∀ R : ℕ, ∀ᵐ x ∂μ₀, x ∈ O ∩ ball (0 : Eucl N) R → g x = 0 := by
      intro R
      set U : Set (Eucl N) := O ∩ ball (0 : Eucl N) R with hU
      have hUo : IsOpen U := hO.inter isOpen_ball
      set g₁ := U.indicator g with hg₁_def
      have hg₁ : Integrable g₁ μ₀ :=
        ((hloc R).mono_set ((inter_subset_right).trans ball_subset_closedBall)).integrable_indicator
          hUo.measurableSet
      have hsmooth : ∀ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ U → ∫ x, φ x * g₁ x ∂μ₀ = ∫ x, φ x * (0 : Eucl N → ℝ) x ∂μ₀ := by
        intro φ hφ hφc hφs
        simp only [Pi.zero_apply, mul_zero, integral_zero]
        rw [← h φ hφ hφc (hφs.trans inter_subset_left)]
        congr 1
        funext x
        by_cases hx : x ∈ U
        · simp [hg₁_def, Set.indicator_of_mem hx]
        · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hφs h'))
          simp [this]
      have hcont := Submission.slicing_ru_smooth_to_continuous N μ₀ μ₀ g₁ 0 hg₁
        (integrable_zero _ _ _) U hUo hsmooth
      have hbdd := Submission.slicing_ru_continuous_to_bounded N μ₀ μ₀ g₁ 0 hg₁
        (integrable_zero _ _ _) U hUo hcont
      set g₂ := hg₁.aestronglyMeasurable.mk g₁ with hg₂_def
      have hg₂m : Measurable g₂ := hg₁.aestronglyMeasurable.stronglyMeasurable_mk.measurable
      have hg₁₂ : g₁ =ᵐ[μ₀] g₂ := hg₁.aestronglyMeasurable.ae_eq_mk
      set hh : Eucl N → ℝ := (U ∩ {x | 0 < g₂ x}).indicator 1 -
        (U ∩ {x | g₂ x < 0}).indicator 1 with hh_def
      have hhm : Measurable hh := by
        refine Measurable.sub ?_ ?_
        · exact measurable_one.indicator (hUo.measurableSet.inter
            (measurableSet_lt measurable_const hg₂m))
        · exact measurable_one.indicator (hUo.measurableSet.inter
            (measurableSet_lt hg₂m measurable_const))
      have hhb : ∃ C : ℝ, ∀ x, |hh x| ≤ C := by
        refine ⟨1, fun x => ?_⟩
        simp only [hh_def, Pi.sub_apply]
        by_cases h1 : x ∈ U ∩ {x | 0 < g₂ x}
        · have h2 : x ∉ U ∩ {x | g₂ x < 0} := fun h' => by
            have := h1.2; have := h'.2; simp only [mem_setOf_eq] at *; linarith
          simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
        · by_cases h2 : x ∈ U ∩ {x | g₂ x < 0}
          · simp [Set.indicator_of_mem h2, Set.indicator_of_notMem h1]
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hhO : ∀ x, x ∉ U → hh x = 0 := by
        intro x hx
        have h1 : x ∉ U ∩ {x | 0 < g₂ x} := fun h' => hx h'.1
        have h2 : x ∉ U ∩ {x | g₂ x < 0} := fun h' => hx h'.1
        simp [hh_def, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hint := hbdd hh hhm hhb hhO
      simp only [Pi.zero_apply, mul_zero, integral_zero] at hint
      have habs : (fun x => hh x * g₁ x) =ᵐ[μ₀] fun x => |g₁ x| := by
        filter_upwards [hg₁₂] with x hx
        by_cases hxb : x ∈ U
        · rcases lt_trichotomy (g₂ x) 0 with hneg | hzero | hpos
          · have h1 : x ∉ U ∩ {x | 0 < g₂ x} := fun h' => by
              have := h'.2; simp only [mem_setOf_eq] at this; linarith
            have h2 : x ∈ U ∩ {x | g₂ x < 0} := ⟨hxb, hneg⟩
            simp only [hh_def, Pi.sub_apply, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Pi.one_apply]
            rw [hx, abs_of_neg hneg]; ring
          · rw [hx, hzero]; simp
          · have h1 : x ∈ U ∩ {x | 0 < g₂ x} := ⟨hxb, hpos⟩
            have h2 : x ∉ U ∩ {x | g₂ x < 0} := fun h' => by
              have := h'.2; simp only [mem_setOf_eq] at this; linarith
            simp only [hh_def, Pi.sub_apply, Set.indicator_of_notMem h2, Set.indicator_of_mem h1,
              Pi.one_apply]
            rw [hx, abs_of_pos hpos]; ring
        · have : g₁ x = 0 := by simp [hg₁_def, Set.indicator_of_notMem hxb]
          rw [this, hhO x hxb]; simp
      have hzero : ∫ x, |g₁ x| ∂μ₀ = 0 := by
        rw [← integral_congr_ae habs, hint]
      have hae : (fun x => |g₁ x|) =ᵐ[μ₀] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hg₁.abs).1 hzero
      filter_upwards [hae] with x hx hxU
      have : |g₁ x| = 0 := hx
      rw [abs_eq_zero] at this
      simpa [hg₁_def, Set.indicator_of_mem hxU] using this
    rw [← ae_all_iff] at hR
    filter_upwards [hR] with x hx hxO
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    exact hx R ⟨hxO, by rw [mem_ball, dist_zero_right]; exact hR⟩
  -- Integer multiplicity data give a measure representation.
  have skp_int_rep : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) (m + 1)) (hT : IsRectifiableTriple univ (m + 1) M θ ξ) (hQ : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1), Q ω = tauAction (m + 1) M θ ξ ω), (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M), ‖ξ x‖ = 1) ∧
      IsMeasureRepresentation Q ((μHE[m + 1] : Measure (Eucl N)).restrict M) (fun x => θ x • ξ x) := by
    clear * - skp_cube_finite skp_simple_norm_one
    revert skp_cube_finite skp_simple_norm_one
    refine id ?_
    intro skp_cube_finite skp_simple_norm_one N m Q M θ ξ hT hQ
    have hnorm : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M), ‖ξ x‖ = 1 := by
      filter_upwards [hT.orients] with x ⟨τ, hτ, _, hξ⟩
      rcases hξ with h | h
      · rw [h, skp_simple_norm_one τ hτ]
      · rw [h, ContinuousLinearMap.opNorm_neg, skp_simple_norm_one τ hτ]
    refine ⟨hnorm, fun ω => ⟨?_, ?_⟩⟩
    · set ω' := (ω : DifferentialForm (Eucl N) (m + 1))
      set K := tsupport ω'
      have hK : IsCompact K := ω.property.1.2
      have hKm : MeasurableSet K := hK.isClosed.measurableSet
      obtain ⟨Cω, hCω⟩ := hK.exists_bound_of_continuousOn ω.property.1.1.continuous.continuousOn
      have hsupp : Function.support (fun x => (θ x • ξ x) (ω' x)) ⊆ K := by
        intro x hx
        by_contra hxK
        apply hx
        show (θ x • ξ x) (ω' x) = 0
        rw [image_eq_zero_of_notMem_tsupport hxK]
        simp
      rw [← integrableOn_iff_integrable_of_support_subset hsupp]
      rw [IntegrableOn, Measure.restrict_restrict hKm]
      have hθ : Integrable θ ((μHE[m + 1] : Measure (Eucl N)).restrict (K ∩ M)) := by
        have := hT.integrableOn K hK (subset_univ _)
        rwa [IntegrableOn, inter_comm] at this
      have hξm : AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl N)).restrict (K ∩ M)) :=
        hT.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
      have hpair : AEStronglyMeasurable (fun x => ξ x (ω' x))
          ((μHE[m + 1] : Measure (Eucl N)).restrict (K ∩ M)) :=
        ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Eucl N) (m + 1))
          (F := ℝ)).continuous.comp_aestronglyMeasurable
            (hξm.prodMk ω.property.1.1.continuous.aestronglyMeasurable))
      have hbd : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict (K ∩ M)), ‖ξ x (ω' x)‖ ≤ Cω := by
        have hnorm' : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict (K ∩ M)), ‖ξ x‖ = 1 :=
          ae_mono (Measure.restrict_mono inter_subset_right le_rfl) hnorm
        filter_upwards [hnorm', ae_restrict_mem₀ (hKm.nullMeasurableSet.inter
          hT.nullMeasurableSet)] with x hx hxKM
        calc ‖ξ x (ω' x)‖ ≤ ‖ξ x‖ * ‖ω' x‖ := (ξ x).le_opNorm _
          _ ≤ 1 * Cω := by rw [hx]; exact mul_le_mul_of_nonneg_left (hCω x hxKM.1) zero_le_one
          _ = Cω := one_mul _
      have := hθ.bdd_mul hpair hbd
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [mul_comm]
    · rw [hQ ω]
      unfold tauAction
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp
  have skp_nvector_norm_smul : ∀ {N k : ℕ} (c : ℝ) (w : NVector (Eucl N) k), ‖c • w‖ = |c| * ‖w‖ := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite N k c w
    apply le_antisymm
    · have := ContinuousLinearMap.opNorm_smul_le (𝕜' := ℝ) c w
      rwa [Real.norm_eq_abs] at this
    · by_cases hc : c = 0
      · rw [hc, abs_zero, zero_mul]; exact ContinuousLinearMap.opNorm_nonneg _
      · have h := ContinuousLinearMap.opNorm_smul_le (𝕜' := ℝ) c⁻¹ (c • w)
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul, Real.norm_eq_abs, abs_inv] at h
        have hc' : 0 < |c| := abs_pos.2 hc
        calc |c| * ‖w‖ ≤ |c| * (|c|⁻¹ * ‖c • w‖) := mul_le_mul_of_nonneg_left h hc'.le
          _ = ‖c • w‖ := by field_simp
  have skp_cnorm_dx_eq_one : ∀ {k N : ℕ} (γ : SimonMultiIndex k N), covectorEuclideanNorm (wedgeCovectors k (fun j => EuclideanSpace.proj (γ j))) = 1 := by
    clear * - skp_cube_finite skp_dx_kron_self skp_dx_kron_ne
    revert skp_cube_finite skp_dx_kron_self skp_dx_kron_ne
    refine id ?_
    intro skp_cube_finite skp_dx_kron_self skp_dx_kron_ne k N γ
    classical
    unfold covectorEuclideanNorm
    rw [Finset.sum_eq_single (γ : Fin k → Fin N)]
    · simp only [γ.strictMono, ite_true, EuclideanSpace.basisFun_apply]
      rw [skp_dx_kron_self]
      simp
    · intro I _ hI
      split_ifs with hm
      · have hne : γ ≠ OrderEmbedding.ofStrictMono I hm := by
          intro h
          apply hI
          rw [h]; rfl
        have := skp_dx_kron_ne γ (OrderEmbedding.ofStrictMono I hm) hne
        simp only [OrderEmbedding.coe_ofStrictMono, EuclideanSpace.basisFun_apply] at this ⊢
        rw [this]
        simp
      · rfl
    · simp
  -- The open face is the isometric image of the open cube, as measures.
  have skp_oface_map : ∀ {n N : ℕ} (F : LatticeFaceIndex n N), (μHE[n] : Measure (Eucl N)).restrict (skpOFace F) =
        Measure.map (skpChart F) (volume.restrict {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}) := by
    clear * - skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_eq_image
    revert skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_eq_image
    refine id ?_
    intro skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_eq_image n N F
    have hiso := skpChart_isometry F
    have hemb : MeasurableEmbedding (skpChart F) := hiso.isClosedEmbedding.measurableEmbedding
    have hmap : (μHE[n] : Measure (Eucl N)).restrict (range (skpChart F)) =
        Measure.map (skpChart F) volume := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    have hsub : skpOFace F ⊆ range (skpChart F) := by
      rw [skp_oface_eq_image]; exact image_subset_range _ _
    rw [← Measure.restrict_restrict_of_subset hsub, hmap, hemb.restrict_map, skp_oface_eq_image,
      preimage_image_eq _ hiso.injective]
  have skp_oface_integral : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (f : Eucl N → ℝ), ∫ x in skpOFace F, f x ∂(μHE[n] : Measure (Eucl N)) =
        ∫ u in {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1}, f (skpChart F u) := by
    clear * - skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map
    revert skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map
    refine id ?_
    intro skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map n N F f
    rw [skp_oface_map, (skpChart_isometry F).isClosedEmbedding.measurableEmbedding.integral_map]
  have skp_oface_integrable_iff : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (f : Eucl N → ℝ), IntegrableOn f (skpOFace F) (μHE[n] : Measure (Eucl N)) ↔
        IntegrableOn (fun u => f (skpChart F u)) {u : Eucl n | ∀ j, 0 < u j ∧ u j < 1} := by
    clear * - skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map
    revert skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map
    refine id ?_
    intro skpOFace skpChart skpChart_isometry skp_cube_finite skp_oface_map n N F f
    rw [IntegrableOn, skp_oface_map,
      (skpChart_isometry F).isClosedEmbedding.measurableEmbedding.integrable_map_iff]
    rfl
  -- On an open face only the tangential coefficient survives.
  have skp_v_on_oface : ∀ {N m : ℕ} (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (F : LatticeFaceIndex (m + 1) N), ∀ᵐ x ∂μ, x ∈ skpOFace F → ∀ a : Covector (Eucl N) (m + 1),
        v x a = a (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) := by
    clear * - skpOFace skp_oface_coord skp_cube_finite skp_nvector_expand
    revert skpOFace skp_oface_coord skp_cube_finite skp_nvector_expand
    refine id ?_
    intro skpOFace skp_oface_coord skp_cube_finite skp_nvector_expand N m μ v hdx F
    filter_upwards [hdx] with x hxd hx a
    rw [skp_nvector_expand, Finset.sum_eq_single F.2]
    · intro γ _ hγ
      obtain ⟨i0, hi0⟩ := skp_oface_coord F x hx γ hγ
      rw [hxd γ ⟨i0, F.1 (γ i0), hi0⟩, mul_zero]
    · simp
  -- The carrier of an integer multiplicity representation lies on the support.
  have skp_int_on_support : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) (m + 1)) (hT : IsRectifiableTriple univ (m + 1) M θ ξ) (hQω : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1), Q ω = tauAction (m + 1) M θ ξ ω) (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hμS : μ Q.supportᶜ = 0), ((μHE[m + 1] : Measure (Eucl N)).restrict M) Q.supportᶜ = 0 := by
    clear * - skp_scalar_form_mem skp_rep_integrableOn skp_cube_finite skp_nvector_expand skp_ae_zero_of_smooth_open skp_int_rep
    revert skp_scalar_form_mem skp_rep_integrableOn skp_cube_finite skp_nvector_expand skp_ae_zero_of_smooth_open skp_int_rep
    refine id ?_
    intro skp_scalar_form_mem skp_rep_integrableOn skp_cube_finite skp_nvector_expand skp_ae_zero_of_smooth_open skp_int_rep N m Q M θ ξ hT hQω μ v hrep hμS
    obtain ⟨hnorm, hrep₀⟩ := skp_int_rep Q M θ ξ hT hQω
    set U := Q.supportᶜ with hU
    have hUo : IsOpen U := by
      have : U = Q.zeroRegion := by
        ext x; simp [hU, GeometricCurrentOn.support]
      rw [this]; exact Q.isOpen_zeroRegion
    have hQU : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1),
        tsupport (ω : DifferentialForm (Eucl N) (m + 1)) ⊆ U → Q ω = 0 := by
      intro ω hω
      rw [(hrep ω).2]
      apply integral_eq_zero_of_ae
      have : ∀ᵐ x ∂μ, x ∉ U := measure_eq_zero_iff_ae_notMem.1 hμS
      filter_upwards [this] with x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h))]
      simp
    have hγ : ∀ γ : SimonMultiIndex (m + 1) N, ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M),
        x ∈ U → θ x * ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
      intro γ
      refine skp_ae_zero_of_smooth_open _ _ U hUo (fun R => ?_) (fun f hf hfc hfU => ?_)
      · have := skp_rep_integrableOn Q _ _ hrep₀
          (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) R
        refine this.congr_fun (fun x _ => ?_) measurableSet_closedBall
        simp
      · have h1 := hQU ⟨_, skp_scalar_form_mem f hf hfc
          (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j)))⟩
          ((tsupport_smul_subset_left _ _).trans hfU)
        rw [(hrep₀ _).2] at h1
        rw [← h1]
        congr 1; funext x
        simp only [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
        try ring
    have hall : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M), ∀ γ : SimonMultiIndex (m + 1) N,
        x ∈ U → θ x * ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 :=
      ae_all_iff.2 hγ
    have hpos : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M), 0 < θ x := by
      filter_upwards [ae_restrict_mem₀ hT.nullMeasurableSet] with x hx using hT.pos x hx
    have hnot : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl N)).restrict M), x ∉ U := by
      filter_upwards [hall, hpos, hnorm] with x h1 h2 h3 hxU
      have hξ0 : ξ x = 0 := by
        ext α
        rw [skp_nvector_expand]
        simp only [ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun γ _ => ?_
        have := h1 γ hxU
        rw [mul_eq_zero] at this
        rcases this with h | h
        · linarith
        · rw [h, mul_zero]
      rw [hξ0, ContinuousLinearMap.opNorm_zero] at h3
      exact zero_ne_one h3
    exact measure_eq_zero_iff_ae_notMem.2 hnot
  have skp_int_density : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbQ : Q.boundary.mass < ∞) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) (m + 1)) (hT : IsRectifiableTriple univ (m + 1) M θ ξ) (hQω : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1), Q ω = tauAction (m + 1) M θ ξ ω) (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hμS : μ Q.supportᶜ = 0) (hQs : Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (F : LatticeFaceIndex (m + 1) N) (g : Eucl (m + 1) → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgt : tsupport g ⊆ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}), ∫ x in skpOFace F, g (skpProj F x) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ =
        ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u *
          M.indicator (fun x => θ x *
            ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)))) (skpChart F u) := by
    clear * - skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skpChart skpProj skpProj_chart skp_oface_iff skp_cube_finite skpH skp_dx_kron_self skp_measurableSet_oface skpKappa skpKappa_one skp_int_hyperplane skp_face_decomp skp_face_nform skp_int_rep skp_oface_integral skp_int_on_support
    revert skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skpChart skpProj skpProj_chart skp_oface_iff skp_cube_finite skpH skp_dx_kron_self skp_measurableSet_oface skpKappa skpKappa_one skp_int_hyperplane skp_face_decomp skp_face_nform skp_int_rep skp_oface_integral skp_int_on_support
    refine id ?_
    intro skpOFace skpNbhd skp_oface_subset_face skp_nbhd_face skpChart skpProj skpProj_chart skp_oface_iff skp_cube_finite skpH skp_dx_kron_self skp_measurableSet_oface skpKappa skpKappa_one skp_int_hyperplane skp_face_decomp skp_face_nform skp_int_rep skp_oface_integral skp_int_on_support N m Q hbQ M θ ξ hT hQω μ v hrep hμS hQs hL hdx F g hg hgt
    obtain ⟨hnorm, hrep₀⟩ := skp_int_rep Q M θ ξ hT hQω
    set μ₀ := (μHE[m + 1] : Measure (Eucl N)).restrict M with hμ₀
    have hS₀ : μ₀ Q.supportᶜ = 0 := skp_int_on_support Q M θ ξ hT hQω μ v hrep hμS
    have hL₀ : ∀ᵐ x ∂μ₀, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F := by
      have : μ₀ (⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F)ᶜ = 0 :=
        measure_mono_null (compl_subset_compl.2 hQs) hS₀
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with x hx
      simpa using hx
    have hdx₀ := skp_int_hyperplane Q hbQ μ₀ (fun x => θ x • ξ x) hrep₀
    obtain ⟨hmem, hsupp⟩ := skp_face_nform (N := N) F g hg hgt
    set ω : TestFormOn (univ : Set (Eucl N)) (m + 1) := ⟨_, hmem⟩
    have hS : ∀ F', (skpOFace F' ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty →
        F' ∈ ({F} : Finset (LatticeFaceIndex (m + 1) N)) := by
      rintro F' ⟨x, hx1, hx2⟩
      have := skp_nbhd_face F F' x (hsupp hx2) (skp_oface_subset_face F' hx1)
      simp [this.1]
    have h1 := skp_face_decomp Q μ v hrep hL hdx ω {F} hS
    have h2 := skp_face_decomp Q μ₀ _ hrep₀ hL₀ hdx₀ ω {F} hS
    rw [Finset.sum_singleton] at h1 h2
    have hω_on : ∀ x ∈ skpOFace F, (ω : DifferentialForm (Eucl N) (m + 1)) x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = g (skpProj F x) := by
      intro x hx
      change ((skpKappa F x * g (skpProj F x)) •
        wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) _ = _
      rw [ContinuousAlternatingMap.smul_apply, skp_dx_kron_self,
        skpKappa_one F x ((skp_oface_iff F x).1 hx).1]
      simp
    have e1 : ∫ x in skpOFace F, (ω : DifferentialForm (Eucl N) (m + 1)) x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ =
        ∫ x in skpOFace F, g (skpProj F x) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ :=
      setIntegral_congr_fun (skp_measurableSet_oface F) fun x hx => by rw [hω_on x hx]
    have e2 : ∫ x in skpOFace F, (ω : DifferentialForm (Eucl N) (m + 1)) x
        (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) *
          (θ x • ξ x) (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ₀ =
        ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u *
          M.indicator (fun x => θ x *
            ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)))) (skpChart F u) := by
      rw [setIntegral_congr_fun (skp_measurableSet_oface F) (fun x hx => by
        rw [hω_on x hx, ContinuousLinearMap.smul_apply, smul_eq_mul])]
      -- pass from `μHE ⌞ M` to an indicator
      have hres : ((μHE[m + 1] : Measure (Eucl N)).restrict M).restrict (skpOFace F) =
          ((μHE[m + 1] : Measure (Eucl N)).restrict (skpOFace F)).restrict M := by
        rw [Measure.restrict_restrict (skp_measurableSet_oface F),
          Measure.restrict_restrict₀ (hT.nullMeasurableSet.mono Measure.restrict_le_self), inter_comm]
      rw [hμ₀, hres, ← integral_indicator₀ (hT.nullMeasurableSet.mono Measure.restrict_le_self),
        skp_oface_integral]
      congr 1; funext u
      by_cases hu : skpChart F u ∈ M
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
        simp only [skpProj_chart]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
    rw [← e1, ← h1, h2, e2]
  have skp_int_values : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbQ : Q.boundary.mass < ∞) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (ξ : Eucl N → NVector (Eucl N) (m + 1)) (hT : IsRectifiableTriple univ (m + 1) M θ ξ) (hθ : ∀ x ∈ M, ∃ k : ℕ, θ x = k) (hQω : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1), Q ω = tauAction (m + 1) M θ ξ ω) (F : LatticeFaceIndex (m + 1) N), ∀ᵐ u ∂(volume.restrict {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}), ∃ k : ℤ,
        M.indicator (fun x => θ x *
          ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)))) (skpChart F u) = k := by
    clear * - skpOFace skp_oface_coord skpChart skpChart_isometry skpChart_mem_oface skp_measurableSet_cube skp_cube_finite skp_int_hyperplane skp_simple_norm_one skp_eF_orthonormal skp_nvector_single skp_int_rep skp_nvector_norm_smul
    revert skpOFace skp_oface_coord skpChart skpChart_isometry skpChart_mem_oface skp_measurableSet_cube skp_cube_finite skp_int_hyperplane skp_simple_norm_one skp_eF_orthonormal skp_nvector_single skp_int_rep skp_nvector_norm_smul
    refine id ?_
    intro skpOFace skp_oface_coord skpChart skpChart_isometry skpChart_mem_oface skp_measurableSet_cube skp_cube_finite skp_int_hyperplane skp_simple_norm_one skp_eF_orthonormal skp_nvector_single skp_int_rep skp_nvector_norm_smul N m Q hbQ M θ ξ hT hθ hQω F
    obtain ⟨hnorm, hrep₀⟩ := skp_int_rep Q M θ ξ hT hQω
    set μ₀ := (μHE[m + 1] : Measure (Eucl N)).restrict M with hμ₀
    have hdx₀ := skp_int_hyperplane Q hbQ μ₀ (fun x => θ x • ξ x) hrep₀
    have hgood : ∀ᵐ x ∂μ₀, x ∈ skpOFace F → ∃ k : ℤ, θ x *
        ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) = k := by
      filter_upwards [hdx₀, hnorm, ae_restrict_mem₀ hT.nullMeasurableSet] with x hxd hxn hxM hxF
      have hθpos := hT.pos x hxM
      have hγ : ∀ γ : SimonMultiIndex (m + 1) N, γ ≠ F.2 →
          ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0 := by
        intro γ hγ
        obtain ⟨i0, hi0⟩ := skp_oface_coord F x hxF γ hγ
        have := hxd γ ⟨i0, F.1 (γ i0), hi0⟩
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_eq_zero] at this
        rcases this with h | h
        · linarith
        · exact h
      have hξ := skp_nvector_single (ξ x) F.2 hγ
      set c := ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) with hc
      have hc1 : |c| = 1 := by
        have := congrArg norm hξ
        rw [skp_nvector_norm_smul, skp_simple_norm_one _ (skp_eF_orthonormal F), mul_one,
          hxn] at this
        exact this.symm
      obtain ⟨k, hk⟩ := hθ x hxM
      rcases abs_eq (zero_le_one) |>.1 hc1 with h | h
      · exact ⟨k, by rw [h, hk]; push_cast; ring⟩
      · exact ⟨-k, by rw [h, hk]; push_cast; ring⟩
    set Bad := {x : Eucl N | ¬ (x ∈ skpOFace F → ∃ k : ℤ, θ x *
        ξ x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) = k)} with hBad
    have hBad0 : (μHE[m + 1] : Measure (Eucl N)) (Bad ∩ M) = 0 := by
      have : μ₀ Bad = 0 := by
        rw [ae_iff] at hgood
        exact hgood
      rwa [hμ₀, Measure.restrict_apply₀' hT.nullMeasurableSet] at this
    have hpre := Submission.lpf_raf_chart_preimage_null N (m + 1) (skpChart F)
      {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1} 1 one_pos
      (fun w _ w' _ => by rw [one_mul, ← dist_eq_norm, ← dist_eq_norm, (skpChart_isometry F).dist_eq])
      (Bad ∩ M) hBad0
    rw [ae_restrict_iff' (skp_measurableSet_cube _)]
    have : ∀ᵐ u ∂(volume : Measure (Eucl (m + 1))),
        u ∉ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1} ∩ skpChart F ⁻¹' (Bad ∩ M) :=
      measure_eq_zero_iff_ae_notMem.1 hpre
    filter_upwards [this] with u hu hucube
    by_cases huM : skpChart F u ∈ M
    · rw [Set.indicator_of_mem huM]
      have hnotbad : skpChart F u ∉ Bad := fun h => hu ⟨hucube, h, huM⟩
      simp only [hBad, mem_setOf_eq, not_not] at hnotbad
      exact hnotbad ((skpChart_mem_oface F u).2 hucube)
    · rw [Set.indicator_of_notMem huM]
      exact ⟨0, by simp⟩
  -- The coefficient `b` is within `K` of an integer, for integer multiplicity `Q`.
  have skp_int_round : ∀ {N m : ℕ} (Q : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hbQ : Q.boundary.mass < ∞) (μ : Measure (Eucl N)) [IsFiniteMeasure μ] (v : Eucl N → NVector (Eucl N) (m + 1)) (hrep : IsMeasureRepresentation Q μ v) (hμS : μ Q.supportᶜ = 0) (hres : ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1),
        (∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1),
          Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) (m + 1)) x) ∂μ) ∧
        (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧
        (IsIntegerMultiplicity Q → IsIntegerMultiplicity Y)) (hQs : Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) N, latticeFace 1 F) (hdx : ∀ᵐ x ∂μ, ∀ γ : SimonMultiIndex (m + 1) N,
        (∃ i0 : Fin (m + 1), ∃ c : ℤ, x (γ i0) = (c : ℝ)) →
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (γ j))) = 0) (hint : IsIntegerMultiplicity Q) (F : LatticeFaceIndex (m + 1) N) (b K : ℝ) (hK : 0 ≤ K) (hPF : ∀ g : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
        (∀ u, |g u| ≤ B) →
        |∫ x in skpOFace F, g (skpProj F x) *
            v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
          b * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤ K * B), |b - round b| ≤ K := by
    clear * - skp_cnorm_smul skp_mass_tool skpOFace skpChart skpProj skpProj_chart skp_oface_iff skp_scalar_form_mem skp_measurableSet_cube skp_volume_cube skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_cube_integrable skp_dx_kron_self skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_face_integral_chart skp_face_integral skp_chain_exists skp_sub_current skp_massOn_le skp_form_chart_fun skp_faces_finset skp_int_rep skp_cnorm_dx_eq_one skp_oface_integral skp_oface_integrable_iff skp_v_on_oface skp_int_density skp_int_values
    revert skp_cnorm_smul skp_mass_tool skpOFace skpChart skpProj skpProj_chart skp_oface_iff skp_scalar_form_mem skp_measurableSet_cube skp_volume_cube skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_cube_integrable skp_dx_kron_self skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_face_integral_chart skp_face_integral skp_chain_exists skp_sub_current skp_massOn_le skp_form_chart_fun skp_faces_finset skp_int_rep skp_cnorm_dx_eq_one skp_oface_integral skp_oface_integrable_iff skp_v_on_oface skp_int_density skp_int_values
    refine id ?_
    intro skp_cnorm_smul skp_mass_tool skpOFace skpChart skpProj skpProj_chart skp_oface_iff skp_scalar_form_mem skp_measurableSet_cube skp_volume_cube skp_cube_finite skpH skpChi skpPsi skpPsi_contDiff skpPsi_nonneg skpPsi_le_one skpPsi_support_cube skpPsi_eventually_one skp_eps_pos skp_eps_tendsto skp_lam_tendsto skp_cube_integrable skp_dx_kron_self skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_rep_integrableOn_bdd skp_face_integral_chart skp_face_integral skp_chain_exists skp_sub_current skp_massOn_le skp_form_chart_fun skp_faces_finset skp_int_rep skp_cnorm_dx_eq_one skp_oface_integral skp_oface_integrable_iff skp_v_on_oface skp_int_density skp_int_values N m Q hbQ μ _ v hrep hμS hres hQs hL hdx hint F b K hK hPF
    classical
    obtain ⟨M, θ, ξ, hT, hθ, hQω⟩ := hint
    set cube := {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1} with hcube
    set dxF := wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)) with hdxF
    set eF : Fin (m + 1) → Eucl N := fun j => EuclideanSpace.single (F.2 j) (1 : ℝ) with heF
    set h : Eucl (m + 1) → ℝ := fun u => M.indicator (fun x => θ x * ξ x dxF) (skpChart F u)
      with hh
    obtain ⟨hnorm, hrep₀⟩ := skp_int_rep Q M θ ξ hT hQω
    -- integrability of `h` on the cube
    have hhint : IntegrableOn h cube := by
      have h1 : IntegrableOn (fun x => (θ x • ξ x) dxF) (skpOFace F)
          ((μHE[m + 1] : Measure (Eucl N)).restrict M) :=
        skp_rep_integrableOn_bdd Q _ _ hrep₀ dxF _ (skp_oface_bounded F)
      have h2 : IntegrableOn (M.indicator fun x => θ x * ξ x dxF) (skpOFace F)
          (μHE[m + 1] : Measure (Eucl N)) := by
        set M' := toMeasurable (μHE[m + 1] : Measure (Eucl N)) M with hM'
        have hMM' : M' =ᵐ[(μHE[m + 1] : Measure (Eucl N))] M :=
          NullMeasurableSet.toMeasurable_ae_eq hT.nullMeasurableSet
        have hM'm : MeasurableSet M' := measurableSet_toMeasurable _ _
        have h1' : IntegrableOn (fun x => θ x * ξ x dxF) (skpOFace F)
            ((μHE[m + 1] : Measure (Eucl N)).restrict M') := by
          rw [Measure.restrict_congr_set hMM']
          refine h1.congr_fun (fun x _ => ?_) (skp_measurableSet_oface F)
          simp
        have h3 : IntegrableOn (M'.indicator fun x => θ x * ξ x dxF) (skpOFace F)
            (μHE[m + 1] : Measure (Eucl N)) := by
          rw [IntegrableOn, integrable_indicator_iff hM'm, IntegrableOn,
            Measure.restrict_restrict hM'm, inter_comm, ← Measure.restrict_restrict
            (skp_measurableSet_oface F)]
          exact h1'
        refine h3.congr_fun_ae ?_
        exact (ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set hMM'))
      exact (skp_oface_integrable_iff F _).1 h2
    -- the density identity for all smooth compactly supported `g`
    have hdens0 := skp_int_density Q hbQ M θ ξ hT hQω μ v hrep hμS hQs hL hdx F
    have hdens : ∀ g : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        ∫ x in skpOFace F, g (skpProj F x) * v x dxF ∂μ = ∫ u in cube, g u * h u := by
      intro g hg hgc
      obtain ⟨B, hB⟩ := hgc.exists_bound_of_continuous hg.continuous
      set G : ℕ → Eucl (m + 1) → ℝ := fun i u => g u * skpPsi (1 / ((i : ℝ) + 2)) u with hG
      have hGi : ∀ i, ∫ x in skpOFace F, G i (skpProj F x) * v x dxF ∂μ = ∫ u in cube, G i u * h u :=
        fun i => hdens0 (G i) (hg.mul (skpPsi_contDiff _))
          ((tsupport_mul_subset_right).trans (skpPsi_support_cube (skp_eps_pos i)))
      have hw : Integrable (fun x => v x dxF) (μ.restrict (skpOFace F)) :=
        skp_rep_integrableOn_bdd Q μ v hrep dxF _ (skp_oface_bounded F)
      have hπc : ∀ᵐ x ∂(μ.restrict (skpOFace F)), skpProj F x ∈ cube := by
        rw [ae_restrict_iff' (skp_measurableSet_oface F)]
        exact Eventually.of_forall fun x hx => ((skp_oface_iff F x).1 hx).2
      have hGb : ∀ i u, |G i u| ≤ B := by
        intro i u
        simp only [hG]
        rw [abs_mul, abs_of_nonneg (skpPsi_nonneg _ _)]
        have := hB u
        rw [Real.norm_eq_abs] at this
        calc |g u| * skpPsi _ u ≤ B * 1 :=
              mul_le_mul this (skpPsi_le_one _ _) (skpPsi_nonneg _ _) ((abs_nonneg _).trans this)
          _ = B := mul_one B
      have hlimψ : ∀ u ∈ cube, Tendsto (fun i => G i u) atTop (𝓝 (g u)) := by
        intro u hu
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [skpPsi_eventually_one _ skp_eps_pos skp_eps_tendsto u hu] with i hi
        simp only [hG]
        rw [hi, mul_one]
      have l1 := (skp_lam_tendsto (μ.restrict (skpOFace F)) (skpProj F) (skpProj_measurable F) hπc
        (fun x => v x dxF) hw G g (fun i => hg.continuous.mul (skpPsi_contDiff _).continuous) B
        (fun i u _ => hGb i u) hlimψ).1
      have l2 : Tendsto (fun i => ∫ u in cube, G i u * h u) atTop (𝓝 (∫ u in cube, g u * h u)) := by
        refine tendsto_integral_of_dominated_convergence (fun u => B * |h u|) (fun i => ?_)
          (hhint.abs.const_mul B) (fun i => ?_) ?_
        · exact (hg.continuous.mul (skpPsi_contDiff _).continuous).aestronglyMeasurable.mul
            hhint.aestronglyMeasurable
        · refine Eventually.of_forall fun u => ?_
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right (hGb i u) (abs_nonneg _)
        · rw [ae_restrict_iff' (skp_measurableSet_cube _)]
          exact Eventually.of_forall fun u hu => (hlimψ u hu).mul_const _
      exact tendsto_nhds_unique (l1.congr fun i => hGi i) l2
    -- integer values
    have hZ := skp_int_values Q hbQ M θ ξ hT hθ hQω F
    -- the current `X = Q ⌞ F̊ - b [[F]]`
    obtain ⟨Y, hYω, hYm, -⟩ := hres (skpOFace F) (skp_measurableSet_oface F)
    obtain ⟨Fch, -, hFch⟩ := skp_chain_exists (N := N) (m := m)
      (fun G : LatticeFaceIndex (m + 1) N => if G = F then b else 0)
    obtain ⟨X, hX⟩ := skp_sub_current Y Fch
    have hvF := skp_v_on_oface μ v hdx F
    have hXω : ∀ ω : TestFormOn (univ : Set (Eucl N)) (m + 1),
        X ω = ∫ u in cube, (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF * (h u - b) := by
      intro ω
      rw [hX, hYω]
      obtain ⟨T, hT'⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
      rw [hFch ω (insert F T) (fun G hG => Finset.mem_insert_of_mem (hT' G hG)),
        Finset.sum_eq_single F (fun G _ hG => by rw [if_neg hG, zero_mul]) (by simp), if_pos rfl]
      have e1 : ∫ x in skpOFace F, v x ((ω : DifferentialForm (Eucl N) (m + 1)) x) ∂μ =
          ∫ x in skpOFace F, (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF)
            (skpProj F x) * v x dxF ∂μ := by
        rw [← skp_face_integral_chart]
        refine setIntegral_congr_ae (skp_measurableSet_oface F) ?_
        filter_upwards [hvF] with x hx hxF
        exact hx hxF _
      obtain ⟨hgs, hgc, hgb⟩ := skp_form_chart_fun F ω
      rw [e1, hdens _ hgs hgc]
      unfold latticeFaceAction
      rw [skp_face_integral]
      have i1 : IntegrableOn (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF * h u) cube := by
        obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
        exact Integrable.bdd_mul (c := C) hhint hgs.continuous.aestronglyMeasurable
          (Eventually.of_forall fun u => hC u)
      have i2 : IntegrableOn (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF) cube := by
        obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
        exact skp_cube_integrable _ hgs.continuous C fun u _ => by simpa [Real.norm_eq_abs] using hC u
      simp_rw [mul_sub]
      rw [integral_sub i1 (i2.mul_const b), integral_mul_const]
      ring
    -- `M(X) ≤ K`
    have hXmass : X.mass ≤ ENNReal.ofReal K := by
      apply skp_massOn_le
      intro ω hω
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨hgs, hgc, hgb⟩ := skp_form_chart_fun F ω
      have hXω' : X ω = ∫ x in skpOFace F, (fun u => (ω : DifferentialForm (Eucl N) (m + 1))
          (skpChart F u) eF) (skpProj F x) * v x dxF ∂μ -
            b * ∫ u in cube, (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF := by
        rw [hXω, hdens _ hgs hgc]
        have i1 : IntegrableOn (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF * h u) cube := by
          obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
          exact Integrable.bdd_mul (c := C) hhint hgs.continuous.aestronglyMeasurable
            (Eventually.of_forall fun u => hC u)
        have i2 : IntegrableOn (fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF) cube := by
          obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
          exact skp_cube_integrable _ hgs.continuous C fun u _ => by simpa [Real.norm_eq_abs] using hC u
        simp_rw [mul_sub]
        rw [integral_sub i1 (i2.mul_const b), integral_mul_const]
        ring
      rw [hXω']
      exact (le_abs_self _).trans ((hPF _ hgs hgc 1 zero_le_one fun u => (hgb u).trans (hω.2 _)).trans
        (by rw [mul_one]))
    have hXfin : X.mass < ∞ := lt_of_le_of_lt hXmass ENNReal.ofReal_lt_top
    obtain ⟨μX, vX, hμXfin, hrepX, -, hμX, huniqX, hresX⟩ := skp_mass_tool X hXfin
    -- a measurable version of `h`
    set h' := hhint.aestronglyMeasurable.mk h with hh'
    have hh'm : Measurable h' := hhint.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hhh' : h =ᵐ[volume.restrict cube] h' := hhint.aestronglyMeasurable.ae_eq_mk
    have hh'int : IntegrableOn h' cube := hhint.congr hhh'
    -- another representation of `X`
    set μ₁ := (μHE[m + 1] : Measure (Eucl N)).restrict (skpOFace F) with hμ₁
    set v₁ : Eucl N → NVector (Eucl N) (m + 1) := fun x => (h' (skpProj F x) - b) • simpleNVector eF
      with hv₁
    have hv₁apply : ∀ x (a : Covector (Eucl N) (m + 1)), v₁ x a = (h' (skpProj F x) - b) * a eF := by
      intro x a; simp [hv₁]
    have hrep₁ : IsMeasureRepresentation X μ₁ v₁ := by
      intro ω
      obtain ⟨hgs, hgc, hgb⟩ := skp_form_chart_fun F ω
      obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgs.continuous
      have hcube_int : IntegrableOn (fun u => (h' u - b) *
          (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF) cube := by
        have := Integrable.bdd_mul (c := C)
          (f := fun u => (ω : DifferentialForm (Eucl N) (m + 1)) (skpChart F u) eF)
          (g := fun u => h' u - b) (μ := volume.restrict cube)
          (hh'int.sub (integrableOn_const (by rw [skp_volume_cube]; exact ENNReal.one_ne_top)))
          hgs.continuous.aestronglyMeasurable (Eventually.of_forall fun u => hC u)
        refine this.congr (Eventually.of_forall fun u => ?_)
        simp only
        ring
      refine ⟨?_, ?_⟩
      · simp_rw [hv₁apply]
        rw [← IntegrableOn, skp_oface_integrable_iff]
        simpa [skpProj_chart] using hcube_int
      · simp_rw [hv₁apply]
        rw [hμ₁, skp_oface_integral, hXω]
        simp only [skpProj_chart]
        refine setIntegral_congr_ae (skp_measurableSet_cube _) ?_
        filter_upwards [(ae_restrict_iff' (skp_measurableSet_cube _)).1 hhh'] with u hu hucube
        rw [hu hucube]; ring
    -- `|∫_A vX(dx_F) dμX| ≤ μX A`
    have hbound : ∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A →
        |∫ x in A, vX x dxF ∂μX| ≤ (μX A).toReal := by
      intro A hA hAb
      obtain ⟨Y', hY'ω, hY'm, -⟩ := hresX A hA
      obtain ⟨R, hR⟩ := hAb.subset_closedBall 0
      obtain ⟨φ, hφs, hφc, hφ1, hφ0, hφle⟩ : ∃ φ : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧
          (∀ x ∈ closedBall (0 : Eucl N) R, φ x = 1) ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) := by
        let bump : ContDiffBump (0 : Eucl N) := ⟨max R 1, max R 1 + 1, by positivity, by linarith⟩
        exact ⟨bump, bump.contDiff, bump.hasCompactSupport,
          fun x hx => bump.one_of_mem_closedBall (closedBall_subset_closedBall (le_max_left _ _) hx),
          fun x => bump.nonneg, fun x => bump.le_one⟩
      have hmem := skp_scalar_form_mem φ hφs hφc dxF
      set ωA : TestFormOn (univ : Set (Eucl N)) (m + 1) := ⟨_, hmem⟩
      have hval : Y' ωA = ∫ x in A, vX x dxF ∂μX := by
        rw [hY'ω]
        refine setIntegral_congr_fun hA fun x hx => ?_
        change vX x (φ x • dxF) = _
        rw [map_smul, hφ1 x (hR hx), one_smul]
      have hadm : ∀ s : ℝ, |s| ≤ 1 → ENNReal.ofReal (Y' (s • ωA)) ≤ μX A := by
        intro s hs
        calc ENNReal.ofReal (Y' (s • ωA)) ≤ Y'.massOn univ := by
              apply GeometricCurrentOn.le_massOn
              refine ⟨subset_univ _, fun x => ?_⟩
              change covectorEuclideanNorm (s • (φ x • dxF)) ≤ 1
              rw [skp_cnorm_smul, skp_cnorm_smul, skp_cnorm_dx_eq_one, mul_one,
                abs_of_nonneg (hφ0 x)]
              calc |s| * φ x ≤ 1 * 1 := mul_le_mul hs (hφle x) (hφ0 x) zero_le_one
                _ = 1 := one_mul 1
          _ = μX A := by rw [hY'm univ isOpen_univ, univ_inter]
      have h1 := hadm 1 (by simp)
      have h2 := hadm (-1) (by simp)
      rw [map_smul, one_smul] at h1
      rw [map_smul, neg_one_smul] at h2
      rw [← hval, abs_le]
      have hfin : μX A ≠ ∞ := measure_ne_top _ _
      constructor
      · have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 h2
        linarith
      · exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
    -- the `L¹` bound on the face
    set Ap := skpOFace F ∩ skpProj F ⁻¹' {u | b < h' u} with hAp
    set An := skpOFace F ∩ skpProj F ⁻¹' {u | h' u < b} with hAn
    have hApm : MeasurableSet Ap := (skp_measurableSet_oface F).inter
      (measurableSet_lt measurable_const hh'm |>.preimage (skpProj_measurable F))
    have hAnm : MeasurableSet An := (skp_measurableSet_oface F).inter
      (measurableSet_lt hh'm measurable_const |>.preimage (skpProj_measurable F))
    have hcomp : ∀ A : Set (Eucl N), MeasurableSet A → A ⊆ skpOFace F →
        ∫ x in A, (h' (skpProj F x) - b) ∂(μHE[m + 1] : Measure (Eucl N)) =
          ∫ x in A, vX x dxF ∂μX := by
      intro A hA hAF
      have := huniqX μ₁ v₁ hrep₁ A hA ((skp_oface_bounded F).subset hAF) dxF
      rw [← this, hμ₁, Measure.restrict_restrict hA, inter_eq_left.2 hAF]
      refine setIntegral_congr_fun hA fun x _ => ?_
      rw [hv₁apply, hdxF, skp_dx_kron_self, mul_one]
    have hP1 := hbound Ap hApm ((skp_oface_bounded F).subset inter_subset_left)
    have hN1 := hbound An hAnm ((skp_oface_bounded F).subset inter_subset_left)
    rw [← hcomp Ap hApm inter_subset_left] at hP1
    rw [← hcomp An hAnm inter_subset_left] at hN1
    have hdisj : Disjoint Ap An := by
      rw [Set.disjoint_left]
      rintro x ⟨_, hx1⟩ ⟨_, hx2⟩
      simp only [mem_preimage, mem_setOf_eq] at hx1 hx2
      linarith
    have hμXsum : (μX Ap).toReal + (μX An).toReal ≤ K := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← measure_union hdisj hAnm]
      calc (μX (Ap ∪ An)).toReal ≤ (μX univ).toReal :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
        _ ≤ K := by
            rw [← hμX univ isOpen_univ]
            exact ENNReal.toReal_le_of_le_ofReal hK hXmass
    -- integrability of `h' ∘ π - b` on the face
    have hfint : IntegrableOn (fun x => h' (skpProj F x) - b) (skpOFace F)
        (μHE[m + 1] : Measure (Eucl N)) := by
      rw [skp_oface_integrable_iff]
      simp only [skpProj_chart]
      exact hh'int.sub (integrableOn_const (by rw [skp_volume_cube]; exact ENNReal.one_ne_top))
    have hL1 : ∫ x in skpOFace F, |h' (skpProj F x) - b| ∂(μHE[m + 1] : Measure (Eucl N)) ≤ K := by
      have hsplit : ∫ x in skpOFace F, |h' (skpProj F x) - b| ∂(μHE[m + 1] : Measure (Eucl N)) =
          ∫ x in Ap, (h' (skpProj F x) - b) ∂(μHE[m + 1] : Measure (Eucl N)) -
            ∫ x in An, (h' (skpProj F x) - b) ∂(μHE[m + 1] : Measure (Eucl N)) := by
        have hpt : ∀ x ∈ skpOFace F, |h' (skpProj F x) - b| =
            Ap.indicator (fun x => h' (skpProj F x) - b) x -
              An.indicator (fun x => h' (skpProj F x) - b) x := by
          intro x hx
          rcases lt_trichotomy b (h' (skpProj F x)) with hlt | heq | hgt
          · have hxA : x ∈ Ap := ⟨hx, hlt⟩
            have hxN : x ∉ An := fun h => by
              have := h.2; simp only [mem_preimage, mem_setOf_eq] at this; linarith
            rw [Set.indicator_of_mem hxA, Set.indicator_of_notMem hxN, abs_of_pos (by linarith)]
            ring
          · have hxA : x ∉ Ap := fun h => by
              have := h.2; simp only [mem_preimage, mem_setOf_eq] at this; linarith
            have hxN : x ∉ An := fun h => by
              have := h.2; simp only [mem_preimage, mem_setOf_eq] at this; linarith
            rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxN, ← heq]
            simp
          · have hxA : x ∉ Ap := fun h => by
              have := h.2; simp only [mem_preimage, mem_setOf_eq] at this; linarith
            have hxN : x ∈ An := ⟨hx, hgt⟩
            rw [Set.indicator_of_notMem hxA, Set.indicator_of_mem hxN, abs_of_neg (by linarith)]
            ring
        rw [setIntegral_congr_fun (skp_measurableSet_oface F) hpt,
          integral_sub (hfint.indicator hApm) (hfint.indicator hAnm),
          setIntegral_indicator hApm, setIntegral_indicator hAnm,
          inter_eq_right.2 (inter_subset_left : Ap ⊆ skpOFace F),
          inter_eq_right.2 (inter_subset_left : An ⊆ skpOFace F)]
      rw [hsplit]
      have a1 := (le_abs_self _).trans hP1
      have a2 := (neg_le_abs _).trans hN1
      linarith
    -- conclusion
    have hcubeL1 : ∫ u in cube, |h u - b| ≤ K := by
      rw [skp_oface_integral] at hL1
      simp only [skpProj_chart] at hL1
      calc ∫ u in cube, |h u - b| = ∫ u in cube, |h' u - b| := by
            refine setIntegral_congr_ae (skp_measurableSet_cube _) ?_
            filter_upwards [(ae_restrict_iff' (skp_measurableSet_cube _)).1 hhh'] with u hu hucube
            rw [hu hucube]
        _ ≤ K := hL1
    have hround : ∫ u in cube, |b - round b| ≤ ∫ u in cube, |h u - b| := by
      refine setIntegral_mono_ae_restrict ?_ ?_ ?_
      · exact integrableOn_const (by rw [skp_volume_cube]; exact ENNReal.one_ne_top)
      · exact (hhint.sub (integrableOn_const (by rw [skp_volume_cube]; exact ENNReal.one_ne_top))).abs
      · filter_upwards [hZ] with u ⟨k, hk⟩
        have hk' : h u = k := hk
        rw [hk']
        calc |b - round b| ≤ |b - k| := round_le b k
          _ = |(k : ℝ) - b| := abs_sub_comm _ _
    rw [setIntegral_const, Measure.real, skp_volume_cube, ENNReal.toReal_one, one_smul] at hround
    linarith
  -- Vectors with vanishing normal coordinates form the span of the tangential basis.
  have skp_mem_span_eF : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (v : Eucl N), v ∈ Submodule.span ℝ (range fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) ↔
        ∀ l, l ∉ range F.2 → v l = 0 := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite n N F v
    classical
    constructor
    · intro hv
      refine Submodule.span_induction (p := fun v _ => ∀ l, l ∉ range F.2 → v l = 0) ?_ ?_ ?_ ?_ hv
      · rintro _ ⟨j, rfl⟩ l hl
        rw [EuclideanSpace.single_apply]
        have : l ≠ F.2 j := fun h => hl ⟨j, h.symm⟩
        simp [this]
      · intro l _; simp
      · intro a b _ _ ha hb l hl; simp [ha l hl, hb l hl]
      · intro c a _ ha l hl; simp [ha l hl]
    · intro hv
      have : v = ∑ j, v (F.2 j) • EuclideanSpace.single (F.2 j) (1 : ℝ) := by
        ext l
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        simp only [PiLp.smul_apply, EuclideanSpace.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        by_cases hl : l ∈ range F.2
        · obtain ⟨j, rfl⟩ := hl
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hi; simp [F.2.injective.eq_iff, hi, Ne.symm hi]
          · simp
        · rw [hv l hl]
          symm
          refine Finset.sum_eq_zero fun j _ => ?_
          have : l ≠ F.2 j := fun h => hl ⟨j, h.symm⟩
          simp [this]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- The affine plane through a face, with constant weight, has the face directions as weighted approximate tangent space.
  have skp_plane_tangent : ∀ {n N : ℕ} (F : LatticeFaceIndex n N) (x : Eucl N) (hx : ∀ l, l ∉ range F.2 → x l = F.1 l) (c : ℝ), HasWeightedApproximateTangentSpaceAt n {y : Eucl N | ∀ l, l ∉ range F.2 → y l = F.1 l}
        (fun _ => c) x (Submodule.span ℝ (range fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))) := by
    clear * - skp_cube_finite skp_eF_orthonormal skp_mem_span_eF
    revert skp_cube_finite skp_eF_orthonormal skp_mem_span_eF
    refine id ?_
    intro skp_cube_finite skp_eF_orthonormal skp_mem_span_eF n N F x hx c
    classical
    refine ⟨?_, fun f => ?_⟩
    · rw [finrank_span_eq_card (skp_eF_orthonormal F).linearIndependent]
      simp
    · have himage : ∀ r : ℝ, r ≠ 0 → Poincare.SimonGMT.Chapter03.blowUpMap x r ''
          {y : Eucl N | ∀ l, l ∉ range F.2 → y l = F.1 l} =
          (Submodule.span ℝ (range fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) : Set (Eucl N)) := by
        intro r hr
        ext v
        simp only [mem_image, mem_setOf_eq, SetLike.mem_coe, skp_mem_span_eF]
        constructor
        · rintro ⟨y, hy, rfl⟩ l hl
          simp only [Poincare.SimonGMT.Chapter03.blowUpMap, PiLp.smul_apply, PiLp.sub_apply,
            smul_eq_mul]
          rw [hy l hl, hx l hl, sub_self, mul_zero]
        · intro hv
          refine ⟨x + r • v, fun l hl => ?_, ?_⟩
          · simp [hv l hl, hx l hl]
          · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, smul_smul,
              inv_mul_cancel₀ hr, one_smul]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      rw [himage r hr.ne', integral_mul_const, mul_comm]
  -- Lattice chains with integer coefficients are integer multiplicity currents.
  have skp_chain_int : ∀ {N m : ℕ} (hNm : m + 1 ≤ N) (β : LatticeFaceIndex (m + 1) N → ℝ) (hβ : ∀ F, ∃ k : ℤ, β F = k) (P : GeometricCurrentOn (univ : Set (Eucl N)) (m + 1)) (hP : ∀ (ω : TestFormOn (univ : Set (Eucl N)) (m + 1)) (S : Finset (LatticeFaceIndex (m + 1) N)),
        (∀ F, (latticeFace 1 F ∩ tsupport (ω : DifferentialForm (Eucl N) (m + 1))).Nonempty → F ∈ S) →
        P ω = ∑ F ∈ S, β F * latticeFaceAction 1 F (ω : DifferentialForm (Eucl N) (m + 1))), IsIntegerMultiplicity P := by
    clear * - skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_coord_continuous skp_oface_subset_face skp_oface_subset_nbhd skp_nbhd_face skp_oface_face skp_oface_disjoint skp_isOpen_nbhd skpChart skpProj skpChart_proj skpChart_isometry skp_oface_iff skp_cube_finite skp_isCompact_face skp_measurableSet_oface skp_eval_continuous skp_face_integral skp_faces_finset skp_eF_orthonormal skp_oface_integral skp_plane_tangent
    revert skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_coord_continuous skp_oface_subset_face skp_oface_subset_nbhd skp_nbhd_face skp_oface_face skp_oface_disjoint skp_isOpen_nbhd skpChart skpProj skpChart_proj skpChart_isometry skp_oface_iff skp_cube_finite skp_isCompact_face skp_measurableSet_oface skp_eval_continuous skp_face_integral skp_faces_finset skp_eF_orthonormal skp_oface_integral skp_plane_tangent
    refine id ?_
    intro skp_mem_face skpOFace skpOFace_mem skpNbhd skpNbhd_mem skp_coord_continuous skp_oface_subset_face skp_oface_subset_nbhd skp_nbhd_face skp_oface_face skp_oface_disjoint skp_isOpen_nbhd skpChart skpProj skpChart_proj skpChart_isometry skp_oface_iff skp_cube_finite skp_isCompact_face skp_measurableSet_oface skp_eval_continuous skp_face_integral skp_faces_finset skp_eF_orthonormal skp_oface_integral skp_plane_tangent N m hNm β hβ P hP
    classical
    set eF : LatticeFaceIndex (m + 1) N → Fin (m + 1) → Eucl N :=
      fun F j => EuclideanSpace.single (F.2 j) (1 : ℝ) with heF
    set A : LatticeFaceIndex (m + 1) N → Set (Eucl N) := fun F =>
      if β F ≠ 0 then skpOFace F else ∅ with hA
    have hAm : ∀ F, MeasurableSet (A F) := fun F => by
      simp only [hA]; split_ifs
      · exact skp_measurableSet_oface F
      · exact MeasurableSet.empty
    have hAsub : ∀ F, A F ⊆ skpOFace F := fun F => by
      simp only [hA]; split_ifs
      · exact subset_rfl
      · exact empty_subset _
    set Mp := ⋃ F, A F with hMp
    have hMpm : MeasurableSet Mp := MeasurableSet.iUnion hAm
    set θp : Eucl N → ℝ := fun x => ∑' F, (skpOFace F).indicator (fun _ => |β F|) x with hθp
    obtain ⟨α₀⟩ : Nonempty (SimonMultiIndex (m + 1) N) := ⟨Fin.castLEOrderEmb hNm⟩
    set dir : Eucl N → SignType × SimonMultiIndex (m + 1) N := fun x =>
      if h : ∃ F : LatticeFaceIndex (m + 1) N, x ∈ skpOFace F then
        (SignType.sign (β h.choose), h.choose.2) else (0, α₀) with hdir
    set Ψ : SignType × SimonMultiIndex (m + 1) N → NVector (Eucl N) (m + 1) := fun p =>
      ((p.1 : ℝ)) • simpleNVector (fun j => EuclideanSpace.single (p.2 j) (1 : ℝ)) with hΨ
    set ξp : Eucl N → NVector (Eucl N) (m + 1) := fun x => Ψ (dir x) with hξp
    have hθF : ∀ F x, x ∈ skpOFace F → θp x = |β F| := by
      intro F x hx
      simp only [hθp]
      rw [tsum_eq_single F (fun G hG => Set.indicator_of_notMem (fun hxG =>
        hG (skp_oface_face F G x hx (skp_oface_subset_face G hxG))) _),
        Set.indicator_of_mem hx]
    have hdirF : ∀ F x, x ∈ skpOFace F → dir x = (SignType.sign (β F), F.2) := by
      intro F x hx
      have h : ∃ F' : LatticeFaceIndex (m + 1) N, x ∈ skpOFace F' := ⟨F, hx⟩
      have hch : h.choose = F :=
        skp_oface_face F h.choose x hx (skp_oface_subset_face _ h.choose_spec)
      simp only [hdir, dif_pos h, hch]
    have hξF : ∀ F x, x ∈ skpOFace F → ξp x = (SignType.sign (β F) : ℝ) • simpleNVector (eF F) := by
      intro F x hx
      simp only [hξp, hdirF F x hx, hΨ]
      rfl
    have hmemMp : ∀ x, x ∈ Mp ↔ ∃ F, β F ≠ 0 ∧ x ∈ skpOFace F := by
      intro x
      simp only [hMp, mem_iUnion, hA]
      constructor
      · rintro ⟨F, hF⟩
        split_ifs at hF with h
        · exact ⟨F, h, hF⟩
        · exact absurd hF (Set.notMem_empty x)
      · rintro ⟨F, h, hF⟩
        exact ⟨F, by rw [if_pos h]; exact hF⟩
    -- the face measure
    have hface1 : ∀ F : LatticeFaceIndex (m + 1) N,
        (μHE[m + 1] : Measure (Eucl N)) (latticeFace 1 F) = 1 := by
      intro F
      have h := Submission.isoperimetric_coord_box_measure (m + 1) N F.2 (fun i => (F.1 i : ℝ)) 0 1
        zero_le_one
      have hset : latticeFace 1 F = {x : Eucl N | ∀ i : Fin N,
          (i ∈ range F.2 → (F.1 i : ℝ) + 0 ≤ x i ∧ x i ≤ (F.1 i : ℝ) + 1) ∧
            (i ∉ range F.2 → x i = F.1 i)} := by
        ext x; rw [skp_mem_face]; simp
      rw [hset, h]
      simp
    refine ⟨Mp, θp, ξp, ⟨subset_univ _, hMpm.nullMeasurableSet, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · -- countably rectifiable
      have hne : Nonempty (LatticeFaceIndex (m + 1) N) :=
        ⟨(fun _ => 0, Fin.castLEOrderEmb hNm)⟩
      obtain ⟨enum, henum⟩ := exists_surjective_nat (LatticeFaceIndex (m + 1) N)
      refine ⟨∅, measure_empty, fun j => skpChart (enum j),
        fun j => ⟨1, (skpChart_isometry (enum j)).lipschitz⟩, ?_⟩
      intro x hx
      obtain ⟨F, _, hxF⟩ := (hmemMp x).1 hx
      obtain ⟨j, rfl⟩ := henum F
      right
      exact mem_iUnion.2 ⟨j, skpProj (enum j) x, skpChart_proj _ x ((skp_oface_iff _ x).1 hxF).1⟩
    · -- positivity
      intro x hx
      obtain ⟨F, hβF, hxF⟩ := (hmemMp x).1 hx
      rw [hθF F x hxF]
      exact abs_pos.2 hβF
    · -- local integrability
      intro K hK _
      obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) K hK
      have hfin : (μHE[m + 1] : Measure (Eucl N)) (Mp ∩ K) < ∞ := by
        calc (μHE[m + 1] : Measure (Eucl N)) (Mp ∩ K) ≤
              (μHE[m + 1] : Measure (Eucl N)) (⋃ F ∈ T, latticeFace 1 F) := by
              apply measure_mono
              rintro x ⟨hxM, hxK⟩
              obtain ⟨F, _, hxF⟩ := (hmemMp x).1 hxM
              exact mem_biUnion (hT F ⟨x, skp_oface_subset_face F hxF, hxK⟩)
                (skp_oface_subset_face F hxF)
          _ ≤ ∑ F ∈ T, (μHE[m + 1] : Measure (Eucl N)) (latticeFace 1 F) := measure_biUnion_finset_le _ _
          _ < ∞ := by simp [hface1]
      set g : Eucl N → ℝ := fun x => ∑ F ∈ T, (skpOFace F).indicator (fun _ => |β F|) x with hg
      have hgm : Measurable g := Finset.measurable_sum _ fun F _ =>
        measurable_const.indicator (skp_measurableSet_oface F)
      obtain ⟨C, hC⟩ : ∃ C, ∀ x, |g x| ≤ C := ⟨∑ F ∈ T, |β F|, fun x => by
        simp only [hg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F _ => ?_)
        by_cases hx : x ∈ skpOFace F
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]⟩
      have hgint : IntegrableOn g (Mp ∩ K) (μHE[m + 1] : Measure (Eucl N)) :=
        Measure.integrableOn_of_bounded (M := C) hfin.ne hgm.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
      refine hgint.congr_fun (fun x hx => ?_) (hMpm.inter hK.isClosed.measurableSet)
      obtain ⟨F, _, hxF⟩ := (hmemMp x).1 hx.1
      rw [hθF F x hxF]
      simp only [hg]
      rw [Finset.sum_eq_single F]
      · rw [Set.indicator_of_mem hxF]
      · intro G _ hG
        exact Set.indicator_of_notMem (fun hxG => hG (skp_oface_face F G x hxF
          (skp_oface_subset_face G hxG))) _
      · intro hFT
        exact absurd (hT F ⟨x, skp_oface_subset_face F hxF, hx.2⟩) hFT
    · -- measurability of the orientation
      have hfib : ∀ p, MeasurableSet (dir ⁻¹' {p}) := by
        intro p
        have hU : MeasurableSet (⋃ F : LatticeFaceIndex (m + 1) N, skpOFace F) :=
          MeasurableSet.iUnion fun F => skp_measurableSet_oface F
        have : dir ⁻¹' {p} = (⋃ F ∈ {F : LatticeFaceIndex (m + 1) N |
            (SignType.sign (β F), F.2) = p}, skpOFace F) ∪
            (if p = (0, α₀) then (⋃ F : LatticeFaceIndex (m + 1) N, skpOFace F)ᶜ else ∅) := by
          ext x
          simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion₂, mem_setOf_eq]
          by_cases h : ∃ F : LatticeFaceIndex (m + 1) N, x ∈ skpOFace F
          · obtain ⟨F, hF⟩ := h
            rw [hdirF F x hF]
            have hnot : x ∉ (⋃ F : LatticeFaceIndex (m + 1) N, skpOFace F)ᶜ :=
              fun h' => h' (mem_iUnion.2 ⟨F, hF⟩)
            constructor
            · intro hp; exact Or.inl ⟨F, hp, hF⟩
            · rintro (⟨G, hG, hxG⟩ | hc)
              · have := skp_oface_face F G x hF (skp_oface_subset_face G hxG)
                rw [← this]; exact hG
              · split_ifs at hc
                · exact absurd hc hnot
                · exact absurd hc (Set.notMem_empty x)
          · have hd : dir x = (0, α₀) := by simp only [hdir, dif_neg h]
            rw [hd]
            have hxU : x ∈ (⋃ F : LatticeFaceIndex (m + 1) N, skpOFace F)ᶜ := by
              simp only [mem_compl_iff, mem_iUnion, not_exists]
              exact fun F hF => h ⟨F, hF⟩
            constructor
            · intro hp
              right
              rw [if_pos hp.symm]
              exact hxU
            · rintro (⟨G, _, hxG⟩ | hc)
              · exact absurd ⟨G, hxG⟩ h
              · split_ifs at hc with hp
                · exact hp.symm
                · exact absurd hc (Set.notMem_empty x)
        rw [this]
        refine MeasurableSet.union (MeasurableSet.biUnion (Set.to_countable _)
          fun F _ => skp_measurableSet_oface F) ?_
        split_ifs
        · exact hU.compl
        · exact MeasurableSet.empty
      let sf : MeasureTheory.SimpleFunc (Eucl N) (NVector (Eucl N) (m + 1)) :=
        { toFun := ξp
          measurableSet_fiber' := fun y => by
            have : ξp ⁻¹' {y} = ⋃ p ∈ {p | Ψ p = y}, dir ⁻¹' {p} := by
              ext x; simp [hξp]
            rw [this]
            exact MeasurableSet.biUnion (Set.to_countable _) fun p _ => hfib p
          finite_range' := (Set.finite_range Ψ).subset (by
            rintro _ ⟨x, rfl⟩; exact ⟨dir x, rfl⟩) }
      exact sf.stronglyMeasurable.aestronglyMeasurable
    · -- orientation by the face frame
      refine ae_restrict_of_forall_mem hMpm fun x hx => ?_
      obtain ⟨F, hβF, hxF⟩ := (hmemMp x).1 hx
      refine ⟨eF F, skp_eF_orthonormal F, ?_, ?_⟩
      · -- the weighted approximate tangent space
        have hplane := skp_plane_tangent F x ((skp_oface_iff F x).1 hxF).1 |β F|
        refine Submission.br_weightedTangent_congr N (m + 1) _ Mp (fun _ => |β F|) θp x (skpNbhd F)
          (skp_isOpen_nbhd F) (skp_oface_subset_nbhd F hxF) ?_ ?_ (hθF F x hxF).symm _ hplane
        · have hempty : symmDiff {y : Eucl N | ∀ l, l ∉ range F.2 → y l = F.1 l} Mp ∩ skpNbhd F = ∅ := by
            ext y
            simp only [mem_inter_iff, mem_symmDiff, mem_setOf_eq, mem_empty_iff_false, iff_false,
              not_and]
            intro hsd hyV
            rcases hsd with ⟨hyP, hyM⟩ | ⟨hyM, hyP⟩
            · apply hyM
              refine (hmemMp y).2 ⟨F, hβF, ?_⟩
              rw [skpOFace_mem]
              intro l
              refine ⟨fun hl => ((skpNbhd_mem F y).1 hyV l).1 hl, hyP l⟩
            · apply hyP
              obtain ⟨G, _, hyG⟩ := (hmemMp y).1 hyM
              have hGF := (skp_nbhd_face F G y hyV (skp_oface_subset_face G hyG)).1
              subst hGF
              exact ((skp_oface_iff G y).1 hyG).1
          rw [hempty, measure_empty]
        · have hPm : MeasurableSet {y : Eucl N | ∀ l, l ∉ range F.2 → y l = F.1 l} := by
            have : {y : Eucl N | ∀ l, l ∉ range F.2 → y l = F.1 l} =
                ⋂ l ∈ (Finset.univ.filter fun l : Fin N => l ∉ range F.2), {y : Eucl N | y l = F.1 l} := by
              ext y; simp
            rw [this]
            exact Finset.measurableSet_biInter _ fun l _ =>
              measurableSet_eq_fun (skp_coord_continuous l).measurable measurable_const
          refine ae_restrict_of_forall_mem (hPm.inter (skp_isOpen_nbhd F).measurableSet) fun y hy => ?_
          have hyF : y ∈ skpOFace F := by
            rw [skpOFace_mem]
            intro l
            exact ⟨fun hl => ((skpNbhd_mem F y).1 hy.2 l).1 hl, hy.1 l⟩
          exact (hθF F y hyF).symm
      · rw [hξF F x hxF]
        rcases lt_or_gt_of_ne hβF with hneg | hpos
        · right
          rw [sign_neg hneg]
          simp only [SignType.coe_neg, SignType.coe_one]
          ext a
          simp
        · left
          rw [sign_pos hpos]
          simp only [SignType.coe_one]
          rw [one_smul]
    · -- integer values
      intro x hx
      obtain ⟨F, _, hxF⟩ := (hmemMp x).1 hx
      obtain ⟨k, hk⟩ := hβ F
      refine ⟨k.natAbs, ?_⟩
      rw [hθF F x hxF, hk, Nat.cast_natAbs, Int.cast_abs]
    · -- the action
      intro ω
      set ω' := (ω : DifferentialForm (Eucl N) (m + 1))
      obtain ⟨T, hT⟩ := skp_faces_finset (k := m + 1) _ ω.property.1.2
      set T' := T.filter fun F => β F ≠ 0
      rw [hP ω T hT]
      have hdrop : ∑ F ∈ T, β F * latticeFaceAction 1 F ω' = ∑ F ∈ T', β F * latticeFaceAction 1 F ω' := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun F _ => ?_
        split_ifs with h
        · rfl
        · push_neg at h; rw [h, zero_mul]
      rw [hdrop]
      unfold tauAction
      have hsub : (⋃ F ∈ T', skpOFace F) ⊆ Mp := by
        intro x hx
        obtain ⟨F, hF, hxF⟩ := mem_iUnion₂.1 hx
        exact (hmemMp x).2 ⟨F, (Finset.mem_filter.1 hF).2, hxF⟩
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMpm hsub ?_]
      · rw [integral_biUnion_finset T' (fun F _ => skp_measurableSet_oface F)
          (fun F _ G _ h => skp_oface_disjoint F G h) ?_]
        · refine Finset.sum_congr rfl fun F hF => ?_
          unfold latticeFaceAction
          rw [skp_face_integral, ← skp_oface_integral F
            (fun x => ω' x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))), ← integral_const_mul]
          refine setIntegral_congr_fun (skp_measurableSet_oface F) fun x hx => ?_
          rw [hθF F x hx, hξF F x hx, ContinuousLinearMap.smul_apply, simpleNVector_apply,
            smul_eq_mul, ← mul_assoc, abs_mul_sign]
        · intro F _
          have hc : Continuous fun x => ω' x (eF F) := skp_eval_continuous _ ω.property.1.1.continuous _
          obtain ⟨C, hC⟩ := (skp_isCompact_face F).exists_bound_of_continuousOn hc.continuousOn
          have hfin : (μHE[m + 1] : Measure (Eucl N)) (skpOFace F) < ∞ :=
            lt_of_le_of_lt (measure_mono (skp_oface_subset_face F)) (by rw [hface1]; exact ENNReal.one_lt_top)
          have hsgn : |(SignType.sign (β F) : ℝ)| ≤ 1 := by
            rcases lt_trichotomy (β F) 0 with h | h | h
            · rw [sign_neg h]; simp
            · rw [h]; simp
            · rw [sign_pos h]; simp
          have hcont : Continuous fun x => |β F| * ((SignType.sign (β F) : ℝ) * ω' x (eF F)) :=
            continuous_const.mul (continuous_const.mul hc)
          have hint0 : IntegrableOn (fun x => |β F| * ((SignType.sign (β F) : ℝ) * ω' x (eF F)))
              (skpOFace F) (μHE[m + 1] : Measure (Eucl N)) := by
            refine Measure.integrableOn_of_bounded (M := |β F| * C) hfin.ne
              hcont.aestronglyMeasurable ?_
            rw [ae_restrict_iff' (skp_measurableSet_oface F)]
            refine Eventually.of_forall fun x hx => ?_
            have := hC x (skp_oface_subset_face F hx)
            rw [Real.norm_eq_abs] at this
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs]
            calc |β F| * (|(SignType.sign (β F) : ℝ)| * |ω' x (eF F)|) ≤ |β F| * (1 * C) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul hsgn this (abs_nonneg _) zero_le_one)
                    (abs_nonneg _)
              _ = |β F| * C := by ring
          refine hint0.congr_fun (fun x hx => ?_) (skp_measurableSet_oface F)
          rw [hθF F x hx, hξF F x hx, ContinuousLinearMap.smul_apply, simpleNVector_apply,
            smul_eq_mul]
      · intro x hx
        obtain ⟨hxM, hxU⟩ := hx
        obtain ⟨F, hβF, hxF⟩ := (hmemMp x).1 hxM
        have hFT : F ∉ T := fun hF => hxU (mem_iUnion₂.2 ⟨F, Finset.mem_filter.2 ⟨hF, hβF⟩, hxF⟩)
        have hω0 : ω' x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hx'
          exact hFT (hT F ⟨x, skp_oface_subset_face F hxF, hx'⟩)
        rw [hω0]; simp
  have skp_round_abs_le : ∀ (b : ℝ), |(round b : ℝ)| ≤ 2 * |b| := by
    clear * - skp_cube_finite
    revert skp_cube_finite
    refine id ?_
    intro skp_cube_finite b
    by_cases h : round b = 0
    · rw [h]; simp
    · have h1 : (1 : ℝ) ≤ |(round b : ℝ)| := by
        have : (1 : ℤ) ≤ |round b| := Int.one_le_abs h
        exact_mod_cast this
      have h2 := abs_sub_round b
      have h3 : |(round b : ℝ)| ≤ |b| + 1 / 2 := by
        calc |(round b : ℝ)| = |b - (b - round b)| := by ring_nf
          _ ≤ |b| + |b - round b| := abs_sub _ _
          _ ≤ |b| + 1 / 2 := by linarith
      linarith
  clear * - skp_mass_tool skpOFace skpProj skp_oface_iff skp_volume_cube skp_cube_finite skpEta0 skpEta skpEta_bound skp_cubeP skp_cubeT skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_int_hyperplane skp_rep_integrableOn_bdd skp_face_HK skp_face_b_bound skp_chain_exists skp_support_boundary skp_assemble skp_int_round skp_chain_int skp_round_abs_le
  revert skp_mass_tool skpOFace skpProj skp_oface_iff skp_volume_cube skp_cube_finite skpEta0 skpEta skpEta_bound skp_cubeP skp_cubeT skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_int_hyperplane skp_rep_integrableOn_bdd skp_face_HK skp_face_b_bound skp_chain_exists skp_support_boundary skp_assemble skp_int_round skp_chain_int skp_round_abs_le
  refine id ?_
  intro skp_mass_tool skpOFace skpProj skp_oface_iff skp_volume_cube skp_cube_finite skpEta0 skpEta skpEta_bound skp_cubeP skp_cubeT skpProj_measurable skp_measurableSet_oface skp_oface_bounded skp_int_hyperplane skp_rep_integrableOn_bdd skp_face_HK skp_face_b_bound skp_chain_exists skp_support_boundary skp_assemble skp_int_round skp_chain_int skp_round_abs_le m ℓ hℓ
  classical
  obtain ⟨c₁, hc₁, hP⟩ := skp_cubeP (m + 1)
  obtain ⟨c₂, hc₂, hT⟩ := skp_cubeT (m + 1)
  obtain ⟨Mη, hMη0, hMη⟩ := skpEta_bound
  set cm : ℝ := (Fintype.card (Fin m → Fin (m + 1 + ℓ)) : ℝ) * (m + 1) with hcm
  set cb : ℝ := (Fintype.card (Fin (m + 1) → Fin (m + 1 + ℓ)) : ℝ) * Mη ^ (m + 1) with hcb
  have hcm0 : 0 ≤ cm := by positivity
  have hcb0 : 0 ≤ cb := by positivity
  set a₁ : ℝ := 2 * c₁ * cm with ha₁
  set a₂ : ℝ := 2 * cb with ha₂
  set a₃ : ℝ := c₂ * (cm + a₁) with ha₃
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have ha₃0 : 0 ≤ a₃ := by positivity
  set C : ℝ := max a₂ (max (1 + a₃) a₁) with hC
  refine ⟨C.toNNReal, ?_⟩
  intro Q hQm hQs _hQt
  have hQ : Q.mass < ∞ := (ENNReal.add_lt_top.1 hQm).1
  have hbQ : Q.boundary.mass < ∞ := (ENNReal.add_lt_top.1 hQm).2
  obtain ⟨μ, v, hμfin, hrep, hμS, hμ, -, hres⟩ := skp_mass_tool Q hQ
  obtain ⟨μ', v', hμ'fin, -, hμ'S, hμ', -, -⟩ := skp_mass_tool Q.boundary hbQ
  have hμL : μ (⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 hQs) hμS
  have hμ'L : μ' (⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 ((skp_support_boundary Q).trans hQs)) hμ'S
  have hL : ∀ᵐ x ∂μ, x ∈ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμL] with x hx
    simpa using hx
  have hdx := skp_int_hyperplane Q hbQ μ v hrep
  -- the data of the cube lemma on each face
  have hπc : ∀ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ),
      ∀ᵐ x ∂(μ.restrict (skpOFace F)), skpProj F x ∈ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1} := by
    intro F
    rw [ae_restrict_iff' (skp_measurableSet_oface F)]
    exact Eventually.of_forall fun x hx => ((skp_oface_iff F x).1 hx).2
  have hw : ∀ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ),
      Integrable (fun x => v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))))
        (μ.restrict (skpOFace F)) := fun F =>
    skp_rep_integrableOn_bdd Q μ v hrep _ _ (skp_oface_bounded F)
  have hHK : ∀ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ),
      ∀ Φ : Fin (m + 1) → Eucl (m + 1) → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) →
      (∀ k, HasCompactSupport (Φ k)) →
      (∀ k, tsupport (Φ k) ⊆ {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}) → ∀ B : ℝ, 0 ≤ B →
      (∀ k u, |Φ k u| ≤ B) →
      |∫ x, (∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ))) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j)))
          ∂(μ.restrict (skpOFace F))| ≤ (cm * (μ' (skpOFace F)).toReal) * B := by
    intro F Φ hΦs _ hΦt B hB hΦb
    have := skp_face_HK Q μ v hrep hL hdx μ' hμ' hμ'L F Φ hΦs hΦt B hB hΦb
    simpa [hcm, mul_assoc] using this
  set b : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ := fun F =>
    ∫ x in skpOFace F, (∏ j, skpEta (skpProj F x j)) *
      v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ with hb
  have hPF : ∀ F (g : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
      (∀ u, |g u| ≤ B) →
      |∫ x in skpOFace F, g (skpProj F x) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
        b F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤
        (c₁ * (cm * (μ' (skpOFace F)).toReal)) * B := by
    intro F g hg hgc B hB hgB
    exact hP (μ.restrict (skpOFace F)) (skpProj F) (skpProj_measurable F) (hπc F) _ (hw F) _
      (hHK F) g hg hgc B hB hgB
  have hbbound : ∀ F, |b F| ≤ cb * (μ (skpOFace F)).toReal := fun F =>
    skp_face_b_bound Q μ v hrep hL hdx hμ hμL F Mη hMη0 hMη
  -- the coefficients
  set β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ := fun F =>
    if IsIntegerMultiplicity Q then (round (b F) : ℝ) else b F with hβ
  have hβb : ∀ F, |b F - β F| ≤ c₁ * (cm * (μ' (skpOFace F)).toReal) := by
    intro F
    by_cases hint : IsIntegerMultiplicity Q
    · simp only [hβ, if_pos hint]
      exact skp_int_round Q hbQ μ v hrep hμS hres hQs hL hdx hint F (b F) _
        (by positivity) (hPF F)
    · simp only [hβ, if_neg hint, sub_self, abs_zero]
      exact mul_nonneg hc₁ (mul_nonneg hcm0 ENNReal.toReal_nonneg)
  have hβ1 : ∀ F (g : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → ∀ B : ℝ, 0 ≤ B →
      (∀ u, |g u| ≤ B) →
      |∫ x in skpOFace F, g (skpProj F x) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
        β F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤
        (a₁ * (μ' (skpOFace F)).toReal) * B := by
    intro F g hg hgc B hB hgB
    have h1 := hPF F g hg hgc B hB hgB
    have h2 : |∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| ≤ B := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}) (C := B) (f := g)
        (by rw [skp_volume_cube]; exact ENNReal.one_lt_top)
        (fun u _ => by rw [Real.norm_eq_abs]; exact hgB u)
      rwa [measureReal_def, skp_volume_cube, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] at this
    have h3 := hβb F
    calc _ = |(∫ x in skpOFace F, g (skpProj F x) *
            v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
          b F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u) +
          (b F - β F) * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1}, g u| := by ring_nf
      _ ≤ (c₁ * (cm * (μ' (skpOFace F)).toReal)) * B +
          (c₁ * (cm * (μ' (skpOFace F)).toReal)) * B := by
          refine (abs_add_le _ _).trans (add_le_add h1 ?_)
          rw [abs_mul]
          exact mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = (a₁ * (μ' (skpOFace F)).toReal) * B := by rw [ha₁]; ring
  have hβ3 : ∀ F (Φ : Fin (m + 1) → Eucl (m + 1) → ℝ), (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ k)) →
      (∀ k, HasCompactSupport (Φ k)) → ∀ B : ℝ, 0 ≤ B → (∀ k u, |Φ k u| ≤ B) →
      |∫ x in skpOFace F, (∑ k, fderiv ℝ (Φ k) (skpProj F x) (EuclideanSpace.single k (1 : ℝ))) *
          v x (wedgeCovectors (m + 1) (fun j => EuclideanSpace.proj (F.2 j))) ∂μ -
        β F * ∫ u in {u : Eucl (m + 1) | ∀ j, 0 < u j ∧ u j < 1},
          ∑ k, fderiv ℝ (Φ k) u (EuclideanSpace.single k (1 : ℝ))| ≤
        (a₃ * (μ' (skpOFace F)).toReal) * B := by
    intro F Φ hΦs hΦc B hB hΦb
    have := hT (μ.restrict (skpOFace F)) (skpProj F) (skpProj_measurable F) (hπc F) _ (hw F)
      (cm * (μ' (skpOFace F)).toReal) (a₁ * (μ' (skpOFace F)).toReal) (β F) (hHK F) (hβ1 F)
      Φ hΦs hΦc B hB hΦb
    calc _ ≤ c₂ * (cm * (μ' (skpOFace F)).toReal + a₁ * (μ' (skpOFace F)).toReal) * B := this
      _ = (a₃ * (μ' (skpOFace F)).toReal) * B := by rw [ha₃]; ring
  have hβ2 : ∀ F, |β F| ≤ a₂ * (μ (skpOFace F)).toReal := by
    intro F
    by_cases hint : IsIntegerMultiplicity Q
    · simp only [hβ, if_pos hint]
      calc |(round (b F) : ℝ)| ≤ 2 * |b F| := skp_round_abs_le _
        _ ≤ 2 * (cb * (μ (skpOFace F)).toReal) := by gcongr; exact hbbound F
        _ = a₂ * (μ (skpOFace F)).toReal := by rw [ha₂]; ring
    · simp only [hβ, if_neg hint]
      calc |b F| ≤ cb * (μ (skpOFace F)).toReal := hbbound F
        _ ≤ a₂ * (μ (skpOFace F)).toReal := by
            rw [ha₂]; gcongr; linarith
  obtain ⟨P, S, hPc, hPS, h1, h2, h3, h4, h5⟩ := skp_assemble Q hQ hbQ μ v hrep hμ hμS μ' hμ'
    hμ'S hL hdx a₁ a₂ a₃ ha₁0 ha₂0 ha₃0 β hβ1 hβ3 hβ2
  have hCreal : ∀ a : ℝ, a ≤ C → ENNReal.ofReal a ≤ (C.toNNReal : ℝ≥0∞) := fun a ha =>
    ENNReal.ofReal_le_ofReal ha
  refine ⟨β, P, S, hPc, hPS, ?_, ?_, ?_, h4, h5, ?_⟩
  · refine h1.trans ?_
    gcongr
    exact hCreal a₂ (le_max_left _ _)
  · refine h2.trans ?_
    gcongr
    exact hCreal (1 + a₃) ((le_max_left _ _).trans (le_max_right _ _))
  · refine h3.trans ?_
    gcongr
    exact hCreal a₁ ((le_max_right _ _).trans (le_max_right _ _))
  · intro hint
    have hβint : ∀ F, ∃ k : ℤ, β F = k := fun F => ⟨round (b F), by simp [hβ, hint]⟩
    refine ⟨hβint, ?_⟩
    obtain ⟨P', hP'c, hP'sum⟩ := skp_chain_exists (N := m + 1 + ℓ) (m := m) β
    have hPP' : P = P' := by
      ext ω
      rw [hPc ω, hP'c ω]
    rw [hPP']
    exact skp_chain_int (by omega) β hβint P' hP'sum

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06

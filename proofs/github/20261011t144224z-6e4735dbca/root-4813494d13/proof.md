<!-- theorem-id: gmt-ch06/root -->

# Final proof of `GMT.Ch06.main_theorem` (Simon, *Introduction to GMT*, Chapter 6 "Currents")

| | |
| --- | --- |
| Node | `root` of run `20261011T144224Z-6e4735dbca`; issue <https://github.com/ZhengyangZhang06/gmt-formalize/issues/6> |
| Declaration | `GMT.Ch06.main_theorem` in `GMT/Ch06/Submission.lean` (lines 69498–69504) |
| Frozen problem | `GMT/Ch06/Contract.lean` at `d8d46c9587747dee0751a1f780fcafdba16a3886`, byte-identical in the candidate |
| Lean source | `GMT/Ch06/Submission.lean`, sha256 `8844dc262ee305c7d301443a16525f97108a466caebf817f3e7d820abf0846f0`, unchanged since commit `e9e57ea4`; this revision changes only this Markdown file |
| Toolchain and libraries | Lean `v4.35.0-rc3`; Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`; `simongmt` (`Poincare.SimonGMT.*`) `2b3663083f3fe399b6296fb8eaee52169170e197`; all pinned by the frozen `lakefile.toml` and `lake-manifest.json` |
| Axioms of `main_theorem` | `propext`, `Classical.choice`, `Quot.sound` (§9) |
| Mathematical source | L. Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua notes), Ch. 6, printed pp. 131–180 |

## 0. Summary

`main_theorem` has no hypotheses. Its type is the conjunction of the twelve frozen propositions of
the contract, the headline results of Simon's Chapter 6. The Lean proof is one anonymous-constructor
term whose twelve components are the twelve accepted children of the root (§2). The type of each
component is, verbatim, the conjunct in its position.

**How results are cited in this document.**

- The twelve conjuncts are the frozen types of the twelve root children. §3 reproduces each of them
  verbatim in Lean and translates it hypothesis by hypothesis. The contract notions they use are
  reproduced and translated in §1.3–§1.4.
- Every other accepted declaration of the run (679 descendants of the root children) is cited
  **only by its exact Lean name** `GMT.Ch06.Submission.<name>`, written without the prefix
  `GMT.Ch06.Submission.`; Appendix A gives its line in `GMT/Ch06/Submission.lean`. This document
  does not paraphrase their results; the authoritative statement of each is its Lean type, which §9
  checks against the node's frozen `lean_statement`.
- Library declarations (Mathlib, SimonGMT) named in the prose are likewise cited only by their
  exact Lean names, with file and line at the pinned revisions (§1.3, §5, Appendix B); the library
  definitions that the statements use are described exactly in §1.3. The Lean code reproduced in
  §3 names further library lemmas, as part of the shown proofs.
- The proofs of the 679 descendants are not re-derived here. Each accepted node's natural-language
  proof was independently reviewed when its parent's decomposition was audited, and its Lean proof
  passed the node's own exact comparator. Appendix A gives, for each node, its theorem issue, its
  solution PR and the committed copy of its reviewed proof; those proofs are cited, not repeated.
  For the twelve root children, §3 shows their Lean proofs, which assemble cited declarations.
- The doc comments in `Submission.lean` are informal notes written by the authors of the accepted
  Lean proofs. They are not part of any Lean statement or proof, and this document does not rely
  on them (§1.5).

**Counts.** The run has 691 accepted declarations besides the root. Each occurs exactly once in
`Submission.lean`, under its exact globally qualified name and with its frozen type (§9). 688 of them
are used, directly or transitively, by the proof of `main_theorem`; the other 3 are kept unchanged
to preserve their accepted interfaces (§6).

**Order.** The book does not prove its results in printed order: Theorem 3.11 (p. 149) is derived
in Remark 8.3(2) (p. 176), which says that it "follows by using 6.3" from Theorem 8.2. The root
children use one another only in the acyclic pattern of §4. Lean checks the declarations of
`Submission.lean` top to bottom, and no declaration refers to a later one, so the order is enforced
by the kernel.

**This revision** replaces the previous version's re-derivations (its §3) and its reproduction of
the accepted declarations' doc comments (its Appendix A) by exact statements of the twelve
conjuncts, the Lean proofs of the twelve root children and name-only citations, in response to the
third independent review (§7, §8). The Lean source is unchanged.

## 1. Statement, assumptions and conventions

### 1.1 The statement

```lean
theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧
    LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧
    DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧
    BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧
    IntegralityOfWeakLimits
```

(In the file the statement is on one line, `Contract.lean:362` and `Submission.lean:69498`.) The
conjunction is right-nested. The book items follow `GMT/Ch06/README.md` ("Statement map"):

| # | Proposition (frozen `def … : Prop`, `Contract.lean` line) | Simon, Ch. 6 | Statement |
| --- | --- | --- | --- |
| 1 | `CompactnessUnderMassBounds` (198) | Lemma 2.15, p. 137 | §3.1 |
| 2 | `ConstancyTheorem` (213) | Theorem 2.34, p. 142 | §3.2 |
| 3 | `LipschitzPushforwardIntegerMultiplicity` (223) | Lemma 3.9, p. 148 | §3.3 |
| 4 | `FedererFlemingCompactness` (234) | Theorem 3.11, p. 149 | §3.4 |
| 5 | `SlicingTheorem` (250) | §4, 4.4–4.10, pp. 153–158 | §3.5 |
| 6 | `DeformationTheorem` (274) | 5.3, p. 160 (5.1 is the case `ρ = 1`) | §3.6 |
| 7 | `IsoperimetricTheorem` (297) | 6.1, p. 168 | §3.7 |
| 8 | `PolyhedralApproximation` (308) | 6.2, p. 169 | §3.8 |
| 9 | `BoundaryRectifiability` (321) | 6.3, p. 170 | §3.9 |
| 10 | `FlatConvergenceIffWeakConvergence` (329) | Theorem 7.2, p. 170 | §3.10 |
| 11 | `RectifiabilityTheorem` (342) | 8.1, p. 173 | §3.11 |
| 12 | `IntegralityOfWeakLimits` (352) | Theorem 8.2, p. 176 | §3.12 |

### 1.2 Assumptions

`main_theorem` is a closed proposition: it has no hypotheses. Each conjunct quantifies over its
dimensions, sets, currents, maps, sequences and scales with exactly the hypotheses of its definition
in `GMT/Ch06/Contract.lean`, reproduced in §3. The proof adds, removes or weakens no hypothesis. It
declares no axiom and uses no `sorry`; the only axioms in its dependency closure are `propext`,
`Classical.choice` and `Quot.sound` (§9).

### 1.3 Notation for the library notions in the statements

Each symbol below abbreviates the Lean notion named next to it; the description is that notion's
definition at the pinned revisions (SimonGMT paths are relative to `Poincare/SimonGMT/` in the
`simongmt` package).

- `ℝ^P` is `Eucl P := EuclideanSpace ℝ (Fin P)` (`Contract.lean:43`), with its Borel σ-algebra.
  "Measure on `ℝ^P`" means `Measure (Eucl P)`. `volume` is Lebesgue measure; `L¹` is Lebesgue
  measure on `ℝ`. `e_i = EuclideanSpace.single i 1` is the `i`-th standard basis vector.
- `Hᵏ` is `μHE[k] = MeasureTheory.Measure.euclideanHausdorffMeasure k`
  (`Mathlib/Geometry/Euclidean/Volume/Measure.lean:68`, notation at `:72`): the Hausdorff
  measure `μH[k]` of `ℝ^P` multiplied by the constant `addHaarScalarFactor volume μH[k]` computed on
  `ℝᵏ`, i.e. `μH[k]` normalized to agree with Lebesgue measure on `k`-dimensional Euclidean space. `Hᵏ⌞M` is `μHE[k].restrict M`.
- A `k`-covector is an element of `Covector (ℝ^P) k = ℝ^P [⋀^Fin k]→L[ℝ] ℝ`, a continuous alternating
  `k`-linear form (`Chapter06/Forms.lean:31`). A `k`-form is a map `ℝ^P → Covector (ℝ^P) k`
  (`DifferentialForm`, `Forms.lean:37`). A `k`-vector is an element of
  `NVector (ℝ^P) k = Covector (ℝ^P) k →L[ℝ] ℝ` (`Chapter06/FormsDuality.lean:31`), and
  `⟨α, ξ⟩ = ξ α`.
- For `τ : Fin k → ℝ^P`, `τ₁ ∧ ⋯ ∧ τₖ` (the entries of `τ` in order) is `simpleNVector τ`, the
  `k`-vector `α ↦ α(τ)` (`FormsDuality.lean:93`).
  For a continuous linear `L : ℝ^P → ℝ^Q`, `L_# ξ` is `nVectorPushforward k L ξ`, the `k`-vector
  `α ↦ ξ(L^# α)` with `(L^# α)(v₁, …, vₖ) = α(L v₁, …, L vₖ)` (`FormsDuality.lean:39`, `:65`).
  `SimonMultiIndex k N = Fin k ↪o Fin N` is the type of strictly increasing maps `Fin k → Fin N`
  (`FormsDuality.lean:22`).
- `𝒟ᵏ(U)` is `TestFormOn U k` (`Chapter06/Currents.lean:100`, `:123`): the `k`-forms `ω` on `ℝ^P` that
  are `C^∞` (`ContDiff ℝ ∞`), have compact support (`HasCompactSupport`) and satisfy
  `tsupport ω ⊆ U`.
- `𝒟ₖ(U)` is `GeometricCurrentOn U k` (`Currents.lean:145`): an `ℝ`-linear map `T : 𝒟ᵏ(U) → ℝ` such
  that `T(ω_j) → 0` for every sequence `ω_j ∈ 𝒟ᵏ(U)` for which some compact `K ⊆ U` contains every
  `tsupport ω_j` and every iterated derivative of `ω_j` tends to `0` uniformly on `K`
  (`TestFormOnConverges`, `Currents.lean:132`). `0` is the zero current.
- `∂T` is `T.boundary` for `T ∈ 𝒟_{k+1}(U)` (`Currents.lean:325`): `∂T(ω) = T(dω)` for
  `ω ∈ 𝒟ᵏ(U)`, with `d` SimonGMT's exterior derivative (`exteriorDerivativeTestOn`, `Currents.lean:193`).
- `|α|` is `covectorEuclideanNorm α = (∑_I α(e_{I(0)}, …, e_{I(k−1)})²)^{1/2}`, the sum over the
  strictly increasing `I : Fin k → Fin P` (`Chapter06/Mass.lean:30`).
- `M_W(T)` is `T.massOn W` (`Mass.lean:68`): the supremum in `[0, ∞]` of `ENNReal.ofReal (T ω)` over
  the `ω ∈ 𝒟ᵏ(U)` with `tsupport ω ⊆ W` and `|ω(x)| ≤ 1` for every `x`. `M(T)` is
  `T.mass = T.massOn U` (`Mass.lean:74`).
- `spt T` is `T.support = U ∖ ⋃ {W : W open, closure W compact, closure W ⊆ U, T(ω) = 0 for every
  ω ∈ 𝒟ᵏ(U) with tsupport ω ⊆ W}` (`Chapter06/CurrentLocalEquality.lean:101–117`).
- `T_j ⇀ T` is `WeaklyConvergesOn (fun j => T_j) T` (`Currents.lean:158`): `T_j(ω) → T(ω)` for every
  `ω ∈ 𝒟ᵏ(U)`.
- `CountablyRectifiable k M` (`Chapter03/Rectifiable.lean:34`): there are a set `M₀ ⊆ ℝ^P` with
  `Hᵏ(M₀) = 0` and Lipschitz maps `F_j : ℝᵏ → ℝ^P` (`j ∈ ℕ`) with `M ⊆ M₀ ∪ ⋃_j F_j(ℝᵏ)`.
- `HasWeightedApproximateTangentSpaceAt k M θ x V` (`Chapter03/Rectifiable.lean:330`), for a
  submodule `V` of `ℝ^P`: `dim V = k`, and for every continuous compactly supported
  `f : ℝ^P → ℝ`, `∫_{η_{x,r}(M)} f(y) θ(x + r y) dHᵏ(y) → θ(x) ∫_V f dHᵏ` as `r → 0⁺`, where
  `η_{x,r}(y) = r⁻¹(y − x)` (`blowUpMap`, `Rectifiable.lean:96`).
- `Θ*ˢ(μ, x)` is `dimensionalUpperDensity μ.toOuterMeasure s univ x`
  (`Chapter01/Densities.lean:44`): `limsup_{r→0⁺} μ(B̄_r(x)) / (ω_s ENNReal.ofReal(r)^s)` in
  `[0, ∞]`, with `ω_s = ENNReal.ofReal(π^{s/2}/Γ(s/2 + 1))` (`realUnitBallVolume`,
  `Chapter01/Hausdorff.lean:34`) and `B̄_r(x)` the closed ball.
- Mathlib conventions used below: `∫` is the Bochner integral, whose value is `0` for a function
  that is not integrable; `∫⁻` is the lower Lebesgue integral of a `[0, ∞]`-valued function; `∑'`
  is the unconditional sum `tsum`, whose value is `0` for a non-summable family; `⨆` is the
  supremum in `[0, ∞]`; `∀ᵐ x ∂μ` means "for `μ`-almost every `x`"; `fderiv ℝ f x` is the Fréchet
  derivative, which is `0` where `f` is not differentiable, and `‖·‖₊` its operator norm in `ℝ≥0`;
  `thickening δ E = {x : infEDist x E < ENNReal.ofReal δ}` (`Mathlib/Topology/MetricSpace/Thickening.lean:53`),
  which is empty if `E` is empty; `IsConnected U` means `U` nonempty and preconnected;
  `LipschitzOnWith L f U` means `edist (f x) (f y) ≤ L · edist x y` for all `x, y ∈ U`, and
  `LocallyLipschitzOn U f` means that every `x ∈ U` has a neighbourhood `t` of `x` within `U`
  (`t ∈ 𝓝[U] x`) on which `f` is Lipschitz with some constant
  (`Mathlib/Topology/EMetricSpace/Lipschitz.lean:72`).

### 1.4 The contract's own definitions

The statements also use the following definitions of `Contract.lean` (namespace `GMT.Ch06`, with
`variable {P : ℕ}`). Each is reproduced verbatim and then read clause by clause.

```lean
def CompactlyContainedOpen (W U : Set (Eucl P)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U
```

`W ⊂⊂ U` means `CompactlyContainedOpen W U`: `W` is open, `closure W` is compact and
`closure W ⊆ U`.

```lean
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
```

`(M, θ, ξ)` is a *rectifiable triple* in `U` of dimension `n` when (1) `M ⊆ U`; (2) `M` is
`Hⁿ`-null-measurable; (3) `M` is countably `n`-rectifiable; (4) `θ(x) > 0` for every `x ∈ M`;
(5) `θ` is `Hⁿ`-integrable on `M ∩ K` for every compact `K ⊆ U`; (6) `ξ : ℝ^P → NVector (ℝ^P) n` is
`Hⁿ⌞M`-almost everywhere strongly measurable; (7) for `Hⁿ⌞M`-almost every `x` there is an
orthonormal family `τ : Fin n → ℝ^P` such that `span τ` is a weighted approximate tangent space of
`(M, θ)` at `x` (`HasWeightedApproximateTangentSpaceAt n M θ x (span τ)`) and
`ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` or `ξ(x) = −τ₁ ∧ ⋯ ∧ τₙ`.

```lean
def tauAction (n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (ω : DifferentialForm (Eucl P) n) : ℝ :=
  ∫ x in M, θ x * ξ x (ω x) ∂(μHE[n] : Measure (Eucl P))

def IsRectifiableCurrent {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

def IsIntegerMultiplicity {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
    ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

def IsIntegralCurrent {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) : Prop :=
  IsIntegerMultiplicity T ∧ IsIntegerMultiplicity T.boundary
```

`τ(M, θ, ξ)(ω) = tauAction n M θ ξ ω` is the Bochner integral `∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHⁿ(x)`.
`T ∈ 𝒟ₙ(U)` is *rectifiable* if there is a rectifiable triple `(M, θ, ξ)` in `U` of dimension `n`
with `T(ω) = τ(M, θ, ξ)(ω)` for every `ω ∈ 𝒟ⁿ(U)`. `T` is *integer multiplicity* if there is a
rectifiable triple `(M, θ, ξ)` in `U` of dimension `n` such that, for every `x ∈ M`, `θ(x) = k` for
some `k ∈ ℕ`, and `T(ω) = τ(M, θ, ξ)(ω)` for every `ω ∈ 𝒟ⁿ(U)`. `T ∈ 𝒟_{m+1}(U)` is an *integral
current* if `T` and `∂T` are both integer multiplicity.

```lean
def IsMeasureRepresentation {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) : Prop :=
  ∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ ∧
    T ω = ∫ x, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

def IsRestriction {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) (A : Set (Eucl P))
    (S : GeometricCurrentOn U n) : Prop :=
  MeasurableSet A ∧ ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
    IsMeasureRepresentation T μ v ∧
    ∀ ω : TestFormOn U n, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

def IsMassMeasure {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) : Prop :=
  μ Uᶜ = 0 ∧ ∀ W, CompactlyContainedOpen W U → μ W = T.massOn W

def IsSlice {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ)
    (t : ℝ) (S : GeometricCurrentOn U m) : Prop :=
  ∃ (A : GeometricCurrentOn U (m + 1)) (B : GeometricCurrentOn U m),
    IsRestriction T {x | x ∈ U ∧ f x < t} A ∧
    IsRestriction T.boundary {x | x ∈ U ∧ f x < t} B ∧
    ∀ ω : TestFormOn U m, S ω = A.boundary ω - B ω
```

`(μ, v)` is a *measure representation* of `T ∈ 𝒟ₙ(U)` if, for every `ω ∈ 𝒟ⁿ(U)`,
`x ↦ ⟨ω(x), v(x)⟩` is `μ`-integrable and `T(ω) = ∫ ⟨ω(x), v(x)⟩ dμ(x)`. `S` is a *restriction* of
`T` to `A` if `A` is Borel and, for some measure representation `(μ, v)` of `T`,
`S(ω) = ∫_A ⟨ω(x), v(x)⟩ dμ(x)` for every `ω ∈ 𝒟ⁿ(U)`. `μ` is a *mass measure* of `T` if
`μ(ℝ^P ∖ U) = 0` and `μ(W) = M_W(T)` for every `W ⊂⊂ U`. `S ∈ 𝒟_m(U)` is a *slice* of
`T ∈ 𝒟_{m+1}(U)` by `f` at `t` if there are a restriction `A ∈ 𝒟_{m+1}(U)` of `T` and a restriction
`B ∈ 𝒟_m(U)` of `∂T`, both to `{x ∈ U : f(x) < t}`, with `S(ω) = ∂A(ω) − B(ω)` for every
`ω ∈ 𝒟ᵐ(U)`.

```lean
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
```

`S ∈ 𝒟ₙ(V)` is a *Lipschitz push-forward* of `T ∈ 𝒟ₙ(U)` by `f : ℝ^P → ℝ^Q` if there are a
rectifiable triple `(M, θ, ξ)` in `U` of dimension `n` with `T = τ(M, θ, ξ)` on `𝒟ⁿ(U)` and a field
`L` of continuous linear maps `ℝ^P → ℝ^Q` such that, for `Hⁿ⌞M`-almost every `x`, for every
submodule `V'` of `ℝ^P` with `HasWeightedApproximateTangentSpaceAt n M θ x V'` and every `v ∈ V'`,
the map `t ↦ f(x + t v)` has derivative `L(x) v` at `t = 0`, and
`S(ω) = ∫_M θ(x) ⟨ω(f(x)), L(x)_# ξ(x)⟩ dHⁿ(x)` for every `ω ∈ 𝒟ⁿ(V)`.

```lean
abbrev LatticeFaceIndex (n N : ℕ) := (Fin N → ℤ) × SimonMultiIndex n N

def latticeFace {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N) : Set (Eucl N) :=
  {x | ∀ i : Fin N,
    (i ∈ range F.2 → ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)) ∧
    (i ∉ range F.2 → x i = ρ * (F.1 i : ℝ))}

def latticeFaceAction {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N)
    (ω : DifferentialForm (Eucl N) n) : ℝ :=
  ∫ x in latticeFace ρ F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
    ∂(μHE[n] : Measure (Eucl N))

def IsLatticeChain {n N : ℕ} {U : Set (Eucl N)} (ρ : ℝ) (β : LatticeFaceIndex n N → ℝ)
    (Pc : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, Pc ω = ∑' F, β F * latticeFaceAction ρ F ω

def flatDistance {U : Set (Eucl P)} {n : ℕ} (W : Set (Eucl P))
    (T₁ T₂ : GeometricCurrentOn U n) : ℝ≥0∞ :=
  ⨅ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n)
    (_ : IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
      ∀ ω : TestFormOn U n, T₁ ω - T₂ ω = R.boundary ω + S ω),
    S.massOn W + R.massOn W
```

A lattice face index `F = (z, α)` consists of `z ∈ ℤᴺ` and a strictly increasing `α : Fin n → Fin N`.
`latticeFace ρ F` is the set of `x ∈ ℝᴺ` with `ρ z_i ≤ x_i ≤ ρ(z_i + 1)` for `i` in the range of `α`
and `x_i = ρ z_i` for the other `i`. `[[F]](ω) = latticeFaceAction ρ F ω` is the Bochner integral
`∫_{latticeFace ρ F} ω(x)(e_{α(0)}, …, e_{α(n−1)}) dHⁿ(x)`. `IsLatticeChain ρ β Pc` means
`Pc(ω) = ∑'_F β(F) [[F]](ω)` for every `ω ∈ 𝒟ⁿ(U)`. `flatDistance W T₁ T₂ = d_W(T₁, T₂)` is the
infimum in `[0, ∞]` of `M_W(S) + M_W(R)` over all pairs `(R, S)` with `R ∈ 𝒟_{n+1}(U)` and
`S ∈ 𝒟ₙ(U)` both integer multiplicity and `T₁(ω) − T₂(ω) = ∂R(ω) + S(ω)` for every
`ω ∈ 𝒟ⁿ(U)`; it is `∞` if there is no such pair.

### 1.5 What `Submission.lean` contains

`GMT/Ch06/Submission.lean` (69506 lines) consists of, in order:

1. Lines 1–15: the contract's 8 imports (lines 1–8, identical to `Contract.lean:1–8`) and 7
   further SimonGMT imports (`Chapter01.RadonCaratheodoryIntegral`, `Chapter06.AffineCurrentPushforward`,
   `Chapter01.RadonPolarRepresentation`, `Chapter02.AreaBranches`, `Chapter01.DensityComparison`,
   `Chapter02.AreaCritical`, `Chapter02.AreaDomain`).
2. Lines 16–367: byte for byte `Contract.lean:9–360`, i.e. the module docstring, the `open` commands,
   `namespace GMT.Ch06`, `noncomputable section`, the contract's 29 definitions (26 `def`s, the
   2 `abbrev`s `Eucl` and `LatticeFaceIndex`, and the `structure IsRectifiableTriple`) and the `end`
   that closes the section. So a contract line `c` (`9 ≤ c ≤ 360`) is line `c + 7` of
   `Submission.lean`.
3. Lines 369–69497: the 691 accepted theorems `Submission.<lean_name>`. Nine of them are preceded
   by a one-command modifier: `set_option maxHeartbeats … in` (3) or
   `open scoped CompactlySupported in` (6; five of these were introduced by the integration
   commits — merges of accepted checkpoints and the controller's "Re-merge declarations
   line-merged from …" commits —, §9). All
   but six (`rectifiability_mass_measure_representation`, `iwl_cr_hp_injective_pieces`,
   `br_top_dim_lattice_approximation`, `ind_pi_ss_cycle_slice_boundary`,
   `rectifiability_mickle_rado_sup_lsc`, `iwl_top_dim_integrality`) carry a doc comment.
4. Lines 69498–69504: `main_theorem`, with the contract's statement and the proof of §2.
5. Line 69506: `end GMT.Ch06`.

There are no other declarations, no duplicate names, one `namespace GMT.Ch06` and one
`end GMT.Ch06` (§9).

**Doc comments.** The doc comments of the 685 documented accepted theorems were written by the
authors of the accepted Lean proofs, and they belong to the accepted declaration texts, which are
kept unchanged (§9).
They are informal. They are neither statements nor proofs, the kernel does not read them, and
this document does not rely on them. The independent reviews of the previous versions of this
document found errors in their Appendix A, which reproduced these doc comments (§7). Wherever a
doc comment and a Lean type differ, the Lean type is authoritative.

## 2. The root argument

The Lean proof of `main_theorem` (`Submission.lean:69498–69504`):

```lean
theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by
  exact ⟨Submission.compactness_under_mass_bounds, Submission.constancy_theorem,
    Submission.lipschitz_pushforward_integer_multiplicity, Submission.federer_fleming_compactness,
    Submission.slicing_theorem, Submission.deformation_theorem, Submission.isoperimetric_theorem,
    Submission.polyhedral_approximation, Submission.boundary_rectifiability,
    Submission.flat_convergence_iff_weak_convergence, Submission.rectifiability_theorem,
    Submission.integrality_of_weak_limits⟩
```

*Proof.* The type of `main_theorem` is the right-nested conjunction
`A₁ ∧ (A₂ ∧ (⋯ ∧ (A₁₁ ∧ A₁₂)))` of the twelve propositions of §1.1, and the anonymous constructor
`⟨h₁, h₂, …, h₁₂⟩` elaborates to `And.intro h₁ (And.intro h₂ (… (And.intro h₁₁ h₁₂)))`. So the term
proves `main_theorem` exactly when each `hᵢ` proves `Aᵢ`. Inside `namespace GMT.Ch06`,
`Submission.X` denotes `GMT.Ch06.Submission.X`, and each of the twelve terms is an accepted theorem
whose declared type is, verbatim, the proposition `Aᵢ` in its position:

| # | Conjunct `Aᵢ` | Term `hᵢ` (declaration line) | Accepted node; theorem issue; solution PR |
| --- | --- | --- | --- |
| 1 | `CompactnessUnderMassBounds` | `Submission.compactness_under_mass_bounds` (69081) | `root.compactness_mass_bounds-a1`; #314; #4238 |
| 2 | `ConstancyTheorem` | `Submission.constancy_theorem` (42133) | `root.constancy-a1`; #316; #4888 |
| 3 | `LipschitzPushforwardIntegerMultiplicity` | `Submission.lipschitz_pushforward_integer_multiplicity` (46209) | `root.lipschitz_pushforward_im-a1`; #319; #4707 |
| 4 | `FedererFlemingCompactness` | `Submission.federer_fleming_compactness` (69482) | `root.federer_fleming-a1`; #342; #8802 |
| 5 | `SlicingTheorem` | `Submission.slicing_theorem` (66972) | `root.slicing-a1`; #322; #5777 |
| 6 | `DeformationTheorem` | `Submission.deformation_theorem` (66990) | `root.deformation-a1`; #325; #7759 |
| 7 | `IsoperimetricTheorem` | `Submission.isoperimetric_theorem` (67200) | `root.isoperimetric-a1`; #329; #8118 |
| 8 | `PolyhedralApproximation` | `Submission.polyhedral_approximation` (67293) | `root.polyhedral_approximation-a1`; #331; #8056 |
| 9 | `BoundaryRectifiability` | `Submission.boundary_rectifiability` (68901) | `root.boundary_rectifiability-a1`; #334; #8641 |
| 10 | `FlatConvergenceIffWeakConvergence` | `Submission.flat_convergence_iff_weak_convergence` (69448) | `root.flat_iff_weak-a1`; #338; #8796 |
| 11 | `RectifiabilityTheorem` | `Submission.rectifiability_theorem` (62437) | `root.rectifiability-a1`; #340; #5445 |
| 12 | `IntegralityOfWeakLimits` | `Submission.integrality_of_weak_limits` (68796) | `root.integrality_weak_limits-a1`; #341; #8548 |

Issues are <https://github.com/ZhengyangZhang06/gmt-formalize/issues/N> and PRs
<https://github.com/ZhengyangZhang06/gmt-formalize/pull/N>. All twelve declarations precede
`main_theorem` in the file; §3 states each of them and shows its Lean proof. The root proof uses no
hypothesis, no other lemma and no tactic besides `exact`. Hence `main_theorem` holds. ∎

## 3. The twelve conjuncts

Each subsection gives the conjunct verbatim, with its line range in `Contract.lean` and in
`Submission.lean` (where it is the same text 7 lines lower); its statement, translated hypothesis
by hypothesis in the notation of §1.3–§1.4; and its proof, which is the accepted root child named
there.

For every root child the following holds, and it is not repeated below. The child's
natural-language proof is in the root decomposition `nodes/root/decomposition-v3.json` of the run
directory `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/`. That decomposition
was accepted by the independent audit `nodes/root/decomposition-audit-v3.json`, which found the
natural-language proof of each of the twelve children acceptable. The proof was handed to the child
node as `parent-supplied-natural-proof.md`, committed on this branch under
`.humanize-workspace/20261011t144224z-6e4735dbca/root/children/<child>/`. The child's Lean proof
passed the child's own exact comparator at its accepted candidate commit, and the root comparator
re-checks it with the Lean kernel as part of the closure of `main_theorem` (§9).

Each subsection shows the root child's Lean proof as it stands in `Submission.lean`, except that
its `--` comments are removed: they are informal notes, not part of the proof. In the twelve proofs
these are 58 comments, 54 on lines of their own (those lines are dropped) and 4 at the end of a code
line (removed with the spaces before them); nothing else is changed. These proofs assemble other accepted declarations. Those are cited by
exact name and line, their statements are their Lean types, and their proofs are cited in Appendix
A. The prose around the code describes only the code, namely which declaration is applied to which
arguments; it does not restate the results of the cited declarations.

### 3.1 `CompactnessUnderMassBounds` (Simon, Lemma 2.15) — `compactness_under_mass_bounds`

Frozen proposition (`Contract.lean:198–208`, `Submission.lean:205–215`):

```lean
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
```

**Statement.** Let `P, n ∈ ℕ`, let `U ⊆ ℝ^P` be open, and let `(T_q)_{q∈ℕ}` be a sequence in `𝒟ₙ(U)`.

- Hypothesis: for every `W ⊂⊂ U`, `sup_q M_W(T_q) < ∞`.
- Conclusion: there are `φ : ℕ → ℕ` and `T₀ ∈ 𝒟ₙ(U)` such that
  1. `φ` is strictly increasing;
  2. `T_{φ(q)} ⇀ T₀`;
  3. for every map `ω : ℝ^P → Covector (ℝ^P) n` that is continuous, has compact support and
     satisfies `tsupport ω ⊆ U`, for all measures `μ_q` on `ℝ^P` and maps
     `v_q : ℝ^P → NVector (ℝ^P) n` (`q ∈ ℕ`), and for every measure `μ₀` on `ℝ^P` and map
     `v₀ : ℝ^P → NVector (ℝ^P) n`: if `(μ_q, v_q)` is a measure representation of `T_{φ(q)}` for
     every `q`, and `(μ₀, v₀)` is a measure representation of `T₀`, then the Bochner integrals
     `∫ ⟨ω(x), v_q(x)⟩ dμ_q(x)` tend to `∫ ⟨ω(x), v₀(x)⟩ dμ₀(x)` as `q → ∞`.

**Proof.** The accepted theorem `Submission.compactness_under_mass_bounds`
(`Submission.lean:69081–69088`; node `root.compactness_mass_bounds-a1`, issue #314, PR #4238,
accepted candidate `ec8c9ac4`). Its Lean proof:

```lean
theorem Submission.compactness_under_mass_bounds : CompactnessUnderMassBounds := by
  intro P n U hU T hT
  obtain ⟨φ, T₀, hφ, hconv⟩ := Submission.cmb_exists_weakly_convergent_subseq P n U hU T hT
  have hTφ : ∀ W, CompactlyContainedOpen W U → (⨆ q, (T (φ q)).massOn W) < ∞ :=
    fun W hW => (iSup_comp_le (fun q => (T q).massOn W) φ).trans_lt (hT W hW)
  exact ⟨φ, T₀, hφ, hconv,
    Submission.cmb_tendsto_integral_of_weaklyConvergesOn P n U hU (fun q => T (φ q)) T₀ hTφ hconv⟩
```

It names the accepted declarations `cmb_exists_weakly_convergent_subseq` (L68932) and
`cmb_tendsto_integral_of_weaklyConvergesOn` (L9980), and no root child. The output `φ, T₀, hφ, hconv` of the first supplies conclusions 1 and 2. The second is
applied to the subsequence `q ↦ T_{φ(q)}`, to `T₀`, to `hTφ` (`sup_q M_W(T_{φ(q)}) < ∞` for every
`W ⊂⊂ U`, obtained from `sup_q M_W(T_{φ(q)}) ≤ sup_q M_W(T_q)`, Mathlib's `iSup_comp_le`) and to
`hconv`, and supplies conclusion 3.

### 3.2 `ConstancyTheorem` (Simon, Theorem 2.34) — `constancy_theorem`

Frozen proposition (`Contract.lean:213–218`, `Submission.lean:220–225`):

```lean
def ConstancyTheorem : Prop :=
  ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U →
    ∀ T : GeometricCurrentOn U (m + 1), T.boundary = 0 →
      ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1),
        T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume
```

**Statement.** Let `m ∈ ℕ`, let `U ⊆ ℝ^{m+1}` be open and connected, and let `T ∈ 𝒟_{m+1}(U)`.

- Hypothesis: `∂T = 0` (the zero current of `𝒟_m(U)`).
- Conclusion: there is `c ∈ ℝ` such that, for every `ω ∈ 𝒟^{m+1}(U)`,
  `T(ω) = c · ∫_U ω(x)(e_0, …, e_m) dx`, where `(e_i)_{i ∈ Fin (m+1)}` is the standard basis
  (`i ↦ EuclideanSpace.single i 1`) and the integral is the Bochner integral over `U` for Lebesgue
  measure (`volume`).

**Proof.** The accepted theorem `Submission.constancy_theorem` (`Submission.lean:42133–42137`;
node `root.constancy-a1`, issue #316, PR #4888, candidate `b4bbd871`). Its Lean proof:

```lean
theorem Submission.constancy_theorem : ConstancyTheorem := by
  intro m U hU hconn T hT
  exact Submission.constancy_of_local_constancy m U hU hconn T
    (Submission.constancy_local_on_balls m U hU T
      (Submission.constancy_closed_kills_partial_derivatives m U T hT))
```

It names the accepted declarations `constancy_closed_kills_partial_derivatives` (L16987),
`constancy_local_on_balls` (L41865) and `constancy_of_local_constancy` (L42065), and no root child.

### 3.3 `LipschitzPushforwardIntegerMultiplicity` (Simon, Lemma 3.9) — `lipschitz_pushforward_integer_multiplicity`

Frozen proposition (`Contract.lean:223–228`, `Submission.lean:230–235`):

```lean
def LipschitzPushforwardIntegerMultiplicity : Prop :=
  ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
    ∀ (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q),
      IsIntegerMultiplicity T → LocallyLipschitzOn U f → MapsTo f U V →
      (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) →
      ∃ S : GeometricCurrentOn V n, IsLipschitzPushforward T f S ∧ IsIntegerMultiplicity S
```

**Statement.** Let `P, Q, n ∈ ℕ`, let `U ⊆ ℝ^P` and `V ⊆ ℝ^Q` be open, let `T ∈ 𝒟ₙ(U)` and let
`f : ℝ^P → ℝ^Q`.

- Hypotheses:
  1. `T` is integer multiplicity;
  2. `f` is locally Lipschitz on `U`;
  3. `f` maps `U` into `V`;
  4. for every compact `K ⊆ V`, the set `f⁻¹(K) ∩ spt T` is compact.
- Conclusion: there is `S ∈ 𝒟ₙ(V)` such that `S` is a Lipschitz push-forward of `T` by `f`
  (`IsLipschitzPushforward T f S`, §1.4) and `S` is integer multiplicity.

**Proof.** The accepted theorem `Submission.lipschitz_pushforward_integer_multiplicity`
(`Submission.lean:46209–46223`; node `root.lipschitz_pushforward_im-a1`, issue #319, PR #4707,
candidate `3289485c`). Its Lean proof:

```lean
theorem Submission.lipschitz_pushforward_integer_multiplicity :
    LipschitzPushforwardIntegerMultiplicity := by
  intro P Q n U V hU hV T f hT hf hfUV hproper
  obtain ⟨M, θ, ξ, hMθξ, hθ, hTrep⟩ := hT
  obtain ⟨L, hLderiv, hLmeas, hLbdd⟩ :=
    Submission.lpf_tangential_differential_exists P Q n U M θ ξ f hU hMθξ hf
  obtain ⟨S, hS⟩ := Submission.lpf_pushforward_is_current P Q n U V hU hV T M θ ξ f L hMθξ hTrep
    hf.continuousOn hproper hLmeas hLbdd
  exact ⟨S, ⟨M, θ, ξ, L, hMθξ, hTrep, hLderiv, hS⟩,
    Submission.lpf_pushforward_integrality P Q n U V hU hV T M θ ξ f L S hMθξ hθ hTrep hf hfUV
      hproper hLderiv hLmeas hS⟩
```

It names the accepted declarations `lpf_tangential_differential_exists` (L45694),
`lpf_pushforward_is_current` (L46182) and `lpf_pushforward_integrality` (L45407), and no root
child. The witness of `IsLipschitzPushforward T f S` is the tuple
`⟨M, θ, ξ, L, hMθξ, hTrep, hLderiv, hS⟩`, whose entries come from hypothesis 1 (`M, θ, ξ, hMθξ,
hTrep`), from the output of `lpf_tangential_differential_exists` (`L, hLderiv`) and from the output
of `lpf_pushforward_is_current` (`hS`).

### 3.4 `FedererFlemingCompactness` (Simon, Theorem 3.11) — `federer_fleming_compactness`

Frozen proposition (`Contract.lean:234–239`, `Submission.lean:241–246`):

```lean
def FedererFlemingCompactness : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U (m + 1),
    (∀ j, IsIntegerMultiplicity (T j)) →
    (∀ W, CompactlyContainedOpen W U → (⨆ j, ((T j).massOn W + (T j).boundary.massOn W)) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U (m + 1)), StrictMono φ ∧
      IsIntegerMultiplicity T₀ ∧ WeaklyConvergesOn (fun j => T (φ j)) T₀
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open, and let `(T_j)_{j∈ℕ}` be a sequence in
`𝒟_{m+1}(U)`.

- Hypotheses:
  1. every `T_j` is integer multiplicity;
  2. for every `W ⊂⊂ U`, `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞`.
- Conclusion: there are `φ : ℕ → ℕ` and `T₀ ∈ 𝒟_{m+1}(U)` such that `φ` is strictly increasing,
  `T₀` is integer multiplicity, and `T_{φ(j)} ⇀ T₀`.

**Proof.** The accepted theorem `Submission.federer_fleming_compactness`
(`Submission.lean:69482–69497`; node `root.federer_fleming-a1`, issue #342, PR #8802, candidate
`5abeab04`). Its Lean proof:

```lean
theorem Submission.federer_fleming_compactness : FedererFlemingCompactness := by
  intro P m U hU T hT hB
  obtain ⟨φ, T₀, hφ, hconv, -⟩ := Submission.compactness_under_mass_bounds P (m + 1) U hU T
    fun W hW => (hB W hW).trans_le' (iSup_mono fun j => le_self_add)
  have hI : ∀ j, IsIntegralCurrent (T j) := fun j =>
    ⟨hT j, Submission.boundary_rectifiability P m U hU (T j) (hT j) fun W hW =>
      (hB W hW).trans_le' (le_add_self.trans
        (le_iSup (fun j => (T j).massOn W + (T j).boundary.massOn W) j))⟩
  exact ⟨φ, T₀, hφ, Submission.integrality_of_weak_limits P m U hU (fun j => T (φ j)) T₀
    (fun j => hI (φ j))
    (fun W hW => (hB W hW).trans_le'
      (iSup_comp_le (fun j => (T j).massOn W + (T j).boundary.massOn W) φ))
    hconv, hconv⟩
```

It names no accepted declaration other than three root children, whose exact statements are §3.1,
§3.9 and §3.12, so the argument can be read off completely. For `W ⊂⊂ U` write
`B_W = sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` (hypothesis 2); all masses lie in `[0, ∞]`.

1. For every `j`, `M_W(T_j) ≤ M_W(T_j) + M_W(∂T_j)`, so `sup_j M_W(T_j) ≤ B_W < ∞`. This is the
   hypothesis of §3.1 for the sequence `(T_j)` (with `n = m + 1`). §3.1 gives a strictly
   increasing `φ` and `T₀ ∈ 𝒟_{m+1}(U)` with `T_{φ(j)} ⇀ T₀` (its conclusion 3 is not used).
2. For every `j` and every `W ⊂⊂ U`, `M_W(∂T_j) ≤ M_W(T_j) + M_W(∂T_j) ≤ B_W < ∞`. With hypothesis 1
   for `T_j`, these are the hypotheses of §3.9 for `T_j`, which gives that `∂T_j` is integer
   multiplicity. So every `T_j` is an integral current.
3. For every `W ⊂⊂ U`, `sup_j (M_W(T_{φ(j)}) + M_W(∂T_{φ(j)})) ≤ B_W < ∞`, a supremum over a
   subfamily. With step 2 for the `T_{φ(j)}` and `T_{φ(j)} ⇀ T₀` from step 1, these are the
   hypotheses of §3.12 for the sequence `(T_{φ(j)})` and `T₀`, which gives that `T₀` is integer
   multiplicity.
4. So `φ`, `T₀` satisfy the conclusion. ∎

### 3.5 `SlicingTheorem` (Simon, §4, 4.4–4.10) — `slicing_theorem`

Frozen proposition (`Contract.lean:250–263`, `Submission.lean:257–270`):

```lean
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
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open and let `T ∈ 𝒟_{m+1}(U)`.

- Hypothesis on `T`: for every `W ⊂⊂ U`, `M_W(T) < ∞` and `M_W(∂T) < ∞`.
- Then, for every `f : ℝ^P → ℝ` and every `L ∈ ℝ≥0` such that `f` is `L`-Lipschitz on `U`
  (`LipschitzOnWith L f U`), there is a family `S : ℝ → 𝒟_m(U)` such that:
  1. for every `t ∈ ℝ`, `S(t)` is a slice of `T` by `f` at `t` (`IsSlice T f t (S t)`);
  2. for every `t ∈ ℝ`, `spt S(t) ⊆ spt T ∩ {x : f(x) = t}`;
  3. if `T` is integer multiplicity, then `S(t)` is integer multiplicity for `L¹`-almost every
     `t ∈ ℝ`;
  4. for every open `W ⊆ U`, every `L_W ∈ ℝ≥0` such that, for Lebesgue-almost every `x ∈ ℝ^P`,
     `x ∈ W` implies `‖fderiv ℝ f x‖₊ ≤ L_W`, all real `a < b`, and every `R ∈ 𝒟_{m+1}(U)` that is
     a restriction of `T` to `{x ∈ U : a < f(x) < b}`, there is a measurable `g : ℝ → [0, ∞]` with
     `M_W(S(t)) ≤ g(t)` for every `t ∈ (a, b)` and `∫⁻_{(a,b)} g dL¹ ≤ L_W · M_W(R)`.

**Proof.** The accepted theorem `Submission.slicing_theorem` (`Submission.lean:66972–66980`;
node `root.slicing-a1`, issue #322, PR #5777, candidate `f27fd6da`). Its Lean proof:

```lean
theorem Submission.slicing_theorem : SlicingTheorem := by
  intro P m U hU T hT f L hf
  choose S hS using Submission.slicing_exists P m U hU T hT f L hf
  refine ⟨S, hS, fun t => Submission.slicing_support_subset P m U hU T f L hf t (S t) (hS t),
    fun hIM => ?_, Submission.slicing_mass_bound P m U hU T hT f L hf S hS⟩
  filter_upwards [Submission.slicing_integer_multiplicity_ae P m U hU T hT f L hf hIM] with t ht
  exact ht (S t) (hS t)
```

It names the accepted declarations `slicing_exists` (L22959), `slicing_support_subset` (L22986),
`slicing_mass_bound` (L23080) and `slicing_integer_multiplicity_ae` (L66941), and no root child.
`choose` (which uses the axiom of choice) turns the output of `slicing_exists` into a family `S`
with property `hS`. The components of the anonymous constructor are, in order, `S`, conclusion 1
(`hS`), conclusion 2 (from `slicing_support_subset` at each `t`), conclusion 3 (from
`slicing_integer_multiplicity_ae`, specialized by `filter_upwards` to `S t` and `hS t`) and
conclusion 4 (from `slicing_mass_bound` applied to `S` and `hS`).

### 3.6 `DeformationTheorem` (Simon, 5.3; 5.1 is `ρ = 1`) — `deformation_theorem`

Frozen proposition (`Contract.lean:274–291`, `Submission.lean:281–298`):

```lean
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
```

**Statement.** Let `m, ℓ ∈ ℕ` with `1 ≤ ℓ`, and write `d = m + 1 + ℓ`. All currents below are
currents in `U = ℝ^d` (`univ`). There is `C ∈ ℝ≥0` with the following property. For every
`T ∈ 𝒟_{m+1}(ℝ^d)` with `M(T) + M(∂T) < ∞` and every real `ρ > 0` there are
`Pc ∈ 𝒟_{m+1}(ℝ^d)`, `β : LatticeFaceIndex (m+1) d → ℝ`, `R ∈ 𝒟_{m+2}(ℝ^d)` and
`S ∈ 𝒟_{m+1}(ℝ^d)` such that

1. `IsLatticeChain ρ β Pc`;
2. `T(ω) − Pc(ω) = ∂R(ω) + S(ω)` for every `ω ∈ 𝒟^{m+1}(ℝ^d)`;
3. `M(Pc) ≤ C · M(T)`;
4. `M(∂Pc) ≤ C · M(∂T)`;
5. `M(R) ≤ C · ρ · M(T)`;
6. `M(S) ≤ C · ρ · M(∂T)`;
7. `spt Pc ∪ spt R ⊆ thickening (2√d · ρ) (spt T)`;
8. `spt ∂Pc ∪ spt S ⊆ thickening (2√d · ρ) (spt ∂T)`;
9. if `T` is integer multiplicity, then every `β(F)` is an integer, and `Pc` and `R` are integer
   multiplicity;
10. if `T` and `∂T` are integer multiplicity, then `S` is integer multiplicity.

(Inequalities 3–6 are in `[0, ∞]`, with `C` and `ρ` read as `(C : ℝ≥0∞)` and `ENNReal.ofReal ρ`.)

**Proof.** The accepted theorem `Submission.deformation_theorem` (`Submission.lean:66990–67193`;
node `root.deformation-a1`, issue #325, PR #7759, candidate `4efd922c`). Its Lean proof:

```lean
theorem Submission.deformation_theorem : DeformationTheorem := by
  intro m ℓ hℓ
  obtain ⟨C₁, hC₁⟩ := Submission.deformation_onto_skeleton Submission.slicing_theorem
    Submission.lipschitz_pushforward_integer_multiplicity m ℓ hℓ
  obtain ⟨C₂, hC₂⟩ := Submission.deformation_skeleton_polyhedral m ℓ hℓ
  refine ⟨C₁ + C₁ * C₂, fun T hT ρ hρ => ?_⟩
  set sd : ℝ := Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ)
  set sn : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ)
  have hsn0 : 0 ≤ sn := Real.sqrt_nonneg _
  have hsd0 : 0 ≤ sd := Real.sqrt_nonneg _
  have hsnd : sn < sd := Real.sqrt_lt_sqrt (Nat.cast_nonneg _) (Nat.cast_lt.mpr (by omega))
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hρi : 0 < ρ⁻¹ := inv_pos.mpr hρ
  obtain ⟨-, dilI, propI, -⟩ := Submission.deformation_dilation (m + 1 + ℓ) ρ⁻¹ hρi (m + 1)
  obtain ⟨-, -, propIb, bdI⟩ := Submission.deformation_dilation (m + 1 + ℓ) ρ⁻¹ hρi m
  obtain ⟨pull, dil, prop, bdR⟩ := Submission.deformation_dilation (m + 1 + ℓ) ρ hρ (m + 1)
  obtain ⟨-, -, propb, bd⟩ := Submission.deformation_dilation (m + 1 + ℓ) ρ hρ m
  obtain ⟨-, dilR, propR, -⟩ := Submission.deformation_dilation (m + 1 + ℓ) ρ hρ (m + 2)
  obtain ⟨T', hT'⟩ := dilI T
  have hbT' := bdI T T' hT'
  obtain ⟨hT'm, hT's, hT'im, -⟩ := propI T T' hT'
  obtain ⟨hbT'm, hbT's, hbT'im, -⟩ := propIb T.boundary T'.boundary hbT'
  obtain ⟨hTm, hTbm⟩ := ENNReal.add_lt_top.mp hT
  have hT'fin : T'.mass + T'.boundary.mass < ∞ := by
    rw [hT'm, hbT'm]
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hTm, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hTbm⟩
  obtain ⟨Q, R₁, S₁, hTQ, hQskel, hQface, hQm, hQbm, hR₁m, hS₁m, hQR₁s, hQbS₁s, hIM₁, hIM₂⟩ :=
    hC₁ T' hT'fin
  have hQfin : Q.mass + Q.boundary.mass < ∞ :=
    ENNReal.add_lt_top.mpr
      ⟨hQm.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mp hT'fin).1),
        hQbm.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mp hT'fin).2)⟩
  obtain ⟨β, P, S', hPβ, hQP, hPm, hPbm, hS'm, hPs, hPbS's, hIMP⟩ := hC₂ Q hQfin hQskel hQface
  obtain ⟨S'', hS''⟩ : ∃ S'' : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1),
      ∀ ω, S'' ω = S₁ ω + S' ω :=
    ⟨⟨S₁.toCurrent + S'.toCurrent, fun seq hseq => by
      simpa using (S₁.continuous' seq hseq).add (S'.continuous' seq hseq)⟩, fun _ => rfl⟩
  have hS''m : S''.mass ≤ S₁.mass + S'.mass := by
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    simp only [hS'']
    exact ENNReal.ofReal_add_le.trans (add_le_add (S₁.le_massOn hω) (S'.le_massOn hω))
  have hS''s : S''.support ⊆ S₁.support ∪ S'.support := by
    rintro x ⟨-, hx⟩
    by_contra hx'
    rw [mem_union, not_or] at hx'
    have h₁ : x ∈ S₁.zeroRegion := by_contra fun h => hx'.1 ⟨mem_univ x, h⟩
    have h₂ : x ∈ S'.zeroRegion := by_contra fun h => hx'.2 ⟨mem_univ x, h⟩
    obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁⟩, hxW₁⟩ := h₁
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂⟩, hxW₂⟩ := h₂
    refine hx (mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
      hW₁c.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left),
      subset_univ _, fun ω hω => ?_⟩, hxW₁, hxW₂⟩)
    rw [hS'', hW₁ ω (hω.trans inter_subset_left), hW₂ ω (hω.trans inter_subset_right), add_zero]
  obtain ⟨Pc, hPc⟩ := dil P
  obtain ⟨S, hS⟩ := dil S''
  obtain ⟨R, hR⟩ := dilR R₁
  have hbPc := bd P Pc hPc
  have hbR := bdR R₁ R hR
  obtain ⟨hPcm, hPcs, hPcim, hPcβ⟩ := prop P Pc hPc
  obtain ⟨hbPcm, hbPcs, -, -⟩ := propb P.boundary Pc.boundary hbPc
  obtain ⟨hSm, hSs, hSim, -⟩ := prop S'' S hS
  obtain ⟨hRm, hRs, hRim, -⟩ := propR R₁ R hR
  have hC12 : (C₁ : ℝ≥0∞) * C₂ ≤ ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_mul]
    exact le_add_self
  have hC1 : (C₁ : ℝ≥0∞) ≤ ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_add]
    exact le_self_add
  have hcancel : ∀ k : ℕ, ENNReal.ofReal (ρ ^ k) * ENNReal.ofReal (ρ⁻¹ ^ k) = 1 := by
    intro k
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ hρ0, one_pow,
      ENNReal.ofReal_one]
  have hpow1 : ENNReal.ofReal (ρ ^ (m + 1)) = ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ m) := by
    rw [← ENNReal.ofReal_mul hρ.le, pow_succ']
  have hpow2 : ENNReal.ofReal (ρ ^ (m + 2)) = ENNReal.ofReal ρ * ENNReal.ofReal (ρ ^ (m + 1)) := by
    rw [← ENNReal.ofReal_mul hρ.le]
    congr 1
    ring
  have hscale : ∀ A B : Set (Eucl (m + 1 + ℓ)),
      B ⊆ cthickening (sn + sd) ((fun x => ρ⁻¹ • x) '' A) →
        (fun x => ρ • x) '' B ⊆ thickening (2 * sd * ρ) A := by
    intro A B hB
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ thickening (2 * sd) ((fun x => ρ⁻¹ • x) '' A) :=
      cthickening_subset_thickening' (by linarith) (by linarith) _ (hB hy)
    obtain ⟨_, ⟨a, ha, rfl⟩, hya⟩ := mem_thickening_iff.mp hy'
    refine mem_thickening_iff.mpr ⟨a, ha, ?_⟩
    calc dist (ρ • y) a = dist (ρ • y) (ρ • ρ⁻¹ • a) := by
          rw [smul_smul, mul_inv_cancel₀ hρ0, one_smul]
      _ = ρ * dist y (ρ⁻¹ • a) := by rw [dist_smul₀, Real.norm_of_nonneg hρ.le]
      _ < ρ * (2 * sd) := mul_lt_mul_of_pos_left hya hρ
      _ = 2 * sd * ρ := by ring
  have hcc : ∀ A B : Set (Eucl (m + 1 + ℓ)), B ⊆ cthickening sd A →
      cthickening sn B ⊆ cthickening (sn + sd) A := fun A B h =>
    (cthickening_subset_of_subset sn h).trans (cthickening_cthickening_subset hsn0 hsd0 A)
  have hc1 : ∀ A : Set (Eucl (m + 1 + ℓ)), cthickening sd A ⊆ cthickening (sn + sd) A :=
    fun A => cthickening_mono (le_add_of_nonneg_left hsn0) A
  have hQs : Q.support ⊆ cthickening sd T'.support := subset_union_left.trans hQR₁s
  have hR₁s : R₁.support ⊆ cthickening sd T'.support := subset_union_right.trans hQR₁s
  have hQbs : Q.boundary.support ⊆ cthickening sd T'.boundary.support :=
    subset_union_left.trans hQbS₁s
  have hS₁s : S₁.support ⊆ cthickening sd T'.boundary.support := subset_union_right.trans hQbS₁s
  have hPbs : P.boundary.support ⊆ cthickening sn Q.boundary.support :=
    subset_union_left.trans hPbS's
  have hS's : S'.support ⊆ cthickening sn Q.boundary.support := subset_union_right.trans hPbS's
  refine ⟨Pc, β, R, S, hPcβ β hPβ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ω
    obtain ⟨η, hη⟩ := pull ω
    have hηω : ∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x =
        ρ⁻¹ ^ (m + 1) • (η : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) (ρ⁻¹ • x) := by
      intro x
      rw [hη]
      simp only [smul_smul, ← mul_pow, inv_mul_cancel₀ hρ0, mul_inv_cancel₀ hρ0, one_pow,
        one_smul]
    rw [(hT' η ω hηω).symm, hPc ω η hη, hbR ω η hη, hS ω η hη, hS'']
    linarith [hTQ η, hQP η]
  · calc Pc.mass = ENNReal.ofReal (ρ ^ (m + 1)) * P.mass := hPcm
      _ ≤ ENNReal.ofReal (ρ ^ (m + 1)) * (C₂ * (C₁ * T'.mass)) := by
          gcongr
          exact hPm.trans (by gcongr)
      _ = (C₁ : ℝ≥0∞) * C₂ * (ENNReal.ofReal (ρ ^ (m + 1)) * ENNReal.ofReal (ρ⁻¹ ^ (m + 1))) *
          T.mass := by
          rw [hT'm]
          ring
      _ = (C₁ : ℝ≥0∞) * C₂ * T.mass := by rw [hcancel, mul_one]
      _ ≤ ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) * T.mass := mul_le_mul_left hC12 _
  · calc Pc.boundary.mass = ENNReal.ofReal (ρ ^ m) * P.boundary.mass := hbPcm
      _ ≤ ENNReal.ofReal (ρ ^ m) * (C₂ * (C₁ * T'.boundary.mass)) := by
          gcongr
          exact hPbm.trans (by gcongr)
      _ = (C₁ : ℝ≥0∞) * C₂ * (ENNReal.ofReal (ρ ^ m) * ENNReal.ofReal (ρ⁻¹ ^ m)) *
          T.boundary.mass := by
          rw [hbT'm]
          ring
      _ = (C₁ : ℝ≥0∞) * C₂ * T.boundary.mass := by rw [hcancel, mul_one]
      _ ≤ ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) * T.boundary.mass := mul_le_mul_left hC12 _
  · calc R.mass = ENNReal.ofReal (ρ ^ (m + 2)) * R₁.mass := hRm
      _ ≤ ENNReal.ofReal (ρ ^ (m + 2)) * (C₁ * T'.mass) := by gcongr
      _ = (C₁ : ℝ≥0∞) * ENNReal.ofReal ρ *
          (ENNReal.ofReal (ρ ^ (m + 1)) * ENNReal.ofReal (ρ⁻¹ ^ (m + 1))) * T.mass := by
          rw [hT'm, hpow2]
          ring
      _ = (C₁ : ℝ≥0∞) * ENNReal.ofReal ρ * T.mass := by rw [hcancel, mul_one]
      _ ≤ ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ρ * T.mass :=
          mul_le_mul_left (mul_le_mul_left hC1 _) _
  · calc S.mass = ENNReal.ofReal (ρ ^ (m + 1)) * S''.mass := hSm
      _ ≤ ENNReal.ofReal (ρ ^ (m + 1)) *
          (C₁ * T'.boundary.mass + C₂ * (C₁ * T'.boundary.mass)) := by
          gcongr
          calc S''.mass ≤ S₁.mass + S'.mass := hS''m
            _ ≤ C₁ * T'.boundary.mass + C₂ * Q.boundary.mass := add_le_add hS₁m hS'm
            _ ≤ C₁ * T'.boundary.mass + C₂ * (C₁ * T'.boundary.mass) := by gcongr
      _ = ((C₁ : ℝ≥0∞) + C₁ * C₂) * ENNReal.ofReal ρ *
          (ENNReal.ofReal (ρ ^ m) * ENNReal.ofReal (ρ⁻¹ ^ m)) * T.boundary.mass := by
          rw [hbT'm, hpow1]
          ring
      _ = ((C₁ + C₁ * C₂ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ρ * T.boundary.mass := by
          rw [hcancel, mul_one, ENNReal.coe_add, ENNReal.coe_mul]
  · rw [hPcs, hRs]
    refine union_subset (hscale _ _ ?_) (hscale _ _ ?_)
    · rw [← hT's]
      exact hPs.trans (hcc _ _ hQs)
    · rw [← hT's]
      exact hR₁s.trans (hc1 _)
  · rw [hbPcs, hSs]
    refine union_subset (hscale _ _ ?_) (hscale _ _ ?_)
    · rw [← hbT's]
      exact hPbs.trans (hcc _ _ hQbs)
    · rw [← hbT's]
      exact hS''s.trans (union_subset (hS₁s.trans (hc1 _)) (hS's.trans (hcc _ _ hQbs)))
  · intro hTim
    obtain ⟨hQim, hR₁im⟩ := hIM₁ (hT'im hTim)
    obtain ⟨hβ, hPim⟩ := hIMP hQim
    exact ⟨hβ, hPcim hPim, hRim hR₁im⟩
  · intro hTim hTbim
    have hT'im' := hT'im hTim
    have hS₁im := hIM₂ hT'im' (hbT'im hTbim)
    have hQim := (hIM₁ hT'im').1
    have hPim := (hIMP hQim).2
    have hS'im : IsIntegerMultiplicity S' :=
      Submission.deformation_im_combination _ _ Q P S' 1 (-1) hQim hPim fun ω => by
        rw [← hQP ω]
        push_cast
        ring
    have hS''im : IsIntegerMultiplicity S'' :=
      Submission.deformation_im_combination _ _ S₁ S' S'' 1 1 hS₁im hS'im fun ω => by
        rw [hS'']
        push_cast
        ring
    exact hSim hS''im
```

It names the accepted declarations `deformation_onto_skeleton` (L47900),
`deformation_skeleton_polyhedral` (L49061), `deformation_dilation` (L66406) and
`deformation_im_combination` (L65922), and two root children, which are the first two arguments of
`deformation_onto_skeleton`: `Submission.slicing_theorem` (§3.5) and
`Submission.lipschitz_pushforward_integer_multiplicity` (§3.3). The constant of the conclusion is
`C = C₁ + C₁ · C₂`, where `C₁` and `C₂` are the first components of the outputs of
`deformation_onto_skeleton` and `deformation_skeleton_polyhedral`.

### 3.7 `IsoperimetricTheorem` (Simon, 6.1) — `isoperimetric_theorem`

Frozen proposition (`Contract.lean:297–302`, `Submission.lean:304–309`):

```lean
def IsoperimetricTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 1),
    IsIntegerMultiplicity T → IsCompact T.support → T.boundary = 0 →
    ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
      R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ c * T.mass
```

**Statement.** Let `m, ℓ ∈ ℕ` with `1 ≤ ℓ`; currents are in `U = ℝ^{m+2+ℓ}` (`univ`). There is
`c ∈ ℝ≥0` such that for every `T ∈ 𝒟_{m+1}(ℝ^{m+2+ℓ})`:

- Hypotheses: `T` is integer multiplicity; `spt T` is compact; `∂T = 0`.
- Conclusion: there is `R ∈ 𝒟_{m+2}(ℝ^{m+2+ℓ})` such that `R` is integer multiplicity, `spt R` is
  compact, `∂R = T`, and `M(R)^{(m+1)/(m+2)} ≤ c · M(T)` in `[0, ∞]`, where the power is the real
  power on `[0, ∞]` (`ENNReal.rpow`) with exponent `(m+1)/(m+2)` and `c` is read as `(c : ℝ≥0∞)`.

**Proof.** The accepted theorem `Submission.isoperimetric_theorem` (`Submission.lean:67200–67286`;
node `root.isoperimetric-a1`, issue #329, PR #8118, candidate `2e7a66f2`). Its Lean proof:

```lean
theorem Submission.isoperimetric_theorem : IsoperimetricTheorem := by
  intro m ℓ hℓ
  obtain ⟨C, hC⟩ := Submission.deformation_theorem m (ℓ + 1) (by omega)
  rw [show m + 1 + (ℓ + 1) = m + 2 + ℓ by omega] at hC
  refine ⟨2 * (C + 1), fun T hT hTc hTb => ?_⟩
  have hTM : T.mass < ∞ := Submission.isoperimetric_mass_lt_top _ _ T hT hTc
  have hTbM : T.boundary.mass = 0 := (Submission.isoperimetric_mass_eq_zero_iff _ _ _ _).2 hTb
  have key : ∀ ρ : ℝ, 0 < ρ → (C : ℝ≥0∞) * T.mass < ENNReal.ofReal (ρ ^ (m + 1)) →
      ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
        R.mass ≤ (C : ℝ≥0∞) * ENNReal.ofReal ρ * T.mass := by
    intro ρ hρ hρC
    obtain ⟨Pc, β, R, S, hPc, hTPc, hPcM, -, hRM, hSM, hspt, -, hIM, -⟩ :=
      hC T (by rw [hTbM, add_zero]; exact hTM) ρ hρ
    obtain ⟨hβ, -, hR⟩ := hIM hT
    have hβ0 : ∀ F, β F = 0 := by
      intro F
      obtain ⟨k, hk⟩ := hβ F
      have hlt := ((Submission.isoperimetric_lattice_chain_mass_ge m _ ρ β Pc hρ hPc F).trans
        hPcM).trans_lt hρC
      rw [ENNReal.ofReal_lt_ofReal_iff (pow_pos hρ _)] at hlt
      have hk1 : |(k : ℝ)| < 1 := by
        rw [← hk]
        nlinarith [pow_pos hρ (m + 1), abs_nonneg (β F)]
      have hk0 : k = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast hk1)
      rw [hk, hk0, Int.cast_zero]
    have hS : S = 0 := (Submission.isoperimetric_mass_eq_zero_iff _ _ _ _).1 <| by
      simpa [hTbM] using hSM
    refine ⟨R, hR, ?_, ?_, hRM⟩
    · exact Metric.isCompact_of_isClosed_isBounded (isClosed_univ.sdiff R.isOpen_zeroRegion)
        (hTc.isBounded.thickening.subset (subset_union_right.trans hspt))
    · ext ω
      have h := hTPc ω
      rw [hPc ω, hS] at h
      simpa [hβ0] using h.symm
  by_cases hT0 : T.mass = 0
  · obtain ⟨R, hR, hRc, hRT, hRM⟩ := key 1 one_pos (by simp [hT0])
    refine ⟨R, hR, hRc, hRT, ?_⟩
    rw [show R.mass = 0 by simpa [hT0] using hRM, hT0, mul_zero,
      ENNReal.zero_rpow_of_pos (by positivity)]
  · obtain ⟨t, ht0, hTt⟩ : ∃ t : ℝ, 0 < t ∧ T.mass = ENNReal.ofReal t :=
      ⟨T.mass.toReal, ENNReal.toReal_pos hT0 hTM.ne, (ENNReal.ofReal_toReal hTM.ne).symm⟩
    have hC1 : (0 : ℝ) < C + 1 := by positivity
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 * (C + 1) * t) ^ ((m + 1 : ℕ) : ℝ)⁻¹ := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by
      rw [hρ]
      exact Real.rpow_pos_of_pos (by positivity) _
    have hρk : ρ ^ (m + 1) = 2 * (C + 1) * t := by
      rw [hρ]
      exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
    have hCT : (C : ℝ≥0∞) * T.mass ≤ ENNReal.ofReal ((C + 1) * t) := by
      rw [hTt, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    obtain ⟨R, hR, hRc, hRT, hRM⟩ := key ρ hρ0 <| hCT.trans_lt <| by
      rw [ENNReal.ofReal_lt_ofReal_iff (pow_pos hρ0 _), hρk]
      nlinarith [mul_pos hC1 ht0]
    refine ⟨R, hR, hRc, hRT, ?_⟩
    have hRρ : R.mass ≤ ENNReal.ofReal (ρ ^ (m + 2)) := by
      calc R.mass ≤ (C : ℝ≥0∞) * ENNReal.ofReal ρ * T.mass := hRM
        _ = ENNReal.ofReal ρ * ((C : ℝ≥0∞) * T.mass) := by ring
        _ ≤ ENNReal.ofReal ρ * ENNReal.ofReal ((C + 1) * t) := by gcongr
        _ = ENNReal.ofReal (ρ * ((C + 1) * t)) := (ENNReal.ofReal_mul hρ0.le).symm
        _ ≤ ENNReal.ofReal (ρ ^ (m + 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show ρ ^ (m + 2) = ρ ^ (m + 1) * ρ from pow_succ ρ (m + 1), hρk]
          nlinarith [mul_pos (mul_pos hρ0 hC1) ht0]
    calc R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ))
        ≤ ENNReal.ofReal (ρ ^ (m + 2)) ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) :=
          ENNReal.rpow_le_rpow hRρ (by positivity)
      _ = ENNReal.ofReal (ρ ^ (m + 1)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (pow_pos hρ0 _).le (by positivity),
            ← Real.rpow_natCast ρ (m + 2), ← Real.rpow_mul hρ0.le, ← Real.rpow_natCast ρ (m + 1),
            ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]
      _ = ((2 * (C + 1) : ℝ≥0) : ℝ≥0∞) * T.mass := by
          rw [hρk, hTt, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          push_cast
          ring_nf
```

It names the accepted declarations `isoperimetric_mass_lt_top` (L2450),
`isoperimetric_mass_eq_zero_iff` (L7542) and `isoperimetric_lattice_chain_mass_ge` (L9544), and one
root child: `Submission.deformation_theorem` (§3.6), applied with the parameters `m` and `ℓ + 1`;
the dimension of its ambient space is then rewritten by `m + 1 + (ℓ + 1) = m + 2 + ℓ`. With `C` the
first component of that output, the constant of the conclusion is `c = 2 · (C + 1)`.

### 3.8 `PolyhedralApproximation` (Simon, 6.2) — `polyhedral_approximation`

Frozen proposition (`Contract.lean:308–316`, `Submission.lean:315–323`):

```lean
def PolyhedralApproximation : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ U : Set (Eucl (m + 1 + ℓ)), IsOpen U →
    ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ)
        (Pk : ℕ → GeometricCurrentOn U (m + 1)),
        (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧
        WeaklyConvergesOn Pk T
```

**Statement.** Let `m, ℓ ∈ ℕ` with `1 ≤ ℓ`, let `U ⊆ ℝ^{m+1+ℓ}` be open, and let `T ∈ 𝒟_{m+1}(U)`.

- Hypotheses: `T` is integer multiplicity; for every `W ⊂⊂ U`, `M_W(T) < ∞` and `M_W(∂T) < ∞`.
- Conclusion: there are `ρ : ℕ → ℝ`, `β : ℕ → LatticeFaceIndex (m+1) (m+1+ℓ) → ℤ` and
  `P_k ∈ 𝒟_{m+1}(U)` (`k ∈ ℕ`) such that `ρ_k > 0` for every `k`, `ρ` is antitone
  (non-increasing), `ρ_k → 0`, `IsLatticeChain ρ_k (F ↦ (β_k(F) : ℝ)) P_k` for every `k`, and
  `P_k ⇀ T`.

**Proof.** The accepted theorem `Submission.polyhedral_approximation` (`Submission.lean:67293–67310`;
node `root.polyhedral_approximation-a1`, issue #331, PR #8056, candidate `786e6c8a`). Its Lean
proof:

```lean
theorem Submission.polyhedral_approximation : PolyhedralApproximation := by
  intro m ℓ hℓ U hU T hT hmass
  obtain ⟨X, hXim, hXmass, hXT⟩ := Submission.polyhedral_approx_truncation_seq
    Submission.slicing_theorem (m + 1 + ℓ) m U hU T hT hmass
  obtain ⟨ρ, β, Pc, hρ, hρa, hρ0, hPc, hconv⟩ := Submission.polyhedral_approx_finite_mass_seq
    Submission.deformation_theorem m ℓ hℓ X hXim hXmass
  refine ⟨ρ, β, fun k => (Pc k).restrictDomain (subset_univ U), hρ, hρa, hρ0,
    fun k ω => hPc k (testFormOnInclusion (subset_univ U) (m + 1) ω), fun ω => ?_⟩
  have h := (hconv (testFormOnInclusion (subset_univ U) (m + 1) ω)).add_const (T ω)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [hXT ω] with k hk
  rw [hk, sub_add_cancel]
  rfl
```

It names the accepted declarations `polyhedral_approx_truncation_seq` (L18213) and
`polyhedral_approx_finite_mass_seq` (L18449), and two root children: `Submission.slicing_theorem`
(§3.5), the first argument of `polyhedral_approx_truncation_seq`, and
`Submission.deformation_theorem` (§3.6), the first argument of `polyhedral_approx_finite_mass_seq`.
The currents of the conclusion are `P_k = (Pc k).restrictDomain (subset_univ U)` (SimonGMT's
`GeometricCurrentOn.restrictDomain`; test forms are transported by SimonGMT's
`testFormOnInclusion`).

### 3.9 `BoundaryRectifiability` (Simon, 6.3) — `boundary_rectifiability`

Frozen proposition (`Contract.lean:321–324`, `Submission.lean:328–331`):

```lean
def BoundaryRectifiability : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) →
    IsIntegerMultiplicity T.boundary
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open and let `T ∈ 𝒟_{m+1}(U)`.

- Hypotheses: `T` is integer multiplicity; for every `W ⊂⊂ U`, `M_W(∂T) < ∞`.
- Conclusion: `∂T` is integer multiplicity.

**Proof.** The accepted theorem `Submission.boundary_rectifiability` (`Submission.lean:68901–68922`;
node `root.boundary_rectifiability-a1`, issue #334, PR #8641, candidate `8f66d3bb`). Its Lean proof:

```lean
theorem Submission.boundary_rectifiability : BoundaryRectifiability := by
  intro P m U hU T hT hbd
  refine Submission.br_isIntegerMultiplicity_of_local P m U hU T.boundary fun x₀ hx₀ => ?_
  obtain ⟨r, hr, hrU, X, hXIM, hXmass, hXbd, hXT⟩ :=
    Submission.br_local_finite_mass_extension Submission.slicing_theorem P m U hU T hT hbd x₀ hx₀
  have hXb : IsIntegerMultiplicity X.boundary :=
    Submission.br_boundary_isIntegerMultiplicity_of_finite_mass Submission.deformation_theorem
      Submission.integrality_of_weak_limits P m X hXIM hXmass hXbd
  refine ⟨ball x₀ r, isOpen_ball, mem_ball_self hr, hrU,
    X.boundary.restrictDomain (subset_univ U),
    Submission.br_restrictDomain_isIntegerMultiplicity P m univ U (subset_univ U) hU X.boundary hXb,
    fun ω hω => ?_⟩
  have hdω : tsupport (exteriorDerivative (ω : DifferentialForm (Eucl P) m)) ⊆ ball x₀ r :=
    (tsupport_exteriorDerivative_subset _).trans hω
  calc T.boundary ω = T (exteriorDerivativeTestOn U m ω) := GeometricCurrentOn.boundary_apply T ω
    _ = X (testFormOnInclusion (subset_univ U) (m + 1) (exteriorDerivativeTestOn U m ω)) :=
        (hXT (exteriorDerivativeTestOn U m ω) hdω).symm
    _ = X.boundary.restrictDomain (subset_univ U) ω := rfl
```

It names the accepted declarations `br_isIntegerMultiplicity_of_local` (L2270),
`br_local_finite_mass_extension` (L31744), `br_boundary_isIntegerMultiplicity_of_finite_mass`
(L31037) and `br_restrictDomain_isIntegerMultiplicity` (L2230), and three root children:
`Submission.slicing_theorem` (§3.5), the first argument of `br_local_finite_mass_extension`, and
`Submission.deformation_theorem` (§3.6) and `Submission.integrality_of_weak_limits` (§3.12), the
first two arguments of `br_boundary_isIntegerMultiplicity_of_finite_mass`.

### 3.10 `FlatConvergenceIffWeakConvergence` (Simon, Theorem 7.2) — `flat_convergence_iff_weak_convergence`

Frozen proposition (`Contract.lean:329–337`, `Submission.lean:336–344`):

```lean
def FlatConvergenceIffWeakConvergence : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      (WeaklyConvergesOn Tj T ↔
        ∀ W, CompactlyContainedOpen W U →
          Tendsto (fun j => flatDistance W (Tj j) T) atTop (𝓝 0))
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open, let `T ∈ 𝒟_{m+1}(U)` and let `(T_j)_{j∈ℕ}`
be a sequence in `𝒟_{m+1}(U)`.

- Hypotheses: `T` is integer multiplicity; every `T_j` is integer multiplicity; for every
  `W ⊂⊂ U`, `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞`.
- Conclusion: `T_j ⇀ T` if and only if, for every `W ⊂⊂ U`, `d_W(T_j, T) → 0` in `[0, ∞]` as
  `j → ∞`.

**Proof.** The accepted theorem `Submission.flat_convergence_iff_weak_convergence`
(`Submission.lean:69448–69477`; node `root.flat_iff_weak-a1`, issue #338, PR #8796, candidate
`7c119a55`). Its Lean proof:

```lean
theorem Submission.flat_convergence_iff_weak_convergence : FlatConvergenceIffWeakConvergence := by
  intro P m U hU T Tj hT hTj hbound
  refine ⟨fun hweak W hW => ?_, Submission.fiw_flat_to_weak P (m + 1) U hU T Tj⟩
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ψ, K, B, T', T'j, -, hK, hKU, hB, hT'j, hT'jb, hT'js, hT'jm, hT'w, hd⟩ :=
    Submission.fiw_localization Submission.slicing_theorem Submission.boundary_rectifiability
      P m U hU T (fun j => Tj (ns j)) hT (fun j => hTj (ns j))
      (fun V hV => (iSup_comp_le (fun j => (Tj j).massOn V + (Tj j).boundary.massOn V) ns).trans_lt
        (hbound V hV))
      (fun ω => (hweak ω).comp hns) W hW
  obtain ⟨φ, -, hφ⟩ := Submission.fiw_flat_cauchy_limit P (m + 1) U hU T'j T'
    (Submission.fiw_total_boundedness Submission.deformation_theorem P m U hU K hK hKU B hB T'j
      hT'j hT'jb hT'js hT'jm) hT'w
  refine ⟨fun ℓ => ψ (φ ℓ), ?_⟩
  have hWU : W ⊆ U := subset_closure.trans hW.2.2
  have hle : ∀ ℓ, flatDistance W (Tj (ns (ψ (φ ℓ)))) T ≤ 2 * 2⁻¹ ^ ℓ := fun ℓ => by
    obtain ⟨R, S, hR, hS, hRS, hRSm⟩ := hφ ℓ
    calc flatDistance W (Tj (ns (ψ (φ ℓ)))) T ≤ S.massOn W + R.massOn W := hd (φ ℓ) R S hR hS hRS
      _ ≤ S.mass + R.mass := add_le_add (S.massOn_mono hWU) (R.massOn_mono hWU)
      _ = R.mass + S.mass := add_comm _ _
      _ ≤ 2 * 2⁻¹ ^ ℓ := hRSm
  have hlim : Tendsto (fun ℓ : ℕ => (2 : ℝ≥0∞) * 2⁻¹ ^ ℓ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := 2)
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one)
      (Or.inr ENNReal.ofNat_ne_top)
    rwa [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hle
```

It names the accepted declarations `fiw_flat_to_weak` (L15470), `fiw_localization` (L64437),
`fiw_total_boundedness` (L69407) and `fiw_flat_cauchy_limit` (L65704), and three root children:
`Submission.slicing_theorem` (§3.5) and `Submission.boundary_rectifiability` (§3.9), the first two
arguments of `fiw_localization`, and `Submission.deformation_theorem` (§3.6), the first argument of
`fiw_total_boundedness`. The second component of the `↔` (from flat to weak convergence) is
`Submission.fiw_flat_to_weak P (m + 1) U hU T Tj`. For the first component the code uses the
subsequence criterion `tendsto_of_subseq_tendsto` (Mathlib's `Filter.tendsto_of_subseq_tendsto`).

### 3.11 `RectifiabilityTheorem` (Simon, 8.1) — `rectifiability_theorem`

Frozen proposition (`Contract.lean:342–347`, `Submission.lean:349–354`):

```lean
def RectifiabilityTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
    (∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧
      ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) →
    IsRectifiableCurrent T
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open and let `T ∈ 𝒟_{m+1}(U)`.

- Hypotheses:
  1. for every `W ⊂⊂ U`, `M_W(T) + M_W(∂T) < ∞`;
  2. there is a measure `μ` on `ℝ^P` that is a mass measure of `T` (`IsMassMeasure T μ`) and
     satisfies `Θ*^{m+1}(μ, x) > 0` for `μ`-almost every `x`.
- Conclusion: `T` is rectifiable (`IsRectifiableCurrent T`).

**Proof.** The accepted theorem `Submission.rectifiability_theorem` (`Submission.lean:62437–62461`;
node `root.rectifiability-a1`, issue #340, PR #5445, candidate `ba8a5544`). Its Lean proof:

```lean
theorem Submission.rectifiability_theorem : RectifiabilityTheorem := by
  intro P m U hU T hT ⟨μ, hμ, hdens⟩
  obtain ⟨M, θ, hMU, hM, hMrect, hθm, hθpos, hθint, rfl⟩ :=
    Submission.rectifiability_mass_measure_rectifiable P m U hU T hT μ hμ hdens
  obtain ⟨ξ, hξm, hξ1, hrep⟩ :=
    (Submission.rectifiability_mass_measure_representation P (m + 1) U hU T fun W hW =>
      (hT W hW).trans_le' le_self_add).2 _ hμ
  have hτ : ∀ ω : TestFormOn U (m + 1), T ω = tauAction (m + 1) M θ ξ ω := fun ω => by
    rw [(hrep ω).2, integral_withDensity_eq_integral_toReal_smul hθm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), tauAction]
    exact setIntegral_congr_fun hM fun x hx => by
      rw [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
  have hξ1' : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
      ∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) α) ^ 2 = 1 := by
    filter_upwards [(ae_withDensity_iff hθm.ennreal_ofReal).1 hξ1, ae_restrict_mem hM]
      with x hx hxM
    exact hx (ENNReal.ofReal_pos.2 (hθpos x hxM)).ne'
  exact ⟨M, θ, ξ, ⟨hMU, hM.nullMeasurableSet, hMrect, hθpos, hθint, hξm.aestronglyMeasurable,
    Submission.rectifiability_orientation P m U hU T (fun W hW => (hT W hW).trans_le' le_add_self)
      M θ ξ hMU hM.nullMeasurableSet hMrect hθpos hθint hξm.aestronglyMeasurable hξ1' hτ⟩, hτ⟩
```

It names the accepted declarations `rectifiability_mass_measure_rectifiable` (L62354),
`rectifiability_mass_measure_representation` (L18946) and `rectifiability_orientation` (L38735),
and no root child.

### 3.12 `IntegralityOfWeakLimits` (Simon, Theorem 8.2) — `integrality_of_weak_limits`

Frozen proposition (`Contract.lean:352–358`, `Submission.lean:359–365`):

```lean
def IntegralityOfWeakLimits : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
      (∀ j, IsIntegralCurrent (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      WeaklyConvergesOn Tj T → IsIntegerMultiplicity T
```

**Statement.** Let `P, m ∈ ℕ`, let `U ⊆ ℝ^P` be open, let `(T_j)_{j∈ℕ}` be a sequence in
`𝒟_{m+1}(U)` and let `T ∈ 𝒟_{m+1}(U)`.

- Hypotheses: every `T_j` is an integral current (`T_j` and `∂T_j` are integer multiplicity); for
  every `W ⊂⊂ U`, `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞`; `T_j ⇀ T`.
- Conclusion: `T` is integer multiplicity.

**Proof.** The accepted theorem `Submission.integrality_of_weak_limits`
(`Submission.lean:68796–68892`; node `root.integrality_weak_limits-a1`, issue #341, PR #8548,
candidate `036fb2d8`). Its Lean proof:

```lean
theorem Submission.integrality_of_weak_limits : IntegralityOfWeakLimits := by
  have hIM_of_eq_zero : ∀ {P k : ℕ} {U : Set (Eucl P)} (X : GeometricCurrentOn U k),
      (∀ ω, X ω = 0) → IsIntegerMultiplicity X := by
    intro P k U X hX
    refine ⟨∅, fun _ => 1, fun _ => 0,
      { subset := empty_subset U
        nullMeasurableSet := nullMeasurableSet_empty
        countablyRectifiable :=
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
        pos := fun x hx => absurd hx (notMem_empty x)
        integrableOn := fun K _ _ => by simp
        aestronglyMeasurable := aestronglyMeasurable_const
        orients := by simp }, fun x hx => absurd hx (notMem_empty x), fun ω => ?_⟩
    simp [tauAction, hX ω]
  have hmassOn_zero : ∀ {P k : ℕ} {U : Set (Eucl P)} (W : Set (Eucl P)),
      (0 : GeometricCurrentOn U k).massOn W = 0 := by
    intro P k U W
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨ω, -, rfl⟩
    simp
  intro P
  have step : ∀ m : ℕ,
      (∀ (Yj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1))
        (Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)),
        (∀ j, IsIntegerMultiplicity (Yj j).boundary) → (⨆ j, (Yj j).boundary.mass) < ∞ →
        WeaklyConvergesOn (fun j => (Yj j).boundary) Y.boundary →
        IsIntegerMultiplicity Y.boundary) →
      ∀ (U : Set (Eucl P)), IsOpen U →
        ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
          (∀ j, IsIntegralCurrent (Tj j)) →
          (∀ W, CompactlyContainedOpen W U →
            (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
          WeaklyConvergesOn Tj T → IsIntegerMultiplicity T := by
    intro m hBLI U hU Tj T hTj hmass hconv
    rcases lt_trichotomy P (m + 1) with hP | rfl | hP
    ·
      have hcov : ∀ c : Covector (Eucl P) (m + 1), c = 0 := by
        intro c
        ext v
        refine c.toAlternatingMap.map_linearDependent v fun hv => ?_
        have h := hv.fintype_card_le_finrank
        rw [Fintype.card_fin, finrank_euclideanSpace_fin] at h
        omega
      refine hIM_of_eq_zero T fun ω => ?_
      rw [show ω = 0 from Subtype.ext (funext fun x => hcov _)]
      exact T.toCurrent.map_zero
    ·
      exact Submission.iwl_top_dim_integrality m U hU Tj T (fun j => (hTj j).1) hmass hconv
    ·
      have hP2 : m + 2 ≤ P := by omega
      refine Submission.iwl_localization P m Submission.slicing_theorem ?_ U hU Tj T hTj hmass
        hconv
      refine Submission.iwl_cycle_reduction P m
        Submission.lipschitz_pushforward_integer_multiplicity hBLI ?_
      intro K _ Tj T hIM hbd _ hM hconv
      have hTbd : T.boundary = 0 := by
        ext ω
        refine tendsto_nhds_unique (hconv.boundary ω) ?_
        simp [hbd]
      have hTmass : ∀ W, CompactlyContainedOpen W univ →
          T.massOn W + T.boundary.massOn W < ∞ := by
        intro W _
        rw [hTbd, hmassOn_zero, add_zero]
        calc T.massOn W ≤ liminf (fun j => (Tj j).massOn W) atTop := hconv.massOn_le_liminf W
          _ ≤ ⨆ j, (Tj j).massOn W := le_trans liminf_le_limsup limsup_le_iSup
          _ ≤ ⨆ j, (Tj j).mass := iSup_mono fun j => (Tj j).massOn_mono (subset_univ W)
          _ < ∞ := hM
      have hrect : IsRectifiableCurrent T :=
        Submission.rectifiability_theorem P m univ isOpen_univ T hTmass
          (Submission.iwl_positive_density P m hP2 Submission.slicing_theorem
            Submission.isoperimetric_theorem
            Submission.lipschitz_pushforward_integer_multiplicity hBLI Tj T hIM hbd hM hconv)
      exact Submission.iwl_integer_density P m hP2 Submission.slicing_theorem
        Submission.lipschitz_pushforward_integer_multiplicity Tj T hIM hbd hM hconv hrect
  intro m
  induction m with
  | zero =>
    refine step 0 fun Yj Y hIM hM hconv => ?_
    exact Submission.iwl_zero_dim_integrality P univ isOpen_univ (fun j => (Yj j).boundary)
      Y.boundary hIM
      (fun W _ => (iSup_mono fun j => (Yj j).boundary.massOn_mono (subset_univ W)).trans_lt hM)
      hconv
  | succ m ih =>
    refine step (m + 1) fun Yj Y hIM hM hconv => ?_
    refine ih univ isOpen_univ (fun j => (Yj j).boundary) Y.boundary
      (fun j => ⟨hIM j, ?_⟩) (fun W _ => ?_) hconv
    · rw [GeometricCurrentOn.boundary_boundary]
      exact hIM_of_eq_zero _ fun _ => rfl
    · simp only [GeometricCurrentOn.boundary_boundary, hmassOn_zero, add_zero]
      exact (iSup_mono fun j => (Yj j).boundary.massOn_mono (subset_univ W)).trans_lt hM
```

It names the accepted declarations `iwl_top_dim_integrality` (L67311), `iwl_localization`
(L57577), `iwl_cycle_reduction` (L58218), `iwl_positive_density` (L58345), `iwl_integer_density`
(L68671) and `iwl_zero_dim_integrality` (L37113), and four root children. The structure of the code
is as follows.

- `hIM_of_eq_zero` shows that a current vanishing on every test form is integer multiplicity, with
  the triple `(∅, x ↦ 1, x ↦ 0)` (its countable rectifiability is SimonGMT's
  `Chapter03.countablyRectifiable_of_measure_zero`); `hmassOn_zero` shows that the zero current has
  mass `0` on every set.
- After `intro P`, the local claim `step m` is: if the boundary-limit property (BLI) holds in
  degree `m + 1`, then the conclusion holds for all open `U` and all `T_j, T ∈ 𝒟_{m+1}(U)`. Here
  (BLI) is the hypothesis written in `step`: for every sequence `Y_j ∈ 𝒟_{m+1}(ℝ^P)` and every
  `Y ∈ 𝒟_{m+1}(ℝ^P)` (currents in `univ`), if every `∂Y_j` is integer multiplicity,
  `sup_j M(∂Y_j) < ∞` and `∂Y_j ⇀ ∂Y`, then `∂Y` is integer multiplicity.
- In `step`, Mathlib's `lt_trichotomy` splits into `P < m + 1`, `P = m + 1` and `P > m + 1`. If
  `P < m + 1`, the code proves `hcov`, that every `(m+1)`-covector on `ℝ^P` is `0`, using Mathlib's
  `AlternatingMap.map_linearDependent`, `LinearIndependent.fintype_card_le_finrank` and
  `finrank_euclideanSpace_fin` and the tactic `omega`; so every test form is `0`, `T` vanishes on
  every test form, and `hIM_of_eq_zero` applies. If `P = m + 1`, the code applies `iwl_top_dim_integrality`. If
  `P > m + 1`, it applies `iwl_localization` (with the argument `Submission.slicing_theorem`, §3.5)
  and then `iwl_cycle_reduction` (with the arguments
  `Submission.lipschitz_pushforward_integer_multiplicity`, §3.3, and (BLI)). The goal that remains
  (introduced as `K _ Tj T hIM hbd _ hM hconv`) is: for every compact `K ⊆ ℝ^P` and all
  `T_j, T ∈ 𝒟_{m+1}(ℝ^P)` such that every `T_j` is integer multiplicity, `∂T_j = 0` and
  `spt T_j ⊆ K` for every `j`, `sup_j M(T_j) < ∞` and `T_j ⇀ T`, the current `T` is integer
  multiplicity. The code shows `∂T = 0` (`hTbd`, from `∂T_j = 0` and SimonGMT's
  `WeaklyConvergesOn.boundary`) and `M_W(T) + M_W(∂T) < ∞` for every `W ⊂⊂ ℝ^P` (`hTmass`, from
  `hTbd`, `hmassOn_zero`, SimonGMT's `WeaklyConvergesOn.massOn_le_liminf` and
  `GeometricCurrentOn.massOn_mono`, and the bound `hM : sup_j M(T_j) < ∞`). It then applies
  `Submission.rectifiability_theorem` (§3.11) in `U = ℝ^P` to `T`, `hTmass` and the output of
  `iwl_positive_density` (with the arguments `Submission.slicing_theorem`,
  `Submission.isoperimetric_theorem` (§3.7), `Submission.lipschitz_pushforward_integer_multiplicity`
  and (BLI)), and finally `iwl_integer_density` (with the arguments `Submission.slicing_theorem`
  and `Submission.lipschitz_pushforward_integer_multiplicity`), whose last argument is the
  resulting `hrect : IsRectifiableCurrent T`.
- After `intro m`, the code proves the claim by induction on `m`, giving (BLI) to `step` in each
  degree. For `m = 0`, (BLI) in degree `1` is `iwl_zero_dim_integrality` applied in `U = ℝ^P` to the
  `0`-currents `∂Y_j` and `∂Y`. In the step from `m` to `m + 1`, (BLI) in degree `m + 2` is the
  induction hypothesis (the claim in degree `m + 1`) applied in `U = ℝ^P` to the sequence `∂Y_j`
  and the current `∂Y`. Its hypotheses hold: each `∂Y_j` is an integral current, since it is
  integer multiplicity by the assumption of (BLI) and `∂∂Y_j = 0` (SimonGMT's
  `GeometricCurrentOn.boundary_boundary`) is integer multiplicity by `hIM_of_eq_zero`; for every
  `W`, `M_W(∂Y_j) + M_W(∂∂Y_j) = M_W(∂Y_j) ≤ M(∂Y_j)`, whose supremum over `j` is finite; and
  `∂Y_j ⇀ ∂Y` is assumed.

## 4. Dependency structure and absence of circularity

The tables below are computed from `Submission.lean`: a declaration *names* another if
`Submission.<name>` occurs in its proof outside comments. The same edges are read from the compiled
environment in §9.

**Root children used by root children.** Only the root children and `main_theorem` name a root
child; no other accepted declaration does.

| Root child | Root children named in its proof (receiving lemma) | Root children used transitively |
| --- | --- | --- |
| `compactness_under_mass_bounds` | — | — |
| `constancy_theorem` | — | — |
| `lipschitz_pushforward_integer_multiplicity` | — | — |
| `slicing_theorem` | — | — |
| `rectifiability_theorem` | — | — |
| `deformation_theorem` | `slicing_theorem`, `lipschitz_pushforward_integer_multiplicity` (both arguments of `deformation_onto_skeleton`) | the same |
| `isoperimetric_theorem` | `deformation_theorem` (applied directly) | + `slicing_theorem`, `lipschitz_pushforward_integer_multiplicity` |
| `polyhedral_approximation` | `slicing_theorem` (argument of `polyhedral_approx_truncation_seq`), `deformation_theorem` (argument of `polyhedral_approx_finite_mass_seq`) | + `lipschitz_pushforward_integer_multiplicity` |
| `integrality_of_weak_limits` | `slicing_theorem` (argument of `iwl_localization`, `iwl_positive_density`, `iwl_integer_density`), `lipschitz_pushforward_integer_multiplicity` (argument of `iwl_cycle_reduction`, `iwl_positive_density`, `iwl_integer_density`), `isoperimetric_theorem` (argument of `iwl_positive_density`), `rectifiability_theorem` (applied directly) | + `deformation_theorem` |
| `boundary_rectifiability` | `slicing_theorem` (argument of `br_local_finite_mass_extension`), `deformation_theorem` and `integrality_of_weak_limits` (arguments of `br_boundary_isIntegerMultiplicity_of_finite_mass`) | + `lipschitz_pushforward_integer_multiplicity`, `isoperimetric_theorem`, `rectifiability_theorem` |
| `flat_convergence_iff_weak_convergence` | `slicing_theorem` and `boundary_rectifiability` (arguments of `fiw_localization`), `deformation_theorem` (argument of `fiw_total_boundedness`) | + `lipschitz_pushforward_integer_multiplicity`, `isoperimetric_theorem`, `rectifiability_theorem`, `integrality_of_weak_limits` |
| `federer_fleming_compactness` | `compactness_under_mass_bounds`, `boundary_rectifiability`, `integrality_of_weak_limits` (applied directly, §3.4) | + `slicing_theorem`, `lipschitz_pushforward_integer_multiplicity`, `deformation_theorem`, `isoperimetric_theorem`, `rectifiability_theorem` |

The middle column is exactly the list of sibling dependencies declared by the accepted root
decomposition (`nodes/root/decomposition-v3.json`): deformation ← {slicing, Lipschitz
push-forward}; isoperimetric ← {deformation}; polyhedral approximation ← {deformation, slicing};
integrality ← {rectifiability, isoperimetric, slicing, Lipschitz push-forward}; boundary
rectifiability ← {deformation, slicing, integrality}; flat ⇔ weak ← {deformation, slicing, boundary
rectifiability}; Federer–Fleming ← {compactness, boundary rectifiability, integrality}; the other
five have no sibling dependencies.

**Conjuncts as hypotheses.** Besides the root children, 21 accepted declarations have one or more
of the twelve propositions among the hypotheses of their Lean types:
`polyhedral_approx_truncation_seq`, `br_local_finite_mass_extension`, `ind_pi_ss_cycle_slice_family`,
`ind_pi_good_slice_selection`, `ind_pi_localized_cycles`, `iwl_localization` (`SlicingTheorem`);
`deformation_im_pushforward_limit`, `ind_pi_pl_linear_pushforward_family`, `ind_pi_projected_limit`,
`iwl_smooth_pushforward`, `iwl_cycle_reduction` (`LipschitzPushforwardIntegerMultiplicity`);
`deformation_onto_skeleton`, `ind_plane_multiplicity_integer`, `iwl_integer_density` (both);
`iwl_positive_density` (both and `IsoperimetricTheorem`); `polyhedral_approx_finite_mass_seq`,
`br_lattice_approximation`, `fiw_tb_finite_net`, `fiw_total_boundedness` (`DeformationTheorem`);
`br_boundary_isIntegerMultiplicity_of_finite_mass` (`DeformationTheorem`,
`IntegralityOfWeakLimits`); `fiw_localization` (`SlicingTheorem`, `BoundaryRectifiability`). Their
proofs do not name any root child; the root children enter only at the call sites of the table
above.

**No circularity.**

- Lean elaborates the top-level declarations of `Submission.lean` in order, and a declaration can
  refer only to declarations that precede it. The file has no `mutual` block, no `partial` or
  `unsafe` definition and no `axiom`. No proof among the 692 (the 691 accepted theorems and
  `main_theorem`) names a later declaration, and the same holds for the references read from the
  compiled environment (§9). So the reference relation is acyclic and the file order is a
  topological order of it. The root children occur in the order `constancy_theorem` (L42133),
  `lipschitz_pushforward_integer_multiplicity` (L46209), `rectifiability_theorem` (L62437),
  `slicing_theorem` (L66972), `deformation_theorem` (L66990), `isoperimetric_theorem` (L67200),
  `polyhedral_approximation` (L67293), `integrality_of_weak_limits` (L68796),
  `boundary_rectifiability` (L68901), `compactness_under_mass_bounds` (L69081),
  `flat_convergence_iff_weak_convergence` (L69448), `federer_fleming_compactness` (L69482), followed
  by `main_theorem` (L69498).
- Labelling the conjuncts by Simon's item numbers, the formal proofs use: nothing else for 2.15,
  2.34, 3.9, §4 and 8.1; §4 and 3.9 for 5.3; 5.3 for 6.1; §4 and 5.3 for 6.2; §4, 3.9, 6.1 and 8.1
  for 8.2; §4, 5.3 and 8.2 for 6.3; §4, 5.3 and 6.3 for 7.2; 2.15, 6.3 and 8.2 for 3.11 (the middle
  column above). In particular the proof of 8.2 does not use 3.11, 6.3 or 7.2.
- Mathlib and SimonGMT are upstream packages pinned before this problem existed; they cannot
  refer to a `GMT.Ch06` declaration.

**Size.** 688 of the 691 accepted declarations are reachable from `main_theorem` through these
references. The longest chain of references starting at `main_theorem` has 18 declarations,
`main_theorem` included.

## 5. Library reuse and provenance

All library declarations used are **existing pinned upstream declarations, reused, not new
helpers**. Theorems enter only through their kernel-checked types, definitions also through their
kernel-checked bodies. The root comparator exports
`main_theorem` with its whole dependency closure, which contains every library declaration used,
re-checks the closure with the Lean kernel and admits only the axioms `propext`, `Quot.sound` and
`Classical.choice` (§9). So their reuse is verified in this run, not trusted. They are cited here
by exact Lean name, with file and line at the pinned revisions; their statements are their Lean
types there.

Read from the compiled environment (§9), the 692 theorems of `Submission.lean` refer directly to
6361 Mathlib constants, 164 SimonGMT constants, 476 constants of Lean's `Init` and 4 of Batteries.

**Mathlib** (`25730c7c759d108ef87ab70af2342a196760f79d`, the revision of `lake-manifest.json`; the
local snapshot's `mathlib/` checkout is at the same commit, §10). Standard Mathlib notions of
measure theory, analysis and topology occur in the statements (§1.3–§1.4) and in the reproduced
Lean code of §3. The table lists the Mathlib declarations that the prose of §3 names, and a
selection of further Mathlib results that accepted declarations refer to directly, with the
accepted declarations that refer to each of them directly.

| Declaration | File:line (Mathlib) | Referred to directly by |
| --- | --- | --- |
| `RealRMK.rieszMeasure` | `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:65` | `smr_rb_borel_riesz_sigma_compact` |
| `RealRMK.integral_rieszMeasure` | `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:345` | `smr_rb_borel_riesz_sigma_compact` |
| `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` | `Mathlib/MeasureTheory/Covering/Differentiation.lean:818` | `iwl_imc_normalized_lebesgue_points`, `ind_ab_weighted_lebesgue_point`, `fiw_tl_ald_ld_weighted_lebesgue_point`, `fiw_tl_ald_closedBall_lebesgue_point`, `iwl_top_dim_integrality` |
| `Besicovitch.vitaliFamily` | `Mathlib/MeasureTheory/Covering/Besicovitch.lean:1021` | `iwl_imc_normalized_lebesgue_points`, `rectifiability_orientation`, `ind_ab_weighted_lebesgue_point`, `fiw_tl_ald_ld_weighted_lebesgue_point`, `fiw_tl_ald_closedBall_lebesgue_point`, `iwl_top_dim_integrality` |
| `Besicovitch.ae_tendsto_measure_inter_div` | `Mathlib/MeasureTheory/Covering/Besicovitch.lean:1105` | `rectifiability_mickle_rado_density_zero`, `fiw_tl_ald_ld_weighted_density_point` |
| `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` | `Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:205` | `ltg_tau_unique_on_open`, `lpf_rsn_weighted_fundamental_lemma`, `polyhedral_approx_finite_smooth_ext`, `iwl_sp_sn_weighted_fundamental_lemma`, `iwl_im_patching`, `ind_pi_ss_cycle_slice_boundary`, `ind_top_form_density_ae_unique`, `iwl_localization` |
| `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` | `Mathlib/MeasureTheory/Function/Jacobian.lean:255` | `slicing_im_st_cd_c1c_critical_image_null`, `lpf_countably_rectifiable_c1_cover`, `iwl_cr_hp_injective_pieces`, `iwl_cr_hp_piece_product`, `rectifiability_weighted_tangent_ae`, `slicing_im_tg_cc_contDiff_range_chart_cover` |
| `LipschitzWith.ae_differentiableAt` | `Mathlib/Analysis/Calculus/Rademacher.lean:385` | `slicing_mb_sa_mollify_lipschitz_hasFDerivAt`, `lpf_c1_approximation_real`, `lpf_countably_rectifiable_c1_cover`, `iwl_cr_hp_injective_pieces`, `slicing_im_coarea_c1_approx`, `slicing_im_st_cd_c1_cover`, `slicing_im_ll_gws_lipschitz_ibp` |
| `MeasureTheory.Measure.measure_toMeasurable_inter` | `Mathlib/MeasureTheory/Measure/Basic.lean:472` | `rectifiability_structure_projection` |
| `iSup_comp_le` | `Mathlib/Order/CompleteLattice/Basic.lean:342` | `compactness_under_mass_bounds`, `flat_convergence_iff_weak_convergence`, `federer_fleming_compactness` |
| `Filter.tendsto_of_subseq_tendsto` | `Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean:125` | `flat_convergence_iff_weak_convergence` |
| `lt_trichotomy` | `Mathlib/Order/Defs/LinearOrder.lean:102` | `fiw_tb_te_l1d_compact_sign_approx`, `slicing_im_si_cutoff_tangential_gradient`, `slicing_support_subset`, `br_top_dim_lattice_approximation`, `br_lattice_approximation`, `deformation_skeleton_polyhedral`, `integrality_of_weak_limits`, `fiw_tb_finite_net` |
| `AlternatingMap.map_linearDependent` | `Mathlib/LinearAlgebra/Alternating/Basic.lean:784` | `br_la_apply_eq_zero_of_lt_degree`, `lpf_pi_induced_orientation`, `lpf_simple_nvector_algebra`, `iwl_top_dim_integrality`, `integrality_of_weak_limits`, `fiw_tb_finite_net` |
| `LinearIndependent.fintype_card_le_finrank` | `Mathlib/LinearAlgebra/Dimension/Finite.lean:157` | `br_la_apply_eq_zero_of_lt_degree`, `iwl_top_dim_integrality`, `integrality_of_weak_limits`, `fiw_tb_finite_net` |
| `finrank_euclideanSpace_fin` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean:205` | 25 accepted declarations |

**SimonGMT** (`simongmt` package, `2b3663083f3fe399b6296fb8eaee52169170e197`, the
`simongmt-library` branch of `ZhengyangZhang06/gmt-formalize`, pinned in `lake-manifest.json`; an
earlier kernel-checked partial formalization of the same book, whose reuse the task allows).

- *Definitions used by the statement.* The contract imports SimonGMT and uses its definitions
  (§1.3), which `GMT/Ch06/README.md` checks against the book: `TestFormOn`, `GeometricCurrentOn`,
  `GeometricCurrentOn.boundary`, `massOn`, `mass`, `support`, `WeaklyConvergesOn`, `NVector`,
  `simpleNVector`, `nVectorPushforward`, `SimonMultiIndex`, `Covector`, `DifferentialForm`,
  `Chapter03.CountablyRectifiable`, `Chapter03.HasWeightedApproximateTangentSpaceAt` and
  `Chapter01.dimensionalUpperDensity`.
- *Constants used by the proofs.* The proofs refer directly to 164 SimonGMT constants from 26
  modules; Appendix B lists them, with the accepted declarations that refer to each theorem. The
  SimonGMT declarations named in the prose of §3, §5 and §6 are the following (a user list longer
  than fifteen is given as a count):

| Declaration (namespace `Poincare.SimonGMT.`) | File:line (package) | Referred to directly by |
| --- | --- | --- |
| `Chapter06.GeometricCurrentOn.boundary_boundary` | `Chapter06/Currents.lean:365` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `dph_lpf_boundary`, `deformation_pushforward_homotopy`, `deformation_onto_skeleton`, `iwl_positive_density`, `integrality_of_weak_limits` |
| `Chapter06.WeaklyConvergesOn.boundary` | `Chapter06/Currents.lean:389` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_onto_skeleton`, `iwl_cycle_reduction`, `iwl_positive_density`, `integrality_of_weak_limits` |
| `Chapter06.WeaklyConvergesOn.massOn_le_liminf` | `Chapter06/Mass.lean:100` | `cmb_tendsto_integral_of_weaklyConvergesOn`, `iwl_restriction_weak_limit`, `iwl_localization`, `iwl_positive_density`, `fiw_localization`, `integrality_of_weak_limits` |
| `Chapter06.GeometricCurrentOn.restrictDomain` | `Chapter06/CurrentLocalEquality.lean:40` | `br_restrictDomain_isIntegerMultiplicity`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_restrictDomain_mass_im`, `fiw_tb_extend_to_univ`, `br_local_finite_mass_extension`, `ind_pi_localized_cycles`, `polyhedral_approximation`, `boundary_rectifiability`, `fiw_tb_finite_net` |
| `Chapter06.testFormOnInclusion` | `Chapter06/CurrentLocalEquality.lean:27` | `br_restrictDomain_isIntegerMultiplicity`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`, `polyhedral_approx_truncation_seq`, `br_local_finite_mass_extension`, `ind_pi_localized_cycles`, `iwl_localization`, `polyhedral_approximation`, `boundary_rectifiability`, `fiw_tb_finite_net` |
| `Chapter03.countablyRectifiable_of_measure_zero` | `Chapter03/Rectifiable.lean:45` | `br_isIntegerMultiplicity_of_local`, `iwl_cr_ip_product_triple`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `imc_isRectifiableTriple_of_eventually_mem`, `iwl_im_patching`, `rectifiability_mass_measure_rectifiable`, `fiw_localization`, `integrality_of_weak_limits`, `fiw_tb_finite_net` |
| `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` | `Chapter03/Rectifiable.lean:514` | `rectifiability_structure_projection`, `rectifiability_mass_measure_rectifiable` |
| `Chapter01.simon_theorem_4_14_caratheodory` | `Chapter01/RadonPolarRepresentation.lean:150` | `rectifiability_mass_measure_representation` |
| `Chapter01.simon_theorem_4_14_positive_envelope` | `Chapter01/VectorFunctionalEnvelope.lean:280` | `rectifiability_mass_measure_representation`, `iwl_restriction_theory` |
| `Chapter01.simon_theorem_4_14_l1_extension` | `Chapter01/VectorFunctionalL1.lean:147` | `iwl_restriction_theory` |
| `Chapter06.GeometricCurrentOn.massOn_mono` | `Chapter06/Mass.lean:81` | 20 accepted declarations |
| `Chapter06.CurrentOn` | `Chapter06/Currents.lean:127` | 193 accepted declarations |

- *Definitions that `GMT/Ch06/README.md` marks as not used.* The README lists
  `Chapter06.MassRepresentation`, `IntegerRectifiableCurrentData`, the `Current`/`GeometricCurrent`
  algebraic API and `Chapter04.RectifiableVarifold`. None of these, and no constant of a `Chapter04`
  module, is among the 164 constants of Appendix B. The proofs do use `Chapter06.CurrentOn U n`, the
  type `TestFormOn U n →ₗ[ℝ] ℝ` of linear functionals underlying `GeometricCurrentOn` (its field
  `toCurrent`), which is not part of that list.

## 6. Historical decomposition versus the lemmas actually used

**The DAG.** The accepted root decomposition (`nodes/root/decomposition-v3.json`, committed as
`.humanize-workspace/20261011t144224z-6e4735dbca/root/decomposition.json`) dispatched the twelve
children of §2. Recursive decompositions produced 679 further accepted nodes, 691 in all. 512 of
them are leaves; the other 179 were decomposed further, each by a decomposition accepted by its own
independent audit. 122 nodes occur in the `children` lists of more than one parent. Every accepted
node occurs in `Submission.lean` under its frozen name and with its frozen type (§9). Appendix A
lists all of them.

**Accepted but unused (3 declarations).** No declaration that `main_theorem` uses names these three.
Each is kept unchanged, so that its accepted interface is preserved.

| Declaration (line) | Node; issue; PR | Declared as a child or dependency of | What those declarations' proofs name instead |
| --- | --- | --- | --- |
| `dph_hausdorff_product_formula` (L28324) | `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1`; #5270; #5552 | `deformation_pushforward_homotopy`, `dph_interval_product_im` | `deformation_pushforward_homotopy` names `cmb_abs_apply_le_of_massOn_le`, `dph_interval_product`, `dph_interval_product_im`, `dph_lipschitz_pushforward`, `dph_lipschitz_pushforward_im`, `dph_lipschitz_smooth_approx`, `dph_smooth_homotopy`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `iwl_cr_ci_slice_testForm`, `iwl_cr_support_lemmas` and `iwl_sp_exists_compatible_testForm`; `dph_interval_product_im` names `iwl_cr_ci_slice_testForm` and `iwl_cr_interval_product_im`, whose proof names `iwl_cr_hausdorff_product_formula` (node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`). The frozen `lean_statement`s of `dph_hausdorff_product_formula` and `iwl_cr_hausdorff_product_formula` are byte-identical. |
| `iwl_imc_restriction_im` (L38058) | `root.integrality_weak_limits-a1.im_closure-a1.restriction_im-a1`; #2825; #3911 | `iwl_im_closure` | `iwl_im_closure` names `iwl_imc_lincomb_im`, `iwl_imc_tangent_overlap`, `iwl_imc_tau_measure_representation`, `iwl_restriction_theory`, `iwl_weighted_tangent_locality` and `slicing_representation_unique` |
| `fiw_tl_ald_closedBall_lebesgue_point` (L64049) | `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.closed_ball_lebesgue_point-a1`; #3185; #3625 | `fiw_tl_ae_l1_density`, `fiw_tl_ald_local_differentiation` | `fiw_tl_ae_l1_density` names `fiw_tl_ald_ball_reduction`, `fiw_tl_ald_local_differentiation` and `fiw_tl_ald_pointwise_estimate`; `fiw_tl_ald_local_differentiation` names `fiw_tl_ald_ld_weighted_density_point` and `fiw_tl_ald_ld_weighted_lebesgue_point`; the latter names no accepted declaration and refers to Mathlib directly (§5) |

**Declared edges that the declaring proof does not use, even transitively (20).** Comparing every
node's declared `children` and `depends_on` with the references of its Lean proof:

| Declaring declaration | Declared but not used, even transitively |
| --- | --- |
| `fiw_tb_extend_to_univ` (L14702) | `fiw_tb_rectifiable_support_null` (L14642) |
| `smr_exists_continuous_extension` (L21858) | `cmb_abs_apply_le_of_massOn_le` (L561), `cmb_exists_compactly_contained_exhaustion` (L401) |
| `imc_lintegral_coordNorm_le_mass` (L24303) | `polyhedral_approx_pairing_expansion` (L17563) |
| `dph_interval_product_im` (L36406) | `dph_hausdorff_product_formula` (L28324) |
| `iwl_im_patching` (L36691) | `br_weightedTangent_congr` (L2130), `ltg_tau_congr_on_open` (L1844) |
| `iwl_imc_density_zero_off_set` (L37453) | `rectifiability_density_comparison` (L32149) |
| `deformation_telescope_limit` (L39553) | `cmb_abs_apply_le_of_massOn_le` (L561) |
| `deformation_ipl_mwc_test_density` (L42408) | `constancy_mdc_smooth_approx_identity_ae_tendsto` (L41192) |
| `deformation_pushforward_homotopy` (L43249) | `dph_hausdorff_product_formula` (L28324), `lpf_raf_local_lipschitz_area` (L20988), `lpf_rectifiable_support_null` (L13320) |
| `slicing_im_coarea_chart_cover` (L44011) | `slicing_im_coarea_c1_approx` (L43963) |
| `slicing_im_coarea_chart_regular` (L47062) | `slicing_im_coarea_glue` (L16427) |
| `deformation_skeleton_polyhedral` (L49061) | `constancy_mollifier_iteratedFDeriv_norm_le_integral` (L9648), `fiw_fcl_nested_subseq` (L803) |
| `iwl_im_closure` (L54313) | `iwl_imc_restriction_im` (L38058) |
| `fiw_tl_ald_local_differentiation` (L64064) | `fiw_tl_ald_closedBall_lebesgue_point` (L64049) |
| `fiw_tl_ae_l1_density` (L64288) | `fiw_tl_ald_closedBall_lebesgue_point` (L64049) |

Five of these edges point to the three unused declarations above; the other fifteen point to
declarations that are used elsewhere in the proof of `main_theorem`.

**References that the decomposition did not declare (6).** `iwl_localization` names
`br_weightedTangent_congr` and `cmb_abs_apply_le_of_massOn_le`; `iwl_positive_density` names
`cmb_covector_eq_sum_coord_smul_wedge`, `cmb_exists_compactly_contained_exhaustion`,
`slicing_ru_continuous_to_bounded` and `slicing_ru_smooth_to_continuous`. All six are accepted
nodes that precede their users in the file, so these references create no new obligation.

**Results the root outline proposed to cite.** The rationale of the accepted root decomposition
ends with the list (its four items joined here by semicolons) "External published results cited
rather than reproved: the Besicovitch–Federer structure theorem (Simon Ch. 3, 3.6; Federer
3.3.13); the area and co-area formulas on rectifiable sets (Simon Ch. 3, §2); BV compactness and
Poincaré inequalities (Simon Ch. 2); vector Riesz representation (SimonGMT `simon_theorem_4_14`)."
The Lean proof assumes none of them. The root comparator re-checks the whole dependency closure of
`main_theorem` with the Lean kernel and admits only the axioms `propext`, `Quot.sound` and
`Classical.choice` (§9). So every result that the Lean proof uses is proved, either by an accepted
declaration of `Submission.lean` or inside Mathlib or SimonGMT. For example, the decompositions
below the root dispatched the accepted nodes `root.rectifiability-a1.structure_projection-a1`
(declaration `rectifiability_structure_projection`), `root.rectifiability-a1.bf_projection_null_ae-a1`
(`rectifiability_bf_projection_null_ae`), `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
(`lpf_rectifiable_area_formula`) and `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`
(`slicing_im_coarea`), whose DAG titles refer to items of that list ("… (Simon 3, Structure Theorem
3.6, as used in 8.1)", "Besicovitch-Federer projection theorem for almost every linear map (finite
measure)", "Area formula on rectifiable sets …", "Co-area formula for a Lipschitz function on a
countably rectifiable carrier …"). Titles are labels, not statements; these four declarations are
proved in the file like every accepted node, and their statements are their Lean types. The
SimonGMT theorems `Chapter01.simon_theorem_4_14_caratheodory`,
`Chapter01.simon_theorem_4_14_positive_envelope` and `Chapter01.simon_theorem_4_14_l1_extension` are
used directly, with their SimonGMT proofs (§5).

## 7. History (preserved, not rewritten)

The following records are left untouched under the run directory
`.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/`. Times are UTC on 2026-10-14
unless stated otherwise.

- `nodes/root/natural-proof-source.md`: the operator-supplied root outline, which points to the
  published proof (`book/sources/chapter-06-source.txt`, sha256
  `ab79aa2a751c92977877c0d793ccd3dc6ead15420d7de71da57d35ac53b75047`) and lists one step per conjunct.
- `nodes/root/plan-source.md`, `plan-draft-v1.md`, `plan-v1.md`: the plan scaffold ("decompose it
  along the conjuncts of the frozen statement").
- `nodes/root/decomposition-v1.json`, `-v2.json`, `-v3.json` with their audits
  (`decomposition-audit-v1.json` to `-v3.json`) and review receipts.
  - v1 was rejected; its audit required four changes (in the Lipschitz push-forward, slicing,
    deformation and rectifiability children).
  - v2 was rejected; its audit required one change (deformation A3, where σ-finiteness relied on
    an unsupported `θ′ ≥ 1`).
  - v3 was accepted; its audit found all twelve children and their natural-language proofs
    acceptable.
- `nodes/*/parent-supplied-natural-proof.md` for every child: the reviewed natural-language proofs.
  Committed copies are under `.humanize-workspace/20261011t144224z-6e4735dbca/` (Appendix A).
- `nodes/root/speculative-prompt-v2.md` and `speculative-process-v2.log`: the speculative root draft,
  commit `405d3381` ("wip(speculative): draft root"). It replaced `by sorry` by the twelve-tuple of
  §2, which is unchanged since.
- `operator-repairs/`: records of operator repairs to *child* integration branches. None concerns
  the root.
- The overlay. Starting from the frozen commit `d8d46c95`, the integration branch merged, in this
  order, the children's accepted candidate commits, which already contain their accepted
  descendants: `ec8c9ac4` (2.15), `b4bbd871` (2.34), `3289485c` (3.9), `f27fd6da` (slicing),
  `4efd922c` (5.3), `2e7a66f2` (6.1), `786e6c8a` (6.2), `8f66d3bb` (6.3), `7c119a55` (7.2) and
  `5abeab04` (3.11); 8.1 (`ba8a5544`) and 8.2 (`036fb2d8`) arrive through the commits that depend
  on them. The merges of `f27fd6da`, `4efd922c`, `786e6c8a`, `8f66d3bb`, `7c119a55` and `5abeab04`
  were each followed by a controller commit "Re-merge declarations line-merged from …"
  (`e7946924`, `f0c3d65e`, `5e1fb0e4`, `6e6a09b9`, `df77b950`, `4c501244`). Then came
  "Drop declarations repeated by merging accepted checkpoints" (`a54722e5`), the merge of the
  speculative draft `405d3381` (`598a5903`) and a last re-merge commit, `dfdc020b`.
- Root rounds. The first is recorded by `lean-audit-v1.json` and `comparison-identity-v1.json`;
  each later one by `nodes/root/rlcr-plan-vN.md` and `rlcr-config-vN.json` and, for its Lean
  candidate, `comparison-identity-vK.json` and `lean-audit-vK.json`:
  1. First round (`lean-audit-v1.json`, `comparison-identity-v1.json`): the overlay `dfdc020b`
     passed the exact comparator, but the Lean acceptance gate failed because no final root prose
     had been committed for independent review.
  2. `rlcr-plan-v1.md` (18:02): produced `e9e57ea4` (§8) and the first version of this file,
     `c3c9b342` (`comparison-identity-v2.json`, `lean-audit-v2.json`; controller's isolated
     comparator run in `comparator-v1.log`). Its independent review,
     `publication-prose-audit-v1.json`, withheld acceptance for two corrections in Appendix A (a
     wrong image-density formula in the entry of `lpf_pushforward_integrality`, and a wrong lemma
     number in that of `rectifiability_bf_trichotomy`).
  3. `rlcr-plan-v2.md` (20:05): produced `e26e6909` (`comparison-identity-v3.json`,
     `lean-audit-v3.json`, `comparator-v2.log`). Its review, `publication-prose-audit-v2.json`,
     found the stated dependency graph acyclic with the reported 688 reachable declarations and
     withheld acceptance for two corrections in Appendix A (the entry of
     `rectifiability_structure_projection`, which asserted that a possibly non-measurable set is,
     up to a null set, a countable union of compact pieces, and an example in the correction line
     of `rectifiability_orientation`, which omitted a boundary term).
  4. `rlcr-plan-v3.md` (21:08): produced `a90a4151` (`comparison-identity-v4.json`,
     `lean-audit-v4.json`, `comparator-v3.log`, `isolated-comparator-result.json`). Its review,
     `publication-prose-audit-v3.json`, withheld acceptance for five findings, all in Appendix A:
     entries that stated accepted declarations more loosely than their Lean types, without
     hypotheses of the Lean type (`imc_isRectifiableTriple_of_eventually_mem`,
     `smr_riesz_borel_euclidean`, `smr_rb_borel_riesz_sigma_compact`,
     `smr_ufd_integral_lower_bound`, `deformation_ipl_mwc_mil_tendsto_integral_mul_det`,
     `deformation_ipl_cc_tendsto_setIntegral_of_partition`) or with a stronger conclusion
     (`imc_im_density_limit`).
  5. `rlcr-plan-v4.md` (23:29): a round whose process record was set aside at a controller
     cutover (`rlcr-process-before-cutover-2026-10-14T234955Z.json`); the branch has no commit
     after `a90a4151` before the present revision.
  6. `rlcr-plan-v5.md` (23:56): the present round. Its plan adds the requirement that every stated
     result of an accepted child or dependency carry every hypothesis of its frozen Lean type, or
     be cited only by its exact Lean name, and that reviewed proofs be cited rather than re-derived.

All these records, the three review records in particular, are left unchanged. The previous versions
of this file remain in the branch history: `c3c9b342`, `e26e6909` and `a90a4151`.

## 8. Changes made in this candidate

**Lean (unchanged in this round).** The only change to a `.lean` file made by the root rounds is
commit `e9e57ea4`. The integration commit `43c463fd` ("Re-merge declarations line-merged from
ba8a5544bc76") had inserted a second, byte-identical copy of the contract's 20-line module
docstring after the imports, and `e9e57ea4` deletes it together with one blank line before and
after it (`1 file changed, 22 deletions(-)`). No declaration, statement, import or proof changed.
Since then `GMT/Ch06/Submission.lean` is unchanged (sha256 `8844dc26…46f0`).

**Prose: this revision.** It restructures this file so that it states no result of an accepted
declaration other than the twelve conjuncts, and re-derives no reviewed proof.

1. Removed: the previous §3 (step-by-step re-derivations of the twelve children's proofs, naming
   and paraphrasing several hundred accepted lemmas), the previous Appendix A (a reproduction of
   the doc comments of the 685 documented accepted declarations and summaries for the other six,
   with 120 correction notes) and the list of
   corrections to the printed text in the previous §6. These passages restated results and proofs
   of accepted declarations; all nine findings of the three reviews concerned entries of that
   Appendix A. The reviewed proofs themselves are cited instead (§3, Appendix A).
2. Added: verbatim reproductions of the contract definitions that the statements use, with clause
   by clause readings (§1.3–§1.4); the twelve conjuncts verbatim, each translated hypothesis by
   hypothesis (§3); for each conjunct, the citation of its accepted child and of its review, the
   child's Lean proof (with its `--` comments removed), and the accepted declarations and root
   children that the proof names, with the lemmas that receive the root children (§3, §4); and the
   argument of `federer_fleming_compactness` read off from its Lean proof, which names only root
   children (§3.4).
3. Appendix A is now a catalogue of the 691 accepted declarations by exact name only: line, node,
   theorem issue, solution PR, accepted candidate commit, the committed reviewed proof, and the
   accepted declarations each proof names.
4. The five findings of `publication-prose-audit-v3.json` concerned the previous Appendix A entries
   of `imc_isRectifiableTriple_of_eventually_mem` (L36264), `imc_im_density_limit` (L47189),
   `smr_riesz_borel_euclidean` (L22593), `smr_rb_borel_riesz_sigma_compact` (L22260),
   `smr_ufd_integral_lower_bound` (L21658), `deformation_ipl_mwc_mil_tendsto_integral_mul_det`
   (L40786) and `deformation_ipl_cc_tendsto_setIntegral_of_partition` (L40325). This revision
   states none of these results. Each declaration is cited only by its exact name (Appendix A), and
   its statement is its Lean type at the line given, which the interface check of §9 compares with
   its frozen `lean_statement`. The same holds for the declarations of the earlier findings
   (`lpf_pushforward_integrality`, `rectifiability_bf_trichotomy`,
   `rectifiability_structure_projection`, `rectifiability_orientation`).
5. Re-verification of the remaining facts of the previous version, from a fresh private build and
   fresh scripts (§9), changed four statements of its §9. (a) A scan for lines that begin with the
   word `theorem` hits three doc-comment lines (32091, 55302 and 65920), not one. (b) The
   declaration texts are byte-identical to the accepted candidate texts for 686 declarations, not
   all 691; the other five differ by one preceding line (§9). (c) The previous version counted 725
   theorems in the module, 33 of them generated by Lean, without recording how it enumerated them;
   enumerating the constants that the compiled module records (`constNames` of its module data)
   gives 1471 theorems, 779 of them generated, all with the same three axioms. (d) The duration of
   the full comparator run is given as 4610 s, the difference of the receipt's `finished_at` and
   `started_at`; the previous version gave 4611 s.

**Prose: earlier revisions** (kept in the branch history, §7). `c3c9b342` added this file;
`e26e6909` made the two corrections of the first review and seventeen more found on re-checking
Appendix A; `a90a4151` made the two corrections of the second review and corrections in 100
further entries of Appendix A and in §0–§6.

None of the prose commits changes a `.lean` file or a build input, so none changes the inputs of
the comparator (§9).

## 9. Verification record

All checks used the pinned toolchain and the shared package tree `lake-packages-25730c7c`
(Mathlib `25730c7c`, `simongmt` `2b366308`). The scripts and scratch files are outside the
repository (`/tmp`).

**Exact configured comparator.** The command given in the task (`env -u HF_TOKEN HUMANIZE_NODE_ID=root
HUMANIZE_COMPARATOR_SUCCESS='Your solution is okay!' HUMANIZE_RUN_DIR=… … python3
…/verifier/gmt-compare.py --lean-target GMT/Ch06/Submission.lean --verifier-dir …/verifier
--verify-dir …/cluster-state/verification --packages …/lake-packages-25730c7c --frozen-commit
d8d46c9587747dee0751a1f780fcafdba16a3886 root`) was run from the worktree root in this round, with
the worktree at `a90a4151` (the previous revision) and no change to any `.lean` file or build
input. It exited with status 0 and printed
`GMT comparator: identical inputs already passed every check in …/results/hoa39/20261014T182015Z-ch06-root-v8uhzxvd; GMT.Ch06.main_theorem accepted without re-running the kernels`
and `Your solution is okay!`. Receipt:
`cluster-state/verification/results/hoa64/20261015T011946Z-ch06-root-actbsvcj/result.json`, status
`passed`, `cached_from` the run below, verdict key
`a14f190d2e735e41e87da9bc3ed4eaa8cc9e4f12a41ee17766a29e82ebfb3e22`. It was run again with a draft
of this file in place in the worktree and the `.lean` files and build inputs still those of
`a90a4151`; it printed the same lines (receipt
`cluster-state/verification/results/hoa64/20261015T023126Z-ch06-root-e84xauax/result.json`, status
`passed`, same `cached_from` and verdict key). The commit of this revision changes only this
Markdown file, so the comparator inputs of the committed candidate are the same.

The full run whose verdict is reused,
`cluster-state/verification/results/hoa39/20261014T182015Z-ch06-root-v8uhzxvd/`, started (receipt
field `started_at`, 18:20:13) 15 s after `e9e57ea4` was committed (18:19:58) and checked the same
inputs: `GMT/Ch06/Submission.lean` sha256
`8844dc262ee305c7d301443a16525f97108a466caebf817f3e7d820abf0846f0`, `GMT/Ch06/Contract.lean` sha256
`ea3ee0ddd08be5db60dced2b002e9f60fd87091910069abcfcbd7e34db89853d`, and `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain` and `GMT.lean` byte-identical to the present ones.

- Receipt `result.json`: status `passed`; checks `exit_zero`, `lean_kernel_accepted` and
  `final_marker` all `true`; verdict key `a14f190d…`; `finished_at − started_at` = 4610 s.
- Configuration (`comparator-config.json`): challenge module `GMT.Ch06.Contract`, solution module
  `GMT.Ch06.Submission`, theorem `GMT.Ch06.main_theorem`, permitted axioms `propext`, `Quot.sound`,
  `Classical.choice`, Nanoda disabled (the Lean kernel check is mandatory).
- Log (`comparator.log`): both modules built ("Build completed successfully (3152 jobs)" and
  "(3306 jobs)"), then "Running Lean default kernel on solution." and "Lean default kernel accepts
  the solution", then "Your solution is okay!". The only `sorry` in the log is the challenge's own
  (``warning: GMT/Ch06/Contract.lean:362:8: declaration uses `sorry` ``).

The earlier comparator runs on the previous revisions (`comparator-v1.log` to `-v3.log` and the
evidence directories they name) reused the same verdict.

The comparator compares `main_theorem` and every definition it depends on with the frozen contract,
replays the Lean kernel on the exported dependency closure and permits only the axioms `propext`,
`Quot.sound` and `Classical.choice`. It reads the `.lean` files and the Lake build inputs of the
worktree; this Markdown file is not among its inputs.

**Private build and axioms.** `GMT/Ch06/Submission.lean` (sha256 `8844dc26…46f0`, identical to
`HEAD`) was compiled in a private copy (`/tmp/ch06build`) that links the shared package tree, with
`lake env lean -j 6 -o … GMT/Ch06/Submission.lean`. It finished with exit status 0 in 3179 s, with
no error and no `sorry`. Its 102 warnings are 84 deprecation warnings (deprecated Mathlib lemma
names and the `push_neg` tactic), 16 linter warnings about unused `simp` arguments and 2 style
suggestions (`have` instead of `haveI`). A meta-program (`Scratch/EnvQuery.lean`) imported the built module and read every
constant of the module `GMT.Ch06.Submission` (1570 constants: 1471 theorems, 96 definitions, and
the inductive type, constructor and recursor of `IsRectifiableTriple`). `collectAxioms` gives
exactly `[propext, Classical.choice, Quot.sound]` for `main_theorem` and for each of the 691
accepted theorems. The other 779 theorems were generated by Lean (605 `_simp_…`, 106 `_proof_…` and
33 `_abel_…` auxiliary lemmas, 16 equation lemmas, 12 congruence lemmas `congr_simp`, and the 7
field projections of the structure `IsRectifiableTriple`); each depends on a subset of the same
three axioms.

**Reference graph.** The same program read the constants that occur in the type and value of every
constant. Following references through the Lean-generated auxiliary constants, the accepted
declarations referred to by each of the 692 theorems are exactly the ones named in its source
(§4, Appendix A): no difference for any theorem. No theorem refers to a later declaration. 688
accepted declarations are reachable from `main_theorem`; the longest reference chain has 18
declarations. The 692 theorems refer directly (again through auxiliary constants) to 6361 Mathlib
constants, 164 SimonGMT constants from 26 modules, 476 constants of Lean's `Init` and 4 of
Batteries.

**Child interfaces.** For each of the 691 accepted DAG nodes, a scratch module
(`Scratch/InterfaceCheck.lean`) states the node's frozen `lean_statement`, taken verbatim from
`dag.json`, in exactly the scope that the child comparator uses: the scope commands of
`Contract.lean` in effect at `main_theorem`, computed with `contract_scope` of
`verifier/gmt-compare.py` (`open MeasureTheory Filter Set Metric`,
`open scoped ENNReal NNReal Topology`, `namespace GMT.Ch06`, the three `open Poincare.SimonGMT…`
commands, `noncomputable section`, `end`). For each node it
(a) proves `theorem _root_.HumanizeIfaceCheck.cNNNN : (<lean_statement>) := by exact Submission.<lean_name>`,
the form of the child comparator's solution module, and
(b) elaborates `<lean_statement>` and compares it with the type of `GMT.Ch06.Submission.<lean_name>`
up to α-equivalence (`Expr` equality after instantiating metavariables), reporting `IFACE-OK`,
`IFACE-DEFEQ-ONLY` or `IFACE-MISMATCH`. The module compiled against the private build with exit status 0 in 250 s,
with no error or warning, and printed `IFACE-OK` for all 691 nodes (no `IFACE-DEFEQ-ONLY`, no
`IFACE-MISMATCH`).
So every accepted node's exact globally qualified name `GMT.Ch06.Submission.<lean_name>` exists,
and its type is syntactically the node's frozen statement.

**Acceptance records.** For every one of the 691 nodes: its last `lean-audit-vN.json` records
`comparator_passed: true` for its `candidate_commit`; `accepted-candidate.json` and
`github-issue-closure.json` (state `closed`) name the same commit; and the committed
`parent-supplied-natural-proof.md` contains, verbatim, the node's natural-language proof from the
parent decomposition whose audit accepted it. All 179 decomposed nodes and the root (180 in all)
have an accepted decomposition; in the latest accepted audit of each, all child entries (954 in
all, reused nodes counted once per parent) are marked acceptable, natural-language proof
included.

**Text identity with the accepted commits.** For each node, the text of its declaration — from the
first line of its header (attached `--` lines, `… in` modifiers and doc comment) to the end of its
proof — was compared with the text of the same declaration in the node's accepted
`candidate_commit` (read with `git show <commit>:GMT/Ch06/Submission.lean`). 686 are byte-identical.
The other five — `cmb_rb_measureRepresentation_integrableOn_coeff` (L4122),
`lpf_lli_countable_lipschitz_cover` (L10487), `fiw_tb_ext_cutoff_current` (L13363),
`constancy_mollified_functional_l1_bounded` (L17244) and `rectifiability_bf_projection_null_ae`
(L61719) — are byte-identical from the doc comment to the end of the proof, and in
`Submission.lean` the doc comment is preceded by the extra line `open scoped CompactlySupported in`
(lines 4117, 10484, 13357, 17236, 61710). These lines are not in the five declarations' own
accepted texts (none of the five candidate commits contains the line); they were introduced by the
integration commits — the merges of accepted checkpoints and the controller's "Re-merge
declarations line-merged from …" commits, on the root branch and on child integration branches
(§7). The root rounds' only Lean change, `e9e57ea4`, deletes lines only. The modifier opens Mathlib's scoped
`CompactlySupported` notation (`C_c`) for the one declaration that follows it. Outside comments,
`C_c` occurs only in `rectifiability_mass_measure_representation` (L18946), whose own accepted text
carries the same modifier; none of the five declarations uses it. The lines were left in place,
since the Lean source already passed the comparator and the task asks for no unrelated Lean change;
the interface check above shows that all five declarations have their frozen types.

**Overlay hygiene.**

- One `namespace GMT.Ch06` (line 41) and one `end GMT.Ch06` (line 69506); one
  `noncomputable section` (line 47), closed by `end` (line 367).
- Lines 16–367 of `Submission.lean` equal lines 9–360 of `Contract.lean` byte for byte, and lines 1–8
  equal `Contract.lean:1–8`; each of the 29 contract definitions occurs exactly once.
- The top-level declarations are the 29 contract definitions, the 691 accepted theorems and
  `main_theorem`, and nothing else; there are no duplicate names. (A scan for lines that begin
  with the word `theorem` also hits three doc-comment lines, 32091, 55302 and 65920.)
- Outside comments, none of the keywords `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`,
  `mutual`, `implemented_by`, `extern` and `native_decide` occurs as a word (the string `partial`
  occurs in code only inside declaration names such as `constancy_closed_kills_partial_derivatives`).
  Inside comments these strings occur only within declaration names and in the English words
  "admits"/"admitting" (lines 4851, 10097, 60796), "opaque" (line 12181), "partial" (lines 12063,
  39590, 51220, 51230) and "mutually" (line 55890).
- `Contract.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `GMT.lean` and the
  other chapters' files are byte-identical to the frozen commit `d8d46c95`. Among source and build
  files, `git diff d8d46c95 HEAD` changes only `GMT/Ch06/Submission.lean`; its other paths are the
  controller's records under `.humanize-workspace/` and this file.

## 10. reference_use

There is exactly one entry, and its source is `local-project`. The queries were run in this round
from the snapshot directory
`.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494`.

```json
[
  {
    "source": "local-project",
    "snapshot": ".humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494",
    "manifest": {
      "mode": "local-project",
      "project_commit": "d8d46c9587747dee0751a1f780fcafdba16a3886",
      "mathlib_commit": "25730c7c759d108ef87ab70af2342a196760f79d"
    },
    "queries": [
      "cat manifest.json",
      "git -C mathlib rev-parse HEAD",
      "rg -n '^(def|abbrev|structure|theorem) ' project/GMT/Ch06/Contract.lean",
      "cmp project/GMT/Ch06/Contract.lean <worktree>/GMT/Ch06/Contract.lean",
      "cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean",
      "cmp project/{lakefile.toml,lake-manifest.json,lean-toolchain,GMT.lean,GMT/Ch06/README.md} <worktree>/{same paths}",
      "rg -c sorry project/GMT/Ch06/Submission.lean",
      "rg -n 'compactness_under_mass_bounds|constancy_theorem|lipschitz_pushforward_integer_multiplicity|federer_fleming_compactness|slicing_theorem|deformation_theorem|isoperimetric_theorem|polyhedral_approximation|boundary_rectifiability|flat_convergence_iff_weak_convergence|rectifiability_theorem|integrality_of_weak_limits' project/",
      "rg -n 'theorem Submission[.]' project/",
      "rg -n '^def thickening|^def LocallyLipschitzOn|^def IsConnected|^def MeasureTheory.Measure.euclideanHausdorffMeasure|notation \"μHE' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean mathlib/Mathlib/Topology/Connected/Basic.lean mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean",
      "rg -n 'noncomputable def rieszMeasure|theorem integral_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean; rg -n '^theorem ae_tendsto_lintegral_enorm_sub_div [{]' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean; rg -n 'protected def vitaliFamily|^theorem ae_tendsto_measure_inter_div ' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean",
      "rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean; rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean; rg -n 'theorem LipschitzWith.ae_differentiableAt ' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean",
      "rg -n 'theorem Measure.measure_toMeasurable_inter ' mathlib/Mathlib/MeasureTheory/Measure/Basic.lean; rg -n 'theorem iSup_comp_le ' mathlib/Mathlib/Order/CompleteLattice/Basic.lean; rg -n 'theorem tendsto_of_subseq_tendsto ' mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean",
      "rg -n '^namespace (RealRMK|VitaliFamily|Besicovitch|Filter|MeasureTheory)' (the five Mathlib files above, and ^namespace in Mathlib/Topology/MetricSpace/Thickening.lean)",
      "rg -n 'Lemma 2.15 [(]p. 137[)]|Theorem 2.34 Constancy|Lemma 3.9 [(]p. 148[)]|Theorem 3.11 Federer|4.4–4.10 Slicing|5.3 Deformation Theorem|6.1 Isoperimetric|6.2 Weak Polyhedral|6.3 Boundary Rectifiability|Theorem 7.2 [(]p. 170[)]|8.1 Rectifiability Theorem|Theorem 8.2 [(]p. 176[)]' project/GMT/Ch06/README.md",
      "rg -n 'MassRepresentation|IntegerRectifiableCurrentData|RectifiableVarifold' project/GMT/Ch06/README.md",
      "rg -n 'theorem map_linearDependent |lemma lt_trichotomy|theorem fintype_card_le_finrank |theorem finrank_euclideanSpace_fin ' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean mathlib/Mathlib/Order/Defs/LinearOrder.lean mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean",
      "rg -n '^namespace (AlternatingMap|LinearIndependent)|^end (AlternatingMap|LinearIndependent)' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean mathlib/Mathlib/LinearAlgebra/Dimension/Finite.lean"
    ],
    "findings": [
      "manifest.json: mode local-project, project d8d46c9587747dee0751a1f780fcafdba16a3886, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; `git -C mathlib rev-parse HEAD` prints the same Mathlib commit, which is the one pinned by the candidate's lake-manifest.json.",
      "project/GMT/Ch06/Contract.lean: 30 matching lines, namely the 29 definitions — 17 at lines 43–185 (abbrev Eucl 43, CompactlyContainedOpen 50, IsRectifiableTriple 63, …, flatDistance 185) and the twelve propositions at 198, 213, 223, 234, 250, 274, 297, 308, 321, 329, 342, 352 — and `theorem main_theorem` at 362; these are the line numbers cited in §1 and §3.",
      "cmp: the snapshot's Contract.lean is byte-identical to the candidate's GMT/Ch06/Contract.lean (exit 0) and to the snapshot's own Submission.lean (exit 0), whose single `sorry` is the contract's (`rg -c sorry` = 1); lakefile.toml, lake-manifest.json, lean-toolchain, GMT.lean and GMT/Ch06/README.md are byte-identical to the candidate's (exit 0 each).",
      "No match (rg exit status 1) for the twelve root-child names anywhere in project/, nor for `theorem Submission.`: the snapshot contains no proof of this chapter, and every Lean proof used here comes from the run's accepted nodes.",
      "Mathlib definitions of §1.3 at the pinned commit: Metric.thickening at Mathlib/Topology/MetricSpace/Thickening.lean:53 (namespace Metric), LocallyLipschitzOn at Mathlib/Topology/EMetricSpace/Lipschitz.lean:72, IsConnected at Mathlib/Topology/Connected/Basic.lean:55, MeasureTheory.Measure.euclideanHausdorffMeasure at Mathlib/Geometry/Euclidean/Volume/Measure.lean:68 with the notation μHE[d] at :72.",
      "Mathlib declarations of §5 at the pinned commit: RealRMK.rieszMeasure and RealRMK.integral_rieszMeasure at RieszMarkovKakutani/Real.lean:65 and :345 (namespace RealRMK from line 52); VitaliFamily.ae_tendsto_lintegral_enorm_sub_div at Covering/Differentiation.lean:818 (namespace VitaliFamily from 87); Besicovitch.vitaliFamily and Besicovitch.ae_tendsto_measure_inter_div at Covering/Besicovitch.lean:1021 and :1105 (namespace Besicovitch from 170); IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero at Analysis/Distribution/AEEqOfIntegralContDiff.lean:205; exists_partition_approximatesLinearOn_of_hasFDerivWithinAt at MeasureTheory/Function/Jacobian.lean:255; LipschitzWith.ae_differentiableAt at Analysis/Calculus/Rademacher.lean:385; MeasureTheory.Measure.measure_toMeasurable_inter at MeasureTheory/Measure/Basic.lean:472 (namespace MeasureTheory from 73); iSup_comp_le at Order/CompleteLattice/Basic.lean:342; Filter.tendsto_of_subseq_tendsto at Order/Filter/AtTopBot/CountablyGenerated.lean:125 (namespace Filter from 28). The compiled environment (§9) confirms each full name.",
      "project/GMT/Ch06/README.md lines 84–95: the statement map pairing the twelve propositions with Simon's items and pages, as used in §1.1; lines 36–37: the SimonGMT definitions marked as not used, checked in §5.",
      "Further Mathlib declarations named in §3.12 and §5: AlternatingMap.map_linearDependent at LinearAlgebra/Alternating/Basic.lean:784 (inside namespace AlternatingMap, lines 499–815), lt_trichotomy at Order/Defs/LinearOrder.lean:102, LinearIndependent.fintype_card_le_finrank at LinearAlgebra/Dimension/Finite.lean:157 (namespace LinearIndependent, lines 149–184), finrank_euclideanSpace_fin at Analysis/InnerProductSpace/PiL2.lean:205.",
      "SimonGMT is not part of the snapshot. Its declarations cited in §1.3 and §5 were located in the pinned package lake-packages-25730c7c/simongmt (git HEAD 2b3663083f3fe399b6296fb8eaee52169170e197, the revision in lake-manifest.json)."
    ],
    "use": "Contract identity and the absence of prior proofs in the snapshot; the line numbers of the frozen definitions; the file and line of the Mathlib definitions and theorems cited in §1.3 and §5 at the pinned revision; the README statement map. No snapshot declaration was copied. Compatibility holds because the pins are identical, and every reused declaration is re-checked by the comparator's kernel replay with the axiom check (§9)."
  }
]
```

No network source was used. The mathematics of this document is the frozen contract and the
accepted, reviewed declarations of the run; Simon's book is cited only to name the conjuncts and,
in §0, for Remark 8.3(2) (`book/chapter-06.txt`, lines 2317–2318).

## 11. Citations

- L. Simon, *Introduction to Geometric Measure Theory*, 2014 Tsinghua lecture notes,
  <https://web.stanford.edu/class/math285/ts-gmt.pdf>; Chapter 6, printed pp. 131–180. Workspace
  copies: `book/chapter-06.txt`, `book/sources/chapter-06-source.txt`. Item and page numbers follow
  `GMT/Ch06/README.md`.
- Mathlib, revision `25730c7c759d108ef87ab70af2342a196760f79d`, and SimonGMT (`Poincare.SimonGMT`,
  package `simongmt`), revision `2b3663083f3fe399b6296fb8eaee52169170e197`, as cited in §1.3 and §5.
- The accepted declarations of the run and their reviewed natural-language proofs, cited by name
  in §3 and Appendix A; theorem issues
  <https://github.com/ZhengyangZhang06/gmt-formalize/issues/N> and solution PRs
  <https://github.com/ZhengyangZhang06/gmt-formalize/pull/N>. The literature that those proofs cite
  is cited there.

## Appendix A. Catalogue of the 691 accepted declarations

Every accepted DAG node of the run, cited by its exact Lean name `GMT.Ch06.Submission.<name>`.
Nothing here restates a statement or a proof: the statement of each declaration is its Lean type at
the line given (`L…`, the line of the `theorem` keyword in `GMT/Ch06/Submission.lean`), which equals
the node's frozen `lean_statement` (§9), and its proof is the reviewed natural-language proof cited.
The entries are grouped by the root child whose DAG subtree contains the node (the first two
components of the node id; a node reused by several parents is listed once, under its own id), and
ordered by line within each group. Each entry gives:

- the DAG node; its theorem issue `#i` (<https://github.com/ZhengyangZhang06/gmt-formalize/issues/i>)
  and solution PR `#p` (<https://github.com/ZhengyangZhang06/gmt-formalize/pull/p>); its accepted
  candidate commit;
- **proof**: the committed copy of its reviewed natural-language proof,
  `.humanize-workspace/20261011t144224z-6e4735dbca/<parent>/children/<node>/parent-supplied-natural-proof.md`,
  given as `<parent>/children/<node>`; it was accepted by the audit of its parent's decomposition
  (`nodes/<parent>/decomposition-audit-vN.json`, version given);
- **names**: the accepted declarations its Lean proof names, in file order (they equal the
  references read from the compiled environment, §9; the converse relation "named by" is obtained by
  inverting these lists, and the root children's users are in §4);
- *unused* if it is not reachable from `main_theorem` (three declarations, §6).

### A.1 Subtree `root.compactness_mass_bounds-a1` (13 declarations)

- **`cmb_exists_compactly_contained_exhaustion`** (L401) — node `root.compactness_mass_bounds-a1.exhaustion-a1`; #687; PR #1628; candidate `cb89cc7f436b`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-exhaustion-a1` (audit v1); names: —.
- **`cmb_abs_apply_le_of_massOn_le`** (L561) — node `root.compactness_mass_bounds-a1.mass_bound-a1`; #689; PR #1632; candidate `ba202ac0407b`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-mass-bound-a1` (audit v1); names: —.
- **`cmb_covector_eq_sum_coord_smul_wedge`** (L2558) — node `root.compactness_mass_bounds-a1.covector_expansion-a1`; #691; PR #1655; candidate `6c6b4b2753e8`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-covector-expansion-a1` (audit v1); names: —.
- **`cmb_rb_abs_euclideanCovectorCoordinate_le`** (L2617) — node `root.compactness_mass_bounds-a1.repr_bound-a1.coord_bound-a1`; #1771; PR #2240; candidate `bc4ced077707`; proof `root-compactness-mass-bounds-a1-repr-bound-a1/children/root-compactness-mass-bounds-a1-repr-bound-a1-coord-bound-a1` (audit v1); names: —.
- **`cmb_exists_countable_dense_testForms`** (L3869) — node `root.compactness_mass_bounds-a1.testform_separable-a1`; #693; PR #1757; candidate `bfaf075e7525`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-testform-separable-a1` (audit v1); names: —.
- **`cmb_exists_testForm_uniform_approx`** (L4035) — node `root.compactness_mass_bounds-a1.mollify-a1`; #695; PR #994; candidate `26d9d850fd23`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-mollify-a1` (audit v1); names: —.
- **`cmb_rb_measureRepresentation_integrableOn_coeff`** (L4122) — node `root.compactness_mass_bounds-a1.repr_bound-a1.coeff_integrable-a1`; #1783; PR #2262; candidate `3cd72266f61a`; proof `root-compactness-mass-bounds-a1-repr-bound-a1/children/root-compactness-mass-bounds-a1-repr-bound-a1-coeff-integrable-a1` (audit v1); names: —.
- **`cmb_rb_integral_coeff_pairing_bound`** (L4151) — node `root.compactness_mass_bounds-a1.repr_bound-a1.pairing_bound-a1`; #1791; PR #2341; candidate `230f547c2f70`; proof `root-compactness-mass-bounds-a1-repr-bound-a1/children/root-compactness-mass-bounds-a1-repr-bound-a1-pairing-bound-a1` (audit v1); names: `cmb_rb_abs_euclideanCovectorCoordinate_le`.
- **`cmb_rb_covectorEuclideanNorm_add_le`** (L6179) — node `root.compactness_mass_bounds-a1.repr_bound-a1.norm_add_le-a1`; #1776; PR #2182; candidate `21d072dc936c`; proof `root-compactness-mass-bounds-a1-repr-bound-a1/children/root-compactness-mass-bounds-a1-repr-bound-a1-norm-add-le-a1` (audit v1); names: —.
- **`cmb_measureRepresentation_continuous_bound`** (L9888) — node `root.compactness_mass_bounds-a1.repr_bound-a1`; #699; PR #2562; candidate `5caba5008111`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-repr-bound-a1` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `cmb_covector_eq_sum_coord_smul_wedge`, `cmb_exists_testForm_uniform_approx`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `cmb_rb_integral_coeff_pairing_bound`, `cmb_rb_covectorEuclideanNorm_add_le`.
- **`cmb_tendsto_integral_of_weaklyConvergesOn`** (L9980) — node `root.compactness_mass_bounds-a1.continuous_form_conv-a1`; #701; PR #3928; candidate `7fe585673d4e`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-continuous-form-conv-a1` (audit v1); names: `cmb_exists_testForm_uniform_approx`, `cmb_measureRepresentation_continuous_bound`.
- **`cmb_exists_weakly_convergent_subseq`** (L68932) — node `root.compactness_mass_bounds-a1.weak_subseq-a1`; #697; PR #1630; candidate `00678bdb7796`; proof `root-compactness-mass-bounds-a1/children/root-compactness-mass-bounds-a1-weak-subseq-a1` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`, `cmb_exists_countable_dense_testForms`.
- **`compactness_under_mass_bounds`** (L69081) — node `root.compactness_mass_bounds-a1`; #314; PR #4238; candidate `ec8c9ac424f6`; proof `root/children/root-compactness-mass-bounds-a1` (audit v3); names: `cmb_tendsto_integral_of_weaklyConvergesOn`, `cmb_exists_weakly_convergent_subseq`.

### A.2 Subtree `root.constancy-a1` (18 declarations)

- **`constancy_mollifier_iteratedFDeriv_norm_le_integral`** (L9648) — node `root.constancy-a1.mollifier_derivative_bound-a1`; #966; PR #1657; candidate `d6285a34810d`; proof `root-constancy-a1/children/root-constancy-a1-mollifier-derivative-bound-a1` (audit v1); names: —.
- **`constancy_closed_kills_partial_derivatives`** (L16987) — node `root.constancy-a1.closed_kills_partials-a1`; #964; PR #1645; candidate `469f013363ea`; proof `root-constancy-a1/children/root-constancy-a1-closed-kills-partials-a1` (audit v1); names: —.
- **`constancy_topForm_scalar_reduction`** (L17096) — node `root.constancy-a1.local_on_balls-a1.scalar_reduction-a1`; #2564; PR #3579; candidate `0104810ac99c`; proof `root-constancy-a1-local-on-balls-a1/children/root-constancy-a1-local-on-balls-a1-scalar-reduction-a1` (audit v2); names: —.
- **`constancy_mollified_functional_l1_bounded`** (L17244) — node `root.constancy-a1.local_on_balls-a1.mollified_l1_bound-a1`; #2582; PR #3492; candidate `43af4e895902`; proof `root-constancy-a1-local-on-balls-a1/children/root-constancy-a1-local-on-balls-a1-mollified-l1-bound-a1` (audit v2); names: —.
- **`constancy_mdc_weak_partials_vanish`** (L17376) — node `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_identity-a1`; #3574; PR #4199; candidate `6403f9e1601b`; proof `root-constancy-a1-local-on-balls-a1-density-constancy-a1/children/root-constancy-a1-local-on-balls-a1-density-constancy-a1-weak-identity-a1` (audit v1); names: —.
- **`constancy_mdc_smooth_approx_identity_ae_tendsto`** (L41192) — node `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1`; #3577; PR #4208; candidate `2219dd324b47`; proof `root-constancy-a1-local-on-balls-a1-density-constancy-a1/children/root-constancy-a1-local-on-balls-a1-density-constancy-a1-smooth-appro-6a720fda87` (audit v1); names: —.
- **`constancy_mdc_ae_const_of_weak_partials_vanish`** (L41351) — node `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_constancy_ball-a1`; #3582; PR #4284; candidate `8b7f3a46c915`; proof `root-constancy-a1-local-on-balls-a1-density-constancy-a1/children/root-constancy-a1-local-on-balls-a1-density-constancy-a1-weak-constancy-ball-a1` (audit v1); names: `constancy_mdc_smooth_approx_identity_ae_tendsto`.
- **`constancy_mollified_density_const`** (L41441) — node `root.constancy-a1.local_on_balls-a1.density_constancy-a1`; #2595; PR #4440; candidate `babfd43a1976`; proof `root-constancy-a1-local-on-balls-a1/children/root-constancy-a1-local-on-balls-a1-density-constancy-a1` (audit v2); names: `constancy_mdc_weak_partials_vanish`, `constancy_mdc_ae_const_of_weak_partials_vanish`.
- **`constancy_local_of_mollified_const`** (L41467) — node `root.constancy-a1.local_on_balls-a1.mollifier_limit-a1`; #2604; PR #3732; candidate `4a6e0cee1f77`; proof `root-constancy-a1-local-on-balls-a1/children/root-constancy-a1-local-on-balls-a1-mollifier-limit-a1` (audit v2); names: —.
- **`constancy_riesz_bounded_density_of_dominated_additive`** (L41537) — node `root.constancy-a1.riesz_l1_dual-a1.dominated_bounded_density-a1`; #2467; PR #3107; candidate `0e9b0c22da46`; proof `root-constancy-a1-riesz-l1-dual-a1/children/root-constancy-a1-riesz-l1-dual-a1-dominated-bounded-density-a1` (audit v1); names: —.
- **`constancy_riesz_eq_integral_mul_of_indicator_eq`** (L41677) — node `root.constancy-a1.riesz_l1_dual-a1.extend_from_indicators-a1`; #2473; PR #3288; candidate `6c2f3038a34e`; proof `root-constancy-a1-riesz-l1-dual-a1/children/root-constancy-a1-riesz-l1-dual-a1-extend-from-indicators-a1` (audit v1); names: —.
- **`constancy_riesz_l1_dual_bounded_density`** (L41762) — node `root.constancy-a1.riesz_l1_dual-a1`; #965; PR #3481; candidate `471cfdd5be90`; proof `root-constancy-a1/children/root-constancy-a1-riesz-l1-dual-a1` (audit v1); names: `constancy_riesz_bounded_density_of_dominated_additive`, `constancy_riesz_eq_integral_mul_of_indicator_eq`.
- **`constancy_approx_identity_iteratedFDeriv_tendstoUniformly`** (L41797) — node `root.constancy-a1.mollifier_derivative_convergence-a1`; #967; PR #1629; candidate `933d7e87b08b`; proof `root-constancy-a1/children/root-constancy-a1-mollifier-derivative-convergence-a1` (audit v1); names: —.
- **`constancy_local_on_balls`** (L41865) — node `root.constancy-a1.local_on_balls-a1`; #968; PR #4605; candidate `0427214b3aca`; proof `root-constancy-a1/children/root-constancy-a1-local-on-balls-a1` (audit v1); names: `constancy_mollifier_iteratedFDeriv_norm_le_integral`, `constancy_topForm_scalar_reduction`, `constancy_mollified_functional_l1_bounded`, `constancy_mollified_density_const`, `constancy_local_of_mollified_const`, `constancy_riesz_l1_dual_bounded_density`, `constancy_approx_identity_iteratedFDeriv_tendstoUniformly`.
- **`constancy_exists_topTestForm_integral_eq_one`** (L41961) — node `root.constancy-a1.globalize-a1.unit_top_form-a1`; #1383; PR #2232; candidate `26804ee35e55`; proof `root-constancy-a1-globalize-a1/children/root-constancy-a1-globalize-a1-unit-top-form-a1` (audit v1); names: —.
- **`constancy_testFormOn_eq_finset_sum_subordinate`** (L42007) — node `root.constancy-a1.globalize-a1.pou_decomposition-a1`; #1384; PR #2252; candidate `5c4bf4ca7a1b`; proof `root-constancy-a1-globalize-a1/children/root-constancy-a1-globalize-a1-pou-decomposition-a1` (audit v1); names: —.
- **`constancy_of_local_constancy`** (L42065) — node `root.constancy-a1.globalize-a1`; #970; PR #2605; candidate `151404f8d9c3`; proof `root-constancy-a1/children/root-constancy-a1-globalize-a1` (audit v1); names: `constancy_exists_topTestForm_integral_eq_one`, `constancy_testFormOn_eq_finset_sum_subordinate`.
- **`constancy_theorem`** (L42133) — node `root.constancy-a1`; #316; PR #4888; candidate `b4bbd87115fa`; proof `root/children/root-constancy-a1` (audit v3); names: `constancy_closed_kills_partial_derivatives`, `constancy_local_on_balls`, `constancy_of_local_constancy`.

### A.3 Subtree `root.lipschitz_pushforward_im-a1` (76 declarations)

- **`lpf_pi_simple_unit_facts`** (L7929) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.simple_unit_facts-a1`; #2550; PR #3498; candidate `a6e4e44adce8`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-simple-unit-facts-a1` (audit v3); names: —.
- **`lpf_pi_induced_orientation`** (L7988) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.induced_orientation-a1`; #2576; PR #3533; candidate `5553df438424`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-induced-o-eb73d1c7d5` (audit v3); names: `lpf_pi_simple_unit_facts`.
- **`lpf_pi_jacobian_local_bound`** (L8073) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.jacobian_local_bound-a1`; #2594; PR #3485; candidate `c19a8600fe53`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-jacobian-751fc80a27` (audit v3); names: —.
- **`lpf_pi_measurability`** (L8136) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.measurability-a1`; #2602; PR #3540; candidate `a2a69a08f815`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-measurability-a1` (audit v3); names: —.
- **`lpf_pi_signed_fibre_sum`** (L8161) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.signed_fibre_sum-a1`; #2621; PR #3559; candidate `db4569b324be`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-signed-fibre-sum-a1` (audit v3); names: —.
- **`lpf_pi_covector_finiteDimensional`** (L8283) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.covector_finite_dimensional-a1`; #2635; PR #3548; candidate `662fd8919e80`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-covector-12d2ee8455` (audit v3); names: —.
- **`lpf_pi_chart_image_rectifiable`** (L8312) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.chart_image_rectifiable-a1`; #2640; PR #3491; candidate `b0fce8642c84`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-chart-ima-e2d21dad87` (audit v3); names: —.
- **`lpf_pi_source_charts`** (L8344) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1`; #2655; PR #3895; candidate `01ef99809f95`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-source-charts-a1` (audit v3); names: `lpf_pi_induced_orientation`.
- **`lpf_pi_image_density`** (L8494) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1`; #2665; PR #3751; candidate `393a8daba3f9`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-image-density-a1` (audit v3); names: `lpf_pi_signed_fibre_sum`, `lpf_pi_covector_finiteDimensional`.
- **`lpf_pi_im_of_chart_density`** (L8980) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.im_of_chart_density-a1`; #2687; PR #3910; candidate `441bdc5bad6a`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-im-of-cha-999423cb08` (audit v3); names: `lpf_pi_simple_unit_facts`, `lpf_pi_chart_image_rectifiable`.
- **`lpf_rsn_null_diff_support_of_local_null`** (L9159) — node `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.support_null_reduction-a1`; #1179; PR #1961; candidate `3f6ddbcb5a98`; proof `root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1-support-2d52519b95` (audit v1); names: —.
- **`lpf_rsn_covector_separating_family`** (L9183) — node `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.covector_separating_family-a1`; #1180; PR #1948; candidate `9d4dd6d3f7b2`; proof `root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1-covector-84c64c5778` (audit v1); names: —.
- **`lpf_rsn_weighted_fundamental_lemma`** (L9215) — node `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.weighted_fundamental_lemma-a1`; #1181; PR #2011; candidate `57d868d3730c`; proof `root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1-weighted-41fa1bc99c` (audit v1); names: —.
- **`lpf_rsn_local_null`** (L9247) — node `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.local_null_on_vanishing_open-a1`; #1182; PR #2111; candidate `b405c044b9ac`; proof `root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1-local-nu-434a84464e` (audit v1); names: `lpf_rsn_covector_separating_family`, `lpf_rsn_weighted_fundamental_lemma`.
- **`lpf_lli_inner_compact_approx`** (L9590) — node `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.inner_compact_approx-a1`; #980; PR #1634; candidate `d24e9e7b54d3`; proof `root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1/children/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f` (audit v1); names: —.
- **`lpf_simple_nvector_algebra`** (L9768) — node `root.lipschitz_pushforward_im-a1.simple_nvector_algebra-a1`; #718; PR #1635; candidate `d57bd3700c22`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-simple-nvector-algebra-a1` (audit v1); names: —.
- **`lpf_lli_countable_lipschitz_cover`** (L10487) — node `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.countable_lipschitz_cover-a1`; #979; PR #1627; candidate `6941b70febfe`; proof `root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1/children/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-countable-dc002d2f60` (audit v1); names: —.
- **`lpf_locally_lipschitz_image`** (L10516) — node `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1`; #723; PR #2036; candidate `e74e195a1134`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1` (audit v1); names: `lpf_lli_inner_compact_approx`, `lpf_lli_countable_lipschitz_cover`.
- **`lpf_raf_lla_disjoint_lipschitz_pieces`** (L10550) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1.disjoint_lipschitz_pieces-a1`; #1906; PR #2201; candidate `06f425e14008`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-2809c506b6/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-1721d1b1cf` (audit v1); names: `lpf_lli_countable_lipschitz_cover`.
- **`lpf_wtc_ae_zero_density_off_set`** (L11274) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.zero_density_off_set-a1`; #1274; PR #2200; candidate `12d217bba2a4`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e` (audit v1); names: —.
- **`lpf_rectifiable_support_null`** (L13320) — node `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1`; #720; PR #2267; candidate `b0d12af0ae3d`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1` (audit v1); names: `lpf_rsn_null_diff_support_of_local_null`, `lpf_rsn_local_null`, `lpf_simple_nvector_algebra`.
- **`lpf_raf_chart_preimage_null`** (L18493) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_preimage_null-a1`; #1072; PR #1472; candidate `9080c178c7e2`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-pr-b8935c5987` (audit v1); names: —.
- **`lpf_raf_jacobian_identity`** (L20823) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.jacobian_identity-a1`; #1075; PR #1414; candidate `b382b2aba005`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-jacobian-937dbe37df` (audit v1); names: —.
- **`lpf_raf_chart_jacobian_ae`** (L20897) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_jacobian_ae-a1`; #1077; PR #1895; candidate `4aee0e083b8d`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ja-6ec72b8d86` (audit v1); names: `lpf_raf_chart_preimage_null`, `lpf_raf_jacobian_identity`.
- **`lpf_raf_fiber_sum_glue`** (L20941) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.fiber_sum_glue-a1`; #1069; PR #1419; candidate `066cbc3bc143`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-fiber-sum-glue-a1` (audit v1); names: —.
- **`lpf_raf_local_lipschitz_area`** (L20988) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1`; #1070; PR #2567; candidate `4b36491e59d4`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-2809c506b6` (audit v1); names: `lpf_raf_lla_disjoint_lipschitz_pieces`, `lpf_raf_fiber_sum_glue`.
- **`lpf_raf_chart_change_of_variables`** (L21048) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`; #1073; PR #2746; candidate `9fc44225b304`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708` (audit v1); names: `lpf_raf_chart_preimage_null`, `lpf_raf_local_lipschitz_area`.
- **`lpf_raf_chart_area_formula`** (L21148) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_area_formula-a1`; #1079; PR #2839; candidate `75b8b2de8736`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ar-4d841a9e74` (audit v1); names: `lpf_raf_local_lipschitz_area`, `lpf_raf_chart_change_of_variables`.
- **`lpf_ccr_hasDerivAt_line_of_comp`** (L21211) — node `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.line_deriv_comp-a1`; #2445; PR #3171; candidate `32fbf107157c`; proof `root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/children/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-line-deriv-comp-a1` (audit v2); names: —.
- **`lpf_wtc_cat_fderiv_lower_bound`** (L21259) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1`; #2028; PR #2617; candidate `8cfbc487a3d1`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9` (audit v1); names: —.
- **`lpf_raf_pushforward_enorm_aemeasurable`** (L23236) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.pushforward_enorm_aemeasurable-a1`; #1080; PR #2010; candidate `3210ebf9ba88`; proof `root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-pushforw-aeac6d58da` (audit v1); names: —.
- **`lpf_pi_local_finite_weight`** (L23260) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.local_finite_weight-a1`; #2607; PR #3541; candidate `fe5e41020e2a`; proof `root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1-local-fin-7a72ceaf7e` (audit v3); names: `lpf_pi_jacobian_local_bound`.
- **`lpf_c1r_lusin_closed`** (L23322) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.lusin_closed-a1`; #1896; PR #2539; candidate `b7b6c0271146`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-5203a6228f` (audit v1); names: —.
- **`lpf_c1r_egoroff_closed`** (L23418) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.egoroff_closed-a1`; #1910; PR #2656; candidate `7919071b797d`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-1292e882bb` (audit v1); names: —.
- **`lpf_c1r_uniform_remainder`** (L23491) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.uniform_remainder-a1`; #1921; PR #2905; candidate `38a84674ea5a`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b87e24bae1` (audit v1); names: `lpf_c1r_egoroff_closed`.
- **`lpf_c1r_whitney_extension`** (L23646) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1`; #1932; PR #2715; candidate `8b631fd6fe8f`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-a7c2d31d99` (audit v1); names: —.
- **`lpf_c1_approximation_real`** (L24399) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`; #1146; PR #3246; candidate `f7a35d70d995`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-b45cce92e1` (audit v1); names: `lpf_c1r_lusin_closed`, `lpf_c1r_uniform_remainder`, `lpf_c1r_whitney_extension`.
- **`lpf_c1_approximation_eucl`** (L24443) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_eucl-a1`; #1147; PR #3446; candidate `eff6bc809135`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab` (audit v1); names: `lpf_c1_approximation_real`.
- **`lpf_c1_local_antilipschitz`** (L24496) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_local_antilipschitz-a1`; #1148; PR #1953; candidate `961fc1089331`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-fa0007faad` (audit v1); names: —.
- **`lpf_lipschitz_localization`** (L24536) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.lipschitz_localization-a1`; #1149; PR #2107; candidate `e9f440ddea21`; proof `root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-lip-66ca1b75a5` (audit v1); names: —.
- **`lpf_lipschitz_c1_immersion_pieces`** (L24577) — node `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`; #726; PR #3642; candidate `682c558f0382`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1` (audit v1); names: `lpf_c1_approximation_eucl`, `lpf_c1_local_antilipschitz`, `lpf_lipschitz_localization`.
- **`lpf_countably_rectifiable_c1_cover`** (L24675) — node `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1`; #728; PR #4028; candidate `4f96ac678110`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1` (audit v1); names: `lpf_lipschitz_c1_immersion_pieces`.
- **`lpf_wtc_cat_rescaled_integral_tendsto`** (L24923) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.rescaled_integral_tendsto-a1`; #2045; PR #2628; candidate `f2f1db7607fa`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8b5bd63a08` (audit v1); names: —.
- **`lpf_wtc_cat_gram_jacobian_continuous`** (L25043) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.gram_jacobian_continuous-a1`; #2076; PR #2613; candidate `3639f75e8f12`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-90b97c9ccd` (audit v1); names: —.
- **`lpf_wtc_wtt_blowup_integral_split`** (L25053) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.blowup_integral_split-a1`; #2098; PR #2683; candidate `405169da3a03`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-c5b5d534a9` (audit v2); names: —.
- **`lpf_wtc_wtt_continuity_error_vanishes`** (L25118) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.continuity_error_vanishes-a1`; #2112; PR #2933; candidate `6a3a02bbf289`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-d7655a2590` (audit v2); names: —.
- **`lpf_wtc_wtt_remainder_vanishes`** (L25211) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.remainder_vanishes-a1`; #2127; PR #2662; candidate `178784030758`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-86d7f9d6d1` (audit v2); names: —.
- **`lpf_wtc_blowup_setIntegral_image`** (L25297) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.blowup_change_of_variables-a1`; #1264; PR #2230; candidate `8389acdfdd73`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6` (audit v1); names: —.
- **`lpf_wtc_chart_image_measurable_locally_finite`** (L25340) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_image_measurable_finite-a1`; #1266; PR #1564; candidate `a2f705665fe4`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-1f4173ea67` (audit v1); names: —.
- **`lpf_wtc_caf_lipschitz_localization`** (L25382) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1.lipschitz_localization-a1`; #2378; PR #2937; candidate `86fd6e41a7a2`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8d37e9b354/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-66b189fcaa` (audit v1); names: —.
- **`lpf_wtc_caf_signed_of_lintegral`** (L25414) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1.signed_of_lintegral-a1`; #2388; PR #2998; candidate `f573bdec80e2`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8d37e9b354/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-241b9c6992` (audit v1); names: —.
- **`lpf_wtc_chart_area_formula`** (L25495) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1`; #1268; PR #3314; candidate `db9ef3e1c6f5`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8d37e9b354` (audit v1); names: `lpf_wtc_caf_lipschitz_localization`, `lpf_wtc_caf_signed_of_lintegral`.
- **`lpf_wtc_chart_approx_tangent`** (L25575) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1`; #1271; PR #3447; candidate `f2c64f39999e`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8ee6679021` (audit v1); names: `lpf_wtc_cat_fderiv_lower_bound`, `lpf_wtc_cat_rescaled_integral_tendsto`, `lpf_wtc_cat_gram_jacobian_continuous`, `lpf_wtc_blowup_setIntegral_image`, `lpf_wtc_chart_area_formula`.
- **`lpf_wtc_lusin_compact_pieces`** (L25634) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.lusin_compact_pieces-a1`; #1273; PR #2283; candidate `5b63f318a7c2`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d` (audit v1); names: —.
- **`lpf_wtc_density_bound_of_tangent`** (L25799) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.density_bound_of_tangent-a1`; #1275; PR #2805; candidate `90ea33e84620`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-dens-cc0a8b304d` (audit v1); names: `lpf_wtc_blowup_setIntegral_image`.
- **`lpf_wtc_tangent_transfer`** (L33856) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.tangent_transfer-a1`; #1276; PR #2806; candidate `b493cac78ec5`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-tang-d8e31ab936` (audit v1); names: `lpf_wtc_blowup_setIntegral_image`.
- **`lpf_wtc_weighted_tangent_transfer`** (L33996) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1`; #1277; PR #3396; candidate `ad4fb1886aef`; proof `root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-weig-08162f69d6` (audit v1); names: `lpf_wtc_wtt_blowup_integral_split`, `lpf_wtc_wtt_continuity_error_vanishes`, `lpf_wtc_wtt_remainder_vanishes`, `lpf_wtc_blowup_setIntegral_image`, `lpf_wtc_density_bound_of_tangent`.
- **`lpf_tde_mcd_single_chart`** (L39623) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.single_chart-a1`; #3289; PR #3737; candidate `0de2b8a211fb`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-f939a87b7a` (audit v1); names: `lpf_wtc_cat_fderiv_lower_bound`.
- **`lpf_tde_mcd_countable_glue`** (L39683) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.countable_glue-a1`; #3300; PR #3742; candidate `e54c806e72bd`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-37e9d69edf` (audit v1); names: —.
- **`lpf_tde_continuous_left_inverse`** (L39711) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.continuous_left_inverse-a1`; #2444; PR #3089; candidate `d9f5b44bfc78`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-co-7afa0393aa` (audit v1); names: —.
- **`lpf_tde_measurable_chart_differential`** (L39764) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`; #2451; PR #3944; candidate `e23946e21500`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655` (audit v1); names: `lpf_tde_mcd_single_chart`, `lpf_tde_mcd_countable_glue`, `lpf_tde_continuous_left_inverse`.
- **`lpf_weighted_tangent_on_c1_chart`** (L39786) — node `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`; #731; PR #3558; candidate `f9637977f9e7`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1` (audit v1); names: `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_chart_approx_tangent`, `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`.
- **`lpf_ccr_ae_pullback`** (L39909) — node `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1`; #2422; PR #3035; candidate `841085c6a9d7`; proof `root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/children/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-pullback-a1` (audit v2); names: `lpf_raf_chart_preimage_null`.
- **`lpf_ccr_ae_differentiableAt_comp`** (L40402) — node `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_diff_comp-a1`; #2431; PR #3543; candidate `f8ca7a783787`; proof `root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/children/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1-ae-diff-comp-a1` (audit v2); names: `lpf_lli_countable_lipschitz_cover`.
- **`lpf_chart_chain_rule`** (L40437) — node `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1`; #735; PR #3692; candidate `a42b48e8b29b`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1` (audit v1); names: `lpf_ccr_hasDerivAt_line_of_comp`, `lpf_weighted_tangent_on_c1_chart`, `lpf_ccr_ae_pullback`, `lpf_ccr_ae_differentiableAt_comp`.
- **`lpf_rectifiable_area_formula`** (L45312) — node `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`; #740; PR #4280; candidate `2acb4ed7dac3`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1` (audit v1); names: `lpf_simple_nvector_algebra`, `lpf_locally_lipschitz_image`, `lpf_raf_chart_jacobian_ae`, `lpf_raf_fiber_sum_glue`, `lpf_raf_chart_area_formula`, `lpf_raf_pushforward_enorm_aemeasurable`, `lpf_countably_rectifiable_c1_cover`, `lpf_chart_chain_rule`.
- **`lpf_pushforward_integrality`** (L45407) — node `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`; #741; PR #4444; candidate `33923222a994`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1` (audit v1); names: `lpf_pi_measurability`, `lpf_pi_source_charts`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_simple_nvector_algebra`, `lpf_locally_lipschitz_image`, `lpf_rectifiable_support_null`, `lpf_pi_local_finite_weight`, `lpf_lipschitz_c1_immersion_pieces`, `lpf_countably_rectifiable_c1_cover`, `lpf_weighted_tangent_on_c1_chart`, `lpf_chart_chain_rule`, `lpf_rectifiable_area_formula`.
- **`lpf_tde_chart_directional_deriv`** (L45433) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_directional_deriv-a1`; #2407; PR #2964; candidate `3dcce9d73b9f`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-4f8efa2336` (audit v1); names: —.
- **`lpf_tde_uniform_lipschitz_near_compact`** (L45490) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.uniform_lipschitz_near_compact-a1`; #2420; PR #2991; candidate `35e5274c045b`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-un-f5c04592aa` (audit v1); names: —.
- **`lpf_tde_chart_nondiff_image_null`** (L45505) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_nondiff_image_null-a1`; #2430; PR #3163; candidate `019ad40a7219`; proof `root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-34870e43f7` (audit v1); names: —.
- **`lpf_tangential_differential_exists`** (L45694) — node `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`; #732; PR #4195; candidate `f55db39d5141`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1` (audit v1); names: `lpf_countably_rectifiable_c1_cover`, `lpf_tde_measurable_chart_differential`, `lpf_weighted_tangent_on_c1_chart`, `lpf_tde_chart_directional_deriv`, `lpf_tde_uniform_lipschitz_near_compact`, `lpf_tde_chart_nondiff_image_null`.
- **`lpf_pic_current_of_dominated_density`** (L45784) — node `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.current_of_dominated_density-a1`; #1065; PR #1916; candidate `52afef6d786b`; proof `root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/children/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1-current-of-7b4042b0e0` (audit v1); names: —.
- **`lpf_pic_density_aestronglyMeasurable`** (L45873) — node `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_measurable-a1`; #1066; PR #1626; candidate `1caba2144799`; proof `root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/children/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1-density-measurable-a1` (audit v1); names: —.
- **`lpf_pic_density_dominated`** (L45898) — node `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_dominated-a1`; #1067; PR #1878; candidate `be6570f329d4`; proof `root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/children/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1-density-dominated-a1` (audit v1); names: —.
- **`lpf_pushforward_is_current`** (L46182) — node `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1`; #738; PR #2537; candidate `4cf8ae752e5f`; proof `root-lipschitz-pushforward-im-a1/children/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1` (audit v1); names: `lpf_rectifiable_support_null`, `lpf_pic_current_of_dominated_density`, `lpf_pic_density_aestronglyMeasurable`, `lpf_pic_density_dominated`.
- **`lipschitz_pushforward_integer_multiplicity`** (L46209) — node `root.lipschitz_pushforward_im-a1`; #319; PR #4707; candidate `3289485ca49a`; proof `root/children/root-lipschitz-pushforward-im-a1` (audit v3); names: `lpf_pushforward_integrality`, `lpf_tangential_differential_exists`, `lpf_pushforward_is_current`.

### A.4 Subtree `root.slicing-a1` (143 declarations)

- **`slicing_im_st_mf_slice_null_measurable`** (L373) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_null_measurable-a1`; #4051; PR #4697; candidate `8962fd5666e0`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-879e5793fd` (audit v1); names: —.
- **`slicing_im_si_coarea_null_sets`** (L4199) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.coarea_null-a1`; #3825; PR #4435; candidate `977af2fe7e51`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-coarea-null-a1` (audit v1); names: —.
- **`slicing_mb_pointwise_cutoff_tendsto`** (L4259) — node `root.slicing-a1.slice_mass_bound-a1.pointwise-a1.cutoff_tendsto-a1`; #2242; PR #2976; candidate `012eb78d57e0`; proof `root-slicing-a1-slice-mass-bound-a1-pointwise-a1/children/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1` (audit v1); names: —.
- **`slicing_mb_pointwise_liminf_bound`** (L4317) — node `root.slicing-a1.slice_mass_bound-a1.pointwise-a1.liminf_bound-a1`; #2254; PR #2919; candidate `7b74e18da55e`; proof `root-slicing-a1-slice-mass-bound-a1-pointwise-a1/children/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-liminf-bound-a1` (audit v1); names: —.
- **`slicing_mb_cutoff`** (L4369) — node `root.slicing-a1.slice_mass_bound-a1.cutoff-a1`; #1869; PR #2205; candidate `b8b3c6bde72a`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-cutoff-a1` (audit v5); names: —.
- **`slicing_mb_cdb_grad_lintegral_le`** (L4505) — node `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.grad_lintegral-a1`; #2219; PR #2963; candidate `4b14fb2e31e2`; proof `root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1-grad-lintegral-a1` (audit v1); names: —.
- **`slicing_mb_cdb_band_measure_tendsto`** (L4565) — node `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.band_limit-a1`; #2233; PR #2981; candidate `9ff4cacca1b5`; proof `root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1-band-limit-a1` (audit v1); names: —.
- **`slicing_mb_cdb_multiplier_integral_tendsto`** (L4623) — node `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.multiplier_limit-a1`; #2243; PR #2985; candidate `73831a4dd0cc`; proof `root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1-multiplier-limit-a1` (audit v1); names: —.
- **`slicing_mb_sa_mollify_lipschitz_close`** (L4647) — node `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_close-a1`; #2185; PR #2833; candidate `0db2d9bb718d`; proof `root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/children/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-close-a1` (audit v1); names: —.
- **`slicing_mb_sa_mollify_lipschitz_hasFDerivAt`** (L4683) — node `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_fderiv-a1`; #2202; PR #2944; candidate `fd43c997849f`; proof `root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/children/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1` (audit v1); names: —.
- **`slicing_mb_sa_mollifier_exists`** (L4724) — node `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollifier-a1`; #2168; PR #2965; candidate `9735e2124d87`; proof `root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/children/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1` (audit v1); names: —.
- **`slicing_mb_smooth_approx`** (L4746) — node `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`; #1874; PR #3315; candidate `e27012d9d09a`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1` (audit v5); names: `slicing_mb_sa_mollify_lipschitz_close`, `slicing_mb_sa_mollify_lipschitz_hasFDerivAt`, `slicing_mb_sa_mollifier_exists`.
- **`slicing_im_coarea_cc_small_lip_partition`** (L4814) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.small_lip_partition-a1`; #3894; PR #4604; candidate `5a9e3fad9b64`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critical-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critica-5fce30ee24` (audit v1); names: —.
- **`slicing_im_coarea_cc_null_of_small_majorants`** (L4856) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.null_of_small_majorants-a1`; #3901; PR #4494; candidate `4dd0c03d8f6b`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critical-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critica-037f0b58df` (audit v1); names: —.
- **`slicing_im_coarea_eil_near_optimal_cover`** (L4899) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.near_optimal_cover-a1`; #4036; PR #4698; candidate `0f6e5c4d010a`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-7f6e8f0ff4` (audit v1); names: —.
- **`slicing_im_coarea_eil_liminf_cover_bound`** (L4927) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.liminf_cover_bound-a1`; #4045; PR #4678; candidate `05b86f9232cb`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-fbf6b6e4af` (audit v1); names: —.
- **`slicing_im_coarea_eil_cover_majorant`** (L4949) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.cover_majorant-a1`; #4054; PR #4700; candidate `c0d786c5e4b0`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-8bffc3f0b1` (audit v1); names: —.
- **`slicing_im_st_mf_slice_integrable`** (L4992) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_integrable-a1`; #4060; PR #4706; candidate `079d76f82b5f`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-14d8526cf7` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`.
- **`slicing_im_st_ae_transfer`** (L5060) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.ae_transfer-a1`; #3390; PR #4011; candidate `dec06e62f162`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-ae-transfer-a1` (audit v1); names: —.
- **`slicing_im_st_mf_contraction_lipschitz`** (L5090) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.contraction_lipschitz-a1`; #4068; PR #4691; candidate `034bfcd73baa`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-b15bd2c3bf` (audit v1); names: —.
- **`slicing_im_st_mf_slice_orientation_aesm`** (L5126) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_orientation_aesm-a1`; #4072; PR #4945; candidate `9defddc28bf9`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-ae11d089ba` (audit v1); names: `slicing_im_st_mf_contraction_lipschitz`.
- **`slicing_im_st_measure_fields`** (L5162) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1`; #3395; PR #5136; candidate `deae3dc4ec25`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1` (audit v1); names: `slicing_im_st_mf_slice_null_measurable`, `slicing_im_st_mf_slice_integrable`, `slicing_im_st_ae_transfer`, `slicing_im_st_mf_slice_orientation_aesm`.
- **`slicing_im_st_cd_c1c_singular_compression`** (L5187) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.singular_compression-a1`; #4874; PR #5073; candidate `a7a07277ab92`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-fbaf41bab5/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-a7e748327a` (audit v1); names: —.
- **`smr_ci_coord_sum_smul_wedge`** (L10040) — node `root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_sum_wedge-a1`; #2611; PR #3028; candidate `1b431e814455`; proof `root-slicing-a1-mass-representation-a1-covector-isometry-a1/children/root-slicing-a1-mass-representation-a1-covector-isometry-a1-coord-sum-wedge-a1` (audit v2); names: —.
- **`smr_ci_norm_eq_sqrt_sum_coord_sq`** (L10076) — node `root.slicing-a1.mass_representation-a1.covector_isometry-a1.norm_coord-a1`; #2636; PR #3167; candidate `a1716c42aeab`; proof `root-slicing-a1-mass-representation-a1-covector-isometry-a1/children/root-slicing-a1-mass-representation-a1-covector-isometry-a1-norm-coord-a1` (audit v2); names: —.
- **`slicing_ru_integrableOn_apply`** (L10757) — node `root.slicing-a1.representation_unique-a1.local_integrability-a1`; #945; PR #1621; candidate `0b6482f55907`; proof `root-slicing-a1-representation-unique-a1/children/root-slicing-a1-representation-unique-a1-local-integrability-a1` (audit v1); names: —.
- **`slicing_ru_smooth_to_continuous`** (L10787) — node `root.slicing-a1.representation_unique-a1.smooth_to_continuous-a1`; #946; PR #1592; candidate `e038063b301d`; proof `root-slicing-a1-representation-unique-a1/children/root-slicing-a1-representation-unique-a1-smooth-to-continuous-a1` (audit v1); names: —.
- **`slicing_ru_continuous_to_bounded`** (L10873) — node `root.slicing-a1.representation_unique-a1.continuous_to_bounded-a1`; #948; PR #1457; candidate `a49e975113ed`; proof `root-slicing-a1-representation-unique-a1/children/root-slicing-a1-representation-unique-a1-continuous-to-bounded-a1` (audit v1); names: —.
- **`slicing_ru_covector_expansion`** (L11215) — node `root.slicing-a1.representation_unique-a1.covector_expansion-a1`; #949; PR #1441; candidate `182a24a66909`; proof `root-slicing-a1-representation-unique-a1/children/root-slicing-a1-representation-unique-a1-covector-expansion-a1` (audit v1); names: —.
- **`slicing_im_st_cd_c1c_critical_image_null`** (L13234) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.critical_image_null-a1`; #4877; PR #5110; candidate `ca0d69f9608b`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-fbaf41bab5/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-7c233f5f47` (audit v1); names: `slicing_im_st_cd_c1c_singular_compression`.
- **`slicing_mb_lb_extDeriv_smul`** (L15604) — node `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.extderiv_leibniz-a1`; #2177; PR #3036; candidate `d90a235b0e2f`; proof `root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-extderiv-leibniz-a1` (audit v1); names: —.
- **`slicing_mb_lb_smul_testForm`** (L15612) — node `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.smul_test_form-a1`; #2193; PR #2864; candidate `1faaa7c7259b`; proof `root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-smul-test-form-a1` (audit v1); names: —.
- **`slicing_mb_lb_wedge_testForm`** (L15623) — node `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.wedge_test_form-a1`; #2211; PR #2883; candidate `1c55ec485bf9`; proof `root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-wedge-test-form-a1` (audit v1); names: —.
- **`slicing_mb_lb_repr_bound`** (L15650) — node `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.repr_bound-a1`; #2222; PR #2987; candidate `9bc99e092729`; proof `root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-repr-bound-a1` (audit v1); names: —.
- **`slicing_mb_wn_sq_sum_eq_factorial_mul`** (L15662) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.count_sq_sum-a1`; #2379; PR #2926; candidate `6c884a2c7528`; proof `root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-count-sq-sum-a1` (audit v1); names: —.
- **`slicing_mb_wn_sq_sum_onb_invariant`** (L15741) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.parseval_sq_sum-a1`; #2390; PR #2966; candidate `f12646af114b`; proof `root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-parseval-sq-sum-a1` (audit v1); names: —.
- **`slicing_mb_wn_norm_sq_eq_onb_sum`** (L15785) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.onb_norm_sq-a1`; #2399; PR #3271; candidate `66289299bcea`; proof `root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-onb-norm-sq-a1` (audit v1); names: `slicing_mb_wn_sq_sum_eq_factorial_mul`, `slicing_mb_wn_sq_sum_onb_invariant`.
- **`slicing_mb_wn_adapted_onb`** (L15802) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_onb-a1`; #2405; PR #2979; candidate `40b4cdead896`; proof `root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-adapted-onb-a1` (audit v1); names: —.
- **`slicing_mb_wn_adapted_sum_le`** (L15841) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_sum_le-a1`; #2419; PR #3027; candidate `1f87f778d505`; proof `root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-adapted-sum-le-a1` (audit v1); names: —.
- **`slicing_mb_wedge_norm_le`** (L15897) — node `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`; #1871; PR #3429; candidate `34503163c994`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1` (audit v5); names: `slicing_mb_wn_norm_sq_eq_onb_sum`, `slicing_mb_wn_adapted_onb`, `slicing_mb_wn_adapted_sum_le`.
- **`slicing_mb_leibniz_bound`** (L15916) — node `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`; #1881; PR #3561; candidate `fdd90dcb0712`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1` (audit v5); names: `slicing_mb_lb_extDeriv_smul`, `slicing_mb_lb_smul_testForm`, `slicing_mb_lb_wedge_testForm`, `slicing_mb_lb_repr_bound`, `slicing_mb_wedge_norm_le`.
- **`slicing_im_ll_mollify`** (L15961) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.mollify-a1`; #3629; PR #4409; candidate `58e6d1ca65a6`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-mollify-a1` (audit v1); names: —.
- **`slicing_im_ll_multiplier_tendsto`** (L16029) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.multiplier_limit-a1`; #3636; PR #4424; candidate `175d7806c319`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-mu-fe115cf2ee` (audit v1); names: —.
- **`slicing_im_creg_box_integrand_measurable`** (L16071) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.integrand_measurable-a1`; #4870; PR #5071; candidate `4a45b7920398`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-56efcb3c65` (audit v1); names: —.
- **`slicing_im_creg_jacobian_identity`** (L16109) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.jacobian-a1`; #4115; PR #4832; candidate `46c9d53ecea6`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-fd47d6c0a6` (audit v1); names: —.
- **`slicing_im_creg_lintegral_cons`** (L16214) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.tonelli-a1`; #4121; PR #4796; candidate `21ca221e7302`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-33a64f6eb8` (audit v1); names: —.
- **`slicing_im_creg_straightening`** (L16238) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.straighten-a1`; #4135; PR #4829; candidate `7a8b65c256aa`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-3781bc1432` (audit v1); names: —.
- **`slicing_im_creg_local_to_global`** (L16355) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.cover-a1`; #4150; PR #4768; candidate `f17042c51b0e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-310b812607` (audit v1); names: —.
- **`slicing_im_coarea_glue`** (L16427) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.glue-a1`; #3394; PR #4029; candidate `8723e7ff4f22`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-glue-a1` (audit v1); names: —.
- **`slicing_im_ll_smooth_leibniz`** (L16464) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.smooth_identity-a1`; #3641; PR #4333; candidate `0374472720fd`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-sm-9d4b939639` (audit v1); names: `slicing_mb_lb_extDeriv_smul`, `slicing_mb_lb_smul_testForm`, `slicing_mb_lb_wedge_testForm`.
- **`slicing_mb_cutoff_defect_bound`** (L16513) — node `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1`; #1883; PR #3684; candidate `6070b3614438`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-cutoff-defect-bound-a1` (audit v5); names: `slicing_mb_cdb_grad_lintegral_le`, `slicing_mb_cdb_band_measure_tendsto`, `slicing_mb_cdb_multiplier_integral_tendsto`, `slicing_mb_smooth_approx`, `slicing_mb_leibniz_bound`.
- **`slicing_mb_pointwise`** (L16605) — node `root.slicing-a1.slice_mass_bound-a1.pointwise-a1`; #1888; PR #3886; candidate `fdaebfd29faa`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-pointwise-a1` (audit v5); names: `slicing_mb_pointwise_cutoff_tendsto`, `slicing_mb_pointwise_liminf_bound`, `slicing_mb_cutoff`, `slicing_mb_cutoff_defect_bound`.
- **`slicing_mb_dm_distribution_mono_rightcont`** (L16670) — node `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.distribution_regularity-a1`; #2189; PR #3069; candidate `31f0d299e59a`; proof `root-slicing-a1-slice-mass-bound-a1-density-majorant-a1/children/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-distribution-c375423177` (audit v1); names: —.
- **`slicing_mb_dm_lowerLeftDini_measurable`** (L16703) — node `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_measurable-a1`; #2204; PR #2894; candidate `630c339ebee4`; proof `root-slicing-a1-slice-mass-bound-a1-density-majorant-a1/children/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-dini-measurable-a1` (audit v1); names: —.
- **`slicing_mb_dm_lintegral_lowerLeftDini_le`** (L16763) — node `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_lintegral_le-a1`; #2217; PR #2958; candidate `f077c7d5152d`; proof `root-slicing-a1-slice-mass-bound-a1-density-majorant-a1/children/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-dini-lintegral-le-a1` (audit v1); names: —.
- **`slicing_mb_dm_density_le_lowerLeftDini`** (L16848) — node `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.density_le_dini-a1`; #2231; PR #2924; candidate `79fa90c23a79`; proof `root-slicing-a1-slice-mass-bound-a1-density-majorant-a1/children/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-density-le-dini-a1` (audit v1); names: —.
- **`slicing_mb_density_majorant`** (L16952) — node `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`; #1894; PR #3401; candidate `5ea978433c6f`; proof `root-slicing-a1-slice-mass-bound-a1/children/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1` (audit v5); names: `slicing_mb_dm_distribution_mono_rightcont`, `slicing_mb_dm_lowerLeftDini_measurable`, `slicing_mb_dm_lintegral_lowerLeftDini_le`, `slicing_mb_dm_density_le_lowerLeftDini`.
- **`slicing_representation_unique`** (L17445) — node `root.slicing-a1.representation_unique-a1`; #666; PR #2077; candidate `48beb763c9e5`; proof `root-slicing-a1/children/root-slicing-a1-representation-unique-a1` (audit v1); names: `slicing_ru_integrableOn_apply`, `slicing_ru_smooth_to_continuous`, `slicing_ru_continuous_to_bounded`, `slicing_ru_covector_expansion`.
- **`slicing_im_si_borel_density`** (L18534) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.borel_density-a1`; #3830; PR #4471; candidate `1f74b5c5bd29`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-borel-density-a1` (audit v1); names: `fiw_ims_tt_unit_bound`.
- **`slicing_im_si_signed_coarea`** (L18671) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1`; #3835; PR #4484; candidate `95342e38669e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-signed-coarea-a1` (audit v1); names: —.
- **`slicing_im_si_slice_ae_transfer`** (L18768) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.slice_transfer-a1`; #3841; PR #4453; candidate `9d0e74d0c981`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-slice-24e9ce6459` (audit v1); names: —.
- **`slicing_im_si_left_lebesgue_point`** (L18822) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.left_lebesgue-a1`; #3844; PR #4415; candidate `bdf3439a7899`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-left-lebesgue-a1` (audit v1); names: —.
- **`slicing_im_si_cutoff_tangential_gradient`** (L18848) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1`; #3848; PR #4430; candidate `586f960d4585`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-cutof-828585ced7` (audit v1); names: —.
- **`smr_ufd_unit_coord_field`** (L21289) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.unit_coord_field-a1`; #2154; PR #2865; candidate `71e312bb1c69`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-unit-coord-field-a1` (audit v1); names: —.
- **`smr_ufd_cl_inner_compact`** (L21333) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1.inner_compact-a1`; #2862; PR #3482; candidate `21abad67dc04`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-lusin-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-l-73bd629320` (audit v1); names: —.
- **`smr_ufd_cl_vector_lusin`** (L21376) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1.vector_lusin-a1`; #2869; PR #3630; candidate `dd9361e25ccd`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-lusin-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-l-08c0542bed` (audit v1); names: —.
- **`smr_ufd_compact_lusin_set`** (L21492) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1`; #2162; PR #3912; candidate `a73776b666a3`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-compact-lusin-a1` (audit v1); names: `smr_ufd_cl_inner_compact`, `smr_ufd_cl_vector_lusin`.
- **`smr_ufd_ball_tietze`** (L21517) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.ball_tietze-a1`; #2174; PR #2858; candidate `e70632735cee`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-ball-tietze-a1` (audit v1); names: —.
- **`smr_ufd_small_cutoff`** (L21598) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.small_cutoff-a1`; #2188; PR #2982; candidate `75510cd11e79`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-small-cutoff-a1` (audit v1); names: —.
- **`smr_ufd_integral_lower_bound`** (L21658) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1.integral_lower_bound-a1`; #2203; PR #2983; candidate `9cfc88355a08`; proof `root-slicing-a1-mass-representation-a1-unit-form-density-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1-integral-9d081869a2` (audit v1); names: —.
- **`smr_ci_covector_eq_zero_of_coord`** (L21704) — node `root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_vanish-a1`; #2622; PR #3033; candidate `133aac9a37fc`; proof `root-slicing-a1-mass-representation-a1-covector-isometry-a1/children/root-slicing-a1-mass-representation-a1-covector-isometry-a1-coord-vanish-a1` (audit v2); names: —.
- **`smr_covector_coord_isometry`** (L21729) — node `root.slicing-a1.mass_representation-a1.covector_isometry-a1`; #1322; PR #3424; candidate `eef9547811f6`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-covector-isometry-a1` (audit v1); names: `smr_ci_coord_sum_smul_wedge`, `smr_ci_norm_eq_sqrt_sum_coord_sq`, `smr_ci_covector_eq_zero_of_coord`.
- **`smr_exists_testForm_uniform_approx`** (L21770) — node `root.slicing-a1.mass_representation-a1.testform_approx-a1`; #1323; PR #2229; candidate `f8173b174e2d`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-testform-approx-a1` (audit v1); names: —.
- **`smr_exists_continuous_extension`** (L21858) — node `root.slicing-a1.mass_representation-a1.continuous_extension-a1`; #1324; PR #3532; candidate `a5ecd9fcb037`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-continuous-extension-a1` (audit v1); names: `smr_covector_coord_isometry`, `smr_exists_testForm_uniform_approx`.
- **`smr_ofReal_integral_le_massOn`** (L22065) — node `root.slicing-a1.mass_representation-a1.continuous_mass_bound-a1`; #1328; PR #3702; candidate `627ca1da6bbc`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-continuous-mass-bound-a1` (audit v1); names: `smr_covector_coord_isometry`, `smr_exists_testForm_uniform_approx`.
- **`smr_rb_transfer_functional`** (L22175) — node `root.slicing-a1.mass_representation-a1.riesz_borel-a1.transfer_functional-a1`; #2073; PR #2727; candidate `accc0298da56`; proof `root-slicing-a1-mass-representation-a1-riesz-borel-a1/children/root-slicing-a1-mass-representation-a1-riesz-borel-a1-transfer-functional-a1` (audit v1); names: —.
- **`smr_rb_borel_riesz_sigma_compact`** (L22260) — node `root.slicing-a1.mass_representation-a1.riesz_borel-a1.borel_riesz-a1`; #2095; PR #2974; candidate `cdfc95dc55d0`; proof `root-slicing-a1-mass-representation-a1-riesz-borel-a1/children/root-slicing-a1-mass-representation-a1-riesz-borel-a1-borel-riesz-a1` (audit v1); names: —.
- **`smr_rb_pushforward_subtype`** (L22536) — node `root.slicing-a1.mass_representation-a1.riesz_borel-a1.pushforward-a1`; #2109; PR #2863; candidate `64646e28b9da`; proof `root-slicing-a1-mass-representation-a1-riesz-borel-a1/children/root-slicing-a1-mass-representation-a1-riesz-borel-a1-pushforward-a1` (audit v1); names: —.
- **`smr_riesz_borel_euclidean`** (L22593) — node `root.slicing-a1.mass_representation-a1.riesz_borel-a1`; #1325; PR #3247; candidate `b25ecc25b937`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-riesz-borel-a1` (audit v1); names: `smr_rb_transfer_functional`, `smr_rb_borel_riesz_sigma_compact`, `smr_rb_pushforward_subtype`.
- **`smr_riesz_continuous_forms`** (L22637) — node `root.slicing-a1.mass_representation-a1.riesz_forms-a1`; #1326; PR #3653; candidate `7b60523bff83`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-riesz-forms-a1` (audit v1); names: `smr_covector_coord_isometry`, `smr_riesz_borel_euclidean`.
- **`smr_restriction_isCurrent`** (L22732) — node `root.slicing-a1.mass_representation-a1.restriction_current-a1`; #1327; PR #2143; candidate `a5855f5953ef`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-restriction-current-a1` (audit v1); names: —.
- **`smr_exists_unit_form_gt`** (L22814) — node `root.slicing-a1.mass_representation-a1.unit_form_density-a1`; #1329; PR #4098; candidate `b5389008e353`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-unit-form-density-a1` (audit v1); names: `smr_ufd_unit_coord_field`, `smr_ufd_compact_lusin_set`, `smr_ufd_ball_tietze`, `smr_ufd_small_cutoff`, `smr_ufd_integral_lower_bound`, `smr_covector_coord_isometry`.
- **`smr_restriction_massOn_eq`** (L22874) — node `root.slicing-a1.mass_representation-a1.restriction_mass-a1`; #1331; PR #4338; candidate `57be985b01b2`; proof `root-slicing-a1-mass-representation-a1/children/root-slicing-a1-mass-representation-a1-restriction-mass-a1` (audit v1); names: `smr_ofReal_integral_le_massOn`, `smr_exists_unit_form_gt`.
- **`slicing_mass_representation`** (L22918) — node `root.slicing-a1.mass_representation-a1`; #664; PR #4788; candidate `59c4caf12f87`; proof `root-slicing-a1/children/root-slicing-a1-mass-representation-a1` (audit v1); names: `smr_exists_continuous_extension`, `smr_riesz_continuous_forms`, `smr_restriction_isCurrent`, `smr_restriction_massOn_eq`.
- **`slicing_exists`** (L22959) — node `root.slicing-a1.slice_exists-a1`; #669; PR #4871; candidate `420db8a1d391`; proof `root-slicing-a1/children/root-slicing-a1-slice-exists-a1` (audit v1); names: `slicing_mass_representation`.
- **`slicing_support_subset`** (L22986) — node `root.slicing-a1.slice_support-a1`; #672; PR #2163; candidate `13f3f1e557e5`; proof `root-slicing-a1/children/root-slicing-a1-slice-support-a1` (audit v1); names: `slicing_representation_unique`.
- **`slicing_mass_bound`** (L23080) — node `root.slicing-a1.slice_mass_bound-a1`; #676; PR #4967; candidate `47b64c8c933b`; proof `root-slicing-a1/children/root-slicing-a1-slice-mass-bound-a1` (audit v1); names: `slicing_mb_pointwise`, `slicing_mb_density_majorant`, `slicing_representation_unique`, `slicing_mass_representation`.
- **`slicing_im_ll_tangent_dual_field`** (L23142) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangent_field-a1`; #3647; PR #4366; candidate `f3a3c5910cef`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-0cf2aa97e2` (audit v1); names: —.
- **`slicing_im_ll_gws_smooth_dense`** (L40561) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_dense-a1`; #4417; PR #4924; candidate `c278f023560d`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584` (audit v1); names: —.
- **`slicing_im_coarea_c1_approx`** (L43963) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1`; #3405; PR #4363; candidate `c7050c55826e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-c1-approx-a1` (audit v1); names: `lpf_c1r_lusin_closed`, `lpf_c1r_uniform_remainder`, `lpf_c1r_whitney_extension`.
- **`slicing_im_coarea_chart_cover`** (L44011) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_cover-a1`; #3410; PR #4662; candidate `de9ec3b03cc1`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-cover-a1` (audit v1); names: `lpf_c1_approximation_eucl`, `lpf_c1_local_antilipschitz`.
- **`slicing_im_ll_twl_cie_weighted_transfer`** (L44125) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.weighted_transfer-a1`; #4904; PR #5095; candidate `b66ff150c0b5`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-24d92287e3` (audit v1); names: —.
- **`slicing_im_ll_twl_cie_jacobian_measurable`** (L44166) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.jacobian_measurable-a1`; #4909; PR #5208; candidate `379410958dd0`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eb34e93b3d` (audit v1); names: —.
- **`slicing_im_tg_cc_lipschitz_range_c1_cover`** (L44178) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.lipschitz_range_cover-a1`; #4039; PR #4669; candidate `db66a30d9176`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-81832218ac` (audit v1); names: `lpf_c1_approximation_eucl`.
- **`slicing_im_tg_cc_contDiff_range_chart_cover`** (L44216) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1`; #4049; PR #4778; candidate `118fa606212e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-afbca4d3f5` (audit v1); names: `lpf_c1_local_antilipschitz`.
- **`slicing_im_tg_c1_chart_cover`** (L44449) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1`; #3324; PR #4886; candidate `7349133a5f3b`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-1b3924ced5` (audit v1); names: `slicing_im_tg_cc_lipschitz_range_c1_cover`, `slicing_im_tg_cc_contDiff_range_chart_cover`.
- **`slicing_im_st_cd_c1_cover`** (L44494) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1`; #4207; PR #5139; candidate `7ce14591c40a`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-fbaf41bab5` (audit v2); names: `slicing_im_st_cd_c1c_critical_image_null`, `lpf_lipschitz_c1_immersion_pieces`.
- **`slicing_im_st_cd_c1_pieces_of_lipschitzOn`** (L44571) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.lipschitz_on_c1_pieces-a1`; #4211; PR #4766; candidate `17098070bab1`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-53709af5bc` (audit v2); names: `lpf_c1_approximation_real`.
- **`slicing_im_st_lsc_kernel_frame`** (L44595) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.kernel_frame-a1`; #4118; PR #4769; candidate `942be35ef94e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-3d005c6960` (audit v1); names: —.
- **`slicing_im_st_lsc_c1_extension`** (L44662) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.c1_extension-a1`; #4123; PR #4751; candidate `829465a8a234`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-9852bcd3c7` (audit v1); names: —.
- **`slicing_im_st_lsc_local_graph`** (L44700) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1`; #4136; PR #4839; candidate `45ba0d8e0ccd`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-5e2e069e1a` (audit v1); names: `slicing_im_st_lsc_kernel_frame`, `slicing_im_st_lsc_c1_extension`.
- **`slicing_im_coarea_eil_unnormalized`** (L44888) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.unnormalized-a1`; #4067; PR #4849; candidate `cd8c8dbf850d`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1-4fd0674b34` (audit v1); names: `slicing_im_coarea_eil_near_optimal_cover`, `slicing_im_coarea_eil_liminf_cover_bound`, `slicing_im_coarea_eil_cover_majorant`.
- **`slicing_im_coarea_eilenberg`** (L44953) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1`; #3389; PR #4896; candidate `bda07ad44078`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-eilenberg-a1` (audit v1); names: `slicing_im_coarea_eil_unnormalized`.
- **`slicing_im_creg_box_bulk`** (L44989) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.bulk-a1`; #4859; PR #5069; candidate `93feccc4b332`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-cf6d5a08c5` (audit v1); names: `lpf_raf_chart_change_of_variables`.
- **`slicing_im_creg_box_slice_area`** (L45061) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.slice_area-a1`; #4866; PR #5079; candidate `754abeed9103`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-8f6f377b03` (audit v1); names: `lpf_raf_chart_change_of_variables`.
- **`slicing_im_tg_weighted_tangent_chart`** (L45184) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1`; #3334; PR #4292; candidate `a812942bc581`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-df4d668443` (audit v1); names: `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_chart_approx_tangent`, `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`.
- **`slicing_im_st_weighted_tangent_on_c1_chart`** (L45248) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.weighted_tangent_chart-a1`; #3404; PR #4325; candidate `04a776d4541f`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-weighte-15b86ca257` (audit v1); names: `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_chart_approx_tangent`, `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`.
- **`slicing_im_tg_cg_gram_field`** (L45556) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1`; #4059; PR #4694; candidate `659bd72cb30a`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-c1a07ddeb6` (audit v1); names: —.
- **`slicing_im_tg_cg_borel_transfer`** (L45631) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.borel_transfer-a1`; #4066; PR #4645; candidate `908c000bd33e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-f154422599` (audit v1); names: —.
- **`slicing_im_tg_line_deriv_of_comp`** (L45653) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.line_deriv-a1`; #3344; PR #3929; candidate `4d089a08226f`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-5d0f3ce1cd` (audit v1); names: —.
- **`slicing_im_st_chart_data`** (L45965) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1`; #3407; PR #5163; candidate `402bc07ae520`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-data-a1` (audit v1); names: `lpf_ccr_hasDerivAt_line_of_comp`, `slicing_im_st_cd_c1_cover`, `slicing_im_st_cd_c1_pieces_of_lipschitzOn`, `slicing_im_st_weighted_tangent_on_c1_chart`.
- **`slicing_im_coarea_chart_tangent`** (L46072) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_tangent-a1`; #3422; PR #4371; candidate `7ecb6efce6fd`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-tangent-a1` (audit v1); names: `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_chart_approx_tangent`, `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`.
- **`slicing_im_coarea_line_deriv`** (L46132) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.line_deriv-a1`; #3428; PR #3948; candidate `b1189c5f5e41`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-line-deriv-a1` (audit v1); names: —.
- **`slicing_im_creg_box_coarea`** (L46231) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`; #4143; PR #5115; candidate `bdc372057ab8`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1-box-a1` (audit v1); names: `slicing_im_creg_box_integrand_measurable`, `slicing_im_creg_jacobian_identity`, `slicing_im_creg_lintegral_cons`, `slicing_im_creg_box_bulk`, `slicing_im_creg_box_slice_area`.
- **`slicing_im_tg_chart_gradient`** (L46331) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1`; #3351; PR #4835; candidate `a51770cbdc26`; proof `root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1-661abdfbe7` (audit v1); names: `lpf_wtc_cat_fderiv_lower_bound`, `lpf_tde_chart_nondiff_image_null`, `slicing_im_tg_cg_gram_field`, `slicing_im_tg_cg_borel_transfer`, `slicing_im_tg_line_deriv_of_comp`.
- **`slicing_im_tangential_gradient`** (L46411) — node `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`; #2474; PR #4985; candidate `dfb10e73f9e3`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1` (audit v1); names: `slicing_im_tg_c1_chart_cover`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_tg_chart_gradient`.
- **`slicing_im_coarea_pieces`** (L46517) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.pieces-a1`; #3440; PR #4830; candidate `e3cb17916c0d`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-pieces-a1` (audit v1); names: `slicing_im_coarea_c1_approx`, `slicing_im_coarea_chart_cover`, `slicing_im_coarea_chart_tangent`, `slicing_im_coarea_line_deriv`.
- **`slicing_im_st_lsc_tangent_range`** (L46673) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.tangent_range-a1`; #4145; PR #4759; candidate `fd6cb8de53c6`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-ddfc31667c` (audit v1); names: `lpf_wtc_cat_fderiv_lower_bound`.
- **`slicing_im_st_level_set_charts`** (L46731) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`; #3419; PR #4916; candidate `54d4b4edc3e9`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817` (audit v1); names: `slicing_im_st_lsc_local_graph`, `slicing_im_st_lsc_tangent_range`.
- **`slicing_im_st_slice_geometry`** (L46813) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.slice_geometry-a1`; #3426; PR #5177; candidate `9a27cfc863f3`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-slice-geometry-a1` (audit v1); names: `slicing_im_st_ae_transfer`, `slicing_im_st_measure_fields`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_st_chart_data`, `slicing_im_st_level_set_charts`.
- **`slicing_im_coarea_chart_critical`** (L46978) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1`; #3443; PR #4942; candidate `cf62f63388be`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-critical-a1` (audit v1); names: `slicing_im_coarea_cc_small_lip_partition`, `slicing_im_coarea_cc_null_of_small_majorants`, `slicing_im_coarea_eilenberg`.
- **`slicing_im_coarea_chart_regular`** (L47062) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`; #3444; PR #5141; candidate `abc1acd4f4d7`; proof `root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1` (audit v1); names: `slicing_im_creg_straightening`, `slicing_im_creg_local_to_global`, `slicing_im_creg_box_coarea`.
- **`slicing_im_coarea`** (L47113) — node `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1`; #2483; PR #5158; candidate `d33ec3b4a054`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1` (audit v1); names: `slicing_im_coarea_glue`, `slicing_im_coarea_eilenberg`, `slicing_im_coarea_pieces`, `slicing_im_coarea_chart_critical`, `slicing_im_coarea_chart_regular`.
- **`slicing_im_st_interior_product`** (L62471) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.interior_product-a1`; #3437; PR #4017; candidate `c005e98f97c3`; proof `root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-interio-e2ad70d40d` (audit v1); names: `fiw_ims_frame_sign`.
- **`slicing_im_slice_triple`** (L62571) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`; #2492; PR #5202; candidate `ec722690b696`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1` (audit v1); names: `slicing_im_st_ae_transfer`, `slicing_im_st_measure_fields`, `slicing_im_st_slice_geometry`, `slicing_im_coarea`, `slicing_im_st_interior_product`.
- **`slicing_im_ll_twl_partition_tendsto`** (L62616) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.partition_tendsto-a1`; #4552; PR #4968; candidate `2153cd87992b`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-2aebefd87c` (audit v1); names: —.
- **`slicing_im_ll_twl_chart_integral_eq`** (L62682) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1`; #4559; PR #5235; candidate `73e7a45462ac`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a` (audit v1); names: `lpf_raf_chart_change_of_variables`, `slicing_im_ll_twl_cie_weighted_transfer`, `slicing_im_ll_twl_cie_jacobian_measurable`.
- **`slicing_im_ll_twl_coefficient_field`** (L62709) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.coefficient_field-a1`; #4575; PR #5292; candidate `60c90f12cfef`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-c96b654981` (audit v1); names: `lpf_wtc_cat_fderiv_lower_bound`, `lpf_tde_continuous_left_inverse`, `lpf_ccr_ae_pullback`, `slicing_im_ll_twl_chart_integral_eq`.
- **`slicing_im_ll_twl_chart_hasFDerivAt`** (L62778) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_has_fderiv_at-a1`; #4585; PR #4986; candidate `9bb46c57022b`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-07cd9b6e07` (audit v1); names: `lpf_ccr_ae_pullback`.
- **`slicing_im_ll_twl_chart_representation`** (L62829) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_representation-a1`; #4592; PR #5303; candidate `583322f91d4e`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-ebabccdb31` (audit v1); names: `slicing_im_ll_twl_chart_integral_eq`, `slicing_im_ll_twl_coefficient_field`, `slicing_im_ll_twl_chart_hasFDerivAt`.
- **`slicing_im_ll_gws_pairing_bound`** (L62880) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.pairing_bound-a1`; #4387; PR #4875; candidate `50d79ad7aedd`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-1436a9332e` (audit v1); names: —.
- **`slicing_im_ll_gws_lipschitz_ibp`** (L62917) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.lipschitz_ibp-a1`; #4397; PR #4914; candidate `50ef52b3e09d`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-26915888ff` (audit v1); names: —.
- **`slicing_im_ll_gws_smooth_tendsto`** (L63024) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_tendsto-a1`; #4405; PR #4949; candidate `c64806cd2cf9`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-37749b6fd4` (audit v1); names: `slicing_im_ll_gws_lipschitz_ibp`.
- **`slicing_im_ll_gradient_weak_star`** (L66420) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1`; #3657; PR #5016; candidate `18e839d9d650`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-b207eb8151` (audit v1); names: `slicing_im_ll_gws_smooth_dense`, `slicing_im_ll_gws_pairing_bound`, `slicing_im_ll_gws_smooth_tendsto`.
- **`slicing_im_ll_tangential_weak_limit`** (L66466) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`; #3668; PR #5343; candidate `7fa5d56cb674`; proof `root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-cf904f7089` (audit v1); names: `lpf_countably_rectifiable_c1_cover`, `lpf_weighted_tangent_on_c1_chart`, `slicing_im_ll_twl_partition_tendsto`, `slicing_im_ll_twl_chart_representation`, `slicing_im_ll_gradient_weak_star`.
- **`slicing_im_lipschitz_leibniz`** (L66540) — node `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`; #2506; PR #5386; candidate `a67b3e1b87f5`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1` (audit v1); names: `slicing_im_ll_mollify`, `slicing_im_ll_multiplier_tendsto`, `slicing_im_ll_smooth_leibniz`, `slicing_im_ll_tangent_dual_field`, `slicing_im_ll_tangential_weak_limit`.
- **`slicing_im_slice_identity`** (L66589) — node `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`; #2519; PR #5413; candidate `ef8a14137aad`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1` (audit v1); names: `slicing_im_si_coarea_null_sets`, `slicing_mb_pointwise_cutoff_tendsto`, `slicing_im_si_borel_density`, `slicing_im_si_signed_coarea`, `slicing_im_si_slice_ae_transfer`, `slicing_im_si_left_lebesgue_point`, `slicing_im_si_cutoff_tangential_gradient`, `slicing_im_coarea`, `slicing_im_lipschitz_leibniz`.
- **`slicing_im_td_countable_seq_dense`** (L66707) — node `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.seq_dense-a1`; #3591; PR #4367; candidate `53a4da30f2c2`; proof `root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1-2c59dae3a5` (audit v1); names: —.
- **`slicing_im_td_current_tendsto`** (L66813) — node `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.current_tendsto-a1`; #3597; PR #4315; candidate `c633e337cd22`; proof `root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1-0081e898fe` (audit v1); names: —.
- **`slicing_im_testform_determining`** (L66840) — node `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1`; #2532; PR #4543; candidate `8392d5e440a2`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`.
- **`slicing_im_tau_current`** (L66864) — node `root.slicing-a1.slice_integer_multiplicity-a1.tau_current-a1`; #2543; PR #3757; candidate `5a70d03c4185`; proof `root-slicing-a1-slice-integer-multiplicity-a1/children/root-slicing-a1-slice-integer-multiplicity-a1-tau-current-a1` (audit v1); names: `ltg_tau_integrable`, `fiw_ims_tt_unit_bound`.
- **`slicing_integer_multiplicity_ae`** (L66941) — node `root.slicing-a1.slice_integer_multiplicity-a1`; #678; PR #5560; candidate `8f220efff156`; proof `root-slicing-a1/children/root-slicing-a1-slice-integer-multiplicity-a1` (audit v1); names: `slicing_im_tangential_gradient`, `slicing_im_slice_triple`, `slicing_im_slice_identity`, `slicing_im_testform_determining`, `slicing_im_tau_current`.
- **`slicing_theorem`** (L66972) — node `root.slicing-a1`; #322; PR #5777; candidate `f27fd6da7e82`; proof `root/children/root-slicing-a1` (audit v3); names: `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `slicing_integer_multiplicity_ae`.

### A.5 Subtree `root.deformation-a1` (123 declarations)

- **`deformation_retraction_dini_segment`** (L860) — node `root.deformation-a1.retraction-a1.dini_segment-a1`; #2488; PR #3340; candidate `9d7e85746c1d`; proof `root-deformation-a1-retraction-a1/children/root-deformation-a1-retraction-a1-dini-segment-a1` (audit v2); names: —.
- **`dph_sa_mollify_lipschitz`** (L5443) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.mollify-a1`; #5464; PR #5616; candidate `43b4eb53677f`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-a-cc89dc078a` (audit v1); names: `slicing_mb_sa_mollifier_exists`.
- **`dph_sa_covector_comp_eq_zero`** (L5546) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.covector_vanish-a1`; #5474; PR #5668; candidate `9696746903a5`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-a-3ac3ec8984` (audit v1); names: —.
- **`dph_lipschitz_smooth_approx`** (L5584) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1`; #5222; PR #5692; candidate `133f872db54f`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1` (audit v2); names: `dph_sa_mollify_lipschitz`, `dph_sa_covector_comp_eq_zero`.
- **`dr_cc_skeleton_facts`** (L6208) — node `root.deformation-a1.retraction-a1.cube_core-a1.skeleton_facts-a1`; #3606; PR #4312; candidate `7e104d9d661f`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-skeleton-facts-a1` (audit v1); names: —.
- **`dr_cc_construction`** (L6262) — node `root.deformation-a1.retraction-a1.cube_core-a1.construction-a1`; #3618; PR #4505; candidate `3bac61695a8d`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-construction-a1` (audit v1); names: `dr_cc_skeleton_facts`.
- **`dr_cc_lip_at_comp`** (L6645) — node `root.deformation-a1.retraction-a1.cube_core-a1.lip_at_comp-a1`; #3593; PR #4314; candidate `947cb45aeb45`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-lip-at-comp-a1` (audit v1); names: —.
- **`dr_cc_lip_at_union`** (L6676) — node `root.deformation-a1.retraction-a1.cube_core-a1.lip_at_union-a1`; #3599; PR #4287; candidate `9fe3ea843dee`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-lip-at-union-a1` (audit v1); names: —.
- **`dr_cc_similarity_bound`** (L6705) — node `root.deformation-a1.retraction-a1.cube_core-a1.similarity_bound-a1`; #3614; PR #4342; candidate `0d6109c0ff96`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-similarity-bound-a1` (audit v1); names: —.
- **`dr_cc_radial_map`** (L6788) — node `root.deformation-a1.retraction-a1.cube_core-a1.radial_map-a1`; #3616; PR #4298; candidate `017a76d5ee3d`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-radial-map-a1` (audit v1); names: —.
- **`dr_cc_pointwise_lip`** (L7012) — node `root.deformation-a1.retraction-a1.cube_core-a1.pointwise_lip-a1`; #3620; PR #4513; candidate `73bb3e057914`; proof `root-deformation-a1-retraction-a1-cube-core-a1/children/root-deformation-a1-retraction-a1-cube-core-a1-pointwise-lip-a1` (audit v1); names: `dr_cc_skeleton_facts`, `dr_cc_lip_at_comp`, `dr_cc_lip_at_union`, `dr_cc_similarity_bound`, `dr_cc_radial_map`.
- **`deformation_retraction_cube_core`** (L7233) — node `root.deformation-a1.retraction-a1.cube_core-a1`; #2515; PR #4661; candidate `8d2377f428a0`; proof `root-deformation-a1-retraction-a1/children/root-deformation-a1-retraction-a1-cube-core-a1` (audit v2); names: `dr_cc_construction`, `dr_cc_pointwise_lip`.
- **`deformation_retraction_periodic_extension`** (L7249) — node `root.deformation-a1.retraction-a1.periodic_extension-a1`; #2530; PR #3483; candidate `99d239abdb3f`; proof `root-deformation-a1-retraction-a1/children/root-deformation-a1-retraction-a1-periodic-extension-a1` (audit v2); names: —.
- **`deformation_retraction_globalize`** (L7340) — node `root.deformation-a1.retraction-a1.globalize-a1`; #2542; PR #3567; candidate `4c4af507c405`; proof `root-deformation-a1-retraction-a1/children/root-deformation-a1-retraction-a1-globalize-a1` (audit v2); names: `deformation_retraction_dini_segment`.
- **`deformation_retraction_skeleton_mem`** (L7611) — node `root.deformation-a1.retraction-a1.skeleton_mem-a1`; #2501; PR #3270; candidate `1bc3c7e40a8a`; proof `root-deformation-a1-retraction-a1/children/root-deformation-a1-retraction-a1-skeleton-mem-a1` (audit v2); names: —.
- **`deformation_retraction`** (L7633) — node `root.deformation-a1.retraction-a1`; #1102; PR #4797; candidate `4fe470f2bf44`; proof `root-deformation-a1/children/root-deformation-a1-retraction-a1` (audit v2); names: `deformation_retraction_cube_core`, `deformation_retraction_periodic_extension`, `deformation_retraction_globalize`, `deformation_retraction_skeleton_mem`.
- **`dgc_tube_cover`** (L7664) — node `root.deformation-a1.good_center-a1.tube_cover-a1`; #4224; PR #4767; candidate `f78b89b01de5`; proof `root-deformation-a1-good-center-a1/children/root-deformation-a1-good-center-a1-tube-cover-a1` (audit v1); names: —.
- **`dgc_pm_ball_volume_le`** (L7696) — node `root.deformation-a1.good_center-a1.periodic_maximal-a1.ball_volume-a1`; #4807; PR #4976; candidate `f935cd0e258f`; proof `root-deformation-a1-good-center-a1-periodic-maximal-a1/children/root-deformation-a1-good-center-a1-periodic-maximal-a1-ball-volume-a1` (audit v1); names: —.
- **`dgc_pm_lattice_tubes_disjoint`** (L7714) — node `root.deformation-a1.good_center-a1.periodic_maximal-a1.tubes_disjoint-a1`; #4814; PR #4972; candidate `3546960ffc20`; proof `root-deformation-a1-good-center-a1-periodic-maximal-a1/children/root-deformation-a1-good-center-a1-periodic-maximal-a1-tubes-disjoint-a1` (audit v1); names: —.
- **`dgc_pm_vitali_volume_bound`** (L7767) — node `root.deformation-a1.good_center-a1.periodic_maximal-a1.vitali_bound-a1`; #4824; PR #5045; candidate `5fd171468962`; proof `root-deformation-a1-good-center-a1-periodic-maximal-a1/children/root-deformation-a1-good-center-a1-periodic-maximal-a1-vitali-bound-a1` (audit v1); names: `dgc_pm_ball_volume_le`.
- **`dgc_periodic_maximal`** (L7811) — node `root.deformation-a1.good_center-a1.periodic_maximal-a1`; #4231; PR #5091; candidate `eb6b2fc0270e`; proof `root-deformation-a1-good-center-a1/children/root-deformation-a1-good-center-a1-periodic-maximal-a1` (audit v1); names: `dgc_pm_lattice_tubes_disjoint`, `dgc_pm_vitali_volume_bound`.
- **`dgc_cylinder_volume`** (L7889) — node `root.deformation-a1.good_center-a1.cylinder_volume-a1`; #4240; PR #4793; candidate `750a384555a8`; proof `root-deformation-a1-good-center-a1/children/root-deformation-a1-good-center-a1-cylinder-volume-a1` (audit v1); names: —.
- **`deformation_ipl_cc_gram_det_lower_bound`** (L9708) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.gram_det_lower_bound-a1`; #4915; PR #5143; candidate `e6cf424d70b1`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-gram-8cd8b7a352` (audit v1); names: —.
- **`imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`** (L10103) — node `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.l1_density-a1`; #4229; PR #4820; candidate `0a00d6a3533d`; proof `root-deformation-a1-im-completeness-a1-mass-lower-bound-a1/children/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1-l1-density-a1` (audit v1); names: —.
- **`imc_mlb_exists_unit_field_integral_ge`** (L10214) — node `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1`; #4241; PR #4854; candidate `6c052c410ac7`; proof `root-deformation-a1-im-completeness-a1-mass-lower-bound-a1/children/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1-polar-field-a1` (audit v1); names: `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`.
- **`imc_mlb_exists_form_lintegral_coordNorm_le`** (L10661) — node `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_form-a1`; #4252; PR #4900; candidate `f2bdf1e59b90`; proof `root-deformation-a1-im-completeness-a1-mass-lower-bound-a1/children/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1-polar-form-a1` (audit v1); names: `smr_ci_coord_sum_smul_wedge`, `smr_ci_norm_eq_sqrt_sum_coord_sq`, `imc_mlb_exists_unit_field_integral_ge`.
- **`imc_lintegral_coordNorm_le_mass`** (L24303) — node `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`; #3244; PR #4943; candidate `c5c589901cff`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1` (audit v2); names: `cmb_rb_measureRepresentation_integrableOn_coeff`, `cmb_measureRepresentation_continuous_bound`, `imc_mlb_exists_form_lintegral_coordNorm_le`.
- **`imc_ae_tendsto_of_summable_lintegral`** (L24356) — node `root.deformation-a1.im_completeness-a1.l1_cauchy_limit-a1`; #3254; PR #4244; candidate `08f55173c4b9`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-l1-cauchy-limit-a1` (audit v2); names: —.
- **`dph_hausdorff_product_formula`** (L28324) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1`; #5270; PR #5552; candidate `cdb962226fc8`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-hausdorf-b758ffe4e7` (audit v2); names: `iwl_cr_hp_cylinder_null`, `iwl_cr_hp_injective_pieces`, `iwl_cr_hp_piece_product`. *Unused.*
- **`dph_lpf_proper_transfer`** (L28423) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.proper_transfer-a1`; #5550; PR #5780; candidate `01fc57f4c068`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-511926ec36` (audit v1); names: —.
- **`dph_lpf_reference_sequence`** (L28468) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.reference_sequence-a1`; #5559; PR #5943; candidate `3ae6d1a24146`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-44fe2de89b` (audit v1); names: `dph_lpf_proper_transfer`.
- **`dph_lpf_cmp_affine_homotopy`** (L28492) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1.affine_homotopy-a1`; #5858; PR #5948; candidate `d3db72734efb`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-0f5b75e2aa/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-944a269411` (audit v1); names: —.
- **`dph_sh_ae_affine_homotopy_contDiff_fderiv`** (L28523) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_fderiv-a1`; #5681; PR #5976; candidate `0e649498f782`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-88afce5b06/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-d98ec3b185` (audit v1); names: —.
- **`dph_sh_ae_affine_homotopy_isCompact_preimage_cyl`** (L28585) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_proper-a1`; #5689; PR #5814; candidate `7a915c9aa2f7`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-88afce5b06/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-cf22dddeb1` (audit v1); names: —.
- **`dph_lpf_cmp_core_estimate`** (L31919) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1.core_estimate-a1`; #5874; PR #5988; candidate `096c8c29bdaa`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-0f5b75e2aa/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-1a90ca2873` (audit v1); names: `br_la_testForm_covectorNorm_bounded`, `iwl_cr_support_lemmas`, `dph_lpf_cmp_affine_homotopy`, `iwl_sp_exists_compatible_testForm`.
- **`dph_lpf_comparison`** (L32022) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1`; #5565; PR #6126; candidate `b258640d1b3d`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-0f5b75e2aa` (audit v1); names: `dph_lpf_proper_transfer`, `dph_lpf_cmp_core_estimate`.
- **`dph_lpf_current_of_bounded_functional`** (L32073) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.current_criterion-a1`; #5572; PR #5916; candidate `f5a2520e7214`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-4a6665d902` (audit v1); names: `fiw_ims_sc_continuous_of_bound`.
- **`deformation_imcomb_subset_locality`** (L32094) — node `root.deformation-a1.im_combination-a1.subset_locality-a1`; #4608; PR #4970; candidate `7fb98fe53fd7`; proof `root-deformation-a1-im-combination-a1/children/root-deformation-a1-im-combination-a1-subset-locality-a1` (audit v1); names: `iwl_weighted_tangent_locality`, `lpf_wtc_ae_zero_density_off_set`.
- **`dph_iprod_horizontal_slices`** (L32767) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_slices-a1`; #5655; PR #5935; candidate `e246cb949718`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-b3ea5a5a02` (audit v1); names: `iwl_sp_exists_compatible_testForm`.
- **`dph_iprod_slice_covector_norm_le`** (L32880) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_norm-a1`; #5642; PR #5984; candidate `6c5fc81ba5e7`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-9977dc81c7` (audit v1); names: —.
- **`dph_lpfex_bounded_compatible_form`** (L33161) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.bounded_compatible-a1`; #5941; PR #6339; candidate `f7dbd7a666a7`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-77970eab9a` (audit v1); names: `iwl_sp_exists_compatible_testForm`, `iwl_sp_covectorEuclideanNorm_pullback_le`.
- **`dph_lpfex_tendsto_of_index_maps`** (L33210) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.index_cauchy-a1`; #5947; PR #6034; candidate `7bee0b9d3976`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-23fd0e85aa` (audit v1); names: —.
- **`dph_lpfex_support_subset_closure_image`** (L33236) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.support_closure-a1`; #5953; PR #6131; candidate `d31416678baa`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-0081a36835` (audit v1); names: —.
- **`dph_lpf_existence`** (L33293) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1`; #5590; PR #6347; candidate `73e44feaf098`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-41deb81aa5` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `dph_lpf_current_of_bounded_functional`, `dph_lpfex_bounded_compatible_form`, `dph_lpfex_tendsto_of_index_maps`, `dph_lpfex_support_subset_closure_image`.
- **`dph_lpf_boundary`** (L33435) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.boundary-a1`; #5608; PR #5930; candidate `e9411ef3642d`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-d4c2f8e63c` (audit v1); names: `iwl_cr_support_lemmas`, `iwl_sp_exists_compatible_testForm`.
- **`dph_lpf_linearity`** (L33568) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.linearity-a1`; #5612; PR #5890; candidate `0b11970c705b`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-e7ea8f6410` (audit v1); names: `iwl_cr_support_lemmas`, `iwl_sp_exists_compatible_testForm`.
- **`dph_sh_apply_eq_of_eqOn_nhds_cyl`** (L33661) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_comparison-a1`; #5452; PR #5971; candidate `12c5eb5f57cb`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-33fe8712de` (audit v1); names: `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_ci_slice_testForm`.
- **`dph_sh_slice_compatible_testForm`** (L33708) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_compatible-a1`; #5463; PR #5691; candidate `b9c2a28d96da`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-a2a415b3c0` (audit v1); names: `iwl_sp_exists_compatible_testForm`.
- **`dph_sh_extDeriv_compatible`** (L33775) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.extderiv_compatible-a1`; #5473; PR #5551; candidate `06e17ac22403`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-f068722a83` (audit v1); names: —.
- **`dph_iprod_current_of_bound`** (L33788) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.current_criterion-a1`; #5667; PR #6095; candidate `51d9121840c6`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-16ef94cf27` (audit v1); names: `dph_iprod_slice_covector_norm_le`.
- **`imc_wte_density_bound_of_weightedTangent`** (L34042) — node `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1.weighted_density_bound-a1`; #4212; PR #4798; candidate `883f2ebd12d5`; proof `root-deformation-a1-im-completeness-a1-weighted-tangent-equiv-a1/children/root-deformation-a1-im-completeness-a1-weighted-tangent-equiv-a1-weig-42817fe601` (audit v1); names: `lpf_wtc_blowup_setIntegral_image`.
- **`imc_wte_approxTangent_of_weightedTangent`** (L34154) — node `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1.tangent_of_weighted_tangent-a1`; #4217; PR #5036; candidate `6d508b9e6a78`; proof `root-deformation-a1-im-completeness-a1-weighted-tangent-equiv-a1/children/root-deformation-a1-im-completeness-a1-weighted-tangent-equiv-a1-tang-ea42ea2275` (audit v1); names: `lpf_wtc_wtt_blowup_integral_split`, `lpf_wtc_wtt_continuity_error_vanishes`, `lpf_wtc_wtt_remainder_vanishes`, `lpf_wtc_blowup_setIntegral_image`, `imc_wte_density_bound_of_weightedTangent`.
- **`imc_ae_zero_density_off_set`** (L34191) — node `root.deformation-a1.im_completeness-a1.zero_density-a1`; #3336; PR #4313; candidate `af9b120b0819`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-zero-density-a1` (audit v2); names: —.
- **`dmr_massMeasure_support_finite`** (L34348) — node `root.deformation-a1.mass_restriction-a1.mass_measure_facts-a1`; #4215; PR #4770; candidate `84f8d2059dd1`; proof `root-deformation-a1-mass-restriction-a1/children/root-deformation-a1-mass-restriction-a1-mass-measure-facts-a1` (audit v3); names: —.
- **`dmr_measureRepresentation_unique`** (L34390) — node `root.deformation-a1.mass_restriction-a1.representation_unique-a1`; #4219; PR #4853; candidate `a23ae889fb64`; proof `root-deformation-a1-mass-restriction-a1/children/root-deformation-a1-mass-restriction-a1-representation-unique-a1` (audit v3); names: `slicing_representation_unique`.
- **`dmr_weightedTangent_inter`** (L34431) — node `root.deformation-a1.mass_restriction-a1.tangent_inter-a1`; #4228; PR #4809; candidate `092432628141`; proof `root-deformation-a1-mass-restriction-a1/children/root-deformation-a1-mass-restriction-a1-tangent-inter-a1` (audit v3); names: `iwl_weighted_tangent_locality`, `lpf_wtc_ae_zero_density_off_set`.
- **`dmr_rectifiableTriple_inter`** (L34495) — node `root.deformation-a1.mass_restriction-a1.triple_inter-a1`; #4237; PR #4850; candidate `bf2b5c94a944`; proof `root-deformation-a1-mass-restriction-a1/children/root-deformation-a1-mass-restriction-a1-triple-inter-a1` (audit v3); names: `dmr_weightedTangent_inter`.
- **`deformation_mass_restriction`** (L34528) — node `root.deformation-a1.mass_restriction-a1`; #1104; PR #4933; candidate `0b7851dc2aad`; proof `root-deformation-a1/children/root-deformation-a1-mass-restriction-a1` (audit v2); names: `polyhedral_approx_restriction_tau`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `dmr_massMeasure_support_finite`, `dmr_measureRepresentation_unique`, `dmr_rectifiableTriple_inter`.
- **`imc_approxTangent_iff_of_subset`** (L34563) — node `root.deformation-a1.im_completeness-a1.approx_tangent_locality-a1`; #3266; PR #4498; candidate `07759cf2463d`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-approx-tangent-locality-a1` (audit v2); names: `lpf_wtc_blowup_setIntegral_image`, `imc_ae_zero_density_off_set`.
- **`dph_iprod_slice_continuity`** (L34678) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_continuity-a1`; #5679; PR #6090; candidate `13ffabe42267`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-50291f51d3` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `dph_iprod_slice_covector_norm_le`.
- **`dph_iprod_slice_extDeriv`** (L34789) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_ext_deriv-a1`; #5688; PR #5889; candidate `705d3ebd6a11`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-8d833e2438` (audit v1); names: —.
- **`dph_iprod_horizontal_ftc`** (L34922) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1`; #5690; PR #6388; candidate `1f0b2a6d3435`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-41027b8a1b` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `dph_iprod_slice_covector_norm_le`, `dph_iprod_slice_continuity`.
- **`dph_sh_ib_covectorEuclideanNorm_contract_le`** (L35076) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1.contraction_bound-a1`; #5641; PR #5915; candidate `6adf1557d9ef`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-715d48ac9c/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-f193576245` (audit v1); names: `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`.
- **`dph_sh_covectorEuclideanNorm_interior_le`** (L35142) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1`; #5475; PR #5965; candidate `da03b6b76312`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-715d48ac9c` (audit v1); names: `fiw_tb_ext_covectorNorm_smul`, `iwl_sp_covectorEuclideanNorm_pullback_le`, `dph_sh_ib_covectorEuclideanNorm_contract_le`.
- **`dph_sh_affine_estimate`** (L35166) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1`; #5484; PR #6121; candidate `5f368d67e216`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-88afce5b06` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `iwl_cr_ci_slice_testForm`, `dph_sh_ae_affine_homotopy_contDiff_fderiv`, `dph_sh_ae_affine_homotopy_isCompact_preimage_cyl`, `iwl_sp_exists_compatible_testForm`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_sh_covectorEuclideanNorm_interior_le`.
- **`dph_iprod_exists`** (L35345) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.product_exists-a1`; #5698; PR #6385; candidate `1f6181bacc73`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-f62a462e6c` (audit v1); names: `isoperimetric_apply_eq_zero_of_disjoint_support`, `iwl_cr_ci_slice_testForm`, `dph_iprod_current_of_bound`, `dph_iprod_slice_continuity`.
- **`dph_iprod_boundary`** (L35517) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.product_boundary-a1`; #5709; PR #6456; candidate `38c8c13b65d2`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-ea428ac2b9` (audit v1); names: `iwl_cr_ci_slice_testForm`, `dph_iprod_horizontal_slices`, `dph_iprod_slice_continuity`, `dph_iprod_slice_extDeriv`, `dph_iprod_horizontal_ftc`.
- **`dph_interval_product`** (L35897) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1`; #5233; PR #6469; candidate `f0b9e8a43281`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-product-a1` (audit v2); names: `dph_iprod_slice_continuity`, `dph_iprod_exists`, `dph_iprod_boundary`.
- **`dph_smooth_homotopy`** (L36028) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1`; #5252; PR #6511; candidate `6c3f4de5c65a`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1` (audit v2); names: `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_support_lemmas`, `iwl_cr_ci_slice_testForm`, `iwl_sp_exists_compatible_testForm`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_sh_slice_compatible_testForm`, `dph_sh_extDeriv_compatible`, `dph_sh_affine_estimate`, `dph_interval_product`.
- **`imc_weightedTangent_iff_approxTangent`** (L36142) — node `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1`; #3282; PR #5168; candidate `af5edcea1275`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-weighted-tangent-equiv-a1` (audit v2); names: `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`, `imc_wte_approxTangent_of_weightedTangent`, `imc_ae_zero_density_off_set`.
- **`imc_isRectifiableTriple_of_eventually_mem`** (L36264) — node `root.deformation-a1.im_completeness-a1.limit_triple-a1`; #3296; PR #5176; candidate `dfb7982325af`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-limit-triple-a1` (audit v2); names: `imc_approxTangent_iff_of_subset`, `imc_weightedTangent_iff_approxTangent`, `fiw_ims_frame_sign`.
- **`dph_interval_product_im`** (L36406) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product_im-a1`; #5242; PR #5573; candidate `266616dc3d88`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-interval-a63896b906` (audit v2); names: `iwl_cr_ci_slice_testForm`, `iwl_cr_interval_product_im`.
- **`dph_lipschitz_pushforward`** (L36426) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`; #5257; PR #6616; candidate `a20cf9c24fee`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d` (audit v2); names: `dph_lipschitz_smooth_approx`, `dph_lpf_reference_sequence`, `dph_lpf_comparison`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_interval_product`, `dph_smooth_homotopy`.
- **`dph_lipschitz_pushforward_im`** (L36460) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward_im-a1`; #5263; PR #5768; candidate `309a1a643b76`; proof `root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-a632d9c646` (audit v2); names: `dph_lipschitz_smooth_approx`, `iwl_sp_exists_compatible_testForm`, `iwl_sp_rectifiable_support_null`.
- **`deformation_skeleton_isClosed`** (L39435) — node `root.deformation-a1.onto_skeleton-a1.skeleton_closed-a1`; #4553; PR #5035; candidate `e0ddd8eced47`; proof `root-deformation-a1-onto-skeleton-a1/children/root-deformation-a1-onto-skeleton-a1-skeleton-closed-a1` (audit v1); names: —.
- **`deformation_good_radius`** (L39485) — node `root.deformation-a1.onto_skeleton-a1.good_radius-a1`; #4561; PR #4974; candidate `6097b18c8c43`; proof `root-deformation-a1-onto-skeleton-a1/children/root-deformation-a1-onto-skeleton-a1-good-radius-a1` (audit v1); names: —.
- **`deformation_telescope_limit`** (L39553) — node `root.deformation-a1.onto_skeleton-a1.telescope_limit-a1`; #4576; PR #5214; candidate `a008ba30dbd5`; proof `root-deformation-a1-onto-skeleton-a1/children/root-deformation-a1-onto-skeleton-a1-telescope-limit-a1` (audit v1); names: `iwl_cr_support_lemmas`, `fiw_ims_series_current`.
- **`deformation_ipl_cc_signed_change_of_variables`** (L39846) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.signed_change_of_variables-a1`; #4918; PR #5112; candidate `81af8e83cfa0`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-sign-b01f3ae29c` (audit v1); names: `lpf_raf_chart_change_of_variables`.
- **`deformation_ipl_cc_chart_orientation_sign`** (L39938) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1`; #4923; PR #5146; candidate `714635af911e`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-char-e8bb93b435` (audit v1); names: `lpf_simple_nvector_algebra`, `lpf_weighted_tangent_on_c1_chart`, `lpf_ccr_ae_pullback`.
- **`deformation_ipl_cc_chart_integral_representation`** (L40113) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_representation-a1`; #4925; PR #5175; candidate `620950e4ff28`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-char-e94950e632` (audit v1); names: `deformation_ipl_cc_gram_det_lower_bound`, `lpf_raf_chart_change_of_variables`, `lpf_wtc_cat_fderiv_lower_bound`, `deformation_ipl_cc_signed_change_of_variables`, `deformation_ipl_cc_chart_orientation_sign`.
- **`deformation_ipl_cc_pushforward_integrand_bound`** (L40247) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.integrand_bound-a1`; #4930; PR #5135; candidate `015c6e0e5ba5`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-inte-b85bcf5018` (audit v1); names: —.
- **`deformation_ipl_cc_tendsto_setIntegral_of_partition`** (L40325) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.partition_tannery-a1`; #4937; PR #5121; candidate `2cd5968b05f4`; proof `root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-part-0e604c3ec5` (audit v1); names: —.
- **`deformation_ipl_tangential_pushforward_aestronglyMeasurable`** (L40477) — node `root.deformation-a1.im_pushforward_limit-a1.pushforward_measurable-a1`; #4388; PR #4893; candidate `47253038859d`; proof `root-deformation-a1-im-pushforward-limit-a1/children/root-deformation-a1-im-pushforward-limit-a1-pushforward-measurable-a1` (audit v3); names: `lpf_countably_rectifiable_c1_cover`, `lpf_tde_measurable_chart_differential`, `lpf_chart_chain_rule`.
- **`deformation_ipl_mwc_td_scalar_smooth_dense`** (L40714) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1.scalar_dense-a1`; #5161; PR #5291; candidate `f4c5e5ae53d1`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-fc38066b61/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-ded0136ac6` (audit v1); names: `slicing_im_ll_gws_smooth_dense`.
- **`deformation_ipl_mwc_mil_abs_det_le`** (L40760) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.abs_det_le-a1`; #5182; PR #5282; candidate `d3a1d7652945`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1c3fd07537/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-ee5f4650a0` (audit v1); names: —.
- **`deformation_ipl_mwc_mil_tendsto_integral_mul_det`** (L40786) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.det_dominated_convergence-a1`; #5187; PR #5323; candidate `a145fda2dac3`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1c3fd07537/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-6f1d5bf106` (audit v1); names: `deformation_ipl_mwc_mil_abs_det_le`.
- **`deformation_ipl_mwc_mil_ae_fderiv_eq_proj`** (L40823) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.ae_fderiv_extension-a1`; #5191; PR #5357; candidate `b42e6549be1d`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1c3fd07537/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1ddf3a1eca` (audit v1); names: —.
- **`deformation_ipl_mwc_mis_integral_fderiv_eq_zero`** (L40849) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.integral_fderiv_zero-a1`; #5253; PR #5381; candidate `f755fa9355f6`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-53f5a337eb` (audit v1); names: —.
- **`deformation_ipl_mwc_mis_det_contDiff`** (L40872) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.det_contdiff-a1`; #5256; PR #5389; candidate `d91c70c26b54`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-459f528ff2` (audit v1); names: —.
- **`deformation_ipl_mwc_pi_cofactor_leibniz`** (L40891) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.cofactor_leibniz-a1`; #5212; PR #5438; candidate `2e78567bf521`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-99997f89ba` (audit v1); names: —.
- **`deformation_ipl_mwc_pi_hessian_symm`** (L40921) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.hessian_symm-a1`; #5224; PR #5344; candidate `d4b83da466bf`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1958a2a21a` (audit v1); names: —.
- **`deformation_ipl_mwc_pi_fderiv_sum_prod`** (L40938) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.fderiv_sum_prod-a1`; #5234; PR #5394; candidate `6ede8508d558`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-ec5042b895` (audit v1); names: —.
- **`deformation_ipl_mwc_pi_swap_cancel`** (L40956) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.swap_cancel-a1`; #5243; PR #5358; candidate `250d1c58c63b`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-9dbfe8dff5` (audit v1); names: —.
- **`deformation_ipl_mwc_piola_identity`** (L40996) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1`; #4929; PR #5454; candidate `a4988d1a63a2`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-f2e89eb27d` (audit v1); names: `deformation_ipl_mwc_pi_cofactor_leibniz`, `deformation_ipl_mwc_pi_hessian_symm`, `deformation_ipl_mwc_pi_fderiv_sum_prod`, `deformation_ipl_mwc_pi_swap_cancel`.
- **`deformation_ipl_mwc_minor_ibp_smooth`** (L41051) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1`; #4932; PR #5478; candidate `58585f8d0e41`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-327766afed` (audit v1); names: `deformation_ipl_mwc_mis_integral_fderiv_eq_zero`, `deformation_ipl_mwc_mis_det_contDiff`, `deformation_ipl_mwc_piola_identity`.
- **`deformation_ipl_mwc_lipschitz_smooth_approx`** (L42146) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.lipschitz_smooth_approx-a1`; #4938; PR #5189; candidate `c2e5d50b952a`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-61569b0ef9` (audit v1); names: `slicing_mb_sa_mollify_lipschitz_close`, `slicing_mb_sa_mollify_lipschitz_hasFDerivAt`, `constancy_mdc_smooth_approx_identity_ae_tendsto`.
- **`deformation_ipl_mwc_minor_ibp_lipschitz`** (L42282) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1`; #4947; PR #5497; candidate `9d1268ce22ea`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-1c3fd07537` (audit v1); names: `deformation_ipl_mwc_mil_tendsto_integral_mul_det`, `deformation_ipl_mwc_mil_ae_fderiv_eq_proj`, `deformation_ipl_mwc_minor_ibp_smooth`, `deformation_ipl_mwc_lipschitz_smooth_approx`.
- **`deformation_ipl_mwc_test_density`** (L42408) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1`; #4952; PR #5304; candidate `0b52fed5b073`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-fc38066b61` (audit v1); names: `deformation_ipl_mwc_td_scalar_smooth_dense`.
- **`deformation_ipl_mwc_minor_weak_star`** (L42469) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1`; #4960; PR #5516; candidate `68685c48420b`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-722770cb6e` (audit v1); names: `deformation_ipl_mwc_minor_ibp_lipschitz`, `deformation_ipl_mwc_test_density`.
- **`deformation_ipl_mwc_coeff_minor_continuity`** (L42710) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.coeff_minor_continuity-a1`; #4965; PR #5542; candidate `398fc995d0bc`; proof `root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-bff0c8b488` (audit v1); names: `deformation_ipl_mwc_minor_weak_star`.
- **`deformation_ipl_minor_weak_continuity`** (L42839) — node `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1`; #4382; PR #5553; candidate `ddc5e2e91796`; proof `root-deformation-a1-im-pushforward-limit-a1/children/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1` (audit v3); names: `cmb_covector_eq_sum_coord_smul_wedge`, `deformation_ipl_mwc_coeff_minor_continuity`.
- **`deformation_ipl_chart_convergence`** (L42953) — node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`; #4399; PR #5744; candidate `9aac4fc5a3d2`; proof `root-deformation-a1-im-pushforward-limit-a1/children/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1` (audit v3); names: `lpf_countably_rectifiable_c1_cover`, `lpf_wtc_chart_image_measurable_locally_finite`, `deformation_ipl_cc_chart_integral_representation`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_cc_tendsto_setIntegral_of_partition`, `lpf_chart_chain_rule`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_minor_weak_continuity`.
- **`deformation_im_pushforward_limit`** (L43187) — node `root.deformation-a1.im_pushforward_limit-a1`; #1111; PR #5894; candidate `64c17f9e467c`; proof `root-deformation-a1/children/root-deformation-a1-im-pushforward-limit-a1` (audit v2); names: `ltg_tau_unique_on_open`, `br_weightedTangent_congr`, `lpf_rectifiable_support_null`, `deformation_ipl_chart_convergence`.
- **`deformation_pushforward_homotopy`** (L43249) — node `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`; #4586; PR #6816; candidate `3e3cf51f15a3`; proof `root-deformation-a1-onto-skeleton-a1/children/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `dph_lipschitz_smooth_approx`, `iwl_cr_support_lemmas`, `iwl_cr_ci_slice_testForm`, `iwl_sp_exists_compatible_testForm`, `dph_interval_product`, `dph_smooth_homotopy`, `dph_interval_product_im`, `dph_lipschitz_pushforward`, `dph_lipschitz_pushforward_im`.
- **`imc_im_density_limit`** (L47189) — node `root.deformation-a1.im_completeness-a1.density_limit-a1`; #3307; PR #5251; candidate `72b1c8658981`; proof `root-deformation-a1-im-completeness-a1/children/root-deformation-a1-im-completeness-a1-density-limit-a1` (audit v2); names: `ltg_tau_integrable`, `polyhedral_approx_pairing_expansion`, `imc_ae_tendsto_of_summable_lintegral`, `imc_isRectifiableTriple_of_eventually_mem`.
- **`deformation_im_completeness`** (L47597) — node `root.deformation-a1.im_completeness-a1`; #1106; PR #5258; candidate `f58460aabccd`; proof `root-deformation-a1/children/root-deformation-a1-im-completeness-a1` (audit v2); names: `ltg_tau_integrable`, `imc_lintegral_coordNorm_le_mass`, `imc_im_density_limit`.
- **`deformation_good_center`** (L47744) — node `root.deformation-a1.good_center-a1`; #1103; PR #5122; candidate `bf5eec48076a`; proof `root-deformation-a1/children/root-deformation-a1-good-center-a1` (audit v2); names: `dgc_tube_cover`, `dgc_periodic_maximal`, `dgc_cylinder_volume`.
- **`deformation_onto_skeleton`** (L47900) — node `root.deformation-a1.onto_skeleton-a1`; #1115; PR #7347; candidate `738861e0720c`; proof `root-deformation-a1/children/root-deformation-a1-onto-skeleton-a1` (audit v2); names: `cmb_abs_apply_le_of_massOn_le`, `deformation_retraction`, `deformation_mass_restriction`, `deformation_skeleton_isClosed`, `deformation_good_radius`, `deformation_telescope_limit`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `deformation_im_completeness`, `deformation_good_center`.
- **`deformation_skeleton_polyhedral`** (L49061) — node `root.deformation-a1.skeleton_polyhedral-a1`; #1118; PR #5072; candidate `261bae15b4dd`; proof `root-deformation-a1/children/root-deformation-a1-skeleton-polyhedral-a1` (audit v2); names: `cmb_abs_apply_le_of_massOn_le`, `br_weightedTangent_congr`, `cmb_covector_eq_sum_coord_smul_wedge`, `isoperimetric_coord_box_measure`, `lpf_simple_nvector_algebra`, `slicing_ru_smooth_to_continuous`, `slicing_ru_continuous_to_bounded`, `lpf_raf_chart_preimage_null`, `deformation_mass_restriction`.
- **`deformation_imcomb_weight_change`** (L65761) — node `root.deformation-a1.im_combination-a1.weight_change-a1`; #4615; PR #5172; candidate `efee9a8cf5a6`; proof `root-deformation-a1-im-combination-a1/children/root-deformation-a1-im-combination-a1-weight-change-a1` (audit v1); names: `iwl_weighted_tangent_locality`, `iwl_imc_normalized_lebesgue_points`.
- **`deformation_imcomb_tangent_overlap`** (L65835) — node `root.deformation-a1.im_combination-a1.tangent_overlap-a1`; #4627; PR #5231; candidate `d3ff54f8631a`; proof `root-deformation-a1-im-combination-a1/children/root-deformation-a1-im-combination-a1-tangent-overlap-a1` (audit v1); names: `deformation_imcomb_subset_locality`, `deformation_imcomb_weight_change`.
- **`deformation_im_combination`** (L65922) — node `root.deformation-a1.im_combination-a1`; #1119; PR #5260; candidate `bf6aeaf20acf`; proof `root-deformation-a1/children/root-deformation-a1-im-combination-a1` (audit v2); names: `fiw_ims_combine`, `deformation_imcomb_tangent_overlap`.
- **`deformation_dilation_im_weightedTangent`** (L65983) — node `root.deformation-a1.dilation-a1.integer_multiplicity-a1.weighted_tangent-a1`; #4905; PR #5232; candidate `4fc201187da5`; proof `root-deformation-a1-dilation-a1-integer-multiplicity-a1/children/root-deformation-a1-dilation-a1-integer-multiplicity-a1-weighted-tangent-a1` (audit v1); names: —.
- **`deformation_dilation_im_rectifiableTriple`** (L66022) — node `root.deformation-a1.dilation-a1.integer_multiplicity-a1.rectifiable_triple-a1`; #4910; PR #5259; candidate `003dc0ac1d63`; proof `root-deformation-a1-dilation-a1-integer-multiplicity-a1/children/root-deformation-a1-dilation-a1-integer-multiplicity-a1-rectifiable-triple-a1` (audit v1); names: `deformation_dilation_im_weightedTangent`.
- **`deformation_dilation_im_tauAction`** (L66096) — node `root.deformation-a1.dilation-a1.integer_multiplicity-a1.tau_action-a1`; #4917; PR #5103; candidate `7939be729e42`; proof `root-deformation-a1-dilation-a1-integer-multiplicity-a1/children/root-deformation-a1-dilation-a1-integer-multiplicity-a1-tau-action-a1` (audit v1); names: —.
- **`deformation_dilation_calculus`** (L66120) — node `root.deformation-a1.dilation-a1.calculus-a1`; #4511; PR #5054; candidate `7a748c7e1c8a`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-calculus-a1` (audit v1); names: —.
- **`deformation_dilation_hausdorff`** (L66210) — node `root.deformation-a1.dilation-a1.hausdorff-a1`; #4519; PR #4951; candidate `8ae4965a0dae`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-hausdorff-a1` (audit v1); names: —.
- **`deformation_dilation_mass`** (L66233) — node `root.deformation-a1.dilation-a1.mass-a1`; #4523; PR #5090; candidate `92a171794173`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-mass-a1` (audit v1); names: `deformation_dilation_calculus`.
- **`deformation_dilation_support`** (L66285) — node `root.deformation-a1.dilation-a1.support-a1`; #4532; PR #5096; candidate `dccf6342d5d1`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-support-a1` (audit v1); names: `deformation_dilation_calculus`.
- **`deformation_dilation_integer_multiplicity`** (L66337) — node `root.deformation-a1.dilation-a1.integer_multiplicity-a1`; #4546; PR #5281; candidate `55e0df8042b9`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-integer-multiplicity-a1` (audit v1); names: `deformation_dilation_im_rectifiableTriple`, `deformation_dilation_im_tauAction`, `deformation_dilation_calculus`, `deformation_dilation_hausdorff`.
- **`deformation_dilation_lattice_chain`** (L66358) — node `root.deformation-a1.dilation-a1.lattice_chain-a1`; #4558; PR #5124; candidate `ce4ee5e2a817`; proof `root-deformation-a1-dilation-a1/children/root-deformation-a1-dilation-a1-lattice-chain-a1` (audit v1); names: `deformation_dilation_calculus`, `deformation_dilation_hausdorff`.
- **`deformation_dilation`** (L66406) — node `root.deformation-a1.dilation-a1`; #1120; PR #5466; candidate `c859568a2876`; proof `root-deformation-a1/children/root-deformation-a1-dilation-a1` (audit v2); names: `deformation_dilation_calculus`, `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`.
- **`deformation_theorem`** (L66990) — node `root.deformation-a1`; #325; PR #7759; candidate `4efd922c99dc`; proof `root/children/root-deformation-a1` (audit v3); names: `lipschitz_pushforward_integer_multiplicity`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `deformation_im_combination`, `deformation_dilation`, `slicing_theorem`.

### A.6 Subtree `root.isoperimetric-a1` (10 declarations)

- **`isoperimetric_apply_eq_zero_of_disjoint_support`** (L2069) — node `root.isoperimetric-a1.vanish_off_support-a1`; #755; PR #1637; candidate `3ccbe082e519`; proof `root-isoperimetric-a1/children/root-isoperimetric-a1-vanish-off-support-a1` (audit v1); names: —.
- **`isoperimetric_abs_covector_apply_le`** (L2379) — node `root.isoperimetric-a1.covector_eval_bound-a1`; #757; PR #1639; candidate `8c000d1fa9fe`; proof `root-isoperimetric-a1/children/root-isoperimetric-a1-covector-eval-bound-a1` (audit v1); names: —.
- **`isoperimetric_mass_lt_top`** (L2450) — node `root.isoperimetric-a1.finite_mass-a1`; #760; PR #2092; candidate `1e660afc8717`; proof `root-isoperimetric-a1/children/root-isoperimetric-a1-finite-mass-a1` (audit v1); names: `isoperimetric_apply_eq_zero_of_disjoint_support`, `isoperimetric_abs_covector_apply_le`.
- **`isoperimetric_mass_eq_zero_iff`** (L7542) — node `root.isoperimetric-a1.zero_mass_iff-a1`; #762; PR #2714; candidate `43971b5da770`; proof `root-isoperimetric-a1/children/root-isoperimetric-a1-zero-mass-iff-a1` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `br_la_testForm_covectorNorm_bounded`.
- **`isoperimetric_coord_covector_eval`** (L7561) — node `root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1`; #1227; PR #2099; candidate `3d98b1871057`; proof `root-isoperimetric-a1-lattice-mass-lower-bound-a1/children/root-isoperimetric-a1-lattice-mass-lower-bound-a1-coord-covector-a1` (audit v1); names: —.
- **`isoperimetric_coord_box_measure`** (L9287) — node `root.isoperimetric-a1.lattice_mass_lower_bound-a1.box_measure-a1`; #1228; PR #1494; candidate `eefd7c3e7c63`; proof `root-isoperimetric-a1-lattice-mass-lower-bound-a1/children/root-isoperimetric-a1-lattice-mass-lower-bound-a1-box-measure-a1` (audit v1); names: —.
- **`isoperimetric_lattice_face_cutoff`** (L9354) — node `root.isoperimetric-a1.lattice_mass_lower_bound-a1.face_cutoff-a1`; #1229; PR #1759; candidate `b27494a624bd`; proof `root-isoperimetric-a1-lattice-mass-lower-bound-a1/children/root-isoperimetric-a1-lattice-mass-lower-bound-a1-face-cutoff-a1` (audit v1); names: —.
- **`isoperimetric_lattice_face_isolating_form`** (L9453) — node `root.isoperimetric-a1.lattice_mass_lower_bound-a1.isolating_form-a1`; #1230; PR #2246; candidate `dded2fa657ff`; proof `root-isoperimetric-a1-lattice-mass-lower-bound-a1/children/root-isoperimetric-a1-lattice-mass-lower-bound-a1-isolating-form-a1` (audit v1); names: `isoperimetric_coord_covector_eval`, `isoperimetric_coord_box_measure`, `isoperimetric_lattice_face_cutoff`.
- **`isoperimetric_lattice_chain_mass_ge`** (L9544) — node `root.isoperimetric-a1.lattice_mass_lower_bound-a1`; #765; PR #2541; candidate `b1a770c375be`; proof `root-isoperimetric-a1/children/root-isoperimetric-a1-lattice-mass-lower-bound-a1` (audit v1); names: `isoperimetric_lattice_face_isolating_form`.
- **`isoperimetric_theorem`** (L67200) — node `root.isoperimetric-a1`; #329; PR #8118; candidate `2e7a66f237aa`; proof `root/children/root-isoperimetric-a1` (audit v3); names: `isoperimetric_mass_lt_top`, `isoperimetric_mass_eq_zero_iff`, `isoperimetric_lattice_chain_mass_ge`, `deformation_theorem`.

### A.7 Subtree `root.polyhedral_approximation-a1` (21 declarations)

- **`polyhedral_approx_exhaustion_function`** (L447) — node `root.polyhedral_approximation-a1.truncation_sequence-a1.exhaustion_function-a1`; #1127; PR #1758; candidate `e902cc9324a7`; proof `root-polyhedral-approximation-a1-truncation-sequence-a1/children/root-polyhedral-approximation-a1-truncation-sequence-a1-exhaustion-function-a1` (audit v1); names: —.
- **`polyhedral_approx_boundary_mass_cutoff`** (L506) — node `root.polyhedral_approximation-a1.truncation_sequence-a1.boundary_mass_cutoff-a1`; #1128; PR #2006; candidate `220d968d8bd7`; proof `root-polyhedral-approximation-a1-truncation-sequence-a1/children/root-polyhedral-approximation-a1-truncation-sequence-a1-boundary-mass-cutoff-a1` (audit v1); names: —.
- **`polyhedral_approx_pairing_wedge_kronecker`** (L3601) — node `root.polyhedral_approximation-a1.pairing_expansion-a1.wedge_kronecker-a1`; #1059; PR #1963; candidate `4f8cb90675e5`; proof `root-polyhedral-approximation-a1-pairing-expansion-a1/children/root-polyhedral-approximation-a1-pairing-expansion-a1-wedge-kronecker-a1` (audit v1); names: —.
- **`polyhedral_approx_pairing_covector_ext`** (L3637) — node `root.polyhedral_approximation-a1.pairing_expansion-a1.covector_ext-a1`; #1060; PR #1928; candidate `564fb5ea9012`; proof `root-polyhedral-approximation-a1-pairing-expansion-a1/children/root-polyhedral-approximation-a1-pairing-expansion-a1-covector-ext-a1` (audit v1); names: —.
- **`polyhedral_approx_rt_integrableOn_apply`** (L10581) — node `root.polyhedral_approximation-a1.restriction_tau-a1.repr_integrability-a1`; #1292; PR #2226; candidate `5309966301ae`; proof `root-polyhedral-approximation-a1-restriction-tau-a1/children/root-polyhedral-approximation-a1-restriction-tau-a1-repr-integrability-a1` (audit v1); names: —.
- **`polyhedral_approx_rt_tau_integrableOn`** (L10617) — node `root.polyhedral_approximation-a1.restriction_tau-a1.tau_integrability-a1`; #1300; PR #2117; candidate `f3e41bc4dfde`; proof `root-polyhedral-approximation-a1-restriction-tau-a1/children/root-polyhedral-approximation-a1-restriction-tau-a1-tau-integrability-a1` (audit v1); names: —.
- **`polyhedral_approx_pairing_coordinate_bound`** (L10731) — node `root.polyhedral_approximation-a1.pairing_expansion-a1.coordinate_bound-a1`; #1061; PR #1503; candidate `e05c5313237c`; proof `root-polyhedral-approximation-a1-pairing-expansion-a1/children/root-polyhedral-approximation-a1-pairing-expansion-a1-coordinate-bound-a1` (audit v1); names: —.
- **`polyhedral_approx_pairing_expansion`** (L17563) — node `root.polyhedral_approximation-a1.pairing_expansion-a1`; #527; PR #2131; candidate `c4c0086a7ea3`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-pairing-expansion-a1` (audit v1); names: `polyhedral_approx_pairing_wedge_kronecker`, `polyhedral_approx_pairing_covector_ext`, `polyhedral_approx_pairing_coordinate_bound`.
- **`polyhedral_approx_density_split`** (L17593) — node `root.polyhedral_approximation-a1.measure_uniqueness-a1.density_split-a1`; #1177; PR #1917; candidate `53e59ae39ad2`; proof `root-polyhedral-approximation-a1-measure-uniqueness-a1/children/root-polyhedral-approximation-a1-measure-uniqueness-a1-density-split-a1` (audit v1); names: —.
- **`polyhedral_approx_finite_smooth_ext`** (L17626) — node `root.polyhedral_approximation-a1.measure_uniqueness-a1.finite_smooth_ext-a1`; #1176; PR #1959; candidate `4e5d18cb88b8`; proof `root-polyhedral-approximation-a1-measure-uniqueness-a1/children/root-polyhedral-approximation-a1-measure-uniqueness-a1-finite-smooth-ext-a1` (audit v1); names: —.
- **`polyhedral_approx_integrable_smooth_ext`** (L17686) — node `root.polyhedral_approximation-a1.measure_uniqueness-a1.integrable_smooth_ext-a1`; #1178; PR #2245; candidate `4279988c51a7`; proof `root-polyhedral-approximation-a1-measure-uniqueness-a1/children/root-polyhedral-approximation-a1-measure-uniqueness-a1-integrable-smooth-ext-a1` (audit v1); names: `polyhedral_approx_density_split`, `polyhedral_approx_finite_smooth_ext`.
- **`polyhedral_approx_measure_uniqueness`** (L17728) — node `root.polyhedral_approximation-a1.measure_uniqueness-a1`; #528; PR #2749; candidate `d5f2301589a8`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-measure-uniqueness-a1` (audit v1); names: `polyhedral_approx_integrable_smooth_ext`.
- **`polyhedral_approx_restriction_tau`** (L17780) — node `root.polyhedral_approximation-a1.restriction_tau-a1`; #530; PR #2849; candidate `d0bdb40ee3ab`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-restriction-tau-a1` (audit v1); names: `polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`, `polyhedral_approx_pairing_expansion`, `polyhedral_approx_measure_uniqueness`.
- **`polyhedral_approx_restriction_exists`** (L17892) — node `root.polyhedral_approximation-a1.restriction_exists-a1`; #529; PR #2197; candidate `0bff98712e72`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-restriction-exists-a1` (audit v1); names: `polyhedral_approx_pairing_expansion`.
- **`polyhedral_approx_open_truncation`** (L18022) — node `root.polyhedral_approximation-a1.open_truncation-a1`; #533; PR #2239; candidate `b3275c855bf2`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-open-truncation-a1` (audit v1); names: `polyhedral_approx_pairing_expansion`.
- **`polyhedral_approx_truncation_seq`** (L18213) — node `root.polyhedral_approximation-a1.truncation_sequence-a1`; #536; PR #2975; candidate `a4d7cce8f764`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-truncation-sequence-a1` (audit v1); names: `polyhedral_approx_exhaustion_function`, `polyhedral_approx_boundary_mass_cutoff`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`.
- **`polyhedral_approx_testForm_covectorNorm_bounded`** (L18339) — node `root.polyhedral_approximation-a1.finite_mass_approximation-a1.testform_bounded-a1`; #2195; PR #2910; candidate `7110c9805fef`; proof `root-polyhedral-approximation-a1-finite-mass-approximation-a1/children/root-polyhedral-approximation-a1-finite-mass-approximation-a1-testfor-2444b65c50` (audit v1); names: —.
- **`polyhedral_approx_scale_seq`** (L18362) — node `root.polyhedral_approximation-a1.finite_mass_approximation-a1.scale_sequence-a1`; #2213; PR #3092; candidate `72f53c6507e1`; proof `root-polyhedral-approximation-a1-finite-mass-approximation-a1/children/root-polyhedral-approximation-a1-finite-mass-approximation-a1-scale-sequence-a1` (audit v1); names: —.
- **`polyhedral_approx_flat_seq_tendsto`** (L18413) — node `root.polyhedral_approximation-a1.finite_mass_approximation-a1.flat_convergence-a1`; #2223; PR #3252; candidate `ca2d03cda38d`; proof `root-polyhedral-approximation-a1-finite-mass-approximation-a1/children/root-polyhedral-approximation-a1-finite-mass-approximation-a1-flat-co-0f93f60fe5` (audit v1); names: `br_la_abs_apply_le_mul_mass`, `polyhedral_approx_testForm_covectorNorm_bounded`.
- **`polyhedral_approx_finite_mass_seq`** (L18449) — node `root.polyhedral_approximation-a1.finite_mass_approximation-a1`; #539; PR #3478; candidate `60949edddf66`; proof `root-polyhedral-approximation-a1/children/root-polyhedral-approximation-a1-finite-mass-approximation-a1` (audit v1); names: `polyhedral_approx_scale_seq`, `polyhedral_approx_flat_seq_tendsto`.
- **`polyhedral_approximation`** (L67293) — node `root.polyhedral_approximation-a1`; #331; PR #8056; candidate `786e6c8abe43`; proof `root/children/root-polyhedral-approximation-a1` (audit v3); names: `polyhedral_approx_truncation_seq`, `polyhedral_approx_finite_mass_seq`, `slicing_theorem`, `deformation_theorem`.

### A.8 Subtree `root.boundary_rectifiability-a1` (31 declarations)

- **`br_la_abs_apply_le_mul_mass`** (L726) — node `root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1`; #1188; PR #2012; candidate `d771ac3ae563`; proof `root-boundary-rectifiability-a1-lattice-approximation-a1/children/root-boundary-rectifiability-a1-lattice-approximation-a1-mass-estimate-a1` (audit v1); names: —.
- **`br_zd_im_dirac_repr`** (L917) — node `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_repr-a1`; #1092; PR #2150; candidate `a530e777eaab`; proof `root-boundary-rectifiability-a1-zero-dim-weak-limit-a1/children/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-dirac-repr-a1` (audit v1); names: —.
- **`br_zd_dirac_massOn_ge`** (L1064) — node `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_mass_bound-a1`; #1094; PR #2281; candidate `6b7f8aea1c33`; proof `root-boundary-rectifiability-a1-zero-dim-weak-limit-a1/children/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-dirac-mass-bound-a1` (audit v1); names: —.
- **`br_zd_dirac_local_limit`** (L1190) — node `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_local_limit-a1`; #1097; PR #1535; candidate `e8520f03dafa`; proof `root-boundary-rectifiability-a1-zero-dim-weak-limit-a1/children/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-dirac-local-limit-a1` (audit v1); names: —.
- **`br_zd_finite_dirac_im`** (L1302) — node `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.finite_dirac_im-a1`; #1095; PR #1515; candidate `360df6808c71`; proof `root-boundary-rectifiability-a1-zero-dim-weak-limit-a1/children/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1-finite-dirac-im-a1` (audit v1); names: —.
- **`ltg_tau_integrable`** (L1431) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1`; #1341; PR #2152; candidate `1d327e46e1cf`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1` (audit v1); names: —.
- **`ltg_covector_separating`** (L1485) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.covector_separating-a1`; #1344; PR #1756; candidate `e4a2285e4918`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-covector-separating-a1` (audit v1); names: —.
- **`ltg_simple_unit_rigidity`** (L1510) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.simple_unit_rigidity-a1`; #1358; PR #1755; candidate `100a3f23645a`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-simple-unit-rigidity-a1` (audit v1); names: —.
- **`ltg_tau_unique_on_open`** (L1570) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_unique_on_open-a1`; #1365; PR #2158; candidate `6e7472481f3b`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-unique-on-open-a1` (audit v1); names: `ltg_tau_integrable`, `ltg_covector_separating`, `ltg_simple_unit_rigidity`.
- **`ltg_glue_triples`** (L1693) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.glue_triples-a1`; #1372; PR #2221; candidate `c1a7e6bba84a`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-glue-triples-a1` (audit v1); names: —.
- **`ltg_tau_congr_on_open`** (L1844) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_congr_on_open-a1`; #1373; PR #1522; candidate `bf2b276506a5`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-congr-on-open-a1` (audit v1); names: —.
- **`ltg_tau_local_to_global`** (L1893) — node `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_local_to_global-a1`; #1377; PR #2196; candidate `0ab0bebaeb02`; proof `root-boundary-rectifiability-a1-local-to-global-im-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-local-to-global-a1` (audit v1); names: `ltg_tau_integrable`.
- **`br_loc_tauAction_current`** (L1977) — node `root.boundary_rectifiability-a1.localization-a1.tau_current-a1`; #2475; PR #3251; candidate `9c856ad6531d`; proof `root-boundary-rectifiability-a1-localization-a1/children/root-boundary-rectifiability-a1-localization-a1-tau-current-a1` (audit v1); names: `ltg_tau_integrable`, `fiw_ims_tt_unit_bound`.
- **`br_weightedTangent_congr`** (L2130) — node `root.boundary_rectifiability-a1.tangent_locality-a1`; #847; PR #1658; candidate `def607d836e2`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-tangent-locality-a1` (audit v1); names: —.
- **`br_restrictDomain_isIntegerMultiplicity`** (L2230) — node `root.boundary_rectifiability-a1.restrict_domain_im-a1`; #852; PR #2238; candidate `03443db0c607`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-restrict-domain-im-a1` (audit v1); names: `br_weightedTangent_congr`.
- **`br_isIntegerMultiplicity_of_local`** (L2270) — node `root.boundary_rectifiability-a1.local_to_global_im-a1`; #857; PR #2309; candidate `4fb91bc57693`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-local-to-global-im-a1` (audit v1); names: `ltg_tau_unique_on_open`, `ltg_glue_triples`, `ltg_tau_congr_on_open`, `ltg_tau_local_to_global`, `br_weightedTangent_congr`.
- **`br_zero_dim_weak_limit_isIntegerMultiplicity`** (L2343) — node `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1`; #859; PR #2773; candidate `66b929ec8db4`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-zero-dim-weak-limit-a1` (audit v1); names: `br_zd_im_dirac_repr`, `br_zd_dirac_massOn_ge`, `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`, `br_isIntegerMultiplicity_of_local`.
- **`br_la_testForm_covectorNorm_bounded`** (L2533) — node `root.boundary_rectifiability-a1.lattice_approximation-a1.testform_bounded-a1`; #1189; PR #2114; candidate `c34586955a82`; proof `root-boundary-rectifiability-a1-lattice-approximation-a1/children/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1` (audit v1); names: —.
- **`br_la_apply_eq_zero_of_lt_degree`** (L3440) — node `root.boundary_rectifiability-a1.lattice_approximation-a1.low_degree_vanish-a1`; #1191; PR #1555; candidate `5e97e54b7c48`; proof `root-boundary-rectifiability-a1-lattice-approximation-a1/children/root-boundary-rectifiability-a1-lattice-approximation-a1-low-degree-vanish-a1` (audit v1); names: —.
- **`br_loc_triple_inter_open`** (L11010) — node `root.boundary_rectifiability-a1.localization-a1.triple_inter_open-a1`; #2484; PR #3461; candidate `980bf2f0ffdd`; proof `root-boundary-rectifiability-a1-localization-a1/children/root-boundary-rectifiability-a1-localization-a1-triple-inter-open-a1` (audit v1); names: `br_weightedTangent_congr`.
- **`br_latticeFace_setIntegral_eq_cube`** (L14757) — node `root.boundary_rectifiability-a1.lattice_face_stokes-a1.lattice_face_param-a1`; #975; PR #1510; candidate `0561b355216f`; proof `root-boundary-rectifiability-a1-lattice-face-stokes-a1/children/root-boundary-rectifiability-a1-lattice-face-stokes-a1-lattice-face-param-a1` (audit v1); names: —.
- **`br_la_weaklyConvergesOn_of_flat_decomposition`** (L28710) — node `root.boundary_rectifiability-a1.lattice_approximation-a1.flat_to_weak-a1`; #1190; PR #2140; candidate `d3d5fa610f70`; proof `root-boundary-rectifiability-a1-lattice-approximation-a1/children/root-boundary-rectifiability-a1-lattice-approximation-a1-flat-to-weak-a1` (audit v1); names: `br_la_abs_apply_le_mul_mass`, `br_la_testForm_covectorNorm_bounded`.
- **`br_cube_integral_fderiv_eq_faces`** (L28745) — node `root.boundary_rectifiability-a1.lattice_face_stokes-a1.cube_ftc-a1`; #976; PR #1450; candidate `f63b90975870`; proof `root-boundary-rectifiability-a1-lattice-face-stokes-a1/children/root-boundary-rectifiability-a1-lattice-face-stokes-a1-cube-ftc-a1` (audit v1); names: —.
- **`br_cube_stokes_lattice`** (L28802) — node `root.boundary_rectifiability-a1.lattice_face_stokes-a1.cube_stokes-a1`; #977; PR #2148; candidate `b16cb9a923c3`; proof `root-boundary-rectifiability-a1-lattice-face-stokes-a1/children/root-boundary-rectifiability-a1-lattice-face-stokes-a1-cube-stokes-a1` (audit v1); names: `br_cube_integral_fderiv_eq_faces`.
- **`br_lattice_face_stokes`** (L28910) — node `root.boundary_rectifiability-a1.lattice_face_stokes-a1`; #863; PR #2192; candidate `c6266655f0f0`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-lattice-face-stokes-a1` (audit v1); names: `br_latticeFace_setIntegral_eq_cube`, `br_cube_stokes_lattice`.
- **`br_lattice_chain_boundary_isIntegerMultiplicity`** (L28933) — node `root.boundary_rectifiability-a1.lattice_boundary_im-a1`; #868; PR #2332; candidate `37bba5ece947`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-lattice-boundary-im-a1` (audit v1); names: `br_lattice_face_stokes`.
- **`br_top_dim_lattice_approximation`** (L29923) — node `root.boundary_rectifiability-a1.top_dim_lattice_approx-a1`; #871; PR #3942; candidate `15d1b4cf7f39`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1` (audit v1); names: `br_lattice_face_stokes`.
- **`br_lattice_approximation`** (L30990) — node `root.boundary_rectifiability-a1.lattice_approximation-a1`; #873; PR #4129; candidate `e0e5bf49d43e`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-lattice-approximation-a1` (audit v1); names: `br_la_apply_eq_zero_of_lt_degree`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_top_dim_lattice_approximation`.
- **`br_boundary_isIntegerMultiplicity_of_finite_mass`** (L31037) — node `root.boundary_rectifiability-a1.finite_mass_boundary_im-a1`; #877; PR #4351; candidate `4f122ed465fe`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-finite-mass-boundary-im-a1` (audit v1); names: `br_zero_dim_weak_limit_isIntegerMultiplicity`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_lattice_approximation`.
- **`br_local_finite_mass_extension`** (L31744) — node `root.boundary_rectifiability-a1.localization-a1`; #880; PR #3730; candidate `d559c74c7b3f`; proof `root-boundary-rectifiability-a1/children/root-boundary-rectifiability-a1-localization-a1` (audit v1); names: `polyhedral_approx_boundary_mass_cutoff`, `ltg_tau_integrable`, `ltg_tau_congr_on_open`, `br_loc_tauAction_current`, `br_loc_triple_inter_open`, `iwl_restriction_theory`, `fiw_im_mass_formula`.
- **`boundary_rectifiability`** (L68901) — node `root.boundary_rectifiability-a1`; #334; PR #8641; candidate `8f66d3bbc008`; proof `root/children/root-boundary-rectifiability-a1` (audit v3); names: `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `br_local_finite_mass_extension`, `slicing_theorem`, `deformation_theorem`, `integrality_of_weak_limits`.

### A.9 Subtree `root.flat_iff_weak-a1` (78 declarations)

- **`fiw_tb_ext_cutoff`** (L622) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff-a1`; #3227; PR #3759; candidate `ecf4b9ac471b`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-cutoff-a1` (audit v1); names: —.
- **`fiw_tb_ext_smul_testForm`** (L642) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1`; #3232; PR #3821; candidate `681990946892`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-smul-testform-a1` (audit v1); names: —.
- **`fiw_tb_ext_apply_eq_of_eqOn`** (L673) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.eq_near-a1`; #3238; PR #3772; candidate `366a98283620`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-eq-near-a1` (audit v1); names: —.
- **`fiw_tb_ext_support_subset`** (L692) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.support_subset-a1`; #3248; PR #3752; candidate `3d64216fd707`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-support-subset-a1` (audit v1); names: —.
- **`fiw_tb_ext_covectorNorm_smul`** (L715) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.norm_smul-a1`; #3262; PR #3755; candidate `47d3d707ce25`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-norm-smul-a1` (audit v1); names: —.
- **`fiw_tb_te_abs_apply_le_mul_mass`** (L764) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.mass_bound-a1`; #3221; PR #3686; candidate `caf42bc49b2c`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-mass-bound-a1` (audit v1); names: —.
- **`fiw_fcl_nested_subseq`** (L803) — node `root.flat_iff_weak-a1.flat_cauchy_limit-a1.nested_subseq-a1`; #1051; PR #1600; candidate `ca04907a3867`; proof `root-flat-iff-weak-a1-flat-cauchy-limit-a1/children/root-flat-iff-weak-a1-flat-cauchy-limit-a1-nested-subseq-a1` (audit v1); names: —.
- **`fiw_fcl_telescope_limit`** (L831) — node `root.flat_iff_weak-a1.flat_cauchy_limit-a1.telescope_limit-a1`; #1053; PR #1748; candidate `d757828a49ef`; proof `root-flat-iff-weak-a1-flat-cauchy-limit-a1/children/root-flat-iff-weak-a1-flat-cauchy-limit-a1-telescope-limit-a1` (audit v1); names: —.
- **`fiw_ims_tt_unit_bound`** (L1959) — node `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1`; #1482; PR #1978; candidate `27af9b191b73`; proof `root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1/children/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1` (audit v1); names: —.
- **`fiw_ims_sc_covectorNorm_le_opNorm`** (L3381) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1.covector_norm-a1`; #1892; PR #2299; candidate `c8cb71851ed3`; proof `root-flat-iff-weak-a1-im-series-a1-series-current-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1-covector-norm-a1` (audit v2); names: —.
- **`fiw_ims_sc_testForm_bounded`** (L5285) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1.testform_bounded-a1`; #1903; PR #2653; candidate `e8e708e479c2`; proof `root-flat-iff-weak-a1-im-series-a1-series-current-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1-testform-bounded-a1` (audit v2); names: `fiw_ims_sc_covectorNorm_le_opNorm`.
- **`fiw_ims_sc_converges_zero_small`** (L5304) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1.converges_small-a1`; #1914; PR #2610; candidate `49ba437cb4c7`; proof `root-flat-iff-weak-a1-im-series-a1-series-current-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1-converges-small-a1` (audit v2); names: `fiw_ims_sc_covectorNorm_le_opNorm`.
- **`fiw_ims_sc_continuous_of_bound`** (L5337) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1.continuity_criterion-a1`; #1925; PR #2815; candidate `5c2485018f33`; proof `root-flat-iff-weak-a1-im-series-a1-series-current-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1-continuity-criterion-a1` (audit v2); names: `fiw_ims_sc_converges_zero_small`.
- **`fiw_ims_sc_series_bound`** (L5364) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1.series_bound-a1`; #1936; PR #2350; candidate `182e22ce5692`; proof `root-flat-iff-weak-a1-im-series-a1-series-current-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1-series-bound-a1` (audit v2); names: —.
- **`fiw_ims_mass_bound`** (L5399) — node `root.flat_iff_weak-a1.im_series-a1.mass_bound-a1`; #1245; PR #2044; candidate `bf9ca0af59c2`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-mass-bound-a1` (audit v1); names: —.
- **`fiw_tb_ri_restrictDomain_mass_le`** (L13348) — node `root.flat_iff_weak-a1.total_boundedness-a1.restrict_im-a1.mass_le-a1`; #3214; PR #3699; candidate `c666a7bc5b72`; proof `root-flat-iff-weak-a1-total-boundedness-a1-restrict-im-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-restrict-im-a1-mass-le-a1` (audit v1); names: —.
- **`fiw_tb_ext_cutoff_current`** (L13363) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff_current-a1`; #3291; PR #3885; candidate `d39fb30b5115`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-cutoff-current-a1` (audit v1); names: `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_covectorNorm_smul`, `br_la_abs_apply_le_mul_mass`, `fiw_ims_sc_converges_zero_small`.
- **`fiw_tb_ext_mass_le_restrictDomain`** (L13407) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.mass_le_restrict-a1`; #3303; PR #3947; candidate `35ad818f31a0`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-mass-le-restrict-a1` (audit v1); names: `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_covectorNorm_smul`.
- **`fiw_tb_ext_isIntegerMultiplicity`** (L13437) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.im_extend-a1`; #3312; PR #3927; candidate `51907ff085ab`; proof `root-flat-iff-weak-a1-total-boundedness-a1-extend-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1-im-extend-a1` (audit v1); names: `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset`, `br_weightedTangent_congr`, `lpf_rectifiable_support_null`.
- **`fiw_tb_tda_density`** (L13500) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density-a1`; #3220; PR #3807; candidate `dedd6091ba85`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-density-a1` (audit v1); names: —.
- **`fiw_tb_tda_im_median_exists`** (L13637) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_exists-a1`; #3875; PR #4565; candidate `4fe6eeba5edf`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-299420ad5d` (audit v1); names: —.
- **`fiw_tb_tda_im_median_bounds`** (L13710) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_bounds-a1`; #3884; PR #4848; candidate `4e72b5fdaf9e`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-a1ff4a20a6` (audit v1); names: —.
- **`fiw_tb_tda_im_median_minimizes`** (L13748) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_minimizes-a1`; #3887; PR #4587; candidate `b7b7a81541f2`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-0c7ab12b90` (audit v1); names: —.
- **`fiw_tb_tda_im_mean_deviation`** (L13834) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.mean_deviation-a1`; #3896; PR #4618; candidate `130b23e22587`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-51896063c1` (audit v1); names: —.
- **`fiw_tb_tda_integer_median`** (L13877) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1`; #3222; PR #4891; candidate `9aeb32700cfa`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-integer-median-a1` (audit v1); names: `fiw_tb_tda_im_median_exists`, `fiw_tb_tda_im_median_bounds`, `fiw_tb_tda_im_median_minimizes`, `fiw_tb_tda_im_mean_deviation`.
- **`fiw_tb_tda_ps_translation_ball`** (L13893) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.translation_ball-a1`; #3651; PR #4410; candidate `77269f38dfbf`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-sum-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-281bd427d2` (audit v1); names: —.
- **`fiw_tb_tda_ps_ball_volume_le`** (L13943) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.ball_volume-a1`; #3660; PR #4316; candidate `a5b46600e539`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-sum-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-c5f2db523d` (audit v1); names: —.
- **`fiw_tb_tda_lattice_cubes`** (L13969) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_cubes-a1`; #3229; PR #3985; candidate `890c3df1bb86`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-lattice-cubes-a1` (audit v1); names: —.
- **`fiw_tb_tda_density_current`** (L14110) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density_current-a1`; #3245; PR #3763; candidate `70c43b4108de`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-density-current-a1` (audit v1); names: —.
- **`fiw_tb_tda_locally_constant_im`** (L14195) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.locally_constant_im-a1`; #3235; PR #3747; candidate `c25a422643ef`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-locally-377642f7dc` (audit v1); names: —.
- **`fiw_tb_tda_lattice_chain`** (L14320) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_chain-a1`; #3256; PR #4127; candidate `81167a2ae0e1`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-lattice-chain-a1` (audit v1); names: `fiw_tb_tda_lattice_cubes`, `fiw_tb_tda_density_current`, `fiw_tb_tda_locally_constant_im`.
- **`fiw_tb_tda_sub_mass`** (L14458) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.sub_mass-a1`; #3269; PR #3774; candidate `91ab1f42b165`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-sub-mass-a1` (audit v1); names: —.
- **`fiw_tb_tda_poincare_sum`** (L14520) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1`; #3284; PR #4567; candidate `314f515e2ee4`; proof `root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-poincare-sum-a1` (audit v1); names: `fiw_tb_tda_ps_translation_ball`, `fiw_tb_tda_ps_ball_volume_le`, `fiw_tb_tda_lattice_cubes`.
- **`fiw_tb_apply_eq_zero_of_disjoint_support`** (L14579) — node `root.flat_iff_weak-a1.total_boundedness-a1.vanish_off_support-a1`; #2338; PR #2949; candidate `702dace4538c`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-vanish-off-support-a1` (audit v5); names: —.
- **`fiw_tb_rectifiable_support_null`** (L14642) — node `root.flat_iff_weak-a1.total_boundedness-a1.support_null-a1`; #2343; PR #3216; candidate `590fa7737e34`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-support-null-a1` (audit v5); names: `fiw_tb_apply_eq_zero_of_disjoint_support`.
- **`fiw_tb_restrictDomain_mass_im`** (L14684) — node `root.flat_iff_weak-a1.total_boundedness-a1.restrict_im-a1`; #2351; PR #3878; candidate `d0e028370d07`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-restrict-im-a1` (audit v5); names: `br_restrictDomain_isIntegerMultiplicity`, `fiw_tb_ri_restrictDomain_mass_le`.
- **`fiw_tb_extend_to_univ`** (L14702) — node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`; #2359; PR #4122; candidate `f174a9de703a`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-extend-a1` (audit v5); names: `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_apply_eq_zero_of_disjoint_support`.
- **`fiw_tb_lcc_face_integral_pos`** (L14854) — node `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.face_integral_pos-a1`; #3233; PR #3716; candidate `0f587a14d3c1`; proof `root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1-fac-f1c15dad9e` (audit v1); names: `br_latticeFace_setIntegral_eq_cube`.
- **`fiw_tb_lcc_local_isolating_form`** (L14898) — node `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1`; #3240; PR #3926; candidate `52bf7c0a0b80`; proof `root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1-loc-026881ca38` (audit v1); names: `isoperimetric_coord_covector_eval`, `isoperimetric_lattice_face_cutoff`, `fiw_tb_lcc_face_integral_pos`.
- **`fiw_tb_lattice_chain_coeff`** (L14985) — node `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`; #2364; PR #4146; candidate `5bfbfcbc2a75`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1` (audit v5); names: `isoperimetric_lattice_chain_mass_ge`, `fiw_tb_lcc_local_isolating_form`.
- **`fiw_tb_lattice_coeff_finite`** (L15005) — node `root.flat_iff_weak-a1.total_boundedness-a1.lattice_coeff_finite-a1`; #2369; PR #3065; candidate `c9c7285ac3ad`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-lattice-coeff-finite-a1` (audit v5); names: —.
- **`fiw_tb_te_directional_form`** (L15071) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.directional_form-a1`; #3226; PR #3803; candidate `31080f006414`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-di-c48d2c2c91` (audit v1); names: —.
- **`fiw_tb_te_translation_dual`** (L15200) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.translation_dual-a1`; #3231; PR #3957; candidate `2cdc05826715`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-tr-ceedffce88` (audit v1); names: —.
- **`fiw_tb_te_l1d_smooth_sign_sep`** (L15274) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.smooth_sign_sep-a1`; #3704; PR #4369; candidate `2d57eebed04b`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-duality-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-e2a3a640a8` (audit v1); names: —.
- **`fiw_tb_te_l1d_compact_sign_approx`** (L15330) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.compact_sign_approx-a1`; #3719; PR #4412; candidate `dd6b43de71c2`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-duality-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-67826f76cb` (audit v1); names: —.
- **`fiw_tb_flat_sub`** (L15415) — node `root.flat_iff_weak-a1.total_boundedness-a1.flat_sub-a1`; #2403; PR #3177; candidate `9dc32d5162c1`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-flat-sub-a1` (audit v5); names: —.
- **`fiw_flat_to_weak`** (L15470) — node `root.flat_iff_weak-a1.flat_to_weak-a1`; #806; PR #1760; candidate `92fbe5f913e3`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-flat-to-weak-a1` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`.
- **`fiw_ims_series_current`** (L15531) — node `root.flat_iff_weak-a1.im_series-a1.series_current-a1`; #1247; PR #2977; candidate `2065ad1fee8c`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-series-current-a1` (audit v1); names: `fiw_ims_sc_testForm_bounded`, `fiw_ims_sc_continuous_of_bound`, `fiw_ims_sc_series_bound`, `fiw_ims_mass_bound`.
- **`fiw_tl_blowup_setIntegral`** (L26010) — node `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1`; #2157; PR #2950; candidate `91a22d1bfc90`; proof `root-flat-iff-weak-a1-tangent-locality-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1` (audit v3); names: —.
- **`fiw_im_mass_formula`** (L31087) — node `root.flat_iff_weak-a1.im_mass_formula-a1`; #814; PR #1823; candidate `83e1f61809c1`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-im-mass-formula-a1` (audit v1); names: —.
- **`fiw_ims_frame_sign`** (L36208) — node `root.flat_iff_weak-a1.im_series-a1.frame_sign-a1`; #1249; PR #1761; candidate `c90a40505abd`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1` (audit v1); names: —.
- **`fiw_ims_orientation_sign`** (L37415) — node `root.flat_iff_weak-a1.im_series-a1.orientation_sign-a1`; #1250; PR #2002; candidate `6f506c46bb4e`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-orientation-sign-a1` (audit v1); names: `fiw_ims_frame_sign`.
- **`fiw_ims_overlap_finite`** (L63069) — node `root.flat_iff_weak-a1.im_series-a1.overlap_finite-a1`; #1252; PR #1542; candidate `02fc45016615`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-overlap-finite-a1` (audit v1); names: —.
- **`fiw_ims_tt_term_bound`** (L63158) — node `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.term_bound-a1`; #1484; PR #2241; candidate `3446f5312c3a`; proof `root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1/children/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-term-bound-a1` (audit v1); names: `fiw_ims_tt_unit_bound`.
- **`fiw_ims_tsum_tau`** (L63232) — node `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`; #1253; PR #2298; candidate `a079caed8454`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1` (audit v1); names: `fiw_ims_tt_term_bound`.
- **`fiw_ims_combine`** (L63314) — node `root.flat_iff_weak-a1.im_series-a1.im_combine-a1`; #1254; PR #2679; candidate `db32c8c94202`; proof `root-flat-iff-weak-a1-im-series-a1/children/root-flat-iff-weak-a1-im-series-a1-im-combine-a1` (audit v1); names: `fiw_ims_orientation_sign`, `fiw_ims_overlap_finite`, `fiw_ims_tsum_tau`.
- **`fiw_tl_tr_weighted_diff_bound`** (L63620) — node `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.weighted_diff_bound-a1`; #3257; PR #3743; candidate `0b194113f2f0`; proof `root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1-weigh-bf77e528cf` (audit v1); names: —.
- **`fiw_tl_tr_scaling_limit`** (L63689) — node `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.scaling_limit-a1`; #3275; PR #3717; candidate `0f6aba64e395`; proof `root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1-scaling-limit-a1` (audit v1); names: —.
- **`fiw_tl_growth_bound`** (L63748) — node `root.flat_iff_weak-a1.tangent_locality-a1.growth_bound-a1`; #2161; PR #3273; candidate `2a9dc9351920`; proof `root-flat-iff-weak-a1-tangent-locality-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-growth-bound-a1` (audit v3); names: `fiw_tl_blowup_setIntegral`.
- **`fiw_tl_transfer`** (L63833) — node `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1`; #2173; PR #3907; candidate `f79cbc10fe41`; proof `root-flat-iff-weak-a1-tangent-locality-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-pointwise-transfer-a1` (audit v3); names: `fiw_tl_blowup_setIntegral`, `fiw_tl_tr_weighted_diff_bound`, `fiw_tl_tr_scaling_limit`, `fiw_tl_growth_bound`.
- **`fiw_tl_ald_ball_reduction`** (L63892) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.ball_reduction-a1`; #3174; PR #3646; candidate `92d0d93e6471`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-ball-reduction-a1` (audit v1); names: —.
- **`fiw_tl_ald_ld_weighted_lebesgue_point`** (L63921) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_lebesgue_point-a1`; #3622; PR #4293; candidate `19e517b0daf0`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-09eb4db1f4/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-6b3918658c` (audit v1); names: —.
- **`fiw_tl_ald_ld_weighted_density_point`** (L63995) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_density_point-a1`; #3626; PR #4372; candidate `fa6e66cc9288`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-09eb4db1f4/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-1bc0aac58f` (audit v1); names: —.
- **`fiw_tl_ald_closedBall_lebesgue_point`** (L64049) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.closed_ball_lebesgue_point-a1`; #3185; PR #3625; candidate `053bc37acaf4`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-closed-bal-73c57412a9` (audit v1); names: —. *Unused.*
- **`fiw_tl_ald_local_differentiation`** (L64064) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1`; #3194; PR #4541; candidate `f7b69229c6f2`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-09eb4db1f4` (audit v1); names: `fiw_tl_ald_ld_weighted_lebesgue_point`, `fiw_tl_ald_ld_weighted_density_point`.
- **`fiw_tl_ald_pointwise_estimate`** (L64115) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.pointwise_estimate-a1`; #3205; PR #3964; candidate `77e959a3b214`; proof `root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-pointwise-estimate-a1` (audit v1); names: —.
- **`fiw_tl_ae_l1_density`** (L64288) — node `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1`; #2187; PR #4860; candidate `13182a2385ff`; proof `root-flat-iff-weak-a1-tangent-locality-a1/children/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1` (audit v3); names: `fiw_tl_ald_ball_reduction`, `fiw_tl_ald_local_differentiation`, `fiw_tl_ald_pointwise_estimate`.
- **`fiw_tangent_locality`** (L64325) — node `root.flat_iff_weak-a1.tangent_locality-a1`; #809; PR #4919; candidate `e508153288a8`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-tangent-locality-a1` (audit v1); names: `fiw_tl_transfer`, `fiw_tl_ae_l1_density`.
- **`fiw_im_series`** (L64348) — node `root.flat_iff_weak-a1.im_series-a1`; #817; PR #4956; candidate `986c7e45798f`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-im-series-a1` (audit v1); names: `fiw_ims_series_current`, `fiw_im_mass_formula`, `fiw_ims_combine`, `fiw_tangent_locality`.
- **`fiw_im_lincomb`** (L64380) — node `root.flat_iff_weak-a1.im_lincomb-a1`; #819; PR #5044; candidate `fbf0e325eb4f`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-im-lincomb-a1` (audit v1); names: `fiw_im_mass_formula`, `fiw_im_series`.
- **`fiw_localization`** (L64437) — node `root.flat_iff_weak-a1.localization-a1`; #824; PR #5105; candidate `7ece361b32af`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-localization-a1` (audit v1); names: `fiw_im_mass_formula`, `fiw_tangent_locality`, `fiw_im_lincomb`.
- **`fiw_flat_cauchy_limit`** (L65704) — node `root.flat_iff_weak-a1.flat_cauchy_limit-a1`; #828; PR #5080; candidate `25b4585dc2a4`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-flat-cauchy-limit-a1` (audit v1); names: `fiw_fcl_nested_subseq`, `fiw_fcl_telescope_limit`, `fiw_im_series`.
- **`fiw_tb_te_l1_le_of_smooth_dual`** (L69096) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1`; #3237; PR #4570; candidate `58888e426fc3`; proof `root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-duality-a1` (audit v1); names: `fiw_tb_te_l1d_smooth_sign_sep`, `fiw_tb_te_l1d_compact_sign_approx`.
- **`fiw_tb_translation_estimate`** (L69113) — node `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`; #2375; PR #4676; candidate `026be1addf72`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1` (audit v5); names: `fiw_tb_te_abs_apply_le_mul_mass`, `fiw_tb_te_directional_form`, `fiw_tb_te_translation_dual`, `fiw_tb_te_l1_le_of_smooth_dual`.
- **`fiw_tb_top_dim_approx`** (L69167) — node `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`; #2384; PR #4931; candidate `9cc90cbe2d04`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1` (audit v5); names: `fiw_tb_tda_density`, `fiw_tb_tda_integer_median`, `fiw_tb_tda_lattice_cubes`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_tda_poincare_sum`, `fiw_tb_rectifiable_support_null`, `fiw_tb_translation_estimate`.
- **`fiw_tb_finite_net`** (L69233) — node `root.flat_iff_weak-a1.total_boundedness-a1.finite_net-a1`; #2393; PR #5123; candidate `16bd0f6600e7`; proof `root-flat-iff-weak-a1-total-boundedness-a1/children/root-flat-iff-weak-a1-total-boundedness-a1-finite-net-a1` (audit v5); names: `fiw_tb_restrictDomain_mass_im`, `fiw_tb_extend_to_univ`, `fiw_tb_lattice_chain_coeff`, `fiw_tb_lattice_coeff_finite`, `fiw_tb_top_dim_approx`.
- **`fiw_total_boundedness`** (L69407) — node `root.flat_iff_weak-a1.total_boundedness-a1`; #826; PR #5211; candidate `efabafdb22bd`; proof `root-flat-iff-weak-a1/children/root-flat-iff-weak-a1-total-boundedness-a1` (audit v1); names: `fiw_tb_flat_sub`, `fiw_im_mass_formula`, `fiw_im_lincomb`, `fiw_tb_finite_net`.
- **`flat_convergence_iff_weak_convergence`** (L69448) — node `root.flat_iff_weak-a1`; #338; PR #8796; candidate `7c119a556b4c`; proof `root/children/root-flat-iff-weak-a1` (audit v3); names: `fiw_flat_to_weak`, `fiw_localization`, `fiw_flat_cauchy_limit`, `slicing_theorem`, `deformation_theorem`, `boundary_rectifiability`, `fiw_total_boundedness`.

### A.10 Subtree `root.rectifiability-a1` (52 declarations)

- **`rpn_moc_abs_covector_apply_le`** (L2632) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.covector_eval_bound-a1`; #3337; PR #3967; candidate `cc8052a37b59`; proof `root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-covecto-538f3c47f1` (audit v1); names: `cmb_covector_eq_sum_coord_smul_wedge`, `cmb_rb_abs_euclideanCovectorCoordinate_le`.
- **`rpn_moc_abs_nvector_apply_le`** (L2652) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.nvector_pairing_bound-a1`; #3346; PR #4030; candidate `cbeda6fb55c2`; proof `root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-nvector-921e87f034` (audit v1); names: `cmb_covector_eq_sum_coord_smul_wedge`.
- **`rpn_moc_exists_testForm_smul`** (L2675) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.scalar_test_form-a1`; #3352; PR #3955; candidate `66a361cb9eac`; proof `root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-scalar-fdc1a20902` (audit v1); names: —.
- **`rpn_moc_abs_apply_le_mul_measure_diff`** (L2685) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.remainder_bound-a1`; #3361; PR #3951; candidate `6b2bcfc06b11`; proof `root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-remainder-bound-a1` (audit v1); names: —.
- **`rpn_moc_abs_apply_top_form_le`** (L2723) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.top_form_estimate-a1`; #3366; PR #4087; candidate `c3b9daddd1cc`; proof `root-rectifiability-a1-projection-null-a1-mass-off-compact-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1-top-for-a0faf9bbe3` (audit v1); names: `rpn_moc_exists_testForm_smul`, `rpn_moc_abs_apply_le_mul_measure_diff`.
- **`rpn_pe_integral_eq_polar`** (L2811) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.polar_integral-a1`; #3268; PR #3914; candidate `bfa69d4e2629`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-polar-a527f3fd17` (audit v1); names: —.
- **`rpn_pe_inv_norm_pow_ball`** (L2862) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.radial_ball_integral-a1`; #3283; PR #3917; candidate `8c5c1649b711`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-radia-39c55ed54b` (audit v1); names: —.
- **`rpn_pe_inv_norm_pow_set_bound`** (L2902) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.set_integral_bound-a1`; #3297; PR #4125; candidate `40d791a916ac`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-set-i-4caf28148f` (audit v1); names: `rpn_pe_inv_norm_pow_ball`.
- **`rpn_pe_kernel_locallyIntegrable`** (L2991) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_local_integrable-a1`; #3309; PR #4124; candidate `1760770a16a1`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-kerne-c743f8cc19` (audit v1); names: `rpn_pe_inv_norm_pow_ball`.
- **`rpn_pe_convolution_contDiff_fderiv`** (L3023) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.convolution_smooth-a1`; #3319; PR #3979; candidate `920181d0d005`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-convo-c921561884` (audit v1); names: —.
- **`rpn_pe_ray_ftc`** (L3047) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.ray_ftc-a1`; #3323; PR #3996; candidate `cbc8f59ccd3b`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-ray-ftc-a1` (audit v1); names: —.
- **`rpn_pe_kernel_representation`** (L3075) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.representation-a1`; #3333; PR #4288; candidate `e2db51a6e54a`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-repre-14bfcc1c26` (audit v1); names: `rpn_pe_integral_eq_polar`, `rpn_pe_kernel_locallyIntegrable`, `rpn_pe_convolution_contDiff_fderiv`, `rpn_pe_ray_ftc`.
- **`rpn_pe_kernel_sup_bound`** (L3137) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_sup_bound-a1`; #3343; PR #4318; candidate `6d0076523601`; proof `root-rectifiability-a1-projection-null-a1-potential-estimate-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1-kerne-a332e93299` (audit v1); names: `rpn_pe_inv_norm_pow_set_bound`.
- **`rpn_potential_estimate`** (L3205) — node `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`; #2387; PR #4510; candidate `7a14a1d4d1a3`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-potential-estimate-a1` (audit v3); names: `rpn_pe_kernel_locallyIntegrable`, `rpn_pe_convolution_contDiff_fderiv`, `rpn_pe_kernel_representation`, `rpn_pe_kernel_sup_bound`.
- **`rpn_pfd_wedge_cons_isLinearMap`** (L3227) — node `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_linear-a1`; #3016; PR #3705; candidate `ba0b2468925a`; proof `root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/children/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-3ac24e3c8c` (audit v1); names: —.
- **`rpn_pfd_wedge_cons_succAbove_sign`** (L3249) — node `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_sign-a1`; #3030; PR #3700; candidate `3ceb8b21a8d3`; proof `root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/children/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-38d99b91f4` (audit v1); names: —.
- **`rpn_pfd_extDeriv_sum_smul_wedge`** (L3280) — node `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.extderiv_sum_wedge-a1`; #3043; PR #3685; candidate `abdbf10e529f`; proof `root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/children/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-7ce573defd` (audit v1); names: —.
- **`rpn_pfd_wedge_cons_comp_succAbove`** (L3297) — node `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.divergence_term-a1`; #3053; PR #3923; candidate `c036e4d501ae`; proof `root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/children/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a-aaad8721ed` (audit v1); names: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_wedge_cons_succAbove_sign`.
- **`rpn_extDeriv_potential_form`** (L3339) — node `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`; #2396; PR #4117; candidate `a5ff80bf4604`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1` (audit v3); names: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`, `rpn_pfd_wedge_cons_comp_succAbove`.
- **`rpn_abs_apply_le_opNorm_mul_massOn`** (L3411) — node `root.rectifiability-a1.projection_null-a1.mass_bound_opnorm-a1`; #2404; PR #3430; candidate `e20ff737992d`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-mass-bound-opnorm-a1` (audit v3); names: `cmb_abs_apply_le_of_massOn_le`, `fiw_ims_sc_covectorNorm_le_opNorm`.
- **`rpn_pullback_top_form_bound`** (L3466) — node `root.rectifiability-a1.projection_null-a1.pullback_top_form_bound-a1`; #2415; PR #4672; candidate `63289e938b29`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-pullback-top-form-bound-a1` (audit v3); names: `rpn_potential_estimate`, `rpn_extDeriv_potential_form`, `rpn_abs_apply_le_opNorm_mul_massOn`.
- **`rpn_covector_rotated_expansion`** (L3664) — node `root.rectifiability-a1.projection_null-a1.covector_rotated_expansion-a1`; #2428; PR #3507; candidate `3eab42406376`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-covector-rotated-expansion-a1` (audit v3); names: `polyhedral_approx_pairing_wedge_kronecker`, `polyhedral_approx_pairing_covector_ext`.
- **`rpn_null_compact_cutoff`** (L3695) — node `root.rectifiability-a1.projection_null-a1.null_compact_cutoff-a1`; #2441; PR #3150; candidate `bba2aab98b8e`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-null-compact-cutoff-a1` (audit v3); names: —.
- **`rpn_massOn_le_mul_measure_diff`** (L3721) — node `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`; #2448; PR #4819; candidate `7bfb5ff2b576`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-mass-off-compact-a1` (audit v3); names: `rpn_moc_abs_covector_apply_le`, `rpn_moc_abs_nvector_apply_le`, `rpn_moc_exists_testForm_smul`, `rpn_moc_abs_apply_top_form_le`, `rpn_pullback_top_form_bound`, `rpn_covector_rotated_expansion`, `rpn_null_compact_cutoff`.
- **`rpn_compact_null_of_le_mul_diff`** (L3812) — node `root.rectifiability-a1.projection_null-a1.compact_null-a1`; #2454; PR #3085; candidate `29906e26815f`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-compact-null-a1` (audit v3); names: —.
- **`rpn_null_of_compact_null`** (L3988) — node `root.rectifiability-a1.projection_null-a1.borel_null-a1`; #2462; PR #3116; candidate `58ab32bdb910`; proof `root-rectifiability-a1-projection-null-a1/children/root-rectifiability-a1-projection-null-a1-borel-null-a1` (audit v3); names: —.
- **`rectifiability_mass_measure_representation`** (L18946) — node `root.rectifiability-a1.mass_measure_representation-a1`; #1019; PR #1843; candidate `b4c070e13355`; proof `root-rectifiability-a1/children/root-rectifiability-a1-mass-measure-representation-a1` (audit v2); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`, `cmb_covector_eq_sum_coord_smul_wedge`, `br_la_apply_eq_zero_of_lt_degree`, `cmb_exists_testForm_uniform_approx`.
- **`rectifiability_density_comparison`** (L32149) — node `root.rectifiability-a1.density_comparison-a1`; #1025; PR #1661; candidate `c5336e1a1413`; proof `root-rectifiability-a1/children/root-rectifiability-a1-density-comparison-a1` (audit v2); names: —.
- **`rectifiability_weighted_tangent_ae`** (L38115) — node `root.rectifiability-a1.weighted_tangent_ae-a1`; #1036; PR #1762; candidate `2f3657605e57`; proof `root-rectifiability-a1/children/root-rectifiability-a1-weighted-tangent-ae-a1` (audit v2); names: `cmb_exists_compactly_contained_exhaustion`, `br_weightedTangent_congr`.
- **`rectifiability_orientation`** (L38735) — node `root.rectifiability-a1.orientation-a1`; #1039; PR #1918; candidate `537363e208ed`; proof `root-rectifiability-a1/children/root-rectifiability-a1-orientation-a1` (audit v2); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`, `cmb_covector_eq_sum_coord_smul_wedge`, `rectifiability_mass_measure_representation`, `rectifiability_density_comparison`, `rectifiability_weighted_tangent_ae`.
- **`rectifiability_projection_null`** (L54258) — node `root.rectifiability-a1.projection_null-a1`; #1021; PR #4899; candidate `63af27b0b88c`; proof `root-rectifiability-a1/children/root-rectifiability-a1-projection-null-a1` (audit v2); names: `rpn_massOn_le_mul_measure_diff`, `rpn_compact_null_of_le_mul_diff`, `rpn_null_of_compact_null`, `rectifiability_mass_measure_representation`.
- **`rectifiability_mass_measure_abs_continuous`** (L54283) — node `root.rectifiability-a1.mass_measure_abs_continuous-a1`; #1023; PR #4950; candidate `f5968e33198f`; proof `root-rectifiability-a1/children/root-rectifiability-a1-mass-measure-abs-continuous-a1` (audit v2); names: `rectifiability_projection_null`.
- **`rectifiability_bf_infinite_fibre_null`** (L59757) — node `root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1`; #1434; PR #2320; candidate `a31774a4af2a`; proof `root-rectifiability-a1-bf-projection-null-ae-a1/children/root-rectifiability-a1-bf-projection-null-ae-a1-infinite-fibre-null-a1` (audit v1); names: —.
- **`rectifiability_bf_cone_density`** (L59866) — node `root.rectifiability-a1.bf_cone_density-a1`; #1027; PR #1854; candidate `fbc29839ab61`; proof `root-rectifiability-a1/children/root-rectifiability-a1-bf-cone-density-a1` (audit v2); names: —.
- **`rectifiability_mickle_rado_limsup_eq_iInf`** (L60368) — node `root.rectifiability-a1.mickle_rado-a1.limsup_eq_iinf-a1`; #2489; PR #3144; candidate `cfa90d4234cc`; proof `root-rectifiability-a1-mickle-rado-a1/children/root-rectifiability-a1-mickle-rado-a1-limsup-eq-iinf-a1` (audit v1); names: —.
- **`rectifiability_mickle_rado_sup_lsc`** (L60380) — node `root.rectifiability-a1.mickle_rado-a1.sup_lsc-a1`; #2500; PR #3328; candidate `c24b145c9e3f`; proof `root-rectifiability-a1-mickle-rado-a1/children/root-rectifiability-a1-mickle-rado-a1-sup-lsc-a1` (audit v1); names: —.
- **`rectifiability_mickle_rado_vitali_bound`** (L60408) — node `root.rectifiability-a1.mickle_rado-a1.vitali_bound-a1`; #2513; PR #3460; candidate `5ffa2b8672c5`; proof `root-rectifiability-a1-mickle-rado-a1/children/root-rectifiability-a1-mickle-rado-a1-vitali-bound-a1` (audit v1); names: —.
- **`rectifiability_mickle_rado_density_zero`** (L60495) — node `root.rectifiability-a1.mickle_rado-a1.density_zero-a1`; #2525; PR #3523; candidate `c75bb5e20a2f`; proof `root-rectifiability-a1-mickle-rado-a1/children/root-rectifiability-a1-mickle-rado-a1-density-zero-a1` (audit v1); names: `rectifiability_mickle_rado_vitali_bound`.
- **`rectifiability_mickle_rado`** (L60571) — node `root.rectifiability-a1.mickle_rado-a1`; #1029; PR #3734; candidate `751505bb8069`; proof `root-rectifiability-a1/children/root-rectifiability-a1-mickle-rado-a1` (audit v2); names: `rectifiability_mickle_rado_limsup_eq_iInf`, `rectifiability_mickle_rado_sup_lsc`, `rectifiability_mickle_rado_density_zero`.
- **`rectifiability_bf_limsup_sup_measurable`** (L60653) — node `root.rectifiability-a1.bf_trichotomy-a1.limsup_sup_measurable-a1`; #4574; PR #4999; candidate `95211c7af512`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-limsup-sup-measurable-a1` (audit v1); names: `rectifiability_mickle_rado_limsup_eq_iInf`.
- **`rectifiability_bf_witness_set_measurable`** (L60801) — node `root.rectifiability-a1.bf_trichotomy-a1.witness_set_measurable-a1`; #4583; PR #4977; candidate `79eed5da6c76`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-witness-set-measurable-a1` (audit v1); names: —.
- **`rectifiability_bf_cone_ratio_measurable`** (L60879) — node `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_measurable-a1`; #4591; PR #5081; candidate `7e1169c130d8`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-cone-ratio-measurable-a1` (audit v1); names: `rectifiability_bf_limsup_sup_measurable`.
- **`rectifiability_bf_cone_ratio_reduction`** (L60918) — node `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_reduction-a1`; #4594; PR #5043; candidate `1bff34429405`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-cone-ratio-reduction-a1` (audit v1); names: —.
- **`rectifiability_bf_fibre_cone_comparison`** (L61032) — node `root.rectifiability-a1.bf_trichotomy-a1.fibre_cone_comparison-a1`; #4600; PR #4962; candidate `ec1bc95d1c91`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-fibre-cone-comparison-a1` (audit v1); names: —.
- **`rectifiability_bf_slice_density_null`** (L61210) — node `root.rectifiability-a1.bf_trichotomy-a1.slice_density_null-a1`; #4612; PR #5184; candidate `1e007dff3e51`; proof `root-rectifiability-a1-bf-trichotomy-a1/children/root-rectifiability-a1-bf-trichotomy-a1-slice-density-null-a1` (audit v1); names: `rectifiability_mickle_rado`, `rectifiability_bf_limsup_sup_measurable`, `rectifiability_bf_witness_set_measurable`.
- **`rectifiability_bf_trichotomy`** (L61537) — node `root.rectifiability-a1.bf_trichotomy-a1`; #1031; PR #5210; candidate `21c4318dcfc4`; proof `root-rectifiability-a1/children/root-rectifiability-a1-bf-trichotomy-a1` (audit v2); names: `rectifiability_bf_witness_set_measurable`, `rectifiability_bf_cone_ratio_measurable`, `rectifiability_bf_cone_ratio_reduction`, `rectifiability_bf_fibre_cone_comparison`, `rectifiability_bf_slice_density_null`.
- **`rectifiability_positive_density_cover_null`** (L61617) — node `root.rectifiability-a1.mass_measure_rectifiable-a1.positive_density_cover_null-a1`; #2490; PR #3417; candidate `d5eadc8d2eab`; proof `root-rectifiability-a1-mass-measure-rectifiable-a1/children/root-rectifiability-a1-mass-measure-rectifiable-a1-positive-density-c-4b4a9741fc` (audit v1); names: `rectifiability_density_comparison`.
- **`rectifiability_rn_positive_real_density`** (L61670) — node `root.rectifiability-a1.mass_measure_rectifiable-a1.rn_positive_density-a1`; #2502; PR #3489; candidate `84cf3d4ed0c1`; proof `root-rectifiability-a1-mass-measure-rectifiable-a1/children/root-rectifiability-a1-mass-measure-rectifiable-a1-rn-positive-density-a1` (audit v1); names: —.
- **`rectifiability_bf_projection_null_ae`** (L61719) — node `root.rectifiability-a1.bf_projection_null_ae-a1`; #1033; PR #5265; candidate `14ad28770cb6`; proof `root-rectifiability-a1/children/root-rectifiability-a1-bf-projection-null-ae-a1` (audit v2); names: `lpf_lli_inner_compact_approx`, `rectifiability_density_comparison`, `rectifiability_bf_infinite_fibre_null`, `rectifiability_bf_cone_density`, `rectifiability_bf_trichotomy`.
- **`rectifiability_structure_projection`** (L61823) — node `root.rectifiability-a1.structure_projection-a1`; #1034; PR #5322; candidate `2fe9c1f38968`; proof `root-rectifiability-a1/children/root-rectifiability-a1-structure-projection-a1` (audit v2); names: `rectifiability_bf_projection_null_ae`.
- **`rectifiability_mass_measure_rectifiable`** (L62354) — node `root.rectifiability-a1.mass_measure_rectifiable-a1`; #1041; PR #5390; candidate `15bc3161e8f8`; proof `root-rectifiability-a1/children/root-rectifiability-a1-mass-measure-rectifiable-a1` (audit v2); names: `cmb_exists_compactly_contained_exhaustion`, `rectifiability_projection_null`, `rectifiability_mass_measure_abs_continuous`, `rectifiability_positive_density_cover_null`, `rectifiability_rn_positive_real_density`, `rectifiability_structure_projection`.
- **`rectifiability_theorem`** (L62437) — node `root.rectifiability-a1`; #340; PR #5445; candidate `ba8a5544bc76`; proof `root/children/root-rectifiability-a1` (audit v3); names: `rectifiability_mass_measure_representation`, `rectifiability_orientation`, `rectifiability_mass_measure_rectifiable`.

### A.11 Subtree `root.integrality_weak_limits-a1` (125 declarations)

- **`iwl_cr_ip_restrict_preimage_eq_map`** (L5695) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.measure_identity-a1`; #3637; PR #4381; candidate `6424bb62b377`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e` (audit v1); names: —.
- **`iwl_cr_ip_pt_slab_restrict_eq_map`** (L5725) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.slab_measure-a1`; #4380; PR #4869; candidate `fddc02f51371`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef18668740` (audit v1); names: —.
- **`iwl_cr_ip_pt_slab_transfer`** (L5788) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.slab_transfer-a1`; #4385; PR #4903; candidate `c3e8cccfe06c`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-86e1067e55` (audit v1); names: `iwl_cr_ip_pt_slab_restrict_eq_map`.
- **`iwl_cr_ip_slice_formula`** (L5850) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.slice_formula-a1`; #3658; PR #4373; candidate `e6904fcdefe0`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-930be90ff5` (audit v1); names: —.
- **`iwl_cr_ip_pt_cylinder_nullMeasurableSet`** (L5944) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.cylinder_null_measurable-a1`; #4394; PR #4911; candidate `ecdea5cf8fdc`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-d977ae51b5` (audit v1); names: —.
- **`iwl_cr_ip_pt_cylinder_countablyRectifiable`** (L5972) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.cylinder_rectifiable-a1`; #4404; PR #4856; candidate `29efe5550b5b`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-88af6a3516` (audit v1); names: —.
- **`iwl_cr_ip_pt_frame_orthonormal`** (L6036) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.frame_orthonormal-a1`; #4414; PR #4892; candidate `32d81ccbe658`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-8df05ea64f` (audit v1); names: —.
- **`iwl_cr_ip_wt_product_plane`** (L6077) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_plane-a1`; #4515; PR #4975; candidate `024164877fb4`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-8488f4fb5b` (audit v1); names: —.
- **`iwl_weighted_tangent_locality`** (L11052) — node `root.integrality_weak_limits-a1.tangent_locality-a1`; #927; PR #2748; candidate `96e830881daf`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-tangent-locality-a1` (audit v1); names: —.
- **`iwl_imc_quotient_rescale_tendsto_zero`** (L11439) — node `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1.quotient_rescale-a1`; #4144; PR #4696; candidate `02defef5b53b`; proof `root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1/children/root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1-5ae7522cf5` (audit v1); names: —.
- **`iwl_imc_tau_measure_representation`** (L11472) — node `root.integrality_weak_limits-a1.im_closure-a1.tau_repr-a1`; #2809; PR #3694; candidate `3b2abc0b5a5e`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-tau-repr-a1` (audit v2); names: `ltg_tau_integrable`.
- **`iwl_rl_monotone_helly_selection`** (L11495) — node `root.integrality_weak_limits-a1.restriction_limit-a1.helly_selection-a1`; #2477; PR #3497; candidate `a66a1c569019`; proof `root-integrality-weak-limits-a1-restriction-limit-a1/children/root-integrality-weak-limits-a1-restriction-limit-a1-helly-selection-a1` (audit v3); names: —.
- **`iwl_rl_testForm_smooth_cutoff`** (L11547) — node `root.integrality_weak_limits-a1.restriction_limit-a1.testform_cutoff-a1`; #2487; PR #3469; candidate `95d4fa1296da`; proof `root-integrality-weak-limits-a1-restriction-limit-a1/children/root-integrality-weak-limits-a1-restriction-limit-a1-testform-cutoff-a1` (audit v3); names: —.
- **`iwl_rl_massOn_iUnion_monotone`** (L11596) — node `root.integrality_weak_limits-a1.restriction_limit-a1.mass_iunion-a1`; #2496; PR #3480; candidate `fc246393d257`; proof `root-integrality-weak-limits-a1-restriction-limit-a1/children/root-integrality-weak-limits-a1-restriction-limit-a1-mass-iunion-a1` (audit v3); names: —.
- **`iwl_cr_ce_apply_eq_of_eqOn_nhds_support`** (L11610) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.locality-a1`; #3701; PR #4361; candidate `2bb89d471b76`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-locality-a1` (audit v1); names: `isoperimetric_apply_eq_zero_of_disjoint_support`.
- **`iwl_cr_ce_cutoff_converges_zero`** (L11634) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_null-a1`; #3711; PR #4473; candidate `1ce45c2246fb`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-cutoff-null-a1` (audit v1); names: —.
- **`iwl_cr_ce_cutoff_radial_operator`** (L11734) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_radial-a1`; #3724; PR #4520; candidate `36fae233c91b`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-cut-96c7a5e3c7` (audit v1); names: `iwl_cr_ce_cutoff_converges_zero`.
- **`iwl_cr_cest_radial_coeff_bound`** (L11846) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.radial_coeff_bound-a1`; #3827; PR #4466; candidate `2b063dab92a3`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-cde2281771` (audit v1); names: `isoperimetric_abs_covector_apply_le`.
- **`iwl_cr_cest_cutoff_radial_form`** (L11923) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cutoff_radial_form-a1`; #3831; PR #4489; candidate `6b30182501b5`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-189e154e9b` (audit v1); names: `iwl_cr_cest_radial_coeff_bound`.
- **`iwl_cr_cest_cone_support`** (L11970) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cone_support-a1`; #3836; PR #4458; candidate `87574e154778`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-e49422c02b` (audit v1); names: —.
- **`iwl_cr_cest_mass_le_of_forms`** (L12013) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.mass_le_of_forms-a1`; #3840; PR #4428; candidate `9635524d1d0b`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-18e28a4913` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`.
- **`iwl_cr_ro_intervalIntegral_contDiff`** (L12060) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.parametric_integral-a1`; #3639; PR #4402; candidate `8eb2f9c26c58`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1-04239efcb3` (audit v1); names: —.
- **`iwl_cr_ro_integrand_contDiff_fderiv`** (L12172) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_derivative-a1`; #3645; PR #4470; candidate `12cdbc2068ea`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1-9a5d15d1f6` (audit v1); names: —.
- **`iwl_cr_ro_integrand_iteratedFDeriv_le`** (L12239) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1`; #3652; PR #4425; candidate `a318ea6a76a5`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1-9cae75a529` (audit v1); names: —.
- **`iwl_cr_radial_operator`** (L12404) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`; #2723; PR #4671; candidate `17ec2f4cdda3`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1` (audit v2); names: `iwl_cr_ro_intervalIntegral_contDiff`, `iwl_cr_ro_integrand_contDiff_fderiv`, `iwl_cr_ro_integrand_iteratedFDeriv_le`.
- **`iwl_cr_rh_integrand_identity`** (L12475) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.integrand_identity-a1`; #3503; PR #4243; candidate `79f67f54610d`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-b30921add2` (audit v1); names: —.
- **`iwl_cr_rh_radial_ftc`** (L12523) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.radial_ftc-a1`; #3513; PR #4283; candidate `af76167caf31`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-803e557495` (audit v1); names: —.
- **`iwl_cr_rh_degree_zero`** (L12565) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.degree_zero-a1`; #3520; PR #4109; candidate `4f025a59c215`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1-2f0073f0b4` (audit v1); names: —.
- **`iwl_cr_radial_homotopy`** (L12610) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`; #2729; PR #4464; candidate `0ca2206b7fe4`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-homotopy-a1` (audit v2); names: `iwl_cr_rh_integrand_identity`, `iwl_cr_rh_radial_ftc`, `iwl_cr_rh_degree_zero`.
- **`iwl_cr_support_lemmas`** (L12654) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`; #2732; PR #3563; candidate `02f3305faacf`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1` (audit v2); names: `isoperimetric_apply_eq_zero_of_disjoint_support`.
- **`iwl_cr_cone_exists`** (L12725) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`; #2737; PR #4818; candidate `3a7a4af18cf4`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1` (audit v2); names: `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_radial_operator`.
- **`iwl_cr_cone_estimates`** (L12750) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`; #2743; PR #4825; candidate `ea4ec8d78d8b`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1` (audit v2); names: `iwl_cr_cest_cutoff_radial_form`, `iwl_cr_cest_cone_support`, `iwl_cr_cest_mass_le_of_forms`, `iwl_cr_radial_operator`.
- **`iwl_cr_cone_boundary`** (L12789) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_boundary-a1`; #2754; PR #4828; candidate `0b613484ca22`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-boundary-a1` (audit v2); names: `isoperimetric_apply_eq_zero_of_disjoint_support`, `iwl_cr_radial_operator`, `iwl_cr_radial_homotopy`, `iwl_cr_support_lemmas`.
- **`iwl_cr_ci_ps_slice_integral_eq_zero`** (L12884) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1.slice_integral_vanish-a1`; #4227; PR #4864; candidate `5570cd6a944d`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-product-support-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-product-2072ce06f4` (audit v1); names: `isoperimetric_apply_eq_zero_of_disjoint_support`.
- **`iwl_cr_ci_slice_testForm`** (L12943) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.slice_forms-a1`; #3624; PR #4323; candidate `143edefdefb7`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1` (audit v1); names: —.
- **`iwl_cr_ci_product_support`** (L13041) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1`; #3627; PR #4902; candidate `340c43fe9003`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-product-support-a1` (audit v1); names: `fiw_tb_ext_support_subset`, `iwl_cr_ci_ps_slice_integral_eq_zero`, `iwl_cr_ci_slice_testForm`.
- **`iwl_cr_ci_cutoff_pullback_testForm`** (L13060) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cutoff_pullback-a1`; #3628; PR #4334; candidate `15be873de6f5`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-cutoff-pullback-a1` (audit v1); names: —.
- **`iwl_cr_ci_cone_map`** (L13084) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cone_map-a1`; #3631; PR #4364; candidate `61b7d3fe17a4`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-cone-map-a1` (audit v1); names: —.
- **`iwl_cr_ci_product_cutoff`** (L13161) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_cutoff-a1`; #3638; PR #4286; candidate `b4056df8fa7b`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-product-cutoff-a1` (audit v1); names: —.
- **`iwl_cr_ci_ie_measure_inter_compact_lt_top`** (L13205) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.finite_measure-a1`; #4221; PR #4808; candidate `e3840f8472f6`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-156760a1e1` (audit v1); names: —.
- **`iwl_restriction_theory`** (L19780) — node `root.integrality_weak_limits-a1.restriction_theory-a1`; #938; PR #1873; candidate `b9f9acdc41ea`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-restriction-theory-a1` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`, `cmb_covector_eq_sum_coord_smul_wedge`, `cmb_exists_testForm_uniform_approx`, `lpf_lli_inner_compact_approx`, `polyhedral_approx_pairing_coordinate_bound`, `slicing_ru_smooth_to_continuous`, `slicing_ru_continuous_to_bounded`.
- **`iwl_cr_ip_wt_plane_fubini`** (L25891) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.plane_fubini-a1`; #4521; PR #5025; candidate `0aea135f9e9c`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-dbcd059e9d` (audit v1); names: —.
- **`iwl_cr_ip_wt_product_measure`** (L25968) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_measure-a1`; #4529; PR #5047; candidate `9e7ae814dd79`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-dddba63eb8` (audit v1); names: —.
- **`iwl_cr_ip_wt_blowup_mass_bound`** (L26056) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.blowup_mass_bound-a1`; #4542; PR #4969; candidate `639092d37fab`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-d97e5caf7c` (audit v1); names: `fiw_tl_blowup_setIntegral`.
- **`iwl_cr_ip_wt_slice_identity`** (L26166) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_identity-a1`; #4556; PR #5082; candidate `2a4a92124eab`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-13379a7a02` (audit v1); names: `iwl_cr_ip_wt_product_measure`, `fiw_tl_blowup_setIntegral`.
- **`iwl_cr_ip_wt_slice_continuous`** (L26346) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_continuous-a1`; #4572; PR #4944; candidate `ffd57024c4c6`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-94ec7e89b7` (audit v1); names: `fiw_tl_blowup_setIntegral`.
- **`iwl_cr_ip_product_weighted_tangent`** (L26428) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`; #3643; PR #5113; candidate `76601b1d3ec9`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8` (audit v1); names: `iwl_cr_ip_wt_product_plane`, `iwl_cr_ip_wt_plane_fubini`, `iwl_cr_ip_wt_blowup_mass_bound`, `iwl_cr_ip_wt_slice_identity`, `iwl_cr_ip_wt_slice_continuous`.
- **`iwl_cr_ip_product_triple`** (L26535) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1`; #3649; PR #5197; candidate `65a29dad072e`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144` (audit v1); names: `iwl_cr_ip_pt_slab_transfer`, `iwl_cr_ip_pt_cylinder_nullMeasurableSet`, `iwl_cr_ip_pt_cylinder_countablyRectifiable`, `iwl_cr_ip_pt_frame_orthonormal`, `iwl_cr_ip_product_weighted_tangent`.
- **`iwl_cr_ci_ie_nvector_intervalIntegral`** (L26683) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.nvector_integral-a1`; #4230; PR #4760; candidate `2136a7f0eda5`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-5b296a6678` (audit v1); names: —.
- **`iwl_cr_ci_ie_param_fubini`** (L26706) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.param_fubini-a1`; #4242; PR #4817; candidate `db77a916adae`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-f33eeed7da` (audit v1); names: `iwl_cr_ci_ie_nvector_intervalIntegral`.
- **`iwl_cr_ci_integral_exchange`** (L26756) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`; #3644; PR #4887; candidate `533e83aac5a2`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa` (audit v1); names: `fiw_ims_tt_unit_bound`, `iwl_cr_ci_ie_measure_inter_compact_lt_top`, `iwl_cr_ci_ie_param_fubini`.
- **`iwl_cr_hp_cylinder_null`** (L26829) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.cylinder_null-a1`; #3756; PR #4465; candidate `52fc2ee0c0a4`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-b10d4bf3df` (audit v1); names: —.
- **`iwl_cr_hp_injective_pieces`** (L27106) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1`; #3758; PR #4437; candidate `d4b1082b0720`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1bf776162` (audit v1); names: —.
- **`iwl_cr_hp_lift_gram_det`** (L27422) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.lift_gram_det-a1`; #3765; PR #4429; candidate `f70b285845da`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-97503d2128` (audit v1); names: —.
- **`iwl_cr_hp_piece_product`** (L27515) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.piece_product-a1`; #3768; PR #4752; candidate `bcc07a06ddc2`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-b20de720cb` (audit v1); names: `iwl_cr_hp_lift_gram_det`.
- **`iwl_cr_hausdorff_product_formula`** (L28269) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`; #2764; PR #4879; candidate `0bfba9891418`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1` (audit v2); names: `iwl_cr_hp_cylinder_null`, `iwl_cr_hp_injective_pieces`, `iwl_cr_hp_piece_product`.
- **`iwl_cr_interval_product_im`** (L28376) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`; #2777; PR #5237; candidate `55f78c3b410c`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1` (audit v2); names: `ltg_tau_integrable`, `br_loc_tauAction_current`, `iwl_cr_ip_restrict_preimage_eq_map`, `iwl_cr_ip_slice_formula`, `iwl_cr_ip_product_triple`, `iwl_cr_hausdorff_product_formula`.
- **`iwl_sp_exists_compatible_testForm`** (L28631) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1`; #2493; PR #3415; candidate `fd5f1e29719e`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1` (audit v3); names: —.
- **`iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`** (L33001) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.tuple_sum_factorial-a1`; #3255; PR #4119; candidate `5d1a7f344e2f`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-71535d6e53` (audit v1); names: `slicing_mb_wn_sq_sum_eq_factorial_mul`, `slicing_mb_wn_norm_sq_eq_onb_sum`.
- **`iwl_sp_pn_sum_sq_comp_basis_le`** (L33013) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.one_slot_bound-a1`; #3267; PR #3777; candidate `e37372c4d9bc`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-76834dc165` (audit v1); names: —.
- **`iwl_sp_pn_multilinear_sum_sq_le`** (L33060) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.multilinear_bound-a1`; #3281; PR #3828; candidate `82bc30ecd41c`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a-ebd8351d5a` (audit v1); names: `iwl_sp_pn_sum_sq_comp_basis_le`.
- **`iwl_sp_covectorEuclideanNorm_pullback_le`** (L33128) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1`; #2481; PR #4332; candidate `3e52d3e816fb`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1` (audit v3); names: `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`, `iwl_sp_pn_multilinear_sum_sq_le`.
- **`iwl_sp_sn_null_diff_support_of_local_null`** (L35718) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.support_cover-a1`; #3265; PR #3941; candidate `06b135a22629`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-dd527b4f36` (audit v1); names: —.
- **`iwl_sp_sn_covector_separating_family`** (L35747) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.covector_basis-a1`; #3280; PR #3735; candidate `ff6ccae0f524`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-c7051b88b3` (audit v1); names: —.
- **`iwl_sp_sn_signed_simpleNVector_bound_ne_zero`** (L35777) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.signed_simple_bound-a1`; #3295; PR #3943; candidate `b1056f9a9134`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-8f231689a7` (audit v1); names: —.
- **`iwl_sp_sn_weighted_fundamental_lemma`** (L35812) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.weighted_fundamental_lemma-a1`; #3306; PR #3930; candidate `fdcd05b897cd`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-414bde14cc` (audit v1); names: —.
- **`iwl_sp_sn_local_null`** (L35844) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.local_null-a1`; #3316; PR #4158; candidate `ef65e5d55971`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1-38f821d844` (audit v1); names: `iwl_sp_sn_covector_separating_family`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_sp_sn_weighted_fundamental_lemma`.
- **`iwl_sp_rectifiable_support_null`** (L36444) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1`; #2463; PR #4341; candidate `05cea8b8ad1f`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1` (audit v3); names: `iwl_sp_sn_null_diff_support_of_local_null`, `iwl_sp_sn_local_null`.
- **`iwl_cr_cone_integer_multiplicity`** (L36560) — node `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1`; #2781; PR #5305; candidate `45a90f14d36d`; proof `root-integrality-weak-limits-a1-cycle-reduction-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1` (audit v2); names: `iwl_cr_radial_operator`, `iwl_cr_ci_slice_testForm`, `iwl_cr_ci_product_support`, `iwl_cr_ci_cutoff_pullback_testForm`, `iwl_cr_ci_cone_map`, `iwl_cr_ci_product_cutoff`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`.
- **`iwl_im_patching`** (L36691) — node `root.integrality_weak_limits-a1.patching-a1`; #928; PR #2913; candidate `c9a4db0e8a68`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-patching-a1` (audit v1); names: `lpf_simple_nvector_algebra`, `iwl_weighted_tangent_locality`, `slicing_ru_covector_expansion`.
- **`iwl_zero_dim_integrality`** (L37113) — node `root.integrality_weak_limits-a1.zero_dim-a1`; #931; PR #3241; candidate `86ccbcdc8dea`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-zero-dim-a1` (audit v1); names: `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`, `iwl_im_patching`.
- **`iwl_imc_density_zero_off_set`** (L37453) — node `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1`; #2799; PR #4846; candidate `4eb4d55a3670`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-density-zero-off-set-a1` (audit v2); names: `lpf_wtc_ae_zero_density_off_set`, `iwl_imc_quotient_rescale_tendsto_zero`.
- **`iwl_imc_lincomb_im`** (L37473) — node `root.integrality_weak_limits-a1.im_closure-a1.lincomb_im-a1`; #2832; PR #4290; candidate `99bffd2f215d`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-lincomb-im-a1` (audit v2); names: `iwl_imc_tau_measure_representation`, `fiw_ims_orientation_sign`.
- **`iwl_imc_normalized_lebesgue_points`** (L37760) — node `root.integrality_weak_limits-a1.im_closure-a1.lebesgue_points-a1`; #2814; PR #3733; candidate `3047dcd2a39a`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-lebesgue-points-a1` (audit v2); names: `rectifiability_density_comparison`.
- **`iwl_imc_tangent_overlap`** (L37885) — node `root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1`; #2820; PR #4894; candidate `840ab47ea3d0`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-tangent-overlap-a1` (audit v2); names: `iwl_imc_density_zero_off_set`, `iwl_imc_normalized_lebesgue_points`.
- **`iwl_imc_restriction_im`** (L38058) — node `root.integrality_weak_limits-a1.im_closure-a1.restriction_im-a1`; #2825; PR #3911; candidate `5d533f06b26a`; proof `root-integrality-weak-limits-a1-im-closure-a1/children/root-integrality-weak-limits-a1-im-closure-a1-restriction-im-a1` (audit v2); names: `iwl_imc_tau_measure_representation`, `slicing_representation_unique`. *Unused.*
- **`iwl_im_closure`** (L54313) — node `root.integrality_weak_limits-a1.im_closure-a1`; #940; PR #4963; candidate `4c06fc8afebf`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-im-closure-a1` (audit v1); names: `iwl_weighted_tangent_locality`, `iwl_imc_tau_measure_representation`, `slicing_representation_unique`, `iwl_restriction_theory`, `iwl_imc_lincomb_im`, `iwl_imc_tangent_overlap`.
- **`iwl_rl_restriction_cutoff_estimate`** (L54369) — node `root.integrality_weak_limits-a1.restriction_limit-a1.cutoff_estimate-a1`; #2516; PR #3562; candidate `9ca4ad88cb32`; proof `root-integrality-weak-limits-a1-restriction-limit-a1/children/root-integrality-weak-limits-a1-restriction-limit-a1-cutoff-estimate-a1` (audit v3); names: `cmb_abs_apply_le_of_massOn_le`.
- **`iwl_restriction_weak_limit`** (L54463) — node `root.integrality_weak_limits-a1.restriction_limit-a1`; #942; PR #3781; candidate `e20506c047f7`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-restriction-limit-a1` (audit v1); names: `br_la_testForm_covectorNorm_bounded`, `iwl_rl_monotone_helly_selection`, `iwl_rl_testForm_smooth_cutoff`, `iwl_rl_massOn_iUnion_monotone`, `iwl_restriction_theory`, `iwl_rl_restriction_cutoff_estimate`.
- **`iwl_sp_lipschitzPushforward_apply_eq`** (L54651) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.pushforward_formula-a1`; #2471; PR #4547; candidate `67ffac86a718`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-pushforward-formula-a1` (audit v3); names: `iwl_sp_rectifiable_support_null`.
- **`ind_pi_pl_linear_pushforward_family`** (L54686) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1.linear_pushforward_family-a1`; #4617; PR #4964; candidate `71c08df2ed2c`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-a6fca12c5f/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-111b814206` (audit v1); names: —.
- **`ind_pi_frame_geometry`** (L54757) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.frame_geometry-a1`; #4002; PR #4699; candidate `0015dc978bea`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-f-fe9aa3c949` (audit v1); names: —.
- **`ind_pi_span_integral`** (L54862) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.span_integral-a1`; #4009; PR #4677; candidate `c763e84863a7`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-dd20d2b7ae` (audit v1); names: —.
- **`ind_pi_constant_vector_current`** (L54902) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.const_vector_current-a1`; #4018; PR #4693; candidate `daec5514531c`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-c-83ee0c3357` (audit v1); names: —.
- **`ind_pi_restriction_open_im`** (L54958) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.restriction_open_im-a1`; #4026; PR #4754; candidate `da35ec9455ab`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-r-eee2ea0d0e` (audit v1); names: —.
- **`ind_pi_ss_cycle_slice_boundary`** (L55138) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_boundary-a1`; #4628; PR #5137; candidate `014fdc802b43`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-64d2f1b0b6` (audit v1); names: —.
- **`ind_pi_ss_restriction_massOn_le`** (L55172) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.restriction_mass_le-a1`; #4616; PR #5085; candidate `6bffed6a5c5b`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-3e0235bc24` (audit v1); names: —.
- **`ind_md_mmb_massMeasure_balls`** (L55274) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1.mass_measure_ball_values-a1`; #3857; PR #4497; candidate `08dc308eae08`; proof `root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-60c452f574` (audit v2); names: —.
- **`ind_md_mass_measure_balls`** (L55292) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1`; #3258; PR #4665; candidate `c4ef827537f1`; proof `root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ma-046d2fc55f` (audit v1); names: `iwl_restriction_theory`, `ind_md_mmb_massMeasure_balls`.
- **`ind_md_closedBall_weak_subseq`** (L55308) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ball_weak_subseq-a1`; #3276; PR #3766; candidate `7c4d6e5f527b`; proof `root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ba-edf2a04af6` (audit v1); names: —.
- **`ind_md_diagonal_weak_subseq`** (L55413) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.diagonal_weak_subseq-a1`; #3292; PR #3876; candidate `93e13175da02`; proof `root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-di-678fbe0631` (audit v1); names: `ind_md_closedBall_weak_subseq`.
- **`ind_md_ae_closedBall_growth`** (L55467) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ae_ball_growth-a1`; #3304; PR #3778; candidate `1a0587a2278f`; proof `root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ae-f7d60da3e2` (audit v1); names: —.
- **`ind_mass_density_bound`** (L55623) — node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`; #2476; PR #4858; candidate `8a48d5a6777e`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1` (audit v1); names: `ind_md_mass_measure_balls`, `ind_md_diagonal_weak_subseq`, `ind_md_ae_closedBall_growth`.
- **`ind_ab_rescaled_tangent_limit`** (L55657) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.rescaled_tangent_limit-a1`; #3293; PR #4005; candidate `63de75d44548`; proof `root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-resca-f7e12f53ef` (audit v1); names: —.
- **`ind_rs_dilation_measurePreserving`** (L55708) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.dilation_measure-a1`; #3286; PR #3956; candidate `45b4ab0d7c67`; proof `root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-dilatio-b17fbb2af1` (audit v1); names: —.
- **`ind_rs_tauAction_dilation`** (L55749) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.tau_action-a1`; #3317; PR #3939; candidate `f01106583c89`; proof `root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-tau-action-a1` (audit v1); names: —.
- **`ind_ab_weighted_ball_growth`** (L55802) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_ball_growth-a1`; #3305; PR #4126; candidate `b235347887c4`; proof `root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-weigh-e45cd9e0ed` (audit v1); names: `ind_ab_rescaled_tangent_limit`.
- **`ind_ab_weighted_lebesgue_point`** (L55893) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_lebesgue_point-a1`; #3313; PR #3940; candidate `d054ee15516d`; proof `root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-weigh-b112046287` (audit v1); names: —.
- **`ind_ab_orientation_error_vanishes`** (L55975) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1`; #3322; PR #3946; candidate `0f20feb1d8e8`; proof `root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1-orien-132e11848c` (audit v1); names: —.
- **`ind_ae_blowup_limit`** (L56121) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`; #2486; PR #4309; candidate `a3152bb94953`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1` (audit v1); names: `ind_ab_rescaled_tangent_limit`, `ind_ab_weighted_ball_growth`, `ind_ab_weighted_lebesgue_point`, `ind_ab_orientation_error_vanishes`.
- **`ind_rs_weightedTangent_dilation`** (L56227) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.weighted_tangent-a1`; #3298; PR #3767; candidate `1633a21d7a93`; proof `root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-weighte-8b99885143` (audit v1); names: —.
- **`ind_rs_rectifiableTriple_dilation`** (L56266) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.triple_image-a1`; #3310; PR #4205; candidate `49800702c686`; proof `root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-triple-image-a1` (audit v1); names: `ind_rs_dilation_measurePreserving`, `ind_rs_weightedTangent_dilation`.
- **`ind_rs_massOn_dilation_le`** (L56347) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.mass_bound-a1`; #3325; PR #3959; candidate `fe04133f0e47`; proof `root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1-mass-bound-a1` (audit v1); names: —.
- **`ind_rescaled_current`** (L56388) — node `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`; #2495; PR #4395; candidate `36b130395d1b`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1` (audit v1); names: `ind_rs_tauAction_dilation`, `ind_rs_rectifiableTriple_dilation`, `ind_rs_massOn_dilation_le`.
- **`ind_diagonal_weak_limit`** (L56486) — node `root.integrality_weak_limits-a1.integer_density-a1.diagonal-a1`; #2508; PR #3499; candidate `b37cb947f505`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-diagonal-a1` (audit v1); names: —.
- **`ind_pi_ss_cycle_slice_family`** (L56757) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_family-a1`; #4633; PR #5162; candidate `e768182b2864`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-ea88c12991` (audit v1); names: `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`.
- **`ind_pi_ss_fatou_level_selection`** (L56818) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.fatou_level_selection-a1`; #4641; PR #5027; candidate `fbecac1595ff`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-1a1addc5ce` (audit v1); names: —.
- **`ind_pi_good_slice_selection`** (L56851) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1`; #4034; PR #6446; candidate `afa97e5c91a5`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-253346ea31` (audit v1); names: `ind_pi_ss_restriction_massOn_le`, `ind_pi_ss_cycle_slice_family`, `ind_pi_ss_fatou_level_selection`.
- **`ind_pi_localized_cycles`** (L56910) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.localized_cycles-a1`; #4044; PR #5194; candidate `205c2f1bc9ea`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-l-5288b63fc6` (audit v1); names: `fiw_tb_ext_support_subset`, `br_restrictDomain_isIntegerMultiplicity`, `ind_pi_frame_geometry`, `ind_pi_span_integral`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_good_slice_selection`.
- **`ind_pi_projected_limit`** (L57021) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1`; #4053; PR #5053; candidate `363a55563e32`; proof `root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-p-a6fca12c5f` (audit v1); names: `iwl_sp_exists_compatible_testForm`, `ind_pi_pl_linear_pushforward_family`, `ind_pi_frame_geometry`, `ind_pi_span_integral`.
- **`ind_top_orthonormal_frame_sign`** (L57096) — node `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.frame_sign_top-a1`; #3511; PR #4108; candidate `520cbc1489b5`; proof `root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-f-d98902e57d` (audit v1); names: —.
- **`ind_top_form_density_ae_unique`** (L57137) — node `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_density_unique-a1`; #3518; PR #4159; candidate `38e98aa2eb31`; proof `root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-t-2c180ab89c` (audit v1); names: —.
- **`ind_top_dim_integer_density`** (L57219) — node `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_integer_density-a1`; #3525; PR #4291; candidate `5d7d2e528f96`; proof `root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/children/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1-t-da58bc8a39` (audit v1); names: `ind_top_orthonormal_frame_sign`.
- **`ind_const_multiple_integer`** (L57320) — node `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`; #2534; PR #4449; candidate `3cf5b3cf1bbd`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1` (audit v1); names: `ind_top_form_density_ae_unique`, `ind_top_dim_integer_density`.
- **`ind_plane_multiplicity_integer`** (L57351) — node `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1`; #2520; PR #5229; candidate `885b2beaddfa`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1` (audit v1); names: `ind_pi_constant_vector_current`, `ind_pi_localized_cycles`, `ind_pi_projected_limit`, `ind_const_multiple_integer`.
- **`ind_ae_integer_multiplicity`** (L57386) — node `root.integrality_weak_limits-a1.integer_density-a1.ae_integer-a1`; #2546; PR #3551; candidate `0213342518a9`; proof `root-integrality-weak-limits-a1-integer-density-a1/children/root-integrality-weak-limits-a1-integer-density-a1-ae-integer-a1` (audit v1); names: —.
- **`iwl_sp_massOn_le_of_compatible`** (L57452) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.mass_bound-a1`; #2507; PR #4596; candidate `31e47f0afb18`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-mass-bound-a1` (audit v3); names: `iwl_sp_exists_compatible_testForm`, `iwl_sp_covectorEuclideanNorm_pullback_le`.
- **`iwl_sp_boundary_apply_eq_of_compatible`** (L57527) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1.boundary_formula-a1`; #2521; PR #3479; candidate `06e3ced73016`; proof `root-integrality-weak-limits-a1-smooth-pushforward-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1-boundary-formula-a1` (audit v3); names: —.
- **`iwl_smooth_pushforward`** (L57550) — node `root.integrality_weak_limits-a1.smooth_pushforward-a1`; #950; PR #4746; candidate `cec1a3ca9165`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-smooth-pushforward-a1` (audit v1); names: `iwl_sp_lipschitzPushforward_apply_eq`, `iwl_sp_massOn_le_of_compatible`, `iwl_sp_boundary_apply_eq_of_compatible`.
- **`iwl_localization`** (L57577) — node `root.integrality_weak_limits-a1.localization-a1`; #951; PR #5185; candidate `f49fc62e2a30`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-localization-a1` (audit v1); names: `cmb_abs_apply_le_of_massOn_le`, `br_weightedTangent_congr`, `iwl_restriction_theory`, `iwl_im_patching`, `iwl_im_closure`, `iwl_restriction_weak_limit`.
- **`iwl_cycle_reduction`** (L58218) — node `root.integrality_weak_limits-a1.cycle_reduction-a1`; #953; PR #5368; candidate `9801717d461a`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-cycle-reduction-a1` (audit v1); names: `iwl_cr_support_lemmas`, `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_closure`, `iwl_smooth_pushforward`.
- **`iwl_positive_density`** (L58345) — node `root.integrality_weak_limits-a1.positive_density-a1`; #954; PR #4855; candidate `3a6ac5216e97`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-positive-density-a1` (audit v1); names: `cmb_exists_compactly_contained_exhaustion`, `cmb_abs_apply_le_of_massOn_le`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `cmb_covector_eq_sum_coord_smul_wedge`, `slicing_ru_smooth_to_continuous`, `slicing_ru_continuous_to_bounded`, `iwl_restriction_theory`, `iwl_restriction_weak_limit`, `iwl_smooth_pushforward`.
- **`iwl_top_dim_integrality`** (L67311) — node `root.integrality_weak_limits-a1.top_dim-a1`; #934; PR #4089; candidate `e7ec1ab7ad46`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-top-dim-a1` (audit v1); names: `iwl_weighted_tangent_locality`.
- **`iwl_integer_density`** (L68671) — node `root.integrality_weak_limits-a1.integer_density-a1`; #955; PR #5271; candidate `914dbf6c21ef`; proof `root-integrality-weak-limits-a1/children/root-integrality-weak-limits-a1-integer-density-a1` (audit v1); names: `iwl_restriction_weak_limit`, `ind_mass_density_bound`, `ind_ae_blowup_limit`, `ind_rescaled_current`, `ind_diagonal_weak_limit`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_smooth_pushforward`, `iwl_top_dim_integrality`.
- **`integrality_of_weak_limits`** (L68796) — node `root.integrality_weak_limits-a1`; #341; PR #8548; candidate `036fb2d84e9c`; proof `root/children/root-integrality-weak-limits-a1` (audit v3); names: `iwl_zero_dim_integrality`, `lipschitz_pushforward_integer_multiplicity`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `rectifiability_theorem`, `slicing_theorem`, `isoperimetric_theorem`, `iwl_top_dim_integrality`, `iwl_integer_density`.

### A.12 Subtree `root.federer_fleming-a1` (1 declarations)

- **`federer_fleming_compactness`** (L69482) — node `root.federer_fleming-a1`; #342; PR #8802; candidate `5abeab044087`; proof `root/children/root-federer-fleming-a1` (audit v3); names: `integrality_of_weak_limits`, `boundary_rectifiability`, `compactness_under_mass_bounds`.

## Appendix B. SimonGMT constants used directly

The 164 constants of the `simongmt` package (revision `2b3663083f3fe399b6296fb8eaee52169170e197`)
to which the 692 theorems of `Submission.lean` refer directly, read from the compiled environment
(§9; references through Lean-generated auxiliary constants are attributed to the theorem that
generated them): 107 theorems (one of them the field `continuous'` of the structure
`GeometricCurrentOn`), 55 definitions, and the structure `GeometricCurrentOn` with its constructor.
They are grouped by module (namespace prefix `Poincare.SimonGMT.` omitted). After each theorem come
the accepted declarations that refer to it; after each definition, the number of accepted
declarations that refer to it. Names ending in `._proof_N` or `.eq_N` are auxiliary constants that
Lean generated inside SimonGMT for the definition named before them.

**`Poincare.SimonGMT.Chapter01.Basic`**

- definition `Chapter01.IsCaratheodoryMeasurable`: 1 declaration
- theorem `Chapter01.measure_toOuterMeasure_isBorelRegular`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter01.Densities`**

- definition `Chapter01.dimensionalDensityQuotient`: 7 declarations
- theorem `Chapter01.dimensionalDensityQuotient.eq_1`: `rectifiability_density_comparison`, `ind_md_ae_closedBall_growth`
- definition `Chapter01.dimensionalUpperDensity`: 12 declarations
- theorem `Chapter01.volume_closedBall_eq_densityNormalization`: `rectifiability_density_comparison`

**`Poincare.SimonGMT.Chapter01.DensityComparison`**

- theorem `Chapter01.ae_dimensionalUpperDensity_eq_zero_outside`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter01.DensityCovering`**

- theorem `Chapter01.exists_fiveTimesCovering`: `rectifiability_density_comparison`
- theorem `Chapter01.fiveTimesCovering_finite_remainder`: `rectifiability_density_comparison`

**`Poincare.SimonGMT.Chapter01.Hausdorff`**

- definition `Chapter01.realUnitBallVolume`: 7 declarations
- theorem `Chapter01.realUnitBallVolume._proof_1`: `rectifiability_bf_cone_ratio_reduction`
- theorem `Chapter01.realUnitBallVolume.eq_1`: `rectifiability_bf_cone_ratio_reduction`
- theorem `Chapter01.realUnitBallVolume_eq`: `rectifiability_density_comparison`
- theorem `Chapter01.realUnitBallVolume_ne_top`: `rectifiability_density_comparison`, `iwl_imc_normalized_lebesgue_points`, `rectifiability_weighted_tangent_ae`, `rectifiability_orientation`, `ind_md_ae_closedBall_growth`, `iwl_positive_density`
- theorem `Chapter01.realUnitBallVolume_pos`: `rectifiability_density_comparison`, `iwl_imc_normalized_lebesgue_points`, `rectifiability_weighted_tangent_ae`, `rectifiability_orientation`, `ind_md_ae_closedBall_growth`, `iwl_positive_density`
- theorem `Chapter01.realUnitBallVolume_zero`: `rectifiability_density_comparison`
- definition `Chapter01.simonHausdorffMeasureReal`: 1 declaration

**`Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral`**

- theorem `Chapter01.ae_radonCaratheodoryMeasure_iff`: `rectifiability_mass_measure_representation`
- theorem `Chapter01.compactL1DualField_represents_test`: `iwl_restriction_theory`
- theorem `Chapter01.integral_radonCaratheodoryMeasure`: `rectifiability_mass_measure_representation`
- definition `Chapter01.radonCaratheodoryMeasure`: 1 declaration

**`Poincare.SimonGMT.Chapter01.RadonLocalDualField`**

- definition `Chapter01.compactL1DualField`: 1 declaration
- theorem `Chapter01.compactL1DualField_ae_eq_inter`: `iwl_restriction_theory`
- theorem `Chapter01.compactL1DualField_norm_le_one`: `iwl_restriction_theory`
- theorem `Chapter01.compactL1DualField_stronglyMeasurable`: `iwl_restriction_theory`

**`Poincare.SimonGMT.Chapter01.RadonPolarRepresentation`**

- theorem `Chapter01.simon_theorem_4_14_caratheodory`: `rectifiability_mass_measure_representation`

**`Poincare.SimonGMT.Chapter01.VectorFunctionalEnvelope`**

- definition `Chapter01.IsLocallyBoundedCcFunctional`: 2 declarations
- theorem `Chapter01.IsLocallyBoundedCcFunctional._proof_1`: `rectifiability_mass_measure_representation`, `iwl_restriction_theory`
- theorem `Chapter01.IsLocallyBoundedCcFunctional._proof_2`: `rectifiability_mass_measure_representation`, `iwl_restriction_theory`
- theorem `Chapter01.simon_theorem_4_14_positive_envelope`: `rectifiability_mass_measure_representation`, `iwl_restriction_theory`
- definition `Chapter01.vectorFunctionalEnvelopeMeasure`: 2 declarations
- theorem `Chapter01.vectorFunctionalEnvelopeMeasure_regular`: `rectifiability_mass_measure_representation`, `iwl_restriction_theory`

**`Poincare.SimonGMT.Chapter01.VectorFunctionalL1`**

- definition `Chapter01.compactlySupportedToL1`: 1 declaration
- theorem `Chapter01.simon_theorem_4_14_l1_extension`: `iwl_restriction_theory`

**`Poincare.SimonGMT.Chapter02.Area`**

- definition `Chapter02.areaJacobianAt`: 1 declaration
- theorem `Chapter02.areaJacobianAt_eq_normDet`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter02.AreaCritical`**

- theorem `Chapter02.area_image_criticalSet_eq_zero`: `slicing_im_coarea_chart_cover`

**`Poincare.SimonGMT.Chapter02.AreaDomain`**

- theorem `Chapter02.ae_fderivWithin_eq_of_lipschitz_extension`: `lpf_raf_local_lipschitz_area`
- theorem `Chapter02.aemeasurable_weightedAreaFiberSum_lipschitzOn`: `lpf_raf_local_lipschitz_area`
- definition `Chapter02.areaJacobianWithin`: 2 declarations
- theorem `Chapter02.areaJacobianWithin.eq_1`: `lpf_raf_local_lipschitz_area`
- theorem `Chapter02.exists_lipschitz_extension_finiteDimensional`: `lpf_raf_local_lipschitz_area`
- theorem `Chapter02.weighted_area_formula_lipschitzOn_fiberSum`: `lpf_raf_local_lipschitz_area`, `lpf_wtc_chart_area_formula`

**`Poincare.SimonGMT.Chapter02.AreaLinearWeighted`**

- theorem `Chapter02.measurePreserving_linearMap_normDet_smul`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter02.AreaLipschitz`**

- definition `Chapter02.areaRegularSet`: 1 declaration
- theorem `Chapter02.area_image_compl_regularSet_eq_zero`: `rectifiability_weighted_tangent_ae`
- theorem `Chapter02.measurableSet_areaRegularSet`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter02.AreaMultiplicity`**

- definition `Chapter02.areaFiber`: 1 declaration
- definition `Chapter02.weightedAreaFiberSum`: 2 declarations

**`Poincare.SimonGMT.Chapter02.AreaNormalization`**

- definition `Chapter02.simonAreaNormalization`: 1 declaration
- theorem `Chapter02.simonAreaNormalization_pos`: `rectifiability_weighted_tangent_ae`
- theorem `Chapter02.simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter02.Lipschitz`**

- theorem `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`: `slicing_im_st_cd_c1c_singular_compression`, `lpf_pi_source_charts`, `lpf_locally_lipschitz_image`, `lpf_raf_chart_preimage_null`, `lpf_countably_rectifiable_c1_cover`, `iwl_cr_hp_injective_pieces`, `rectifiability_weighted_tangent_ae`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `slicing_im_coarea_chart_cover`, `slicing_im_tg_cc_lipschitz_range_c1_cover`, `slicing_im_tg_cc_contDiff_range_chart_cover`, `slicing_im_st_cd_c1_cover`, `lpf_tde_chart_nondiff_image_null`, `slicing_im_st_chart_data`, `slicing_im_coarea_pieces`, `slicing_im_coarea_chart_critical`, `rectifiability_mass_measure_abs_continuous`, `rectifiability_bf_infinite_fibre_null`, `rectifiability_bf_projection_null_ae`, `rectifiability_structure_projection`

**`Poincare.SimonGMT.Chapter02.WeightedArea`**

- theorem `Chapter02.integrableOn_image_iff_integrableOn_areaJacobian_smul`: `rectifiability_weighted_tangent_ae`
- theorem `Chapter02.integral_area_formula_of_injective_derivative`: `rectifiability_weighted_tangent_ae`

**`Poincare.SimonGMT.Chapter03.Rectifiable`**

- definition `Chapter03.CountablyRectifiable`: 35 declarations
- theorem `Chapter03.CountablyRectifiable.congr_simp`: `iwl_imc_lincomb_im`
- theorem `Chapter03.CountablyRectifiable.mono`: `ltg_glue_triples`, `br_restrictDomain_isIntegerMultiplicity`, `lpf_pi_chart_image_rectifiable`, `lpf_pi_im_of_chart_density`, `br_loc_triple_inter_open`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_locally_constant_im`, `polyhedral_approx_open_truncation`, `iwl_cr_ip_product_triple`, `iwl_cr_hausdorff_product_formula`, `dph_hausdorff_product_formula`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `dmr_rectifiableTriple_inter`, `imc_isRectifiableTriple_of_eventually_mem`, `iwl_im_patching`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_weighted_tangent_ae`, `iwl_im_closure`, `ind_pi_restriction_open_im`, `ind_ae_integer_multiplicity`, `iwl_localization`, `rectifiability_bf_cone_density`, `rectifiability_structure_projection`, `rectifiability_mass_measure_rectifiable`, `fiw_ims_combine`, `fiw_localization`
- definition `Chapter03.HasApproximateTangentSpaceAt`: 12 declarations
- definition `Chapter03.HasWeightedApproximateTangentSpaceAt`: 105 declarations
- theorem `Chapter03.HasWeightedApproximateTangentSpaceAt.unique`: `lpf_pi_source_charts`, `lpf_pi_im_of_chart_density`, `lpf_raf_chart_jacobian_ae`, `slicing_im_ll_tangent_dual_field`, `imc_isRectifiableTriple_of_eventually_mem`, `fiw_ims_orientation_sign`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `lpf_tangential_differential_exists`, `slicing_im_tangential_gradient`, `slicing_im_st_slice_geometry`
- definition `Chapter03.PurelyUnrectifiable`: 4 declarations
- theorem `Chapter03.PurelyUnrectifiable.mono`: `rectifiability_bf_projection_null_ae`, `rectifiability_structure_projection`
- definition `Chapter03.blowUpMap`: 35 declarations
- theorem `Chapter03.countablyRectifiable_iUnion`: `ltg_glue_triples`, `lpf_pi_chart_image_rectifiable`, `lpf_pi_im_of_chart_density`, `imc_isRectifiableTriple_of_eventually_mem`, `iwl_im_patching`, `iwl_imc_lincomb_im`, `fiw_ims_combine`
- theorem `Chapter03.countablyRectifiable_of_measure_zero`: `br_isIntegerMultiplicity_of_local`, `iwl_cr_ip_product_triple`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `imc_isRectifiableTriple_of_eventually_mem`, `iwl_im_patching`, `rectifiability_mass_measure_rectifiable`, `fiw_localization`, `integrality_of_weak_limits`, `fiw_tb_finite_net`
- theorem `Chapter03.countablyRectifiable_range`: `lpf_pi_chart_image_rectifiable`, `fiw_tb_tda_locally_constant_im`, `iwl_cr_ip_wt_plane_fubini`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `rectifiability_bf_cone_density`
- theorem `Chapter03.countablyRectifiable_sUnion`: `br_lattice_chain_boundary_isIntegerMultiplicity`, `rectifiability_mass_measure_rectifiable`
- theorem `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition`: `rectifiability_structure_projection`, `rectifiability_mass_measure_rectifiable`
- theorem `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule`: `iwl_cr_ip_wt_plane_fubini`, `rectifiability_orientation`
- theorem `Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover`: `rectifiability_mass_measure_rectifiable`
- theorem `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule`: `rectifiability_orientation`

**`Poincare.SimonGMT.Chapter06.AffineCurrentPushforward`**

- definition `Chapter06.GeometricCurrentOn.affinePushforward`: 1 declaration
- theorem `Chapter06.GeometricCurrentOn.boundary_affinePushforward`: `ind_rescaled_current`
- definition `Chapter06.affinePullbackForm`: 1 declaration
- definition `Chapter06.affinePullbackTestOn`: 1 declaration
- theorem `Chapter06.affinePullbackTestOn_coe`: `ind_rescaled_current`

**`Poincare.SimonGMT.Chapter06.CurrentLocalEquality`**

- definition `Chapter06.GeometricCurrentOn.VanishesOn`: 22 declarations
- theorem `Chapter06.GeometricCurrentOn.isOpen_zeroRegion`: `iwl_cr_support_lemmas`, `fiw_tb_rectifiable_support_null`, `dph_lpf_cmp_core_estimate`, `dph_lpf_comparison`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_sh_affine_estimate`, `dph_iprod_exists`, `dph_lipschitz_pushforward_im`, `iwl_cr_cone_integer_multiplicity`, `deformation_pushforward_homotopy`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_pl_linear_pushforward_family`, `iwl_positive_density`, `isoperimetric_theorem`
- definition `Chapter06.GeometricCurrentOn.restrictDomain`: 11 declarations
- theorem `Chapter06.GeometricCurrentOn.restrictDomain_apply`: `br_restrictDomain_isIntegerMultiplicity`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`, `br_local_finite_mass_extension`
- definition `Chapter06.GeometricCurrentOn.support`: 73 declarations
- theorem `Chapter06.GeometricCurrentOn.support.eq_1`: `dmr_massMeasure_support_finite`, `deformation_dilation_support`
- theorem `Chapter06.GeometricCurrentOn.support_subset_domain`: `lpf_pi_local_finite_weight`, `lpf_pushforward_is_current`, `ind_pi_projected_limit`, `iwl_smooth_pushforward`
- definition `Chapter06.GeometricCurrentOn.zeroRegion`: 31 declarations
- definition `Chapter06.testFormOnInclusion`: 12 declarations
- theorem `Chapter06.testFormOnInclusion._proof_1`: `fiw_tb_ext_support_subset`, `iwl_cr_cest_cone_support`, `iwl_cr_support_lemmas`, `slicing_support_subset`, `dph_lpfex_support_subset_closure_image`, `dph_iprod_exists`, `deformation_onto_skeleton`, `iwl_localization`, `fiw_localization`, `deformation_dilation_support`, `deformation_theorem`
- theorem `Chapter06.testFormOnInclusion._proof_2`: `fiw_tb_ext_support_subset`, `iwl_cr_cest_cone_support`, `iwl_cr_support_lemmas`, `slicing_support_subset`, `dph_lpfex_support_subset_closure_image`, `dph_iprod_exists`, `deformation_onto_skeleton`, `iwl_localization`, `fiw_localization`, `deformation_dilation_support`, `deformation_theorem`
- theorem `Chapter06.testFormOnInclusion._proof_3`: `fiw_tb_ext_support_subset`, `iwl_cr_cest_cone_support`, `iwl_cr_support_lemmas`, `slicing_support_subset`, `dph_lpfex_support_subset_closure_image`, `dph_iprod_exists`, `deformation_onto_skeleton`, `iwl_localization`, `fiw_localization`, `deformation_dilation_support`, `deformation_theorem`
- theorem `Chapter06.testFormOnInclusion_coe`: `fiw_tb_ext_mass_le_restrictDomain`, `br_local_finite_mass_extension`, `ind_pi_localized_cycles`

**`Poincare.SimonGMT.Chapter06.Currents`**

- definition `Chapter06.CurrentOn`: 193 declarations
- structure `Chapter06.GeometricCurrentOn`: 207 declarations
- definition `Chapter06.GeometricCurrentOn.boundary`: 83 declarations
- theorem `Chapter06.GeometricCurrentOn.boundary_apply`: `polyhedral_approx_boundary_mass_cutoff`, `rpn_pullback_top_form_bound`, `iwl_cr_support_lemmas`, `iwl_cr_cone_boundary`, `fiw_tb_flat_sub`, `fiw_flat_to_weak`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_pointwise`, `constancy_closed_kills_partial_derivatives`, `polyhedral_approx_flat_seq_tendsto`, `slicing_support_subset`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `dph_iprod_boundary`, `dph_smooth_homotopy`, `rectifiability_orientation`, `deformation_pushforward_homotopy`, `deformation_skeleton_polyhedral`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `deformation_dilation_calculus`, `iwl_top_dim_integrality`, `boundary_rectifiability`, `fiw_tb_translation_estimate`
- theorem `Chapter06.GeometricCurrentOn.boundary_boundary`: `br_boundary_isIntegerMultiplicity_of_finite_mass`, `dph_lpf_boundary`, `deformation_pushforward_homotopy`, `deformation_onto_skeleton`, `iwl_positive_density`, `integrality_of_weak_limits`
- theorem `Chapter06.GeometricCurrentOn.continuous'`: `iwl_cr_cone_exists`, `fiw_tb_tda_sub_mass`, `fiw_tb_flat_sub`, `constancy_topForm_scalar_reduction`, `slicing_exists`, `deformation_telescope_limit`, `deformation_im_completeness`, `deformation_skeleton_polyhedral`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_localization`, `deformation_dilation_calculus`, `slicing_im_td_current_tendsto`, `deformation_theorem`
- theorem `Chapter06.GeometricCurrentOn.ext`: `isoperimetric_mass_eq_zero_iff`, `iwl_cr_cone_boundary`, `fiw_tb_extend_to_univ`, `iwl_restriction_theory`, `dph_lpf_existence`, `dph_iprod_exists`, `deformation_telescope_limit`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_ss_cycle_slice_boundary`, `ind_rescaled_current`, `ind_pi_localized_cycles`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_im_lincomb`, `fiw_localization`, `slicing_im_testform_determining`, `isoperimetric_theorem`, `integrality_of_weak_limits`, `fiw_tb_finite_net`
- constructor `Chapter06.GeometricCurrentOn.mk`: 29 declarations
- definition `Chapter06.GeometricCurrentOn.toCurrent`: 193 declarations
- theorem `Chapter06.GeometricCurrentOn.zero_apply`: `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_pushforward_homotopy`, `deformation_onto_skeleton`, `ind_pi_ss_cycle_slice_boundary`, `iwl_cycle_reduction`, `iwl_positive_density`
- theorem `Chapter06.TestFormConverges._proof_2`: `br_zd_finite_dirac_im`, `br_loc_tauAction_current`, `fiw_ims_sc_converges_zero_small`, `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_ce_cutoff_radial_operator`, `fiw_tb_tda_density_current`, `constancy_topForm_scalar_reduction`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `iwl_restriction_theory`, `smr_restriction_isCurrent`, `br_top_dim_lattice_approximation`, `dph_iprod_current_of_bound`, `lpf_pic_current_of_dominated_density`, `deformation_skeleton_polyhedral`, `ind_pi_constant_vector_current`, `iwl_localization`, `fiw_localization`, `deformation_dilation_calculus`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`, `slicing_im_tau_current`, `cmb_exists_weakly_convergent_subseq`
- theorem `Chapter06.TestFormConverges._proof_3`: `br_zd_finite_dirac_im`, `br_loc_tauAction_current`, `fiw_ims_sc_converges_zero_small`, `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_ce_cutoff_radial_operator`, `fiw_tb_tda_density_current`, `constancy_topForm_scalar_reduction`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `iwl_restriction_theory`, `smr_restriction_isCurrent`, `br_top_dim_lattice_approximation`, `dph_iprod_current_of_bound`, `lpf_pic_current_of_dominated_density`, `deformation_skeleton_polyhedral`, `ind_pi_constant_vector_current`, `iwl_localization`, `fiw_localization`, `deformation_dilation_calculus`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`, `slicing_im_tau_current`, `cmb_exists_weakly_convergent_subseq`
- definition `Chapter06.TestFormOn`: 233 declarations
- definition `Chapter06.TestFormOnConverges`: 36 declarations
- definition `Chapter06.WeaklyConvergesOn`: 38 declarations
- theorem `Chapter06.WeaklyConvergesOn.boundary`: `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_onto_skeleton`, `iwl_cycle_reduction`, `iwl_positive_density`, `integrality_of_weak_limits`
- definition `Chapter06.exteriorDerivativeTestOn`: 41 declarations
- theorem `Chapter06.exteriorDerivative_isTestForm`: `rectifiability_orientation`, `slicing_im_lipschitz_leibniz`
- definition `Chapter06.instZeroGeometricCurrentOn`: 22 declarations
- definition `Chapter06.testFormOnSubmodule`: 7 declarations
- theorem `Chapter06.testFormSubmodule._proof_4`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `fiw_fcl_telescope_limit`, `br_zd_im_dirac_repr`, `br_zd_dirac_massOn_ge`, `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`, `ltg_tau_local_to_global`, `br_loc_tauAction_current`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `br_zero_dim_weak_limit_isIntegerMultiplicity`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_abs_apply_le_opNorm_mul_massOn`, `br_la_apply_eq_zero_of_lt_degree`, `rpn_pullback_top_form_bound`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `fiw_ims_sc_converges_zero_small`, `fiw_ims_mass_bound`, `isoperimetric_mass_eq_zero_iff`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_local_null`, `isoperimetric_lattice_chain_mass_ge`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `iwl_imc_tau_measure_representation`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_cest_cone_support`, `iwl_cr_cest_mass_le_of_forms`, `iwl_cr_support_lemmas`, `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_ci_ps_slice_integral_eq_zero`, `iwl_cr_ci_product_support`, `lpf_rectifiable_support_null`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_density_current`, `fiw_tb_tda_locally_constant_im`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_apply_eq_zero_of_disjoint_support`, `fiw_tb_rectifiable_support_null`, `fiw_tb_extend_to_univ`, `fiw_tb_lattice_chain_coeff`, `fiw_tb_flat_sub`, `fiw_flat_to_weak`, `fiw_ims_series_current`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `constancy_closed_kills_partial_derivatives`, `constancy_topForm_scalar_reduction`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `polyhedral_approx_flat_seq_tendsto`, `polyhedral_approx_finite_mass_seq`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_isCurrent`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `lpf_pi_local_finite_weight`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dph_lpf_cmp_core_estimate`, `dph_lpf_comparison`, `dph_lpf_current_of_bounded_functional`, `dph_lpfex_support_subset_closure_image`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dmr_measureRepresentation_unique`, `deformation_mass_restriction`, `dph_iprod_slice_continuity`, `dph_iprod_horizontal_ftc`, `dph_sh_affine_estimate`, `dph_iprod_exists`, `dph_iprod_boundary`, `iwl_sp_sn_local_null`, `dph_interval_product`, `dph_smooth_homotopy`, `dph_interval_product_im`, `dph_lipschitz_pushforward`, `iwl_sp_rectifiable_support_null`, `dph_lipschitz_pushforward_im`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_telescope_limit`, `constancy_local_on_balls`, `constancy_of_local_constancy`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_pl_linear_pushforward_family`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_rescaled_current`, `ind_diagonal_weak_limit`, `ind_pi_ss_cycle_slice_family`, `ind_pi_good_slice_selection`, `ind_pi_localized_cycles`, `ind_pi_projected_limit`, `ind_top_dim_integer_density`, `ind_const_multiple_integer`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_sp_massOn_le_of_compatible`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_smooth_pushforward`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `rectifiability_theorem`, `fiw_im_series`, `fiw_im_lincomb`, `fiw_localization`, `fiw_flat_cauchy_limit`, `deformation_im_combination`, `deformation_dilation_calculus`, `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`, `deformation_dilation`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`, `slicing_im_testform_determining`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `deformation_theorem`, `isoperimetric_theorem`, `polyhedral_approximation`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `boundary_rectifiability`, `cmb_exists_weakly_convergent_subseq`, `fiw_tb_translation_estimate`, `fiw_tb_top_dim_approx`, `fiw_tb_finite_net`, `fiw_total_boundedness`, `flat_convergence_iff_weak_convergence`
- theorem `Chapter06.testFormSubmodule._proof_5`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `fiw_fcl_telescope_limit`, `br_zd_im_dirac_repr`, `br_zd_dirac_massOn_ge`, `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`, `ltg_tau_local_to_global`, `br_loc_tauAction_current`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `br_zero_dim_weak_limit_isIntegerMultiplicity`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_abs_apply_le_opNorm_mul_massOn`, `br_la_apply_eq_zero_of_lt_degree`, `rpn_pullback_top_form_bound`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `fiw_ims_sc_converges_zero_small`, `fiw_ims_mass_bound`, `isoperimetric_mass_eq_zero_iff`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_local_null`, `isoperimetric_lattice_chain_mass_ge`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `iwl_imc_tau_measure_representation`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_cest_cone_support`, `iwl_cr_cest_mass_le_of_forms`, `iwl_cr_support_lemmas`, `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_ci_ps_slice_integral_eq_zero`, `iwl_cr_ci_product_support`, `lpf_rectifiable_support_null`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_density_current`, `fiw_tb_tda_locally_constant_im`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_apply_eq_zero_of_disjoint_support`, `fiw_tb_rectifiable_support_null`, `fiw_tb_extend_to_univ`, `fiw_tb_lattice_chain_coeff`, `fiw_tb_flat_sub`, `fiw_flat_to_weak`, `fiw_ims_series_current`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `constancy_closed_kills_partial_derivatives`, `constancy_topForm_scalar_reduction`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `polyhedral_approx_flat_seq_tendsto`, `polyhedral_approx_finite_mass_seq`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_isCurrent`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `lpf_pi_local_finite_weight`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dph_lpf_cmp_core_estimate`, `dph_lpf_comparison`, `dph_lpf_current_of_bounded_functional`, `dph_lpfex_support_subset_closure_image`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dmr_measureRepresentation_unique`, `deformation_mass_restriction`, `dph_iprod_slice_continuity`, `dph_iprod_horizontal_ftc`, `dph_sh_affine_estimate`, `dph_iprod_exists`, `dph_iprod_boundary`, `iwl_sp_sn_local_null`, `dph_interval_product`, `dph_smooth_homotopy`, `dph_interval_product_im`, `dph_lipschitz_pushforward`, `iwl_sp_rectifiable_support_null`, `dph_lipschitz_pushforward_im`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_telescope_limit`, `constancy_local_on_balls`, `constancy_of_local_constancy`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_pl_linear_pushforward_family`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_rescaled_current`, `ind_diagonal_weak_limit`, `ind_pi_ss_cycle_slice_family`, `ind_pi_good_slice_selection`, `ind_pi_localized_cycles`, `ind_pi_projected_limit`, `ind_top_dim_integer_density`, `ind_const_multiple_integer`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_sp_massOn_le_of_compatible`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_smooth_pushforward`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `rectifiability_theorem`, `fiw_im_series`, `fiw_im_lincomb`, `fiw_localization`, `fiw_flat_cauchy_limit`, `deformation_im_combination`, `deformation_dilation_calculus`, `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`, `deformation_dilation`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`, `slicing_im_testform_determining`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `deformation_theorem`, `isoperimetric_theorem`, `polyhedral_approximation`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `boundary_rectifiability`, `cmb_exists_weakly_convergent_subseq`, `fiw_tb_translation_estimate`, `fiw_tb_top_dim_approx`, `fiw_tb_finite_net`, `fiw_total_boundedness`, `flat_convergence_iff_weak_convergence`
- theorem `Chapter06.testFormSubmodule._proof_6`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `fiw_fcl_telescope_limit`, `br_zd_im_dirac_repr`, `br_zd_dirac_massOn_ge`, `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`, `ltg_tau_local_to_global`, `br_loc_tauAction_current`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `br_zero_dim_weak_limit_isIntegerMultiplicity`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_abs_apply_le_opNorm_mul_massOn`, `br_la_apply_eq_zero_of_lt_degree`, `rpn_pullback_top_form_bound`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `fiw_ims_sc_converges_zero_small`, `fiw_ims_mass_bound`, `isoperimetric_mass_eq_zero_iff`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_local_null`, `isoperimetric_lattice_chain_mass_ge`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `iwl_imc_tau_measure_representation`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_cest_cone_support`, `iwl_cr_cest_mass_le_of_forms`, `iwl_cr_support_lemmas`, `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_ci_ps_slice_integral_eq_zero`, `iwl_cr_ci_product_support`, `lpf_rectifiable_support_null`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_density_current`, `fiw_tb_tda_locally_constant_im`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_apply_eq_zero_of_disjoint_support`, `fiw_tb_rectifiable_support_null`, `fiw_tb_extend_to_univ`, `fiw_tb_lattice_chain_coeff`, `fiw_tb_flat_sub`, `fiw_flat_to_weak`, `fiw_ims_series_current`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `constancy_closed_kills_partial_derivatives`, `constancy_topForm_scalar_reduction`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `polyhedral_approx_flat_seq_tendsto`, `polyhedral_approx_finite_mass_seq`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_isCurrent`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `lpf_pi_local_finite_weight`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dph_lpf_cmp_core_estimate`, `dph_lpf_comparison`, `dph_lpf_current_of_bounded_functional`, `dph_lpfex_support_subset_closure_image`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dmr_measureRepresentation_unique`, `deformation_mass_restriction`, `dph_iprod_slice_continuity`, `dph_iprod_horizontal_ftc`, `dph_sh_affine_estimate`, `dph_iprod_exists`, `dph_iprod_boundary`, `iwl_sp_sn_local_null`, `dph_interval_product`, `dph_smooth_homotopy`, `dph_interval_product_im`, `dph_lipschitz_pushforward`, `iwl_sp_rectifiable_support_null`, `dph_lipschitz_pushforward_im`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_telescope_limit`, `constancy_local_on_balls`, `constancy_of_local_constancy`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_pl_linear_pushforward_family`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_rescaled_current`, `ind_diagonal_weak_limit`, `ind_pi_ss_cycle_slice_family`, `ind_pi_good_slice_selection`, `ind_pi_localized_cycles`, `ind_pi_projected_limit`, `ind_top_dim_integer_density`, `ind_const_multiple_integer`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_sp_massOn_le_of_compatible`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_smooth_pushforward`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `rectifiability_theorem`, `fiw_im_series`, `fiw_im_lincomb`, `fiw_localization`, `fiw_flat_cauchy_limit`, `deformation_im_combination`, `deformation_dilation_calculus`, `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`, `deformation_dilation`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`, `slicing_im_testform_determining`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `deformation_theorem`, `isoperimetric_theorem`, `polyhedral_approximation`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `boundary_rectifiability`, `cmb_exists_weakly_convergent_subseq`, `fiw_tb_translation_estimate`, `fiw_tb_top_dim_approx`, `fiw_tb_finite_net`, `fiw_total_boundedness`, `flat_convergence_iff_weak_convergence`
- theorem `Chapter06.tsupport_exteriorDerivative_subset`: `iwl_cr_support_lemmas`, `fiw_tb_extend_to_univ`, `fiw_flat_to_weak`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `slicing_support_subset`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `rectifiability_orientation`, `deformation_skeleton_polyhedral`, `iwl_localization`, `slicing_im_slice_identity`, `boundary_rectifiability`

**`Poincare.SimonGMT.Chapter06.Forms`**

- definition `Chapter06.Covector`: 345 declarations
- definition `Chapter06.DifferentialForm`: 249 declarations
- definition `Chapter06.IsSmoothForm`: 112 declarations
- theorem `Chapter06.IsSmoothForm._proof_1`: `polyhedral_approx_boundary_mass_cutoff`, `fiw_tb_ext_smul_testForm`, `br_zd_dirac_massOn_ge`, `br_zd_dirac_local_limit`, `ltg_tau_unique_on_open`, `ltg_tau_local_to_global`, `br_loc_tauAction_current`, `isoperimetric_mass_lt_top`, `br_la_testForm_covectorNorm_bounded`, `rpn_moc_exists_testForm_smul`, `cmb_exists_countable_dense_testForms`, `cmb_exists_testForm_uniform_approx`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `fiw_ims_sc_testForm_bounded`, `lpf_pi_image_density`, `lpf_rsn_local_null`, `isoperimetric_lattice_face_isolating_form`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `polyhedral_approx_rt_integrableOn_apply`, `slicing_ru_integrableOn_apply`, `iwl_imc_tau_measure_representation`, `iwl_rl_testForm_smooth_cutoff`, `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_cest_cutoff_radial_form`, `iwl_cr_cone_boundary`, `iwl_cr_ci_cutoff_pullback_testForm`, `fiw_tb_tda_density_current`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_lcc_local_isolating_form`, `fiw_flat_to_weak`, `slicing_mb_lb_smul_testForm`, `slicing_mb_lb_wedge_testForm`, `slicing_mb_leibniz_bound`, `constancy_closed_kills_partial_derivatives`, `slicing_representation_unique`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_testForm_covectorNorm_bounded`, `slicing_im_si_borel_density`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_testForm_uniform_approx`, `slicing_mass_representation`, `slicing_im_ll_tangent_dual_field`, `iwl_cr_interval_product_im`, `iwl_sp_exists_compatible_testForm`, `br_cube_stokes_lattice`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_local_finite_mass_extension`, `dph_iprod_horizontal_slices`, `dph_lpf_boundary`, `dmr_measureRepresentation_unique`, `dph_iprod_slice_continuity`, `dph_iprod_slice_extDeriv`, `dph_iprod_horizontal_ftc`, `dph_iprod_boundary`, `iwl_sp_sn_local_null`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `rectifiability_orientation`, `constancy_testFormOn_eq_finset_sum_subordinate`, `constancy_of_local_constancy`, `deformation_im_pushforward_limit`, `lpf_pic_current_of_dominated_density`, `deformation_im_completeness`, `deformation_skeleton_polyhedral`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_diagonal_weak_limit`, `ind_top_form_density_ae_unique`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_localization`, `iwl_positive_density`, `fiw_ims_tsum_tau`, `fiw_localization`, `deformation_dilation_calculus`, `slicing_im_td_current_tendsto`, `slicing_im_tau_current`, `iwl_top_dim_integrality`, `iwl_integer_density`, `cmb_exists_weakly_convergent_subseq`
- definition `Chapter06.IsTestForm`: 126 declarations
- definition `Chapter06.exteriorDerivative`: 26 declarations
- theorem `Chapter06.exteriorDerivative_apply`: `fiw_tb_te_directional_form`, `constancy_closed_kills_partial_derivatives`, `br_cube_stokes_lattice`, `br_top_dim_lattice_approximation`, `dph_iprod_slice_extDeriv`, `iwl_top_dim_integrality`

**`Poincare.SimonGMT.Chapter06.FormsDuality`**

- definition `Chapter06.NVector`: 180 declarations
- theorem `Chapter06.NVector._proof_1`: `br_zd_im_dirac_repr`, `br_zd_finite_dirac_im`, `ltg_tau_integrable`, `ltg_covector_separating`, `ltg_simple_unit_rigidity`, `ltg_tau_unique_on_open`, `ltg_glue_triples`, `ltg_tau_congr_on_open`, `ltg_tau_local_to_global`, `fiw_ims_tt_unit_bound`, `br_loc_tauAction_current`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_nvector_apply_le`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `slicing_im_st_mf_slice_orientation_aesm`, `slicing_im_st_measure_fields`, `iwl_cr_ip_pt_slab_transfer`, `iwl_cr_ip_slice_formula`, `lpf_pi_simple_unit_facts`, `lpf_pi_induced_orientation`, `lpf_pi_jacobian_local_bound`, `lpf_pi_measurability`, `lpf_pi_source_charts`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_covector_separating_family`, `lpf_rsn_local_null`, `lpf_simple_nvector_algebra`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`, `imc_mlb_exists_form_lintegral_coordNorm_le`, `slicing_ru_integrableOn_apply`, `br_loc_triple_inter_open`, `iwl_imc_tau_measure_representation`, `lpf_rectifiable_support_null`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_locally_constant_im`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `slicing_representation_unique`, `polyhedral_approx_pairing_expansion`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `slicing_im_si_borel_density`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `lpf_raf_jacobian_identity`, `lpf_raf_chart_jacobian_ae`, `smr_ufd_unit_coord_field`, `smr_ofReal_integral_le_massOn`, `smr_riesz_continuous_forms`, `smr_restriction_isCurrent`, `smr_exists_unit_form_gt`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `slicing_im_ll_tangent_dual_field`, `lpf_raf_pushforward_enorm_aemeasurable`, `imc_lintegral_coordNorm_le_mass`, `iwl_cr_ip_product_triple`, `iwl_cr_ci_ie_nvector_intervalIntegral`, `iwl_cr_ci_ie_param_fubini`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dmr_measureRepresentation_unique`, `dmr_rectifiableTriple_inter`, `deformation_mass_restriction`, `iwl_sp_sn_covector_separating_family`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_sp_sn_local_null`, `fiw_ims_frame_sign`, `imc_isRectifiableTriple_of_eventually_mem`, `dph_lipschitz_pushforward_im`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `fiw_ims_orientation_sign`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_cc_chart_integral_representation`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_chart_convergence`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pic_density_aestronglyMeasurable`, `lpf_pic_density_dominated`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `slicing_im_st_slice_geometry`, `imc_im_density_limit`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `rectifiability_projection_null`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_tauAction_dilation`, `ind_ab_weighted_lebesgue_point`, `ind_ab_orientation_error_vanishes`, `ind_ae_blowup_limit`, `ind_rs_rectifiableTriple_dilation`, `ind_pi_localized_cycles`, `ind_top_orthonormal_frame_sign`, `ind_top_dim_integer_density`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_localization`, `iwl_positive_density`, `rectifiability_theorem`, `slicing_im_st_interior_product`, `slicing_im_slice_triple`, `fiw_ims_tt_term_bound`, `fiw_ims_tsum_tau`, `fiw_ims_combine`, `fiw_localization`, `deformation_dilation_im_rectifiableTriple`, `deformation_dilation_im_tauAction`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `compactness_under_mass_bounds`, `fiw_tb_finite_net`, `federer_fleming_compactness`
- theorem `Chapter06.NVector._proof_2`: `br_zd_im_dirac_repr`, `br_zd_finite_dirac_im`, `ltg_tau_integrable`, `ltg_covector_separating`, `ltg_simple_unit_rigidity`, `ltg_tau_unique_on_open`, `ltg_glue_triples`, `ltg_tau_congr_on_open`, `ltg_tau_local_to_global`, `fiw_ims_tt_unit_bound`, `br_loc_tauAction_current`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_nvector_apply_le`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `slicing_im_st_mf_slice_orientation_aesm`, `slicing_im_st_measure_fields`, `iwl_cr_ip_pt_slab_transfer`, `iwl_cr_ip_slice_formula`, `lpf_pi_simple_unit_facts`, `lpf_pi_induced_orientation`, `lpf_pi_jacobian_local_bound`, `lpf_pi_measurability`, `lpf_pi_source_charts`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_covector_separating_family`, `lpf_rsn_local_null`, `lpf_simple_nvector_algebra`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`, `imc_mlb_exists_form_lintegral_coordNorm_le`, `slicing_ru_integrableOn_apply`, `br_loc_triple_inter_open`, `iwl_imc_tau_measure_representation`, `lpf_rectifiable_support_null`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_locally_constant_im`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `slicing_representation_unique`, `polyhedral_approx_pairing_expansion`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `slicing_im_si_borel_density`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `lpf_raf_jacobian_identity`, `lpf_raf_chart_jacobian_ae`, `smr_ufd_unit_coord_field`, `smr_ofReal_integral_le_massOn`, `smr_riesz_continuous_forms`, `smr_restriction_isCurrent`, `smr_exists_unit_form_gt`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `slicing_im_ll_tangent_dual_field`, `lpf_raf_pushforward_enorm_aemeasurable`, `imc_lintegral_coordNorm_le_mass`, `iwl_cr_ip_product_triple`, `iwl_cr_ci_ie_nvector_intervalIntegral`, `iwl_cr_ci_ie_param_fubini`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dmr_measureRepresentation_unique`, `dmr_rectifiableTriple_inter`, `deformation_mass_restriction`, `iwl_sp_sn_covector_separating_family`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_sp_sn_local_null`, `fiw_ims_frame_sign`, `imc_isRectifiableTriple_of_eventually_mem`, `dph_lipschitz_pushforward_im`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `fiw_ims_orientation_sign`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_cc_chart_integral_representation`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_chart_convergence`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pic_density_aestronglyMeasurable`, `lpf_pic_density_dominated`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `slicing_im_st_slice_geometry`, `imc_im_density_limit`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `rectifiability_projection_null`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_tauAction_dilation`, `ind_ab_weighted_lebesgue_point`, `ind_ab_orientation_error_vanishes`, `ind_ae_blowup_limit`, `ind_rs_rectifiableTriple_dilation`, `ind_pi_localized_cycles`, `ind_top_orthonormal_frame_sign`, `ind_top_dim_integer_density`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_localization`, `iwl_positive_density`, `rectifiability_theorem`, `slicing_im_st_interior_product`, `slicing_im_slice_triple`, `fiw_ims_tt_term_bound`, `fiw_ims_tsum_tau`, `fiw_ims_combine`, `fiw_localization`, `deformation_dilation_im_rectifiableTriple`, `deformation_dilation_im_tauAction`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `compactness_under_mass_bounds`, `fiw_tb_finite_net`, `federer_fleming_compactness`
- theorem `Chapter06.NVector._proof_3`: `br_zd_im_dirac_repr`, `br_zd_finite_dirac_im`, `ltg_tau_integrable`, `ltg_covector_separating`, `ltg_simple_unit_rigidity`, `ltg_tau_unique_on_open`, `ltg_glue_triples`, `ltg_tau_congr_on_open`, `ltg_tau_local_to_global`, `fiw_ims_tt_unit_bound`, `br_loc_tauAction_current`, `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `isoperimetric_mass_lt_top`, `rpn_moc_abs_nvector_apply_le`, `rpn_moc_abs_apply_le_mul_measure_diff`, `rpn_moc_abs_apply_top_form_le`, `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`, `rpn_massOn_le_mul_measure_diff`, `cmb_rb_measureRepresentation_integrableOn_coeff`, `slicing_im_st_mf_slice_orientation_aesm`, `slicing_im_st_measure_fields`, `iwl_cr_ip_pt_slab_transfer`, `iwl_cr_ip_slice_formula`, `lpf_pi_simple_unit_facts`, `lpf_pi_induced_orientation`, `lpf_pi_jacobian_local_bound`, `lpf_pi_measurability`, `lpf_pi_source_charts`, `lpf_pi_image_density`, `lpf_pi_im_of_chart_density`, `lpf_rsn_covector_separating_family`, `lpf_rsn_local_null`, `lpf_simple_nvector_algebra`, `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`, `imc_mlb_exists_form_lintegral_coordNorm_le`, `slicing_ru_integrableOn_apply`, `br_loc_triple_inter_open`, `iwl_imc_tau_measure_representation`, `lpf_rectifiable_support_null`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_density`, `fiw_tb_tda_locally_constant_im`, `slicing_mb_lb_repr_bound`, `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `slicing_representation_unique`, `polyhedral_approx_pairing_expansion`, `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_truncation_seq`, `slicing_im_si_borel_density`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `lpf_raf_jacobian_identity`, `lpf_raf_chart_jacobian_ae`, `smr_ufd_unit_coord_field`, `smr_ofReal_integral_le_massOn`, `smr_riesz_continuous_forms`, `smr_restriction_isCurrent`, `smr_exists_unit_form_gt`, `smr_restriction_massOn_eq`, `slicing_mass_representation`, `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `slicing_im_ll_tangent_dual_field`, `lpf_raf_pushforward_enorm_aemeasurable`, `imc_lintegral_coordNorm_le_mass`, `iwl_cr_ip_product_triple`, `iwl_cr_ci_ie_nvector_intervalIntegral`, `iwl_cr_ci_ie_param_fubini`, `iwl_cr_ci_integral_exchange`, `iwl_cr_interval_product_im`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `dmr_measureRepresentation_unique`, `dmr_rectifiableTriple_inter`, `deformation_mass_restriction`, `iwl_sp_sn_covector_separating_family`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_sp_sn_local_null`, `fiw_ims_frame_sign`, `imc_isRectifiableTriple_of_eventually_mem`, `dph_lipschitz_pushforward_im`, `iwl_im_patching`, `iwl_zero_dim_integrality`, `fiw_ims_orientation_sign`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `rectifiability_orientation`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_cc_chart_integral_representation`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_chart_convergence`, `deformation_im_pushforward_limit`, `deformation_pushforward_homotopy`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`, `lpf_pic_current_of_dominated_density`, `lpf_pic_density_aestronglyMeasurable`, `lpf_pic_density_dominated`, `lpf_pushforward_is_current`, `lipschitz_pushforward_integer_multiplicity`, `slicing_im_st_slice_geometry`, `imc_im_density_limit`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `rectifiability_projection_null`, `iwl_im_closure`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `iwl_sp_lipschitzPushforward_apply_eq`, `ind_pi_constant_vector_current`, `ind_pi_restriction_open_im`, `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_tauAction_dilation`, `ind_ab_weighted_lebesgue_point`, `ind_ab_orientation_error_vanishes`, `ind_ae_blowup_limit`, `ind_rs_rectifiableTriple_dilation`, `ind_pi_localized_cycles`, `ind_top_orthonormal_frame_sign`, `ind_top_dim_integer_density`, `ind_plane_multiplicity_integer`, `ind_ae_integer_multiplicity`, `iwl_localization`, `iwl_positive_density`, `rectifiability_theorem`, `slicing_im_st_interior_product`, `slicing_im_slice_triple`, `fiw_ims_tt_term_bound`, `fiw_ims_tsum_tau`, `fiw_ims_combine`, `fiw_localization`, `deformation_dilation_im_rectifiableTriple`, `deformation_dilation_im_tauAction`, `slicing_im_lipschitz_leibniz`, `slicing_im_slice_identity`, `slicing_im_tau_current`, `slicing_integer_multiplicity_ae`, `iwl_top_dim_integrality`, `iwl_integer_density`, `integrality_of_weak_limits`, `compactness_under_mass_bounds`, `fiw_tb_finite_net`, `federer_fleming_compactness`
- definition `Chapter06.SimonMultiIndex`: 67 declarations
- definition `Chapter06.covectorPullback`: 10 declarations
- theorem `Chapter06.covectorPullback_apply`: `deformation_ipl_cc_chart_integral_representation`
- theorem `Chapter06.covectorPullback_wedgeCovectors`: `rpn_covector_rotated_expansion`, `rectifiability_orientation`
- definition `Chapter06.euclideanCovectorCoordinate`: 32 declarations
- definition `Chapter06.euclideanNVectorCoordinate`: 14 declarations
- definition `Chapter06.nVectorPushforward`: 23 declarations
- theorem `Chapter06.nVectorPushforward._proof_1`: `lpf_raf_pushforward_enorm_aemeasurable`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `iwl_sp_lipschitzPushforward_apply_eq`
- theorem `Chapter06.nVectorPushforward_simple`: `lpf_pi_induced_orientation`, `lpf_pi_jacobian_local_bound`, `lpf_raf_jacobian_identity`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`
- definition `Chapter06.simpleNVector`: 79 declarations
- theorem `Chapter06.simpleNVector._proof_1`: `lpf_pi_jacobian_local_bound`, `polyhedral_approx_rt_tau_integrableOn`, `lpf_pic_density_dominated`
- theorem `Chapter06.simpleNVector._proof_2`: `lpf_pi_jacobian_local_bound`, `polyhedral_approx_rt_tau_integrableOn`, `lpf_pic_density_dominated`
- theorem `Chapter06.simpleNVector._proof_3`: `lpf_pi_jacobian_local_bound`, `polyhedral_approx_rt_tau_integrableOn`, `lpf_pic_density_dominated`
- theorem `Chapter06.simpleNVector_apply`: `fiw_ims_tt_unit_bound`, `lpf_simple_nvector_algebra`, `polyhedral_approx_open_truncation`, `fiw_ims_frame_sign`, `rectifiability_orientation`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_cc_pushforward_integrand_bound`, `imc_im_density_limit`, `deformation_skeleton_polyhedral`, `ind_ab_weighted_lebesgue_point`, `ind_ae_blowup_limit`, `ind_top_orthonormal_frame_sign`, `ind_top_dim_integer_density`, `iwl_localization`, `fiw_localization`
- definition `Chapter06.wedgeCovectors`: 51 declarations
- theorem `Chapter06.wedgeCovectors._proof_1`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_10`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_2`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_3`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_4`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_5`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_6`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors._proof_9`: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors.eq_2`: `rpn_pfd_extDeriv_sum_smul_wedge`
- theorem `Chapter06.wedgeCovectors_apply_det`: `ltg_simple_unit_rigidity`, `cmb_covector_eq_sum_coord_smul_wedge`, `rpn_pfd_wedge_cons_succAbove_sign`, `polyhedral_approx_pairing_wedge_kronecker`, `isoperimetric_coord_covector_eval`, `lpf_simple_nvector_algebra`, `smr_ci_coord_sum_smul_wedge`, `slicing_ru_covector_expansion`, `fiw_tb_tda_density`, `fiw_tb_te_directional_form`, `constancy_closed_kills_partial_derivatives`, `constancy_topForm_scalar_reduction`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `br_top_dim_lattice_approximation`, `fiw_im_mass_formula`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `rectifiability_orientation`, `deformation_ipl_cc_chart_orientation_sign`, `constancy_exists_topTestForm_integral_eq_one`, `deformation_ipl_minor_weak_continuity`, `imc_im_density_limit`, `deformation_skeleton_polyhedral`, `ind_top_form_density_ae_unique`, `ind_top_dim_integer_density`, `iwl_localization`, `fiw_localization`, `iwl_top_dim_integrality`

**`Poincare.SimonGMT.Chapter06.Mass`**

- theorem `Chapter06.GeometricCurrentOn.le_massOn`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `br_zd_dirac_massOn_ge`, `fiw_ims_mass_bound`, `isoperimetric_lattice_chain_mass_ge`, `iwl_rl_massOn_iUnion_monotone`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_flat_sub`, `polyhedral_approx_truncation_seq`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `br_top_dim_lattice_approximation`, `fiw_im_mass_formula`, `br_local_finite_mass_extension`, `iwl_zero_dim_integrality`, `deformation_telescope_limit`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_diagonal_weak_limit`, `ind_pi_localized_cycles`, `iwl_sp_massOn_le_of_compatible`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_localization`, `deformation_dilation_mass`, `deformation_theorem`, `iwl_top_dim_integrality`
- definition `Chapter06.GeometricCurrentOn.mass`: 73 declarations
- definition `Chapter06.GeometricCurrentOn.massOn`: 87 declarations
- theorem `Chapter06.GeometricCurrentOn.massOn_mono`: `iwl_rl_massOn_iUnion_monotone`, `iwl_restriction_theory`, `imc_lintegral_coordNorm_le_mass`, `br_boundary_isIntegerMultiplicity_of_finite_mass`, `dmr_massMeasure_support_finite`, `deformation_mass_restriction`, `deformation_telescope_limit`, `deformation_onto_skeleton`, `iwl_rl_restriction_cutoff_estimate`, `iwl_restriction_weak_limit`, `ind_pi_pl_linear_pushforward_family`, `ind_md_mmb_massMeasure_balls`, `ind_md_mass_measure_balls`, `ind_pi_localized_cycles`, `iwl_positive_density`, `fiw_localization`, `fiw_flat_cauchy_limit`, `iwl_integer_density`, `integrality_of_weak_limits`, `flat_convergence_iff_weak_convergence`
- theorem `Chapter06.WeaklyConvergesOn.massOn_le_liminf`: `cmb_tendsto_integral_of_weaklyConvergesOn`, `iwl_restriction_weak_limit`, `iwl_localization`, `iwl_positive_density`, `fiw_localization`, `integrality_of_weak_limits`
- definition `Chapter06.covectorEuclideanNorm`: 118 declarations
- theorem `Chapter06.covectorEuclideanNorm.eq_1`: `br_zd_dirac_massOn_ge`, `cmb_rb_abs_euclideanCovectorCoordinate_le`, `fiw_ims_sc_covectorNorm_le_opNorm`, `cmb_rb_covectorEuclideanNorm_add_le`, `isoperimetric_coord_covector_eval`, `slicing_mb_wn_norm_sq_eq_onb_sum`, `rectifiability_mass_measure_representation`, `dph_iprod_slice_covector_norm_le`, `iwl_zero_dim_integrality`
- theorem `Chapter06.covectorEuclideanNorm_neg`: `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `isoperimetric_lattice_chain_mass_ge`, `cmb_measureRepresentation_continuous_bound`, `fiw_tb_flat_sub`, `smr_ofReal_integral_le_massOn`, `deformation_im_completeness`, `deformation_onto_skeleton`, `iwl_cycle_reduction`, `fiw_localization`
- theorem `Chapter06.covectorEuclideanNorm_nonneg`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `isoperimetric_abs_covector_apply_le`, `iwl_rl_testForm_smooth_cutoff`, `iwl_cr_cest_radial_coeff_bound`, `iwl_cr_cest_cutoff_radial_form`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_flat_to_weak`, `slicing_mb_wedge_norm_le`, `polyhedral_approx_open_truncation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `iwl_sp_covectorEuclideanNorm_pullback_le`, `dph_lpfex_bounded_compatible_form`, `dph_lpf_existence`, `dph_sh_ib_covectorEuclideanNorm_contract_le`, `dph_sh_affine_estimate`, `rectifiability_orientation`, `deformation_skeleton_polyhedral`, `iwl_rl_restriction_cutoff_estimate`, `ind_pi_ss_restriction_massOn_le`, `ind_diagonal_weak_limit`, `iwl_sp_massOn_le_of_compatible`, `iwl_positive_density`, `iwl_top_dim_integrality`
- theorem `Chapter06.covectorEuclideanNorm_zero`: `br_la_testForm_covectorNorm_bounded`, `slicing_mb_cdb_grad_lintegral_le`, `fiw_flat_to_weak`, `polyhedral_approx_testForm_covectorNorm_bounded`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `dph_lpfex_bounded_compatible_form`, `dph_lpf_existence`, `dph_iprod_current_of_bound`, `dph_sh_affine_estimate`, `imc_im_density_limit`, `deformation_im_completeness`, `cmb_exists_weakly_convergent_subseq`
- definition `Chapter06.massAdmissibleOn`: 60 declarations
- theorem `Chapter06.massAdmissibleOn._proof_1`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `isoperimetric_mass_lt_top`, `rpn_massOn_le_mul_measure_diff`, `fiw_ims_mass_bound`, `isoperimetric_lattice_face_isolating_form`, `isoperimetric_lattice_chain_mass_ge`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_cone_estimates`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_tda_sub_mass`, `fiw_tb_rectifiable_support_null`, `fiw_tb_flat_sub`, `fiw_ims_series_current`, `slicing_mb_pointwise`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_massOn_eq`, `br_top_dim_lattice_approximation`, `fiw_im_mass_formula`, `dph_lpf_current_of_bounded_functional`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dph_iprod_boundary`, `deformation_pushforward_homotopy`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_diagonal_weak_limit`, `iwl_sp_massOn_le_of_compatible`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_localization`, `deformation_dilation_mass`, `iwl_top_dim_integrality`
- theorem `Chapter06.massAdmissibleOn._proof_2`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `isoperimetric_mass_lt_top`, `rpn_massOn_le_mul_measure_diff`, `fiw_ims_mass_bound`, `isoperimetric_lattice_face_isolating_form`, `isoperimetric_lattice_chain_mass_ge`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_cone_estimates`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_tda_sub_mass`, `fiw_tb_rectifiable_support_null`, `fiw_tb_flat_sub`, `fiw_ims_series_current`, `slicing_mb_pointwise`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_massOn_eq`, `br_top_dim_lattice_approximation`, `fiw_im_mass_formula`, `dph_lpf_current_of_bounded_functional`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dph_iprod_boundary`, `deformation_pushforward_homotopy`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_diagonal_weak_limit`, `iwl_sp_massOn_le_of_compatible`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_localization`, `deformation_dilation_mass`, `iwl_top_dim_integrality`
- theorem `Chapter06.massAdmissibleOn._proof_3`: `polyhedral_approx_boundary_mass_cutoff`, `cmb_abs_apply_le_of_massOn_le`, `br_la_abs_apply_le_mul_mass`, `fiw_tb_te_abs_apply_le_mul_mass`, `isoperimetric_mass_lt_top`, `rpn_massOn_le_mul_measure_diff`, `fiw_ims_mass_bound`, `isoperimetric_lattice_face_isolating_form`, `isoperimetric_lattice_chain_mass_ge`, `iwl_rl_massOn_iUnion_monotone`, `iwl_cr_cone_estimates`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_tda_sub_mass`, `fiw_tb_rectifiable_support_null`, `fiw_tb_flat_sub`, `fiw_ims_series_current`, `slicing_mb_pointwise`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_restriction_massOn_eq`, `br_top_dim_lattice_approximation`, `fiw_im_mass_formula`, `dph_lpf_current_of_bounded_functional`, `dph_iprod_current_of_bound`, `dmr_massMeasure_support_finite`, `dph_iprod_boundary`, `deformation_pushforward_homotopy`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `ind_diagonal_weak_limit`, `iwl_sp_massOn_le_of_compatible`, `iwl_localization`, `iwl_cycle_reduction`, `iwl_positive_density`, `fiw_localization`, `deformation_dilation_mass`, `iwl_top_dim_integrality`
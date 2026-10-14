<!-- theorem-id: gmt-ch06/root -->

# Final proof of `GMT.Ch06.main_theorem` (Simon, *Introduction to GMT*, Chapter 6 "Currents")

| | |
| --- | --- |
| Node | `root` of run `20261011T144224Z-6e4735dbca`; issue <https://github.com/ZhengyangZhang06/gmt-formalize/issues/6> |
| Declaration | `GMT.Ch06.main_theorem` in `GMT/Ch06/Submission.lean` (line 69498) |
| Frozen problem | `GMT/Ch06/Contract.lean` at `d8d46c9587747dee0751a1f780fcafdba16a3886` (unchanged; byte-identical in the candidate) |
| Lean source of this candidate | commit `e9e57ea4` ("Remove the module docstring duplicated by the overlay merge"), `GMT/Ch06/Submission.lean` sha256 `8844dc262ee305c7d301443a16525f97108a466caebf817f3e7d820abf0846f0`. The commits that add and revise this file change no `.lean` file. |
| Toolchain and libraries | Lean `v4.35.0-rc3`; Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`; `simongmt` (`Poincare.SimonGMT.*`) `2b3663083f3fe399b6296fb8eaee52169170e197`; all pinned by the frozen `lakefile.toml`/`lake-manifest.json` |
| Axioms of `main_theorem` | `propext`, `Classical.choice`, `Quot.sound` only (§9) |
| Mathematical source | L. Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua notes), Ch. 6, printed pp. 131–180, with the cross-references to Chs. 1–3 that the printed proofs use |

## 0. Summary

`main_theorem` has no hypotheses. Its type is the conjunction of the twelve frozen headline
propositions of Chapter 6. The Lean proof is a single anonymous-constructor term whose twelve
components are the twelve accepted root children (§2), one per conjunct.

The root children are proved in `GMT/Ch06/Submission.lean` from 679 accepted descendant
declarations, from Mathlib and from the pinned `simongmt` library. Altogether the run's DAG has
**691 accepted declarations** besides the root. Each of them occurs exactly once in
`Submission.lean`, under its exact globally qualified name `GMT.Ch06.Submission.<lean_name>` and
with its frozen type (checked by elaboration, §9), and its full text equals the text in its
accepted candidate commit (§9). **688** of the 691 are used, directly or transitively, by the proof
of `main_theorem`. The other **3** are accepted but unused; they are kept, unchanged, to preserve
their accepted interfaces, and §6 explains why the formal proof does not need them.

Section 3 is the mathematical core: for each conjunct it gives the proof that the Lean code
actually carries out, step by step, naming the accepted lemmas that carry each step at the point
where they are used and stating their roles; the lemmas below them are in Appendix A. Appendix A catalogues all 691 accepted declarations with their statements and
proofs (the Lean doc comments), the accepted declarations each one calls and the ones that call it.
In 120 entries the reproduced text contained an error. Counting each entry once, under its most
serious error, 14 contain a false or ill-formed mathematical claim, 53 omit a hypothesis of the
Lean statement on which the claim depends, and 53 have a wrong locator, quotation or provenance
label. None of these errors is in a Lean statement or proof. They are corrected in Appendix A and
listed in §8.
Appendix B lists the SimonGMT constants that the proofs use directly, with the declarations that use
each SimonGMT theorem, as read from the compiled environment.

The chapter's results are not proved in the printed order. The book states 3.11 (Federer–Fleming)
in §3 and proves it only in Remark 8.3(2), and the proofs of 6.2, 6.3 and 7.2 use 5.3 and 4.4–4.10.
The formal proof uses the order of §4, in which every theorem is proved before it is used; Lean
checks declarations top to bottom, so this order is enforced by the kernel.

The Lean source of this candidate is that of the previously compared overlay `dfdc020b` minus a
second copy of the contract's module docstring that the overlay merge had introduced (§8). That
deletion changes no declaration.

## 1. Statement, assumptions and conventions

### 1.1 The statement

```lean
theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧
    LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧
    DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧
    BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧
    IntegralityOfWeakLimits
```

| # | Proposition (frozen `def … : Prop` of the contract) | Simon, Ch. 6 |
| --- | --- | --- |
| 1 | `CompactnessUnderMassBounds` | Lemma 2.15, p. 137 |
| 2 | `ConstancyTheorem` | Theorem 2.34, p. 142 |
| 3 | `LipschitzPushforwardIntegerMultiplicity` | Lemma 3.9, p. 148 |
| 4 | `FedererFlemingCompactness` | Theorem 3.11, p. 149 |
| 5 | `SlicingTheorem` | §4, 4.4–4.10, pp. 153–158 |
| 6 | `DeformationTheorem` | 5.3 (scaled), p. 160; 5.1 is `ρ = 1` |
| 7 | `IsoperimetricTheorem` | 6.1, p. 168 |
| 8 | `PolyhedralApproximation` | 6.2, p. 169 |
| 9 | `BoundaryRectifiability` | 6.3, p. 170 |
| 10 | `FlatConvergenceIffWeakConvergence` | Theorem 7.2, p. 170 |
| 11 | `RectifiabilityTheorem` | 8.1, p. 173 |
| 12 | `IntegralityOfWeakLimits` | Theorem 8.2, p. 176 |

### 1.2 Assumptions

The theorem is a closed proposition and has no hypotheses. Each conjunct quantifies over all
dimensions `P, m, ℓ, n, Q`, open sets, currents, maps, sequences and scales with exactly the
hypotheses written in its definition in `GMT/Ch06/Contract.lean`. The proof adds, removes or weakens
no hypothesis. It declares no axiom and contains no `sorry`, `admit`, `opaque`, `native_decide`,
`implemented_by` or `extern` (a search of the source finds only the English words
"admits"/"admitting" in three doc comments, and "(opaque)" in one `--` comment, line 12181).

### 1.3 Conventions and the frozen definitions

Notation is that of the contract and of `GMT/Ch06/README.md`:

- `ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P)`; `Hⁿ = μHE[n]`, Mathlib's normalized Hausdorff measure,
  which is Lebesgue measure `Lⁿ` on `ℝⁿ`.
- `𝒟ⁿ(U) = TestFormOn U n` (smooth `n`-forms on `ℝ^P` with compact `tsupport ⊆ U`) and
  `𝒟ₙ(U) = GeometricCurrentOn U n` (sequentially continuous linear functionals on `𝒟ⁿ(U)`), both
  from SimonGMT. `∂T = T.boundary` is defined on degree `m + 1` by `∂T(ω) = T(dω)`.
- `|α|` is the Euclidean coefficient norm of a covector (`covectorEuclideanNorm`, Simon 1.15 and
  Remark 2.6), `M_W(T) = T.massOn W = sup {T(ω) : spt ω ⊆ W, |ω| ≤ 1}`, `M(T) = T.mass = M_U(T)`,
  `spt T = T.support` (2.11) and `T_j ⇀ T` is `WeaklyConvergesOn` (2.13).
- `W ⊂⊂ U` is `CompactlyContainedOpen W U`: `W` open, `closure W` compact and contained in `U`.
- `τ(M, θ, ξ)(ω) = tauAction n M θ ξ ω = ∫_M θ ⟨ω, ξ⟩ dHⁿ` (3.1 (‡)); a *rectifiable triple*
  `IsRectifiableTriple U n M θ ξ` requires `M ⊆ U` `Hⁿ`-null-measurable and countably
  `n`-rectifiable, `θ > 0` on `M` and integrable on `M ∩ K` for compact `K ⊆ U`, `ξ`
  `Hⁿ⌞M`-a.e. strongly measurable, and `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of a
  weighted approximate tangent space (`HasWeightedApproximateTangentSpaceAt`, Ch. 3, 1.7) at
  `Hⁿ`-a.e. `x ∈ M`. `IsIntegerMultiplicity T` asks for such a triple with `θ(x) ∈ ℕ` on `M`;
  `IsRectifiableCurrent T` allows real `θ`; `IsIntegralCurrent T` means `T` and `∂T` are integer
  multiplicity.
- `IsMeasureRepresentation T μ v` is (2.7): `⟨ω, v⟩` is `μ`-integrable and `T(ω) = ∫ ⟨ω, v⟩ dμ`
  for every test form; `IsRestriction T A S` is (2.9) through some representation;
  `IsMassMeasure T μ` is (2.8); `IsSlice T f t S` is (4.6),
  `S = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` with the sets taken inside `U`.
- `IsLipschitzPushforward T f S` is (3.6) through some representation `T = τ(M, θ, ξ)` and some
  field `L` of linear maps that are tangential derivatives of `f` at `Hⁿ`-a.e. point of `M`.
- `latticeFace ρ F`, `latticeFaceAction ρ F` and `IsLatticeChain ρ β P` describe the lattice chains
  `P = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]` of §5; `flatDistance W T₁ T₂` is `d_W` of (7.1).

**Degree convention.** Whenever a statement involves `∂T` for an `n`-current, the book's `n` is
written `m + 1`; in 6.1 the book's `n ≥ 2` is `m + 2`. In 5.3 and 6.2 the ambient space is
`ℝ^{(m+1)+ℓ}` and in 6.1 it is `ℝ^{(m+2)+ℓ}`, in each case with `ℓ ≥ 1`; 6.3 is stated for every
`ℝ^P`.

**Corrections already built into the frozen statement** (`GMT/Ch06/README.md`, "Errata / notes"):

- 4.10 is stated for a general `T`, with the localized constant `L_W ≥ ess sup_W |Df|`, with `M_W`
  on the right side (the printed `M` is weaker; the printed proof 4.9 gives `M_W`), and with the
  upper integral `∫*` encoded as a measurable majorant `g`.
- 5.3: the printed `n, k`, `C(n, k)`, `𝓛_j(ρ)` and "so is s" are read as `n, ℓ`, `C(n, ℓ)`,
  `𝓛ₙ(ρ)` and `S`; `dist(x, ∅) = ∞` is encoded by `Metric.thickening`.
- 6.2: the printed `F_n(ρ_k)`, `β_R^{(k)}` are read as `𝓛ₙ(ρ_k)`, `β_F^{(k)}`.
- 6.3: the printed `M(∂T)` is read as `M_W(∂T) < ∞` for all `W ⊂⊂ U`.
- 2.15 requires the convergence on continuous compactly supported forms for *all*
  representations (2.7) of the currents.

### 1.4 What `Submission.lean` contains

`GMT/Ch06/Submission.lean` (69506 lines) consists of, in order:

1. The contract's 8 imports and 7 further SimonGMT imports (`Chapter01.RadonCaratheodoryIntegral`,
   `Chapter06.AffineCurrentPushforward`, `Chapter01.RadonPolarRepresentation`,
   `Chapter02.AreaBranches`, `Chapter01.DensityComparison`, `Chapter02.AreaCritical`,
   `Chapter02.AreaDomain`), lines 1–15.
2. Lines 16–367: byte-for-byte the contract's lines 9–360, i.e. the module docstring, the `open`
   commands, `namespace GMT.Ch06`, `noncomputable section`, the 29 definitions of the contract
   (26 `def`s, 2 `abbrev`s and the `structure IsRectifiableTriple`) and the `end` closing the section.
3. Lines 368–69497: the 691 accepted child theorems `Submission.*`, all but six of them with a doc
   comment (Appendix A).
4. Line 69498: `main_theorem`, with the contract's statement and the proof of §2.
5. Line 69506: `end GMT.Ch06`.

There are no other declarations, no duplicate names, one `namespace GMT.Ch06` and one
`end GMT.Ch06`.

## 2. The root argument (the Lean proof of `main_theorem`)

```lean
theorem main_theorem : CompactnessUnderMassBounds ∧ … ∧ IntegralityOfWeakLimits := by
  exact ⟨Submission.compactness_under_mass_bounds, Submission.constancy_theorem,
    Submission.lipschitz_pushforward_integer_multiplicity, Submission.federer_fleming_compactness,
    Submission.slicing_theorem, Submission.deformation_theorem, Submission.isoperimetric_theorem,
    Submission.polyhedral_approximation, Submission.boundary_rectifiability,
    Submission.flat_convergence_iff_weak_convergence, Submission.rectifiability_theorem,
    Submission.integrality_of_weak_limits⟩
```

*Proof.* A conjunction is proved by proving each conjunct. The conjunction is right-nested, so the
anonymous constructor builds `And.intro h₁ (And.intro h₂ (… h₁₂))` from the twelve terms in order.
Inside `namespace GMT.Ch06`, `Submission.X` denotes `GMT.Ch06.Submission.X`. Each term's type is,
verbatim, the conjunct in its position: it is the frozen `lean_statement` of the accepted child.

| # | Conjunct | Proof term (line) | Accepted node; issue; solution PR |
| --- | --- | --- | --- |
| 1 | `CompactnessUnderMassBounds` | `compactness_under_mass_bounds` (69081) | `root.compactness_mass_bounds-a1`; issue #314; PR #4238 |
| 2 | `ConstancyTheorem` | `constancy_theorem` (42133) | `root.constancy-a1`; issue #316; PR #4888 |
| 3 | `LipschitzPushforwardIntegerMultiplicity` | `lipschitz_pushforward_integer_multiplicity` (46209) | `root.lipschitz_pushforward_im-a1`; issue #319; PR #4707 |
| 4 | `FedererFlemingCompactness` | `federer_fleming_compactness` (69482) | `root.federer_fleming-a1`; issue #342; PR #8802 |
| 5 | `SlicingTheorem` | `slicing_theorem` (66972) | `root.slicing-a1`; issue #322; PR #5777 |
| 6 | `DeformationTheorem` | `deformation_theorem` (66990) | `root.deformation-a1`; issue #325; PR #7759 |
| 7 | `IsoperimetricTheorem` | `isoperimetric_theorem` (67200) | `root.isoperimetric-a1`; issue #329; PR #8118 |
| 8 | `PolyhedralApproximation` | `polyhedral_approximation` (67293) | `root.polyhedral_approximation-a1`; issue #331; PR #8056 |
| 9 | `BoundaryRectifiability` | `boundary_rectifiability` (68901) | `root.boundary_rectifiability-a1`; issue #334; PR #8641 |
| 10 | `FlatConvergenceIffWeakConvergence` | `flat_convergence_iff_weak_convergence` (69448) | `root.flat_iff_weak-a1`; issue #338; PR #8796 |
| 11 | `RectifiabilityTheorem` | `rectifiability_theorem` (62437) | `root.rectifiability-a1`; issue #340; PR #5445 |
| 12 | `IntegralityOfWeakLimits` | `integrality_of_weak_limits` (68796) | `root.integrality_weak_limits-a1`; issue #341; PR #8548 |

The root uses no hypothesis, no other lemma and no tactic besides `exact`. Hence `main_theorem`
holds as soon as the twelve children hold; §3 proves them. ∎

## 3. Proofs of the twelve conjuncts (the formalized route)

The conjuncts are treated in a dependency order (§4): every theorem uses only theorems treated
before it. All names below are in namespace `GMT.Ch06`; `Submission.` is
omitted. "(Lnnnn)" is the line of the declaration in `GMT/Ch06/Submission.lean`. Every lemma named
here is an accepted node of the run; its full statement and proof are in Appendix A, and its frozen
Lean type is checked in §9. Library results are named with their full Lean names; §5 gives their
provenance.

### 3.0 Shared tools

Several facts are used by more than one conjunct. They are proved once, in the subtree where they
first arose, and reused (§6 lists the reuse).

**(R) Representation, mass measure and restriction (Simon 2.7–2.9, 2.12).**

- `rectifiability_mass_measure_representation` (L18946).
  If `M_W(T) < ∞` for all `W ⊂⊂ U`, then `T` has a mass measure `μ` (`IsMassMeasure T μ`), and for
  *every* mass measure `μ` there is a strongly measurable `ξ` with `∑_α ξ(x)(dx^α)² = 1` for
  `μ`-a.e. `x` and `T(ω) = ∫ ⟨ω, ξ⟩ dμ`. `T` is extended to continuous compactly supported forms by
  the mass estimate and uniform approximation (`cmb_exists_testForm_uniform_approx`); SimonGMT's
  vector Riesz theorem (Simon Ch. 1, 4.14: `simon_theorem_4_14_caratheodory` and the positive
  envelope `simon_theorem_4_14_positive_envelope`) represents the extension; an arbitrary mass
  measure is identified with the Riesz measure by uniqueness of measures agreeing on the π-system
  formed by the open sets `W ⊂⊂ U` and the Borel sets missing `U`.
- `slicing_mass_representation` (L22918). The same with a Borel field
  `v` satisfying `|⟨α, v(x)⟩| ≤ |α|`, and with the restrictions `(T ⌞ A)(ω) = ∫_A ⟨ω, v⟩ dμ` to Borel
  `A` being currents with `M_W(T ⌞ A) = μ(W ∩ A)` for open `W ⊆ U`. Here the Riesz step is Mathlib's
  Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) with Radon–Nikodym, on the σ-compact space
  `U` (`smr_rb_borel_riesz_sigma_compact`), and the lower bound `μ(W ∩ A) ≤ M_W(T ⌞ A)` is a
  unit-form argument (Lusin, Tietze, Urysohn: `smr_exists_unit_form_gt`).
- `iwl_restriction_theory` (L19780). (R0) a representation gives locally
  finite mass; (R1) restrictions do not depend on the representation; (R2) mass measures and
  restrictions exist, with `M_W(X ⌞ A) = μ(W ∩ A)`.
- Uniqueness of the vector measure `v μ`: `slicing_representation_unique`,
  `dmr_measureRepresentation_unique`, `polyhedral_approx_measure_uniqueness` (agreement on smooth
  test functions passes to continuous and then to bounded Borel functions).
- `deformation_mass_restriction` (L34528) packages all of this for
  `X ∈ 𝒟ₖ(ℝ^N)` with `M(X) < ∞`, including `X ⌞ A = τ(M ∩ A, θ, ξ)` for integer multiplicity `X`.

**(τ) Integer multiplicity currents.**

- `τ(M, θ, ξ)` is a current: `ltg_tau_integrable`, `br_loc_tauAction_current`,
  `slicing_im_tau_current` (`|⟨α, ξ⟩| ≤ ‖α‖` a.e. because `ξ = ±τ₁ ∧ ⋯ ∧ τₙ`, `fiw_ims_tt_unit_bound`).
- Mass formula (Remark 3.2(3)): `fiw_im_mass_formula`, `M_W(τ(M, θ, ξ)) = ∫_{M ∩ W} θ dHⁿ`.
- A representation lives on the support: `lpf_rectifiable_support_null`,
  `iwl_sp_rectifiable_support_null`, `fiw_tb_rectifiable_support_null`, `Hⁿ(M ∖ spt T) = 0`.
- Uniqueness of triples: `ltg_tau_unique_on_open`; restriction: `polyhedral_approx_restriction_tau`
  (`τ(M, θ, ξ) ⌞ A = τ(M ∩ A, θ, ξ)`), `dmr_rectifiableTriple_inter`, `iwl_im_closure`,
  `ind_pi_restriction_open_im`, `br_restrictDomain_isIntegerMultiplicity`.
- Closure properties of integer multiplicity: integer linear combinations (Remark 3.2(1):
  `deformation_im_combination`, `iwl_imc_lincomb_im`, `fiw_im_lincomb`) and `M`-absolutely
  convergent integer series (3.13: `fiw_im_series`, `fiw_ims_combine`). Both rest on the fact that
  weighted approximate tangent planes of two carriers agree `Hⁿ`-a.e. on their overlap
  (`deformation_imcomb_tangent_overlap`, `iwl_imc_tangent_overlap`, `fiw_tangent_locality`), which
  together with `fiw_ims_frame_sign` makes the orientations agree up to sign there. Limits in mass
  (Lemma 3.13): `deformation_im_completeness`. Dilations: `deformation_dilation`,
  `ind_rescaled_current`. Local-to-global: `br_isIntegerMultiplicity_of_local`, `iwl_im_patching`.

**(G) Rectifiable sets (Simon Chs. 2–3), proved in the file.**

- `C¹` approximation of Lipschitz maps (Ch. 2, 1.5): `lpf_c1_approximation_real` (Rademacher,
  Lusin `lpf_c1r_lusin_closed`, the uniform-remainder step with Egorov `lpf_c1r_uniform_remainder`,
  Whitney's extension theorem `lpf_c1r_whitney_extension`).
- `C¹` antilipschitz chart covers of countably rectifiable sets (Ch. 3, Lemma 1.2):
  `lpf_countably_rectifiable_c1_cover` and its variants `slicing_im_coarea_chart_cover`,
  `slicing_im_tg_c1_chart_cover`, `slicing_im_st_cd_c1_cover`.
- Approximate tangent planes: on a `C¹` chart (Ch. 3, proof of 1.6 and Remark 1.8(1)),
  `lpf_weighted_tangent_on_c1_chart`; almost everywhere on a rectifiable triple (Ch. 3, 1.9),
  `rectifiability_weighted_tangent_ae`; locality, `br_weightedTangent_congr`,
  `iwl_weighted_tangent_locality`.
- Area formula on rectifiable sets (Ch. 3, 2.4–2.5), `lpf_rectifiable_area_formula`, from SimonGMT's
  area formula for maps Lipschitz on a set; co-area formula for real Lipschitz functions (Ch. 3,
  2.8–2.9), `slicing_im_coarea`, with Eilenberg's inequality `slicing_im_coarea_eilenberg`.
- Density comparison (Ch. 1, 3.3), `rectifiability_density_comparison`; upper density theorem
  (Ch. 1, 3.6), `lpf_wtc_ae_zero_density_off_set` and `imc_ae_zero_density_off_set`.

**(S) Supports and the mass estimate.** A current kills every test form whose support misses its
support (`isoperimetric_apply_eq_zero_of_disjoint_support`); supports of boundaries, weak limits
and linear combinations behave as expected (`iwl_cr_support_lemmas`); and
`|T(ω)| ≤ M_W(T) · sup |ω|` for `spt ω ⊆ W` (`cmb_abs_apply_le_of_massOn_le`).

### 3.1 Lemma 2.15 — `compactness_under_mass_bounds` (L69081)

**Claim.** Let `U ⊆ ℝ^P` be open and `T_q ∈ 𝒟ₙ(U)` with `sup_q M_W(T_q) < ∞` for every `W ⊂⊂ U`.
Then some subsequence `T_{φ(q)}` converges weakly to some `T₀ ∈ 𝒟ₙ(U)`, and
`∫ ⟨ω, v_q⟩ dμ_q → ∫ ⟨ω, v₀⟩ dμ₀` for every continuous compactly supported `n`-form `ω` with
`tsupport ω ⊆ U` and all representations `(μ_q, v_q)` of `T_{φ(q)}` and `(μ₀, v₀)` of `T₀`.

**Proof.**

1. *Weakly convergent subsequence* (`cmb_exists_weakly_convergent_subseq`, the printed
   Banach–Alaoglu step made sequential).
   - Exhaust `U` by open `W_i ⊂⊂ U` such that every compact `K ⊆ U` lies in some `W_i`
     (`cmb_exists_compactly_contained_exhaustion`), and put `B_i = sup_q M_{W_i}(T_q) < ∞`.
   - For each `i` there is a countable family `E_i` of test forms supported in `W_i` that is
     uniformly dense, in the coefficient norm, among all test forms supported in `W_i`
     (`cmb_exists_countable_dense_testForms`).
   - By the mass estimate, `|T_q(η)| ≤ B_i sup |η|` for `η ∈ E_i`. The countable product of the
     compact intervals `[−b_η, b_η]` is sequentially compact, so one strictly increasing `φ` makes
     `T_{φ(q)}(η)` converge for every `η ∈ ⋃_i E_i`.
   - For an arbitrary test form `ω`, supported in some `W_i`, density and the mass estimate make
     `T_{φ(q)}(ω)` a Cauchy sequence. Its limit `L(ω)` is linear and satisfies
     `|L(ω)| ≤ B_i · N · sup ‖ω‖` for `spt ω ⊆ W_i`, which gives sequential continuity. So `L` is a
     current `T₀` and `T_{φ(q)} ⇀ T₀`.
2. *Mass bounds pass to the subsequence:* `sup_q M_W(T_{φ(q)}) ≤ sup_q M_W(T_q) < ∞`.
3. *Continuous forms* (`cmb_tendsto_integral_of_weaklyConvergesOn`). Fix `ω` and choose
   `W ⊂⊂ U` containing `tsupport ω`; let `B = sup_q M_W(T_{φ(q)})`. Lower semicontinuity of mass
   under weak convergence (Simon 2.14, SimonGMT's `WeaklyConvergesOn.massOn_le_liminf`) gives
   `M_W(T₀) ≤ B`.
   - For *any* representation `(μ, v)` of a current `X` with `M_W(X) ≤ B` and any continuous form
     `θ` with `tsupport θ ⊆ W` and `|θ| ≤ C`, `⟨θ, v⟩` is `μ`-integrable and
     `|∫ ⟨θ, v⟩ dμ| ≤ B C` (`cmb_measureRepresentation_continuous_bound`). Its proof shows that the
     coefficients `v_β = ⟨dx^β, v⟩` are integrable on compact sets
     (`cmb_rb_measureRepresentation_integrableOn_coeff`), bounds `|∫ ⟨θ, v⟩ dμ|` by
     `D ∑_β ∫ |v_β|` (`cmb_rb_integral_coeff_pairing_bound`), and then sharpens the constant to `B C`
     by approximating `θ` by test forms and using the mass estimate. No normalization of `v` is
     assumed.
   - Given `δ > 0`, mollification and a cut-off give a test form `η` supported in `W` with
     `|ω − η| ≤ δ` (`cmb_exists_testForm_uniform_approx`). Then
     `∫ ⟨ω, v_q⟩ dμ_q = T_{φ(q)}(η) + ∫ ⟨ω − η, v_q⟩ dμ_q`, with the last term at most `B δ`, and
     likewise for `(μ₀, v₀)`. As `T_{φ(q)}(η) → T₀(η)`, an `ε/3` argument concludes. ∎

*Uses:* no sibling.

### 3.2 Theorem 2.34 (Constancy) — `constancy_theorem` (L42133)

**Claim.** Let `U ⊆ ℝⁿ`, `n = m + 1`, be open and connected, `T ∈ 𝒟ₙ(U)` and `∂T = 0`. Then for some
`c ∈ ℝ`, `T(ω) = c ∫_U ω(x)(e₁, …, eₙ) dLⁿ(x)` for every `ω ∈ 𝒟ⁿ(U)`.

**Proof.** The Lean term is
`constancy_of_local_constancy (constancy_local_on_balls (constancy_closed_kills_partial_derivatives hT))`.

1. *Closed currents kill derivatives* (`constancy_closed_kills_partial_derivatives`, the printed
   display (2)). If `a ∈ C_c^∞` with `spt a ⊆ U` and `ω(x)(e) = D_j a(x)`, then `ω = dη` for
   `η = a · ι_{e_j}(dx¹ ∧ ⋯ ∧ dxⁿ)` (the book's `ω_j`), because top-degree covectors are determined
   by their value on `e = (e₁, …, eₙ)`. Hence `T(ω) = T(dη) = ∂T(η) = 0`.
2. *Local constancy* (`constancy_local_on_balls`). Every `x₀ ∈ U` has a ball `B_r(x₀) ⊆ U` and a
   `c` with `T(ω) = c ∫ ω(e)` whenever `spt ω ⊆ B_r(x₀)`.
   - Write `T(ω) = u(ω(·)(e))` with `u(b) = T(b dx¹ ∧ ⋯ ∧ dxⁿ)`
     (`constancy_topForm_scalar_reduction`).
   - For mollifiers `ψ_k` with supports shrinking to `0`, `F_k(f) = u(ψ_k ∗ 1_B f)` is linear and
     bounded on `L¹(B)`, `B = B_ρ(x₀)` (`constancy_mollified_functional_l1_bounded`, using the
     derivative bounds `constancy_mollifier_iteratedFDeriv_norm_le_integral` and the sequential
     continuity of `u`).
   - The duality `(L¹)* = L^∞` for finite measures, which the book uses without proof, is proved
     (`constancy_riesz_l1_dual_bounded_density`): a dominated finitely additive set function has a
     bounded density by Radon–Nikodym (`constancy_riesz_bounded_density_of_dominated_additive`), and
     the identity extends from indicators to `L¹` (`constancy_riesz_eq_integral_mul_of_indicator_eq`).
     So `F_k(f) = ∫_B f θ_k` with `θ_k` bounded.
   - By step 1, `θ_k` has vanishing weak partial derivatives on `B`
     (`constancy_mdc_weak_partials_vanish`), hence is a.e. constant there
     (`constancy_mdc_ae_const_of_weak_partials_vanish`, by mollification and Lebesgue points,
     `constancy_mdc_smooth_approx_identity_ae_tendsto`); this is `constancy_mollified_density_const`.
   - Letting `k → ∞` (`constancy_local_of_mollified_const`, with
     `constancy_approx_identity_iteratedFDeriv_tendstoUniformly`: `D^q(ψ_k ∗ b) → D^q b` uniformly
     for every `q`)
     gives `u(b) = c ∫ b` for `spt b ⊆ B`.
3. *Globalization* (`constancy_of_local_constancy`). On the overlap of two such balls the constants
   agree (test with a unit-integral form supported in the overlap,
   `constancy_exists_topTestForm_integral_eq_one`), so `x ↦ c(x)` is locally constant, hence
   constant on the connected `U`. A partition of unity subordinate to finitely many balls
   (`constancy_testFormOn_eq_finset_sum_subordinate`) adds up the local identities to
   `T = c [[U]]`. ∎

*Uses:* no sibling.

### 3.3 Theorem 8.1 (Rectifiability) — `rectifiability_theorem` (L62437)

**Claim.** Let `U ⊆ ℝ^P` be open, `n = m + 1`, `T ∈ 𝒟ₙ(U)` with `M_W(T) + M_W(∂T) < ∞` for all
`W ⊂⊂ U`, and suppose some mass measure `μ` of `T` has `Θ*ⁿ(μ, x) > 0` for `μ`-a.e. `x`. Then
`T = τ(M, θ, ξ)` for a rectifiable triple `(M, θ, ξ)` with real `θ`.

**Proof (assembly).**

1. `rectifiability_mass_measure_rectifiable` (printed (1)–(8)): `μ = θ Hⁿ ⌞ M` with `M ⊆ U` Borel and
   countably `n`-rectifiable, `θ` Borel, `θ > 0` on `M` and locally `Hⁿ`-integrable on `M` in `U`.
2. `rectifiability_mass_measure_representation` (part (ii), with `M_W(T) ≤ M_W(T) + M_W(∂T)`):
   `T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `ξ` strongly measurable and `|ξ| = 1` `μ`-a.e.
3. (9): as `μ = θ Hⁿ ⌞ M` and `θ > 0` on `M`, `T(ω) = ∫_M θ ⟨ω, ξ⟩ dHⁿ = τ(M, θ, ξ)(ω)`, and
   `|ξ| = 1` holds `Hⁿ`-a.e. on `M`.
4. `rectifiability_orientation` (printed (10)–(13), with `M_W(∂T) ≤ M_W(T) + M_W(∂T)`): for
   `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of a weighted approximate
   tangent space of `(M, θ)` at `x`. Together with step 1 this makes `(M, θ, ξ)` a rectifiable
   triple, and step 3 gives `T = τ(M, θ, ξ)`.

**Step 1 in detail** (`rectifiability_mass_measure_rectifiable`).

- *Absolute continuity, Remark 2.37(1)* (`rectifiability_mass_measure_abs_continuous`): `μ ≪ Hⁿ`.
  A Borel `B` with `Hⁿ(B) = 0` has `Lⁿ(p_α(B)) ≤ Hⁿ(B) = 0` for the 1-Lipschitz coordinate
  projections `p_α`, so Lemma 2.36 gives `μ(B) = 0`.
- *Lemma 2.36 with Remarks 2.37(1)–(2)* (`rectifiability_projection_null`): if `E` is Borel and
  `Lⁿ(p_α(Q(E))) = 0` for every `α ∈ I(n, P)`, `Q` a linear isometry, then `μ(E) = 0`. For compact
  `K ⊆ E`, `M_W(T) ≤ C μ(W ∖ K)` (`rpn_massOn_le_mul_measure_diff`), then `μ(K) = 0` by shrinking
  `W ↓ K` (`rpn_compact_null_of_le_mul_diff`), and inner regularity extends this to `E`
  (`rpn_null_of_compact_null`). The estimate expands each admissible form in the rotated frame
  (`rpn_covector_rotated_expansion`) and bounds each top-degree piece with small cut-offs on the
  null compact projections (`rpn_null_compact_cutoff`, `rpn_moc_abs_apply_top_form_le`). The bound
  on a piece is `rpn_pullback_top_form_bound`: `|T(φ)| ≤ C · M · Lⁿ(spt a)^{1/n}` for
  `φ = f · (a ∘ L) · L^#dy`, obtained from `T(φ) = ∂T(Φ) − T(Ξ)` (`rpn_extDeriv_potential_form`)
  and the potential estimate `rpn_potential_estimate`. That estimate replaces the BV argument of
  Remark 2.35 by the potential estimates of Gilbarg–Trudinger, §7.8. It writes `a = ∑_j ∂_jψ_j`
  with `ψ_j = K_j * a` and the kernels `K_j(t) = t_j/(nω_n|t|ⁿ)` (the representation formula of
  Lemma 7.14), and bounds `|ψ_j| ≤ C M Lⁿ(spt a)^{1/n}` through `∫_S |w|^{1−n} dw ≤ c Lⁿ(S)^{1/n}`
  (as in the proof of Lemma 7.12).
- *σ-finiteness and null sets on the positive-density carrier*
  (`rectifiability_positive_density_cover_null`, printed (1) and (6)): by the density comparison
  (Ch. 1, 3.3), a set of positive upper density covered by open sets of finite `μ`-measure is
  covered by countably many sets of finite `Hⁿ`-measure, and it is `Hⁿ`-null when it is `μ`-null.
- *Decomposition and structure theorem.* SimonGMT's
  `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` (Ch. 3, Lemma 3.2) splits a
  Borel carrier `B₀ ⊆ U ∩ {Θ*ⁿ(μ, ·) > 0}` of `μ`, which is `Hⁿ`-σ-finite, into a countably
  `n`-rectifiable Borel part `R` and a purely `n`-unrectifiable part `P′`. The structure theorem (Ch. 3, 3.6),
  `rectifiability_structure_projection`, gives a linear isometry (orthogonal transformation) `Q` of
  `ℝ^P` for which every coordinate projection `p_α(Q(P′))` is `Lⁿ`-null. It assumes only that `P′`
  is purely `n`-unrectifiable and covered by countably many sets `S_j` of finite `Hⁿ`-measure, and
  it is derived from the Besicovitch–Federer projection theorem
  `rectifiability_bf_projection_null_ae` (for a Borel, purely unrectifiable `E` with `Hⁿ(E) < ∞`,
  `Lⁿ(L_v(E)) = 0` for Lebesgue-a.e. frame `v`) as follows.
  - Each `P′ ∩ S_j` has a Borel hull `B_j` with `Hⁿ(B_j ∩ F) = Hⁿ(P′ ∩ S_j ∩ F)` for measurable `F`.
    Splitting `B_j` by Ch. 3, Lemma 3.2 shows that `B_j` is purely unrectifiable: its countably
    rectifiable part is `Hⁿ`-null by this identity.
  - Inner regularity gives compact `C_{j,i} ⊆ B_j` with `Hⁿ(B_j ∖ ⋃_i C_{j,i}) = 0`.
  - For a.e. frame `v`, every `L_v(C_{j,i})` is null. So is `L_v(P′ ∖ ⋃_{j,i} C_{j,i})`, because
    `L_v` is Lipschitz and that set is `Hⁿ`-null.
  - The set `Z` of bad frames (those `v` with `Lⁿ(L_v(C_{j,i})) > 0` for some `j, i`) is Borel
    and null. For every `n × n` matrix `G`, `Lⁿ(L_{Gv}(C)) = |det G| Lⁿ(L_v(C))`, where `Gv` is the
    frame with rows recombined by `G`. Hence `v ∈ Z` whenever `Gv ∈ Z`.
  - The first `n` Gram–Schmidt vectors of a frame recombine its first `n` vectors. Apply
    Gram–Schmidt to a random frame, distributed by Lebesgue measure on the linearly independent
    frames in a ball. Tonelli's theorem shows that the orthonormalized frame and its transpose have
    the same law, and coordinate permutations reduce every `α` to `α = (1, …, n)`. This gives an
    orthonormal basis `(b_k)` all of whose subframes `(b_{α(1)}, …, b_{α(n)})` avoid `Z`. The
    linear isometry `Q` with `Q⁻¹ e_k = b_k` then satisfies `p_α ∘ Q = L_{(b_{α(i)})_i}` for every
    `α`.

  The details are in the entry for `rectifiability_structure_projection` in A.3. The projection
  theorem follows Mattila, Ch. 18 and Hovila–Järvenpää–Järvenpää–Ledrappier:
  - the trichotomy `rectifiability_bf_trichotomy`, built from the Mickle–Radó density theorem
    `rectifiability_mickle_rado`, Borel measurability of the cone ratio, and the comparison of cones
    with fibres;
  - the conical density lemma `rectifiability_bf_cone_density`, whose exceptional set is
    `Hⁿ`-null;
  - the density comparison for the points of infinite projected density;
  - Eilenberg finiteness `rectifiability_bf_infinite_fibre_null` for the points with infinite
    fibres.
- Hence `μ(P′) = 0`. The decomposition gives `P′` only as an `Hⁿ`-null-measurable set, so the
  Lean proof takes a Borel set `B_k ⊆ P′` with `Hⁿ(P′ ∖ B_k) = 0`. Lemma 2.36 with this `Q` gives
  `μ(B_k) = 0`, and `μ ≪ Hⁿ` gives `μ(P′ ∖ B_k) = 0`. Then `Hⁿ(P′) = 0` by
  `rectifiability_positive_density_cover_null` (printed (6)), so `B₀ = R ∪ P′` is countably
  rectifiable (printed (7)).
- Finally, `Hⁿ ⌞ B₀` is σ-finite (it is covered by sets of finite `Hⁿ`-measure), `μ` is σ-finite,
  `μ(ℝ^P ∖ B₀) = 0` and `μ ≪ Hⁿ`. So σ-finite Radon–Nikodym
  (`rectifiability_rn_positive_real_density`, printed (8)) gives a Borel `M ⊆ B₀` and a Borel
  `θ > 0` on `M` with `μ = (Hⁿ ⌞ M).withDensity θ`. Here `M = B₀ ∩ {0 < dμ/d(Hⁿ⌞B₀) < ∞}`, which
  is countably rectifiable as a subset of `B₀`, and `θ = (dμ/d(Hⁿ⌞B₀)).toReal`, which is
  `Hⁿ`-integrable on `M ∩ K` whenever `μ(K) < ∞`. A compact `K ⊆ U` lies in one of the exhaustion
  sets `W_i` with `μ(W_i) < ∞`, so `θ` is locally integrable on `M` in `U`.

**Step 4 in detail** (`rectifiability_orientation`, printed (10)–(13)). Weighted approximate
tangent spaces `L = TₓM` exist `Hⁿ`-a.e. on `M` (`rectifiability_weighted_tangent_ae`, Ch. 3, 1.9
"⇒"). That lemma cuts the Lipschitz parametrizations of `M` into Borel pieces on which they are
differentiable with injective derivative and uniformly bi-Lipschitz (Rademacher's theorem, null
images of critical sets, an approximately linear partition), and then uses the injective area
formula and Lebesgue points. Fix a point `x`
where moreover `ξ` has a Lebesgue point for `θ Hⁿ ⌞ M` and both `θ Hⁿ ⌞ M` and the mass measure
`ν` of `∂T` have finite upper `n`-density (Ch. 1, 3.3). Let `a` be a covector vanishing on `L`,
`β` an `(n−1)`-covector, `ϕ` a cut-off with support in `B̄₂(0)`, `Ψ(z) = a(z) ϕ(z) β` and
`Ω = dΨ`; on `L`, where `a(z) = 0`, `Ω = ϕ · (a ∧ β)`. With the blow-up forms
`ψ_r(y) = r Ψ((y − x)/r)`, supported in `B̄_{2r}(x)` and with `dψ_r(y) = Ω((y − x)/r)`:

- `I_r := ∂T(ψ_r) = T(dψ_r) = ∫_M θ ⟨Ω((y − x)/r), ξ(y)⟩ dHⁿ(y)`;
- (12) `|I_r| ≤ M_{B_{4r}(x)}(∂T) · sup |ψ_r| = O(rⁿ) · O(r)`;
- (11) `r⁻ⁿ I_r → θ(x) ∫_L ⟨Ω, ξ(x)⟩ dHⁿ`, by the weighted tangent plane at `x` and the Lebesgue
  point of `ξ`.

Hence `∫_L ⟨Ω, ξ(x)⟩ dHⁿ = ⟨a ∧ β, ξ(x)⟩ ∫_L ϕ dHⁿ = 0` with `∫_L ϕ > 0`, i.e.
`⟨a ∧ β, ξ(x)⟩ = 0`. (This is the conclusion that the book draws on p. 175 from its display (13),
the definition of the limit current `S_x`, and from `∂S_x = 0`.) In an orthonormal frame adapted
to `L` this forces
`ξ(x) = c τ₁ ∧ ⋯ ∧ τₙ`, and `|ξ(x)| = 1` gives `c = ±1`. ∎

*Uses:* no sibling. The structure theorem, which SimonGMT does not provide (`GMT/Ch06/README.md`), is
proved here.

### 3.4 Lemma 3.9 — `lipschitz_pushforward_integer_multiplicity` (L46209)

**Claim.** Let `T ∈ 𝒟ₙ(U)` be integer multiplicity, `f` locally Lipschitz on `U` with `f(U) ⊆ V`
(`U ⊆ ℝ^P`, `V ⊆ ℝ^Q` open), and `f⁻¹(K) ∩ spt T` compact for compact `K ⊆ V`. Then some
`S ∈ 𝒟ₙ(V)` satisfies `IsLipschitzPushforward T f S` and is integer multiplicity.

**Proof.** Write `T = τ(M, θ, ξ)` with `θ` natural-valued.

1. *Tangential differential* (`lpf_tangential_differential_exists`; Ch. 3, §2, 2.1–2.2 and p. 76).
   There is `L : ℝ^P → L(ℝ^P, ℝ^Q)`, `Hⁿ⌞M`-a.e. strongly measurable and bounded on `M ∩ K` for
   compact `K ⊆ U`, such that for `Hⁿ`-a.e. `x ∈ M` and every `v` in every weighted approximate
   tangent space of `(M, θ)` at `x`, `t ↦ f(x + tv)` has derivative `L(x)v` at `0`.
   - `M` is covered up to a null set by `C¹` charts `Φ_j` antilipschitz on open `Ω_j`
     (`lpf_countably_rectifiable_c1_cover`).
   - On each chart, `D(f ∘ Φ_j)(w) ∘ Λ(DΦ_j(w))`, with `Λ` the Moore–Penrose left inverse
     (`lpf_tde_continuous_left_inverse`), is Borel (`lpf_tde_mcd_single_chart`); the pieces are
     glued by the first chart index (`lpf_tde_mcd_countable_glue`).
   - Rademacher on the charts makes the non-differentiability set null
     (`lpf_tde_chart_nondiff_image_null`). `DΦ_j(w)(ℝⁿ)` is the weighted tangent space a.e.
     (`lpf_weighted_tangent_on_c1_chart`), and the directional derivative identity holds there
     (`lpf_tde_chart_directional_deriv`, with uniform Lipschitz bounds near compacts
     `lpf_tde_uniform_lipschitz_near_compact`).
2. *The push-forward is a current* (`lpf_pushforward_is_current`, (3.6)).
   `S(ω) = ∫_M θ ⟨ω(f(x)), L(x)_# ξ(x)⟩ dHⁿ` defines `S ∈ 𝒟ₙ(V)`. The density `θ L_#ξ` is
   measurable (`lpf_pic_density_aestronglyMeasurable`). On `{f ∈ K}` it is dominated by the
   integrable `1_{K′} Cⁿ θ`, `K′ = f⁻¹(K) ∩ spt T` compact (`lpf_pic_density_dominated`), because
   `Hⁿ(M ∖ spt T) = 0` (`lpf_rectifiable_support_null`) and `‖A_#v‖ ≤ ‖A‖ⁿ‖v‖`.
   `lpf_pic_current_of_dominated_density` turns this into a current. Together with step 1, the data
   `(M, θ, ξ, L)` witness `IsLipschitzPushforward T f S`.
3. *Integrality* (`lpf_pushforward_integrality`, printed 3.4–3.9).
   - *Source side* (`lpf_pi_source_charts`): for `Hⁿ`-a.e. `x ∈ M` with `L(x)_#ξ(x) ≠ 0`,
     `L(x)_#ξ(x) = ±‖L(x)_#ξ(x)‖ σ₁ ∧ ⋯ ∧ σₙ` for an orthonormal frame `σ` of the tangent plane
     `DG_k(w)(ℝⁿ)` of a `C¹` antilipschitz chart `G_k` with `G_k(w) = f(x)`
     (`lpf_pi_induced_orientation`, `lpf_lipschitz_c1_immersion_pieces`).
   - *Area formula* (`lpf_rectifiable_area_formula`):
     `∫_A h ‖L_#ξ‖ dHⁿ = ∫ ∑_{x ∈ A ∩ f⁻¹(y)} h(x) dHⁿ(y)`, from the chart chain rule
     `lpf_chart_chain_rule` and the Jacobian identity `lpf_raf_jacobian_identity`.
   - *Image density* (`lpf_pi_image_density`): `S(ω) = ∫_Y ⟨ω, Ψ⟩ dHⁿ`, where `Ψ(y)` is the fibre
     sum of `θ(x) ‖Ξ(x)‖⁻¹ Ξ(x)` over `f(x) = y`, `Ξ = L_#ξ`; `Ψ(y)` is a.e. an integer combination
     of unit simple `n`-vectors of chart tangent planes (signed fibre sums
     `lpf_pi_signed_fibre_sum`, local finiteness `lpf_pi_local_finite_weight`, null images
     `lpf_locally_lipschitz_image`).
   - *Target side* (`lpf_pi_im_of_chart_density`): at `Hⁿ`-a.e. `y` all chart planes through `y`
     are the approximate tangent plane of `Y` (`lpf_weighted_tangent_on_c1_chart` for `(Y, 1)`),
     so the unit simple `n`-vectors agree up to sign (`lpf_pi_simple_unit_facts`), and
     `Ψ(y) = c(y) σ₁ ∧ ⋯ ∧ σₙ` with `c(y) ∈ ℤ`. Hence `S = τ(M′, θ′, ξ′)` with `M′ = {Ψ ≠ 0}`,
     `θ′ = ‖Ψ‖ ∈ ℕ` and `ξ′ = Ψ/‖Ψ‖`.

   The rejected first version of the decomposition argued that different image sheets have
   density zero at each other's points (audit `decomposition-audit-v1.json`); the accepted proof,
   and the Lean proof, use the common tangent plane of overlapping sheets instead. ∎

*Uses:* no sibling.

### 3.5 Slicing, Simon 4.4–4.10 — `slicing_theorem` (L66972)

**Claim.** Let `U ⊆ ℝ^P` be open, `T ∈ 𝒟_{m+1}(U)` with `M_W(T) < ∞` and `M_W(∂T) < ∞` for all
`W ⊂⊂ U`, and `f` `L`-Lipschitz on `U`. Then there are `S : ℝ → 𝒟_m(U)` such that

1. `S(t)` is a slice `⟨T, f, t⟩` in the sense of (4.6) for every `t`;
2. `spt S(t) ⊆ spt T ∩ {f = t}` for every `t` (4.8);
3. if `T` is integer multiplicity, `S(t)` is integer multiplicity for `L¹`-a.e. `t` (4.4, 4.5(2));
4. for every open `W ⊆ U`, every `L_W` with `‖Df‖ ≤ L_W` a.e. on `W`, all `a < b` and every
   restriction `R = T ⌞ {a < f < b}`, there is a measurable `g` with `M_W(S(t)) ≤ g(t)` on
   `(a, b)` and `∫_{(a,b)} g ≤ L_W M_W(R)` (4.9–4.10).

**Proof (assembly).** Choose `S(t)` with `slicing_exists` for every `t` (axiom of choice). Then
(2) is `slicing_support_subset`, (4) is `slicing_mass_bound` (valid for any family of slices), and
(3) follows from `slicing_integer_multiplicity_ae`, whose exceptional null set of levels does not
depend on the chosen slices.

- **Existence, 4.6** (`slicing_exists`). `A_t = {x ∈ U : f(x) < t}` is open, since `f` is continuous
  on the open `U`. `slicing_mass_representation` (§3.0 (R)) represents `T` and `∂T` and makes their
  restrictions to `A_t` currents; `∂(T ⌞ A_t) − (∂T) ⌞ A_t` is again sequentially continuous.
- **Support, 4.8** (`slicing_support_subset`). With representations `(μ, v)` of `T` and `(μ′, v′)` of
  `∂T`, `S(ω) = ∫_{A_t} ⟨dω, v⟩ dμ − ∫_{A_t} ⟨ω, v′⟩ dμ′`. For `ω` supported where `T` vanishes, both
  integrals vanish by uniqueness of the representation (`slicing_representation_unique`, against the
  zero representation); for `ω` supported in `{f > t}` both vanish; and for `ω` supported in
  `{f < t}` both equal `T(dω)`.
- **Mass bound, 4.9–4.10** (`slicing_mass_bound`).
  - *Pointwise bound 4.9* (`slicing_mb_pointwise`):
    `M_W(S(t)) ≤ L_W liminf_{h↓0} h⁻¹ μ(W ∩ {t − h ≤ f ≤ t})` for the normalized representation.
    For an admissible `ω`, take the smooth cut-off `χ_h` of `slicing_mb_cutoff` (equal to `1` below
    `t − h`, to `0` above `t`, with slope at most `(1 + ε)/h`). The defect of 4.11, computed
    through representations `(μ, v)` of `T` and `(μ′, v′)` of `∂T`,
    `X(h) = ∫ χ_h(f) ⟨ω, v′⟩ dμ′ − ∫ χ_h(f) ⟨dω, v⟩ dμ`, tends to `−S(ω)` as `h ↓ 0`
    (`slicing_mb_pointwise_cutoff_tendsto`, dominated convergence). It is bounded by
    `(1 + ε)/h · L_W · μ(W ∩ {t − h ≤ f ≤ t})` (`slicing_mb_cutoff_defect_bound`).
    That bound uses: the Leibniz rule `d(ψω) = ψ dω + Dψ ∧ ω` (`slicing_mb_leibniz_bound`); the
    wedge estimate `|α ∧ γ| ≤ ‖α‖ |γ|` (`slicing_mb_wedge_norm_le`, computing the coefficient norm in
    an orthonormal basis adapted to `α`); and, as in Simon's "`f^{(σ)}` in place of `f`", smooth
    functions `g` close to `f` on `spt ω` with `‖Dg‖ ≤ L_W` (`slicing_mb_smooth_approx`, a
    mollified McShane extension; this is where only `ess sup_W |Df| ≤ L_W` is needed).
    `slicing_mb_pointwise_liminf_bound` passes to the `liminf` and lets `ε ↓ 0`.
  - *Integration 4.10* (`slicing_mb_density_majorant`): the lower left density of
    `ν = f_#(μ ⌞ W)` has a Borel majorant with integral over `(a, b)` at most `ν((a, b))` (lower left
    Dini derivative of the distribution function, and Lebesgue's theorem for monotone functions).
  - *Identification:* by uniqueness of restrictions, `M_W(R) = μ(W ∩ {a < f < b}) = ν((a, b))`.
- **Integrality, 4.4–4.5(2)** (`slicing_integer_multiplicity_ae`). Write `T = τ(M, θ, ξ)` and
  replace `f` by a McShane extension `g` (slices only see `f` on `U`).
  - *Tangential gradient* (`slicing_im_tangential_gradient`): a Borel `G` with `‖G‖ ≤ L` that lies in
    the weighted tangent plane and represents the derivative of `g` along it, `Hⁿ`-a.e. on `M`
    (chart gradients via Gram representatives, `slicing_im_tg_chart_gradient`).
  - *Countable determining family* (`slicing_im_testform_determining`): countably many test forms
    determine currents, so a.e. statements for each of them give one common null set of levels.
  - *Slice triple* (`slicing_im_slice_triple`, Simon 4.1–4.4): for a.e. `t`,
    `M_t = {x ∈ M : g(x) = t, G(x) ≠ 0}` with multiplicity `θ` and orientation
    `ξ_t = ξ ⌞ (G/|G|)` is a rectifiable `m`-triple. Its ingredients are the co-area formula
    `slicing_im_coarea` (chart pieces, regular and critical parts, Eilenberg's inequality), the
    measure-theoretic fields `slicing_im_st_measure_fields`, the slice geometry
    `slicing_im_st_slice_geometry` (`M_t` is countably `m`-rectifiable with weighted tangent plane
    `TₓM ∩ G(x)^⊥`, through level-set charts from the implicit function theorem,
    `slicing_im_st_level_set_charts`) and the interior product
    `slicing_im_st_interior_product` (Simon 4.3: `ξ ⌞ ν = ±τ′₁ ∧ ⋯ ∧ τ′ₘ`).
  - *Slice identity* (`slicing_im_slice_identity`, Remark 4.2 and the proof of 4.5(2)): for each
    test form `ω` and a.e. `t`, every slice `S` at `t` has `S(ω) = τ(M_t, θ, ξ_t)(ω)`. Let `b` be a
    Borel density with `θ ⟨G♭ ∧ ω, ξ⟩ = |G| b` a.e. on `M` (`slicing_im_si_borel_density`) and
    `φ(r) = ∫_{M ∩ g⁻¹{r}} b dHᵐ`; by the co-area formula and the null transfer to slices,
    `φ(t) = τ(M_t, θ, ξ_t)(ω)` for a.e. `t`. For the Lipschitz cut-off `h_ε = ψ_ε ∘ g`
    (`ψ_ε(s) = max(0, min(1, (t − s)/ε))`, with tangential gradient `−ε⁻¹ 1_{t−ε<g<t} G`), the
    Leibniz rule for Lipschitz multipliers (`slicing_im_lipschitz_leibniz`: mollify, use the tangent
    dual field, and pass to the limit with the tangential weak limit
    `slicing_im_ll_tangential_weak_limit`, which rests on weak-* convergence of gradients of
    uniformly convergent Lipschitz functions, `slicing_im_ll_gradient_weak_star`) and the signed
    co-area formula give `∫ h_ε ⟨ω, v′⟩ dμ′ − ∫ h_ε ⟨dω, v⟩ dμ = −ε⁻¹ ∫_{t−ε}^t φ`. As `ε ↓ 0`, the
    left side tends to `(∂T) ⌞ A_t (ω) − ∂(T ⌞ A_t)(ω) = −S(ω)` (dominated convergence) and, at a
    left Lebesgue point `t` of `φ`, the right side tends to `−φ(t)`.
  - `slicing_im_tau_current` makes `τ(M_t, θ, ξ_t)` a current; agreement on the determining family
    gives equality, and `θ ∈ ℕ` on `M_t ⊆ M`. ∎

*Uses:* no sibling. The co-area formula and the slicing calculus of Ch. 3, §2 and Ch. 6, 4.1–4.3 are
proved here rather than cited.

### 3.6 Deformation Theorem 5.1/5.3 — `deformation_theorem` (L66990)

**Claim** (`DeformationTheorem`). For `n = m + 1`, `ℓ ≥ 1` and `d = n + ℓ` there is `C = C(m, ℓ)`
such that every `T ∈ 𝒟ₙ(ℝ^d)` with `M(T) + M(∂T) < ∞` and every `ρ > 0` admit `P_c, β, R, S` with:
`P_c = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]`; `T − P_c = ∂R + S`; `M(P_c) ≤ C M(T)`, `M(∂P_c) ≤ C M(∂T)`,
`M(R) ≤ C ρ M(T)`, `M(S) ≤ C ρ M(∂T)`; `spt P_c ∪ spt R` and `spt ∂P_c ∪ spt S` within distance
`< 2√d ρ` of `spt T` and `spt ∂T` respectively; `β_F ∈ ℤ` and `P_c, R` integer multiplicity when `T`
is; `S` integer multiplicity when `T` and `∂T` are.

**Proof (assembly; the Lean proof follows these steps literally).**

- Let `C₁` be the constant of `deformation_onto_skeleton` (instantiated with `slicing_theorem` and
  `lipschitz_pushforward_integer_multiplicity`, §3.5 and §3.4) and `C₂` that of
  `deformation_skeleton_polyhedral`; put `C = C₁ + C₁C₂`.
- **Rescale.** By `deformation_dilation` with `η_λ(x) = λx`, `T′ = (η_{1/ρ})_# T` exists with
  `M(T′) = ρ^{−n} M(T)`, `M(∂T′) = ρ^{−m} M(∂T)` (`∂T′ = (η_{1/ρ})_# ∂T`), `spt T′ = ρ⁻¹ spt T`,
  and `T′` integer multiplicity if `T` is (the same for `∂T`).
- **Deform onto the unit skeleton.** `deformation_onto_skeleton` gives `T′ − Q = ∂R₁ + S₁` with
  `spt Q` in the unit `n`-skeleton `⋃_F latticeFace 1 F`, `Q` killing forms without tangential
  component near each face, `M(Q) ≤ C₁ M(T′)`, `M(∂Q) ≤ C₁ M(∂T′)`, `M(R₁) ≤ C₁ M(T′)`,
  `M(S₁) ≤ C₁ M(∂T′)`, `spt Q ∪ spt R₁` in the closed `√d`-neighbourhood of `spt T′`,
  `spt ∂Q ∪ spt S₁` in that of `spt ∂T′`, `Q, R₁` integer multiplicity if `T′` is, and `S₁`
  integer multiplicity if `T′, ∂T′` are.
- **Replace `Q` by a lattice chain.** `deformation_skeleton_polyhedral` gives
  `Q − P = S′` with `P = ∑_F β_F [[F]]` on the unit lattice, `M(P) ≤ C₂ M(Q)`,
  `M(∂P) ≤ C₂ M(∂Q)`, `M(S′) ≤ C₂ M(∂Q)`, `spt P` in the closed `√n`-neighbourhood of `spt Q`,
  `spt ∂P ∪ spt S′` in that of `spt ∂Q`, and `β_F ∈ ℤ`, `P` integer multiplicity, if `Q` is.
- **Combine.** `S″ = S₁ + S′` (a current, with `M(S″) ≤ M(S₁) + M(S′)` and
  `spt S″ ⊆ spt S₁ ∪ spt S′`), so `T′ − P = ∂R₁ + S″`.
- **Scale back.** `P_c = (η_ρ)_# P` is the lattice chain `∑_F β_F [[ρF]]` at scale `ρ`
  (`deformation_dilation`, lattice clause), `R = (η_ρ)_# R₁` and `S = (η_ρ)_# S″`. Testing with
  `η_ρ^# ω` gives `T − P_c = ∂R + S`. The masses scale by `ρ^n`, `ρ^m`, `ρ^{n+1}`:
  `M(P_c) = ρⁿ M(P) ≤ C₁C₂ M(T)`, `M(∂P_c) ≤ C₁C₂ M(∂T)`, `M(R) = ρ^{n+1} M(R₁) ≤ C₁ ρ M(T)` and
  `M(S) = ρⁿ M(S″) ≤ (C₁ + C₁C₂) ρ M(∂T)`. Supports lie within `√n + √d < 2√d` of `spt T′`
  (resp. `spt ∂T′`) before scaling, hence in the open `2√d ρ`-neighbourhood of `spt T`
  (resp. `spt ∂T`) after it.
- **Integrality.** If `T` is integer multiplicity, so are `T′`, `Q`, `R₁`, `P` (with `β_F ∈ ℤ`),
  and hence `P_c` and `R`. If also `∂T` is, then `S₁` is, `S′ = 1·Q + (−1)·P` and
  `S″ = 1·S₁ + 1·S′` are integer multiplicity by `deformation_im_combination` (Remark 3.2(1), via the
  series theorem `fiw_ims_combine` and `deformation_imcomb_tangent_overlap`), and so is `S`.

**The main step, `deformation_onto_skeleton`** (printed proof of 5.1, displays (1)–(26)). It is
stated with the Slicing Theorem and Lemma 3.9 as hypotheses and applied to §3.5 and §3.4.

1. *Good centre* (`deformation_good_center`, printed (1)–(7)). For the finite mass measures `μ₁, μ₂`
   of `T` and `∂T` (`deformation_mass_restriction`), there is `a` near `(1/2, …, 1/2)` with
   `μᵢ{dist(·, L_{ℓ−1}(a)) < σ} ≤ c σ^{m+2} μᵢ(ℝ^d)` for `0 < σ < 1/4`. This is proved by the
   periodic maximal estimate `dgc_periodic_maximal` (Vitali covering, `dgc_pm_vitali_volume_bound`),
   the corrected cylinder bound `dgc_cylinder_volume` (printed (5)) and the tube cover
   `dgc_tube_cover`; ball volumes are bounded by the cube bound `Lᵏ(B̄_r) ≤ (2r)ᵏ`
   (`dgc_pm_ball_volume_le`), a simplification of the printed `ω_k rᵏ`.
2. *Retraction, Lemma 5.4* (`deformation_retraction`). A map `ψ` sends `ℝ^d ∖ L_{ℓ−1}(a)` into the
   `n`-skeleton and each unit cube into itself, and is `c/σ`-Lipschitz on
   `{dist(·, L_{ℓ−1}(a)) ≥ σ}`. It is the periodic extension of the composite of radial face
   retractions of the unit cube (`deformation_retraction_cube_core`), whose pointwise Lipschitz
   constant `c₁/dist(x, L(a))` (claim (3)) is proved by induction on the face dimension with the
   corrected similarity bound `dr_cc_similarity_bound`; `deformation_retraction_globalize` passes
   from pointwise to Lipschitz bounds.
3. *Good radii* (`deformation_good_radius`, printed (10)). The Slicing Theorem's mass bound for `T`
   and `∂T` sliced by `dist(·, L_{ℓ−1}(a))`, with a Chebyshev choice, gives
   `σ_ν ∈ (2^{−ν−4}, 2^{−ν−3})` with small slices.
4. *Push-forward and homotopy* (`deformation_pushforward_homotopy`, Simon 2.17–2.29, 3.2(2)). For a
   Lipschitz `f`, the operators `P X = f_# X` and `H X = h_#([[0,1]] × X)`,
   `h(t, x) = f(x) + t(x − f(x))`, are defined on normal currents by smooth approximation
   (`dph_lipschitz_pushforward`: comparison lemma, existence, `∂P = P∂`, linearity), with the
   interval product `[[0,1]] × X` (`dph_interval_product`: existence, mass and support bounds,
   boundary formula) and the homotopy formula `X − P X = ∂ H X + H ∂X`
   (`dph_smooth_homotopy`, with the affine estimate 2.27 `dph_sh_affine_estimate`). Integrality of
   `P X` and `H X` for integer multiplicity `X` (`dph_lipschitz_pushforward_im`,
   `dph_interval_product_im`) uses `deformation_im_pushforward_limit`: Lemma 3.9's push-forward is
   the limit of `C¹` push-forwards. That limit is proved by weak continuity of Jacobian minors
   under uniform convergence with Lipschitz bounds (`deformation_ipl_minor_weak_continuity`; Ball
   1977, via integration by parts for minors, the Piola identity and density of smooth test
   functions), on the chart pieces of `M`.
5. *Truncations and limits* (printed (11)–(21)). With `d_a = dist(·, L_{ℓ−1}(a))`, the pieces
   `X_ν = T ⌞ {d_a ≥ σ_ν}`, `Z′_ν = (∂T) ⌞ {d_a ≥ σ_ν}` and their increments are pushed forward by
   `ψ` and along the homotopy. The estimates (11)–(16) make the increments summable in mass, so
   `Q = lim ψ_# X_ν`, `R = lim H X_ν` and `S = lim H Z′_ν` exist with the mass bounds
   (`deformation_telescope_limit`, via the series of currents `fiw_ims_series_current`). The
   homotopy formula gives `T − Q = ∂R + S` and `∂Q = lim ψ_# Z′_ν`. `spt Q` lies in the skeleton
   because the skeleton is closed (`deformation_skeleton_isClosed`) and supports pass to weak limits.
6. *Integrality.* The approximants are integer multiplicity, and limits in mass of integer
   multiplicity currents are integer multiplicity (`deformation_im_completeness`, Lemma 3.13).

**`deformation_skeleton_polyhedral`** (printed (26)–(37)). Write `Q` and `∂Q` through their
representations (`deformation_mass_restriction`). Finite boundary mass forces the
`dx^γ`-coefficient of `Q` to vanish a.e. on each hyperplane `{x_{γ(i)} = c}`. So `Q` does not
charge the `(n−1)`-skeleton and is the sum over the open faces `F` of `∫_F ω(e_F) v_F dμ` (so the
tangentiality hypothesis is in fact not needed). On each open face a Poincaré inequality, built
from a smooth divergence solver, and a trace inequality bound `Q ⌞ F − b_F [[F]]` by `M(∂Q)` near
`F`, where `b_F` is a weighted mean of the density. Take `β_F = b_F`, or `β_F = round(b_F)` when `Q`
is integer multiplicity: the density is then integer valued on `F`, so `|b_F − round(b_F)|` obeys
the same bound. An integer lattice chain is integer multiplicity. ∎

*Uses:* `slicing_theorem` (§3.5) and `lipschitz_pushforward_integer_multiplicity` (§3.4).

### 3.7 Isoperimetric Theorem 6.1 — `isoperimetric_theorem` (L67200)

**Claim.** For `n = m + 2 ≥ 2` and `ℓ ≥ 1` there is `c` such that every integer multiplicity
`T ∈ 𝒟_{m+1}(ℝ^{m+2+ℓ})` with compact support and `∂T = 0` is `T = ∂R` for an integer multiplicity
`R ∈ 𝒟_{m+2}(ℝ^{m+2+ℓ})` with compact support and `M(R)^{(m+1)/(m+2)} ≤ c M(T)`.

**Proof** (the printed proof, p. 169). Apply §3.6 with `(m, ℓ + 1)`: its ambient space
`ℝ^{(m+1)+(ℓ+1)}` is `ℝ^{m+2+ℓ}`. Let `C` be its constant and put `c = 2(C + 1)`.

1. `M(T) < ∞` (`isoperimetric_mass_lt_top`: a bump equal to `1` near the compact `spt T` and the
   covector bound `isoperimetric_abs_covector_apply_le`), and `M(∂T) = 0` because `∂T = 0`
   (`isoperimetric_mass_eq_zero_iff`).
2. *Key step.* Let `ρ > 0` with `C M(T) < ρ^{m+1}`. The Deformation Theorem at scale `ρ` gives
   `T − P_c = ∂R + S` with integer `β_F`.
   - For every face `F`, `|β_F| ρ^{m+1} ≤ M(P_c)` (`isoperimetric_lattice_chain_mass_ge`, printed (1):
     test `P_c` with a form that isolates `F`, `isoperimetric_lattice_face_isolating_form`).
     As `M(P_c) ≤ C M(T) < ρ^{m+1}`, the integer `β_F` has `|β_F| < 1`, so `β_F = 0` and `P_c = 0`.
   - `M(S) ≤ C ρ M(∂T) = 0`, so `S = 0` (`isoperimetric_mass_eq_zero_iff`).
   - Hence `T = ∂R`, `R` is integer multiplicity, `M(R) ≤ C ρ M(T)`, and `spt R` is closed and lies
     in the bounded `2√(m+2+ℓ) ρ`-neighbourhood of the compact `spt T`, so it is compact.
3. If `M(T) = 0`, apply step 2 with `ρ = 1`: `M(R) ≤ C M(T) = 0`, so `M(R)^{(m+1)/(m+2)} = 0`.
4. If `0 < M(T) < ∞`, take `ρ` with `ρ^{m+1} = 2(C + 1) M(T)`. Then `C M(T) < ρ^{m+1}`, and
   `M(R) ≤ C ρ M(T) ≤ ρ (C + 1) M(T) ≤ ρ^{m+2}`, so
   `M(R)^{(m+1)/(m+2)} ≤ ρ^{m+1} = 2(C + 1) M(T)`. ∎

*Uses:* `deformation_theorem` (§3.6).

### 3.8 Weak Polyhedral Approximation 6.2 — `polyhedral_approximation` (L67293)

**Claim.** Let `U ⊆ ℝ^{m+1+ℓ}` be open (`ℓ ≥ 1`) and `T ∈ 𝒟_{m+1}(U)` integer multiplicity with
`M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U`. Then there are scales `ρ_k ↓ 0` and integer lattice chains
`P_k = ∑_{F ∈ 𝓛_{m+1}(ρ_k)} β^{(k)}_F [[F]]` with `P_k ⇀ T` in `U`.

**Proof.**

1. *Truncations* (`polyhedral_approx_truncation_seq`, the printed second paragraph; it takes the
   Slicing Theorem as a hypothesis). There are integer multiplicity `X_k ∈ 𝒟_{m+1}(ℝ^{m+1+ℓ})` with
   `M(X_k) + M(∂X_k) < ∞` that agree with `T` on each test form of `U` for all large `k`.
   - Take the 1-Lipschitz exhaustion function `φ` of `U` (`polyhedral_approx_exhaustion_function`):
     its superlevel sets `{φ ≥ t}`, `t > 0`, are compact subsets of `U`.
   - With `W_k = {φ > 1/(2(k+2))} ⊂⊂ U`, the slicing mass bound (4.10) for `−φ` picks levels
     `λ_k ∈ (1/(k+2), 1/(k+1))` with `M_{W_k}(⟨T, −φ, −λ_k⟩) < ∞`.
   - `X_k = τ(M ∩ {φ > λ_k}, θ, ξ)` is the book's `T ⌞ {φ > λ_k}` (`polyhedral_approx_open_truncation`,
     `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`). By (4.6) and a
     cut-off (`polyhedral_approx_boundary_mass_cutoff`),
     `M(∂X_k) ≤ M_{W_k}(⟨T, −φ, −λ_k⟩) + M_{W_k}((∂T) ⌞ {φ > λ_k}) < ∞`.
2. *Lattice chains* (`polyhedral_approx_finite_mass_seq`, the printed first paragraph; it takes the
   Deformation Theorem as a hypothesis). Choose `ρ_k ↓ 0` with
   `ρ_k (M(X_k) + M(∂X_k)) ≤ 1/(k+1)` (`polyhedral_approx_scale_seq`). 5.3 at scale `ρ_k` gives
   `X_k − Pc_k = ∂R_k + S_k` with integer coefficients and `M(R_k), M(S_k) → 0`, hence
   `Pc_k(ω) − X_k(ω) = −(R_k(dω) + S_k(ω)) → 0` (`polyhedral_approx_flat_seq_tendsto`).
3. `P_k` is `Pc_k` restricted to `U`, with the same coefficients. For each test form `ω` of `U`,
   `P_k(ω) = (Pc_k(ω) − X_k(ω)) + T(ω)` for all large `k`, which tends to `T(ω)`. ∎

*Uses:* `slicing_theorem` (§3.5) and `deformation_theorem` (§3.6).

### 3.9 Theorem 8.2 (integrality of weak limits) — `integrality_of_weak_limits` (L68796)

**Claim.** Let `U ⊆ ℝ^P` be open, `T_j, T ∈ 𝒟_{m+1}(U)`, each `T_j` an integral current (`T_j` and
`∂T_j` integer multiplicity), `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`, and
`T_j ⇀ T`. Then `T` is integer multiplicity.

**Proof.** Two trivial facts are used: a current that kills every test form is `τ(∅, 1, 0)`, hence
integer multiplicity; and the zero current has zero mass.

*Induction on `m`, for all `U` at once.* In degree `m + 1` the proof uses the *boundary-limit
hypothesis* (BLI): if `Y_j, Y ∈ 𝒟_{m+1}(ℝ^P)`, every `∂Y_j` is integer multiplicity,
`sup_j M(∂Y_j) < ∞` and `∂Y_j ⇀ ∂Y`, then `∂Y` is integer multiplicity.

- For `m = 0`, (BLI) is the zero-dimensional case `iwl_zero_dim_integrality` (8.2 for `n = 0`,
  "trivial" in the book). Each integer multiplicity `0`-current is a locally finite integer Dirac sum
  (`br_zd_im_dirac_repr`), whose total weight on a small ball is bounded by the mass
  (`br_zd_dirac_massOn_ge`). Finite configurations of bounded size converge after extraction, so
  the limit is a finite integer Dirac sum near each point (`br_zd_dirac_local_limit`), which is
  integer multiplicity (`br_zd_finite_dirac_im`); `iwl_im_patching` globalizes.
- For `m + 1`, (BLI) is the induction hypothesis in degree `m + 1` applied to the currents `∂Y_j`:
  they are integral since `∂∂Y_j = 0` (SimonGMT's `GeometricCurrentOn.boundary_boundary`), and
  `M(∂∂Y_j) = 0`.

*The step: degree `m + 1` given (BLI).* Compare `P` with `m + 1`.

1. `P < m + 1`: any `m + 1` vectors of `ℝ^P` are linearly dependent, so every `(m+1)`-covector,
   every test form and `T` vanish; `T = τ(∅, 1, 0)`.
2. `P = m + 1`: Remark 3.12, `iwl_top_dim_integrality`. This is the BV compactness argument, proved
   in full; it uses only that the `T_j` are integer multiplicity and the two mass bounds:
   - every `T_j` has a Borel integer-valued locally integrable density `β_j`,
     `T_j(ω) = ∫ β_j ω(e) dLⁿ`;
   - the translation estimate (Remark 2.35) bounds `∫_K |β_j(x + z) − β_j(x)| dx` by a constant
     multiple of `|z| M_V(∂T_j)` for small `z` (`K` compact, `V` a neighbourhood of `K`);
   - mollification turns weak convergence into an `L¹_loc` Cauchy property of `(β_j)`;
   - a subsequence converges a.e. and in `L¹_loc` to an integer-valued `β` (integer-valued
     sequences converging a.e. are eventually constant a.e.);
   - `T(ω) = ∫ β ω(e)`, and by Lebesgue points and `iwl_weighted_tangent_locality`,
     `T = τ({β ≠ 0}, |β|, sign(β) e₁ ∧ ⋯ ∧ eₙ)`.
3. `P ≥ m + 2`:
   - *Localization, Remark 8.3(1)* (`iwl_localization`, with the Slicing Theorem): 8.2 on `U`
     follows from its case for currents in `ℝ^P` supported in a fixed compact set. Near each
     `ξ₀ ∈ U`: slice the `T_j` by `|x − ξ₀|`; choose a radius `r` (Fatou and Helly selection,
     `iwl_restriction_weak_limit`) with integer multiplicity slices of bounded mass along a
     subsequence on which `T_j ⌞ B_r(ξ₀) ⇀ T ⌞ B_r(ξ₀)`; extend to `ℝ^P` by a cut-off, apply the
     compact case, restrict back (`iwl_im_closure`), and patch the local representations
     (`iwl_im_patching`).
   - *Reduction to cycles* (`iwl_cycle_reduction`, with Lemma 3.9 and (BLI)). With all supports in
     `B̄_R(0)`, `∂T` is integer multiplicity by (BLI). The cones `C_j = 0 ⨯ ∂T_j`, `C = 0 ⨯ ∂T`
     (`iwl_cr_cone_exists`, the radial operator `ψ(x)(v) = ∫₀¹ t^m ω(tx)(x, v) dt`) satisfy
     `∂C_j = ∂T_j` (`iwl_cr_cone_boundary`, radial homotopy formula),
     `M(C_j) ≤ c R M(∂T_j)` and `C_j ⇀ C` (`iwl_cr_cone_estimates`). They are integer multiplicity
     (`iwl_cr_cone_integer_multiplicity`: the cone is the push-forward of `[[(0,1)]] × X` by
     `h(y) = y₀ π(y)`; the product is integer multiplicity by the Hausdorff product formula,
     `iwl_cr_interval_product_im`, and the push-forward by `iwl_smooth_pushforward`, which
     identifies Lemma 3.9's push-forward with the smooth one of 2.23). So `T′_j = T_j − C_j` are
     integer multiplicity cycles in `B̄_R(0)` with `T′_j ⇀ T − C`; the cycle case makes `T − C`
     integer multiplicity, and so is `T = (T − C) + C` (`iwl_im_closure`, integer combinations).
   - *The cycle case.* Let `T_j` be integer multiplicity cycles, supported in a compact set, with
     `sup_j M(T_j) < ∞` and `T_j ⇀ T`. Then `∂T = 0` (limits of boundaries) and
     `M_W(T) ≤ liminf_j M_W(T_j) < ∞` (SimonGMT's `WeaklyConvergesOn.massOn_le_liminf`, Simon 2.14).
     - *Positive density* (`iwl_positive_density`, printed (1)–(6), with the Slicing Theorem, the
       Isoperimetric Theorem, Lemma 3.9 and (BLI)): `Θ*^{m+1}(μ_T, x) > 0` for `μ_T`-a.e. `x`.
       `∂(T ⌞ B_r(x))` is integer multiplicity for a.e. `r`. If `μ_T(B_δ(x))` is small, a good
       radius `r < δ` has `M(∂(T ⌞ B_r(x))) ≤ κ μ_T(B_r(x))^{m/(m+1)}` (otherwise the integrated
       slicing inequality makes `μ_T(B_r(x))^{1/(m+1)}` grow linearly, a contradiction). The
       isoperimetric filling of `∂(T ⌞ B_r(x))`, compressed into `B_{3r}(x)` by a smooth push-forward,
       has mass `≤ μ_T(B_r(x))/2` (for `m = 0` the boundary has mass `< 1` and vanishes). A
       Besicovitch disjoint-ball argument with the cone estimate and lower semicontinuity of mass
       then forces `μ_T{Θ* < ε₀} = 0`.
     - So 8.1 (`rectifiability_theorem`, §3.3) makes `T` rectifiable.
     - *Integer density* (`iwl_integer_density`, printed (7)–(10)): writing `T = τ(M, θ, ξ)`, for
       `Hⁿ`-a.e. `x ∈ M`, after a subsequence, `M_{B_r(x)}(T_j) ≤ C rⁿ` for small `r` and large `j`
       (`ind_mass_density_bound`), and the blow-ups of `T` at `x` converge to
       `θ(x) ∫_{TₓM} ⟨·, ξ(x)⟩ dHⁿ` (`ind_ae_blowup_limit`). A diagonal sequence of rescalings
       `(η_{x,λ_k})_# T_{j(k)}` (`ind_rescaled_current`, `ind_diagonal_weak_limit`) consists of
       integer multiplicity cycles of bounded mass in `B₂(0)` converging to `c [[span τ]]`,
       `c = ±θ(x)`. The planar case `ind_plane_multiplicity_integer` gives `c ∈ ℤ`: slicing by the
       distance to the plane localizes the cycles to a cylinder (`ind_pi_localized_cycles`), their
       push-forwards by the frame coordinates converge to `c [[B₁(0)]]` in `ℝ^{m+1}`
       (`ind_pi_projected_limit`), the top-dimensional case 2 above makes `c [[B₁(0)]]` integer
       multiplicity, and so `c ∈ ℤ` (`ind_const_multiple_integer`). Hence `θ(x) ∈ ℕ` a.e., and
       `T` is integer multiplicity (`ind_ae_integer_multiplicity`). ∎

*Uses:* `slicing_theorem` (§3.5), `lipschitz_pushforward_integer_multiplicity` (§3.4),
`rectifiability_theorem` (§3.3) and `isoperimetric_theorem` (§3.7), hence transitively also
`deformation_theorem`. It does not use 3.11, 6.3 or 7.2.

### 3.10 Boundary Rectifiability Theorem 6.3 — `boundary_rectifiability` (L68901)

**Claim.** If `T ∈ 𝒟_{m+1}(U)` is integer multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U`, then
`∂T` is integer multiplicity.

**Proof.**

1. Integer multiplicity is local (`br_isIntegerMultiplicity_of_local`): it suffices that every
   `x₀ ∈ U` has an open `V ∋ x₀` on which `∂T` agrees with an integer multiplicity current. (Countably
   many such `V_i` cover `U`; the local triples agree a.e. on overlaps, `ltg_tau_unique_on_open`, and
   glue, `ltg_glue_triples`; `ltg_tau_local_to_global` concludes with a partition of unity.)
2. *Localization by slicing* (`br_local_finite_mass_extension`, with the Slicing Theorem). There are
   `r > 0` with `B_r(x₀) ⊆ U` and an integer multiplicity `X ∈ 𝒟_{m+1}(ℝ^P)` with `M(X) < ∞`,
   `M(∂X) < ∞` and `X = T` on forms supported in `B_r(x₀)`; namely `X = τ(M ∩ B_r(x₀), θ, ξ)` for
   `T = τ(M, θ, ξ)`. `T` is represented by `(Hⁿ ⌞ M, θ ξ)`, so it has locally finite mass, and
   `M_W(∂T) < ∞` by hypothesis; so the Slicing Theorem applies. With `f = |· − x₀|`,
   `W = B_{2r₀}(x₀) ⊂⊂ U` and `R = T ⌞ {r₀/2 < f < r₀}`, 4.10 gives
   `∫_{r₀/2}^{r₀} M_W(⟨T, f, t⟩) dt ≤ M_W(R) < ∞`; fix `r ∈ (r₀/2, r₀)` with
   `M_W(⟨T, f, r⟩) < ∞`. By uniqueness of restrictions, the restriction `T ⌞ B_r(x₀)` (a current
   in `U`) agrees with `X` on every test form of `U`, so `∂X = ⟨T, f, r⟩ + (∂T) ⌞ B_r(x₀)` on forms
   supported in `W`, and the cut-off lemma
   (`polyhedral_approx_boundary_mass_cutoff`) gives `M(∂X) ≤ M_W(⟨T, f, r⟩) + M_W(∂T) < ∞`.
3. *The finite-mass case in `ℝ^P`* (`br_boundary_isIntegerMultiplicity_of_finite_mass`, with the
   Deformation Theorem and 8.2 as hypotheses; proof of 6.3 and Remark 6.4).
   - Integer lattice chains `P_k ⇀ X` with `sup_k M(∂P_k) < ∞` exist (`br_lattice_approximation`).
     For `P < m + 1`, `X = 0`. For `P = m + 1`, `br_top_dim_lattice_approximation` uses integer
     medians on cubes, a translation estimate and Stokes on lattice cubes. For `P ≥ m + 2`, use 5.3
     at scales `1/(k+1)`.
   - Each `∂P_k` is an integer lattice chain, hence integer multiplicity (Stokes on each face,
     `br_lattice_face_stokes`, and regrouping, `br_lattice_chain_boundary_isIntegerMultiplicity`),
     and a cycle.
   - `∂P_k ⇀ ∂X` with bounded masses, so `∂X` is integer multiplicity: for `m = 0` by the
     zero-dimensional case (`br_zero_dim_weak_limit_isIntegerMultiplicity`), for `m ≥ 1` by 8.2
     applied to the integral currents `∂P_k` (their boundaries vanish). Only this zero-boundary use
     of 8.2 occurs; this is the content of the book's Remark 6.4.
4. Restrict `∂X` to `U` (`br_restrictDomain_isIntegerMultiplicity`). For `ω` supported in
   `B_r(x₀)`, also `spt dω ⊆ B_r(x₀)`, so `∂T(ω) = T(dω) = X(dω) = ∂X(ω)`. ∎

*Uses:* `slicing_theorem` (§3.5), `deformation_theorem` (§3.6) and `integrality_of_weak_limits`
(§3.9).

### 3.11 Theorem 7.2 (flat versus weak convergence) — `flat_convergence_iff_weak_convergence` (L69448)

**Claim.** Let `T, T_j ∈ 𝒟_{m+1}(U)` be integer multiplicity with
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`. Then `T_j ⇀ T` iff `d_W(T_j, T) → 0` for
every `W ⊂⊂ U`.

**Proof.**

- *"If"* (`fiw_flat_to_weak`). For `ω`, take `W ⊂⊂ U` containing `spt ω ⊇ spt dω`. A decomposition
  `T_j − T = ∂R + S` with `M_W(S) + M_W(R) < δ` gives
  `|T_j(ω) − T(ω)| = |R(dω) + S(ω)| ≤ δ (sup |dω| + sup |ω|)`.
- *"Only if".* Fix `W ⊂⊂ U`. By the subsequence principle it suffices that every subsequence
  `T_{ns(j)}` has a further subsequence along which `d_W(·, T) → 0`.
  1. *Localization, printed (4)* (`fiw_localization`, with the Slicing Theorem and 6.3). After a
     subsequence `ψ`, cutting along a good level `{φ = s}` of `φ = δ − dist(·, closure W)` gives
     integer multiplicity `T′_j = T_{ns(ψ(j))} ⌞ {φ ≥ s}` and `T′ = T ⌞ {φ ≥ s}`, with
     `∂T′_j` integer multiplicity by 6.3, all supported in a fixed compact `K ⊆ U`, with
     `M(T′_j) + M(∂T′_j) ≤ B < ∞` and `T′_j ⇀ T′`. Every decomposition `T′_j − T′ = ∂R + S` with
     integer multiplicity `R, S` gives `d_W(T_{ns(ψ(j))}, T) ≤ M_W(S) + M_W(R)`. (The good level
     comes from Helly selection and Fatou applied to the slice masses. The restrictions are integer
     multiplicity by the restriction calculus and tangent locality, `fiw_tangent_locality`; integer
     combinations, such as the remainder `Ŝ` of the transferred decomposition
     `T_{ns(ψ(j))} − T = ∂R + Ŝ`, are integer multiplicity by `fiw_im_lincomb`.)
  2. *Total boundedness, printed (1)–(3)* (`fiw_total_boundedness`, with the Deformation Theorem).
     For every `ε > 0`, every infinite `J ⊆ ℕ` contains an infinite `J′` such that
     `T′_i − T′_j = ∂R + S` with integer multiplicity `R, S` and `M(R) + M(S) < ε` for
     `i, j ∈ J′`. The finite flat net `fiw_tb_finite_net` approximates every `T′_j`, up to
     `∂R + S` with `M(R) + M(S) ≤ C ρ B`, by one of finitely many centres. For `P < m + 1` all these
     currents vanish. Otherwise each `T′_j` is extended to `ℝ^P` (`fiw_tb_extend_to_univ`) and
     approximated by a lattice chain, by 5.3 for `P ≥ m + 2` and by `fiw_tb_top_dim_approx`
     (integer medians and a translation estimate) for `P = m + 1`; the restrictions to `U` of these
     chains are the centres, and their integer coefficients range over a finite set
     (`fiw_tb_lattice_chain_coeff`, `fiw_tb_lattice_coeff_finite`). Then choose `ρ` with
     `2 C ρ B < ε`, apply the pigeonhole principle, and subtract two decompositions
     (`fiw_tb_flat_sub`).
  3. *Cauchy limit, printed (5)* (`fiw_flat_cauchy_limit`). A nested diagonal subsequence `φ` gives
     `T′_{φ(r)} − T′_{φ(r+1)} = ∂R_r + S_r` with integer multiplicity `R_r, S_r` and
     `M(R_r) + M(S_r) ≤ 2^{−r}` (`fiw_fcl_nested_subseq`). The integer series
     `∑_k R_{ℓ+k}`, `∑_k S_{ℓ+k}` are integer multiplicity (`fiw_im_series`, Lemma 3.13), and
     telescoping with `T′_j ⇀ T′` gives `T′_{φ(ℓ)} − T′ = ∂R + S` with
     `M(R) + M(S) ≤ 2 · 2^{−ℓ}`.
  4. Hence `d_W(T_{ns(ψ(φ(ℓ)))}, T) ≤ M_W(S) + M_W(R) ≤ M(R) + M(S) ≤ 2 · 2^{−ℓ} → 0`. ∎

*Uses:* `slicing_theorem` (§3.5), `deformation_theorem` (§3.6) and `boundary_rectifiability`
(§3.10).

### 3.12 Federer–Fleming Compactness 3.11 — `federer_fleming_compactness` (L69482)

**Claim.** If `T_j ∈ 𝒟_{m+1}(U)` are integer multiplicity and
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`, then some subsequence converges weakly to an
integer multiplicity `T₀`.

**Proof** (Remark 8.3(2), p. 176).

1. 2.15 (§3.1), with `M_W(T_j) ≤ M_W(T_j) + M_W(∂T_j)`, gives `φ` and `T₀` with `T_{φ(j)} ⇀ T₀`.
2. 6.3 (§3.10), with `M_W(∂T_j) ≤ sup_j (M_W(T_j) + M_W(∂T_j))`, makes every `∂T_j` integer
   multiplicity, so every `T_j` is an integral current.
3. 8.2 (§3.9) for `T_{φ(j)}`, whose mass bounds are dominated by those of the whole sequence, shows
   that `T₀` is integer multiplicity. ∎

*Uses:* `compactness_under_mass_bounds` (§3.1), `boundary_rectifiability` (§3.10) and
`integrality_of_weak_limits` (§3.9).

## 4. Dependency structure and absence of circularity

**Actual Lean usage among the twelve root children.** The table is extracted from the proof bodies
of `Submission.lean` (every `Submission.*` name occurring outside comments). "Directly" means the
child's own proof names the sibling; "transitively" follows the references of all accepted
descendants.

| Root child | Siblings used directly | Siblings used transitively |
| --- | --- | --- |
| `compactness_under_mass_bounds` | — | — |
| `constancy_theorem` | — | — |
| `rectifiability_theorem` | — | — |
| `lipschitz_pushforward_integer_multiplicity` | — | — |
| `slicing_theorem` | — | — |
| `deformation_theorem` | slicing, Lipschitz push-forward | the same |
| `isoperimetric_theorem` | deformation | + slicing, Lipschitz push-forward |
| `polyhedral_approximation` | slicing, deformation | + Lipschitz push-forward |
| `integrality_of_weak_limits` | slicing, Lipschitz push-forward, rectifiability, isoperimetric | + deformation |
| `boundary_rectifiability` | slicing, deformation, integrality | + Lipschitz push-forward, isoperimetric, rectifiability |
| `flat_convergence_iff_weak_convergence` | slicing, boundary rectifiability, deformation | + Lipschitz push-forward, isoperimetric, rectifiability, integrality |
| `federer_fleming_compactness` | compactness, boundary rectifiability, integrality | + slicing, Lipschitz push-forward, deformation, isoperimetric, rectifiability |

These are exactly the sibling dependencies declared by the accepted decomposition
(`nodes/root/decomposition-v3.json`), so no sibling is used without having been declared:
deformation ← {slicing, Lipschitz push-forward}; isoperimetric ← {deformation}; polyhedral
approximation ← {deformation, slicing}; integrality ← {rectifiability, isoperimetric, slicing,
Lipschitz push-forward}; boundary rectifiability ← {deformation, slicing, integrality}; flat ⇔ weak
← {deformation, slicing, boundary rectifiability}; Federer–Fleming ← {compactness, boundary
rectifiability, integrality}.

**No circularity.**

- Lean elaborates the top-level declarations of `Submission.lean` in order, and a declaration can
  only mention declarations that precede it. The file has no `mutual` block, `partial` definition
  or `axiom`. A scan of all 692 proof bodies (the 691 children and `main_theorem`) finds no
  reference to a later declaration. So the usage relation is a well-founded DAG, and the file order
  is a topological order. The root children appear in this order: `constancy_theorem` (L42133),
  `lipschitz_pushforward_integer_multiplicity` (L46209),
  `rectifiability_theorem` (L62437), `slicing_theorem` (L66972),
  `deformation_theorem` (L66990), `isoperimetric_theorem` (L67200),
  `polyhedral_approximation` (L67293), `integrality_of_weak_limits` (L68796),
  `boundary_rectifiability` (L68901), `compactness_under_mass_bounds` (L69081),
  `flat_convergence_iff_weak_convergence` (L69448),
  `federer_fleming_compactness` (L69482), and `main_theorem` (L69498).
- Mathematically, the order is: 2.15, 2.34, 8.1, 3.9 and 4.4–4.10 from first principles (with
  Mathlib and SimonGMT); then 5.3 from §4 and 3.9; 6.1 from 5.3; 6.2 from 5.3 and §4; 8.2 from 8.1, 6.1, §4 and
  3.9; 6.3 from 5.3, §4 and 8.2; 7.2 from 5.3, §4 and 6.3; and 3.11 from 2.15, 6.3 and 8.2. In
  particular 8.2 does not use 3.11, 6.3 or 7.2, and 6.3 uses 8.2 only for cycles (the book's
  Remarks 6.4 and 8.3(2)).
- Several hypotheses of intermediate lemmas are full conjuncts (`SlicingTheorem`,
  `LipschitzPushforwardIntegerMultiplicity`, `DeformationTheorem`, `IntegralityOfWeakLimits`,
  `IsoperimetricTheorem`, `BoundaryRectifiability`). Each such lemma is applied to the
  corresponding root child, which precedes it in the file. For example, `deformation_onto_skeleton`
  is applied to `slicing_theorem` and `lipschitz_pushforward_integer_multiplicity`, and
  `br_boundary_isIntegerMultiplicity_of_finite_mass` to `deformation_theorem` and
  `integrality_of_weak_limits`.
- The libraries (Mathlib, `simongmt`) are upstream packages pinned before this problem existed, and
  cannot refer to any `GMT.Ch06` declaration.

**Size.** The longest chain of `Submission.*` references starting at `main_theorem` has 18
declarations. 688 of the 691 accepted declarations are reachable from `main_theorem`.

## 5. Library reuse and provenance

All library declarations below are **existing pinned upstream declarations, reused, not new
helpers**. They enter only through their kernel-checked statements. The root comparator rebuilds
the candidate, exports `GMT.Ch06.main_theorem` with its whole dependency closure (which contains
every Mathlib and SimonGMT declaration used), re-checks the closure with Lean's kernel and allows
only the axioms `propext`, `Quot.sound` and `Classical.choice` (§9). So their reuse is verified in
this run, not trusted.

**Mathlib** (`25730c7c759d108ef87ab70af2342a196760f79d`, the revision of `lake-manifest.json`; the
local snapshot's `mathlib` checkout is at the same commit). Standard measure theory, analysis and
linear algebra are used throughout. The results named in §3 are:

| Declaration | File (snapshot, line) | Use |
| --- | --- | --- |
| `RealRMK.rieszMeasure`, `RealRMK.integral_rieszMeasure` | `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean:65`, `:345` | Riesz step of `slicing_mass_representation` (§3.0 (R)) |
| `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` | `Mathlib/MeasureTheory/Covering/Differentiation.lean:818` | Lebesgue points along closed balls (`iwl_top_dim_integrality`, `fiw_tl_ald_ld_weighted_lebesgue_point`, `ind_ab_weighted_lebesgue_point`, `iwl_imc_normalized_lebesgue_points`) |
| `Besicovitch.vitaliFamily`, `Besicovitch.ae_tendsto_measure_inter_div` | `Mathlib/MeasureTheory/Covering/Besicovitch.lean:1021`, `:1105` | Besicovitch differentiation along closed balls (the Lebesgue-point lemmas of the previous row, and `rectifiability_orientation`, `rectifiability_mickle_rado_density_zero`, `fiw_tl_ald_ld_weighted_density_point`) |
| `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` | `Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:205` | fundamental lemma of the calculus of variations (`ltg_tau_unique_on_open`, `lpf_rsn_weighted_fundamental_lemma`, `iwl_im_patching`, `ind_pi_ss_cycle_slice_boundary` and others) |
| `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` | `Mathlib/MeasureTheory/Function/Jacobian.lean:255` | almost-linear Borel pieces of Lipschitz maps (`lpf_countably_rectifiable_c1_cover`, `rectifiability_weighted_tangent_ae`, `iwl_cr_hp_injective_pieces` and others) |
| `LipschitzWith.ae_differentiableAt` | `Mathlib/Analysis/Calculus/Rademacher.lean:385` | Rademacher's theorem |

**SimonGMT** (`simongmt` package, `2b3663083f3fe399b6296fb8eaee52169170e197`, the
`simongmt-library` branch of `ZhengyangZhang06/gmt-formalize`; an earlier kernel-checked partial
formalization of the same book, whose reuse the task allows).

- *Definitions.* The contract itself imports SimonGMT and uses its definitions, all checked against
  the book in `GMT/Ch06/README.md`: `TestFormOn`, `GeometricCurrentOn`, `boundary`, `massOn`,
  `mass`, `support`, `WeaklyConvergesOn`, `NVector`, `simpleNVector`, `nVectorPushforward`,
  `SimonMultiIndex`, `Covector`, `DifferentialForm`, `Chapter03.CountablyRectifiable`,
  `Chapter03.HasWeightedApproximateTangentSpaceAt` and `Chapter01.dimensionalUpperDensity`.
- *Theorems.*
  The child proofs use 164 distinct SimonGMT constants (definitions and theorems) from 26 modules
  directly, each by name; Appendix B lists them, with the declarations that use each theorem, as
  read from the compiled environment (§9).
  The ones named in §3 are:

| Declaration (namespace `Poincare.SimonGMT.`) | File (package, line) | Use |
| --- | --- | --- |
| `Chapter06.GeometricCurrentOn.boundary_boundary` | `Chapter06/Currents.lean:365` | `∂∂ = 0` (§3.9) |
| `Chapter06.WeaklyConvergesOn.massOn_le_liminf` | `Chapter06/Mass.lean:100` | lower semicontinuity of mass, 2.14 (§3.1, §3.9) |
| `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` | `Chapter03/Rectifiable.lean:514` | Ch. 3, Lemma 3.2 (§3.3) |
| `Chapter01.simon_theorem_4_14_caratheodory` | `Chapter01/RadonPolarRepresentation.lean:150` | vector Riesz representation, Ch. 1, 4.14, in `rectifiability_mass_measure_representation` (§3.0 (R)) |
| `Chapter01.simon_theorem_4_14_positive_envelope`, `Chapter01.vectorFunctionalEnvelopeMeasure` | `Chapter01/VectorFunctionalEnvelope.lean:280`, `:270` | the envelope identity `μ(W) = M_W(T)`, in `rectifiability_mass_measure_representation` and `iwl_restriction_theory` (§3.0 (R)) |
| `Chapter01.simon_theorem_4_14_l1_extension`, `Chapter01.compactL1DualField` | `Chapter01/VectorFunctionalL1.lean:147`, `Chapter01/RadonLocalDualField.lean:33` | the `L¹` extension and local dual fields of the proof of 4.14, in `iwl_restriction_theory` (§3.0 (R)) |
| `Chapter02.weighted_area_formula_lipschitzOn_fiberSum` | `Chapter02/AreaDomain.lean:106` | area formula for maps Lipschitz on a set, in `lpf_raf_local_lipschitz_area` and `lpf_wtc_chart_area_formula` (§3.0 (G), §3.4) |
| `Chapter02.area_image_compl_regularSet_eq_zero` | `Chapter02/AreaLipschitz.lean:59` | null image of the critical set, in `rectifiability_weighted_tangent_ae` (§3.3) |
| `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn` | `Chapter02/Lipschitz.lean:216` | `Hᵐ` of Lipschitz images, e.g. in `iwl_cr_hp_injective_pieces` |

- *Definitions marked as not to be used.* `GMT/Ch06/README.md` lists `Chapter06.MassRepresentation`,
  `IntegerRectifiableCurrentData`, the `Current`/`GeometricCurrent` algebraic API and
  `Chapter04.RectifiableVarifold` as not used. No constant of `MassRepresentation`, `IntegerRectifiableCurrentData`, the global
  `Current`/`GeometricCurrent` structures or any `Chapter04` module occurs among the 164 constants of
  Appendix B. The proofs do use `Chapter06.CurrentOn U n`, which is by definition the space
  `TestFormOn U n →ₗ[ℝ] ℝ` of linear functionals underlying `GeometricCurrentOn` (its field
  `toCurrent`), to form linear combinations of currents such as `S₁ + S′` in `deformation_theorem`.

## 6. Historical decomposition versus the lemmas actually used

**The DAG.** The accepted root decomposition (`nodes/root/decomposition-v3.json`, committed as
`.humanize-workspace/20261011t144224z-6e4735dbca/root/decomposition.json`) dispatched the twelve
children of §2 with the sibling dependencies listed in §4. Recursive decompositions of the children
produced 679 further accepted nodes, 691 in all; 122 of them were reused by more than one parent
(their DAG node appears in several `children` lists). Every accepted node is present in
`Submission.lean` under its frozen name and type (§9).

**Accepted but unused (3 nodes).** The formal proof does not need these three declarations. Each is
kept unchanged, so that its accepted interface is preserved. In each case the planned use was
discharged by an equivalent accepted declaration or by an inline step:

| Declaration (line) | DAG node; issue; PR | Planned use | What the Lean proof does instead |
| --- | --- | --- | --- |
| `dph_hausdorff_product_formula` (L28324) | `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1`; issue #5270; PR #5552 | `dph_interval_product_im` (product `[[0,1]] × X` of an integer multiplicity current in the deformation subtree) | `dph_interval_product_im` calls `iwl_cr_interval_product_im`, which uses the same product formula in its integrality-subtree version `iwl_cr_hausdorff_product_formula` |
| `iwl_imc_restriction_im` (L38058) | `root.integrality_weak_limits-a1.im_closure-a1.restriction_im-a1`; issue #2825; PR #3911 | part (b) of `iwl_im_closure` (restrictions of integer multiplicity currents) | `iwl_im_closure` proves part (b) inline, from uniqueness of the representation and the tangent comparison `iwl_imc_tangent_overlap` |
| `fiw_tl_ald_closedBall_lebesgue_point` (L64049) | `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.closed_ball_lebesgue_point-a1`; issue #3185; PR #3625 | `fiw_tl_ald_local_differentiation` (Lebesgue points along closed balls) | `fiw_tl_ald_local_differentiation` uses `fiw_tl_ald_ld_weighted_lebesgue_point`, which applies Mathlib's `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` for the Besicovitch Vitali family directly |

**Declared dependencies that a node's proof does not use.** Comparing every node's declared
`children` and `depends_on` with the references in its Lean proof:

- Most declared children that a node does not reference directly are used through a sibling. For
  example, `boundary_rectifiability` reaches `br_lattice_approximation` through
  `br_boundary_isIntegerMultiplicity_of_finite_mass`.
- 20 declared edges are not used even transitively by the declaring node. Five of them point to
  the three unused nodes above. The other 15 point to declarations that are used elsewhere: the
  declaring proof found a shorter route (for instance `deformation_skeleton_polyhedral` proves its
  auxiliary facts as local steps) or used another accepted lemma with the same content (for
  instance `deformation_pushforward_homotopy` obtains the product formula through
  `iwl_cr_interval_product_im` and the support fact through `iwl_sp_rectifiable_support_null`,
  instead of the declared `dph_hausdorff_product_formula`, `lpf_raf_local_lipschitz_area` and
  `lpf_rectifiable_support_null`).
- Conversely, two proofs reference accepted declarations that their decomposition had not listed:
  `iwl_localization` uses `br_weightedTangent_congr` and `cmb_abs_apply_le_of_massOn_le`, and
  `iwl_positive_density` uses `cmb_covector_eq_sum_coord_smul_wedge`,
  `cmb_exists_compactly_contained_exhaustion`, `slicing_ru_continuous_to_bounded` and
  `slicing_ru_smooth_to_continuous`. All six are accepted nodes that precede their users in the
  file, so these references create no new obligation.

**Results the plan cited and the Lean proof proves.** The root decomposition named four published
results to be cited rather than re-proved: the Besicovitch–Federer structure theorem, the area and
co-area formulas on rectifiable sets, BV compactness with Poincaré inequalities, and the vector
Riesz representation. In the final Lean proof:

- the structure theorem is proved (`rectifiability_structure_projection` and the
  `rectifiability_bf_*` and `rectifiability_mickle_rado*` declarations, §3.3);
- the area formula on rectifiable sets (`lpf_rectifiable_area_formula`) is derived from SimonGMT's
  area formula for maps Lipschitz on a set, and the co-area formula (`slicing_im_coarea`, with
  Eilenberg's inequality) is proved (§3.5);
- BV compactness in top dimension is proved inside `iwl_top_dim_integrality` (§3.9), and the
  Poincaré/trace estimates of 5.1 inside `deformation_skeleton_polyhedral` and
  `fiw_tb_top_dim_approx` (§3.6, §3.11);
- the vector Riesz representation is SimonGMT's kernel-checked proof of Ch. 1, 4.14
  (`simon_theorem_4_14_caratheodory`, `simon_theorem_4_14_positive_envelope`,
  `simon_theorem_4_14_l1_extension`, used by `rectifiability_mass_measure_representation` and
  `iwl_restriction_theory`), and the
  finite-dimensional-valued Riesz step of `slicing_mass_representation` uses Mathlib's
  Riesz–Markov–Kakutani theorem (§5).

So nothing is assumed beyond Mathlib and the pinned SimonGMT library.

**Gaps filled, arguments replaced and printed steps corrected by the accepted children** (no
frozen statement is changed):

- 2.34 uses `(L¹)* = L^∞` without proof; it is proved (§3.2).
- The BV argument of Remark 2.35 is replaced by the potential estimates of Gilbarg–Trudinger, §7.8
  (§3.3).
- In Remark 2.37(2) the projections `p_α ∘ Q` are meant, not `Q` (§3.3).
- In the proof of 5.1, the cylinder bound (5) is corrected (`dgc_cylinder_volume`). In the proof of
  Lemma 5.4, the printed "`|y − a| ≥ 3/4`" before (6) fails: for `a = (1/2, …, 1/2)` and small
  `δ > 0`, the point `x = (1/4, 1/2 + δ, …, 1/2 + δ)` has no coordinate in `a_i + ℤ`, so it lies off
  the dual skeleton, and its radial projection from `a` onto `∂[0, 1]^d` is
  `y = (0, 1/2 + 2δ, …, 1/2 + 2δ)`, with `|y − a| < 3/4`. Only `|y − a| > 1/4` holds, and the
  similarity estimate (4)–(7) is adjusted accordingly (`dr_cc_similarity_bound`).
- The ball volumes in the proof of 5.1 are bounded by the cube bound `Lᵏ(B̄_r) ≤ (2r)ᵏ`
  (`dgc_pm_ball_volume_le`). This is a simplification of the printed `ω_k rᵏ`, not a correction.

One more correction concerns the run's own work, not the book: the first, rejected root
decomposition claimed in the proof of 3.9 that different image sheets have density zero at each
other's points. That claim was false, and the accepted proof uses the common approximate tangent
plane instead (§3.4).

## 7. History (preserved, not rewritten)

The following records are left untouched under
`.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/`:

- `nodes/root/natural-proof-source.md`: the operator-supplied pointer to the published proof
  (`book/sources/chapter-06-source.txt`, sha256
  `ab79aa2a751c92977877c0d793ccd3dc6ead15420d7de71da57d35ac53b75047`).
- `nodes/root/plan-source.md`, `plan-draft-v1.md`, `plan-v1.md`: the plan scaffold.
- `nodes/root/decomposition-v1.json`, `-v2.json`, `-v3.json` with their audits and review receipts.
  - v1 was rejected for four gaps: the image-sheet density claim in 3.9 (step 5), the ambient mass
    measure of the slicing preliminaries, a domination step in the deformation proof (A3), and the
    case `P < m + 1` of 8.1.
  - v2 was rejected for one gap: the σ-finiteness of `Hᵏ⌞(M ∪ M′)` in deformation (A3) relied on an
    unsupported `θ′ ≥ 1`.
  - v3 was accepted.
- `nodes/*/parent-supplied-natural-proof.md` for every child: the reviewed natural-language proofs.
  Committed copies are under `.humanize-workspace/20261011t144224z-6e4735dbca/`.
- `nodes/root/speculative-prompt-v2.md` and `speculative-process-v2.log`: the speculative root draft,
  commit `405d3381` ("wip(speculative): draft root"). It replaced `by sorry` by the twelve-tuple of
  §2, which is unchanged since.
- `operator-repairs/`: records of operator repairs to *child* integration branches (an unclosed doc
  comment after a reconcile for issue 341; duplicate copies of `cmb_abs_apply_le_of_massOn_le` for
  issue 334; a declaration placed below its user for issue 338; imports placed after the module doc
  for issue 341; two workers stopped by a service removal). None of these records concerns the
  root.
- `nodes/root/comparison-identity-v1.json` and `lean-audit-v1.json`: the first root round. The
  overlay `dfdc020b` passed the exact comparator (evidence
  `cluster-state/verification/results/hoa39/20261014T165641Z-ch06-root-oypmaw0x/`). The Lean
  acceptance gate nevertheless failed, because no final root prose had been committed for
  independent review.
- `nodes/root/rlcr-plan-v1.md`: the plan of the second round. That round produced `e9e57ea4` (§8)
  and the first version of this file (commit `c3c9b342`). `comparison-identity-v2.json` and
  `lean-audit-v2.json` record that `c3c9b342` passed the exact comparator. The same holds for
  `comparator-v1.log`, which holds the controller's isolated comparator run on `c3c9b342`
  (evidence `20261014T195224Z-ch06-root-kexkmndq`). That run reused the
  verdict of the full run on `e9e57ea4` (§9).
- `nodes/root/publication-prose-audit-v1.json`: the independent review of that first version. It
  found no circularity in the dependency order. It withheld acceptance for two corrections in
  Appendix A: a wrong image-density formula and a wrong lemma number. The revision `e26e6909`
  made both corrections and seventeen further ones found by re-checking Appendix A (§8). The review
  record is left unchanged.
- `nodes/root/rlcr-plan-v2.md`: the plan of the third round, which produced `e26e6909`.
  `comparison-identity-v3.json` and `lean-audit-v3.json` record that `e26e6909` passed the exact
  comparator; `comparator-v2.log` holds the controller's isolated comparator run on `e26e6909`
  (evidence `20261014T205631Z-ch06-root-u8y3fc07`), which reused the verdict of the full run on
  `e9e57ea4` (§9). `isolated-comparator-result.json` is overwritten by each isolated run; when this
  revision was written it recorded the run on `e26e6909`.
- `nodes/root/publication-prose-audit-v2.json`: the independent review of `e26e6909`. It found the
  stated dependency graph acyclic, with the reported 688 reachable declarations, and withheld
  acceptance for two corrections in A.3: the claim in `rectifiability_structure_projection` that a
  possibly non-measurable `A` is, up to a null set, a countable union of compact pieces, and the
  example in the Correction line of `rectifiability_orientation`, which omitted a boundary term.
  This revision makes both corrections and the further ones of §8. The review record is left
  unchanged.
- `nodes/root/rlcr-plan-v3.md`: the plan of the present round, which revises this file.

**The overlay.** Starting from the frozen commit `d8d46c95`, the integration branch merged the
twelve children's accepted candidate commits, which already contain their accepted descendants:
`ec8c9ac4` (2.15), `b4bbd871` (2.34), `3289485c` (3.9), `f27fd6da` (slicing), `4efd922c` (5.3),
`2e7a66f2` (6.1), `786e6c8a` (6.2), `8f66d3bb` (6.3), `7c119a55` (7.2) and `5abeab04` (3.11). 8.1
(`ba8a5544`) and 8.2 (`036fb2d8`) arrive through the commits that depend on them. After these
merges came the controller's commits "Re-merge declarations line-merged from …" and "Drop
declarations repeated by merging accepted checkpoints", and finally the merge of the speculative
draft `405d3381`, giving `dfdc020b`.

## 8. Changes made in this candidate

**Lean: removal of a duplicated module docstring** (commit `e9e57ea4`). The integration commit
`43c463fd` ("Re-merge declarations line-merged from ba8a5544bc76", which re-merged the 8.1
candidate `ba8a5544`) had inserted a second copy of the contract's 20-line module docstring
`/-! … -/` after the imports. The overlay check that the controller asks for ("duplicated namespaces and repeated placeholder
scaffolds") flagged it. The commit deletes that copy together with one blank line before and after
it:

- It is a pure deletion of 22 lines (`git diff --stat`: `1 file changed, 22 deletions(-)`), and the
  two copies were byte-identical.
- Afterwards lines 16–367 of `Submission.lean` equal lines 9–360 of `Contract.lean` byte for byte,
  and the contract's header occurs exactly once.
- No declaration, statement, import or proof changed. A docstring does not affect elaboration.

**Prose.** This file was added in commit `c3c9b342`, revised in commit `e26e6909`, and is revised
again by the commit that records the present revision. None of these commits changes a `.lean`
file or a build input, so none changes the comparator's inputs (§9).

**Corrections after the first publication review.** The independent review of the first version
of this file (`nodes/root/publication-prose-audit-v1.json`) withheld acceptance for two corrections.
Both concern doc comments reproduced in Appendix A:

1. `lpf_pushforward_integrality` (A.4) printed the image density as the fibre sum
   `∑_{f(x) = y} θ(x) L_#ξ(x)`. The correct density is `∑ θ(x) ‖L_#ξ(x)‖⁻¹ L_#ξ(x)` over the
   preimages with `L_#ξ(x) ≠ 0`; §3.4 and the entry `lpf_pi_image_density` already had this form.
2. `rectifiability_bf_trichotomy` (A.3) cited Lemma 2.4 of Hovila–Järvenpää–Järvenpää–Ledrappier.
   The trichotomy is Lemma 2.5 of arXiv:1104.3453; 2.4 is the definition of transversality.

Following these two findings, all 691 entries of Appendix A were re-checked against the
declarations' doc comments and types in `Submission.lean`, against the book text
(`book/chapter-0*.txt`, with the printed page headers, and `book/simon-gmt.pdf`), and, where
available, against the cited papers. The re-check found seventeen further errors:

- **Mathematical error.** `rectifiability_orientation` (A.3) bounded `|∂T(η^#φ)|` by `O(rⁿ⁺¹)`
  instead of `O(r)`. The exponent `n + 1` belongs to the Lean proof's test forms `rⁿ η^#φ`.
- **Omitted hypothesis.** `br_weightedTangent_congr` (A.3) did not state the hypothesis
  `θ(x) = θ′(x)` of its Lean statement, and without it the claim is false.
- **Wrong locators into Simon's book:**
  - `lpf_raf_chart_preimage_null` and `lpf_raf_fiber_sum_glue` (A.4): the cited step is in the proof
    of Ch. 3, 2.4, not of 2.6.
  - `slicing_im_creg_local_to_global` (A.5): Lemma 4.1 is on p. 154, not p. 153.
  - `dph_smooth_homotopy` (A.6): `d f^# = f^# d` is (1.14), not (2.5).
  - `dph_lpfex_tendsto_of_index_maps` (A.6): the Lipschitz push-forward as a limit, with its Cauchy
    argument, is 2.29, not 3.6–3.9.
  - `isoperimetric_mass_eq_zero_iff` (A.7): the quoted sentence is not in the book, and the proof
    of 6.1 is on p. 169.
  - `iwl_restriction_weak_limit`, `iwl_rl_testForm_smooth_cutoff` and `ind_diagonal_weak_limit`
    (A.9): wrong pages, and cutoffs ascribed to the proof of 8.2 that it does not contain.
  - `iwl_sp_boundary_apply_eq_of_compatible` (A.9): 2.24(1) is on p. 139.
  - `ind_top_dim_integer_density` and `ind_top_form_density_ae_unique` (A.9): the display of 2.35
    is marked (‡), not (∗).
  - `fiw_tb_extend_to_univ`, `fiw_tb_rectifiable_support_null` and
    `fiw_tb_ext_isIntegerMultiplicity` (A.11): (G2), (G3) and Lemma B are labels of the accepted
    natural-language proofs, not of Simon's proof of 7.2.

Each passage is corrected in place, marked **[corrected]**, and followed by a **Correction** line
in its entry. Appendix A now also explains that step labels such as "Step 6" or "(P4)" refer to the
accepted natural-language proofs. None of these errors is in a Lean statement or a Lean proof: doc
comments are part of neither, and the Lean kernel checks both (§9). The doc comments themselves
belong to the accepted declaration texts. Those texts are kept byte-identical to the accepted
commits (§9), so the doc comments are corrected only in this file.

**Corrections after the second publication review.** The independent review of `e26e6909`
(`nodes/root/publication-prose-audit-v2.json`) withheld acceptance for two corrections in A.3:

1. `rectifiability_structure_projection` said that, up to an `Hⁿ`-null set, `A` is a countable
   union of compact purely unrectifiable pieces of finite measure. `A` is not assumed measurable,
   and for a non-measurable `A` this is false. The entry (its passage and its Correction line) now describes what the Lean proof does:
   Borel hulls `B_j` of the pieces `A ∩ S_j`, which are purely unrectifiable by the hull identity
   and Ch. 3, Lemma 3.2; compact cores of the `B_j`; and the transfer of null projections to `A` by
   inclusion and the Lipschitz null-image bound. §3.3 now gives the same argument, and also states
   the recombination invariance of the set of bad frames on which the Gram–Schmidt step rests.
2. The Correction line of `rectifiability_orientation` illustrated the order `O(r)` with
   `T = (2 + y₁)[[B₁(0)]]` and the formula `∂T(φ) = −∫ φ(e₂) dL²`, which omits the boundary term
   `∫_{∂B₁(0)} (2 + y₁) ⟨φ, τ⟩ dH¹`. The example now states the general formula, takes `x = 0`, and
   uses `φ = a dy₂` with `spt a ⊆ B_R(0)` and `r < 1/R`, so that `η^#φ` has compact support in the
   open disc and the boundary term vanishes. The reference to Simon's display (12) is now a
   paraphrase rather than a quotation, since the book writes `λ` and a constant factor.

Following these two findings, every entry of Appendix A and every paragraph of §0–§6 were audited
again. Each entry was compared with the Lean statement at its line, with the accepted
natural-language proof of its node, with the book (`book/chapter-0*.txt`, using the printed page
headers), and, for external citations, with the cited sources. The audit found errors in 100
further entries, and added to the corrections of four previously corrected entries. Each entry is
again corrected in place, marked **[corrected]**, and explained in its **Correction** line, with a
counterexample where one is not immediate from the explanation. Grouped by the
most serious error in the entry, the newly corrected entries are the following (the first group
includes `rectifiability_structure_projection` of item 1).

- **False or ill-formed mathematical claims (11).**
  - A.1: `cmb_exists_countable_dense_testForms` (the constant `N` was undefined, and with the value
    of the neighbouring entry the bound is false).
  - A.3: `rpn_pe_kernel_sup_bound` (a reflected set called a translate), `rectifiability_structure_projection`.
  - A.5: `slicing_im_st_slice_geometry` (level-set charts exist only at regular points).
  - A.6: `dph_lpf_cmp_core_estimate` (the boundary term has the factor `c′ L^{k−1}`, not `c L^k`),
    `iwl_restriction_theory` (missing absolute values), `dr_cc_similarity_bound` (a case missing
    from a case distinction).
  - A.9: `iwl_top_dim_integrality` (a translation estimate stated without its smallness condition).
  - A.10: `br_zd_im_dirac_repr` (a `0`-vector written as a current).
  - A.11: `fiw_tl_ae_l1_density` (a non-compact set called compact), `fiw_tb_finite_net` (a
    quantifier in the wrong place).
- **Omitted hypotheses (51).** In these entries the reproduced statement left out hypotheses of the
  Lean statement on which its claim depends, most often measurability, openness, local finiteness,
  positivity of a weight, a normalization of a representation, or a finite mass:
  - A.3: `rectifiability_mass_measure_rectifiable`, `rectifiability_mickle_rado_density_zero`.
  - A.4: `lpf_lipschitz_localization`, `lpf_weighted_tangent_on_c1_chart`,
    `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_lusin_compact_pieces`,
    `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_caf_lipschitz_localization`,
    `lpf_wtc_caf_signed_of_lintegral`, `lpf_wtc_wtt_remainder_vanishes`,
    `lpf_wtc_wtt_blowup_integral_split`, `lpf_rsn_local_null`, `lpf_pic_current_of_dominated_density`,
    `lpf_pi_signed_fibre_sum`, `lpf_rectifiable_area_formula`, `lpf_raf_chart_area_formula`,
    `lpf_raf_chart_change_of_variables`, `lpf_pi_im_of_chart_density`.
  - A.5: `smr_rb_transfer_functional`, `smr_exists_unit_form_gt`, `smr_ufd_unit_coord_field`,
    `slicing_mb_pointwise`, `slicing_mb_pointwise_cutoff_tendsto`, `slicing_im_tg_weighted_tangent_chart`,
    `slicing_im_slice_triple`, `slicing_im_coarea_chart_tangent`, `slicing_im_st_measure_fields`,
    `slicing_im_st_mf_slice_integrable`, `slicing_im_st_weighted_tangent_on_c1_chart`.
  - A.6: `dph_iprod_current_of_bound`, `dph_sh_ae_affine_homotopy_isCompact_preimage_cyl`,
    `dph_lpf_comparison`, `dph_lpf_existence`, `imc_ae_zero_density_off_set`,
    `isoperimetric_coord_box_measure`, `fiw_ims_overlap_finite`, `iwl_imc_normalized_lebesgue_points`.
  - A.9: `iwl_imc_tangent_overlap`, `iwl_imc_density_zero_off_set`, `iwl_rl_restriction_cutoff_estimate`,
    `iwl_cr_ce_cutoff_converges_zero`, `iwl_cr_cone_estimates`, `iwl_cr_cest_mass_le_of_forms`,
    `iwl_cr_ci_ie_param_fubini`, `iwl_sp_massOn_le_of_compatible`, `iwl_integer_density`,
    `ind_ae_blowup_limit`, `ind_pi_good_slice_selection`, `ind_pi_ss_fatou_level_selection`.
  - A.11: `flat_convergence_iff_weak_convergence`, `fiw_flat_cauchy_limit`.
- **Wrong locators, quotations or provenance labels (39).** Pages and item numbers into Simon's
  book; quotations that were not verbatim (for example "(1), (2) give `P_k(ω) → T(ω)`", where p. 169
  prints `T_k(ω)`, a misprint for `T(ω)`); step labels of the accepted natural-language proofs
  presented as steps of the book's or of Mattila's proofs; uses ascribed to the proof of 3.9 that
  serve the formal proof of 5.1; an outdated remark on imports; a ball-volume bound presented as an
  erratum; and three summaries (`iwl_cr_hp_injective_pieces`, `iwl_top_dim_integrality`,
  `ind_pi_ss_cycle_slice_boundary`) labelled as summaries of the accepted natural-language proofs,
  although they summarize the Lean proofs, which take a different route. (`iwl_top_dim_integrality`
  is counted in the first group, because its summary also stated the translation estimate
  without its smallness condition.)
  - A.2: `constancy_theorem`, `constancy_local_of_mollified_const`.
  - A.3: `br_la_apply_eq_zero_of_lt_degree`, `rectifiability_bf_cone_ratio_measurable`,
    `rectifiability_mickle_rado_sup_lsc`, `rectifiability_bf_fibre_cone_comparison`.
  - A.4: `lpf_c1_approximation_eucl`.
  - A.5: `slicing_mass_representation`, `smr_exists_testForm_uniform_approx`, `smr_ufd_small_cutoff`,
    `slicing_im_tangential_gradient`, `slicing_im_coarea_eil_liminf_cover_bound`,
    `slicing_im_st_lsc_c1_extension`, `slicing_im_ll_twl_cie_jacobian_measurable`.
  - A.6: `fiw_ims_sc_converges_zero_small`, `iwl_cr_hp_injective_pieces`,
    `br_la_testForm_covectorNorm_bounded`, `dgc_pm_ball_volume_le`,
    `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`, `deformation_ipl_cc_chart_orientation_sign`,
    `deformation_ipl_cc_signed_change_of_variables`, `deformation_ipl_mwc_mil_ae_fderiv_eq_proj`,
    `fiw_ims_combine`.
  - A.8: `polyhedral_approx_flat_seq_tendsto`, `polyhedral_approx_testForm_covectorNorm_bounded`.
  - A.9: `iwl_cycle_reduction`, `iwl_cr_radial_operator`, `iwl_cr_ci_cutoff_pullback_testForm`,
    `ind_md_diagonal_weak_subseq`, `ind_ab_weighted_lebesgue_point`, `ind_pi_ss_cycle_slice_boundary`,
    `ind_const_multiple_integer`.
  - A.10: `br_la_weaklyConvergesOn_of_flat_decomposition`.
  - A.11: `fiw_localization`, `fiw_tangent_locality`, `fiw_tl_growth_bound`,
    `fiw_tb_translation_estimate`, `fiw_tb_te_directional_form`, `fiw_tb_lattice_coeff_finite`.

The audit also extended four earlier corrections. In `slicing_im_creg_local_to_global` the
hypotheses `Ω` open, `f` measurable and `W ⊆ Φ(Ω)` Borel are added. The title of
`iwl_restriction_weak_limit` now says that the convergence holds along a subsequence and for all
but countably many levels, and its quotation is verbatim. In `ind_top_form_density_ae_unique` the
quotation of p. 179 is replaced by a paraphrase. The Correction line of
`iwl_rl_testForm_smooth_cutoff` now mentions the extension `ω̃` of p. 179.

With these extensions `iwl_restriction_weak_limit` counts as a false claim and
`slicing_im_creg_local_to_global` as an omitted hypothesis, so the 19 entries corrected before this
revision now count 3, 2 and 14 in the three groups.

Altogether 120 entries of Appendix A now carry a Correction line. Counting each entry once, under
its most serious error, 14 contained a false or ill-formed mathematical claim, 53 omitted a
hypothesis of the Lean statement, and 53 had a wrong locator, quotation or provenance label. The
preamble of Appendix A also states two reading conventions that the audit made explicit: Simon's
implicit hypotheses, and phrases such as "the locality step in the proof of 6.3" when the printed
proof is shorter.

**Corrections of the main text in this revision.**

- §1.2: the source search also finds "(opaque)" in one `--` comment.
- §1.3: the ambient spaces of 5.3, 6.2, 6.1 and 6.3 are stated separately (6.1 lives in
  `ℝ^{(m+2)+ℓ}`, 6.3 in every `ℝ^P`).
- §1.4: six of the 691 declarations have no doc comment.
- §3.3: the structure-theorem bullet describes the hull argument and the Gram–Schmidt step; the
  step `μ(P′) = 0` uses a Borel subset of `P′` of full measure, as the Lean proof does; the
  Radon–Nikodym step is applied to `B₀`, not to `R`; the potential estimate cites Gilbarg–Trudinger
  §7.8 (the representation formula of Lemma 7.14 and the bound in the proof of Lemma 7.12);
  `rectifiability_weighted_tangent_ae` is described through bi-Lipschitz pieces instead of `C¹`
  charts; and the conclusion `⟨a ∧ β, ξ(x)⟩ = 0` is no longer labelled (13), which in the book is
  the definition of `S_x`.
- §3.6 and §6: the cube bound `(2r)ᵏ` for ball volumes is described as a simplification, not as an
  erratum; the §6 list now distinguishes gaps filled, arguments replaced and printed steps corrected,
  states the failing printed bound of Lemma 5.4, and moves the false claim of the first root
  decomposition out of the list of printed errors.
- §4: 6.2 depends on §4 (slicing) as well as on 5.3.
- §0: §3 names the accepted lemmas that carry each step, not every lemma.

## 9. Verification record

All checks used the pinned toolchain and the shared package tree
`lake-packages-25730c7c` (Mathlib `25730c7c`, `simongmt` `2b366308`).

**Exact configured comparator.** The command given in the task (`env -u HF_TOKEN
HUMANIZE_NODE_ID=root HUMANIZE_COMPARATOR_SUCCESS='Your solution is okay!' HUMANIZE_RUN_DIR=… … python3
…/verifier/gmt-compare.py --lean-target GMT/Ch06/Submission.lean --verifier-dir …/verifier
--verify-dir …/cluster-state/verification --packages …/lake-packages-25730c7c --frozen-commit
d8d46c9587747dee0751a1f780fcafdba16a3886 root`, run from the worktree root with `SWARM_NODE=hoa39`)
**passed** on the committed Lean candidate:

- Candidate commit `e9e57ea4f3401c64d2209512ec7e2b48fedd6af0` (tree `2976dbf69aa8e2ece26d7e74d66f50231f6aa223`);
  `GMT/Ch06/Submission.lean` sha256 `8844dc262ee305c7d301443a16525f97108a466caebf817f3e7d820abf0846f0`;
  `GMT/Ch06/Contract.lean` sha256 `ea3ee0ddd08be5db60dced2b002e9f60fd87091910069abcfcbd7e34db89853d`,
  equal to the frozen commit's.
- Exit status 0 after 4611 s. The output ends with
  `GMT comparator: comparator and Lean kernel accepted GMT.Ch06.main_theorem` and
  `Your solution is okay!`.
- Receipt `result.json`: status `passed`; checks `exit_zero`, `lean_kernel_accepted` and
  `final_marker` all `true`; `post_check_failures: []`; verdict key
  `a14f190d2e735e41e87da9bc3ed4eaa8cc9e4f12a41ee17766a29e82ebfb3e22`.
- Comparator configuration: challenge module `GMT.Ch06.Contract`, solution module
  `GMT.Ch06.Submission`, theorem `GMT.Ch06.main_theorem`, permitted axioms `propext`,
  `Quot.sound`, `Classical.choice` (Nanoda off, as configured; the Lean kernel check is mandatory).
- Log: both modules built ("Build completed successfully", 3152 and 3306 jobs); "Running Lean default
  kernel on solution. / Lean default kernel accepts the solution". The only `sorry` in the log is the
  challenge's own (`GMT/Ch06/Contract.lean:362`).
- Evidence: `cluster-state/verification/results/hoa39/20261014T182015Z-ch06-root-v8uhzxvd/`.

The comparator compares `main_theorem` and every definition it depends on with the frozen contract,
replays the Lean kernel on the exported closure and permits only the three axioms above. The commits
that add and revise this file change only this Markdown file. It is not a comparator input, since
the wrapper reads only the `.lean` files and the Lake build inputs of the worktree. So the
comparator's inputs are byte-identical to those of the run above. The comparator was run on the
first version of this file (`c3c9b342`) by the author (evidence
`20261014T194958Z-ch06-root-h1hdql_2`) and by the controller (evidence
`20261014T195224Z-ch06-root-kexkmndq`). On the second version (`e26e6909`) it ran just after the
commit (evidence `20261014T205523Z-ch06-root-sm9imq73`) and in the controller's isolated check
(evidence `20261014T205631Z-ch06-root-u8y3fc07`). For the present revision it was run on `e26e6909`
before any edit (evidence `20261014T211347Z-ch06-root-ekb9ck7e`), and on the edited worktree
immediately before the commit (evidence `20261014T231552Z-ch06-root-4x3admcz`). All these runs passed and reused the
verdict of the run above (key `a14f190d…`). The previous overlay `dfdc020b`, which differs only by the duplicated docstring of §8,
had also passed (evidence `20261014T165641Z-ch06-root-oypmaw0x`).

**Private build and axioms.** `GMT/Ch06/Submission.lean` of commit `e9e57ea4` (sha256
`8844dc26…46f0`) was compiled with `lake env lean -o` in a private `/tmp` copy that links the
shared package tree.
It compiled with exit status 0 in 4116 s, with no error and no `sorry` (102 linter warnings, such
as unused `simp` arguments and the deprecated `push_neg`). In the resulting environment `#print
axioms GMT.Ch06.main_theorem` prints `[propext, Classical.choice, Quot.sound]`. A meta-program
(`Scratch/EnvQuery.lean`, outside the repository) ran `collectAxioms` on each of the 725 theorems
of the module: the 691 children and `main_theorem` depend on exactly `propext`, `Classical.choice`
and `Quot.sound`, and the other 33 (equation, congruence and projection lemmas that Lean generated)
on a subset of these. The same program listed, for every constant of the module, the SimonGMT
constants in its type and value (Appendix B); `ConstantInfo.value?` omits theorem bodies, so the
program reads the value fields of theorems and definitions directly.

**Child interfaces.** For each of the 691 accepted DAG nodes, a scratch module states the node's
frozen `lean_statement`, taken verbatim from `dag.json`, in exactly the scope that the child
comparator uses: the scope commands of `Contract.lean` in effect at `main_theorem`, computed with
`contract_scope` of `verifier/gmt-compare.py` (`open MeasureTheory Filter Set Metric`,
`open scoped ENNReal NNReal Topology`, `namespace GMT.Ch06`, the three `open Poincare.SimonGMT…`
lines, `noncomputable section`, `end`). Each statement is proved by
`exact Submission.<lean_name>`.
The scratch module (691 theorems, `Scratch/InterfaceCheck.lean`, outside the repository) compiled
against the built `GMT.Ch06.Submission` with exit status 0 and no error or warning. So every
accepted node's exact globally qualified name `GMT.Ch06.Submission.<lean_name>` exists and has the
node's frozen type.
(A purely textual comparison of the 691 types in the source with the frozen `lean_statement`s, up to whitespace, differs only for three nodes,
`rectifiability_bf_cone_ratio_reduction`, `rectifiability_bf_witness_set_measurable` and
`slicing_im_creg_box_integrand_measurable`, whose source writes the type inside outer parentheses
`(…)`; the elaboration check covers them.)

**Text identity with the accepted commits.** For each node, the full text of its declaration
(doc comment, statement and proof) in `Submission.lean` was compared with the text of the same
declaration in the node's accepted `candidate_commit` (read with
`git show <commit>:GMT/Ch06/Submission.lean`): all 691 are identical. (A first version of the extractor reported one difference, for
`deformation_good_center`; it was a two-line `--` comment that belongs to the following
declaration, `deformation_onto_skeleton`, and that the extractor had attached to the preceding
block.)

**Overlay hygiene.**

- One `namespace GMT.Ch06` (line 41) and one `end GMT.Ch06` (line 69506); one
  `noncomputable section` (line 47) closed by `end` (line 367).
- Each of the 29 contract definitions occurs exactly once; lines 16–367 equal lines 9–360 of
  `Contract.lean` byte for byte; the contract's 8 imports are lines 1–8.
- 721 top-level declarations: the 29 contract definitions, the 691 child theorems and
  `main_theorem`, and nothing else (a line-based scan also hits one doc-comment line that begins
  with the word "theorem"). No duplicate names.
- No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern` or `native_decide`.
- `Contract.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `GMT.lean` and the
  other chapters' files are byte-identical to the frozen commit `d8d46c95`. Among source and build
  files, `git diff d8d46c95 HEAD` changes only `GMT/Ch06/Submission.lean`; its other paths are the
  controller's workflow records under `.humanize-workspace/` (4703 files) and this file.
- No forward references (§4).

## 10. reference_use

There is exactly one entry, and its source is `local-project`.

```json
[
  {
    "source": "local-project",
    "snapshot": ".humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494",
    "manifest": {"mode": "local-project", "project_commit": "d8d46c9587747dee0751a1f780fcafdba16a3886", "mathlib_commit": "25730c7c759d108ef87ab70af2342a196760f79d"},
    "queries": [
      "cat manifest.json",
      "rg -n '^theorem main_theorem|^namespace|^end GMT|^noncomputable section|^def CompactnessUnderMassBounds|^def ConstancyTheorem|^def SlicingTheorem|^def DeformationTheorem|^def IsoperimetricTheorem|^def RectifiabilityTheorem|^def IntegralityOfWeakLimits' project/GMT/Ch06/Contract.lean",
      "cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean; cmp project/GMT/Ch06/Contract.lean <worktree>/GMT/Ch06/Contract.lean; cmp project/{lakefile.toml,lake-manifest.json,lean-toolchain,GMT.lean} <worktree>/{…}",
      "rg -c sorry project/GMT/Ch06/Submission.lean",
      "rg -n 'Submission\\.' project/GMT",
      "rg -n 'compactness_under_mass_bounds|slicing_theorem|deformation_theorem|integrality_of_weak_limits|boundary_rectifiability|rectifiability_theorem|federer_fleming_compactness|lipschitz_pushforward_integer_multiplicity|flat_convergence_iff_weak_convergence|isoperimetric_theorem|polyhedral_approximation|constancy_theorem' project/",
      "git -C mathlib rev-parse HEAD",
      "rg -n 'def rieszMeasure|theorem integral_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/; rg -n '^namespace|^end ' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean",
      "rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div\\b' mathlib/Mathlib/MeasureTheory/Covering/; rg -n '^namespace|^end [A-Z]' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean",
      "rg -n 'def vitaliFamily|theorem ae_tendsto_measure_inter_div\\b' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean",
      "rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib/Analysis/Distribution/ mathlib/Mathlib/MeasureTheory/",
      "rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean; rg -n '^namespace|^end [A-Z]' mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean",
      "rg -n 'theorem LipschitzWith.ae_differentiableAt\\b' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean",
      "rg -n 'HasWeightedApproximateTangentSpaceAt' project/GMT/Ch06/Contract.lean; rg -n 'nVectorPushforward' project/GMT/Ch06/Contract.lean",
      "rg -n 'Hovila|1104\\.3453|Mickle' project/",
      "rg -n 'lpf_pushforward_integrality|rectifiability_bf_trichotomy|br_weightedTangent_congr|rectifiability_orientation' project/",
      "rg -n '3\\.1 \\(‡\\)|2\\.35' project/GMT/Ch06/",
      "rg -n 'theorem Measure.measure_toMeasurable_inter' mathlib/Mathlib/MeasureTheory/Measure/Basic.lean",
      "rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean",
      "rg -c 'rectifiability_structure_projection|lpf_wtc_lusin_compact_pieces|dph_lpf_cmp_core_estimate|iwl_integer_density' project/",
      "cmp project/GMT/Ch06/Contract.lean <worktree>/GMT/Ch06/Contract.lean"
    ],
    "findings": [
      "manifest.json: mode local-project, project d8d46c9587747dee0751a1f780fcafdba16a3886, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; `git -C mathlib rev-parse HEAD` = 25730c7c…, the revision pinned in lake-manifest.json.",
      "project/GMT/Ch06/Contract.lean: namespace GMT.Ch06 at line 34, noncomputable section at 40, the twelve Prop definitions (e.g. CompactnessUnderMassBounds at 198, IntegralityOfWeakLimits at 352), `theorem main_theorem … := by sorry` at 362, `end GMT.Ch06` at 364.",
      "The snapshot's Submission.lean is byte-identical to its Contract.lean (one `sorry`), and the snapshot's Contract.lean, lakefile.toml, lake-manifest.json, lean-toolchain and GMT.lean are byte-identical to the candidate's.",
      "`Submission.` occurs only in README prose of the snapshot (e.g. project/GMT/Ch06/README.md:4); none of the twelve child names occurs anywhere in project/ (rg exit status 1). The snapshot contains no prior proof of this chapter; every Lean proof used here comes from the run's accepted nodes.",
      "Mathlib (snapshot): RealRMK.rieszMeasure at RieszMarkovKakutani/Real.lean:65 and RealRMK.integral_rieszMeasure at :345 (namespace RealRMK, lines 52–494); VitaliFamily.ae_tendsto_lintegral_enorm_sub_div at Covering/Differentiation.lean:818 (namespace VitaliFamily, 87–872); Besicovitch.vitaliFamily at Covering/Besicovitch.lean:1021 and Besicovitch.ae_tendsto_measure_inter_div at :1105; IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero at Analysis/Distribution/AEEqOfIntegralContDiff.lean:205; exists_partition_approximatesLinearOn_of_hasFDerivWithinAt at MeasureTheory/Function/Jacobian.lean:255 (before `namespace MeasureTheory` at 272, so a root-namespace name); LipschitzWith.ae_differentiableAt at Analysis/Calculus/Rademacher.lean:385.",
      "SimonGMT is not part of the snapshot; its declarations cited in §5 were located in the pinned package lake-packages-25730c7c/simongmt (git HEAD 2b3663083f3fe399b6296fb8eaee52169170e197, the revision in lake-manifest.json), e.g. GeometricCurrentOn.boundary_boundary at Chapter06/Currents.lean:365 and measurable_rectifiable_purelyUnrectifiable_decomposition at Chapter03/Rectifiable.lean:514.",
      "Revision checks for the corrections of Appendix A (§8). Contract.lean uses HasWeightedApproximateTangentSpaceAt at lines 37, 74 (orientation clause of IsRectifiableTriple) and 150 (derivative clause of IsLipschitzPushforward). Line 153 defines the push-forward through the source-side density `θ x * nVectorPushforward n (L x) (ξ x)`; the normalized image density of §3.4 and A.4 occurs only in the run's proofs. 'Hovila|1104.3453|Mickle' and the four declaration names corrected in A.3–A.4 have no match in project/ (rg exit status 1 both times). The snapshot contains no doc comment of this run's declarations, so the corrections concern only the run's Submission.lean. '3.1 (‡)' occurs at Contract.lean:77, README.md:49 and the snapshot's Submission.lean:77. This is the contract's reading of the display marker; the same glyph marks the display of 2.35 in the book, which is why '2.35 (∗)' is corrected to '(‡)'.",
      "Checks for the corrections after the second review (§8). Mathlib (snapshot) has Measure.measure_toMeasurable_inter at MeasureTheory/Measure/Basic.lean:472, with hypotheses `MeasurableSet s` and `μ t ≠ ∞`: the hull identity `Hⁿ(B_j ∩ F) = Hⁿ(A_j ∩ F)` for measurable `F` used in the corrected entry `rectifiability_structure_projection`, whose Lean proof applies it with `Hⁿ(A ∩ S_j) < ∞`. MemLp.exists_hasCompactSupport_eLpNorm_sub_le is at MeasureTheory/Function/ContinuousMapDense.lean:141; that module is imported by the final Submission.lean through SimonGMT's Chapter01.RadonCaratheodoryIntegral, VectorFunctionalL1 and RadonDensity (pinned package lake-packages-25730c7c/simongmt), which corrects the remark in `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`. The search for four corrected declaration names in project/ has no match (rg exit status 1), as expected since the snapshot's Submission.lean is its Contract.lean (third finding): the snapshot contains none of the run's doc comments. Its Contract.lean is byte-identical to the candidate's (cmp exit status 0)."
    ],
    "use": "Contract identity and absence of prior proofs; provenance (file and line at the pinned revisions) of the Mathlib and SimonGMT declarations named in §3 and §5; the contract's definitions and notation behind the corrections of Appendix A (§8). No snapshot declaration was copied. Compatibility holds because the pins are identical, and every reused declaration is re-checked by the comparator's kernel replay with the axiom check (§9)."
  }
]
```

Web access was used only for bibliographic checks of the external citations of §11.

- Hovila–Järvenpää–Järvenpää–Ledrappier: the text of <https://arxiv.org/pdf/1104.3453> (version 2,
  December 2012) was checked. Its Theorem 1.2 is the projection theorem, Lemma 2.2 the conical
  density lemma, Definition 2.4 the definition of transversality, and Lemma 2.5 the trichotomy
  (§8). See also <https://arxiv.org/abs/1104.3453>.
- Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958) 433–439: the reference was confirmed as cited in
  <https://www.ams.org/journals/tran/1959-092-02/S0002-9947-1959-0112947-5/S0002-9947-1959-0112947-5.pdf>.
- In the second audit (§8) the following were consulted to confirm locators only: Federer 2.10.25
  as Eilenberg's inequality (<https://arxiv.org/pdf/2006.00419>), Federer 3.2.23 as the product
  formula for rectifiable sets (<https://arxiv.org/pdf/2505.11279>), Mattila's statement of the
  Mickle–Radó lemma in his survey (<https://arxiv.org/pdf/2112.00540>, Lemma 4.14), and Whitney's
  extension theorem in Evans–Gariepy §6.5 (<https://ncatlab.org/nlab/show/Whitney+extension+theorem>).
  A search for the numbering of Gilbarg–Trudinger's Lemmas 7.12 and 7.14 was inconclusive. §3.3 and
  §6 therefore cite §7.8 of that book and use the lemma numbers given in the accepted doc comments.

No proof step depends on a network source: the mathematics is that of Simon's book as recorded in
the accepted child proofs, which cite the additional sources listed in §11.

## 11. Citations

- L. Simon, *Introduction to Geometric Measure Theory*, 2014 Tsinghua lecture notes,
  <https://web.stanford.edu/class/math285/ts-gmt.pdf>; Chapter 6, printed pp. 131–180, with the
  cross-references to Chs. 1–3. The workspace copies are `book/chapter-06.txt` and
  `book/sources/chapter-06-source.txt`. Theorem and page numbers above are printed pages.
- Mathlib, revision `25730c7c759d108ef87ab70af2342a196760f79d`, and SimonGMT (`Poincare.SimonGMT`),
  revision `2b3663083f3fe399b6296fb8eaee52169170e197`, as cited in §5.
- Sources cited in the doc comments of the accepted declarations, for steps that the book states
  without proof or that the children prove differently:
  - P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Cambridge Univ. Press, 1995,
    Ch. 15 and Ch. 18 (conical densities, Mickle–Radó, Besicovitch–Federer projection theorem);
  - R. Hovila, E. Järvenpää, M. Järvenpää, F. Ledrappier, *Besicovitch–Federer projection theorem
    and geodesic flows on Riemann surfaces*, Geom. Dedicata 161 (2012), 51–61, arXiv:1104.3453
    (theorem and lemma numbers as in the arXiv version);
  - E. J. Mickle, T. Radó, *Density theorems for outer measures in n-space*, Proc. Amer. Math. Soc. 9
    (1958), 433–439;
  - D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §7.8 and
    Lemmas 7.12, 7.14 (the potential estimate replacing Remark 2.35);
  - H. Federer, *Geometric Measure Theory*, 1969, 2.10.25 and 3.2.23 (Eilenberg's inequality and the
    product formula for Hausdorff measure);
  - J. M. Ball, *Convexity conditions and existence theorems in nonlinear elasticity*, Arch.
    Rational Mech. Anal. 63 (1977), and I. Fonseca, G. Leoni, J. Malý, Arch. Rational Mech. Anal. 178
    (2005) (weak continuity of Jacobian minors);
  - L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §6.5 (Whitney's
    extension theorem); L. C. Evans, *Partial Differential Equations*, §8.1.4 (the Piola identity);
  - G. B. Folland, *Real Analysis*, Thm 6.15 (`(L¹)* = L^∞`); A. S. Kechris, *Classical Descriptive
    Set Theory*, Thm 15.1 (Lusin–Souslin).
## Appendix A. Catalogue of the 691 accepted declarations

Every accepted DAG node of the run, grouped by the root child under which the Lean proof first uses it, in depth-first order of the actual call tree (§4 order of the root children). A declaration used by several subtrees is listed once, in the first subtree that uses it; later subtrees refer to it. The three accepted but unused declarations are listed in A.13. For each declaration:

- its name (all are `GMT.Ch06.Submission.<name>`) and line in `GMT/Ch06/Submission.lean`;
- its DAG node, theorem issue `#i` (<https://github.com/ZhengyangZhang06/gmt-formalize/issues/i>), solution PR `#p` (<https://github.com/ZhengyangZhang06/gmt-formalize/pull/p>) and accepted candidate commit;
- **Statement and proof**: its Lean doc comment, reproduced verbatim except that line breaks are joined. Six declarations have no doc comment, and for them a summary is given, marked as such. For three of them it summarizes the accepted natural-language proof. For `iwl_cr_hp_injective_pieces`, `iwl_top_dim_integrality` and `ind_pi_ss_cycle_slice_boundary` it summarizes the Lean proof, which takes a different route from the accepted natural-language proof (see their entries). In 120 entries the reproduced text contained an error; they are listed in §8. Counting each entry once, under its most serious error, 14 contained a false or ill-formed mathematical claim, 53 omitted a hypothesis of the Lean statement on which the claim depends, and 53 had a wrong locator, quotation or provenance label. In those entries the reproduced passage is corrected in place, and each change is marked **[corrected]**. A **Correction** line in the same entry quotes the original wording and justifies the change. The Lean doc comments themselves belong to the accepted declarations' text and are left unchanged. The authoritative statement is the declaration's Lean type, which equals the node's frozen `lean_statement` (§9);
- **Calls**: the accepted declarations its proof references directly, with the section where each is listed;
- **Called by**: the accepted declarations (or `main_theorem`) whose proofs reference it directly.

Doc comments sometimes refer to an accepted declaration by an abbreviation, for example `l1_density` for `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le` (node `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.l1_density-a1`) or `minor_weak_star` for `deformation_ipl_mwc_minor_weak_star`. Each such abbreviation (a DAG key, i.e. the last component of a node id, or the end of a declaration name) was checked to denote exactly one declaration of this catalogue; the **Calls** and **Called by** lines give exact names.

Doc comments also use the step labels of the accepted natural-language proofs (`nodes/*/parent-supplied-natural-proof.md`, §7). Examples are "Step 6", "Part I", "I.5", "(6c)", "(P4)", "(E0)", "(Aff)" and "(MF)". Such labels number steps of those reviewed proofs, not items of Simon's book or of the other cited works, even where the same sentence names the theorem of the book that the step helps to prove.

Some doc comments locate a step of the formal proof "in the proof of" a theorem of the book whose printed proof is shorter. For example, the printed proof of 6.3 (p. 170) is the single sentence "A direct consequence of 6.2 above and the Compactness 3.11". So "the locality step in the proof of Ch. 6, 6.3" means a step of the formal proof of 6.3, i.e. of the accepted natural-language proofs of `root.boundary_rectifiability-a1` and its descendants, and does not claim that the printed proof contains that step.

Doc comments often state a result in Simon's conventions, in which some hypotheses are implicit. For instance, Ch. 3, 1.7 (p. 74) builds the measurability of `M` and the positivity and local integrability of `θ` into the definition of the approximate tangent space, while SimonGMT's `HasWeightedApproximateTangentSpaceAt` does not. Where a reproduced statement omitted a hypothesis of the Lean statement on which its claim depends, the hypothesis is added and marked **[corrected]**.

### A.1 Lemma 2.15 (§3.1): `compactness_under_mass_bounds` and its 12 further declarations

#### `compactness_under_mass_bounds` (L69081)

- `root.compactness_mass_bounds-a1` · issue #314 · PR #4238 · candidate `ec8c9ac424f6`
- **Statement and proof**: **Simon Ch. 6, Lemma 2.15 (p. 137).**  Take a weakly convergent subsequence `T_{φ(q)} ⇀ T₀` (`cmb_exists_weakly_convergent_subseq`).  Since `sup_q M_W(T_{φ(q)}) ≤ sup_q M_W(T_q) < ∞` for every `W ⊂⊂ U`, it also converges on continuous compactly supported forms for all measure representations (`cmb_tendsto_integral_of_weaklyConvergesOn`).
- **Calls**: `cmb_exists_weakly_convergent_subseq`, `cmb_tendsto_integral_of_weaklyConvergesOn`
- **Called by**: `federer_fleming_compactness`, `main_theorem`

#### `cmb_exists_weakly_convergent_subseq` (L68932)

- `root.compactness_mass_bounds-a1.weak_subseq-a1` · issue #697 · PR #1630 · candidate `00678bdb7796`
- **Statement and proof**: **Weak compactness step of Simon Ch. 6, Lemma 2.15 (p. 137).**  If `sup_q M_W(T_q) < ∞` for every `W ⊂⊂ U`, a subsequence of `T_q` converges weakly in `U`.  Take an exhaustion `W i ⊂⊂ U`, `B i = sup_q M_{W i}(T_q)`, and countable families `E i` of test forms supported in `W i` that are uniformly dense there.  The mass estimate bounds `T_q(η)` uniformly in `q` for `η ∈ ⋃ i, E i`, so sequential compactness of the countable product `∏_η [-b_η, b_η]` gives one subsequence `φ` along which every `T_q(η)` converges.  Density and the mass estimate make `T_{φ q}(ω)` Cauchy for every test form `ω`; its limit `L` is linear, and `|L(ω)| ≤ B i · N · sup_x ‖ω(x)‖` for `spt ω ⊆ W i` (operator norm `‖·‖`, `N = √#(Fin n → Fin P)`) gives the sequential continuity of `L`.
- **Calls**: `cmb_exists_compactly_contained_exhaustion`, `cmb_exists_countable_dense_testForms`, `cmb_abs_apply_le_of_massOn_le`
- **Called by**: `compactness_under_mass_bounds`

#### `cmb_exists_compactly_contained_exhaustion` (L401)

- `root.compactness_mass_bounds-a1.exhaustion-a1` · issue #687 · PR #1628 · candidate `cb89cc7f436b`
- **Statement and proof**: Exhaustion of an open `U ⊆ ℝ^P` by open sets `W i ⊂⊂ U` such that every compact `K ⊆ U` lies in some `W i`: `W i = {x : |x| < i, (i + 1)⁻¹ < infEDist x (ℝ^P ∖ U)}`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_mf_slice_integrable`, `fiw_flat_to_weak`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `rectifiability_weighted_tangent_ae`, `rectifiability_orientation`, `iwl_positive_density`, `rectifiability_mass_measure_rectifiable`, `slicing_im_testform_determining`, `cmb_exists_weakly_convergent_subseq`

#### `cmb_exists_countable_dense_testForms` (L3869)

- `root.compactness_mass_bounds-a1.testform_separable-a1` · issue #693 · PR #1757 · candidate `bfaf075e7525`
- **Statement and proof**: **Separability step of Simon Ch. 6, Lemma 2.15 (p. 137).**  If `closure W` is compact, a countable family `E` of test forms supported in `W` is dense among all test forms supported in `W`, uniformly in the Euclidean coefficient norm.  The coefficient vector `c(α) = (α(e_{I 0}, …, e_{I (n-1)}))_I ∈ ℝ^(Fin n → Fin P)` satisfies `|α| ≤ √N ‖c(α)‖_∞` with `N = #(Fin n → Fin P)` **[corrected]**.  For each accuracy `1/(m+1)` and scale `1/(j+1)`, the forms whose coefficients oscillate by less than `1/(m+1)` at scale `1/(j+1)` are approximated through their values on a finite `1/(j+1)`-net of `closure W`, which lie in a separable finite-dimensional space.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves `N` undefined. The neighbouring entry `cmb_exists_weakly_convergent_subseq` uses `N` for `√#(Fin n → Fin P)`, and with that value the bound would be false: for `P = 2`, `n = 1` and `α = dx¹ + dx²`, `|α| = √2 > 2^{1/4}` while `‖c(α)‖_∞ = 1`. The Lean proof (lines 3878–3880), whose local constant `N` is `√#(Fin n → Fin P)`, proves `|α| ≤ √#(Fin n → Fin P) · ‖c(α)‖_∞`, i.e. the stated bound with `N = #(Fin n → Fin P)`: `|α|²` is the sum of the squares of at most `N` coefficients, each at most `‖c(α)‖_∞²`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `cmb_exists_weakly_convergent_subseq`

#### `cmb_abs_apply_le_of_massOn_le` (L561)

- `root.compactness_mass_bounds-a1.mass_bound-a1` · issue #689 · PR #1632 · candidate `ba202ac0407b`
- **Statement and proof**: Mass estimate: if `M_W(T) ≤ B` and `ω` is supported in `W` with `|ω(x)| ≤ C` everywhere (Euclidean covector norm), then `|T(ω)| ≤ B · C`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_abs_apply_le_opNorm_mul_massOn`, `isoperimetric_mass_eq_zero_iff`, `cmb_measureRepresentation_continuous_bound`, `iwl_cr_cest_mass_le_of_forms`, `fiw_flat_to_weak`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `dph_lpf_existence`, `dph_iprod_slice_continuity`, `dph_iprod_horizontal_ftc`, `dph_sh_affine_estimate`, `rectifiability_orientation`, `deformation_pushforward_homotopy`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `iwl_rl_restriction_cutoff_estimate`, `iwl_localization`, `iwl_positive_density`, `cmb_exists_weakly_convergent_subseq`

#### `cmb_tendsto_integral_of_weaklyConvergesOn` (L9980)

- `root.compactness_mass_bounds-a1.continuous_form_conv-a1` · issue #701 · PR #3928 · candidate `7fe585673d4e`
- **Statement and proof**: **Convergence on continuous forms in Simon Ch. 6, Lemma 2.15 (p. 137).**  If `sup_q M_W(S_q) < ∞` for each `W ⊂⊂ U` and `S_q ⇀ S₀`, then `∫ ⟨ω, v_q⟩ dμ_q → ∫ ⟨ω, v₀⟩ dμ₀` for every continuous compactly supported `n`-form `ω` with `tsupport ω ⊆ U` and all representations (2.7) `(μ_q, v_q)` of `S_q` and `(μ₀, v₀)` of `S₀`.  Take `W ⊂⊂ U` containing `tsupport ω` and `B = sup_q M_W(S_q)`, so that `M_W(S₀) ≤ B` by 2.14.  A test form `η` supported in `W` with `|ω - η| ≤ δ` splits `∫ ⟨ω, v⟩ dμ = T(η) + ∫ ⟨ω - η, v⟩ dμ` with remainder at most `B δ`, and `S_q(η) → S₀(η)`.
- **Calls**: `cmb_exists_testForm_uniform_approx`, `cmb_measureRepresentation_continuous_bound`
- **Called by**: `compactness_under_mass_bounds`

#### `cmb_exists_testForm_uniform_approx` (L4035)

- `root.compactness_mass_bounds-a1.mollify-a1` · issue #695 · PR #994 · candidate `26d9d850fd23`
- **Statement and proof**: **Mollification step of Simon Ch. 6, Lemma 2.15 (p. 137).**  A continuous compactly supported `n`-form `ω` with `tsupport ω ⊆ V`, `V` open, is a uniform limit, in the Euclidean coefficient norm, of test forms supported in `V`.  As `|α| ≤ √N ‖α‖` (`N = #(Fin n → Fin P)`, `‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ ω)`: `ψ ⋆ ω` is the convolution of `ω` with a normalized smooth bump `ψ` supported in a ball whose radius is a uniform-continuity modulus of `ω`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to `1` exactly on `tsupport ω`, whose support `V'` has compact closure in `V`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `cmb_measureRepresentation_continuous_bound`, `cmb_tendsto_integral_of_weaklyConvergesOn`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`

#### `cmb_measureRepresentation_continuous_bound` (L9888)

- `root.compactness_mass_bounds-a1.repr_bound-a1` · issue #699 · PR #2562 · candidate `5caba5008111`
- **Statement and proof**: **Continuous forms against a measure representation: the step "by (2.7)" in the proof of Simon Ch. 6, Lemma 2.15 (p. 137).**  Let `(μ, v)` represent `T` as in (2.7), `W ⊂⊂ U` and `M_W(T) ≤ B`.  If `ω` is a continuous `n`-form with `tsupport ω ⊆ W` and `|ω(x)| ≤ C` everywhere (Euclidean coefficient norm), then `⟨ω, v⟩` is `μ`-integrable and `|∫ ⟨ω, v⟩ dμ| ≤ B · C`. Choose `V` open with `tsupport ω ⊆ V` and `closure V ⊆ W` compact.  The coefficients `v_β` of `v` are `μ`-integrable on `closure V`, so for every continuous `θ` vanishing off `closure V` with `|θ| ≤ D`, `⟨θ, v⟩ = ∑_β θ(e_β) v_β` is integrable and `|∫ ⟨θ, v⟩ dμ| ≤ D · G`, where `G = ∑_β ∫_{closure V} |v_β| dμ`.  For a test form `η` supported in `V` with `|ω - η| ≤ ε`, the mass bound gives `|∫ ⟨ω, v⟩ dμ| ≤ |T(η)| + ε G ≤ B (C + ε) + ε G`; let `ε → 0`.
- **Calls**: `cmb_rb_measureRepresentation_integrableOn_coeff`, `cmb_covector_eq_sum_coord_smul_wedge`, `cmb_rb_integral_coeff_pairing_bound`, `cmb_exists_testForm_uniform_approx`, `cmb_rb_covectorEuclideanNorm_add_le`, `cmb_abs_apply_le_of_massOn_le`
- **Called by**: `cmb_tendsto_integral_of_weaklyConvergesOn`, `imc_lintegral_coordNorm_le_mass`

#### `cmb_rb_measureRepresentation_integrableOn_coeff` (L4122)

- `root.compactness_mass_bounds-a1.repr_bound-a1.coeff_integrable-a1` · issue #1783 · PR #2262 · candidate `3cd72266f61a`
- **Statement and proof**: Coefficients of a measure representation (2.7) are integrable on compact sets (Simon Ch. 6, p. 136): for compact `K ⊆ W ⊆ U`, `W` open, test with `ψ = χ dx^β`, where the smooth cutoff `χ` equals `1` exactly on `K` and has compact support in `W`.  Then `⟨ψ, v⟩` is `μ`-integrable and agrees on `K` with the coefficient `⟨dx^β, v⟩`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `cmb_measureRepresentation_continuous_bound`, `imc_lintegral_coordNorm_le_mass`

#### `cmb_covector_eq_sum_coord_smul_wedge` (L2558)

- `root.compactness_mass_bounds-a1.covector_expansion-a1` · issue #691 · PR #1655 · candidate `6c6b4b2753e8`
- **Statement and proof**: Coordinate expansion of an `n`-covector on `ℝ^P` in the wedge basis: `α = ∑_β α(e_{β(0)}, …, e_{β(n-1)}) dx^β` over the increasing multi-indices `β`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_moc_abs_covector_apply_le`, `rpn_moc_abs_nvector_apply_le`, `cmb_measureRepresentation_continuous_bound`, `rectifiability_mass_measure_representation`, `iwl_restriction_theory`, `rectifiability_orientation`, `deformation_ipl_minor_weak_continuity`, `deformation_skeleton_polyhedral`, `iwl_positive_density`

#### `cmb_rb_integral_coeff_pairing_bound` (L4151)

- `root.compactness_mass_bounds-a1.repr_bound-a1.pairing_bound-a1` · issue #1791 · PR #2341 · candidate `230f547c2f70`
- **Statement and proof**: **Coordinate pairing estimate, the step "by (2.7)" in the proof of Simon Ch. 6, Lemma 2.15 (p. 137).**  Let the coefficients `v^β = ⟨dx^β, v⟩` of `v` be `μ`-integrable on a measurable set `K`, and let `θ` be a continuous `n`-form vanishing off `K` with `|θ| ≤ D` (Euclidean coefficient norm).  Then `f = ∑_β θ(e_β) v^β` is `μ`-integrable and `|∫ f dμ| ≤ D ∑_β ∫_K |v^β| dμ`.  Each coefficient `θ(e_β)` is continuous with `|θ(e_β)| ≤ |θ| ≤ D`, so `f` is integrable on `K`; it vanishes off `K`; and `|f| ≤ ∑_β D |v^β|` pointwise.
- **Calls**: `cmb_rb_abs_euclideanCovectorCoordinate_le`
- **Called by**: `cmb_measureRepresentation_continuous_bound`

#### `cmb_rb_abs_euclideanCovectorCoordinate_le` (L2617)

- `root.compactness_mass_bounds-a1.repr_bound-a1.coord_bound-a1` · issue #1771 · PR #2240 · candidate `bc4ced077707`
- **Statement and proof**: A coordinate of an `n`-covector is bounded by its Euclidean coefficient norm: `|α(e_{β(0)}, …, e_{β(n-1)})| ≤ |α|` for every increasing multi-index `β`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_moc_abs_covector_apply_le`, `cmb_rb_integral_coeff_pairing_bound`

#### `cmb_rb_covectorEuclideanNorm_add_le` (L6179)

- `root.compactness_mass_bounds-a1.repr_bound-a1.norm_add_le-a1` · issue #1776 · PR #2182 · candidate `21d072dc936c`
- **Statement and proof**: The triangle inequality for the Euclidean coefficient norm of covectors (Simon Ch. 6, 1.15): `|α + γ| ≤ |α| + |γ|`.  `|a|` is the Euclidean norm of the coefficient vector `c(a)_I = [I strictly increasing] · a(b_{I(0)}, …, b_{I(n-1)})` in `ℝ^(Fin n → Fin P)`, and `c` is additive, so this is `norm_add_le` in that Euclidean space.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `cmb_measureRepresentation_continuous_bound`

### A.2 Theorem 2.34 (§3.2): `constancy_theorem` and its 17 further declarations

#### `constancy_theorem` (L42133)

- `root.constancy-a1` · issue #316 · PR #4888 · candidate `b4bbd87115fa`
- **Statement and proof**: **Simon Ch. 6, Theorem 2.34 (Constancy Theorem, p. 142).**  The proof in three parts, of which the printed proof contains the first two **[corrected]**: `∂T = 0` makes `T` kill every `(D_j a) dx¹ ∧ ⋯ ∧ dxⁿ` (display (2)); such a `T` is `c_{x₀} [[B_r(x₀)]]` near each `x₀ ∈ U` (Riesz representation of the mollified functional, `θ_ε` constant, `ε ↓ 0`); on connected `U` these local constants agree, and a partition of unity gives `T = c [[U]]`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "The printed proof in three parts". The printed proof (pp. 142–143) ends with the constancy of `T` on balls `B_ρ(x₀) ⊆ U` and the words "and the result follows". The third part, the agreement of the local constants on the connected set `U` and the partition of unity, is supplied by the formal proof (`constancy_of_local_constancy`, `constancy_testFormOn_eq_finset_sum_subordinate`).
- **Calls**: `constancy_of_local_constancy`, `constancy_local_on_balls`, `constancy_closed_kills_partial_derivatives`
- **Called by**: `main_theorem`

#### `constancy_of_local_constancy` (L42065)

- `root.constancy-a1.globalize-a1` · issue #970 · PR #2605 · candidate `151404f8d9c3`
- **Statement and proof**: Globalization in **Simon Ch. 6, Theorem 2.34** (end of the proof, p. 143): if near every point of the open connected set `U` the current `T` is a constant multiple of `[[U]]`, then it is one global constant multiple of `[[U]]`.  Overlapping balls carry the same constant (test with a unit-integral form supported in the overlap), so the constant is locally constant, hence constant on the connected `U`; a partition of unity subordinate to the balls adds up the local identities.
- **Calls**: `constancy_exists_topTestForm_integral_eq_one`, `constancy_testFormOn_eq_finset_sum_subordinate`
- **Called by**: `constancy_theorem`

#### `constancy_exists_topTestForm_integral_eq_one` (L41961)

- `root.constancy-a1.globalize-a1.unit_top_form-a1` · issue #1383 · PR #2232 · candidate `26804ee35e55`
- **Statement and proof**: A top-degree test form with unit integral supported in a prescribed nonempty open set (Simon Ch. 6, proof of 2.34, p. 143): `ω = (f / ∫ f dLⁿ) dx¹ ∧ ⋯ ∧ dxⁿ` for a smooth bump `f` with `spt f = B̄_{δ/2}(z) ⊆ B_δ(z) ⊆ W`, so `spt ω ⊆ W ⊆ U` and `∫ ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ = 1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_of_local_constancy`

#### `constancy_testFormOn_eq_finset_sum_subordinate` (L42007)

- `root.constancy-a1.globalize-a1.pou_decomposition-a1` · issue #1384 · PR #2252 · candidate `5c4bf4ca7a1b`
- **Statement and proof**: Partition-of-unity decomposition of a test form (globalization step of the proof of Simon Ch. 6, Theorem 2.34, p. 143): if `spt ω ⊆ ⋃ᵢ Vᵢ` with every `Vᵢ` open, then `ω = ∑_{i ∈ s} ηᵢ` for a finite `s` and test forms `ηᵢ ∈ 𝒟ⁿ(U)` with `spt ηᵢ ⊆ Vᵢ`.  Take a finite subcover of the compact set `spt ω`, a smooth partition of unity `(χᵢ)_{i ∈ s}` on `spt ω` subordinate to it, and `ηᵢ = χᵢ ω`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_of_local_constancy`

#### `constancy_local_on_balls` (L41865)

- `root.constancy-a1.local_on_balls-a1` · issue #968 · PR #4605 · candidate `0427214b3aca`
- **Statement and proof**: **Simon Ch. 6, Theorem 2.34 (Constancy Theorem), proof pp. 142–143: `T = c [[B_r(x₀)]]` near each point.**  If `T(ω) = 0` whenever `ω(·)(e₁, …, eₙ) = D_j a` for a `C^∞` compactly supported `a` with `spt a ⊆ U` (the printed `T(dω_j) = ∂T(ω_j) = 0`), then every `x₀ ∈ U` has a ball `B_r(x₀) ⊆ U` with `T(ω) = c ∫ ω(x)(e₁, …, eₙ) dLⁿ(x)` whenever `spt ω ⊆ B_r(x₀)`.  Write `T(ω) = u(ω(·)(e))`.  For normalized smooth bumps `ψ_k` with `spt ψ_k ⊆ B̄_{ε_k}(0)`, `ε_k ↓ 0`, the functional `f ↦ u(ψ_k ∗ 1_B f)` is bounded on `L¹(B)`, hence equals `f ↦ ∫_B f θ_k` (Riesz), and `θ_k` is a.e. constant on `B` (printed display (2)); letting `k → ∞` gives `u(b) = c ∫ b` for `spt b ⊆ B`.  (Book `n = m + 1`.)
- **Calls**: `constancy_topForm_scalar_reduction`, `constancy_mollified_functional_l1_bounded`, `constancy_mollifier_iteratedFDeriv_norm_le_integral`, `constancy_riesz_l1_dual_bounded_density`, `constancy_mollified_density_const`, `constancy_local_of_mollified_const`, `constancy_approx_identity_iteratedFDeriv_tendstoUniformly`
- **Called by**: `constancy_theorem`

#### `constancy_topForm_scalar_reduction` (L17096)

- `root.constancy-a1.local_on_balls-a1.scalar_reduction-a1` · issue #2564 · PR #3579 · candidate `0104810ac99c`
- **Statement and proof**: Step 1 of the proof of the Constancy Theorem (Simon Ch. 6, Theorem 2.34, pp. 142–143): every top-degree form is `ω = a_ω dx¹ ∧ ⋯ ∧ dxⁿ` with `a_ω(x) = ω(x)(e₁, …, eₙ)`, so `T ∈ 𝒟ₙ(U)` acts as `T(ω) = u(a_ω)` for `u(b) = T(b dx¹ ∧ ⋯ ∧ dxⁿ)`; `u` is linear on `C^∞` functions with compact support in `U` and continuous for `C^∞` convergence with supports in a compact `K ⊆ U`. (Book `n = m + 1`.)
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_local_on_balls`

#### `constancy_mollified_functional_l1_bounded` (L17244)

- `root.constancy-a1.local_on_balls-a1.mollified_l1_bound-a1` · issue #2582 · PR #3492 · candidate `43af4e895902`
- **Statement and proof**: **Step 3 of the proof of Simon Ch. 6, Theorem 2.34 (Constancy Theorem, pp. 142–143).**  Let `B = B_ρ(x₀)` with `B̄_{ρ+ε}(x₀) ⊆ U` and let `φ` be `C^∞` with `spt φ ⊆ B̄_ε(0)` and the derivative bounds `‖D^q(φ ∗ g)‖ ≤ C_q ∫ |g|`.  Then `F(f) = u(φ ∗ 1_B f)` is linear and `L¹(B)`-bounded.  Each `φ ∗ 1_B f` is `C^∞` with support in the compact set `K = B̄_{ρ+ε}(x₀) ⊆ U`, so linearity follows from that of `u`.  If no bound held, there would be `f_k` with `|F(f_k)| > (k + 1) ∫_B |f_k|`; then `g_k = F(f_k)⁻¹ f_k` has `F(g_k) = 1` and `∫_B |g_k| ≤ 1 / (k + 1)`, so all derivatives of `φ ∗ 1_B g_k` tend to `0` uniformly and continuity of `u` gives `1 = F(g_k) → u 0 = 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_local_on_balls`

#### `constancy_mollifier_iteratedFDeriv_norm_le_integral` (L9648)

- `root.constancy-a1.mollifier_derivative_bound-a1` · issue #966 · PR #1657 · candidate `d6285a34810d`
- **Statement and proof**: Simon Ch. 6, proof of Theorem 2.34 (p. 142): `D^β (φ ∗ g) = (D^β φ) ∗ g`, so every derivative of a mollification is bounded by the `L¹` norm of the mollified function.  By induction on `q`, for a vector-valued smooth compactly supported kernel `f` and a bilinear `L` with `‖L u t‖ ≤ B ‖u‖ |t|`: `‖D^q (f ∗_L g)(x)‖ ≤ B · sup ‖D^q f‖ · ∫ |g|`, using `D (f ∗_L g) = (D f) ∗_{L.precompL} g` and `‖D^{q+1} h‖ = ‖D^q (D h)‖`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_local_on_balls`

#### `constancy_riesz_l1_dual_bounded_density` (L41762)

- `root.constancy-a1.riesz_l1_dual-a1` · issue #965 · PR #3481 · candidate `471cfdd5be90`
- **Statement and proof**: **Riesz representation `(L¹(μ))* = L^∞(μ)`** for a finite measure `μ`, used without proof in Simon Ch. 6, proof of Theorem 2.34 (p. 142; cf. Folland, *Real Analysis*, Thm 6.15).  Put `C' = max(C, 0)` and `ν(A) = F(1_A)`.  Since `1_{A ∪ B} = 1_A + 1_B` for disjoint `A, B` and `∫ |1_A| dμ = μ(A)`, `ν` is additive with `|ν(A)| ≤ C' μ(A)`.  The bounded density lemma gives a measurable `θ` with `|θ| ≤ C'` everywhere and `F(1_A) = ∫_A θ dμ`, and the extension from indicators gives `F f = ∫ f θ dμ` for every integrable `f`.
- **Calls**: `constancy_riesz_bounded_density_of_dominated_additive`, `constancy_riesz_eq_integral_mul_of_indicator_eq`
- **Called by**: `constancy_local_on_balls`

#### `constancy_riesz_bounded_density_of_dominated_additive` (L41537)

- `root.constancy-a1.riesz_l1_dual-a1.dominated_bounded_density-a1` · issue #2467 · PR #3107 · candidate `0e9b0c22da46`
- **Statement and proof**: **Bounded density of a dominated finitely additive set function** (the Radon–Nikodym step of `(L¹)* = L^∞`, used without proof in Simon Ch. 6, Theorem 2.34, p. 142; cf. Folland, *Real Analysis*, Thm 6.15).  Let `μ` be finite, `C ≥ 0`, and `ν` additive on disjoint measurable sets with `|ν(A)| ≤ C μ(A)`.  Then `ρ = ν + C μ` is a finite measure: `ν(∅) = 0`, `ρ` is finitely additive, and `ρ(⋃ sᵢ) - ρ(⋃_{i<N} sᵢ) = ρ(⋃ sᵢ \ ⋃_{i<N} sᵢ) ≤ 2C μ(⋃ sᵢ \ ⋃_{i<N} sᵢ) → 0`. Also `ρ ≪ μ`, so `ρ = f μ` for `f = dρ/dμ` (zero singular part), and `0 ≤ f ≤ 2C` `μ`-a.e.  The truncation `θ = min(f, 2C) - C` is measurable, `|θ| ≤ C` everywhere, and `θ = f - C` `μ`-a.e., so `ν(A) = ρ(A) - C μ(A) = ∫_A θ dμ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_riesz_l1_dual_bounded_density`

#### `constancy_riesz_eq_integral_mul_of_indicator_eq` (L41677)

- `root.constancy-a1.riesz_l1_dual-a1.extend_from_indicators-a1` · issue #2473 · PR #3288 · candidate `6c2f3038a34e`
- **Statement and proof**: Extension from indicators for the duality `(L¹(μ))* = L^∞(μ)` (Riesz), used in Simon Ch. 6, proof of Theorem 2.34 (p. 142).  Let `μ` be finite and let `F` be additive and homogeneous with `|F f| ≤ C ∫ |f| dμ` on `μ`-integrable functions.  Let `θ` be measurable with `|θ| ≤ M`, and suppose `F (1_A) = ∫_A θ dμ` for every measurable `A`.  Then `F f = ∫ f θ dμ` for every integrable `f`.  Both sides are additive and `L¹`-Lipschitz, hence continuous on `α →₁[μ] ℝ`, so `Integrable.induction` extends the identity from multiples of indicators to all of `L¹(μ)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_riesz_l1_dual_bounded_density`

#### `constancy_mollified_density_const` (L41441)

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1` · issue #2595 · PR #4440 · candidate `babfd43a1976`
- **Statement and proof**: Simon Ch. 6, 2.34, printed display (2) and the conclusion that `θ_ε` is constant on `B_ρ(x₀)`: a bounded measurable density `θ` of `f ↦ u(φ ∗ (1_B f))`, `B = B_ρ(x₀)`, is a.e. a constant `c` on `B`, so `u(φ ∗ (1_B f)) = c ∫_B f`.  `θ` is locally integrable (measurable and bounded), its weak coordinate derivatives vanish on `B` (`Submission.constancy_mdc_weak_partials_vanish`), hence `θ = c` a.e. on `B` (`Submission.constancy_mdc_ae_const_of_weak_partials_vanish`).
- **Calls**: `constancy_mdc_weak_partials_vanish`, `constancy_mdc_ae_const_of_weak_partials_vanish`
- **Called by**: `constancy_local_on_balls`

#### `constancy_mdc_weak_partials_vanish` (L17376)

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_identity-a1` · issue #3574 · PR #4199 · candidate `6403f9e1601b`
- **Statement and proof**: Simon Ch. 6, Proof of Theorem 2.34 (Constancy Theorem, pp. 142–143), display (2): `∫ D_j a θ_ε dLⁿ = T(dω_j) = ∂T(ω_j) = 0`.  Here `u(D_j a) = 0` for every `a ∈ C_c^∞` with `spt a ⊆ U` plays the role of `∂T = 0`, `φ` the role of the mollifier `ϕ_ε`, and `θ` represents `f ↦ u(φ ∗ (1_B f))` on `B = B_ρ(x₀)` (display (1)).  For `a ∈ C_c^∞` with `spt a ⊆ B`, the function `d = D_j a` is continuous with `spt d ⊆ spt a ⊆ B`; `φ ∗ a` is `C^∞` with compact support and `spt (φ ∗ a) ⊆ B̄_{ρ+ε}(x₀) ⊆ U`; and `D_j (φ ∗ a) = φ ∗ d = φ ∗ (1_B d)`.  Hence `0 = u(D_j (φ ∗ a)) = ∫_B d θ = ∫ θ d`, the last step because `d θ` vanishes off `B`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_mollified_density_const`

#### `constancy_mdc_ae_const_of_weak_partials_vanish` (L41351)

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_constancy_ball-a1` · issue #3582 · PR #4284 · candidate `8b7f3a46c915`
- **Statement and proof**: Weak constancy on a ball (Simon Ch. 6, Theorem 2.34, printed proof p. 143): if `θ` is locally integrable and `∫ θ D_j a = 0` for every `a ∈ C_c^∞(B_ρ(x₀))` and every `j`, then `θ` is a.e. constant on `B_ρ(x₀)`.  The mollifications `θ ∗ ψ_k` have vanishing derivative on `B_{ρ - 1/(k+1)}(x₀)`, hence are constant there, and they converge to `θ` a.e.
- **Calls**: `constancy_mdc_smooth_approx_identity_ae_tendsto`
- **Called by**: `constancy_mollified_density_const`

#### `constancy_mdc_smooth_approx_identity_ae_tendsto` (L41192)

- `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1` · issue #3577 · PR #4208 · candidate `2219dd324b47`
- **Statement and proof**: A smooth approximate identity on `ℝⁿ` (Simon Ch. 6, proof of 2.34, p. 143; Ch. 2, §2): `ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1) y)` for a smooth bump `0 ≤ h ≤ 1` with `h(0) = 1`, `spt h ⊆ B_1(0)` and `I = ∫ h > 0`.  Each `ψ_k` is `C^∞`, nonnegative, of integral `1` and supported in `B̄_{1/(k+1)}(0)`, and `0 ≤ ψ_k ≤ (k+1)ⁿ I⁻¹`.  For locally integrable `g` and every Lebesgue point `x` of `g` (Simon Ch. 1, 3.17), `|(g ∗ ψ_k)(x) − g(x)| ≤ I⁻¹ Lⁿ(B_1(0)) · ⨍_{B̄_{1/(k+1)}(x)} |g − g(x)| → 0`, so `g ∗ ψ_k → g` almost everywhere.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_mdc_ae_const_of_weak_partials_vanish`, `deformation_ipl_mwc_lipschitz_smooth_approx`

#### `constancy_local_of_mollified_const` (L41467)

- `root.constancy-a1.local_on_balls-a1.mollifier_limit-a1` · issue #2604 · PR #3732 · candidate `4a6e0cee1f77`
- **Statement and proof**: Simon Ch. 6, Theorem 2.34: Step 5 of the accepted natural-language proof of `constancy_local_on_balls`, i.e. the final passage to the limit in the mollification parameter in the printed proof (p. 143) **[corrected]**: let `u` be sequentially continuous on C^∞ functions supported in a fixed compact `K ⊆ U` (condition (C)), `B̄_R(x₀) ⊆ U`, and let continuous kernels `ψ_k` with `spt ψ_k ⊆ B̄_{r_k}(0)`, `ρ + r_k ≤ R`, satisfy `D^q(ψ_k ∗ b) → D^q b` uniformly for every C^∞ compactly supported `b`.  If `u(ψ_k ∗ (1_{B_ρ(x₀)} f)) = c_k ∫_{B_ρ(x₀)} f` for all `k` and all `f` integrable on `B_ρ(x₀)`, then `u(b) = c₀ ∫ b` for one constant `c₀` and every C^∞ compactly supported `b` with `spt b ⊆ B_ρ(x₀)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Step 5 of the proof (p. 143, "letting ε ↓ 0")". The printed proof has no numbered steps, and `ε` is the accepted proofs' name for the book's mollification parameter, so the quotation is not verbatim. The step is Step 5, "(Letting ε ↓ 0.)", of the accepted natural-language proof of the parent node `root.constancy-a1.local_on_balls-a1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_local_on_balls`

#### `constancy_approx_identity_iteratedFDeriv_tendstoUniformly` (L41797)

- `root.constancy-a1.mollifier_derivative_convergence-a1` · issue #967 · PR #1629 · candidate `933d7e87b08b`
- **Statement and proof**: Simon Ch. 6, proof of Theorem 2.34 (p. 143): mollifications of a test function converge to it in the test-function topology.  For a nonnegative approximate identity `ψ k` (`∫ ψ k = 1`, `spt ψ k ⊆ B̄_{r k}(0)`, `r k → 0`) and `b` smooth with compact support, every derivative `D^q (ψ k ∗ b)` converges to `D^q b` uniformly on `ℝⁿ`.  The derivatives fall on `b`, `D^q (ψ ∗ b) = ψ ∗ D^q b` (induction on `q` with `hasFDerivAt_convolution_right`; the currying isometries commute with the integral), and `D^q b` is uniformly continuous, so `dist_convolution_le` gives the uniform estimate.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_local_on_balls`

#### `constancy_closed_kills_partial_derivatives` (L16987)

- `root.constancy-a1.closed_kills_partials-a1` · issue #964 · PR #1645 · candidate `469f013363ea`
- **Statement and proof**: Simon Ch. 6, proof of Theorem 2.34 (p. 143): a closed current kills `(D_j a) dx¹ ∧ ⋯ ∧ dxⁿ`. The test form `η = a · ι_{e_j} dx` (the book's `ω_j = (−1)^{j−1} a dx¹ ∧ ⋯ ∧ dx̂ʲ ∧ ⋯ ∧ dxⁿ`) has `dη(x)(e) = D_j a(x) = ω(x)(e)`.  Top-degree covectors are determined by their value on the standard basis `e`, so `dη = ω` and `T ω = T (dη) = ∂T η = 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `constancy_theorem`

### A.3 Theorem 8.1 (§3.3): `rectifiability_theorem` and its 57 further declarations

#### `rectifiability_theorem` (L62437)

- `root.rectifiability-a1` · issue #340 · PR #5445 · candidate `ba8a5544bc76`
- **Statement and proof**: **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  By (1)–(8) of the printed proof the mass measure is `μ = θ Hⁿ ⌞ M` with `M` countably `n`-rectifiable and `θ > 0` locally `Hⁿ`-integrable on `M`; by (2.7)–(2.8) `T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|ξ| = 1` `μ`-a.e., so `T = τ(M, θ, ξ)` (9); and by (10)–(13) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the weighted approximate tangent space `TₓM`, for `Hⁿ`-a.e. `x ∈ M`.  (Book `n = m + 1`.)
- **Calls**: `rectifiability_mass_measure_rectifiable`, `rectifiability_mass_measure_representation`, `rectifiability_orientation`
- **Called by**: `integrality_of_weak_limits`, `main_theorem`

#### `rectifiability_mass_measure_rectifiable` (L62354)

- `root.rectifiability-a1.mass_measure_rectifiable-a1` · issue #1041 · PR #5390 · candidate `15bc3161e8f8`
- **Statement and proof**: Simon Ch. 6, proof of 8.1, (1)–(8) (pp. 173–174): if `M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` **[corrected]** and `Θ*ⁿ(μ, x) > 0` for `μ`-a.e. `x`, the mass measure `μ` of `T` is `θ Hⁿ ⌞ M` for a Borel, countably `n`-rectifiable `M ⊆ U` and a Borel `θ`, positive on `M` and locally `Hⁿ`-integrable in `U`.  A Borel carrier `B₀ ⊆ U ∩ {Θ*ⁿ(μ, ·) > 0}` of `μ` is `Hⁿ`-σ-finite; in its decomposition `B₀ = R ∪ P'` (Ch. 3, Lemma 3.2) the purely unrectifiable part `P'` is `μ`-null by the structure theorem and Remark 2.37(2), hence `Hⁿ`-null; Radon–Nikodym for `μ ≪ Hⁿ ⌞ B₀` then gives `M` and `θ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves implicit the hypothesis of 8.1 that `M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, which the Lean statement (line 62354) assumes and the proof needs (Lemma 2.36 uses the bound on `∂T`).
- **Calls**: `cmb_exists_compactly_contained_exhaustion` (A.1), `rectifiability_mass_measure_abs_continuous`, `rectifiability_positive_density_cover_null`, `rectifiability_structure_projection`, `rectifiability_projection_null`, `rectifiability_rn_positive_real_density`
- **Called by**: `rectifiability_theorem`

#### `rectifiability_mass_measure_abs_continuous` (L54283)

- `root.rectifiability-a1.mass_measure_abs_continuous-a1` · issue #1023 · PR #4950 · candidate `f5968e33198f`
- **Statement and proof**: **Simon Ch. 6, Remark 2.37(1) (p. 144).**  If `M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, the mass measure `μ_T` is absolutely continuous with respect to `Hⁿ`.  Each coordinate projection `p_α` is 1-Lipschitz, so a Borel set `B` with `Hⁿ(B) = 0` has `Lⁿ(p_α(B)) = Hⁿ(p_α(B)) ≤ Hⁿ(B) = 0` for every `α`, and Lemma 2.36 (`projection_null`, with `Q = id`) gives `μ_T(B) = 0`; an arbitrary `Hⁿ`-null set lies in a Borel `Hⁿ`-null set.  (Book `n = m + 1`.)
- **Calls**: `rectifiability_projection_null`
- **Called by**: `rectifiability_mass_measure_rectifiable`

#### `rectifiability_projection_null` (L54258)

- `root.rectifiability-a1.projection_null-a1` · issue #1021 · PR #4899 · candidate `63af27b0b88c`
- **Statement and proof**: **Simon Ch. 6, Lemma 2.36 with Remarks 2.37(1)–(2) (pp. 144–145).**  Let `T ∈ 𝒟ₙ(U)`, `n = m + 1`, satisfy `M_W(T) + M_W(∂T) < ∞` for every `W ⊂⊂ U`, let `μ = μ_T` be its mass measure and `Q` a linear isometry of `ℝ^P`.  If `E` is Borel and `Lⁿ(p_α(Q(E))) = 0` for every `α ∈ I(n, P)`, then `μ(E) = 0`.  (2.37(2) prints `Lⁿ(Q(E)) = 0`; the projections `p_α ∘ Q` are meant.)  With `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `|ξ| = 1` `μ`-a.e. (2.7–2.8), printed (1)–(4) give `μ(W) = M_W(T) ≤ C μ(W ∖ K)` for every compact `K ⊆ E` and open `W ⊂⊂ U`; letting `W ↓ K` gives `μ(K) = 0`, and inner regularity (Ch. 1, 1.15) extends this to `E`.
- **Calls**: `rectifiability_mass_measure_representation`, `rpn_null_of_compact_null`, `rpn_massOn_le_mul_measure_diff`, `rpn_compact_null_of_le_mul_diff`
- **Called by**: `rectifiability_mass_measure_abs_continuous`, `rectifiability_mass_measure_rectifiable`

#### `rectifiability_mass_measure_representation` (L18946)

- `root.rectifiability-a1.mass_measure_representation-a1` · issue #1019 · PR #1843 · candidate `b4c070e13355`
- **Statement and proof** (no doc comment in the source; summary of the accepted natural-language proof): **Simon Ch. 6, (2.7)–(2.8).** If `M_W(T) < ∞` for every `W ⊂⊂ U`, then (i) `T` has a mass measure `μ` (`IsMassMeasure T μ`), and (ii) for every mass measure `μ` there is a strongly measurable `k`-vector field `ξ` with `∑_α ξ(x)(dx^α)² = 1` for `μ`-a.e. `x` and `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` for every test form (`IsMeasureRepresentation T μ ξ`). Proof: identify `k`-covectors and `k`-vectors isometrically with `ℝ^N` through their coordinates on increasing multi-indices (if `k > P`, then `T = 0` and `μ = 0`); extend `T`, by the mass bound and uniform approximation of continuous forms by test forms, to a locally bounded linear functional on continuous compactly supported forms in `U`; SimonGMT's vector Riesz theorem (Simon Ch. 1, 4.14) gives a Radon measure `μ_T` and a unit field with `μ_T(W) = sup{L(g) : |g| ≤ 1, spt g ⊆ W}`, which equals `M_W(T)` for open `W ⊂⊂ U`; any mass measure agrees with `μ_T(· ∩ U)` on the π-system of open `W ⊂⊂ U` together with the Borel sets missing `U`, which generates the Borel sets and has a countable cover of finite measure, hence equals it; a Borel unit version of the field gives `ξ`.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `cmb_exists_compactly_contained_exhaustion` (A.1), `cmb_abs_apply_le_of_massOn_le` (A.1), `cmb_exists_testForm_uniform_approx` (A.1), `br_la_apply_eq_zero_of_lt_degree`
- **Called by**: `deformation_mass_restriction`, `rectifiability_orientation`, `rectifiability_projection_null`, `rectifiability_theorem`

#### `br_la_apply_eq_zero_of_lt_degree` (L3440)

- `root.boundary_rectifiability-a1.lattice_approximation-a1.low_degree_vanish-a1` · issue #1191 · PR #1555 · candidate `5e97e54b7c48`
- **Statement and proof**: Currents of degree `n > P` in `ℝ^P` vanish (step 1 of the accepted natural-language proof of `br_lattice_approximation`, the finite-mass case of Simon Ch. 6, 6.2 used for 6.3 **[corrected]**): any `n` vectors of `ℝ^P` are linearly dependent, so every `n`-covector is `0`, every test form is `0`, and `X(ω) = X(0) = 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 1 of the proof of Simon Ch. 6, 6.2". The printed proof of 6.2 (pp. 169–170) has no such step; the case `P < m + 1` is step 1 of the accepted proof of the parent node `root.boundary_rectifiability-a1.lattice_approximation-a1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_mass_measure_representation`, `br_lattice_approximation`

#### `rpn_null_of_compact_null` (L3988)

- `root.rectifiability-a1.projection_null-a1.borel_null-a1` · issue #2462 · PR #3116 · candidate `58ab32bdb910`
- **Statement and proof**: Simon Ch. 6, end of the proof of Lemma 2.36 and Remark 2.37(1), via Ch. 1, 1.15(2): if `U` is open, `μ(ℝ^P ∖ U) = 0` and `μ(W) < ∞` for every `W ⊂⊂ U`, then a Borel set `E` whose compact subsets inside `U` are all `μ`-null is itself `μ`-null.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_projection_null`

#### `rpn_massOn_le_mul_measure_diff` (L3721)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1` · issue #2448 · PR #4819 · candidate `7bfb5ff2b576`
- **Statement and proof**: **Mass off a compact set with null projections (Simon Ch. 6, proof of Lemma 2.36, displays (1)–(3), run for `Q_#T` as in Remark 2.37(2)).**  Let `T ∈ 𝒟ₙ(U)` (`n = m + 1`) have `M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and be represented by `(μ, ξ)` with `Σ_β ξ(x)(dx^β)² = 1` for `μ`-a.e. `x`.  If `K` is compact and `Lⁿ(π_α(K)) = 0` for every `α ∈ I(n, P)`, where `π_α(x) = ((Qx)_{α(0)}, …, (Qx)_{α(m)})`, then `M_W(T) ≤ C μ(W∖K)` for every open `W ⊂⊂ U`.  Each admissible `ω` expands as `Σ_α ω_α θ_α` with `ω_α = ω(Q⁻¹e_α)` and `θ_α = Q^*dx^α` (the top form of `π_α`).  For each `α` the cut-off estimate gives `|T(ω_α θ_α)| ≤ c_α c'_α μ(W∖K)`, with `c_α = Σ_β |dx^β(Q⁻¹e_α)|` and `c'_α = Σ_β |θ_α(e_β)|`.
- **Calls**: `rpn_moc_abs_nvector_apply_le`, `rpn_moc_abs_covector_apply_le`, `rpn_moc_exists_testForm_smul`, `rpn_covector_rotated_expansion`, `rpn_moc_abs_apply_top_form_le`, `rpn_pullback_top_form_bound`, `rpn_null_compact_cutoff`
- **Called by**: `rectifiability_projection_null`

#### `rpn_moc_abs_nvector_apply_le` (L2652)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.nvector_pairing_bound-a1` · issue #3346 · PR #4030 · candidate `cbeda6fb55c2`
- **Statement and proof**: Pairing bound for a unit `n`-vector on `ℝ^P`: if `∑_β w(dx^β)² = 1`, then `|w(θ)| ≤ ∑_β |θ(e_{β(0)}, …, e_{β(n-1)})|`.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1)
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `rpn_moc_abs_covector_apply_le` (L2632)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.covector_eval_bound-a1` · issue #3337 · PR #3967 · candidate `cc8052a37b59`
- **Statement and proof**: Evaluation bound for an `n`-covector at an arbitrary tuple of vectors: `|φ(v)| ≤ (∑_β |dx^β(v)|) · |φ|`, summing over the increasing multi-indices `β`.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `cmb_rb_abs_euclideanCovectorCoordinate_le` (A.1)
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `rpn_moc_exists_testForm_smul` (L2675)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.scalar_test_form-a1` · issue #3352 · PR #3955 · candidate `66a361cb9eac`
- **Statement and proof**: A smooth compactly supported `f` with `tsupport f ⊆ U` times a constant `n`-covector `θ` is a test form in `𝒟ⁿ(U)`: `φ(x) = f(x) θ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_moc_abs_apply_top_form_le`, `rpn_massOn_le_mul_measure_diff`

#### `rpn_covector_rotated_expansion` (L3664)

- `root.rectifiability-a1.projection_null-a1.covector_rotated_expansion-a1` · issue #2428 · PR #3507 · candidate `3eab42406376`
- **Statement and proof**: **Rotated coordinate expansion of a covector (Simon Ch. 6, 1.2; Lemma 2.36, Remark 2.37(2)).** For a linear isometry `Q` of `ℝ^P`, every `n`-covector expands as `φ = ∑_α φ(Q⁻¹e_{α(0)}, …, Q⁻¹e_{α(n-1)}) Q^*dx^α`, where `Q^*dx^α = (dx^{α(0)} ∘ Q) ∧ ⋯ ∧ (dx^{α(n-1)} ∘ Q)`.  The pull-back `φ' = (Q⁻¹)^*φ` has coordinates `φ'(e_α) = φ(Q⁻¹e_α)`, so the Kronecker property `dx^α(e_I) = δ_{αI}` gives `φ' = ∑_α φ'(e_α) dx^α` on increasing coordinates, hence everywhere.  Pulling back by `Q` gives `φ = Q^*φ'`.
- **Calls**: `polyhedral_approx_pairing_covector_ext`, `polyhedral_approx_pairing_wedge_kronecker`
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `polyhedral_approx_pairing_covector_ext` (L3637)

- `root.polyhedral_approximation-a1.pairing_expansion-a1.covector_ext-a1` · issue #1060 · PR #1928 · candidate `564fb5ea9012`
- **Statement and proof**: An `n`-covector on `ℝ^P` is determined by its coordinates on increasing multi-indices (Simon Ch. 6, 1.2): if `α(e_{I(0)}, …, e_{I(n-1)}) = β(e_{I(0)}, …, e_{I(n-1)})` for every increasing `I`, then `α = β`.  Alternating maps agreeing on injective tuples of basis vectors are equal; sorting an injective tuple `v` by `σ = Tuple.sort v` gives the increasing `I = v ∘ σ`, and `e_v = e_I ∘ σ⁻¹` gives `γ(e_v) = sign(σ⁻¹) γ(e_I)` for `γ = α, β`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_covector_rotated_expansion`, `polyhedral_approx_pairing_expansion`

#### `polyhedral_approx_pairing_wedge_kronecker` (L3601)

- `root.polyhedral_approximation-a1.pairing_expansion-a1.wedge_kronecker-a1` · issue #1059 · PR #1963 · candidate `4f8cb90675e5`
- **Statement and proof**: **Kronecker duality of coordinate wedges (Simon Ch. 6, 1.1–1.2).**  For an increasing multi-index `I`, `dx^I = dx^{I₁} ∧ ⋯ ∧ dx^{Iₙ}` has coordinate `1` at `I` and `0` at every increasing `J ≠ I`: by (1.1), `dx^I(e_{J₁}, …, e_{Jₙ}) = det [I i = J j]`.  For `J = I` this matrix is the identity, as `I` is injective.  For `J ≠ I` some `I i ∉ range J` (otherwise the finite ranges, of equal cardinality, coincide, and increasing enumerations with equal ranges are equal), so row `i` vanishes.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_covector_rotated_expansion`, `polyhedral_approx_pairing_expansion`

#### `rpn_moc_abs_apply_top_form_le` (L2723)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.top_form_estimate-a1` · issue #3366 · PR #4087 · candidate `c3b9daddd1cc`
- **Statement and proof**: Cut-off estimate for the top-degree form `f θ_L`, `θ_L = L^*(dy¹ ∧ ⋯ ∧ dyⁿ)` (Simon Ch. 6, proof of Lemma 2.36, display (2)): from the pullback bound (H1) and cut-offs `b = 1` on `L(K)` with `𝓛ⁿ(spt b)` arbitrarily small (H2), `|T(f θ_L)| ≤ c c' μ(W \ K)`.
- **Calls**: `rpn_moc_exists_testForm_smul`, `rpn_moc_abs_apply_le_mul_measure_diff`
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `rpn_moc_abs_apply_le_mul_measure_diff` (L2685)

- `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1.remainder_bound-a1` · issue #3361 · PR #3951 · candidate `6b2bcfc06b11`
- **Statement and proof**: Representation estimate on `W \ K`: if `φ = h • θ` where `|h| ≤ c`, `h = 0` off `W` and on `K`, and `|ξ(x)(θ)| ≤ c'` for `μ`-a.e. `x`, then `|T φ| ≤ c c' μ(W \ K)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_moc_abs_apply_top_form_le`

#### `rpn_pullback_top_form_bound` (L3466)

- `root.rectifiability-a1.projection_null-a1.pullback_top_form_bound-a1` · issue #2415 · PR #4672 · candidate `63289e938b29`
- **Statement and proof**: Simon Ch. 6, the estimate behind Lemma 2.36 (via Remark 2.35), for a linear map `L : ℝ^P → ℝⁿ`, `n = m + 1`: if `M_W(T), M_W(∂T) < ∞` and `f` is a smooth compactly supported cutoff with `tsupport f ⊆ W`, then every test form `φ = f · (a ∘ L) · L^*dy` satisfies `|T(φ)| ≤ C · M · Lⁿ(spt a)^{1/n}` whenever `|a| ≤ M`, with `C` independent of `a`, `M`, `φ`. Write `a = ∑ⱼ ∂ⱼψⱼ` with `|ψⱼ| ≤ R = C₁ M Lⁿ(spt a)^{1/n}` (`rpn_potential_estimate`) and `Φ = ∑ⱼ (-1)ʲ f (ψⱼ ∘ L) θⱼ`, `θⱼ = ⋀_{i ≠ j} (yⁱ ∘ L)`.  Then `dΦ = φ + Ξ` with `Ξ = ∑ⱼ (-1)ʲ (ψⱼ ∘ L) Df ∧ θⱼ` (`rpn_extDeriv_potential_form`), so `T(φ) = ∂T(Φ) - T(Ξ)`, and both terms are bounded through `M_W(∂T)` and `M_W(T)` (`rpn_abs_apply_le_opNorm_mul_massOn`).
- **Calls**: `rpn_potential_estimate`, `rpn_extDeriv_potential_form`, `rpn_abs_apply_le_opNorm_mul_massOn`
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `rpn_potential_estimate` (L3205)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1` · issue #2387 · PR #4510 · candidate `7a14a1d4d1a3`
- **Statement and proof**: **Potential estimate (replaces Simon Ch. 6, Remark 2.35; Gilbarg–Trudinger, Lemma 7.14 and §7.8).**  For `n = m + 1`, `ω_n = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)` with `|a| ≤ M`, the potentials `ψ_j(y) = ∫ K_j(t) a(y - t) dt` of the kernels `K_j(t) = t_j / (n ω_n |t|ⁿ)` are `C^∞`, satisfy `∑_j ∂_j ψ_j = a` and `|ψ_j| ≤ C M Lⁿ(spt a)^{1/n}` with `C` depending only on `m`.  The kernels are locally integrable, so `ψ_j` is smooth with `∂_k ψ_j = K_j ⋆ ∂_k a`; summing `∂_j ψ_j` over `j` gives `a` by the representation formula, and the bound is the kernel sup estimate.
- **Calls**: `rpn_pe_kernel_locallyIntegrable`, `rpn_pe_convolution_contDiff_fderiv`, `rpn_pe_kernel_representation`, `rpn_pe_kernel_sup_bound`
- **Called by**: `rpn_pullback_top_form_bound`

#### `rpn_pe_kernel_locallyIntegrable` (L2991)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_local_integrable-a1` · issue #3309 · PR #4124 · candidate `1760770a16a1`
- **Statement and proof**: The kernels `K(w) = w_j / (c|w|^{m+1})` on `ℝ^{m+1}` are locally integrable. This is Step 2 of the potential estimate (Gilbarg–Trudinger §7.8) that replaces the BV argument of Simon Ch. 6, Remark 2.35 in the proof of 8.1; there `c = nωₙ`. With `x / 0 = 0`, `|K(w)| ≤ |c|⁻¹ (|w|^m)⁻¹` everywhere, and `(|w|^m)⁻¹` is integrable on every ball about `0` (`Submission.rpn_pe_inv_norm_pow_ball`).
- **Calls**: `rpn_pe_inv_norm_pow_ball`
- **Called by**: `rpn_pe_kernel_representation`, `rpn_potential_estimate`

#### `rpn_pe_inv_norm_pow_ball` (L2862)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.radial_ball_integral-a1` · issue #3283 · PR #3917 · candidate `8c5c1649b711`
- **Statement and proof**: The radial integral `∫_{B_ρ(0)} |w|^{1-n} dw = n ω_n ρ` in `ℝⁿ`, `n = m + 1`, `ρ > 0`, `ω_n = Lⁿ(B_1(0))` (formula (R) of the potential estimate in the proof of Simon Ch. 6, 8.1); `|w|^{1-n}` is written `(‖w‖ ^ m)⁻¹`.  In polar coordinates (`integrableOn_fun_norm_addHaar`, `integral_fun_norm_addHaar`) the radial profile `r^{n-1} (r^{n-1})⁻¹` is `1` on `(0, ρ)`: this gives integrability, and with `1_{B_ρ(0)}(w) = 1_{(-∞, ρ)}(|w|)` the value `n ω_n ρ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pe_inv_norm_pow_set_bound`, `rpn_pe_kernel_locallyIntegrable`

#### `rpn_pe_convolution_contDiff_fderiv` (L3023)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.convolution_smooth-a1` · issue #3319 · PR #3979 · candidate `920181d0d005`
- **Statement and proof**: Convolution of a locally integrable kernel with a `C^∞` compactly supported function: `ψ(y) = ∫ K(t) a(y - t) dt` is `C^∞`, and for all `y, v`, `t ↦ K(t) Da(y - t)v` is integrable with `Dψ(y)v = ∫ K(t) Da(y - t)v dt`.  Here `ψ = K ⋆ a` for the pairing `lsmul ℝ ℝ`, so `HasCompactSupport.contDiff_convolution_right` gives smoothness, `convolutionExists_right` applied to the continuous compactly supported `z ↦ Da(z)v` gives integrability, and `hasFDerivAt_convolution_right` with `convolution_precompR_apply` gives the derivative.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pe_kernel_representation`, `rpn_potential_estimate`

#### `rpn_pe_kernel_representation` (L3075)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.representation-a1` · issue #3333 · PR #4288 · candidate `e2db51a6e54a`
- **Statement and proof**: **Representation formula (Gilbarg–Trudinger, §7.8, proof of Lemma 7.14).**  For `n = m + 1`, `ω = Lⁿ(B₁(0))` and `a ∈ C_c^∞(ℝⁿ)`, the kernels `K_j(t) = t_j / (n ω |t|ⁿ)` satisfy `∑_j ∫ K_j(t) ∂_j a(y - t) dt = a(y)`.  Expanding `t` in the standard basis, the sum is `∫ G` with `G(t) = Da(y - t) t / (n ω |t|ⁿ)`.  In polar coordinates `r^m G(rθ) = Da(y - rθ) θ / (n ω)`, so each ray integral is `a(y) / (n ω)` (fundamental theorem of calculus along the ray), and the unit sphere has measure `n ω`.
- **Calls**: `rpn_pe_convolution_contDiff_fderiv`, `rpn_pe_kernel_locallyIntegrable`, `rpn_pe_integral_eq_polar`, `rpn_pe_ray_ftc`
- **Called by**: `rpn_potential_estimate`

#### `rpn_pe_integral_eq_polar` (L2811)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.polar_integral-a1` · issue #3268 · PR #3914 · candidate `bfa69d4e2629`
- **Statement and proof**: Polar coordinates for an integrable `g` on `ℝ^{m+1}`, with `σ = (Lᵐ⁺¹).toSphere`: `∫ g = ∫_{S^m} ∫_0^∞ r^m g(rθ) dr dσ(θ)`.  As in Mathlib's `integral_fun_norm_addHaar`, `homeomorphUnitSphereProd` carries Lebesgue measure on `ℝ^{m+1} ∖ {0}` to `σ ⊗ volumeIoiPow m`, Fubini splits the product, and `volumeIoiPow m` is `r^m dr` on `(0, ∞)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pe_kernel_representation`

#### `rpn_pe_ray_ftc` (L3047)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.ray_ftc-a1` · issue #3323 · PR #3996 · candidate `cbc8f59ccd3b`
- **Statement and proof**: The fundamental theorem of calculus along a ray: for `a` of class `C¹` with compact support and `θ ≠ 0`, `∫_{(0,∞)} Da(y - rθ)θ dr = a(y)`.  The function `h(r) = a(y - rθ)` is `C¹` with `h'(r) = -Da(y - rθ)θ`.  It has compact support because `r ↦ y - rθ` is a closed embedding. So `HasCompactSupport.integral_Ioi_deriv_eq` gives `∫_{(0,∞)} h' = -h(0) = -a(y)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pe_kernel_representation`

#### `rpn_pe_kernel_sup_bound` (L3137)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.kernel_sup_bound-a1` · issue #3343 · PR #4318 · candidate `6d0076523601`
- **Statement and proof**: Sup bound for the kernel potentials (Step 5 of the potential estimate).  With `ω = Lⁿ(B₁(0))`, `c = (m + 1) ω` and `K_j(t) = t_j / (c |t|^{m+1})`, every compactly supported `a` with `|a| ≤ M` satisfies `|∫ K_j(t) a(y - t) dt| ≤ C M Lⁿ(spt a)^{1/(m+1)}` with `C = (m + 2) ω^{m/(m+1)} / c`.  Proof: `|K_j(t) a(y - t)| ≤ (M / c) 1_{S_y}(t) |t|^{-m}` on `S_y = {t : y - t ∈ spt a} = y − spt a`, the image of `spt a` under the measure-preserving map `s ↦ y − s`, so that `Lⁿ(S_y) = Lⁿ(spt a)` **[corrected]**; integrate and apply `rpn_pe_inv_norm_pow_set_bound` to `S_y`.  No measurability of `a` is needed.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), calls `S_y` "a translate of `spt a`". It is `y − spt a`, a translate of the reflection `−spt a`, and in general not a translate of `spt a` (for `n = 1`, `spt a = [0, 1] ∪ [2, 4]` and `y = 0`, `S_0 = [−4, −2] ∪ [−1, 0]`). The proof only uses `Lⁿ(S_y) = Lⁿ(spt a)`, which holds because `t ↦ y − t` preserves Lebesgue measure.
- **Calls**: `rpn_pe_inv_norm_pow_set_bound`
- **Called by**: `rpn_potential_estimate`

#### `rpn_pe_inv_norm_pow_set_bound` (L2902)

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1.set_integral_bound-a1` · issue #3297 · PR #4125 · candidate `40d791a916ac`
- **Statement and proof**: Potential estimate over a set of finite measure (Gilbarg–Trudinger, proof of Lemma 7.12, with the cruder constant `n + 1`): for measurable `S ⊆ ℝⁿ`, `n = m + 1`, with `Lⁿ(S) < ∞`, the kernel `|w|^{1-n} = (|w|^m)⁻¹` is integrable on `S` and `∫_S |w|^{1-n} dw ≤ (n + 1) ω^{(n-1)/n} Lⁿ(S)^{1/n}`, `ω = Lⁿ(B_1(0))`.  Split `S` at the radius `ρ = (Lⁿ(S)/ω)^{1/n}`: the part inside `B_ρ(0)` contributes at most `∫_{B_ρ(0)} |w|^{1-n} = nωρ`, the part outside at most `ρ^{1-n} Lⁿ(S) = ωρ`.
- **Calls**: `rpn_pe_inv_norm_pow_ball`
- **Called by**: `rpn_pe_kernel_sup_bound`

#### `rpn_extDeriv_potential_form` (L3339)

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1` · issue #2396 · PR #4117 · candidate `a5ff80bf4604`
- **Statement and proof**: Exterior derivative of the pulled-back potential form (Simon Ch. 6, 1.14 and the divergence identity `dψ̂ = (div ψ) dy` of Remark 2.35).  For `λᵢ = yⁱ ∘ L`, `θⱼ = λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ` and `Φ(z) = ∑ⱼ (-1)ʲ f(z) ψⱼ(Lz) θⱼ`, `dΦ(x) = f(x) (∑ⱼ ∂ⱼψⱼ(Lx)) λ₀ ∧ ⋯ ∧ λₘ + ∑ⱼ (-1)ʲ ψⱼ(Lx) Df(x) ∧ θⱼ`.
- **Calls**: `rpn_pfd_extDeriv_sum_smul_wedge`, `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_wedge_cons_comp_succAbove`
- **Called by**: `rpn_pullback_top_form_bound`

#### `rpn_pfd_extDeriv_sum_smul_wedge` (L3280)

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.extderiv_sum_wedge-a1` · issue #3043 · PR #3685 · candidate `abdbf10e529f`
- **Statement and proof**: `d(∑ⱼ gⱼ θⱼ) = ∑ⱼ dgⱼ ∧ θⱼ` for constant covectors `θⱼ = βⱼ,₀ ∧ ⋯ ∧ βⱼ,ₘ₋₁` (Simon Ch. 6, (1.11), p. 134: `d(a dx^α) = da ∧ dx^α`, with general constant one-covectors `βⱼ` in place of the coordinate differentials).  `extDeriv Φ x = Alt (DΦ(x))` only needs `gⱼ` differentiable at `x`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_extDeriv_potential_form`

#### `rpn_pfd_wedge_cons_isLinearMap` (L3227)

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_linear-a1` · issue #3016 · PR #3705 · candidate `ba0b2468925a`
- **Statement and proof**: The wedge `γ ∧ β₀ ∧ ⋯ ∧ β_{m-1}` is linear in its first factor `γ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pfd_wedge_cons_comp_succAbove`, `rpn_extDeriv_potential_form`

#### `rpn_pfd_wedge_cons_comp_succAbove` (L3297)

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.divergence_term-a1` · issue #3053 · PR #3923 · candidate `c036e4d501ae`
- **Statement and proof**: One term of the divergence identity of Simon Ch. 6, 2.35 (`dω = div a dx¹ ∧ ⋯ ∧ dxⁿ`), pulled back by a linear `L : ℝ^P → ℝ^{m+1}`: for `λᵢ = yⁱ ∘ L` and `ℓ ∈ (ℝ^{m+1})*`, `(ℓ ∘ L) ∧ λ₀ ∧ ⋯ ∧ λ̂ⱼ ∧ ⋯ ∧ λₘ = (-1)ʲ ℓ(eⱼ) λ₀ ∧ ⋯ ∧ λₘ`.  Expand `ℓ ∘ L = ∑ᵢ ℓ(eᵢ) λᵢ`; the wedge is linear in its first factor, and by the sign lemma only the term `i = j` survives.
- **Calls**: `rpn_pfd_wedge_cons_isLinearMap`, `rpn_pfd_wedge_cons_succAbove_sign`
- **Called by**: `rpn_extDeriv_potential_form`

#### `rpn_pfd_wedge_cons_succAbove_sign` (L3249)

- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_sign-a1` · issue #3030 · PR #3700 · candidate `3ceb8b21a8d3`
- **Statement and proof**: Sign lemma for wedges of one-covectors: moving the factor `l j` to the front costs `(-1)^j`, while putting another factor `l i` (`i ≠ j`) in front repeats a factor.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_pfd_wedge_cons_comp_succAbove`

#### `rpn_abs_apply_le_opNorm_mul_massOn` (L3411)

- `root.rectifiability-a1.projection_null-a1.mass_bound_opnorm-a1` · issue #2404 · PR #3430 · candidate `e20ff737992d`
- **Statement and proof**: Mass estimate with the operator norm: if `M_W(T) ≤ B` and `ω` is supported in `W` with `‖ω(x)‖ ≤ C` everywhere (operator norm), then `|T(ω)| ≤ P^n · B · C`, because the Euclidean coefficient norm is at most `√(P^n) · ‖·‖ ≤ P^n · ‖·‖`.
- **Calls**: `fiw_ims_sc_covectorNorm_le_opNorm`, `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `rpn_pullback_top_form_bound`

#### `fiw_ims_sc_covectorNorm_le_opNorm` (L3381)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.covector_norm-a1` · issue #1892 · PR #2299 · candidate `c8cb71851ed3`
- **Statement and proof**: The Euclidean coefficient norm of an `n`-covector on `ℝ^P` is at most `√(P^n)` times its operator norm: each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` (`b` the standard orthonormal basis) is bounded by `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_abs_apply_le_opNorm_mul_massOn`, `fiw_ims_sc_testForm_bounded`, `fiw_ims_sc_converges_zero_small`

#### `rpn_null_compact_cutoff` (L3695)

- `root.rectifiability-a1.projection_null-a1.null_compact_cutoff-a1` · issue #2441 · PR #3150 · candidate `bba2aab98b8e`
- **Statement and proof**: Smooth cutoffs for a compact Lebesgue-null set (Simon Ch. 6, proof of Lemma 2.36, display (2)): if `F ⊆ ℝ^N` is compact with `Lᴺ(F) = 0` and `δ > 0`, there is a `C^∞` function `b : ℝ^N → [0, 1]` with compact support, `b = 1` on `F` and `Lᴺ(spt b) ≤ δ`.  By outer regularity pick an open `G ⊇ F` with `Lᴺ(G) < δ`, then an open `V` with `F ⊆ V ⊆ closure V ⊆ G` and `closure V` compact, and a smooth Urysohn function equal to `1` on `F` and to `0` off `V`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rpn_massOn_le_mul_measure_diff`

#### `rpn_compact_null_of_le_mul_diff` (L3812)

- `root.rectifiability-a1.projection_null-a1.compact_null-a1` · issue #2454 · PR #3085 · candidate `29906e26815f`
- **Statement and proof**: Shrinking neighbourhoods (Simon Ch. 6, proof of Lemma 2.36, after (4)): if `K ⊆ U` is compact, `μ(W) < ∞` and `μ(W) ≤ C μ(W ∖ K)` for every open `W ⊂⊂ U`, then `μ(K) = 0`.  The thickenings `W_q = {dist(·, K) < r₀/(q+1)}` are `⊂⊂ U` and decrease to `K`, so continuity from above gives `μ(K) ≤ μ(W_q) ≤ C μ(W_q ∖ K) → 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_projection_null`

#### `rectifiability_positive_density_cover_null` (L61617)

- `root.rectifiability-a1.mass_measure_rectifiable-a1.positive_density_cover_null-a1` · issue #2490 · PR #3417 · candidate `d5eadc8d2eab`
- **Statement and proof**: Simon Ch. 6, proof of 8.1, (1) and (6): a set `S` of positive upper density `Θ*ⁿ(ν, ·)`, covered by open sets `W q` of finite `ν`-measure, is covered by countably many sets of finite `Hⁿ`-measure, and it is `Hⁿ`-null when it is `ν`-null.  The pieces `{x ∈ S ∩ W q : (j + 1)⁻¹ ≤ Θ*ⁿ(ν, x)}` are controlled by the density comparison with `V = W q`, and, when `ν(S) = 0`, with `V = O ∩ W q` for an open `O ⊇ S` given by outer regularity of the finite measure `ν ⌞ W q`.
- **Calls**: `rectifiability_density_comparison`
- **Called by**: `rectifiability_mass_measure_rectifiable`

#### `rectifiability_density_comparison` (L32149)

- `root.rectifiability-a1.density_comparison-a1` · issue #1025 · PR #1661 · candidate `c5336e1a1413`
- **Statement and proof**: Simon Ch. 1, Theorem 3.3 (with `A₁ = A`, `A₂ = V`): if `Θ*ⁿ(ν, x) ≥ t` on `A ⊆ V`, `V` open, then `t Hⁿ(A) ≤ ν(V)`.  The isodiametric inequality (coordinate Steiner symmetrization) shows that a closed ball of radius `r` has `μHE[n]`-cost at most `ωₙ rⁿ`, and the five-times covering argument with its finite-tail step bounds `μHE[n](A)` by the cost of a disjoint family of balls `B̄ ⊆ V` with `τ ωₙ rⁿ ≤ ν(B̄)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_imc_normalized_lebesgue_points`, `rectifiability_orientation`, `rectifiability_positive_density_cover_null`, `rectifiability_bf_projection_null_ae`

#### `rectifiability_structure_projection` (L61823)

- `root.rectifiability-a1.structure_projection-a1` · issue #1034 · PR #5322 · candidate `2fe9c1f38968`
- **Statement and proof**: **Simon Ch. 3, Structure Theorem 3.6, as used in Ch. 6, 8.1 (p. 174).**  If `A ⊆ ℝ^P` is purely `n`-unrectifiable and `Hⁿ`-σ-finite (`n = m + 1`), then some rotation `Q` makes every coordinate projection `p_α(Q(A))`, `α ∈ I(n, P)`, Lebesgue-null.  Up to an `Hⁿ`-null set, `A` is covered by countably many compact purely unrectifiable sets of finite measure, which lie in Borel hulls `B_j` of the pieces `A ∩ S_j` and not necessarily in `A`; their images under `x ↦ (⟪vᵢ, x⟫)ᵢ` are null for almost every frame `v` (`rectifiability_bf_projection_null_ae`), and so is the image of the `Hⁿ`-null rest of `A`, because a linear map is Lipschitz **[corrected]**.  Gram–Schmidt applied to a random frame, together with Tonelli's theorem, gives an orthonormal frame all of whose coordinate subframes avoid the null set of bad frames.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Up to an `Hⁿ`-null set, `A` is a countable union of compact purely unrectifiable pieces of finite measure". The statement does not assume that `A` is measurable, and for a non-measurable `A` this is false, because a set that differs from a countable union of compact sets by an `Hⁿ`-null set is `Hⁿ`-measurable. For example, let `C ⊆ ℝ²` be the four-corner Cantor set of Ch. 3, 3.5 (p. 79): it is compact and purely 1-unrectifiable, with `0 < H¹(C) < ∞`. Any non-`H¹`-measurable `A ⊆ C` satisfies the hypotheses. Such a set exists because `H¹⌞C` is a non-zero, finite, atomless Borel measure. The Lean proof covers `A` instead of decomposing it. This happens in its block "Step 2" (step 2 of the accepted natural-language proof, which uses Borel hulls as the proof of Ch. 3, Lemma 3.2, p. 78, does) and in its final block "Steps 4 and 3(d)" (step 3(d) of that proof).
  - *Hulls.* The hypothesis gives sets `S_j` with `A ⊆ ⋃_j S_j` and `Hⁿ(S_j) < ∞`. Put `A_j = A ∩ S_j` and `B_j = toMeasurable Hⁿ A_j`. This is a Borel set containing `A_j`, with `Hⁿ(B_j) = Hⁿ(A_j) < ∞` and `Hⁿ(B_j ∩ F) = Hⁿ(A_j ∩ F)` for every measurable `F` (Mathlib `Measure.measure_toMeasurable_inter`).
  - *The hulls are purely unrectifiable.* SimonGMT's `measurable_rectifiable_purelyUnrectifiable_decomposition` (Ch. 3, Lemma 3.2), which needs a measurable set and is therefore applied to `B_j` and not to `A_j`, gives `B_j = R_j ∪ P_j` with `R_j` measurable and countably `n`-rectifiable and `P_j` purely `n`-unrectifiable. Since `R_j ⊆ B_j`, `Hⁿ(R_j) = Hⁿ(B_j ∩ R_j) = Hⁿ(A_j ∩ R_j) = 0`, because `A_j ∩ R_j` is a countably rectifiable subset of `A`. So every countably rectifiable `T ⊆ B_j` has `Hⁿ(T) ≤ Hⁿ(R_j) + Hⁿ(T ∩ P_j) = 0`.
  - *Compact cores.* Inner regularity of the finite measure `Hⁿ⌞B_j` gives compact sets `C_{j,i} ⊆ B_j` with `Hⁿ(B_j ∖ ⋃_i C_{j,i}) = 0`. Each `C_{j,i}` is compact, purely unrectifiable and of finite measure, and `A ∖ ⋃_{j,i} C_{j,i} ⊆ ⋃_j (B_j ∖ ⋃_i C_{j,i})` is `Hⁿ`-null.
  - *Transfer to `A`.* Let `v` lie outside the null set of frames for which some `Lⁿ(L_v(C_{j,i}))` is positive. Then `L_v(A) ⊆ ⋃_{j,i} L_v(C_{j,i}) ∪ L_v(A ∖ ⋃_{j,i} C_{j,i})`. The last set is null, because `L_v` is linear, hence Lipschitz, Lipschitz maps send `Hⁿ`-null sets to `Hⁿ`-null sets (SimonGMT `euclideanHausdorffMeasure_image_le_of_lipschitzOn`), and `Hⁿ = Lⁿ` on `ℝⁿ`.

  The passage above is corrected accordingly. Here "rotation" means what the Lean statement provides: a linear isometry `Q` of `ℝ^P`, i.e. an orthogonal transformation, as in Simon's use of 3.6 on p. 174. The last sentence of the passage relies on one more property of the set `Z` of bad frames, proved in the Lean proof (Step 3(c) and the block `hZpre`) and used in its Steps 4–6: `Lⁿ(L_{Gv}(C)) = |det G| Lⁿ(L_v(C))` for every `n × n` matrix `G`, so `v ∈ Z` whenever the recombined frame `Gv` lies in `Z`. Since the first `n` Gram–Schmidt vectors of a frame recombine its first `n` vectors, they lie outside `Z` for almost every random frame (see §3.3).
- **Calls**: `rectifiability_bf_projection_null_ae`
- **Called by**: `rectifiability_mass_measure_rectifiable`

#### `rectifiability_bf_projection_null_ae` (L61719)

- `root.rectifiability-a1.bf_projection_null_ae-a1` · issue #1033 · PR #5265 · candidate `14ad28770cb6`
- **Statement and proof**: **Besicovitch–Federer projection theorem, finite-measure case** (Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 18.1; Hovila–Järvenpää–Järvenpää–Ledrappier, arXiv:1104.3453, Theorem 1.2).  Let `k = m + 1` and `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ`.  If `E ⊆ ℝ^N` is Borel and purely `k`-unrectifiable with `Hᵏ(E) < ∞`, then `Lᵏ(L_v(E)) = 0` for Lebesgue-a.e. `v ∈ (ℝ^N)ᵏ`.  After passing to a σ-compact core of `E`, the trichotomy splits `E`, up to an `Hᵏ`-null set, into the cone-density sets (`Hᵏ`-null), the points over which `(L_v)_# (Hᵏ ⌞ E)` has infinite density (Lebesgue-null image by density comparison) and the points with infinite `L_v`-fibres (Lebesgue-null image by Eilenberg finiteness).
- **Calls**: `lpf_lli_inner_compact_approx`, `rectifiability_bf_trichotomy`, `rectifiability_bf_cone_density`, `rectifiability_density_comparison`, `rectifiability_bf_infinite_fibre_null`
- **Called by**: `rectifiability_structure_projection`

#### `lpf_lli_inner_compact_approx` (L9590)

- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.inner_compact_approx-a1` · issue #980 · PR #1634 · candidate `d24e9e7b54d3`
- **Statement and proof**: Compact inner approximation: a `μ`-null-measurable `A ⊆ ℝ^P` with `μ ⌞ A` σ-finite is, up to a `μ`-null set, the union of countably many compact subsets of `A`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_locally_lipschitz_image`, `iwl_restriction_theory`, `rectifiability_bf_projection_null_ae`

#### `rectifiability_bf_trichotomy` (L61537)

- `root.rectifiability-a1.bf_trichotomy-a1` · issue #1031 · PR #5210 · candidate `21c4318dcfc4`
- **Statement and proof**: **Besicovitch–Federer trichotomy for almost every linear map** (Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9; Hovila–Järvenpää–Järvenpää–Ledrappier, arXiv:1104.3453, Lemma 2.5 **[corrected]**).  Let `k = m + 1`, `μ = Hᵏ⌞E`, `L_v x = (⟨v_i, x⟩)_i`, `X_v(a,r,s) = {x : |x − a| < r, |L_v(x − a)| < s|x − a|}` and `Φ(a,v) = limsup_{s↓0} sup_{0<r<δ} μ(X_v(a,r,s))/(rs)ᵏ`.  Fix `a`.  By Mickle–Radó on the slices `v ⊕_j c`, for a.e. `v` without a fibre witness (T3) every fibre density `ϑ_j(v)` lies in `{0, ∞}`, and `ϑ_j ≤ Φ ≤ N^{k/2} Σ_j ϑ_j` puts `Φ(a,v)` in `{0, ∞}`.  The set of such `(a,v)` is Borel, so Fubini gives the same for a.e. `v` and `μ`-a.e. `a`; `Φ = 0` is (T1) and `Φ = ∞` gives the infinite projected density (T2).
- **Correction**: the Lean doc comment, which is kept byte-identical as part of the accepted declaration text (§9), cites this as "Geom. Dedicata 161 (2012), Lemma 2.4". In the paper (arXiv:1104.3453, the version linked in §11), Definition 2.4 is the definition of transversality, and the trichotomy is Lemma 2.5, introduced as the analogue of Mattila's Lemma 18.9. It states that for a.e. parameter and `Hᵐ`-a.e. `a ∈ E`, the cone ratio is `0` (2.1) or `∞` (2.2), or `a` has another point of `E` near it in its fibre (2.3). The locator above is corrected accordingly. The citation is bibliographic only; the proof of this declaration does not depend on it.
- **Calls**: `rectifiability_bf_cone_ratio_measurable`, `rectifiability_bf_witness_set_measurable`, `rectifiability_bf_slice_density_null`, `rectifiability_bf_fibre_cone_comparison`, `rectifiability_bf_cone_ratio_reduction`
- **Called by**: `rectifiability_bf_projection_null_ae`

#### `rectifiability_bf_cone_ratio_measurable` (L60879)

- `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_measurable-a1` · issue #4591 · PR #5081 · candidate `7e1169c130d8`
- **Statement and proof**: **Borel measurability of the cone ratio** (steps 2(a)–(c) of the accepted natural-language proof of the Besicovitch–Federer trichotomy `rectifiability_bf_trichotomy`, cf. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9 **[corrected]**).  For `v ∈ (ℝ^N)^k`, `k = m + 1`, let `L_v y = (⟨v₁, y⟩, …, ⟨v_k, y⟩)` and `X_v(a, r, s) = {x : |x - a| < r, |L_v (x - a)| < s |x - a|}`.  Then `Φ(a, v) = limsup_{s → 0⁺} sup_{0 < r < δ} μ(X_v(a, r, s)) / (rs)ᵏ` is measurable in `(a, v)`: the cones are the sections of `G(r, s) = {((a, v), x) : |x - a| < r, |L_v (x - a)| < s |x - a|}`, which is open, monotone in `s` and left continuous in `r`, so `limsup_sup_measurable` applies.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 2(a)–(c) of the Besicovitch–Federer trichotomy, Mattila, …, Lemma 18.9". The step labels are those of the accepted proof of `rectifiability_bf_trichotomy`, not of Mattila's proof.
- **Calls**: `rectifiability_bf_limsup_sup_measurable`
- **Called by**: `rectifiability_bf_trichotomy`

#### `rectifiability_bf_limsup_sup_measurable` (L60653)

- `root.rectifiability-a1.bf_trichotomy-a1.limsup_sup_measurable-a1` · issue #4574 · PR #4999 · candidate `95211c7af512`
- **Statement and proof**: For an s-finite `μ` and measurable sets `G r s ⊆ Z × Y`, increasing in `s` and with `G r s = ⋃_{0<r'<r} G r' s` for `r > 0`, the map `z ↦ limsup_{s→0⁺} sup_{0<r<δ} μ{y | (z, y) ∈ G r s} / (r s)ᵏ` is measurable.  Each section measure is measurable in `z` (Tonelli).  By continuity from below along rational `r' < r` the supremum over `r` may be taken over rational `r`, and since `F(s) ≤ (s'/s)ᵏ F(s')` for `0 < s ≤ s'`, the supremum over `s ∈ (0, ε)` may be taken over rational `s`.  Computing the upper limit along the radii `1/(n+1)` then gives a countable `inf`–`sup` of measurable functions.
- **Calls**: `rectifiability_mickle_rado_limsup_eq_iInf`
- **Called by**: `rectifiability_bf_cone_ratio_measurable`, `rectifiability_bf_slice_density_null`

#### `rectifiability_mickle_rado_limsup_eq_iInf` (L60368)

- `root.rectifiability-a1.mickle_rado-a1.limsup_eq_iinf-a1` · issue #2489 · PR #3144 · candidate `cfa90d4234cc`
- **Statement and proof**: The upper limit of `f : ℝ → [0,∞]` at `0⁺` is computed along the radii `1/(n+1)`: `limsup_{t→0⁺} f(t) = inf_{n ∈ ℕ} sup_{0<t<1/(n+1)} f(t)`.  The intervals `(0, ε)`, `ε > 0`, form a basis of `𝓝[>] 0`, so the upper limit is `inf_{ε>0} sup_{(0,ε)} f`; each radius `1/(n+1)` is admissible, and every `ε > 0` exceeds some `1/(n+1)`, below which the supremum is smaller.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_mickle_rado`, `rectifiability_bf_limsup_sup_measurable`

#### `rectifiability_bf_witness_set_measurable` (L60801)

- `root.rectifiability-a1.bf_trichotomy-a1.witness_set_measurable-a1` · issue #4583 · PR #4977 · candidate `79eed5da6c76`
- **Statement and proof**: The parameter set of fibre witnesses (alternative T3 of the Besicovitch–Federer trichotomy in the proof of Simon Ch. 6, 8.1) is Borel.  For `E ⊆ ℝ^N` σ-compact, `δ ∈ ℝ` and `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`), the set `W` of `(a, v)` admitting `x ∈ E` with `x ≠ a`, `|x − a| < δ` and `L_v x = L_v a` is measurable.  With `E = ⋃ₙ Kₙ`, `Kₙ` compact, `W = ⋃_{n,l} π(C_{n,l})`, where `π(x, (a, v)) = (a, v)` and `C_{n,l}` is the compact set of `(x, (a, v))` with `x ∈ Kₙ`, `‖(a, v)‖ ≤ l`, `1/(l+1) ≤ |x − a| ≤ δ − 1/(l+1)` and `L_v x = L_v a`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_bf_slice_density_null`, `rectifiability_bf_trichotomy`

#### `rectifiability_bf_slice_density_null` (L61210)

- `root.rectifiability-a1.bf_trichotomy-a1.slice_density_null-a1` · issue #4612 · PR #5184 · candidate `1e007dff3e51`
- **Statement and proof**: **Slice densities of the exceptional parameters** (Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 18.9; for transversal families, Hovila–Järvenpää–Järvenpää–Ledrappier, arXiv:1104.3453, Lemma 2.5).  Let `k = m + 1`, `L_u y = (⟨u_i, y⟩)_i`, `w ⊕ c = (w_i + c_i e_j)_i`, `K_w(C) = {x ≠ a : L_{w ⊕ c}(x − a) = 0 for some c ∈ C}` and `ϑ_j(u) = limsup_{t↓0} sup_{0<r<δ} μ(B(a,r) ∩ K_u(B(0,t)))/(rt)ᵏ`.  Then the set `𝔅_j` of `u` with `0 < ϑ_j(u) < ∞` and no `x ∈ E` with `0 < |x − a| < δ` and `L_u x = L_u a` is Lebesgue-null. For fixed `w`, `ψ_w(C) = sup_{0<r<δ} μ(B(a,r) ∩ K_w(C))/rᵏ` is an outer measure on `ℝᵏ`, inner continuous on open balls, and vanishes on the Borel set `D_w` of those `c` for which `w ⊕ c` has no such `x`, because `μ(ℝ^N ∖ E) = 0`.  As `K_w(B(c,t)) = K_{w ⊕ c}(B(0,t))`, the upper `k`-density of `ψ_w` at `c` is `ϑ_j(w ⊕ c)`, so by the Mickle–Radó theorem `Lᵏ{c : w ⊕ c ∈ 𝔅_j} = 0` for every `w`.  `𝔅_j` is Borel, and Tonelli for `(w, c) ↦ w ⊕ c` in both orders, with translation invariance, gives `𝓛(𝔅_j) · ∞ = 0`.
- **Calls**: `rectifiability_bf_limsup_sup_measurable`, `rectifiability_bf_witness_set_measurable`, `rectifiability_mickle_rado`
- **Called by**: `rectifiability_bf_trichotomy`

#### `rectifiability_mickle_rado` (L60571)

- `root.rectifiability-a1.mickle_rado-a1` · issue #1029 · PR #3734 · candidate `751505bb8069`
- **Statement and proof**: **Mickle–Radó density theorem** (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439; Mattila, Thm 18.5).  Let `ψ` be an outer measure on `ℝᵏ`, `k = m + 1`, inner continuous on open balls, and `D` a Borel set with `ψ(D) = 0`.  Then the upper density `ϑ(c) = limsup_{t↓0} ψ(B(c,t))/tᵏ` lies in `{0, ∞}` at `Lᵏ`-a.e. point of `D`.  With `g_n(c) = sup_{0<t<1/(n+1)} ψ(B(c,t))/tᵏ`, each `g_n` is lower semicontinuous and `ϑ = inf_n g_n`, so `ϑ` is Borel.  The set `{c ∈ D : 0 < ϑ(c) < ∞}` is covered by the Borel sets `S_n = {c ∈ D : (n+1)⁻¹ < ϑ(c), g_n(c) ≤ n+1}`.  If `Lᵏ(S_n) > 0`, a compact `K ⊆ S_n` with `Lᵏ(K) > 0` has `ψ(K) = 0` and `ψ(B(z,τ)) ≤ (n+1)τᵏ` for `z ∈ K`, `0 < τ < 1/(n+1)`; hence `ϑ = 0` at `Lᵏ`-a.e. point of `K`, contradicting `ϑ > (n+1)⁻¹` on `K`.
- **Calls**: `rectifiability_mickle_rado_limsup_eq_iInf`, `rectifiability_mickle_rado_sup_lsc`, `rectifiability_mickle_rado_density_zero`
- **Called by**: `rectifiability_bf_slice_density_null`

#### `rectifiability_mickle_rado_sup_lsc` (L60380)

- `root.rectifiability-a1.mickle_rado-a1.sup_lsc-a1` · issue #2500 · PR #3328 · candidate `c24b145c9e3f`
- **Statement and proof** (no doc comment in the source; summary of the accepted natural-language proof): **Lower semicontinuity of the truncated density supremum** (step 1 of the accepted natural-language proof of `rectifiability_mickle_rado`, the Mickle–Radó density theorem, cf. Mattila, Thm 18.5 **[corrected]**). If the outer measure `ψ` on `ℝᵏ`, `k = m + 1`, is inner continuous on open balls, then for every `r` the function `c ↦ sup_{0<t<r} ψ(B(c, t))/tᵏ` is lower semicontinuous. Proof: inner continuity gives, for `a < ψ(B(c, τ))`, some `τ′ < τ` with `a < ψ(B(c, τ′))`, and `B(c, τ′) ⊆ B(c′, τ)` for `|c′ − c| < τ − τ′`, so `c ↦ ψ(B(c, τ))` is lower semicontinuous; division by `tᵏ ∈ (0, ∞)` is a continuous monotone bijection of `[0, ∞]`, and a supremum of lower semicontinuous functions is lower semicontinuous.
- **Correction**: the summary in the previous revision of this file said "step 1 of Mattila, Thm 18.5". The step number is that of the accepted proof of the parent node `root.rectifiability-a1.mickle_rado-a1`, whose source is Mattila's Theorem 18.5; it is not a step number of Mattila's proof.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_mickle_rado`

#### `rectifiability_mickle_rado_density_zero` (L60495)

- `root.rectifiability-a1.mickle_rado-a1.density_zero-a1` · issue #2525 · PR #3523 · candidate `c75bb5e20a2f`
- **Statement and proof**: Mickle–Radó density step (step 3 of the accepted natural-language proof of `rectifiability_mickle_rado`, run with `ε ↓ 0`; cf. Mattila, Thm 18.5 **[corrected]**): if `ψ(B(z,τ)) ≤ C τᵏ` for `z ∈ K`, `0 < τ < r`, with `C < ∞` and `r > 0` **[corrected]**, where `K` is closed and `ψ(K) = 0`, then the upper `k`-density of `ψ` vanishes at `Lᵏ`-a.e. point of `K`.  At a Lebesgue density point `c ∈ K` of `K`, the Vitali estimate `ψ(B(c,t))·ω ≤ C·6ᵏ·Lᵏ(B(c,2t) ∖ K)` together with `Lᵏ(B̄(c,2t) ∖ K) = (2t)ᵏ·ω·(1 − R_c(2t))`, `R_c(ρ) = Lᵏ(K ∩ B̄(c,ρ))/Lᵏ(B̄(c,ρ)) → 1`, gives `ψ(B(c,t))/tᵏ ≤ C·12ᵏ·(1 − R_c(2t)) → 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Mattila, Thm 18.5, step 3". The step number is that of the accepted proof of the parent node `root.rectifiability-a1.mickle_rado-a1`, whose source is Mattila's Theorem 18.5; it is not a step number of Mattila's proof. The doc comment also leaves implicit the hypotheses `C < ∞` and `r > 0` of the Lean statement (line 60495).
- **Calls**: `rectifiability_mickle_rado_vitali_bound`
- **Called by**: `rectifiability_mickle_rado`

#### `rectifiability_mickle_rado_vitali_bound` (L60408)

- `root.rectifiability-a1.mickle_rado-a1.vitali_bound-a1` · issue #2513 · PR #3460 · candidate `5ffa2b8672c5`
- **Statement and proof**: Vitali covering estimate off a `ψ`-null closed set, a covering step for the Mickle–Radó density theorem (Mickle–Radó, Proc. Amer. Math. Soc. 9 (1958), 433–439).  If `K` is closed, `ψ K = 0` and `ψ(B(z,τ)) ≤ C τᵏ` for `z ∈ K`, `0 < τ < r` (`k = m + 1`), then `ψ(B(c₀,t)) · Lᵏ(B(0,1)) ≤ C 6ᵏ Lᵏ(B(c₀,2t) ∖ K)` for `c₀ ∈ K`, `0 < t`, `6t ≤ r`.  The balls `B(z, d z)`, `d z = dist(z,K)`, `z ∈ B(c₀,t) ∖ K`, miss `K` and lie in `B(c₀,2t)`.  A disjoint (hence countable) Vitali subfamily has `5`-fold enlargements covering `B(c₀,t) ∖ K`, and `B(b, 5 d b) ⊆ B(z'_b, 6 d b)` for a nearest point `z'_b ∈ K` of `b`, where `6 d b < 6t ≤ r`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_mickle_rado_density_zero`

#### `rectifiability_bf_fibre_cone_comparison` (L61032)

- `root.rectifiability-a1.bf_trichotomy-a1.fibre_cone_comparison-a1` · issue #4600 · PR #4962 · candidate `ec1bc95d1c91`
- **Statement and proof**: Cones versus unions of coordinate fibres (step 4 of the accepted natural-language proof of the Besicovitch–Federer trichotomy `rectifiability_bf_trichotomy`, cf. Mattila 18.9; used for Simon Ch. 6, 8.1 **[corrected]**).  Let `k = m + 1`, `L_u(y) = (⟨u₁, y⟩, …, ⟨u_k, y⟩)`, `X_u(a, r, s) = {x : |x − a| < r, |L_u(x − a)| < s|x − a|}`, `u ⊕_j c = (uᵢ + cᵢ e_j)ᵢ` and `K_j(t) = {x ≠ a : L_{u ⊕_j c}(x − a) = 0 for some |c| < t}`.  With `Φ = limsup_{s → 0⁺} sup_{0<r<δ} μ(X_u(a, r, s))/(rs)ᵏ` and `ϑ_j = limsup_{t → 0⁺} sup_{0<r<δ} μ(B(a, r) ∩ K_j(t))/(rt)ᵏ`, we have `ϑ_j ≤ Φ` for every `j` and `Φ ≤ (√N)ᵏ Σ_j ϑ_j`.  Since `L_{u ⊕_j c}(y) = L_u(y) + y_j c`, `B(a, r) ∩ K_j(t) ⊆ X_u(a, r, t)` and `X_u(a, r, s) ⊆ ⋃_j B(a, r) ∩ K_j(√N s)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 4 of the Besicovitch–Federer trichotomy, Mattila 18.9". The step number is that of the accepted proof of `rectifiability_bf_trichotomy`, not of Mattila's proof.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_bf_trichotomy`

#### `rectifiability_bf_cone_ratio_reduction` (L60918)

- `root.rectifiability-a1.bf_trichotomy-a1.cone_ratio_reduction-a1` · issue #4594 · PR #5043 · candidate `1bff34429405`
- **Statement and proof**: Cone-ratio dichotomy.  Write `L x = (⟨v₁, x⟩, …, ⟨v_k, x⟩)` (`k = m + 1`), `X(r, s) = {x : |x − a| < r, |L(x − a)| < s|x − a|}` and `Φ = limsup_{s→0⁺} sup_{0<r<δ} μ(X(r, s))/(rs)ᵏ`.  If `Φ = 0`, then for each `η > 0` some `s ∈ (0, 1)` has `μ(X(r, s)) ≤ η(rs)ᵏ` for all `r ∈ (0, δ)`.  If `Φ = ∞`, then `X(r, s) ⊆ L⁻¹(B̄(La, rs))`, so the push-forward `L_# μ` has infinite upper `k`-density at `La`: its density quotients at the radii `rs → 0⁺` are unbounded.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_bf_trichotomy`

#### `rectifiability_bf_cone_density` (L59866)

- `root.rectifiability-a1.bf_cone_density-a1` · issue #1027 · PR #1854 · candidate `fbc29839ab61`
- **Statement and proof**: **Conical density lemma for purely unrectifiable sets** (Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, 15.13–15.15; Hovila–Järvenpää–Järvenpää–Ledrappier, arXiv:1104.3453, Lemma 2.2).  Let `k = m + 1`, `L_v x = (⟨v₁, x⟩, …, ⟨v_k, x⟩) ∈ ℝᵏ` and `X_v(a,r,s) = {x : |x - a| < r, |L_v(x - a)| < s |x - a|}`.  If `E ⊆ ℝ^N` is purely `k`-unrectifiable, the set of `a ∈ E` at which, for every `η > 0`, some aperture `s ∈ (0,1)` gives `Hᵏ(E ∩ X_v(a,r,s)) ≤ η (r s)ᵏ` for all `r ∈ (0,δ)` is `Hᵏ`-null.  The three steps of the proof (the conical density estimate, the uniform density bound forcing measure zero, and the reduction to rational apertures) are local `have`s of this single declaration.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_bf_projection_null_ae`

#### `rectifiability_bf_infinite_fibre_null` (L59757)

- `root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1` · issue #1434 · PR #2320 · candidate `a31774a4af2a`
- **Statement and proof**: Eilenberg finiteness: if `f : ℝ^N → ℝ^{m+1}` is Lipschitz and `E ⊆ ℝ^N` is Borel with `H^{m+1}(E) < ∞`, then `E ∩ f⁻¹{y}` is finite for Lebesgue-a.e. `y ∈ ℝ^{m+1}`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_bf_projection_null_ae`

#### `rectifiability_rn_positive_real_density` (L61670)

- `root.rectifiability-a1.mass_measure_rectifiable-a1.rn_positive_density-a1` · issue #2502 · PR #3489 · candidate `84cf3d4ed0c1`
- **Statement and proof**: Simon Ch. 6, proof of 8.1, (8) (p. 174): σ-finite Radon–Nikodym with a positive real density. If `ν⌞B` and `μ` are σ-finite, `μ(X ∖ B) = 0` and `μ ≪ ν`, then `μ = (ν⌞M).withDensity θ` with `M = B ∩ {0 < dμ/d(ν⌞B) < ∞}` and `θ = (dμ/d(ν⌞B)).toReal`; `θ` is `ν`-integrable on `M ∩ K` whenever `μ K < ∞`, since `∫_{M ∩ K} θ dν = μ K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `rectifiability_mass_measure_rectifiable`

#### `rectifiability_orientation` (L38735)

- `root.rectifiability-a1.orientation-a1` · issue #1039 · PR #1918 · candidate `537363e208ed`
- **Statement and proof**: Simon Ch. 6, proof of Theorem 8.1 (pp. 174–175), (10)–(13) and the concluding argument: the orientation of a rectifiable representation of a current with locally finite boundary mass. For `Hⁿ`-a.e. `x ∈ M` (weighted tangent space `L`, Lebesgue point of `ξ` for `μ = θ Hⁿ⌞M`, finite upper densities of `μ` and of the mass measure `ν` of `∂T`), the blow-ups of `T` at `x` converge to `S_x(ω) = θ(x) ∫_L ⟨ω, ξ(x)⟩ dHⁿ`, while the boundary bound `|∂T(η^#φ)| ≤ sup |η^#φ| ν(B_{4r}(x)) = O(r)` **[corrected]** gives `∂S_x = 0`.  Testing with `φ = (a ϕ) β`, `a` a covector vanishing on `L`, shows `⟨a ∧ β, ξ(x)⟩ = 0`; in an orthonormal frame adapted to `L` this forces `ξ(x) = c τ₁ ∧ ⋯ ∧ τₙ`, and `|ξ(x)| = 1` gives `c = ±1`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), writes this bound as `= O(rⁿ⁺¹)`. Here `η^#φ` is the pull-back of the `(n − 1)`-form `φ` by `η_{x,r}(y) = (y − x)/r`, so `sup |η^#φ| = r^{1−n} sup |φ|`. The finite upper density of `ν` gives `ν(B_{4r}(x)) = O(rⁿ)`, so the bound is `O(r)`. This is Simon's display (12) of the proof of 8.1 (p. 175), with `λ` for `r`: for `spt ω ⊆ B_R(0)` it bounds `∂(η_{x,λ#}T)(ω) = ∂T(η_{x,λ}^# ω)` by a constant times `|ω| λ^{1−n} μ_{∂T}(B_{λR}(x))`, which tends to `0` as `λ ↓ 0` because `Θ*ⁿ(μ_{∂T}, x) < ∞`. The order `rⁿ⁺¹` is false for `η^#φ` in general. For example, let `n = 2`, `x = 0` and `T = (2 + y₁)[[B₁(0)]]` in `ℝ²`, i.e. `T(ω) = ∫_{B₁(0)} (2 + y₁) ⟨ω, e₁ ∧ e₂⟩ dL²`. For a 1-form `ψ`, the divergence theorem gives `∂T(ψ) = T(dψ) = ∫_{∂B₁(0)} (2 + y₁) ⟨ψ, τ⟩ dH¹ − ∫_{B₁(0)} ψ(e₂) dL²`, where `τ` is the counterclockwise unit tangent of the circle. The boundary term vanishes when `spt ψ` is a compact subset of the open disc `B₁(0)`. Take `φ = a dy₂` with `a ∈ C_c^∞(B_R(0))`, `∫ a dL² ≠ 0`, and `0 < r < 1/R`. Then `η^#φ = r⁻¹ a(y/r) dy₂`, and its support `r · spt a` is a compact subset of `B_{rR}(0) ⊆ B₁(0)`. Hence `∂T(η^#φ) = −r⁻¹ ∫ a(y/r) dL²(y) = −r ∫ a dL²`, which is of exact order `r`, not `O(r³) = O(rⁿ⁺¹)`. (The previous revision of this file stated the example without the boundary term and without the support condition; see §8.) The exponent `n + 1` belongs to the test forms of the Lean proof, `ψ_r(y) = r φ((y − x)/r) = rⁿ (η^#φ)(y)`. For these, `|∂T(ψ_r)| ≤ sup |ψ_r| M_{B_{4r}(x)}(∂T) = O(rⁿ⁺¹)`, and the blow-up is normalized by `r⁻ⁿ` (§3.3, Step 4). Both normalizations give `∂S_x = 0`, so the Lean proof is unaffected.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `cmb_exists_compactly_contained_exhaustion` (A.1), `rectifiability_mass_measure_representation`, `rectifiability_weighted_tangent_ae`, `rectifiability_density_comparison`, `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `rectifiability_theorem`

#### `rectifiability_weighted_tangent_ae` (L38115)

- `root.rectifiability-a1.weighted_tangent_ae-a1` · issue #1036 · PR #1762 · candidate `2f3657605e57`
- **Statement and proof**: Simon Ch. 3, Theorem 1.9 "⇒" (via Theorem 1.6 and Remark 1.8(1)), localized to an open `U`: if `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable and `θ > 0` is locally `Hⁿ`-integrable on `M` in `U`, then `M` has an approximate tangent space with respect to `θ` at `Hⁿ`-a.e. point of `M` (`n = m + 1`). Proof.  Localize to `M ∩ W_q` with `W_q ⊂⊂ U` (`cmb_exists_compactly_contained_exhaustion`, `br_weightedTangent_congr`) and pass to a Borel subset of full measure, so that `θ ∈ L¹(Hⁿ⌞M)`. Cut the Lipschitz parametrizations `F_j : ℝⁿ → ℝ^P` of `M` into Borel pieces `T_p` on which `G_p = F_j` is differentiable with injective derivative and uniformly bi-Lipschitz (Rademacher, null critical images, approximately linear partition).  Fix `p`, put `A = T_p ∩ G_p⁻¹(M)` and `h = 1_A J_{G_p} (θ ∘ G_p) ∈ L¹(ℝⁿ)` (injective area formula).  At `x = G_p(b)` with `b ∈ A` a Lebesgue point of `h` and `θ Hⁿ⌞(M ∖ G_p(T_p))` of zero `n`-density at `x` (Simon Ch. 1, 3.6), the area formula and the substitution `b' = b + r c` give `∫_{η_{x,r}(M)} f(y) θ(x + r y) dHⁿ(y) = ∫ h(b + r c) f((G_p(b + r c) - x) / r) dc + o(1)`, the integrand vanishes for `|c| > R'` (lower bound on `T_p`), and the right side tends to `h(b) ∫ f(dG_p(b) c) dc = θ(x) ∫_{dG_p(b)(ℝⁿ)} f dHⁿ` (Lebesgue point, dominated convergence, linear area formula).  The exceptional sets are countably many `Hⁿ`-null sets.
- **Calls**: `cmb_exists_compactly_contained_exhaustion` (A.1), `br_weightedTangent_congr`
- **Called by**: `rectifiability_orientation`

#### `br_weightedTangent_congr` (L2130)

- `root.boundary_rectifiability-a1.tangent_locality-a1` · issue #847 · PR #1658 · candidate `def607d836e2`
- **Statement and proof**: Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), the locality step in the proof of Ch. 6, 6.3: the tangent spaces of `(M, θ)` at `x` only depend on `M ∩ V` up to `Hᵏ`-null sets and on `θ` up to `Hᵏ ⌞ (M ∩ V)`-null sets together with its value `θ(x)` **[corrected]**, `V ∋ x` open.  If `B_δ(x) ⊆ V` and `f = 0` off `B_R(0)`, then for `0 < r < δ / R` the blow-up integrands vanish off `W = η_{x,r}(V)`, and `Hᵏ(η_{x,r} Z) = r⁻ᵏ Hᵏ(Z)`; so the blow-up integrals of `(M, θ)` and `(M', θ')` agree for all small `r`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), does not mention the value `θ(x)`. The Lean statement does assume `θ x = θ' x`, and the hypothesis is needed. The definition (Ch. 3, 1.7; SimonGMT's `HasWeightedApproximateTangentSpaceAt`) asks the blow-up integrals to converge to `θ(x) ∫_L f dHᵏ`. For `k ≥ 1`, changing `θ` at the single point `x` changes this limit but not the blow-up integrals. So the argument above shows that the blow-up integrals of `(M, θ)` and `(M′, θ′)` agree for small `r`. Because `θ(x) = θ′(x)`, the two required limits also agree. Every application supplies this hypothesis, since the Lean statement requires it.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_restrictDomain_isIntegerMultiplicity`, `br_isIntegerMultiplicity_of_local`, `br_loc_triple_inter_open`, `fiw_tb_ext_isIntegerMultiplicity`, `rectifiability_weighted_tangent_ae`, `deformation_im_pushforward_limit`, `deformation_skeleton_polyhedral`, `iwl_localization`

### A.4 Lemma 3.9 (§3.4): `lipschitz_pushforward_integer_multiplicity` and its 74 further declarations

#### `lipschitz_pushforward_integer_multiplicity` (L46209)

- `root.lipschitz_pushforward_im-a1` · issue #319 · PR #4707 · candidate `3289485ca49a`
- **Statement and proof**: **Simon Ch. 6, Lemma 3.9 (p. 148).**  Write `T = τ(M, θ, ξ)` with `θ` integer valued.  The tangential differential `d^M f` (Ch. 3, §2) supplies the linear maps `L x`; with them (3.6) defines a current `S = f_# T` in `V`, and the area formula with 3.7–3.8 gives `S = τ(f(M), N, ζ)` with `N` integer valued, so `S` is integer multiplicity.
- **Calls**: `lpf_tangential_differential_exists`, `lpf_pushforward_is_current`, `lpf_pushforward_integrality`
- **Called by**: `deformation_theorem`, `integrality_of_weak_limits`, `main_theorem`

#### `lpf_tangential_differential_exists` (L45694)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1` · issue #732 · PR #4195 · candidate `f55db39d5141`
- **Statement and proof**: Tangential differential of a locally Lipschitz map along a rectifiable triple (Simon Ch. 3 §2, 2.1–2.2 and p. 76; input to Simon Ch. 6, 3.6).  If `U ⊆ ℝ^P` is open, `(M, θ, ξ)` is a rectifiable triple in `U` and `f` is locally Lipschitz on `U`, there is `L : ℝ^P → L(ℝ^P, ℝ^Q)`, strongly measurable and bounded on `M ∩ K` for compact `K ⊆ U`, such that for `Hⁿ`-a.e. `x ∈ M`, `t ↦ f(x + t v)` has derivative `L(x) v` at `0` for every `v` in every weighted approximate tangent space of `(M, θ)` at `x`.
- **Calls**: `lpf_countably_rectifiable_c1_cover`, `lpf_tde_measurable_chart_differential`, `lpf_tde_chart_nondiff_image_null`, `lpf_weighted_tangent_on_c1_chart`, `lpf_tde_uniform_lipschitz_near_compact`, `lpf_tde_chart_directional_deriv`
- **Called by**: `lipschitz_pushforward_integer_multiplicity`

#### `lpf_countably_rectifiable_c1_cover` (L24675)

- `root.lipschitz_pushforward_im-a1.countably_rectifiable_c1_cover-a1` · issue #728 · PR #4028 · candidate `4f96ac678110`
- **Statement and proof**: **Simon Ch. 3, Lemma 1.2 ("only if").**  A countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by the images `Φ_j(Ω_j)` of `C¹` maps `Φ_j : ℝⁿ → ℝ^P` which are Lipschitz and antilipschitz on open sets `Ω_j ⊆ ℝⁿ`.
- **Calls**: `lpf_lipschitz_c1_immersion_pieces`
- **Called by**: `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_chart_convergence`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`, `lpf_tangential_differential_exists`, `slicing_im_ll_tangential_weak_limit`

#### `lpf_lipschitz_c1_immersion_pieces` (L24577)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1` · issue #726 · PR #3642 · candidate `682c558f0382`
- **Statement and proof**: Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) combined with the inverse-function-theorem estimate of Ch. 3, Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148).  A map `u : ℝⁿ → ℝ^Q` that is locally Lipschitz on an open `Ω` agrees, together with its derivative, with `C¹` maps `G_k` on pairwise disjoint Borel sets `E_k ⊆ O_k ∩ Ω`, where `G_k` is antilipschitz on the open set `O_k`; and `Lⁿ`-a.e. point of `Ω` at which `u` has an injective derivative lies in `⋃_k E_k`.
- **Calls**: `lpf_lipschitz_localization`, `lpf_c1_approximation_eucl`, `lpf_c1_local_antilipschitz`
- **Called by**: `lpf_countably_rectifiable_c1_cover`, `slicing_im_st_cd_c1_cover`, `lpf_pushforward_integrality`

#### `lpf_lipschitz_localization` (L24536)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.lipschitz_localization-a1` · issue #1149 · PR #2107 · candidate `e9f440ddea21`
- **Statement and proof**: Countable localization of a map `u` that is locally Lipschitz on an open set `Ω` **[corrected]**: open sets `B m ⊆ Ω` covering `Ω` and globally Lipschitz maps `v m` agreeing with `u` on `B m` (Lindelöf, then Lipschitz extension).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not say that `Ω` is open, which the Lean statement (line 24537) assumes; open subsets of `Ω` can cover `Ω` only if `Ω` is open.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_lipschitz_c1_immersion_pieces`

#### `lpf_c1_approximation_eucl` (L24443)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_eucl-a1` · issue #1147 · PR #3446 · candidate `eff6bc809135`
- **Statement and proof**: Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42) for `ℝ^Q`-valued maps, applied componentwise (as in Simon's proof of Ch. 3, Lemma 1.2; used for Ch. 6, Lemma 3.9, p. 148) **[corrected]**: a Lipschitz `u : ℝⁿ → ℝ^Q` agrees with a `C¹` map `G`, and has Fréchet derivative `DG(x)`, at every `x` of a closed set `A` with `Lⁿ(ℝⁿ ∖ A) < ε`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "applied componentwise as in the proof of Ch. 6, Lemma 3.9 (p. 148)". The printed discussion of 3.9 (3.3–3.9, pp. 146–148) does not invoke Ch. 2, Theorem 1.5. The componentwise application is made in the accepted proof of `lpf_lipschitz_c1_immersion_pieces` (step 3), which follows Simon's proof of Ch. 3, Lemma 1.2 and which the formal proof of 3.9 uses.
- **Calls**: `lpf_c1_approximation_real`
- **Called by**: `lpf_lipschitz_c1_immersion_pieces`, `slicing_im_coarea_chart_cover`, `slicing_im_tg_cc_lipschitz_range_c1_cover`

#### `lpf_c1_approximation_real` (L24399)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1` · issue #1146 · PR #3246 · candidate `f7a35d70d995`
- **Statement and proof**: Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem, p. 42), in the form established by its printed proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees with a `C¹` function `h` on a closed set `A` with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A` with `Dg = Dh` there.  Rademacher gives a Borel set `D` of full measure where `g` is differentiable; Lusin gives a closed `C ⊆ D` with `Dg|C` continuous; the `η_k` step gives a closed `A ⊆ C` satisfying Whitney's condition (‡) (Thm 1.6); Whitney's extension theorem then gives `h`.
- **Calls**: `lpf_c1r_lusin_closed`, `lpf_c1r_uniform_remainder`, `lpf_c1r_whitney_extension`
- **Called by**: `lpf_c1_approximation_eucl`, `slicing_im_st_cd_c1_pieces_of_lipschitzOn`

#### `lpf_c1r_lusin_closed` (L23322)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.lusin_closed-a1` · issue #1896 · PR #2539 · candidate `b7b6c0271146`
- **Statement and proof**: Simon Ch. 1, Theorem 1.17 (Lusin), in the form used in the proof of Ch. 2, Theorem 1.5 (p. 44), "which applies to sets of infinite measure for `Lⁿ`": if `S ⊆ ℝⁿ` is Borel and `f : ℝⁿ → (ℝⁿ)*` is Borel measurable, then for every `ε > 0` there is a closed `C ⊆ S` with `Lⁿ(S ∖ C) < ε` and `f|C` continuous.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_c1_approximation_real`, `slicing_im_coarea_c1_approx`

#### `lpf_c1r_uniform_remainder` (L23491)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.uniform_remainder-a1` · issue #1921 · PR #2905 · candidate `38a84674ea5a`
- **Statement and proof**: Simon Ch. 2, proof of Theorem 1.5 (C¹ Approximation Theorem, p. 44), the `η_k` step.  Let `g : ℝⁿ → ℝ` be Lipschitz and `C` closed, with `g` differentiable at every point of `C` and `Dg` continuous on `C`.  Then there is a closed `A ⊆ C` with `Lⁿ(C ∖ A) < ε` on which the remainder `R(x, y) = (g(y) − g(x) − Dg(x)(y − x)) / |y − x|` tends to `0` as `y → x` in `A`, uniformly for `x` in each compact `L ⊆ A` (Whitney's condition 1.6 (‡)).  The functions `η_k(x) = sup ({0} ∪ {|R(x, y)| : y ∈ C, 0 < |y − x| < 1/(k+1)})` (`η_k = 0` off `C`) are Borel and tend to `0` on `C`, so Egoroff (`lpf_c1r_egoroff_closed`) makes the convergence uniform on the bounded parts of a closed `A ⊆ C`.
- **Calls**: `lpf_c1r_egoroff_closed`
- **Called by**: `lpf_c1_approximation_real`, `slicing_im_coarea_c1_approx`

#### `lpf_c1r_egoroff_closed` (L23418)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.egoroff_closed-a1` · issue #1910 · PR #2656 · candidate `7919071b797d`
- **Statement and proof**: Closed Egorov theorem on `ℝⁿ` (Simon Ch. 2, proof of Theorem 1.5): if Borel `f k` converge pointwise on a Borel set `C` to a Borel `g`, then for every `ε > 0` there is a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that `f k → g` uniformly on every bounded part `A ∩ B̄_R(0)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_c1r_uniform_remainder`

#### `lpf_c1r_whitney_extension` (L23646)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1.whitney_extension-a1` · issue #1932 · PR #2715 · candidate `8b631fd6fe8f`
- **Statement and proof**: Whitney's `C¹` extension theorem (Simon Ch. 2, Theorem 1.6), with derivatives as continuous linear maps: if `A ⊆ ℝⁿ` is closed and `f`, `τ` are continuous on `A` with the compact-uniform Taylor condition, then some `C¹` function `h` agrees with `f` on `A` and has derivative `τ a` at every `a ∈ A`.  Standard construction (Evans–Gariepy §6.5): Whitney radius `r = min(1, dist(·, A)) / 100`, a Vitali family of disjoint balls `B(c, r c)` whose fourfold enlargements cover `ℝⁿ ∖ A`, uniformly bounded overlap, rescaled bumps normalized to a partition of unity `w_c` with `∑ ‖Dw_c(x)‖ ≤ M / r x`, and `h = ∑ w_c P_{q c}` off `A`, where `P_b(y) = f b + τ b (y - b)` and `q c ∈ A` is a nearest point.  The steps follow the pinned SimonGMT proof `Poincare.SimonGMT.Chapter02.exists_contDiff_one_extension_of_whitney` (whose module is not imported here), inlined.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_c1_approximation_real`, `slicing_im_coarea_c1_approx`

#### `lpf_c1_local_antilipschitz` (L24496)

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_local_antilipschitz-a1` · issue #1148 · PR #1953 · candidate `961fc1089331`
- **Statement and proof**: Simon Ch. 3, proof of Lemma 1.2 (p. 70), as used for Ch. 6, Lemma 3.9 (p. 148): the inverse-function-theorem estimate.  If `G : ℝⁿ → ℝ^Q` is `C¹` and `DG(w)` is injective, then `c |z − z'| ≤ |G z − G z'|` for all `z, z'` in some ball `B_r(w)`, with `c > 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_lipschitz_c1_immersion_pieces`, `slicing_im_coarea_chart_cover`, `slicing_im_tg_cc_contDiff_range_chart_cover`

#### `lpf_tde_measurable_chart_differential` (L39764)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1` · issue #2451 · PR #3944 · candidate `e23946e21500`
- **Statement and proof**: Borel chartwise tangential differential (Simon Ch. 3 §2, 2.1–2.2, for Ch. 6, 3.6): for C¹ charts `Φ j` antilipschitz on open `Ω j` and any `f`, glue the Borel pieces `x = Φ j w ↦ D(f ∘ Φ j)(w) ∘ Λ(DΦ j(w))` along the first chart through `x`, and `0` off the charts; `Λ` is the continuous left inverse of `lpf_tde_continuous_left_inverse`.
- **Calls**: `lpf_tde_continuous_left_inverse`, `lpf_tde_mcd_single_chart`, `lpf_tde_mcd_countable_glue`
- **Called by**: `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `lpf_tangential_differential_exists`

#### `lpf_tde_continuous_left_inverse` (L39711)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.continuous_left_inverse-a1` · issue #2444 · PR #3089 · candidate `d9f5b44bfc78`
- **Statement and proof**: Moore–Penrose left inverse (Simon Ch. 3 §2, input to 2.1–2.2): `Λ(A) = (A* A)⁻¹ A*` is continuous on the injective `A : ℝⁿ → ℝ^P`, `Λ(A) A = id`, and the orthogonal projection `A Λ(A)` onto `range A` does not increase norms.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_tde_measurable_chart_differential`, `slicing_im_ll_twl_coefficient_field`

#### `lpf_tde_mcd_single_chart` (L39623)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.single_chart-a1` · issue #3289 · PR #3737 · candidate `0de2b8a211fb`
- **Statement and proof**: Measurable tangential differential on a single `C¹` chart (for the push-forward in Simon Ch. 6, 3.9): let `Φ` be `C¹` with `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` (`c > 0`) on the open set `Ω`, and let `Λ A` be a left inverse of each injective `A` with `‖A (Λ A v)‖ ≤ ‖v‖`, `Λ` continuous on the injective maps.  With `Ψ` the inverse of `Φ` on `S = Φ(Ω)`, the map `G x = D(f ∘ Φ)(Ψ x) ∘ Λ(DΦ(Ψ x))` on `S` (`0` elsewhere) is Borel: `S` is Borel by Lusin–Souslin, `Ψ` is `c⁻¹`-Lipschitz on `S`, `DΦ(w)` is injective by `lpf_wtc_cat_fderiv_lower_bound`, and `D(f ∘ Φ)` is Borel.
- **Calls**: `lpf_wtc_cat_fderiv_lower_bound`
- **Called by**: `lpf_tde_measurable_chart_differential`

#### `lpf_wtc_cat_fderiv_lower_bound` (L21259)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1` · issue #2028 · PR #2617 · candidate `8cfbc487a3d1`
- **Statement and proof**: Derivative lower bound (step 1 of the C¹ chart approximate tangent argument for Simon Ch. 6, 3.9): if `c ‖v - v'‖ ≤ ‖Φ v - Φ v'‖` on an open `Ω ∋ w` and `Φ` is differentiable at `w`, then `c ‖s‖ ≤ ‖DΦ(w) s‖` for every `s` (no sign condition on `c`).  Apply the bound to `v = w + t • s`, `v' = w`, divide by `t > 0` and let `t → 0⁺`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_approx_tangent`, `lpf_tde_mcd_single_chart`, `deformation_ipl_cc_chart_integral_representation`, `slicing_im_tg_chart_gradient`, `slicing_im_st_lsc_tangent_range`, `slicing_im_ll_twl_coefficient_field`

#### `lpf_tde_mcd_countable_glue` (L39683)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.countable_glue-a1` · issue #3300 · PR #3742 · candidate `e54c806e72bd`
- **Statement and proof**: Countable measurable gluing by the first index: for measurable sets `S j` and measurable maps `G j : X → Y` there is a measurable `L : X → Y` vanishing off `⋃ j, S j` and agreeing at each `x ∈ ⋃ j, S j` with some `G j` such that `x ∈ S j`.  Take `L x = G'_{j(x)} x` with `G'_j = (S j).piecewise (G j) 0` and `j(x)` the least `j` with `x ∈ S j ∨ x ∉ ⋃ i, S i`; `L` is measurable by `Measurable.find`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_tde_measurable_chart_differential`

#### `lpf_tde_chart_nondiff_image_null` (L45505)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_nondiff_image_null-a1` · issue #2430 · PR #3163 · candidate `019ad40a7219`
- **Statement and proof**: Rademacher on a Lipschitz chart (Simon Ch. 2, 1.4 and 1.8(i)): for `f` locally Lipschitz on an open `U` and `Φ` `K`-Lipschitz on an open `Ω ⊆ ℝⁿ`, the `Φ`-image of the set of `w ∈ Ω` with `Φ w ∈ U` at which `f ∘ Φ` is not differentiable is `Hⁿ`-null.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_tangential_differential_exists`, `slicing_im_tg_chart_gradient`

#### `lpf_weighted_tangent_on_c1_chart` (L39786)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1` · issue #731 · PR #3558 · candidate `f9637977f9e7`
- **Statement and proof**: Let `V` be open, `M ⊆ V` `Hⁿ`-null-measurable and `θ > 0` on `M` with `θ` `Hⁿ`-integrable on `M ∩ K` for compact `K ⊆ V` **[corrected]**. For `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and `w ∈ Ω` with `Φ w = y`, `DΦ(w)(ℝⁿ)` is the approximate tangent space of `M` with multiplicity `θ` at `y` (Simon Ch. 3, proof of 1.6 and Remark 1.8(1), for one `C¹` chart `Φ` that is antilipschitz on the open set `Ω`).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves the hypotheses on `(M, θ)` implicit; they are part of Simon's setting in Ch. 3, 1.7, but not of SimonGMT's `HasWeightedApproximateTangentSpaceAt`. The Lean statement (lines 39788–39791) assumes them, and they are now stated.
- **Calls**: `lpf_wtc_chart_image_measurable_locally_finite`, `lpf_wtc_lusin_compact_pieces`, `lpf_wtc_ae_zero_density_off_set`, `lpf_wtc_tangent_transfer`, `lpf_wtc_chart_approx_tangent`, `lpf_wtc_weighted_tangent_transfer`
- **Called by**: `deformation_ipl_cc_chart_orientation_sign`, `lpf_chart_chain_rule`, `lpf_pushforward_integrality`, `lpf_tangential_differential_exists`, `slicing_im_ll_tangential_weak_limit`

#### `lpf_wtc_chart_image_measurable_locally_finite` (L25340)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_image_measurable_finite-a1` · issue #1266 · PR #1564 · candidate `a2f705665fe4`
- **Statement and proof**: The image `Φ(Ω)` of an open `Ω ⊆ ℝⁿ` under a `C¹` map `Φ : ℝⁿ → ℝ^Q` with `c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` for some `c > 0` **[corrected]** is Borel, and `Hⁿ(Φ(Ω) ∩ K) < ∞` for every compact `K`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not say `c > 0`, which the Lean statement (line 25342) assumes. With `c = 0` the local finiteness fails: `Φ(t) = (1 + (1 + t²)⁻¹)(cos t, sin t)` is `C¹` and injective on `Ω = (0, ∞)`, and its image is a curve of infinite length in `B̄₂(0)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_weighted_tangent_on_c1_chart`, `deformation_ipl_chart_convergence`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_lusin_compact_pieces` (L25634)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.lusin_compact_pieces-a1` · issue #1273 · PR #2283 · candidate `5b63f318a7c2`
- **Statement and proof**: Lusin decomposition (Simon Ch. 3, Remark 1.8(1)): if `V` is open and `M ⊆ V` is `Hⁿ`-null-measurable **[corrected]**, a positive weight `θ`, `Hⁿ`-integrable on `M ∩ K` for compact `K ⊆ V`, is continuous on countably many compact pieces `C k ⊆ M` of finite `Hⁿ`-measure which cover `M` up to an `Hⁿ`-null set.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits three hypotheses of the Lean statement (lines 25635–25636): `V` is open, `M ⊆ V`, and `M` is `Hⁿ`-null-measurable. The last one is necessary: a set that is covered up to an `Hⁿ`-null set by compact subsets of itself is `Hⁿ`-null-measurable. For example, for `n = Q = 1`, `θ ≡ 1` and a Bernstein set `M ⊆ [0, 1]` (every compact subset of `M` is countable, and `M` has outer measure `1`), the other hypotheses hold but no such pieces exist.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_weightedTangent_iff_approxTangent`, `lpf_weighted_tangent_on_c1_chart`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_ae_zero_density_off_set` (L11274)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.zero_density_off_set-a1` · issue #1274 · PR #2200 · candidate `12d217bba2a4`
- **Statement and proof**: Localized upper density theorem (Simon Ch. 1, 3.6) for `ν = (Hⁿ ⌞ S).withDensity g`: if `W` is open, `S` is `Hⁿ`-null-measurable **[corrected]** and `∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K ⊆ W`, then `ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for `Hⁿ`-a.e. `y ∈ W \ S`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits two hypotheses of the Lean statement (lines 11275–11276): `W` is open and `S` is `Hⁿ`-null-measurable. Simon's Ch. 1, 3.6 (p. 16) also concerns a measurable set. Without measurability the claim fails: for `n = Q = 1`, `W = ℝ`, `g ≡ 1` and a Bernstein set `S ⊆ [0, 1]`, `S` meets every interval `I ⊆ [0, 1]` in a set of outer measure `|I|`, so `ν(B̄_ρ(y)) = 2ρ` for every `y ∈ (0, 1)` and small `ρ`, while `(0, 1) ∖ S` has outer measure `1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_imcomb_subset_locality`, `dmr_weightedTangent_inter`, `iwl_imc_density_zero_off_set`, `lpf_weighted_tangent_on_c1_chart`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_tangent_transfer` (L33856)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.tangent_transfer-a1` · issue #1276 · PR #2806 · candidate `b493cac78ec5`
- **Statement and proof**: Transfer of approximate tangent planes (Simon Ch. 3, proof of Theorem 1.6 "⇒", step 2).  If `T` is the approximate tangent space of `N` at `y`, `Hⁿ(N ∩ B̄_r(y)) < ∞` for some `r > 0` and `Hⁿ((C ∖ N) ∩ B̄_ρ(y))`, `Hⁿ((N ∖ C) ∩ B̄_ρ(y))` are `o(ρⁿ)`, then `T` is the approximate tangent space of `C` at `y`.  For `φ ∈ C_c` with `|φ| ≤ A` and `tsupport φ ⊆ B_R(0)`, the blow-up formula `lpf_wtc_blowup_setIntegral_image` localizes both blow-up integrals to `B = B̄_{λR}(y)`, and splitting `C ∩ B`, `N ∩ B` along `C ∩ N ∩ B` gives, for small `λ > 0`, `|∫_{η_{y,λ}(C)} φ - ∫_{η_{y,λ}(N)} φ| ≤ A Rⁿ (q₁(λR) + q₂(λR))`, where `q₁, q₂` are the two density quotients of the hypotheses.
- **Calls**: `lpf_wtc_blowup_setIntegral_image`
- **Called by**: `imc_weightedTangent_iff_approxTangent`, `lpf_weighted_tangent_on_c1_chart`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_blowup_setIntegral_image` (L25297)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.blowup_change_of_variables-a1` · issue #1264 · PR #2230 · candidate `8389acdfdd73`
- **Statement and proof**: Change of variables for `Hⁿ`-integrals over blow-ups: `η = η_{y,r}`, `η(x) = r⁻¹(x − y)`, pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so `∫_{η(S)} g dHⁿ = (rⁿ)⁻¹ ∫_S g ∘ η dHⁿ` for every set `S` and every `g` (both sides are Bochner set integrals).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_approx_tangent`, `lpf_wtc_density_bound_of_tangent`, `lpf_wtc_tangent_transfer`, `lpf_wtc_weighted_tangent_transfer`, `imc_wte_density_bound_of_weightedTangent`, `imc_wte_approxTangent_of_weightedTangent`, `imc_approxTangent_iff_of_subset`

#### `lpf_wtc_chart_approx_tangent` (L25575)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1` · issue #1271 · PR #3447 · candidate `f2c64f39999e`
- **Statement and proof**: A `C¹` chart that is antilipschitz on the open set `Ω` has, at each `y = Φ(w)` (`w ∈ Ω`), the approximate tangent space `T = DΦ(w)(ℝⁿ)` (Simon Ch. 3, Def. 1.4) of `N = Φ(Ω)`.  The blow-up integral `∫_{η_{y,λ}(N)} φ dHⁿ` is `(λⁿ)⁻¹ ∫_Ω JΦ(v) φ(λ⁻¹(Φ(v) − y)) dv` (blow-up change of variables, then the area formula), which tends to `∫ JΦ(w) φ(DΦ(w)s) ds`; the area formula for the linear map `DΦ(w)` identifies this limit with `∫_T φ dHⁿ`.
- **Calls**: `lpf_wtc_cat_fderiv_lower_bound`, `lpf_wtc_chart_area_formula`, `lpf_wtc_cat_rescaled_integral_tendsto`, `lpf_wtc_cat_gram_jacobian_continuous`, `lpf_wtc_blowup_setIntegral_image`
- **Called by**: `lpf_weighted_tangent_on_c1_chart`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_chart_area_formula` (L25495)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1` · issue #1268 · PR #3314 · candidate `db9ef3e1c6f5`
- **Statement and proof**: Injective area formula on a `C¹` antilipschitz chart (Simon Ch. 2, (3.1), (3.2), (3.5)): if `Φ : ℝⁿ → ℝ^Q` is `C¹`, `Ω ⊆ ℝⁿ` is open and `c |w - w'| ≤ |Φ w - Φ w'|` on `Ω` for some `c > 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω JΦ(v) h(Φ(v)) dLⁿ(v)` for every `h ∈ C_c(ℝ^Q, ℝ)`, where `JΦ(v) = √det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)`. Proof.  `JΦ(v) = normDet(DΦ(v))` (`LinearMap.normDet_sq_eq_det_gram` for the standard basis), and `JΦ` is continuous and nonnegative; `Φ` is injective on `Ω`.  Localize to a bounded open `s ⊆ Ω` containing `Ω ∩ Φ⁻¹(spt h)` on which `Φ` is Lipschitz (`lpf_wtc_caf_lipschitz_localization`).  As `Φ` is injective on `s`, the fibre sum of the weighted area formula on `s` (`weighted_area_formula_lipschitzOn_fiberSum`, weight `g ∘ Φ`) is the indicator of the Borel set `Φ(s)` applied to `g`, and the within Jacobian on the open `s` is `JΦ`; this gives `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s JΦ (g ∘ Φ) dLⁿ` for every Borel `g ≥ 0`.  The signed identity on `Ω` then follows from `lpf_wtc_caf_signed_of_lintegral`.
- **Calls**: `lpf_wtc_caf_lipschitz_localization`, `lpf_wtc_caf_signed_of_lintegral`
- **Called by**: `lpf_wtc_chart_approx_tangent`

#### `lpf_wtc_caf_lipschitz_localization` (L25382)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1.lipschitz_localization-a1` · issue #2378 · PR #2937 · candidate `86fd6e41a7a2`
- **Statement and proof**: For a `C¹` map `Φ : ℝⁿ → ℝ^Q` with `c |w - w'| ≤ |Φ w - Φ w'|` on an open `Ω ⊆ ℝⁿ` for some `c > 0` **[corrected]** and a compact `K ⊆ ℝ^Q`, `Ω ∩ Φ⁻¹(K)` lies in a bounded open `s ⊆ Ω` on which `Φ` is Lipschitz.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not say `c > 0`, which the Lean statement (line 25384) assumes. With `c = 0`, `n ≥ 1`, `Φ ≡ 0`, `Ω = ℝⁿ` and `K = {0}`, the set `Ω ∩ Φ⁻¹(K) = ℝⁿ` lies in no bounded `s`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_area_formula`

#### `lpf_wtc_caf_signed_of_lintegral` (L25414)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_area_formula-a1.signed_of_lintegral-a1` · issue #2388 · PR #2998 · candidate `f573bdec80e2`
- **Statement and proof**: Signed area formula from the nonnegative one: let `Ω, s ⊆ ℝⁿ` be open with `s ⊆ Ω` and `s` bounded, `Φ` continuous and injective on `Ω`, and `J ≥ 0` continuous **[corrected]**. If `∫⁻_{Φ(s)} g dHⁿ = ∫⁻_s J · (g ∘ Φ) dLⁿ` for every Borel `g ≥ 0`, then `∫_{Φ(Ω)} h dHⁿ = ∫_Ω J · (h ∘ Φ) dLⁿ` for every continuous compactly supported `h` with `Ω ∩ Φ⁻¹(spt h) ⊆ s`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves `Ω`, `s`, `Φ` and `J` unqualified. The Lean statement (lines 25416–25417) assumes the conditions now stated, and `s ⊆ Ω` is necessary: for `n = Q = 1`, `Ω = (0, 1)`, `s = (−1, 1)`, `Φ(v) = |v|`, `J ≡ 1/2` and continuous `h ≥ 0` with `spt h ⊆ (0, 1)` and `∫ h = 1`, the hypothesis holds (both sides equal `∫₀¹ g`) but the conclusion reads `1 = 1/2`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_area_formula`

#### `lpf_wtc_cat_rescaled_integral_tendsto` (L24923)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.rescaled_integral_tendsto-a1` · issue #2045 · PR #2628 · candidate `f2f1db7607fa`
- **Statement and proof**: Rescaled chart integrals converge (Simon Ch. 3, approximate tangent space of a `C¹` chart image): for `Φ` continuous, differentiable at `w ∈ Ω` and antilipschitz on the open set `Ω`, `J` continuous and `φ ∈ C_c`, `(rⁿ)⁻¹ ∫_Ω J(v) φ(r⁻¹(Φ v − Φ w)) dv → ∫ J(w) φ(DΦ(w) s) ds` as `r → 0⁺`.  Substituting `v = w + r s` (Haar scaling and translation invariance) turns the left side into `∫ F_r`; for `0 < r ≤ 1` the antilipschitz bound confines the support of `F_r` to `‖s‖ ≤ R / c`, so `F_r` is dominated by a constant on a ball, and `F_r(s) → J(w) φ(DΦ(w) s)` pointwise by differentiability at `w`; dominated convergence concludes.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_approx_tangent`

#### `lpf_wtc_cat_gram_jacobian_continuous` (L25043)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.gram_jacobian_continuous-a1` · issue #2076 · PR #2613 · candidate `3639f75e8f12`
- **Statement and proof**: Continuity of the Jacobian `JΦ = √det((DΦ)* DΦ)` (Simon Ch. 2, (3.3)) of a `C¹` map `Φ : ℝⁿ → ℝ^Q`, written as the Gram determinant `det(⟨DΦ(v)eᵢ, DΦ(v)eⱼ⟩)` of the columns of `DΦ(v)`.  `v ↦ DΦ(v)` is continuous since `Φ` is `C¹`, so are the columns `DΦ(v)eᵢ`, the Gram entries, the Gram matrix (entrywise), its determinant (a polynomial in the entries) and the square root.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_chart_approx_tangent`

#### `lpf_wtc_weighted_tangent_transfer` (L33996)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1` · issue #1277 · PR #3396 · candidate `ad4fb1886aef`
- **Statement and proof**: Simon Ch. 3, Remark 1.8(1): if `T` is the approximate tangent space of `C ⊆ M` at `y ∈ C` (Definition 1.4), `θ ≥ 0` is `Hⁿ`-integrable on `M` near `y`, `θ|C` is continuous at `y` and `θ Hⁿ ⌞ (M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `M` at `y` with respect to `θ` (Definition 1.7).  After the change of variables `z = η_{y,t}(x)`, the weighted blow-up integral is `θ(y) ∫_{η_{y,t}(C)} φ`, which tends to `θ(y) ∫_T φ`, plus the oscillation of `θ` along `C` and the contribution of `M ∖ C`, both of which tend to `0`.
- **Calls**: `lpf_wtc_density_bound_of_tangent`, `lpf_wtc_blowup_setIntegral_image`, `lpf_wtc_wtt_continuity_error_vanishes`, `lpf_wtc_wtt_remainder_vanishes`, `lpf_wtc_wtt_blowup_integral_split`
- **Called by**: `imc_weightedTangent_iff_approxTangent`, `lpf_weighted_tangent_on_c1_chart`, `slicing_im_tg_weighted_tangent_chart`, `slicing_im_st_weighted_tangent_on_c1_chart`, `slicing_im_coarea_chart_tangent`

#### `lpf_wtc_density_bound_of_tangent` (L25799)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.density_bound_of_tangent-a1` · issue #1275 · PR #2805 · candidate `90ea33e84620`
- **Statement and proof**: Density bound at a tangent point (Simon Ch. 3, Remark 1.5(3), boundedness part): if `T` is the approximate tangent space (Def. 1.4) of `S` at `y` and `Hⁿ(S ∩ B̄_r(y)) < ∞` for some `r > 0`, then `Hⁿ(S ∩ B̄_ρ(y)) ≤ K ρⁿ` for all sufficiently small `ρ > 0`.
- **Calls**: `lpf_wtc_blowup_setIntegral_image`
- **Called by**: `lpf_wtc_weighted_tangent_transfer`

#### `lpf_wtc_wtt_continuity_error_vanishes` (L25118)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.continuity_error_vanishes-a1` · issue #2112 · PR #2933 · candidate `6a3a02bbf289`
- **Statement and proof**: If `C` is `Hⁿ`-null-measurable, `θ` is continuous at `y` within `C` and `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for small `ρ > 0`, then `t⁻ⁿ ∫_C φ(η_{y,t}(x)) (θ(x) - θ(y)) dHⁿ(x) → 0` as `t → 0⁺`.  With `tsupport φ ⊆ B_R(0)` and `|φ| ≤ A`, the integrand vanishes off `B̄_{tR}(y)` and is at most `A ε₁` on `C ∩ B̄_{tR}(y)` once `tR < δ(ε₁)`, so the integral is at most `A ε₁ K (tR)ⁿ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_weighted_tangent_transfer`, `imc_wte_approxTangent_of_weightedTangent`

#### `lpf_wtc_wtt_remainder_vanishes` (L25211)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.remainder_vanishes-a1` · issue #2127 · PR #2662 · candidate `178784030758`
- **Statement and proof**: Zero `θ`-weighted `n`-density of `D` at `y` kills the blow-up integrals (Simon Ch. 3, Remark 1.8(1)): let `D` be `Hⁿ`-null-measurable and `θ ≥ 0` on `D` **[corrected]**. If `(∫⁻_{D ∩ B̄_ρ(y)} θ dHⁿ) / ρⁿ → 0` as `ρ ↓ 0`, then for every `φ ∈ C_c(ℝ^Q)`, `(tⁿ)⁻¹ ∫_D φ(η_{y,t}(x)) θ(x) dHⁿ(x) → 0` as `t ↓ 0`.  No integrability of `θ` is assumed.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves implicit these hypotheses of the Lean statement (line 25211).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_weighted_tangent_transfer`, `imc_wte_approxTangent_of_weightedTangent`

#### `lpf_wtc_wtt_blowup_integral_split` (L25053)

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.weighted_tangent_transfer-a1.blowup_integral_split-a1` · issue #2098 · PR #2683 · candidate `405169da3a03`
- **Statement and proof**: Splitting of the blown-up weighted integral (Simon Ch. 3, Remark 1.8(1)): for `Hⁿ`-null-measurable sets `C ⊆ M` such that `Hⁿ(C ∩ B̄_r(y)) < ∞` and `θ` is `Hⁿ`-integrable on `M ∩ B̄_r(y)` for some `r > 0` **[corrected]**, and all small `t > 0`, `∫_M φ(η_t) θ = θ(y) ∫_C φ(η_t) + ∫_C φ(η_t) (θ − θ(y)) + ∫_{M∖C} φ(η_t) θ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 25053). Additivity of the integral over `M = C ∪ (M ∖ C)` needs the null-measurability of `C`: for `n = Q = 1`, `M = [0, 1]`, `θ ≡ 1`, `y = 1/2`, `C ⊆ M` a Bernstein set and `φ ≥ 0` with `spt φ ⊆ (−1, 1)` and `∫ φ = 1`, the integrals over `C` and over `M ∖ C` both equal the integral over `[0, 1]`, so for `t < 1/2` the right side is `2t` and the left side is `t`. The finiteness conditions near `y` make the three integrals on the right finite for small `t`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_wtc_weighted_tangent_transfer`, `imc_wte_approxTangent_of_weightedTangent`

#### `lpf_tde_uniform_lipschitz_near_compact` (L45490)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.uniform_lipschitz_near_compact-a1` · issue #2420 · PR #2991 · candidate `35e5274c045b`
- **Statement and proof**: Uniform Lipschitz constant and radius near a compact set (Step 6 of the tangential differential construction for Simon Ch. 6, Lemma 3.9).  If `f` is locally Lipschitz on the open set `U ⊆ ℝ^P` and `K ⊆ U` is compact, there are `C ≥ 0` and `ρ > 0` such that for every `x ∈ K` the ball `B_ρ(x)` lies in `U` and `f` is `C`-Lipschitz on it.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_tangential_differential_exists`

#### `lpf_tde_chart_directional_deriv` (L45433)

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_directional_deriv-a1` · issue #2407 · PR #2964 · candidate `3dcce9d73b9f`
- **Statement and proof**: Simon Ch. 3 §2 (p. 76), fact (DD) at one chart point: if `f` is `K`-Lipschitz on `B_ρ(Φ(w))`, `DΦ(w) = A` and `D(f ∘ Φ)(w) = B`, then `t ↦ f(Φ(w) + t A s)` has derivative `B s` at `t = 0`, and `|B s| ≤ K |A s|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_tangential_differential_exists`

#### `lpf_pushforward_is_current` (L46182)

- `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1` · issue #738 · PR #2537 · candidate `4cf8ae752e5f`
- **Statement and proof**: **Simon Ch. 6, (3.6) (p. 147): the push-forward formula defines a current.**  Let `T = τ(M, θ, ξ)` in the open `U`, `f` continuous on `U` with `f⁻¹(K) ∩ spt T` compact for every compact `K ⊆ V`, and `L` an `Hⁿ ⌞ M`-a.e. strongly measurable field of linear maps bounded on `M ∩ K` for every compact `K ⊆ U`.  Then `ω ↦ ∫_M θ(x) ⟨ω(f(x)), L(x)_# ξ(x)⟩ dHⁿ(x)` is a current in `𝒟ₙ(V)`: the density `θ L_# ξ` is `Hⁿ ⌞ M`-a.e. strongly measurable, and on `{f ∈ K}` it is dominated by `1_{K'} Cⁿ θ` with `K' = f⁻¹(K) ∩ spt T`, because `Hⁿ(M \ spt T) = 0`.
- **Calls**: `lpf_rectifiable_support_null`, `lpf_pic_density_aestronglyMeasurable`, `lpf_pic_density_dominated`, `lpf_pic_current_of_dominated_density`
- **Called by**: `lipschitz_pushforward_integer_multiplicity`

#### `lpf_rectifiable_support_null` (L13320)

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1` · issue #720 · PR #2267 · candidate `b0d12af0ae3d`
- **Statement and proof**: **A rectifiable representation lives on the support (step (P2) of Simon Ch. 6, Lemma 3.9).** If `T = τ(M, θ, ξ)` then `Hⁿ(M \ spt T) = 0`.  An orthonormal frame `τ` has Gram matrix `1`, so `‖simpleNVector τ‖ = 1` by `lpf_simple_nvector_algebra` and `‖ξ‖ = 1` `Hⁿ`-a.e. on `M` (`orients`).  Hence `Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes (`lpf_rsn_local_null`), and countably many such `W` cover the zero region of `T` (`lpf_rsn_null_diff_support_of_local_null`).
- **Calls**: `lpf_simple_nvector_algebra`, `lpf_rsn_null_diff_support_of_local_null`, `lpf_rsn_local_null`
- **Called by**: `fiw_tb_ext_isIntegerMultiplicity`, `deformation_im_pushforward_limit`, `lpf_pushforward_integrality`, `lpf_pushforward_is_current`

#### `lpf_simple_nvector_algebra` (L9768)

- `root.lipschitz_pushforward_im-a1.simple_nvector_algebra-a1` · issue #718 · PR #1635 · candidate `d57bd3700c22`
- **Statement and proof**: **Simple `n`-vectors (step (P1) of Simon Ch. 6, Lemma 3.9).**  The operator norm of `v₁ ∧ ⋯ ∧ vₙ = simpleNVector v` is the square root of the Gram determinant `det (⟪vᵢ, vⱼ⟫)`, and a change of frame `τ ↦ Bτ` multiplies `simpleNVector τ` by `det B`.  The second identity is the uniqueness of alternating forms on `ℝⁿ` (`AlternatingMap.eq_smul_basis_det`).  A dependent `v` makes both sides of the first vanish.  An independent `v` is `Bτ` for an orthonormal basis `τ` of `span v`, so `G(v) = B Bᵀ`; `|α τ| ≤ ‖α‖` and the covector `u ↦ det (⟪τᵢ, uⱼ⟫)` (norm `≤ 1` by Hadamard's and Bessel's inequalities, value `1` at `τ`) give `‖simpleNVector v‖ = |det B|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_rectifiable_support_null`, `iwl_im_patching`, `deformation_ipl_cc_chart_orientation_sign`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`, `deformation_skeleton_polyhedral`

#### `lpf_rsn_null_diff_support_of_local_null` (L9159)

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.support_null_reduction-a1` · issue #1179 · PR #1961 · candidate `3f6ddbcb5a98`
- **Statement and proof**: If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`: `M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_rectifiable_support_null`

#### `lpf_rsn_local_null` (L9247)

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.local_null_on_vanishing_open-a1` · issue #1182 · PR #2111 · candidate `b405c044b9ac`
- **Statement and proof**: **A representation is null where the current vanishes (steps 5–8 of (P2) in Simon Ch. 6, Lemma 3.9).**  If `T = τ(M, θ, ξ)` with `M` `Hⁿ`-null-measurable, `θ > 0` on `M`, `ξ` `Hⁿ⌞M`-a.e. strongly measurable **[corrected]** and `‖ξ‖ = 1` `Hⁿ`-a.e. on `M`, `T` vanishes on the open set `W ⊆ U` and `θ` is integrable on `M ∩ W`, then `Hⁿ(M ∩ W) = 0`.  Testing `T` with `φ α` (`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so `⟨α, ξ⟩ = 0` a.e. on `M ∩ W` (`lpf_rsn_weighted_fundamental_lemma`).  Finitely many covectors separate `n`-vectors (`lpf_rsn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`; as `‖ξ‖ = 1` a.e. on `M`, the set `M ∩ W` is null.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits three hypotheses of the Lean statement (line 9247). `θ > 0` is necessary: for `θ ≡ 0` the current `τ(M, θ, ξ)` vanishes whatever `M` is.
- **Calls**: `lpf_rsn_weighted_fundamental_lemma`, `lpf_rsn_covector_separating_family`
- **Called by**: `lpf_rectifiable_support_null`

#### `lpf_rsn_weighted_fundamental_lemma` (L9215)

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.weighted_fundamental_lemma-a1` · issue #1181 · PR #2011 · candidate `57d868d3730c`
- **Statement and proof**: **Fundamental lemma of the calculus of variations with a positive weight** (a step of the proof that a rectifiable `τ(M, θ, ξ)` lives on its support, Simon Ch. 6, 3.9).  If `θ > 0` on `M`, `θ` is `μ`-integrable on `M ∩ W` with `W` open, `g` is a.e.-strongly measurable and a.e. bounded for `μ ⌞ M`, and `∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with `tsupport φ ⊆ W`, then `g = 0` `μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`, which is integrable on `W` for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_rsn_local_null`

#### `lpf_rsn_covector_separating_family` (L9183)

- `root.lipschitz_pushforward_im-a1.rectifiable_support_null-a1.covector_separating_family-a1` · issue #1180 · PR #1948 · candidate `9d4dd6d3f7b2`
- **Statement and proof**: Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Lemma 3.9 to show that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set).  Evaluation on tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds `Λⁿ(ℝ^P)` linearly into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values on basis vectors. So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis `b₁, …, b_N` is zero.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_rsn_local_null`

#### `lpf_pic_density_aestronglyMeasurable` (L45873)

- `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_measurable-a1` · issue #1066 · PR #1626 · candidate `1caba2144799`
- **Statement and proof**: Measurability of the push-forward density in Simon Ch. 6, (3.6) (p. 147): for a rectifiable triple `(M, θ, ξ)` in an open `U` and an `Hⁿ⌞M`-a.e. strongly measurable `L`, the density `x ↦ θ(x) L(x)_# ξ(x)` is `Hⁿ⌞M`-a.e. strongly measurable.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pushforward_is_current`

#### `lpf_pic_density_dominated` (L45898)

- `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_dominated-a1` · issue #1067 · PR #1878 · candidate `be6570f329d4`
- **Statement and proof**: **Domination of the push-forward density on a compact preimage (Simon Ch. 6, (3.6)).**  Let `(M, θ, ξ)` be a rectifiable triple in `U`, `Z ⊆ U` with `Hⁿ(M \ Z) = 0`, `K' = f⁻¹(K) ∩ Z` compact and `‖L x‖ ≤ C` on `M ∩ K'`.  Then `h = 1_{K'} Cⁿ θ` is `Hⁿ ⌞ M`-integrable (`θ` is integrable on `M ∩ K'`, as `K' ⊆ U` is compact) and `‖θ(x) L(x)_# ξ(x)‖ ≤ h(x)` for `Hⁿ ⌞ M`-a.e. `x` with `f x ∈ K`: a.e. such `x` lies in `M ∩ K'`; `‖A_# v‖ ≤ ‖A‖ⁿ ‖v‖` because `A_# v = v ∘ A^#` and `‖A^# β‖ ≤ ‖A‖ⁿ ‖β‖`; and `‖ξ(x)‖ ≤ 1` because `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pushforward_is_current`

#### `lpf_pic_current_of_dominated_density` (L45784)

- `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.current_of_dominated_density-a1` · issue #1065 · PR #1916 · candidate `52afef6d786b`
- **Statement and proof**: Simon Ch. 6, (3.6): if `g` is `μ`-a.e. measurable, then a `μ`-a.e. strongly measurable **[corrected]** `n`-vector density `w` that is dominated by an integrable function on `g⁻¹(K)` for every compact `K ⊆ V` defines a current `ω ↦ ∫ ⟨ω(g x), w x⟩ dμ(x)` in `𝒟ₙ(V)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the measurability of `g` and `w`, which the Lean statement (line 45785) assumes; without it the integrals that define the current need not exist.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pushforward_is_current`

#### `lpf_pushforward_integrality` (L45407)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1` · issue #741 · PR #4444 · candidate `33923222a994`
- **Statement and proof**: **Simon Ch. 6, Lemma 3.9 (p. 148), integrality of the push-forward.**  If `T = τ(M, θ, ξ)` is integer multiplicity, `f` is locally Lipschitz on `U` with `f(U) ⊆ V` and `f | spt T` proper, `L` is the a.e. tangential differential of `f` on `M`, and `S(ω) = ∫_M θ ⟨ω ∘ f, L_#ξ⟩ dHⁿ`, then `S` is integer multiplicity (printed 3.4–3.9). * Source side (`Submission.lpf_pi_source_charts`; Steps 1, 3, 6): for `Hⁿ`-a.e. `x ∈ M` with `L_#ξ(x) ≠ 0`, `L_#ξ(x) = ±‖L_#ξ(x)‖ σ₁ ∧ ⋯ ∧ σₙ` for an orthonormal frame `σ` of the tangent plane `DG_k(w)(ℝⁿ)` of a `C¹` antilipschitz chart `G_k` with `G_k(w) = f(x)`. * Image density (`Submission.lpf_pi_image_density`; Steps 4, 5, 8, 9): by the area formula `Submission.lpf_rectifiable_area_formula`, `S(ω) = ∫_Y ⟨ω, Ψ⟩ dHⁿ` with `Ψ(y)` the fibre sum `∑_{x ∈ M₊, f(x) = y} θ(x) ‖L_#ξ(x)‖⁻¹ L_#ξ(x)` over `M₊ = M ∩ {L_#ξ ≠ 0}` **[corrected]**, an integer combination of unit simple `n`-vectors on chart planes. * Target side (`Submission.lpf_pi_im_of_chart_density`; Steps 7, 8, 10, 11): such a representation is `τ(M', θ', ξ')` with `θ'` positive integer-valued.
- **Correction**: the Lean doc comment, which is kept byte-identical as part of the accepted declaration text (§9), writes the fibre sum as `∑_{f(x) = y} θ(x) L_#ξ(x)`, without the normalization. That formula is wrong, and the passage above is corrected. Write `Ξ = L_#ξ` and `M₊ = M ∩ {Ξ ≠ 0}`. Points of `M ∖ M₊` contribute nothing to `S`. The area formula `lpf_rectifiable_area_formula` has Jacobian `‖Ξ‖`, the norm of the push-forward of the unit simple `n`-vector `ξ`. Its signed form (`lpf_pi_signed_fibre_sum`) therefore gives `S(ω) = ∫_{M₊} θ ‖Ξ‖⁻¹ ⟨ω ∘ f, Ξ⟩ ‖Ξ‖ dHⁿ = ∫ ⟨ω(y), ∑_{x ∈ M₊ ∩ f⁻¹(y)} θ(x) ‖Ξ(x)‖⁻¹ Ξ(x)⟩ dHⁿ(y)`. Without the factor `‖Ξ(x)‖⁻¹`, the image density would be wrong. For example, take `T = [[0, 1]]` in `ℝ` (`M = [0, 1]`, `θ = 1`, `ξ = e₁`) and `f(x) = x/2`, so `Ξ = e₁/2`. The un-normalized sum gives multiplicity `1/2` on `[0, 1/2]`, whereas `S(ω) = ∫₀¹ ⟨ω(x/2), e₁/2⟩ dx = ∫₀^{1/2} ⟨ω(y), e₁⟩ dy`, i.e. `S = [[0, 1/2]]` with multiplicity `1`. With the normalization, the source-side bullet gives `θ(x) ‖Ξ(x)‖⁻¹ Ξ(x) = ±θ(x) σ₁ ∧ ⋯ ∧ σₙ`, an integer multiple of a unit simple `n`-vector, as the passage claims. The Lean proof is not affected, because the doc comment is neither part of the declaration's type nor of its proof. This proof takes `Y` and `Ψ` from `lpf_pi_image_density`. That lemma defines `Ψ(y) = ∑'_{x ∈ M₊, f x = y} (θ x * ‖Ξ x‖⁻¹) • Ξ x` in its proof, and its statement records the two properties used here: `Ψ(y)` is a.e. an integer combination of unit simple `n`-vectors on chart planes, and `S(ω) = ∫_Y ⟨ω, Ψ⟩ dHⁿ` (see its entry below and §3.4).
- **Calls**: `lpf_simple_nvector_algebra`, `lpf_pi_source_charts`, `lpf_countably_rectifiable_c1_cover`, `lpf_chart_chain_rule`, `lpf_lipschitz_c1_immersion_pieces`, `lpf_pi_local_finite_weight`, `lpf_rectifiable_support_null`, `lpf_pi_measurability`, `lpf_pi_image_density`, `lpf_locally_lipschitz_image`, `lpf_rectifiable_area_formula`, `lpf_pi_im_of_chart_density`, `lpf_weighted_tangent_on_c1_chart`
- **Called by**: `lipschitz_pushforward_integer_multiplicity`

#### `lpf_pi_source_charts` (L8344)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.source_charts-a1` · issue #2655 · PR #3895 · candidate `01ef99809f95`
- **Statement and proof**: Source charts for Simon Ch. 6, Lemma 3.9 (p. 148): under (SNA), (CRC), (CCR) and (LCIP), countably many `C¹` maps `G k`, antilipschitz on open `O k`, carry the push-forward orientation: for `Hⁿ`-a.e. `x ∈ M` with `L(x)_# ξ(x) ≠ 0` there are `k` and `w ∈ O k` with `G k w = f x` and `L(x)_# ξ(x) = ±‖L(x)_# ξ(x)‖ σ₁ ∧ ⋯ ∧ σₙ` for an orthonormal basis `σ` of `range DG_k(w)`.
- **Calls**: `lpf_pi_induced_orientation`
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_pi_induced_orientation` (L7988)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.induced_orientation-a1` · issue #2576 · PR #3533 · candidate `5553df438424`
- **Statement and proof**: The orientation induced by a linear map (Simon Ch. 6, 3.4–3.5, p. 147, at a single point): if `τ` is orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₙ` and `A_# w ≠ 0`, then `Aτ₁, …, Aτₙ` are linearly independent, and for their Gram–Schmidt orthonormalization `σ` (same span) `A_# w = ±|A_# w| σ₁ ∧ ⋯ ∧ σₙ`.  Writing `Aτᵢ = ∑ⱼ Bᵢⱼ σⱼ`, the determinant identity of the hypothesis gives `A_# w = ±det B σ₁ ∧ ⋯ ∧ σₙ`, and `|σ₁ ∧ ⋯ ∧ σₙ| = 1` (`Submission.lpf_pi_simple_unit_facts`), so `|A_# w| = |det B|`.
- **Calls**: `lpf_pi_simple_unit_facts`
- **Called by**: `lpf_pi_source_charts`

#### `lpf_pi_simple_unit_facts` (L7929)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.simple_unit_facts-a1` · issue #2550 · PR #3498 · candidate `a6e4e44adce8`
- **Statement and proof**: Unit simple `n`-vectors orienting the same `n`-plane agree up to sign (the orientations `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of Simon Ch. 6, 3.1), given the simple `n`-vector algebra `‖v₁ ∧ ⋯ ∧ vₙ‖² = det(⟨vᵢ, vⱼ⟩)` and `(∑ⱼ B₁ⱼ τⱼ) ∧ ⋯ ∧ (∑ⱼ Bₙⱼ τⱼ) = det B · τ₁ ∧ ⋯ ∧ τₙ`. An orthonormal `σ` has Gram matrix `1`, so `‖σ₁ ∧ ⋯ ∧ σₙ‖ = 1`.  If `σ, σ'` span the same plane, then `σ'ᵢ = ∑ⱼ Bᵢⱼ σⱼ`, so `σ'₁ ∧ ⋯ ∧ σ'ₙ = det B · σ₁ ∧ ⋯ ∧ σₙ`, and taking norms gives `|det B| = 1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pi_induced_orientation`, `lpf_pi_im_of_chart_density`

#### `lpf_chart_chain_rule` (L40437)

- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1` · issue #735 · PR #3692 · candidate `a42b48e8b29b`
- **Statement and proof**: Chain rule on a `C¹` antilipschitz chart (Simon Ch. 6, proof of 3.9, steps 2 and 5.2): for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`, `DΦ(w)(ℝⁿ)` is the weighted approximate tangent space of `(M, θ)` at `Φ(w)` and `D(f∘Φ)(w) = L(Φ w) ∘ DΦ(w)`.  The tangent identification and the derivative clause for `L` hold `Hⁿ`-a.e. on `M`, hence at `Φ w` for a.e. parameter; `f∘Φ` is differentiable a.e. (Rademacher); and along each `DΦ(w)s ∈ TₓM` both `L(Φ w)` and `D(f∘Φ)(w)` give the derivative of `t ↦ f(Φ(w) + t DΦ(w)s)` at `0`.
- **Calls**: `lpf_ccr_ae_pullback`, `lpf_weighted_tangent_on_c1_chart`, `lpf_ccr_ae_differentiableAt_comp`, `lpf_ccr_hasDerivAt_line_of_comp`
- **Called by**: `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `deformation_ipl_chart_convergence`, `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`

#### `lpf_ccr_ae_pullback` (L39909)

- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1` · issue #2422 · PR #3035 · candidate `841085c6a9d7`
- **Statement and proof**: `Hⁿ`-a.e. properties pull back along antilipschitz charts (used for Simon Ch. 6, 3.9): if `M` is `Hⁿ`-null-measurable, `Ω` and `Φ` are measurable and `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω` with `c > 0`, then `Ω ∩ Φ⁻¹(M)` is `Lⁿ`-null-measurable, and a property holding `Hⁿ`-a.e. on `M ∩ Φ(Ω)` holds at `Φ w` for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`.
- **Calls**: `lpf_raf_chart_preimage_null`
- **Called by**: `deformation_ipl_cc_chart_orientation_sign`, `lpf_chart_chain_rule`, `slicing_im_ll_twl_coefficient_field`, `slicing_im_ll_twl_chart_hasFDerivAt`

#### `lpf_raf_chart_preimage_null` (L18493)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_preimage_null-a1` · issue #1072 · PR #1472 · candidate `9080c178c7e2`
- **Statement and proof**: Antilipschitz charts pull back `Hⁿ`-null sets to `Lⁿ`-null sets (Simon Ch. 3, proof of 2.4, p. 77 **[corrected]**; used for Ch. 6, 3.9): if `c ‖w - w'‖ ≤ ‖Φ w - Φ w'‖` on `Ω` with `c > 0`, then `Φ` has a `c⁻¹`-Lipschitz inverse `Ψ` on `Φ(Ω)` with `Ω ∩ Φ⁻¹(Z) ⊆ Ψ(Φ(Ω) ∩ Z)`, so `Hⁿ(Z) = 0` gives `Lⁿ(Ω ∩ Φ⁻¹(Z)) = Hⁿ(Ω ∩ Φ⁻¹(Z)) = 0`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), cites "Simon Ch. 3, proof of 2.6". Item 2.6 of Ch. 3 (p. 77) has no proof of its own: it is the case of 2.5 in which `f|M` is one-to-one. The fact used here closes the proof of 2.4 on p. 77: a locally Lipschitz map sends `Hⁿ`-null sets to `Hⁿ`-null sets. Here it is applied to the Lipschitz inverse `Ψ`. The lemma serves the formal version of 2.6 with a weight, `lpf_raf_chart_change_of_variables`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_raf_chart_jacobian_ae`, `lpf_raf_chart_change_of_variables`, `lpf_ccr_ae_pullback`, `deformation_skeleton_polyhedral`

#### `lpf_ccr_ae_differentiableAt_comp` (L40402)

- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_diff_comp-a1` · issue #2431 · PR #3543 · candidate `f8ca7a783787`
- **Statement and proof**: Rademacher for `f ∘ Φ`: if `f` is locally Lipschitz on an open `U ⊆ ℝ^P` and `Φ : ℝⁿ → ℝ^P` is `C¹`, then `f ∘ Φ` is differentiable at `Lⁿ`-a.e. `w` with `Φ w ∈ U`.
- **Calls**: `lpf_lli_countable_lipschitz_cover`
- **Called by**: `lpf_chart_chain_rule`

#### `lpf_lli_countable_lipschitz_cover` (L10487)

- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.countable_lipschitz_cover-a1` · issue #979 · PR #1627 · candidate `6941b70febfe`
- **Statement and proof**: Countable Lipschitz cover (Lindelöf): if `f` is locally Lipschitz on an arbitrary `U ⊆ ℝ^P`, then countably many open sets `O i` cover `U` and `f` is `K i`-Lipschitz on each `O i ∩ U`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_locally_lipschitz_image`, `lpf_raf_lla_disjoint_lipschitz_pieces`, `lpf_ccr_ae_differentiableAt_comp`

#### `lpf_ccr_hasDerivAt_line_of_comp` (L21211)

- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.line_deriv_comp-a1` · issue #2445 · PR #3171 · candidate `32fbf107157c`
- **Statement and proof**: Simon Ch. 2, 4.7/4.10 (used for Ch. 6, 3.9): if `f` is `K`-Lipschitz on a neighbourhood `V` of `Φ(w)` and both `Φ` and `f ∘ Φ` are differentiable at `w`, then `t ↦ f(Φ(w) + t DΦ(w)s)` has derivative `D(f∘Φ)(w)s` at `0`.  For small `t` it differs from `t ↦ f(Φ(w + ts))` by at most `K ‖Φ(w + ts) - Φ(w) - t DΦ(w)s‖ = o(t)`, and the latter map has derivative `D(f∘Φ)(w)s`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_chart_chain_rule`, `slicing_im_st_chart_data`

#### `lpf_pi_local_finite_weight` (L23260)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.local_finite_weight-a1` · issue #2607 · PR #3541 · candidate `fe5e41020e2a`
- **Statement and proof**: **Local finiteness of the pushed-forward weight (Step 4(b) of the integrality of `f_# T`, Simon Ch. 6, Lemma 3.9).**  Let `T = τ(M, θ, ξ)` in the open `U`, `f` locally Lipschitz on `U` with `f⁻¹(K) ∩ spt T` compact for every compact `K ⊆ V`, and `L` given by the derivative clause. Then `∫_{M ∩ f⁻¹(K)} θ ‖L_# ξ‖ dHⁿ < ∞` for compact `K ⊆ V`.  Off the `Hⁿ`-null set `M \ spt T` (hypothesis (RSN), the statement of `lpf_rectifiable_support_null`), `M ∩ f⁻¹(K)` lies in the compact `K' = f⁻¹(K) ∩ spt T ⊆ U`.  There `‖L_# ξ‖ ≤ C` a.e. (`lpf_pi_jacobian_local_bound`) and `θ` is integrable (`IsRectifiableTriple.integrableOn`).
- **Calls**: `lpf_pi_jacobian_local_bound`
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_pi_jacobian_local_bound` (L8073)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.jacobian_local_bound-a1` · issue #2594 · PR #3485 · candidate `c19a8600fe53`
- **Statement and proof**: Step 2 of Simon Ch. 6, Lemma 3.9 (p. 148): local essential bound for the tangential Jacobian of the push-forward (3.6).  If `(M, θ, ξ)` is a rectifiable triple in `U`, `f` is locally Lipschitz on `U` and `L x` agrees `Hⁿ⌞M`-a.e. with the directional derivatives of `f` along the approximate tangent space, then `‖(L x)_# ξ(x)‖` is essentially bounded on `M ∩ K` for compact `K ⊆ U`: with `Λ` a Lipschitz constant of `f` on a compact neighbourhood of `K` in `U`, `|L(x) τᵢ| ≤ Λ` for the orthonormal frame `τ` of `TₓM`, so `‖(L x)_# (±τ₁ ∧ ⋯ ∧ τₙ)‖ ≤ ∏ᵢ |L(x) τᵢ| ≤ Λⁿ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pi_local_finite_weight`

#### `lpf_pi_measurability` (L8136)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.measurability-a1` · issue #2602 · PR #3540 · candidate `a2a69a08f815`
- **Statement and proof**: Measurability part of Step 1 of the integrality of the Lipschitz push-forward (Simon Ch. 6, (3.6) and Lemma 3.9, pp. 147–148): for a rectifiable triple `(M, θ, ξ)` in an open `U` and an `Hⁿ⌞M`-a.e. strongly measurable `L`, the multiplicity `θ` is `Hⁿ⌞M`-a.e. measurable and `x ↦ L(x)_# ξ(x)` is `Hⁿ⌞M`-a.e. strongly measurable.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_pi_image_density` (L8494)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1` · issue #2665 · PR #3751 · candidate `393a8daba3f9`
- **Statement and proof**: Image `n`-vector density of the push-forward (fibre sums over `M₊ = M ∩ {Ξ ≠ 0}`).  The counting function `N(y) = Σ'_{x ∈ M₊, f x = y} θ x` is locally integrable on `V` by (AF) and (LF).  On `Y = {y ∈ V : N(y) ≠ 0, N(y) ≠ ∞}` every fibre is finite, and `Ψ(y) = Σ_{x ∈ M₊, f x = y} (θ x * ‖Ξ x‖⁻¹) • Ξ x` is locally integrable, is a.e. an integer combination of unit simple `n`-vectors on chart tangent planes (by (CH), off the null image of the exceptional set), and represents `S` (via the signed fibre sum `Submission.lpf_pi_signed_fibre_sum`).
- **Calls**: `lpf_pi_covector_finiteDimensional`, `lpf_pi_signed_fibre_sum`
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_pi_covector_finiteDimensional` (L8283)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.covector_finite_dimensional-a1` · issue #2635 · PR #3548 · candidate `662fd8919e80`
- **Statement and proof**: The space of `n`-covectors on `ℝ^Q` is finite-dimensional: `α ↦ (α(e_{r(1)}, …, e_{r(n)}))_r` (`r : Fin n → Fin Q`) is a linear injection into the finite coordinate space `(Fin n → Fin Q) → ℝ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pi_image_density`

#### `lpf_pi_signed_fibre_sum` (L8161)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.signed_fibre_sum-a1` · issue #2621 · PR #3559 · candidate `db4569b324be`
- **Statement and proof**: Signed form of a fibre-sum area identity.  Let `J : X → [0, ∞]` be `μ⌞A`-a.e. measurable **[corrected]**. If `∫⁻_A h J dμ = ∫⁻ ∑'_{x ∈ A, f x = y} h x dν(y)` with the fibre sum `ν`-a.e. measurable **[corrected]**, for every `μ⌞A`-a.e. measurable `h : X → [0, ∞]`, and `g : X → ℝ` is `μ⌞A`-a.e. strongly measurable with `∫⁻_A ‖g‖ₑ J dμ < ∞`, then for `ν`-a.e. `y` the fibre family of `g` over `y` is summable, the fibre sum of `g` is `ν`-integrable and `∫_A g J dμ = ∫ ∑'_{x ∈ A, f x = y} g x dν(y)`.  Apply the identity to `ofReal ∘ g` and `ofReal ∘ (-g)`: both sides equal the difference of the two finite lintegrals, the source side because `g = 0` a.e. where `J = ∞`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not introduce `J`. In the Lean statement (line 8163) `J` is `[0, ∞]`-valued and `μ⌞A`-a.e. measurable, and the hypothesis includes the `ν`-a.e. measurability of the fibre sums (lines 8164–8166).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pi_image_density`

#### `lpf_locally_lipschitz_image` (L10516)

- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1` · issue #723 · PR #2036 · candidate `e74e195a1134`
- **Statement and proof**: Locally Lipschitz images (step (P3) of Simon Ch. 6, Lemma 3.9; cf. Ch. 2, Theorem 1.8(i)). If `f` is locally Lipschitz on `U ⊆ ℝ^P`, then `f` maps `Hⁿ`-null subsets of `U` to `Hⁿ`-null sets, and `Hⁿ`-null-measurable `A ⊆ U` with `Hⁿ ⌞ A` σ-finite to `Hⁿ`-null-measurable sets.
- **Calls**: `lpf_lli_countable_lipschitz_cover`, `lpf_lli_inner_compact_approx` (A.3)
- **Called by**: `lpf_rectifiable_area_formula`, `lpf_pushforward_integrality`

#### `lpf_rectifiable_area_formula` (L45312)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1` · issue #740 · PR #4280 · candidate `2acb4ed7dac3`
- **Statement and proof**: Area formula on a rectifiable set (Simon Ch. 3, 2.4–2.5), with `J^M f = ‖L_# ξ‖`: for `Hⁿ`-null-measurable `A ⊆ M` and `Hⁿ⌞A`-a.e. measurable `h : ℝ^P → [0, ∞]` **[corrected]**, the fibre sum `y ↦ ∑_{x ∈ A ∩ f⁻¹(y)} h(x)` is `Hⁿ`-a.e. measurable and `∫_A h ‖L_# ξ‖ dHⁿ = ∫ ∑_{x ∈ A ∩ f⁻¹(y)} h(x) dHⁿ(y)`. `A` is cut into the pieces `A ∩ disjointed (Φⱼ(Ωⱼ)) j` of the `C¹` chart cover; on each piece the chart area formula applies, and the rest of `A` is `Hⁿ`-null with `Hⁿ`-null image.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says only "`h ≥ 0`". The Lean statement (line 45322) assumes `h` `Hⁿ⌞A`-a.e. measurable, and the claimed measurability of the fibre sum needs it: for `f = id` on `M = A = [0, 1]ⁿ` the fibre sum is `h` itself, which need not be measurable.
- **Calls**: `lpf_countably_rectifiable_c1_cover`, `lpf_locally_lipschitz_image`, `lpf_raf_pushforward_enorm_aemeasurable`, `lpf_chart_chain_rule`, `lpf_raf_chart_jacobian_ae`, `lpf_simple_nvector_algebra`, `lpf_raf_chart_area_formula`, `lpf_raf_fiber_sum_glue`
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_raf_pushforward_enorm_aemeasurable` (L23236)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.pushforward_enorm_aemeasurable-a1` · issue #1080 · PR #2010 · candidate `3210ebf9ba88`
- **Statement and proof**: A.e. measurability of the push-forward density `x ↦ ‖L(x)_# ξ(x)‖` (Simon Ch. 6, (3.6), as used in the area formula of Ch. 3, §2).  The map `(A, w) ↦ A_# w = w ∘ A^#` is jointly continuous (the pullback `A ↦ A^#` is continuous and composition of continuous linear maps is jointly continuous), so it carries the a.e. strongly measurable pair `(L, ξ)` to an a.e. strongly measurable function; its norm is then a.e. measurable, and `‖v‖ₑ = ofReal ‖v‖`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_rectifiable_area_formula`

#### `lpf_raf_chart_jacobian_ae` (L20897)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_jacobian_ae-a1` · issue #1077 · PR #1895 · candidate `4aee0e083b8d`
- **Statement and proof**: A.e. Jacobian identity on a `C¹` antilipschitz chart (Simon Ch. 6, 3.9 via Ch. 3, 2.4–2.5): for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`, `θ(Φ w) > 0`, the orientation `ξ(Φ w) = ±τ₁ ∧ ⋯ ∧ τₙ` holds (its `Hⁿ`-null exceptional set pulls back to an `Lⁿ`-null set), the tangent plane `range DΦ(w) = span τ` is unique, and the Jacobian identity with `D(f ∘ Φ)(w) = L(Φ w) ∘ DΦ(w)` gives `‖L(Φ w)_# ξ(Φ w)‖ · JΦ(w) = J(f ∘ Φ)(w)`.
- **Calls**: `lpf_raf_chart_preimage_null`, `lpf_raf_jacobian_identity`
- **Called by**: `lpf_rectifiable_area_formula`

#### `lpf_raf_jacobian_identity` (L20823)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.jacobian_identity-a1` · issue #1075 · PR #1414 · candidate `b382b2aba005`
- **Statement and proof**: Jacobian identity for one linear map (Simon Ch. 6, 3.4–3.5, p. 147): given (S1) `‖v₁ ∧ ⋯ ∧ vₙ‖² = det(⟨vᵢ, vⱼ⟩)` and (S2) `simpleNVector (B τ) = det B • simpleNVector τ`, if `τ` is orthonormal, `A : ℝⁿ → ℝ^P` takes values in `span τ` and `ξ = ±τ₁ ∧ ⋯ ∧ τₙ`, then `‖L_# ξ‖ · √det(⟨A eᵢ, A eⱼ⟩) = √det(⟨L A eᵢ, L A eⱼ⟩)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_raf_chart_jacobian_ae`

#### `lpf_raf_chart_area_formula` (L21148)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_area_formula-a1` · issue #1079 · PR #2839 · candidate `75b8b2de8736`
- **Statement and proof**: **Area formula on one chart piece (Simon Ch. 3, 2.1–2.2, for one piece `A_j` of the proof of the area formula on a countably `n`-rectifiable set).**  Let `f` be locally Lipschitz on the open set `U ⊆ ℝ^P`, `Φ` Lipschitz and `c`-antilipschitz on the open set `Ω ⊆ ℝⁿ`, and `A ⊆ U ∩ Φ(Ω)` `Hⁿ`-measurable, and let `h, J : ℝ^P → [0, ∞]` be `Hⁿ⌞A`-a.e. measurable **[corrected]**.  If `J(Φ w) · JΦ(w) = J(f ∘ Φ)(w)` for a.e. `w ∈ Ω ∩ Φ⁻¹(A)` (Gram-determinant Jacobians), then `N_A(y) = ∑_{x ∈ A, f x = y} h(x)` is `Hⁿ`-a.e. measurable and `∫_A h J dHⁿ = ∫ N_A dHⁿ`. With `D = Ω ∩ Φ⁻¹(A)`: the change of variables `x = Φ(w)` and the Jacobian identity give `∫_A h J dHⁿ = ∫_D h(Φ w) J(f ∘ Φ)(w) dw`; the area formula for `f ∘ Φ`, which is locally Lipschitz on the open set `Ω ∩ Φ⁻¹(U) ⊇ D`, gives `∫ ∑_{w ∈ D, f(Φ w) = y} h(Φ w) dHⁿ(y)`; and `Φ` maps the fibres `{w ∈ D : f(Φ w) = y}` bijectively onto `{x ∈ A : f x = y}`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not introduce `h` and `J`. In the Lean statement (line 21148) they are `[0, ∞]`-valued and `Hⁿ⌞A`-a.e. measurable; the claimed measurability of `N_A` needs the measurability of `h` (for `f = Φ = id` the fibre sum is `h` on `A`).
- **Calls**: `lpf_raf_chart_change_of_variables`, `lpf_raf_local_lipschitz_area`
- **Called by**: `lpf_rectifiable_area_formula`

#### `lpf_raf_chart_change_of_variables` (L21048)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1` · issue #1073 · PR #2746 · candidate `9fc44225b304`
- **Statement and proof**: Change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6 with a weight; used for Ch. 6, 3.9): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω` and `A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable and `g : ℝ^P → [0, ∞]` is `Hⁿ⌞A`-a.e. measurable **[corrected]**, then `D = Ω ∩ Φ⁻¹(A)` is `Lⁿ`-null-measurable, `g ∘ Φ` is a.e.-measurable on `D`, and `∫_A g dHⁿ = ∫_D g(Φ(w)) JΦ(w) dLⁿ(w)`.  This is the area formula for `Φ` on `D`, whose fibre sums are `1_A g` because `Φ` is injective on `Ω`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not introduce `g`. In the Lean statement (line 21048) `g` is `[0, ∞]`-valued and `Hⁿ⌞A`-a.e. measurable; the claimed measurability of `g ∘ Φ` needs this (for `Φ = id` on `Ω = ℝⁿ`, `g ∘ Φ = g`).
- **Calls**: `lpf_raf_chart_preimage_null`, `lpf_raf_local_lipschitz_area`
- **Called by**: `lpf_raf_chart_area_formula`, `deformation_ipl_cc_signed_change_of_variables`, `deformation_ipl_cc_chart_integral_representation`, `slicing_im_creg_box_bulk`, `slicing_im_creg_box_slice_area`, `slicing_im_ll_twl_chart_integral_eq`

#### `lpf_raf_local_lipschitz_area` (L20988)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1` · issue #1070 · PR #2567 · candidate `4b36491e59d4`
- **Statement and proof**: Area formula for a map locally Lipschitz on an open set (Simon Ch. 2, (3.5), localized by the countable decomposition of the proof of Ch. 3, 2.4–2.5; used for Ch. 6, 3.9): if `u` is locally Lipschitz on open `Ω ⊆ ℝⁿ`, `D ⊆ Ω` is `Lⁿ`-null-measurable and `w ≥ 0` is `Lⁿ ⌞ D`-a.e. measurable, then the fibre sum `N(y) = ∑_{x ∈ D, u x = y} w x` is `Hⁿ`-a.e. measurable and `∫_D w Ju dLⁿ = ∫ N dHⁿ`, where `Ju = √det(⟨Du eᵢ, Du eⱼ⟩)`.  Split `D` into disjoint pieces `B m` inside open `V m ⊆ Ω` on which `u` is Lipschitz, apply SimonGMT's area formula for maps Lipschitz on a set to each piece (its within-derivative Jacobian is `Ju` a.e. on `B m`, via a Lipschitz extension of `u|V m`), and glue the pieces.
- **Calls**: `lpf_raf_lla_disjoint_lipschitz_pieces`, `lpf_raf_fiber_sum_glue`
- **Called by**: `lpf_raf_chart_change_of_variables`, `lpf_raf_chart_area_formula`

#### `lpf_raf_lla_disjoint_lipschitz_pieces` (L10550)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1.disjoint_lipschitz_pieces-a1` · issue #1906 · PR #2201 · candidate `06f425e14008`
- **Statement and proof**: Disjoint Lipschitz pieces: if `u` is locally Lipschitz on an open `Ω ⊆ ℝⁿ` and `D ⊆ Ω` is `Lⁿ`-null-measurable, then `D` is covered by pairwise disjoint null-measurable `B m ⊆ D ∩ V m`, where the `V m ⊆ Ω` are open and `u` is `K m`-Lipschitz on `V m`.
- **Calls**: `lpf_lli_countable_lipschitz_cover`
- **Called by**: `lpf_raf_local_lipschitz_area`

#### `lpf_raf_fiber_sum_glue` (L20941)

- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.fiber_sum_glue-a1` · issue #1069 · PR #1419 · candidate `066cbc3bc143`
- **Statement and proof**: Countable gluing of fibre-sum area identities (Simon Ch. 3, proof of 2.4, pp. 76–77 **[corrected]**; used for Ch. 6, 3.9): if `A` is covered, up to a `μ`-null set `Z` with `ν`-null image `f '' Z`, by pairwise disjoint `μ`-null-measurable pieces `B m ⊆ A`, each satisfying `∫_{B m} F dμ = ∫ N_{B m} dν` with an a.e.-measurable fibre sum `N_S(y) = ∑_{x ∈ S, f x = y} h x`, then so does `A`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), cites "Simon Ch. 3, proof of 2.6". Item 2.6 of Ch. 3 has no proof of its own: it is the case of 2.5 in which `f|M` is one-to-one. The gluing is the step of the proof of 2.4 (pp. 76–77) that "conclude[s] 2.4 by summing over `j ≥ 1`", together with the fact stated there that locally Lipschitz maps send `Hⁿ`-null sets to `Hⁿ`-null sets.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_raf_local_lipschitz_area`, `lpf_rectifiable_area_formula`

#### `lpf_pi_im_of_chart_density` (L8980)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.im_of_chart_density-a1` · issue #2687 · PR #3910 · candidate `441bdc5bad6a`
- **Statement and proof**: Integer multiplicity from an integer chart-oriented density (parent Steps 7, 8, 10, 11). Let `Y ⊆ V` (`V` open) be `Hⁿ`-null-measurable with `Hⁿ(Y ∩ K) < ∞`, let `Ψ` be `Hⁿ⌞Y`-a.e. strongly measurable with `‖Ψ‖` integrable on `Y ∩ K`, for compact `K ⊆ V`, and let the `G_k` be `C¹` and antilipschitz on open sets `O_k` **[corrected]**. Let `S(ω) = ∫_Y ⟨ω, Ψ⟩ dHⁿ`, where for `Hⁿ`-a.e. `y ∈ Y`, `Ψ(y) = ∑ᵢ aᵢ σᵢ₁ ∧ ⋯ ∧ σᵢₙ` with `aᵢ ∈ ℤ` and `σᵢ` an orthonormal frame of `DG_{kᵢ}(wᵢ)(ℝⁿ)`, `wᵢ ∈ O_{kᵢ}` **[corrected]** and `G_{kᵢ}(wᵢ) = y`.  By (WTC) for `(Y, 1)` all these planes are the approximate tangent plane of `Y` at `y`, so sign rigidity gives `Ψ(y) = c(y) σ₁ ∧ ⋯ ∧ σₙ` with `c(y) ∈ ℤ` and `‖Ψ(y)‖ = |c(y)|`.  Off a null set, `S = τ(M′, θ′, ξ′)` with `M′ = {y ∈ Y : Ψ(y) ≠ 0}` **[corrected]**, `θ′ = ‖Ψ‖` and `ξ′ = Ψ/‖Ψ‖`; (WTC) for `(M′, θ′)` orients `ξ′`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves these hypotheses of the Lean statement (line 8980) implicit; (WTC) applies to `(Y, 1)` and `(M′, θ′)` only under them. It also writes `M′ = {Ψ ≠ 0}`; the Lean proof takes the points of `Y` where `Ψ ≠ 0`, minus a null set.
- **Calls**: `lpf_pi_simple_unit_facts`, `lpf_pi_chart_image_rectifiable`
- **Called by**: `lpf_pushforward_integrality`

#### `lpf_pi_chart_image_rectifiable` (L8312)

- `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.chart_image_rectifiable-a1` · issue #2640 · PR #3491 · candidate `b0fce8642c84`
- **Statement and proof**: Images of open sets under `C¹` maps `ℝⁿ → ℝ^Q` are countably `n`-rectifiable.  `O` is a countable union of compact sets `C j ⊆ O`; `G` is locally Lipschitz on `O`, hence Lipschitz on each `C j`, and extends to a Lipschitz `g j : ℝⁿ → ℝ^Q`; then `G '' O ⊆ ⋃ j, range (g j)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `lpf_pi_im_of_chart_density`

### A.5 Slicing, 4.4–4.10 (§3.5): `slicing_theorem` and its 145 further declarations

#### `slicing_theorem` (L66972)

- `root.slicing-a1` · issue #322 · PR #5777 · candidate `f27fd6da7e82`
- **Statement and proof**: **Simon Ch. 6, §4 Slicing (4.4–4.10, pp. 153–158).**  Choose for every level `t` a slice `S t = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` (4.6).  Every slice satisfies the support bound 4.8; for integer multiplicity `T`, off one `L¹`-null set of levels every slice is integer multiplicity (4.4, 4.5(2)); and any family of slices obeys the mass bound 4.9–4.10.
- **Calls**: `slicing_exists`, `slicing_support_subset`, `slicing_mass_bound`, `slicing_integer_multiplicity_ae`
- **Called by**: `deformation_theorem`, `polyhedral_approximation`, `integrality_of_weak_limits`, `boundary_rectifiability`, `flat_convergence_iff_weak_convergence`, `main_theorem`

#### `slicing_exists` (L22959)

- `root.slicing-a1.slice_exists-a1` · issue #669 · PR #4871 · candidate `420db8a1d391`
- **Statement and proof**: **Simon Ch. 6, 4.6 (p. 157).**  The slice `⟨T, f, t₋⟩ = ∂(T ⌞ A_t) − (∂T) ⌞ A_t` exists for every level `t`.  `A_t = {x ∈ U | f x < t}` is open, as `f` is continuous on the open set `U`; the representations of `T` and `∂T` from `slicing_mass_representation` restrict to `A_t`, and `∂(T ⌞ A_t) − (∂T) ⌞ A_t` is again a sequentially continuous functional.
- **Calls**: `slicing_mass_representation`
- **Called by**: `slicing_theorem`

#### `slicing_mass_representation` (L22918)

- `root.slicing-a1.mass_representation-a1` · issue #664 · PR #4788 · candidate `59c4caf12f87`
- **Statement and proof**: **Simon Ch. 6, 2.7–2.9 (p. 136 **[corrected]**).**  A current `X ∈ 𝒟ₖ(U)` with `M_W(X) < ∞` for every `W ⊂⊂ U` is represented as `X(ω) = ∫ ⟨ω, v⟩ dμ` (2.7) by a Borel measure `μ` living on `U`, finite on compact subsets of `U`, with `|⟨α, v(x)⟩| ≤ |α|`; the restrictions `(X ⌞ A)(ω) = ∫_A ⟨ω, v⟩ dμ` to Borel sets `A` are currents (2.9) with `M_W(X ⌞ A) = μ(W ∩ A)` for every open `W ⊆ U` (2.8).  `X` extends to continuous compactly supported forms in `U` (`smr_exists_continuous_extension`); the Riesz representation of the extension (`smr_riesz_continuous_forms`) gives `(μ, v)`, and the restriction statements are `smr_restriction_isCurrent` and `smr_restriction_massOn_eq`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives "pp. 136–137". The cited items 2.7–2.9 are printed on p. 136 (as is 2.10); 2.11 is on p. 137.
- **Calls**: `smr_exists_continuous_extension`, `smr_riesz_continuous_forms`, `smr_restriction_isCurrent`, `smr_restriction_massOn_eq`
- **Called by**: `slicing_exists`, `slicing_mass_bound`

#### `smr_exists_continuous_extension` (L21858)

- `root.slicing-a1.mass_representation-a1.continuous_extension-a1` · issue #1324 · PR #3532 · candidate `a5ecd9fcb037`
- **Statement and proof**: Continuous extension of a current of locally finite mass (Simon Ch. 6, 2.7, pp. 136–137, steps P1–P2): there is `L` on continuous forms with `L = X` on test forms, additive and homogeneous on continuous compactly supported forms in `U`, and with `|L φ|` bounded on each compact `K ⊆ U` for `|φ| ≤ 1` (Euclidean coefficient norm).  `L φ` is the limit of `X (ζ j)` along any sequence of test forms `ζ j`, supported in a common `V ⊂⊂ U`, converging to `φ` uniformly; the limit exists and is unique by the mass estimate `|X ω| ≤ M_V(X) · sup |ω|`.
- **Calls**: `smr_covector_coord_isometry`, `smr_exists_testForm_uniform_approx`
- **Called by**: `slicing_mass_representation`

#### `smr_covector_coord_isometry` (L21729)

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1` · issue #1322 · PR #3424 · candidate `eef9547811f6`
- **Statement and proof**: Simon (6.1.2)–(6.1.5): listing the coefficients `α(e_{I(0)}, …, e_{I(k-1)})` over the increasing multi-indices `I` is a linear isomorphism `J` of the `k`-covectors on `ℝ^P` onto `ℝ^N` with `|α| = ‖J α‖` for the Euclidean coefficient norm `|α| = covectorEuclideanNorm α`.
- **Calls**: `smr_ci_covector_eq_zero_of_coord`, `smr_ci_coord_sum_smul_wedge`, `smr_ci_norm_eq_sqrt_sum_coord_sq`
- **Called by**: `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`, `smr_riesz_continuous_forms`, `smr_exists_unit_form_gt`

#### `smr_ci_covector_eq_zero_of_coord` (L21704)

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_vanish-a1` · issue #2622 · PR #3033 · candidate `133aac9a37fc`
- **Statement and proof**: A `k`-covector on `ℝ^P` whose coordinates `α(e_{I(0)}, …, e_{I(k-1)})` vanish for every increasing multi-index `I` is zero.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_covector_coord_isometry`

#### `smr_ci_coord_sum_smul_wedge` (L10040)

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_sum_wedge-a1` · issue #2611 · PR #3028 · candidate `1b431e814455`
- **Statement and proof**: The coordinate wedge covectors are dual to the increasing basis tuples: the `J`-th coordinate of `∑_I c_I dx^I` is `c_J`, i.e. `dx^I(e_{J(0)}, …, e_{J(k-1)}) = δ_{IJ}`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_mlb_exists_form_lintegral_coordNorm_le`, `smr_covector_coord_isometry`

#### `smr_ci_norm_eq_sqrt_sum_coord_sq` (L10076)

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1.norm_coord-a1` · issue #2636 · PR #3167 · candidate `a1716c42aeab`
- **Statement and proof**: The Euclidean coefficient norm of a `k`-covector on `ℝ^P` is the `ℓ²`-norm of its coordinates `α(e_{I(0)}, …, e_{I(k-1)})` over the increasing multi-indices `I : Fin k ↪o Fin P`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_mlb_exists_form_lintegral_coordNorm_le`, `smr_covector_coord_isometry`

#### `smr_exists_testForm_uniform_approx` (L21770)

- `root.slicing-a1.mass_representation-a1.testform_approx-a1` · issue #1323 · PR #2229 · candidate `f8173b174e2d`
- **Statement and proof**: **Mollification step of Simon Ch. 6, 2.7–2.9 (p. 136 **[corrected]**).**  A continuous compactly supported `k`-form `φ` with `tsupport φ ⊆ V`, `V` open, is a uniform limit, in the Euclidean coefficient norm, of test forms supported in `V`.  As `|α| ≤ √M ‖α‖` (`M = #(Fin k → Fin P)`, `‖α‖` the operator norm), it suffices to approximate in `‖·‖`.  The approximant is `χ • (ψ ⋆ φ)`: `ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to `1` exactly on `tsupport φ`, whose support `V'` has compact closure in `V`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives "pp. 136–137". The cited items 2.7–2.9 are printed on p. 136 (as is 2.10); 2.11 is on p. 137.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn`

#### `smr_riesz_continuous_forms` (L22637)

- `root.slicing-a1.mass_representation-a1.riesz_forms-a1` · issue #1326 · PR #3653 · candidate `7b60523bff83`
- **Statement and proof**: Riesz representation of a locally bounded linear functional `L` on the continuous compactly supported `k`-forms in `U` (Simon Ch. 6, 2.7, from Ch. 1, 4.14): `L(φ) = ∫ ⟨φ, v⟩ dμ` with `|v(x)(α)| ≤ |α|` and, `μ`-a.e., `v(x)(α) = 1` for some `|α| ≤ 1`.  The isometry `J : Λᵏ(ℝ^P) ≅ ℝ^N` of `Submission.smr_covector_coord_isometry` (continuous in finite dimension) transfers `L` to `L_H(f) = L(J⁻¹ ∘ f)` on `ℝ^N`-valued functions; `Submission.smr_riesz_borel_euclidean` gives `L_H(f) = ∫ ⟨f, ν⟩ dμ` with Borel `ν`, `‖ν‖ ≤ 1` and `‖ν‖ = 1` `μ`-a.e.; and `v(x)(α) = ⟨ν(x), Jα⟩`, with unit witness `α = J⁻¹(ν(x))`.
- **Calls**: `smr_covector_coord_isometry`, `smr_riesz_borel_euclidean`
- **Called by**: `slicing_mass_representation`

#### `smr_riesz_borel_euclidean` (L22593)

- `root.slicing-a1.mass_representation-a1.riesz_borel-a1` · issue #1325 · PR #3247 · candidate `b25ecc25b937`
- **Statement and proof**: Riesz representation (Simon Ch. 1, 4.14) for a locally bounded functional `L` on `CF_N(U) = {f ∈ C_c(ℝ^P, ℝ^N) : tsupport f ⊆ U}`, `U ⊆ ℝ^P` open: there are a Borel measure `μ` on `ℝ^P` living on `U`, finite on compact subsets of `U`, and a Borel field `ν` with `‖ν‖ ≤ 1` and `‖ν‖ = 1` `μ`-a.e., such that `L f = ∫ ⟨f, ν⟩ dμ` for every `f ∈ CF_N(U)`.
- **Calls**: `smr_rb_transfer_functional`, `smr_rb_borel_riesz_sigma_compact`, `smr_rb_pushforward_subtype`
- **Called by**: `smr_riesz_continuous_forms`

#### `smr_rb_transfer_functional` (L22175)

- `root.slicing-a1.mass_representation-a1.riesz_borel-a1.transfer_functional-a1` · issue #2073 · PR #2727 · candidate `accc0298da56`
- **Statement and proof**: Extension by zero from `↥U` to `ℝ^P` transfers a locally bounded linear **[corrected]** functional `L` on `CF_N(U)` to a locally bounded linear functional `L'` on `C_c(↥U, ℝ^N)`, with `L f = L' (f ∘ ι)` for every `f ∈ CF_N(U)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not say that `L` is linear (additive and homogeneous on `CF_N(U)`), which the Lean statement (line 22175) assumes.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_riesz_borel_euclidean`

#### `smr_rb_borel_riesz_sigma_compact` (L22260)

- `root.slicing-a1.mass_representation-a1.riesz_borel-a1.borel_riesz-a1` · issue #2095 · PR #2974 · candidate `cdfc95dc55d0`
- **Statement and proof**: Riesz representation (Simon Ch. 1, 4.14) with Borel data on a σ-compact locally compact Hausdorff space: a locally bounded functional on `C_c(Y, ℝ^N)` is `g ↦ ∫ ⟨g, ν⟩ dm` for a measure `m` finite on compacts and a Borel field `ν` with `‖ν‖ ≤ 1`, `‖ν‖ = 1` `m`-a.e.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_riesz_borel_euclidean`

#### `smr_rb_pushforward_subtype` (L22536)

- `root.slicing-a1.mass_representation-a1.riesz_borel-a1.pushforward-a1` · issue #2109 · PR #2863 · candidate `64646e28b9da`
- **Statement and proof**: Push-forward of Borel representing data from the open subspace `↥U` to `ℝ^P`: `μ = m.map ι` and the zero extension `ν` of `ν₁` represent the same integrals against every `f ∈ CF_N(U)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_riesz_borel_euclidean`

#### `smr_restriction_isCurrent` (L22732)

- `root.slicing-a1.mass_representation-a1.restriction_current-a1` · issue #1327 · PR #2143 · candidate `a5855f5953ef`
- **Statement and proof**: **Restriction of a measure representation is a current (Simon Ch. 6, (2.9), p. 136).**  If `⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ᵏ(U)`, `μ(K) < ∞` for every compact `K ⊆ U` and `|⟨α, v(x)⟩| ≤ |α|` for all `x` and all `k`-covectors `α`, then for every set `A`, `S(ω) = ∫_A ⟨ω, v⟩ dμ` is a current `S ∈ 𝒟ₖ(U)`.  `S` is linear because every integrand is integrable.  With `M = #(Fin k → Fin P)`, `|α| ≤ √M ‖α‖` for the operator norm; if `ω_j → 0` in `𝒟ᵏ(U)`, the supports lie in one compact `K ⊆ U` and `ω_j → 0` uniformly on `K`, so `|S(ω_j)| ≤ √M μ(K) sup_K ‖ω_j‖ → 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mass_representation`

#### `smr_restriction_massOn_eq` (L22874)

- `root.slicing-a1.mass_representation-a1.restriction_mass-a1` · issue #1331 · PR #4338 · candidate `57be985b01b2`
- **Statement and proof**: **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6 of `slicing_mass_representation`.  Let `μ` be finite on compact subsets of `U`, `|⟨α, v(x)⟩| ≤ |α|`, `x ↦ ⟨α, v(x)⟩` Borel, and, `μ`-a.e., `⟨α, v(x)⟩ = 1` for some `|α| ≤ 1`.  If `S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, `A` Borel, then `M_W(S) = μ(W ∩ A)` for every open `W ⊆ U`. `≤`: an admissible `ω` has `‖⟨ω(x), v(x)⟩‖ ≤ 1_{spt ω}(x)`, so `S(ω) ≤ ∫_A ‖⟨ω, v⟩‖ dμ ≤ μ(spt ω ∩ A) ≤ μ(W ∩ A)`.  `≥`: for `c < μ(W ∩ A)`, `smr_exists_unit_form_gt` gives a continuous compactly supported `φ` with `spt φ ⊆ W`, `|φ| ≤ 1` and `c < ∫_A ⟨φ, v⟩ dμ`, and `smr_ofReal_integral_le_massOn` gives `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)`.
- **Calls**: `smr_exists_unit_form_gt`, `smr_ofReal_integral_le_massOn`
- **Called by**: `slicing_mass_representation`

#### `smr_exists_unit_form_gt` (L22814)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1` · issue #1329 · PR #4098 · candidate `b5389008e353`
- **Statement and proof**: Simon Ch. 6, 2.8–2.9 (p. 136 **[corrected]**), the step `μ(W ∩ A) ≤ M_W(T ⌞ A)` of the mass formula for a restriction: continuous unit forms supported in an open `W ⊆ U` detect `μ(W ∩ A)`, for `μ` finite on compact subsets of `U` and a Borel `v` with `|v(x)(α)| ≤ |α|` for all `x`, `α` and, for `μ`-a.e. `x`, `v(x)(α) = 1` for some `|α| ≤ 1` **[corrected]**.  Write `v(x)(α) = ⟨Jα, u(x)⟩` for an isometry `J` of `(Λᵏ, |·|)` onto `ℝ^N`, so `‖u‖ ≤ 1` and `‖u‖ = 1` `μ`-a.e.  Take a compact Lusin set `C ⊆ W ∩ A ∩ {‖u‖ = 1}` of `u` with `c < μ(C)`, a continuous extension `w` of `u|C` with `‖w‖ ≤ 1` (Tietze) and a cutoff `ψ ∈ [0, 1]`, `ψ = 1` on `C`, with `tsupport ψ ⊆ W` and `μ(support ψ ∖ C) < μ(C) − c` (Urysohn).  Then `φ = J⁻¹(ψ w)` has `|φ| ≤ 1`, and `⟨φ, v⟩ = ⟨ψ w, u⟩` is `1` on `C` and `0` off `support ψ`, so `∫_A ⟨φ, v⟩ dμ > c`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives "pp. 136–137"; 2.8 and 2.9 are printed on p. 136. It also leaves implicit the hypotheses on `(μ, v)` of the Lean statement (line 22814), on which "so `‖u‖ ≤ 1` and `‖u‖ = 1` `μ`-a.e." rests (see `smr_ufd_unit_coord_field`).
- **Calls**: `smr_covector_coord_isometry`, `smr_ufd_unit_coord_field`, `smr_ufd_compact_lusin_set`, `smr_ufd_ball_tietze`, `smr_ufd_small_cutoff`, `smr_ufd_integral_lower_bound`
- **Called by**: `smr_restriction_massOn_eq`

#### `smr_ufd_unit_coord_field` (L21289)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.unit_coord_field-a1` · issue #2154 · PR #2865 · candidate `71e312bb1c69`
- **Statement and proof**: Coordinates of a Borel `k`-vector field `v` with `|v(x)(α)| ≤ |α|` for all `x` and `α` and, for `μ`-a.e. `x`, `v(x)(α) = 1` for some `α` with `|α| ≤ 1` **[corrected]**, in an isometric chart `J` of the `k`-covectors: `u(x) = (v(x)(J⁻¹eᵢ))ᵢ` is Borel, `‖u‖ ≤ 1`, `‖u‖ = 1` `μ`-a.e. and `v(x)(α) = ⟨Jα, u(x)⟩`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these two hypotheses of the Lean statement (lines 21293 and 21295), without which `‖u‖ ≤ 1` and `‖u‖ = 1` fail: since `J` is an isometry, `‖u(x)‖ = sup_{|α| ≤ 1} v(x)(α)`; e.g. `v(x)(α) = 2α(e₁)` for `P = k = N = 1` gives `‖u‖ ≡ 2`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_exists_unit_form_gt`

#### `smr_ufd_compact_lusin_set` (L21492)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1` · issue #2162 · PR #3912 · candidate `a73776b666a3`
- **Statement and proof**: Lusin's theorem with compact sets of large measure (Simon Ch. 1, 1.17, with inner regularity; used for Ch. 6, 2.7–2.9): let `μ` be finite on compact subsets of `U`, `u : ℝ^P → ℝ^N` Borel, `E` Borel and `W ⊆ U` open.  If `c < μ(W ∩ E)`, then some compact `C ⊆ W ∩ E` has `c < μ(C)` and `u|C` continuous.
- **Calls**: `smr_ufd_cl_inner_compact`, `smr_ufd_cl_vector_lusin`
- **Called by**: `smr_exists_unit_form_gt`

#### `smr_ufd_cl_inner_compact` (L21333)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1.inner_compact-a1` · issue #2862 · PR #3482 · candidate `21abad67dc04`
- **Statement and proof**: Compact inner approximation inside an open `W ⊆ U`: if `μ` is finite on compact subsets of `U`, `E` is Borel and `c < μ (W ∩ E)`, then some compact `K ⊆ W ∩ E` has `c < μ K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_ufd_compact_lusin_set`

#### `smr_ufd_cl_vector_lusin` (L21376)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.compact_lusin-a1.vector_lusin-a1` · issue #2869 · PR #3630 · candidate `dd9361e25ccd`
- **Statement and proof**: Lusin's theorem with compact sets (Simon Ch. 1, 1.17, applied coordinatewise): if `μ` is a measure on `ℝ^P`, `u : ℝ^P → ℝ^N` is Borel and `A ⊆ ℝ^P` is Borel with `μ(A) < ∞`, then for every `ε > 0` there is a compact `C ⊆ A` with `μ(A ∖ C) < ε` and `u|C` continuous.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_ufd_compact_lusin_set`

#### `smr_ufd_ball_tietze` (L21517)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.ball_tietze-a1` · issue #2174 · PR #2858 · candidate `e70632735cee`
- **Statement and proof**: Tietze extension into the closed unit ball of `ℝ^N`: if `u` is continuous on a closed set `C ⊆ ℝ^P` with `‖u‖ ≤ 1` on `C`, there is a continuous `w : ℝ^P → ℝ^N` with `‖w‖ ≤ 1` and `w = u` on `C`.  Off `C`, `w` is a continuous selection (partition of unity) of the convex hulls of the values of `u` on `C ∩ B(y, 3 d(y, C))`, as in Dugundji's extension theorem.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_exists_unit_form_gt`

#### `smr_ufd_small_cutoff` (L21598)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.small_cutoff-a1` · issue #2188 · PR #2982 · candidate `75510cd11e79`
- **Statement and proof**: **Small cutoff (step of Simon Ch. 6, 2.7–2.9, p. 136 **[corrected]**).**  If `μ` is finite on compact subsets of `U`, `C` is compact and `W ⊆ U` is open with `C ⊆ W`, then for every `ε > 0` there is a continuous compactly supported `ψ : ℝ^P → [0, 1]` with `tsupport ψ ⊆ W`, `ψ = 1` on `C` and `μ(support ψ ∖ C) < ε`.  Choose `r > 0` with the compact `cthickening r C ⊆ W`; the open thickenings `O j = thickening (r / (j + 1)) C` decrease to `C`, so by continuity from above `μ(O j ∖ C) < ε` for some `j`, and Urysohn's lemma for `C` and `(O j)ᶜ` gives `ψ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives "pp. 136–137". The cited items 2.7–2.9 are printed on p. 136 (as is 2.10); 2.11 is on p. 137.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_exists_unit_form_gt`

#### `smr_ufd_integral_lower_bound` (L21658)

- `root.slicing-a1.mass_representation-a1.unit_form_density-a1.integral_lower_bound-a1` · issue #2203 · PR #2983 · candidate `9cfc88355a08`
- **Statement and proof**: Simon Ch. 6, 2.7–2.9 (the final step of the unit-form density argument): if `|g| ≤ 1`, `g = 1` on `C ⊆ A`, `g = 0` off `S` with `μ(S) < ∞` and `c + μ(S ∖ C) < μ(C)`, then `c < ∫_A g dμ`.  As `g = 1` on `C` and `g = 0` off `S`, `C ⊆ S`, so all measures involved are finite, and `|g| ≤ 1_S` makes `g` integrable.  Then `∫_A g = μ(C) + ∫_{A ∖ C} g` and `|∫_{A ∖ C} g| = |∫_{(A ∖ C) ∩ S} g| ≤ μ(S ∖ C)`, so `∫_A g ≥ μ(C) − μ(S ∖ C) > c`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `smr_exists_unit_form_gt`

#### `smr_ofReal_integral_le_massOn` (L22065)

- `root.slicing-a1.mass_representation-a1.continuous_mass_bound-a1` · issue #1328 · PR #3702 · candidate `627ca1da6bbc`
- **Statement and proof**: **Simon Ch. 6, 2.7–2.9 (p. 136)**, step P6(v) of `slicing_mass_representation`.  If `S(ω) = ∫_A ⟨ω, v⟩ dμ` for every `ω ∈ 𝒟ᵏ(U)`, where `|⟨α, v(x)⟩| ≤ |α|` and `μ` is finite on compact subsets of `U`, then `∫_A ⟨φ, v⟩ dμ ≤ M_W(S)` for every continuous compactly supported `k`-form `φ` with `spt φ ⊆ W ⊆ U`, `W` open, and `|φ| ≤ 1`. Take an open `V ⊇ spt φ` whose closure is a compact subset of `W`.  The smooth approximants `η_j ∈ 𝒟ᵏ(U)` of `smr_exists_testForm_uniform_approx` (`spt η_j ⊆ V`, `|φ - η_j| ≤ δ_j → 0`), rescaled to `ζ_j = (1 + δ_j)⁻¹ η_j`, are admissible for `M_W(S)` and satisfy `|ζ_j - φ| ≤ 2 δ_j`; the triangle inequality and homogeneity of `|·|` come from `smr_covector_coord_isometry`.  Dominated convergence on `μ ⌞ A` with the bound `1_{closure V}` gives `S(ζ_j) → ∫_A ⟨φ, v⟩ dμ`, and `ofReal (S(ζ_j)) ≤ M_W(S)` passes to the limit.
- **Calls**: `smr_covector_coord_isometry`, `smr_exists_testForm_uniform_approx`
- **Called by**: `smr_restriction_massOn_eq`

#### `slicing_support_subset` (L22986)

- `root.slicing-a1.slice_support-a1` · issue #672 · PR #2163 · candidate `13f3f1e557e5`
- **Statement and proof**: **Simon Ch. 6, 4.8 (p. 157).**  Every slice `S = ⟨T, f, t₋⟩` of (4.6) satisfies `spt S ⊆ spt T ∩ {f = t}`.  With `A_t = {x ∈ U | f x < t}` and representations `(μ, v)` of `T` and `(μ', v')` of `∂T`, `S(ω) = ∫_{A_t} ⟨dω, v⟩ dμ − ∫_{A_t} ⟨ω, v'⟩ dμ'`.  Both integrals vanish for `ω` supported where `T = 0` (`slicing_representation_unique` against the zero representation) or where `f > t`, and both equal `T(dω)` for `ω` supported where `f < t`.
- **Calls**: `slicing_representation_unique`
- **Called by**: `slicing_theorem`

#### `slicing_representation_unique` (L17445)

- `root.slicing-a1.representation_unique-a1` · issue #666 · PR #2077 · candidate `48beb763c9e5`
- **Statement and proof**: Simon Ch. 6, 2.7–2.9 (uniqueness of the vector measure `v μ` of a representation (2.7)), localized to an open `W`: if two representations agree on the test forms supported in `W`, their restrictions to every Borel set `A` agree on those forms.
- **Calls**: `slicing_ru_integrableOn_apply`, `slicing_ru_continuous_to_bounded`, `slicing_ru_smooth_to_continuous`, `slicing_ru_covector_expansion`
- **Called by**: `slicing_support_subset`, `slicing_mass_bound`, `dmr_measureRepresentation_unique`, `iwl_imc_restriction_im` (A.13, unused), `iwl_im_closure`

#### `slicing_ru_integrableOn_apply` (L10757)

- `root.slicing-a1.representation_unique-a1.local_integrability-a1` · issue #945 · PR #1621 · candidate `0b6482f55907`
- **Statement and proof**: **Local integrability from test forms (Simon Ch. 6, (2.7), p. 136).**  If `⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ᵏ(U)`, then `⟨c, v⟩` is `μ`-integrable on every compact `L ⊆ U`, for every constant `k`-covector `c`.  Some closed thickening `cthickening δ L` lies in `U`; the smooth Urysohn lemma gives a smooth `χ` with values in `[0, 1]`, `support χ = thickening δ L` and `χ = 1` exactly on `L`.  Then `ω = χ c` is a test form on `U`, so `χ ⟨c, v⟩ = ⟨ω, v⟩` is `μ`-integrable, and it agrees with `⟨c, v⟩` on the closed set `L`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_representation_unique`

#### `slicing_ru_continuous_to_bounded` (L10873)

- `root.slicing-a1.representation_unique-a1.continuous_to_bounded-a1` · issue #948 · PR #1457 · candidate `a49e975113ed`
- **Statement and proof**: Simon Ch. 6, (2.7)–(2.9): uniqueness step for representations of currents.  If `g₁ μ₁` and `g₂ μ₂` agree on continuous compactly supported functions with support in the open set `O`, then they agree on bounded Borel functions vanishing off `O`.  With `g⁺ = max g 0`, `g⁻ = max (-g) 0`, the finite measures `m₁ = g₁⁺ μ₁ + g₂⁻ μ₂`, `m₂ = g₁⁻ μ₁ + g₂⁺ μ₂` satisfy `∫ f dm₁ - ∫ f dm₂ = ∫ f g₁ dμ₁ - ∫ f g₂ dμ₂` for bounded measurable `f`, so they agree on `C_c(O)`.  Urysohn functions and inner regularity give `m₁ V = m₂ V` for open `V ⊆ O`; by the π–λ theorem `m₁ ⌞ O = m₂ ⌞ O`, and the claim follows.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_representation_unique`, `iwl_restriction_theory`, `deformation_skeleton_polyhedral`, `iwl_positive_density`

#### `slicing_ru_smooth_to_continuous` (L10787)

- `root.slicing-a1.representation_unique-a1.smooth_to_continuous-a1` · issue #946 · PR #1592 · candidate `e038063b301d`
- **Statement and proof**: **Step 4 of the uniqueness of the representation (2.7), Simon Ch. 6 (p. 136).**  If `g₁ μ₁` and `g₂ μ₂` (`gᵢ` `μᵢ`-integrable) agree on smooth compactly supported functions `φ` with `tsupport φ ⊆ O`, `O` open, they agree on continuous compactly supported functions `φ` with `tsupport φ ⊆ O`.  The approximants are `χ (ψ ⋆ φ)`: `ψ ⋆ φ` is the convolution of `φ` with a normalized smooth bump `ψ` supported in a ball whose radius is a uniform-continuity modulus of `φ`, and `χ` is a smooth cutoff with values in `[0, 1]`, equal to `1` exactly on `tsupport φ`, whose support `V` has compact closure in `O`.  Dominated convergence passes to the limit.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_representation_unique`, `iwl_restriction_theory`, `deformation_skeleton_polyhedral`, `iwl_positive_density`

#### `slicing_ru_covector_expansion` (L11215)

- `root.slicing-a1.representation_unique-a1.covector_expansion-a1` · issue #949 · PR #1441 · candidate `182a24a66909`
- **Statement and proof**: **Coordinate expansion of covectors, Simon Ch. 6, (1.1)–(1.2) (pp. 131–132).**  Every `k`-covector `α` on `ℝ^P` is `∑_{β ∈ I(k,P)} α(e_{β(0)}, …, e_{β(k-1)}) dx^β`.  By (1.1), `dx^β(e_γ) = δ_{βγ}` for increasing `β, γ` (the determinant of the identity matrix if `β = γ`, of a matrix with a zero column otherwise), so both sides agree on increasing basis tuples; sorting and the sign rule for alternating maps extend this to all injective basis tuples, and an alternating map is determined by its values on those.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_representation_unique`, `iwl_im_patching`

#### `slicing_mass_bound` (L23080)

- `root.slicing-a1.slice_mass_bound-a1` · issue #676 · PR #4967 · candidate `47b64c8c933b`
- **Statement and proof**: **Mass bound for slices (Simon Ch. 6, 4.9–4.10, pp. 157–158).**  For `W ⊆ U` open, `‖Df‖ ≤ L_W` a.e. on `W` and `a < b`, `t ↦ M_W(⟨T, f, t⟩)` has a measurable majorant `g` on `(a, b)` with `∫⁻_{(a,b)} g ≤ L_W M_W(T ⌞ {a < f < b})`.  In the normalized representation `(μ, v)` of `T`, `M_W(T ⌞ {a < f < b}) = μ(W ∩ {a < f < b})`, and (4.9) bounds `M_W(⟨T, f, t⟩)` by `L_W liminf_{h ↓ 0} h⁻¹ μ(W ∩ f⁻¹[t - h, t])`.  This is `L_W` times the lower left density at `t` of `ν = f_#(μ ⌞ W)`, which has a measurable majorant with integral `≤ ν(a, b)` (4.10).
- **Calls**: `slicing_mass_representation`, `slicing_representation_unique`, `slicing_mb_density_majorant`, `slicing_mb_pointwise`
- **Called by**: `slicing_theorem`

#### `slicing_mb_density_majorant` (L16952)

- `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1` · issue #1894 · PR #3401 · candidate `5ea978433c6f`
- **Statement and proof**: The measurable majorant in Simon Ch. 6, 4.10 (`M_W(T ⌞ {f < t})` is increasing in `t`, so it is differentiable a.e. and its derivative integrates to at most `M_W(T ⌞ {a < f < b})`), for a Borel measure `ν` on `ℝ`: the lower left density `liminf_{h → 0+} ν([t - h, t]) / h` has a Borel majorant on `(a, b)` whose integral over `(a, b)` is at most `ν((a, b))`. If `ν((a, b)) = ∞` the constant `∞` works.  Otherwise the distribution function `G(r) = ν((a, b) ∩ (-∞, r])` is nondecreasing and right-continuous, and the majorant is `D` on `(a, b)` and `0` elsewhere, where `D(t) = liminf_{k → 0+} (G(t) - G(t - k)) / k` is the lower left Dini derivative of `G`: `D` is Borel, it dominates the closed-band density, and by Lebesgue's theorem for monotone functions `∫_{(a,b)} D ≤ G(b) - G(a) = ν((a, b))`.
- **Calls**: `slicing_mb_dm_distribution_mono_rightcont`, `slicing_mb_dm_lowerLeftDini_measurable`, `slicing_mb_dm_density_le_lowerLeftDini`, `slicing_mb_dm_lintegral_lowerLeftDini_le`
- **Called by**: `slicing_mass_bound`

#### `slicing_mb_dm_distribution_mono_rightcont` (L16670)

- `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.distribution_regularity-a1` · issue #2189 · PR #3069 · candidate `31f0d299e59a`
- **Statement and proof**: The distribution function `G(r) = ν((a,b) ∩ (-∞, r])` of a measure `ν` on `ℝ` with `ν((a,b)) < ∞` is nondecreasing and right-continuous.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_density_majorant`

#### `slicing_mb_dm_lowerLeftDini_measurable` (L16703)

- `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_measurable-a1` · issue #2204 · PR #2894 · candidate `630c339ebee4`
- **Statement and proof**: The lower left Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` of a nondecreasing right-continuous `G : ℝ → ℝ` is Borel measurable.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_density_majorant`

#### `slicing_mb_dm_density_le_lowerLeftDini` (L16848)

- `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.density_le_dini-a1` · issue #2231 · PR #2924 · candidate `79fa90c23a79`
- **Statement and proof**: **Lower left density versus the lower left Dini derivative** (Simon Ch. 6, p. 158, the step "4.9 gives 4.10").  Let `ν((a, b)) < ∞`, `G r = ν((a, b) ∩ (-∞, r])` (as a real number) and `t ∈ (a, b)`.  Then `liminf_{h → 0+} ν([t - h, t]) / h ≤ liminf_{k → 0+} (G t - G (t - k)) / k`. For `c > 1` and `0 < k < t - a`, `[t - k / c, t] ⊆ (a, b) ∩ (t - k, t]`, a band of mass `G t - G (t - k)`, so the density at `h = k / c` is at most `c · (G t - G (t - k)) / k`. Reparametrizing `h = k / c` gives `liminf ≤ c · liminf`, and `c ↓ 1` finishes.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_density_majorant`

#### `slicing_mb_dm_lintegral_lowerLeftDini_le` (L16763)

- `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_lintegral_le-a1` · issue #2217 · PR #2958 · candidate `f077c7d5152d`
- **Statement and proof**: For nondecreasing `G : ℝ → ℝ` and `a ≤ b`, the lower integral over `(a, b)` of the lower left Dini derivative `D(t) = liminf_{k → 0+} ofReal ((G t - G (t - k)) / k)` is at most `G b - G a`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_density_majorant`

#### `slicing_mb_pointwise` (L16605)

- `root.slicing-a1.slice_mass_bound-a1.pointwise-a1` · issue #1888 · PR #3886 · candidate `fdaebfd29faa`
- **Statement and proof**: Simon Ch. 6, 4.9 (p. 158) for the slice `S = ⟨T, f, t₋⟩` of 4.6, `f` Lipschitz on `U`, and `T` represented by `(μ, v)` with `μ` finite on compact subsets of `U` and `|⟨α, v(x)⟩| ≤ |α|` for all `x` and `α` **[corrected]**: for open `W ⊆ U` with `|Df| ≤ L_W` a.e. on `W`, `M_W(S) ≤ L_W · liminf_{h ↓ 0} μ(W ∩ {t - h ≤ f ≤ t}) / h`.  For admissible `ω` and the cut-offs `χ_h` of `slicing_mb_cutoff` (slope at most `(1 + ε)/h`), the defect `X(h) = ∫ χ_h(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ_h(f) ⟨dω, v₁⟩ dμ₁` of 4.11 tends to `B(ω) - ∂A(ω) = -S(ω)` as `h ↓ 0` and satisfies `|X(h)| ≤ (1 + ε)/h · L_W · μ(W ∩ {t - h ≤ f ≤ t})`; let `h ↓ 0`, then `ε ↓ 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits three hypotheses of the Lean statement (lines 16608–16610). The normalization `|⟨α, v(x)⟩| ≤ |α|` is necessary, because a representation in the sense of `IsMeasureRepresentation`, the contract's reading of (2.7), need not be normalized: for `P = 1`, `U = W = ℝ`, `T = [[(0, 1)]]`, `f(x) = x` and `t = 1/2`, the slice is `δ_{1/2}` with `M_W(S) = 1`, while `μ = ½ L¹⌞(0, 1)` and `v = 2e₁` represent `T` and give `liminf_{h ↓ 0} μ([1/2 − h, 1/2])/h = 1/2`.
- **Calls**: `slicing_mb_pointwise_liminf_bound`, `slicing_mb_cutoff`, `slicing_mb_pointwise_cutoff_tendsto`, `slicing_mb_cutoff_defect_bound`
- **Called by**: `slicing_mass_bound`

#### `slicing_mb_pointwise_liminf_bound` (L4317)

- `root.slicing-a1.slice_mass_bound-a1.pointwise-a1.liminf_bound-a1` · issue #2254 · PR #2919 · candidate `7b74e18da55e`
- **Statement and proof**: Passing `ofReal |X_ε(h)| ≤ ofReal ((1 + ε) / h) · LW · a(h)` to the `liminf` as `h → 0+` and then letting `ε ↓ 0`, in `[0, ∞]`: if for every `ε > 0` some `X_ε(h) → r` as `h → 0+` satisfies this bound for all `h > 0`, then `ofReal |r| ≤ LW · liminf_{h → 0+} a(h) / ofReal h`. For fixed `ε`, `ofReal |r|` is the `liminf` of `ofReal |X_ε(h)|`, and `ofReal ((1 + ε) / h) · LW · a(h) = (ofReal (1 + ε) · LW) · (a(h) / ofReal h)` for `h > 0`; the finite constant `ofReal (1 + ε) · LW` commutes with the `liminf`, and `ofReal (1 + ε) → 1` as `ε → 0+`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_pointwise`

#### `slicing_mb_cutoff` (L4369)

- `root.slicing-a1.slice_mass_bound-a1.cutoff-a1` · issue #1869 · PR #2205 · candidate `b8b3c6bde72a`
- **Statement and proof**: Sharp smooth cut-off below the level `t` (the cut-off of the proof of Simon Ch. 6, 4.11, p. 158, with slope bound `(1 + ε)/h`): for `h, ε > 0` there is a `C^∞` function `χ : ℝ → ℝ` with `0 ≤ χ ≤ 1`, `χ = 1` on `(-∞, t - h]`, `χ = 0` on `[t, ∞)`, `|χ'| ≤ (1 + ε)/h`, and `χ' = 0` off `(t - h, t)`.  Take `χ = ρ ⋆ λ`: `λ` is the clamped affine profile equal to `1` on `(-∞, t - h + κ]`, to `0` on `[t - κ, ∞)` and of slope `-(1 + ε)/h` in between (`κ = εh/(2(1 + ε))`), and `ρ` is a normalized smooth bump supported in `(-κ/2, κ/2)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_pointwise`

#### `slicing_mb_pointwise_cutoff_tendsto` (L4259)

- `root.slicing-a1.slice_mass_bound-a1.pointwise-a1.cutoff_tendsto-a1` · issue #2242 · PR #2976 · candidate `012eb78d57e0`
- **Statement and proof**: Level cut-offs converge to the indicator of `{x ∈ U : f x < t}` under the integral: for `f` Lipschitz on the open set `U`, `F` `ν`-integrable with `F = 0` off `U`, and measurable `χ_h` **[corrected]** with `χ_h = 1` on `(-∞, t - h]`, `χ_h = 0` on `[t, ∞)` and `|χ_h| ≤ 1`, `∫ χ_h(f) F dν → ∫_{x ∈ U, f x < t} F dν` as `h → 0+` (dominated convergence; Simon 4.11).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 4259). `F = 0` off `U` is necessary: the pointwise limit of `χ_h(f)` is `1_{f < t}` on all of `ℝ^P`; e.g. for `U = (0, 1)`, `f = id`, `ν = δ_{−1}`, `F ≡ 1` and `t = 1/2`, the left side is `1` for small `h` and the right side is `0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_pointwise`, `slicing_im_slice_identity`

#### `slicing_mb_cutoff_defect_bound` (L16513)

- `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1` · issue #1883 · PR #3684 · candidate `6070b3614438`
- **Statement and proof**: The cut-off defect bound in the proof of Simon Ch. 6, 4.9 for Lipschitz `f` (4.11 and the bound of its right side, p. 158, with `f^{(σ)}` in place of `f`, then `σ ↓ 0`).  Let `K = spt ω ⊆ W`, `|ω| ≤ 1`, `|v| ≤ 1` on covectors, `|Df| ≤ L_W` a.e. on the open `W ⊆ U`, and `|χ| ≤ 1`, `|χ'| ≤ c`, `χ' = 0` off `(t - h, t)`.  Then `|∫ χ(f) ⟨ω, v₂⟩ dμ₂ - ∫ χ(f) ⟨dω, v₁⟩ dμ₁| ≤ c L_W μ(K ∩ {t - h ≤ f ≤ t})`, i.e. `∂T(χ(f) ω) - T(χ(f) dω)` computed through the representations of `∂T` and `T`.  For smooth `g_j` with `|g_j - f| ≤ 1/(j+1)` and `|Dg_j| ≤ L_W` on `K`, 4.11 for `ψ_j = χ ∘ g_j` gives the bound with the band `K ∩ {t - h - 1/(j+1) < f < t + 1/(j+1)}`; let `j → ∞` by dominated convergence on the left and continuity from above on the right.
- **Calls**: `slicing_mb_smooth_approx`, `slicing_mb_leibniz_bound`, `slicing_mb_cdb_grad_lintegral_le`, `slicing_mb_cdb_multiplier_integral_tendsto`, `slicing_mb_cdb_band_measure_tendsto`
- **Called by**: `slicing_mb_pointwise`

#### `slicing_mb_smooth_approx` (L4746)

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1` · issue #1874 · PR #3315 · candidate `e27012d9d09a`
- **Statement and proof**: Simon Ch. 6, 4.11 ("use `f^{(σ)}` in place of `f`") on a compact `K ⊆ W`: if `f` is `L`-Lipschitz on the open set `W` and `‖Df‖ ≤ LW` a.e. on `W`, then some `C^∞` function `g` is `δ`-close to `f` on `K` with `‖Dg‖ ≤ LW` on `K`.  Here `g = ρ ⋆ F` mollifies a McShane extension `F` of `f|W` with a kernel supported in a ball small enough that `x - y ∈ W` whenever `x ∈ K` and `ρ(y) ≠ 0`.
- **Calls**: `slicing_mb_sa_mollifier_exists`, `slicing_mb_sa_mollify_lipschitz_close`, `slicing_mb_sa_mollify_lipschitz_hasFDerivAt`
- **Called by**: `slicing_mb_cutoff_defect_bound`

#### `slicing_mb_sa_mollifier_exists` (L4724)

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollifier-a1` · issue #2168 · PR #2965 · candidate `9735e2124d87`
- **Statement and proof**: The mollifier behind Simon's `f^{(σ)}` (Ch. 6, §4, p. 158; parent Step 4): a smooth, nonnegative, compactly supported `ρ` vanishing off `B(0, σ)` with `∫ ρ = 1`.  Take the bump `φ` centred at `0` with radii `σ/2 < σ`; then `support φ = B(0, σ)`, so `c = ∫ φ > 0` and `ρ = c⁻¹ φ` works.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_smooth_approx`, `dph_sa_mollify_lipschitz`

#### `slicing_mb_sa_mollify_lipschitz_close` (L4647)

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_close-a1` · issue #2185 · PR #2833 · candidate `0db2d9bb718d`
- **Statement and proof**: **Uniform error of a mollified Lipschitz function** (Simon Ch. 6, 4.11, p. 158: "use `f^{(σ)}` in place of `f`").  If `F` is `L`-Lipschitz and `ρ ≥ 0` is continuous with compact support, `ρ(y) = 0` for `|y| ≥ σ` and `∫ ρ = 1`, then `|∫ ρ(y) F(x − y) dy − F(x)| ≤ L σ`. As `∫ ρ = 1`, the error is `∫ ρ(y) (F(x − y) − F(x)) dy`, and pointwise `|ρ(y) (F(x − y) − F(x))| ≤ ρ(y) L |y| ≤ ρ(y) L σ`, since `ρ(y) ≠ 0` forces `|y| < σ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_smooth_approx`, `deformation_ipl_mwc_lipschitz_smooth_approx`

#### `slicing_mb_sa_mollify_lipschitz_hasFDerivAt` (L4683)

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_fderiv-a1` · issue #2202 · PR #2944 · candidate `fd43c997849f`
- **Statement and proof**: Differentiation under the integral sign for the mollification of a globally Lipschitz `F` by a continuous compactly supported `ρ`: `D(∫ ρ(y) F(· - y) dy)(x) = ∫ ρ(y) DF(x - y) dy`. By Rademacher's theorem and the invariance of Lebesgue measure under `y ↦ x - y`, `F` is differentiable at `x - y` for a.e. `y`; `x' ↦ ρ(y) F(x' - y)` is `L |ρ(y)|`-Lipschitz on `ℝ^P` with integrable majorant `L |ρ|`, so `hasFDerivAt_integral_of_dominated_loc_of_lip` applies with `s = ℝ^P`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_smooth_approx`, `deformation_ipl_mwc_lipschitz_smooth_approx`

#### `slicing_mb_leibniz_bound` (L15916)

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1` · issue #1881 · PR #3561 · candidate `fdd90dcb0712`
- **Statement and proof**: **Boundary defect of a smooth multiplier** (Simon Ch. 6, 4.11, with the representation estimate (2.7) and the wedge bound): if `(μ, v)` represents `T ∈ 𝒟ₘ₊₁(U)` with `|⟨α, v⟩| ≤ |α|`, `ω ∈ 𝒟ᵐ(U)` and `ψ` is `C^∞`, then `η₁ = ψω` and `η₂ = ψ dω` are test forms with `|∂T(η₁) − T(η₂)| ≤ ∫ |Dψ| |ω| dμ`.  The Leibniz rule `d(ψω) = ψ dω + Dψ ∧ ω` gives `∂T(η₁) − T(η₂) = T(Dψ ∧ ω)`, bounded by the representation and `|Dψ ∧ ω| ≤ ‖Dψ‖ |ω|`.
- **Calls**: `slicing_mb_lb_smul_testForm`, `slicing_mb_lb_wedge_testForm`, `slicing_mb_lb_extDeriv_smul`, `slicing_mb_lb_repr_bound`, `slicing_mb_wedge_norm_le`
- **Called by**: `slicing_mb_cutoff_defect_bound`

#### `slicing_mb_lb_smul_testForm` (L15612)

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.smul_test_form-a1` · issue #2193 · PR #2864 · candidate `1faaa7c7259b`
- **Statement and proof**: Multiplication by a smooth function `ψ` maps `𝒟ᵏ(U)` into itself: `ψ φ` is smooth, and `spt (ψ φ) ⊆ spt φ`, which is compact and contained in `U`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`

#### `slicing_mb_lb_wedge_testForm` (L15623)

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.wedge_test_form-a1` · issue #2211 · PR #2883 · candidate `1c55ec485bf9`
- **Statement and proof**: The wedge `α ∧ ω` of a `C^∞` field `α` of covectors with a test form `ω ∈ 𝒟ᵐ(U)` is a test form in `𝒟ᵐ⁺¹(U)`, given pointwise by `alternatizeUncurryFin ((α x).smulRight (ω x))`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`

#### `slicing_mb_lb_extDeriv_smul` (L15604)

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.extderiv_leibniz-a1` · issue #2177 · PR #3036 · candidate `d90a235b0e2f`
- **Statement and proof**: Simon Ch. 6, 4.11 (Leibniz rule, pointwise): `d(ψω)(x) = ψ(x) dω(x) + Dψ(x) ∧ ω(x)`, the wedge `Dψ(x) ∧ ω(x)` being the alternatization of `h ↦ Dψ(x)(h) ω(x)`.  As `d = Alt ∘ D` (Mathlib's `extDeriv`), this is the product rule `D(ψω)(x) = ψ(x) Dω(x) + Dψ(x) ⊗ ω(x)` followed by linearity of `alternatizeUncurryFin`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_leibniz_bound`, `slicing_im_ll_smooth_leibniz`

#### `slicing_mb_lb_repr_bound` (L15650)

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.repr_bound-a1` · issue #2222 · PR #2987 · candidate `9bc99e092729`
- **Statement and proof**: **Mass estimate from a normalized measure representation** (Simon Ch. 6, (2.7)).  If `T(η) = ∫ ⟨η, v⟩ dμ` for every test form `η` and `|⟨α, v(x)⟩| ≤ |α|` for every `x` and every `n`-covector `α` (Euclidean coefficient norm), then `|T(η)| ≤ ∫ |η| dμ` in `[0, ∞]`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_leibniz_bound`

#### `slicing_mb_wedge_norm_le` (L15897)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1` · issue #1871 · PR #3429 · candidate `34503163c994`
- **Statement and proof**: The wedge estimate behind the bound on the right side of Simon Ch. 6, 4.11 (proof of 4.8–4.9): for a covector `α` and an `m`-covector `γ` on `ℝ^P`, the Euclidean coefficient norm of `α ∧ γ = alternatizeUncurryFin (α.smulRight γ)` is at most `‖α‖ |γ|`.  The coefficient norm can be computed in any orthonormal basis.  In a basis `u` with `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`, the coefficients of `α ∧ γ` are `‖α‖` times coefficients of `γ` on pairwise distinct multi-indices, so `|α ∧ γ|² ≤ ‖α‖² |γ|²`.
- **Calls**: `slicing_mb_wn_adapted_onb`, `slicing_mb_wn_norm_sq_eq_onb_sum`, `slicing_mb_wn_adapted_sum_le`
- **Called by**: `slicing_mb_leibniz_bound`

#### `slicing_mb_wn_adapted_onb` (L15802)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_onb-a1` · issue #2405 · PR #2979 · candidate `40b4cdead896`
- **Statement and proof**: Every continuous linear functional `α` on `ℝ^P` has an adapted orthonormal basis `u`: `α(u₀) = ‖α‖` and `α(uⱼ) = 0` for `j ≠ 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_wedge_norm_le`

#### `slicing_mb_wn_norm_sq_eq_onb_sum` (L15785)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.onb_norm_sq-a1` · issue #2399 · PR #3271 · candidate `66289299bcea`
- **Statement and proof**: The Euclidean coefficient norm of a `k`-covector can be computed in any orthonormal basis `u` of `ℝ^P` (Simon Ch. 6, 1.5–1.6 and Remark 2.6): `|φ|² = ∑_{I increasing} φ(u_I)²`. With `e` the standard basis used by `covectorEuclideanNorm` and `N_w(φ) = ∑_{all I} φ(w_I)²`, `k! |φ|² = N_e(φ) = N_u(φ) = k! ∑_{I increasing} φ(u_I)²`, and `k! ≠ 0`.
- **Calls**: `slicing_mb_wn_sq_sum_eq_factorial_mul`, `slicing_mb_wn_sq_sum_onb_invariant`
- **Called by**: `slicing_mb_wedge_norm_le`, `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`

#### `slicing_mb_wn_sq_sum_eq_factorial_mul` (L15662)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.count_sq_sum-a1` · issue #2379 · PR #2926 · candidate `6c884a2c7528`
- **Statement and proof**: Counting identity: for any family `u` of vectors of `ℝ^P` and any `k`-covector `φ`, `∑_I φ(u_{I 0}, …, u_{I (k-1)})² = k! ∑_{I strictly increasing} φ(u_{I 0}, …, u_{I (k-1)})²`, where `I` ranges over all maps `Fin k → Fin P`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_wn_norm_sq_eq_onb_sum`, `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`

#### `slicing_mb_wn_sq_sum_onb_invariant` (L15741)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.parseval_sq_sum-a1` · issue #2390 · PR #2966 · candidate `f12646af114b`
- **Statement and proof**: Basis independence of the full coefficient sum (Parseval's identity, one slot at a time): for orthonormal bases `u`, `v` of `ℝ^P` and a `k`-covector `φ`, `∑_I φ(u_{I 0}, …, u_{I (k-1)})² = ∑_I φ(v_{I 0}, …, v_{I (k-1)})²`, both sums over all index maps `I : Fin k → Fin P`.  Induction on `k`: write `I = (i, J)` and `φ(w_I) = (φ.curryLeft w_i)(w_J)`, replace `u` by `v` in the last `k` slots by the induction hypothesis for `φ.curryLeft (u i)`, then in slot `0` by `OrthonormalBasis.norm_dual` for the functional `z ↦ (φ.curryLeft z)(v_J)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_wn_norm_sq_eq_onb_sum`

#### `slicing_mb_wn_adapted_sum_le` (L15841)

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_sum_le-a1` · issue #2419 · PR #3027 · candidate `1f87f778d505`
- **Statement and proof**: Coefficient sum of `α ∧ γ` on a family adapted to `α`: if `α (u j)` is `c` for `j = 0` and `0` otherwise, then `∑_{I increasing} ((α ∧ γ)(u_I))² ≤ c² ∑_{J increasing} γ(u_J)²`, where `α ∧ γ = alternatizeUncurryFin (α.smulRight γ)`.  The family `u` need not be orthonormal.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_wedge_norm_le`

#### `slicing_mb_cdb_grad_lintegral_le` (L4505)

- `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.grad_lintegral-a1` · issue #2219 · PR #2963 · candidate `4b14fb2e31e2`
- **Statement and proof**: Simon Ch. 6, proof of 4.8–4.9 (p. 158): the integral bounding the right side of 4.11, for a differentiable approximation `g` of `f` (Simon's `f^{(σ)}`): `∫ |D(χ ∘ g)| |ω| dμ ≤ c L_W μ(spt ω ∩ {t − h − δ < f < t + δ})` when `|ω| ≤ 1`, `|g − f| ≤ δ` and `‖Dg‖ ≤ L_W` on `spt ω`, `|χ'| ≤ c` and `χ' = 0` off `(t − h, t)`. Off `spt ω` the integrand vanishes.  On `spt ω` the chain rule gives `‖D(χ ∘ g)(x)‖ ≤ |χ'(g x)| ‖Dg(x)‖`; this is `0` unless `t − h < g x < t`, and then `t − h − δ < f x < t + δ` and the bound is `c L_W`.  Integrate the indicator bound.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_cutoff_defect_bound`

#### `slicing_mb_cdb_multiplier_integral_tendsto` (L4623)

- `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.multiplier_limit-a1` · issue #2243 · PR #2985 · candidate `73831a4dd0cc`
- **Statement and proof**: Dominated convergence for the bounded continuous multipliers `χ(g_j)` against an integrable density `F` (the limit `σ ↓ 0` in the cutoff defect bound of the slice mass estimate, Simon Ch. 6, 4.9–4.10): if `F` vanishes off `K` and `g_j → f` on `K`, then `∫ χ(g_j) F dν → ∫ χ(f) F dν`. The integrands are dominated by `|F|` since `|χ| ≤ 1`, and converge everywhere: on `K` by continuity of `χ`, off `K` because `F = 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_cutoff_defect_bound`

#### `slicing_mb_cdb_band_measure_tendsto` (L4565)

- `root.slicing-a1.slice_mass_bound-a1.cutoff_defect_bound-a1.band_limit-a1` · issue #2233 · PR #2981 · candidate `9ff4cacca1b5`
- **Statement and proof**: Continuity from above for the shrinking level bands (parent proof, Step 6).  With `δ_j = 1/(j+1)`, the sets `E_j = K ∩ f⁻¹((a − δ_j, b + δ_j))` are Borel (`K` is closed and `f` is continuous on `K`), decrease in `j`, have intersection `K ∩ f⁻¹([a, b])`, and `μ(E_0) ≤ μ(K) < ∞`; so `μ(E_j) → μ(K ∩ f⁻¹([a, b]))`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_mb_cutoff_defect_bound`

#### `slicing_integer_multiplicity_ae` (L66941)

- `root.slicing-a1.slice_integer_multiplicity-a1` · issue #678 · PR #5560 · candidate `8f220efff156`
- **Statement and proof**: Simon Ch. 6, 4.4–4.5(2) (pp. 155–157): if `T` is integer multiplicity, with `M_W(T)` and `M_W(∂T)` finite for every `W ⊂⊂ U`, and `f` is `L`-Lipschitz on `U`, then for `L¹`-a.e. `t` every slice `S` with `IsSlice T f t S` is integer multiplicity.  Write `T = τ(M, θ, ξ)` and let `g` be a McShane extension of `f`.  `IsSlice` only sees `f` on `U`, so slices of `T` by `f` and by `g` coincide.  Let `G` be a tangential gradient of `g` on `M` and `E` a countable family of test forms determining currents.  For a.e. `t`, the triple `(M_t, θ, ξ⌞(G/|G|))` with `M_t = {x ∈ M : g(x) = t, G(x) ≠ 0}` is rectifiable, and every slice agrees on each `e ∈ E` with the current `τ(M_t, θ, ξ⌞(G/|G|))`, hence equals it; `θ` is integer-valued on `M_t ⊆ M`.
- **Calls**: `slicing_im_tangential_gradient`, `slicing_im_testform_determining`, `slicing_im_slice_triple`, `slicing_im_slice_identity`, `slicing_im_tau_current`
- **Called by**: `slicing_theorem`

#### `slicing_im_tangential_gradient` (L46411)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1` · issue #2474 · PR #4985 · candidate `dfb10e73f9e3`
- **Statement and proof**: Tangential gradient of a Lipschitz function on a rectifiable carrier (Simon Ch. 3, 2.1, for the weighted tangent planes of 1.7): for a rectifiable triple `(M, θ, ξ)` (Ch. 6, 3.1, with real `θ > 0`) **[corrected]** and `f` `L`-Lipschitz there is a Borel `G` with `‖G‖ ≤ L` everywhere such that for `Hⁿ`-a.e. `x ∈ M`, `G x` lies in every weighted approximate tangent plane `Q` of `(M, θ)` at `x` and `⟨G x, u⟩` is the derivative of `f` at `x` along every `u ∈ Q`.  Cover `M` up to an `Hⁿ`-null set by C¹ bi-Lipschitz charts `Φ_j : Ω_j → ℝ^P`, let `g_j` be the gradient of `f` along `range DΦ_j` on `Φ_j(Ω_j)`, and put `G = g_j` on `Φ_j(Ω_j)` for some `j` and `G = 0` off `⋃ j, Φ_j(Ω_j)`.  At `Hⁿ`-a.e. `x = Φ_j(w) ∈ M`, `range DΦ_j(w)` is a weighted approximate tangent plane, hence the only one as `θ x > 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "`(M, θ, ξ)` as in 3.1" right after a parenthetical citing Ch. 3, so that it reads as Ch. 3, 3.1, the definition of purely unrectifiable sets. The triple is that of Ch. 6, 3.1 (p. 146), and the Lean hypothesis `IsRectifiableTriple` allows real `θ > 0`.
- **Calls**: `slicing_im_tg_c1_chart_cover`, `slicing_im_tg_chart_gradient`, `slicing_im_tg_weighted_tangent_chart`
- **Called by**: `slicing_integer_multiplicity_ae`

#### `slicing_im_tg_c1_chart_cover` (L44449)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1` · issue #3324 · PR #4886 · candidate `7349133a5f3b`
- **Statement and proof**: Simon Ch. 3, Lemma 1.2 ("only if", pp. 69–70) with Remark 1.3 (p. 70), in chart form: a countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by images `Φ_j(Ω_j)` of open `Ω_j ⊆ ℝⁿ` under `C¹` maps `Φ_j : ℝⁿ → ℝ^P` that are Lipschitz and antilipschitz on `Ω_j`. Write `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` (1.1); each `F_j(ℝⁿ)` is covered up to an `Hⁿ`-null set by `C¹` images `G_{ji}(ℝⁿ)` (display (1)), and each `G_{ji}(ℝⁿ)` by images `G_{ji}(O_{jik})` of open sets on which `G_{ji}` is Lipschitz and antilipschitz (the area formula at critical points and the inverse function theorem at regular points); the triples `(j, i, k)` are enumerated by `ℕ`.
- **Calls**: `slicing_im_tg_cc_lipschitz_range_c1_cover`, `slicing_im_tg_cc_contDiff_range_chart_cover`
- **Called by**: `slicing_im_tangential_gradient`

#### `slicing_im_tg_cc_lipschitz_range_c1_cover` (L44178)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.lipschitz_range_cover-a1` · issue #4039 · PR #4669 · candidate `db66a30d9176`
- **Statement and proof**: Simon Ch. 3, proof of Lemma 1.2 (p. 70), displays (1)–(2): for a Lipschitz `F : ℝⁿ → ℝ^P` there are `C¹` maps `G_i : ℝⁿ → ℝ^P` with `F(ℝⁿ) ⊆ F(Z) ∪ ⋃_i G_i(ℝⁿ)` and `Hⁿ(F(Z)) = 0`, where `F = G_i` off a set of measure `< 1/i` (C¹ Approximation Theorem) and `Lⁿ(Z) = 0`.
- **Calls**: `lpf_c1_approximation_eucl` (A.4)
- **Called by**: `slicing_im_tg_c1_chart_cover`

#### `slicing_im_tg_cc_contDiff_range_chart_cover` (L44216)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_cover-a1.c1_range_chart_cover-a1` · issue #4049 · PR #4778 · candidate `118fa606212e`
- **Statement and proof**: Simon Ch. 3, proof of Lemma 1.2 (p. 70) and Remark 1.3, for one `C¹` map `G : ℝⁿ → ℝ^P`: countably many open sets `O k` on each of which `G` is Lipschitz and bi-Lipschitz onto its image cover `G(ℝⁿ)` up to an `Hⁿ`-null set.  Regular points (`DG(w)` injective) lie in some `O k`; the image of the critical set is `Hⁿ`-null: near a critical point, `G` composed with a linear map that shrinks the directions orthogonal to a kernel vector has a small Lipschitz constant.
- **Calls**: `lpf_c1_local_antilipschitz` (A.4)
- **Called by**: `slicing_im_tg_c1_chart_cover`

#### `slicing_im_tg_chart_gradient` (L46331)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1` · issue #3351 · PR #4835 · candidate `a51770cbdc26`
- **Statement and proof**: Tangential gradient of a Lipschitz function on a C¹ bi-Lipschitz chart (the gradient `∇ᴹf` of Simon Ch. 3, 2.1, via Ch. 2, 4.10; used for the slices of Ch. 6, §4): for `f` `L`-Lipschitz and `Φ` C¹, Lipschitz and antilipschitz on the open `Ω`, there is a Borel `g` with `‖g‖ ≤ L` such that for `Hⁿ`-a.e. `y = Φ(w) ∈ Φ(Ω)`, `g(y) ∈ DΦ(w)(ℝⁿ)` and `s ↦ f(y + s v)` has derivative `⟨g(y), v⟩` at `0` for every `v ∈ DΦ(w)(ℝⁿ)`.  Take `g := γ ∘ (Φ|_D)⁻¹` on `Φ(D)` and `0` elsewhere, where `D` is the Borel set of `w ∈ Ω` at which `f ∘ Φ` is differentiable and `γ(w) ∈ range DΦ(w)` is the Gram representative of `D(f ∘ Φ)(w)`; the failure set lies in the `Hⁿ`-null `Φ(Ω ∖ D)`.
- **Calls**: `lpf_wtc_cat_fderiv_lower_bound` (A.4), `slicing_im_tg_cg_gram_field`, `slicing_im_tg_cg_borel_transfer`, `slicing_im_tg_line_deriv_of_comp`, `lpf_tde_chart_nondiff_image_null` (A.4)
- **Called by**: `slicing_im_tangential_gradient`

#### `slicing_im_tg_cg_gram_field` (L45556)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.gram_field-a1` · issue #4059 · PR #4694 · candidate `659bd72cb30a`
- **Statement and proof**: Gram representative of a differential along a `C¹` chart (chart gradient for the tangential gradient in the slicing of Simon Ch. 6, §4): if `Φ : ℝⁿ → ℝ^P` is `C¹` and `A_w = DΦ(w)` is injective on an open `Ω`, then for any `h : ℝⁿ → ℝ` the field `γ(w) = A_w (A_w* A_w)⁻¹ a_w`, with `a_w` the Riesz vector of `Dh(w)`, extended by `0` off `Ω`, is Borel, lies in `range A_w` and satisfies `⟨γ(w), A_w u⟩ = Dh(w) u` on `Ω`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_tg_chart_gradient`

#### `slicing_im_tg_cg_borel_transfer` (L45631)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_gradient-a1.borel_transfer-a1` · issue #4066 · PR #4645 · candidate `908c000bd33e`
- **Statement and proof**: Borel transfer through a chart (Lusin–Souslin, Kechris, *Classical Descriptive Set Theory*, Thm. 15.1): if `D ⊆ ℝⁿ` is Borel and `Φ` is continuous and injective on `D`, then `Φ|_D` is a measurable embedding, so a Borel `γ` factors as `γ = g ∘ Φ` on `D` through the Borel map `g = extend (Φ|_D) (γ|_D) 0`, which vanishes off `Φ(D)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_tg_chart_gradient`

#### `slicing_im_tg_line_deriv_of_comp` (L45653)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.line_deriv-a1` · issue #3344 · PR #3929 · candidate `4d089a08226f`
- **Statement and proof**: Simon Ch. 2, 4.10 (cf. 4.7): if `f` is `L`-Lipschitz and both `Φ` and `f ∘ Φ` are differentiable at `w`, then `s ↦ f(Φ(w) + s DΦ(w)u)` has derivative `D(f∘Φ)(w)u` at `0`.  It differs from `s ↦ f(Φ(w + su))` by at most `L ‖Φ(w + su) - Φ(w) - s DΦ(w)u‖ = o(s)`, and the latter map has derivative `D(f∘Φ)(w)u` by the chain rule.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_tg_chart_gradient`

#### `slicing_im_tg_weighted_tangent_chart` (L45184)

- `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1` · issue #3334 · PR #4292 · candidate `a812942bc581`
- **Statement and proof**: Weighted approximate tangent plane along a `C¹` chart (Simon Ch. 3, proof of 1.6 "⇒", Remarks 1.5(2) and 1.8(1); used for the tangential gradient in Ch. 6, 4.1–4.5 **[corrected]**): let `V` be open, `M ⊆ V` `Hⁿ`-null-measurable and `θ > 0` on `M` with `θ` `Hⁿ`-integrable on `M ∩ K` for compact `K ⊆ V` **[corrected]**. If `Φ` is `C¹` and antilipschitz on the open set `Ω`, then for `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and `w ∈ Ω` with `Φ w = y`, `DΦ(w)(ℝⁿ)` is the approximate tangent space of `M` with respect to `θ` at `y`. Cover `M` up to an `Hⁿ`-null set by compact pieces `C k` on which `θ` is continuous; at `Hⁿ`-a.e. `y ∈ C k ∩ Φ(Ω)` the sets `C k ∖ Φ(Ω)`, `Φ(Ω) ∖ C k` and the weight `θ` on `M ∖ C k` have `n`-density `0`, so the tangent plane of `Φ(Ω)` passes to `C k` and then to `(M, θ)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "used for the tangential gradient in Ch. 6, 4.6–4.7". 4.6–4.7 (p. 157) define the slices of a general current and do not involve the tangential gradient; `∇^M f` is used in 4.1–4.5 (pp. 154–157). It also leaves the hypotheses on `(M, θ)` implicit; Simon's Ch. 3, 1.7 (p. 74) builds them into the definition of the approximate tangent space, SimonGMT's `HasWeightedApproximateTangentSpaceAt` does not, and the Lean statement (lines 45186–45189) assumes them.
- **Calls**: `lpf_wtc_chart_image_measurable_locally_finite` (A.4), `lpf_wtc_lusin_compact_pieces` (A.4), `lpf_wtc_ae_zero_density_off_set` (A.4), `lpf_wtc_tangent_transfer` (A.4), `lpf_wtc_chart_approx_tangent` (A.4), `lpf_wtc_weighted_tangent_transfer` (A.4)
- **Called by**: `slicing_im_tangential_gradient`

#### `slicing_im_testform_determining` (L66840)

- `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1` · issue #2532 · PR #4543 · candidate `8392d5e440a2`
- **Statement and proof**: A countable family of test forms determines currents (the "countable dense set of `ω ∈ 𝒟ⁿ(U)`" in the proof of Simon Ch. 6, 4.5(2)): for open `U ⊆ ℝ^P` there is a countable `E ⊆ 𝒟ᵏ(U)` such that two currents in `𝒟ₖ(U)` agreeing on `E` are equal.
- **Calls**: `cmb_exists_compactly_contained_exhaustion` (A.1), `slicing_im_td_countable_seq_dense`, `slicing_im_td_current_tendsto`
- **Called by**: `slicing_integer_multiplicity_ae`

#### `slicing_im_td_countable_seq_dense` (L66707)

- `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.seq_dense-a1` · issue #3591 · PR #4367 · candidate `53a4da30f2c2`
- **Statement and proof**: **Countable sequential density of test forms supported in a compact `K ⊆ U`** (the "countable dense set of `ω ∈ 𝒟ⁿ(U)`" of Simon Ch. 6, proof of 4.5, p. 157).  The value spaces `ℝ^P [×i]→L[ℝ] Λᵏ` of `D^i ω` are second countable (by currying).  For each order `m` and scale `1/(j+1)`, the forms whose jets `(D^i ω)_{i ≤ m}` oscillate on `K` by less than `1/(m+1)` at scale `1/(j+1)` are approximated within `3/(m+1)` on `K` through their jets on a finite `1/(j+1)`-net of `K`.  A choice over the orders `m` gives a sequence whose derivatives of every order converge uniformly on `K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_testform_determining`

#### `slicing_im_td_current_tendsto` (L66813)

- `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.current_tendsto-a1` · issue #3597 · PR #4315 · candidate `c633e337cd22`
- **Statement and proof**: Simon's currents are sequentially continuous at every test form: if `e l → ω` in `𝒟ᵏ(U)`, then `S (e l) → S ω`.  The differences `e l - ω` converge to `0` on the same compact set, so continuity of `S` at `0` (`GeometricCurrentOn.continuous'`) and linearity give the limit.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_testform_determining`

#### `slicing_im_slice_triple` (L62571)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1` · issue #2492 · PR #5202 · candidate `ec722690b696`
- **Statement and proof**: Slices of a rectifiable triple are rectifiable triples (Simon Ch. 6, 4.1–4.4).  Let `f` be `L`-Lipschitz on `ℝ^P` and `G` a Borel tangential gradient of `f` on `M` with `|G| ≤ L` (as given by `slicing_im_tangential_gradient`) **[corrected]**. For `L¹`-a.e. `t`, `M_t = {x ∈ M : f(x) = t, G(x) ≠ 0}` with multiplicity `θ` and orientation `ξ_t = ξ ⌞ ν`, `ν = |G|⁻¹ G` (`ξ_t(x)(α) = ξ(x)(ν(x)♭ ∧ α)`), is a rectifiable `m`-triple in `U`. The co-area formula `slicing_im_coarea` for `(M, f, G)` feeds `slicing_im_st_measure_fields` (null-measurability of `M_t`, local integrability of `θ` on `M_t`, measurability of `ξ_t`), `slicing_im_st_slice_geometry` (`M_t` is countably `m`-rectifiable with weighted approximate tangent plane `TₓM ∩ G(x)^⊥`, Simon 4.1(1)–(2) **[corrected]**) and the null transfer `slicing_im_st_ae_transfer`, which carries the orientation clause of `(M, θ, ξ)` and the tangential-gradient property to `Hᵐ`-a.e. point of `M_t`; `subset` and `pos` are inherited from `M_t ⊆ M`.  At such a point, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ₊₁` with `τ` an orthonormal basis of `TₓM ∋ G(x) ≠ 0`, so `slicing_im_st_interior_product` gives an orthonormal basis `τ'` of `TₓM ∩ G(x)^⊥` with `ξ_t(x) = ±τ'₁ ∧ ⋯ ∧ τ'ₘ` (Simon 4.3).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not state the hypotheses on `f` and `G` of the Lean statement (lines 62573–62578), and they are needed: for an arbitrary `G`, `ξ_t = ξ ⌞ ν` can vanish (e.g. `M = ℝ² × {0}` in `ℝ³`, `ξ = e₁ ∧ e₂`, `f = x₁`, `G ≡ e₃`). It also cites 4.1(2) for the countable rectifiability of `M_t`, which is 4.1(1); 4.1(2) gives the tangent planes.
- **Calls**: `slicing_im_coarea`, `slicing_im_st_measure_fields`, `slicing_im_st_slice_geometry`, `slicing_im_st_ae_transfer`, `slicing_im_st_interior_product`
- **Called by**: `slicing_integer_multiplicity_ae`

#### `slicing_im_coarea` (L47113)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1` · issue #2483 · PR #5158 · candidate `d33ec3b4a054`
- **Statement and proof**: Simon Ch. 3, (2.8)–(2.9) for a real-valued Lipschitz `f` on the carrier `M` of a rectifiable triple (`n = m + 1`): if `G` is a Borel tangential gradient of `f` on `M`, then for every Borel `g ≥ 0` the function `t ↦ ∫_{M ∩ f⁻¹{t}} g dH^m` is a.e.-measurable and `∫_ℝ ∫_{M ∩ f⁻¹{t}} g dH^m dt = ∫_M |G| g dHⁿ`. `M` is cut into disjoint Borel chart pieces `W i` (`slicing_im_coarea_pieces`) covering `M` up to an `Hⁿ`-null set `Z`. The co-area formula holds on the regular parts `W i ∩ {G ≠ 0}` (`slicing_im_coarea_chart_regular`). The slices of the critical parts `W i ∩ {G = 0}` (`slicing_im_coarea_chart_critical`) and of `Z` (`slicing_im_coarea_eilenberg`) are `H^m`-null for a.e. `t`, and `|G| g = 0` on the critical parts, so the regular parts glue to the statement on `M` (`slicing_im_coarea_glue`).
- **Calls**: `slicing_im_coarea_pieces`, `slicing_im_coarea_glue`, `slicing_im_coarea_eilenberg`, `slicing_im_coarea_chart_critical`, `slicing_im_coarea_chart_regular`
- **Called by**: `slicing_im_slice_triple`, `slicing_im_slice_identity`

#### `slicing_im_coarea_pieces` (L46517)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.pieces-a1` · issue #3440 · PR #4830 · candidate `e3cb17916c0d`
- **Statement and proof**: Pieces for the co-area formula (Steps 1–4 of `slicing_im_coarea`; Simon Ch. 2, 1.2 and 1.5, Ch. 3, 1.2–1.8).  Up to an `Hⁿ`-null set, `M` is the disjoint union of Borel pieces `W i ⊆ Φ i(Ω i)`, where the `Φ i` are `C¹` antilipschitz charts.  On `Φ i⁻¹(W i)`, `f ∘ Φ i` agrees with a `C¹` function `h i`, and `Dh i(w) u = ⟨G(Φ i w), DΦ i(w) u⟩`. The charts come from `slicing_im_coarea_chart_cover`.  The Lipschitz extension of `f ∘ Φ j|Ω j` is approximated by `slicing_im_coarea_c1_approx` off a set `ℝⁿ ∖ A' j k` of measure `< k⁻¹`. Off the null sets where `slicing_im_coarea_chart_tangent` or the tangential-gradient hypothesis fails, `range DΦ j(w)` is a tangent plane at `Φ j w`; `slicing_im_coarea_line_deriv` and uniqueness of derivatives then give `⟨G, DΦ j(w) u⟩ = Dh(w) u`.  The pieces disjointify `(B ∩ Φ j(Ω j ∩ A' j k)) ∖ (Z₁ j ∪ Z₂)`, with `B ⊆ M` a Borel kernel.
- **Calls**: `slicing_im_coarea_chart_cover`, `slicing_im_coarea_c1_approx`, `slicing_im_coarea_chart_tangent`, `slicing_im_coarea_line_deriv`
- **Called by**: `slicing_im_coarea`

#### `slicing_im_coarea_chart_cover` (L44011)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_cover-a1` · issue #3410 · PR #4662 · candidate `de9ec3b03cc1`
- **Statement and proof**: Simon Ch. 3, Lemma 1.2 ("only if" part, p. 70), with each chart restricted, as in the printed proof, to a small neighbourhood of a point where its differential is injective, so that it is both Lipschitz and antilipschitz: a countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by countably many images `Φ_i(Ω_i)` of open sets `Ω_i ⊆ ℝⁿ` under `C¹` maps `Φ_i` with `c_i |w − w'| ≤ |Φ_i(w) − Φ_i(w')| ≤ K_i |w − w'|` on `Ω_i`.  The `C¹` Approximation Theorem (Ch. 2, 1.5) gives `C¹` maps `G_{j,k}` that agree to first order with the Lipschitz parametrizations `F_j` off sets of measure `< 1/(k+1)`; the area formula makes the image of the critical set of `F_j` null; near points where `DG_{j,k}` is injective, `G_{j,k}` is a chart on a small basic open set.
- **Calls**: `lpf_c1_approximation_eucl` (A.4), `lpf_c1_local_antilipschitz` (A.4)
- **Called by**: `slicing_im_coarea_pieces`

#### `slicing_im_coarea_c1_approx` (L43963)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.c1_approx-a1` · issue #3405 · PR #4363 · candidate `c7050c55826e`
- **Statement and proof**: Simon Ch. 2, Theorem 1.5 (`C¹` Approximation Theorem), in the form established by its printed proof (p. 44): a Lipschitz `g : ℝⁿ → ℝ` agrees, together with its derivative, with a `C¹` function `h` on a closed set `A` with `Lⁿ(ℝⁿ ∖ A) < ε`, and `g` is differentiable on `A`. Rademacher, then Lusin (`lpf_c1r_lusin_closed`), the uniform remainder estimate (`lpf_c1r_uniform_remainder`) and Whitney's extension theorem (`lpf_c1r_whitney_extension`).
- **Calls**: `lpf_c1r_lusin_closed` (A.4), `lpf_c1r_uniform_remainder` (A.4), `lpf_c1r_whitney_extension` (A.4)
- **Called by**: `slicing_im_coarea_pieces`

#### `slicing_im_coarea_chart_tangent` (L46072)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_tangent-a1` · issue #3422 · PR #4371 · candidate `7ecb6efce6fd`
- **Statement and proof**: Weighted approximate tangent planes along a `C¹` chart (Simon Ch. 3, proof of Theorem 1.6 "⇒" and Remark 1.8(1), for one chart): let `V` be open, `M ⊆ V` `Hⁿ`-null-measurable and `θ > 0` on `M` with `θ` `Hⁿ`-integrable on `M ∩ K` for compact `K ⊆ V` **[corrected]**. If `Φ : ℝⁿ → ℝ^Q` is `C¹` and antilipschitz on the open set `Ω`, then at `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)`, with `y = Φ(w)`, `DΦ(w)(ℝⁿ)` is the approximate tangent space of `M` with respect to `θ`.  Cover `M` up to a null set by compact pieces `C` with `θ|C` continuous (`lpf_wtc_lusin_compact_pieces`).  At a.e. `y ∈ C ∩ Φ(Ω)`, the sets `C ∖ Φ(Ω)`, `Φ(Ω) ∖ C` and the measure `θ Hⁿ ⌞ (M ∖ C)` have zero `n`-density (`lpf_wtc_ae_zero_density_off_set`); there the tangent plane of `Φ(Ω)` (`lpf_wtc_chart_approx_tangent`) passes to `C` (`lpf_wtc_tangent_transfer`) and then to the weighted set `(M, θ)` (`lpf_wtc_weighted_tangent_transfer`).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves the hypotheses on `(M, θ)` implicit. Simon's Ch. 3, 1.7 (p. 74) builds them into the definition of the approximate tangent space (for compact `K` in the whole space), but SimonGMT's `HasWeightedApproximateTangentSpaceAt` does not. The Lean statement (line 46072) assumes them, and they are now stated.
- **Calls**: `lpf_wtc_chart_image_measurable_locally_finite` (A.4), `lpf_wtc_lusin_compact_pieces` (A.4), `lpf_wtc_ae_zero_density_off_set` (A.4), `lpf_wtc_chart_approx_tangent` (A.4), `lpf_wtc_tangent_transfer` (A.4), `lpf_wtc_weighted_tangent_transfer` (A.4)
- **Called by**: `slicing_im_coarea_pieces`

#### `slicing_im_coarea_line_deriv` (L46132)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.line_deriv-a1` · issue #3428 · PR #3948 · candidate `b1189c5f5e41`
- **Statement and proof**: Simon Ch. 2, 4.7/4.10 (used for the co-area step of Ch. 6, 4.5): if `F : ℝ^P → ℝ` is `K`-Lipschitz on a neighbourhood `V` of `Φ(w)` and both `Φ` and `F ∘ Φ` are differentiable at `w`, then `t ↦ F(Φ(w) + t DΦ(w)s)` has derivative `D(F∘Φ)(w)s` at `0`.  For small `t` it differs from `t ↦ F(Φ(w + ts))` by at most `K ‖Φ(w + ts) - Φ(w) - t DΦ(w)s‖ = o(t)`, and the latter map has derivative `D(F∘Φ)(w)s`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_pieces`

#### `slicing_im_coarea_glue` (L16427)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.glue-a1` · issue #3394 · PR #4029 · candidate `8723e7ff4f22`
- **Statement and proof**: Countable gluing of co-area identities.  Put `Z = M \ ⋃ i, W i`.  For a.e. `t`, `ν (Z ∩ f⁻¹{t}) = 0`, so `M ∩ f⁻¹{t}` and `⋃ i, (W i ∩ f⁻¹{t})` are `ν`-a.e. equal and the slice integral over `M` is the sum of the slice integrals over the disjoint pieces `W i ∩ f⁻¹{t}`. Integrating in `t` (`lintegral_tsum`) and summing the piece identities gives `∫_{⋃ W i} J g dμ` (`lintegral_iUnion`), which is `∫_M J g dμ` because `J g = 0` a.e. on `Z`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea`

#### `slicing_im_coarea_eilenberg` (L44953)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1` · issue #3389 · PR #4896 · candidate `bda07ad44078`
- **Statement and proof**: Eilenberg's inequality for a real-valued Lipschitz function (Federer 2.10.25 with target `ℝ`), for the normalized `Hᵏ = μHE[k]`: if `f` is `L`-Lipschitz on `A ⊆ ℝ^P`, some Borel `φ` majorizes `t ↦ Hᵐ(A ∩ f⁻¹{t})` with `∫ φ ≤ C(m) L Hᵐ⁺¹(A)`.  With `κ_d` the scalar of `μHE[d] = κ_d • μH[d]` (`euclideanHausdorffMeasure_def`; it does not depend on the space and `κ_{m+1} ≠ 0`), take `C = 2 κ_m / κ_{m+1}` and `φ = κ_m ψ`, where `ψ` is the majorant for the unnormalized `μH` with constant `2` (`slicing_im_coarea_eil_unnormalized`).
- **Calls**: `slicing_im_coarea_eil_unnormalized`
- **Called by**: `slicing_im_coarea_chart_critical`, `slicing_im_coarea`

#### `slicing_im_coarea_eil_unnormalized` (L44888)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.unnormalized-a1` · issue #4067 · PR #4849 · candidate `cd8c8dbf850d`
- **Statement and proof**: Eilenberg's inequality for the unnormalized Hausdorff measures on an extended metric space: if `f : X → ℝ` is `L`-Lipschitz on `A`, some Borel `ψ` majorizes `t ↦ μH[m](A ∩ f⁻¹{t})` with `∫ ψ ≤ 2 L μH[m+1](A)`.  For `L = 0` take `∞ · 1_{f(A)}` (`f(A)` has at most one point), and for `μH[m+1](A) = ∞` the constant `∞`.  Otherwise `ψ = liminf_k ψ_k`, where `ψ_k` is the majorant (`slicing_im_coarea_eil_cover_majorant`) of a near-optimal cover of `A` at scale `(k + 1)⁻¹` (`slicing_im_coarea_eil_near_optimal_cover`): the pointwise bound is `slicing_im_coarea_eil_liminf_cover_bound` and the integral bound is Fatou's lemma.
- **Calls**: `slicing_im_coarea_eil_near_optimal_cover`, `slicing_im_coarea_eil_cover_majorant`, `slicing_im_coarea_eil_liminf_cover_bound`
- **Called by**: `slicing_im_coarea_eilenberg`

#### `slicing_im_coarea_eil_near_optimal_cover` (L4899)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.near_optimal_cover-a1` · issue #4036 · PR #4698 · candidate `0f6e5c4d010a`
- **Statement and proof**: Near-optimal covers for `μH[d]` (`d ≥ 0`, `μH[d] A < ∞`): for `r, ε > 0`, `A` is covered by sets `S i ⊆ A` of diameter `≤ r` with `∑ᵢ (diam S i)^d ≤ μH[d] A + ε`, empty pieces counting `0`. By `hausdorffMeasure_apply` the `r`-content of `A` is `≤ μH[d] A < μH[d] A + ε`, so some cover `t` beats `μH[d] A + ε`; its traces `t i ∩ A` keep the cover and only shrink diameters.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_eil_unnormalized`

#### `slicing_im_coarea_eil_cover_majorant` (L4949)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.cover_majorant-a1` · issue #4054 · PR #4700 · candidate `c0d786c5e4b0`
- **Statement and proof**: If `f` is `L`-Lipschitz on `A` and `S i ⊆ A`, a Borel `ψ : ℝ → [0, ∞]` majorizes the slice sums `∑ᵢ (ediam (S i ∩ A ∩ f⁻¹{t}))^m` over nonempty pieces, with `∫ ψ ≤ 2 L ∑ᵢ (ediam (S i))^(m+1)` (empty `S i` omitted).  Pick `a i = f xᵢ` with `xᵢ ∈ S i` (any `a i` if `S i = ∅`), so `f (S i) ⊆ Iᵢ := closedEBall (a i) (L · ediam (S i))`, and take `ψ = ∑ᵢ cᵢ 1_{Iᵢ}`, `cᵢ = (ediam (S i))^m` (`0` if `S i = ∅`): a nonempty piece `S i ∩ (A ∩ f⁻¹{t}) ∋ y` forces `t = f y ∈ Iᵢ`, and `λ¹(Iᵢ) = 2 L ediam (S i)` (`Real.volume_closedEBall`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_eil_unnormalized`

#### `slicing_im_coarea_eil_liminf_cover_bound` (L4927)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.eilenberg-a1.liminf_cover_bound-a1` · issue #4045 · PR #4678 · candidate `05b86f9232cb`
- **Statement and proof**: Used for Eilenberg's inequality (Federer 2.10.25) in the formal proof of the co-area formula of Simon Ch. 6, Lemma 4.1 **[corrected]**: if for every `k` the sets `T k i` (`i ∈ ℕ`) cover `s` and have diameter `≤ r k`, where `r k → 0`, then `μH[d](s) ≤ liminf_k ∑ᵢ (ediam T k i)^d`, empty pieces contributing `0`.  Reindexing the `k`-th cover by its nonempty pieces `{i // (T k i).Nonempty}` (a countable type) keeps a cover of `s` with the same diameter bound, so Mathlib's `hausdorffMeasure_le_liminf_tsum` bounds `μH[d](s)` by the liminf of the reindexed sums; each reindexed sum is at most the sum over all `i`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Simon Ch. 6, §4 (Eilenberg's inequality in the coarea step)". Simon's §4 does not use Eilenberg's inequality; it enters through step 5 of the accepted proof of `slicing_im_coarea`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_eil_unnormalized`

#### `slicing_im_coarea_chart_critical` (L46978)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1` · issue #3443 · PR #4942 · candidate `cf62f63388be`
- **Statement and proof**: Slices of the critical part of a `C¹` chart piece are `Hᵐ`-null for a.e. level (Simon Ch. 2, 6.3–6.4, via Eilenberg's inequality).  Put `E₀ = Ω ∩ Φ⁻¹(W)`, so that `W = Φ(E₀)` and `Dh = 0` on `E₀`.  For `R ∈ ℕ` and `ε > 0`, `slicing_im_coarea_cc_small_lip_partition` splits `E₀ ∩ B(0, R)` into disjoint Borel pieces `D k` on which `h` is `ε`-Lipschitz.  As `f ∘ Φ = h` on `E₀` and `c |w - w'| ≤ |Φ w - Φ w'|`, `f` is `ε c⁻¹`-Lipschitz on `Φ(D k)`, so Eilenberg's inequality `slicing_im_coarea_eilenberg` dominates the slices of `Φ(D k)` by `φ k` with `∫ φ k ≤ C ε c⁻¹ Hⁿ(Φ(D k)) ≤ C ε c⁻¹ Kⁿ Lⁿ(D k)`; these sum to at most `ε · C c⁻¹ Kⁿ Lⁿ(B(0, R))`.  Hence `slicing_im_coarea_cc_null_of_small_majorants` makes the slices of `Φ(E₀ ∩ B(0, R))` null for a.e. level, and `W = ⋃_R Φ(E₀ ∩ B(0, R))`.
- **Calls**: `slicing_im_coarea_eilenberg`, `slicing_im_coarea_cc_null_of_small_majorants`, `slicing_im_coarea_cc_small_lip_partition`
- **Called by**: `slicing_im_coarea`

#### `slicing_im_coarea_cc_null_of_small_majorants` (L4856)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.null_of_small_majorants-a1` · issue #3901 · PR #4494 · candidate `4dd0c03d8f6b`
- **Statement and proof**: Slices of `S` are `ν`-null for a.e. level if `S` admits countable covers with measurable majorants of arbitrarily small total integral: if for every `ε > 0` there are `A k` covering `S` and measurable `φ k` with `ν (A k ∩ f ⁻¹' {t}) ≤ φ k t` and `∑' k, ∫⁻ φ k ≤ ε * M` (`M ≠ ∞`), then `ν (S ∩ f ⁻¹' {t}) = 0` for a.e. `t`.  For `ε_j = 1 / (j + 1)`, `g = ⨅ j, ∑' k, φ_j k` is a measurable majorant of `t ↦ ν (S ∩ f ⁻¹' {t})` with `∫⁻ g ≤ ε_j * M → 0`, so `g = 0` a.e.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_chart_critical`

#### `slicing_im_coarea_cc_small_lip_partition` (L4814)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_critical-a1.small_lip_partition-a1` · issue #3894 · PR #4604 · candidate `5a9e3fad9b64`
- **Statement and proof**: A `C¹` function `h` on `ℝⁿ` is `ε`-Lipschitz on each piece of a countable Borel partition of a Borel set `E` on which `Dh = 0`.  Continuity of `Dh` gives balls `B(w, r w)`, `w ∈ E`, with `‖Dh‖₊ < ε`, on which `h` is `ε`-Lipschitz by the mean value inequality; countably many of them cover `E` (Lindelöf), and `D k = E ∩ disjointed B k` disjointifies this cover.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_chart_critical`

#### `slicing_im_coarea_chart_regular` (L47062)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1` · issue #3444 · PR #5141 · candidate `abc1acd4f4d7`
- **Statement and proof**: Co-area formula on a regular injective `C¹` chart (Simon Ch. 3, 2.9 for real-valued `f` on `M = Φ(Ω)`; the last part of Ch. 6, Lemma 4.1): let `Φ` be `C¹`, Lipschitz and antilipschitz on the open `Ω ⊆ ℝⁿ`, `W ⊆ Φ(Ω)` Borel, and on `Ω ∩ Φ⁻¹(W)` let `G ≠ 0` be the tangential gradient of `f` along `Φ`: `f ∘ Φ = h`, `G(Φw) ∈ range DΦ(w)` and `⟨G(Φw), DΦ(w)u⟩ = Dh(w)u`.  Then `t ↦ ∫_{W ∩ f⁻¹{t}} g dH^m` is a.e.-measurable and `∫ ∫_{W ∩ f⁻¹{t}} g dH^m dt = ∫_W |G| g dHⁿ`. Every `w₀ ∈ Ω ∩ Φ⁻¹(W)` is a regular point of `h`, so `h` is straightened by a chart `χ` with `w₀ ∈ χ(B)`; on Borel subsets of `χ(B)` the identity holds by the box co-area lemma, and the local-to-global lemma glues these pieces.
- **Calls**: `slicing_im_creg_local_to_global`, `slicing_im_creg_straightening`, `slicing_im_creg_box_coarea`
- **Called by**: `slicing_im_coarea`

#### `slicing_im_creg_local_to_global` (L16355)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.cover-a1` · issue #4150 · PR #4768 · candidate `f17042c51b0e`
- **Statement and proof**: Local-to-global gluing of co-area identities through an injective continuous chart (used for the co-area formula of Simon Ch. 6, Lemma 4.1, p. 154 **[corrected]**): let `Ω` be open, `f` measurable and `W ⊆ Φ(Ω)` Borel **[corrected]**. If every point of `Ω ∩ Φ⁻¹(W)` has an open neighbourhood `O` such that for all Borel `S ⊆ O ∩ Ω ∩ Φ⁻¹(W)` the slice function `t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dν` is a.e.-measurable and `∫ ∫_{Φ(S) ∩ f⁻¹{t}} g dν dt = ∫_{Φ(S)} J g dμ`, then the same holds with `Φ(S)` replaced by `W` (Lindelöf, disjointification, Lusin–Souslin and countable additivity).
- **Correction**: the Lean doc comment, kept byte-identical (§9), gives p. 153. §4 begins at the foot of p. 153, but Lemma 4.1 and its co-area formula are printed on p. 154, the page that `slicing_im_st_slice_geometry` cites. The doc comment also omits these hypotheses of the Lean statement (line 16355). `W ⊆ Φ(Ω)` is necessary: for `n = P = 1`, `Ω = (0, 1)`, `Φ = f = id`, `W = {5}`, `ν = 0`, `μ = δ₅` and `J = g = 1`, the hypothesis holds vacuously while the conclusion reads `0 = 1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_chart_regular`

#### `slicing_im_creg_straightening` (L16238)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.straighten-a1` · issue #4135 · PR #4829 · candidate `7a8b65c256aa`
- **Statement and proof**: Straightening at a regular point (inverse function theorem): if `h` is `C¹` and `Dh(w₀) ≠ 0`, the local inverse `χ` of `Ψ = [h, π]` (`π` the orthogonal projection onto `ker Dh(w₀) ≅ ℝ^m`) is a `C¹`, Lipschitz chart on an open `B` with `w₀ ∈ χ(B) ⊆ Ω`, `h ∘ χ = y ↦ y 0` on `B`, and `|v - v'| ≤ |χ[t,v] - χ[t,v']|` on each slice `{y 0 = t}`, where `[t,v] = (t, v_0, …, v_{m-1})`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_coarea_chart_regular`

#### `slicing_im_creg_box_coarea` (L46231)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1` · issue #4143 · PR #5115 · candidate `bdc372057ab8`
- **Statement and proof**: Co-area formula on one straightened box.  Let `Φ` be a `C¹` Lipschitz, antilipschitz chart on `Ω`, and let `(B, χ)` straighten `h`: `h (χ y) = y₀` on `B` and `‖v - v'‖ ≤ ‖χ [t, v] - χ [t, v']‖`. If `S ⊆ χ(B)` is Borel and on `S` we have `f ∘ Φ = h`, `G ∘ Φ ∈ range DΦ` and `⟪G (Φ w), DΦ(w) u⟫ = Dh(w) u`, then `t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dHᵐ` is a.e.-measurable and `∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dHᵐ dt = ∫_{Φ(S)} ‖G‖ g dHᵐ⁺¹`.  Both sides equal `∫ F̃ dLᵐ⁺¹`, where `F̃ = 1_{B ∩ χ⁻¹(S)} · g(Φ(χ y)) · 𝒥(y)`: the right side by `bulk` and the Jacobian identity, the left side by Tonelli along `y = [y₀, tail y]` and `slice_area`.
- **Calls**: `slicing_im_creg_jacobian_identity`, `slicing_im_creg_lintegral_cons`, `slicing_im_creg_box_integrand_measurable`, `slicing_im_creg_box_slice_area`, `slicing_im_creg_box_bulk`
- **Called by**: `slicing_im_coarea_chart_regular`

#### `slicing_im_creg_jacobian_identity` (L16109)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.jacobian-a1` · issue #4115 · PR #4832 · candidate `46c9d53ecea6`
- **Statement and proof**: Jacobian identity for the slice map, in Gram-determinant form: if `γ ∈ range A` is dual to the first coordinate, `⟪γ, A (D y)⟫ = y₀`, then with `eᵢ` the standard basis, `√det(⟪A D e_{i+1}, A D e_{j+1}⟫)_{i,j<m} = ‖γ‖ · √det(⟪A eᵢ, A eⱼ⟫)_{i,j≤m} · |det D|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_creg_box_coarea`

#### `slicing_im_creg_lintegral_cons` (L16214)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.tonelli-a1` · issue #4121 · PR #4796 · candidate `21ca221e7302`
- **Statement and proof**: Tonelli in the coordinates `ℝ^{m+1} = ℝ × ℝ^m`: `(t, v) ↦ [t, v]` is the composite of the volume-preserving maps `id × ofLp`, `(piFinSuccAbove _ 0).symm = Fin.cons` and `toLp`, so `∫ F = ∫ F ∘ [·,·]` over `ℝ × ℝ^m`, which splits by `lintegral_prod`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_creg_box_coarea`

#### `slicing_im_creg_box_integrand_measurable` (L16071)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.integrand_measurable-a1` · issue #4870 · PR #5071 · candidate `4a45b7920398`
- **Statement and proof**: Borel measurability of the straightened slice-Jacobian integrand `F̃ = 1_{S′} · (y ↦ g(Φ(χ y)) · √det(⟨DΦ(χ y)(Dχ(y)e_{i+1}), DΦ(χ y)(Dχ(y)e_{j+1})⟩)_{i,j<m})`, `S′ = B ∩ χ⁻¹(S)`, for `Φ` of class `C¹`, `χ` of class `C¹` on the open set `B`, `S` and `g` Borel.  The extension `χ̃ = B.piecewise χ 0` of `χ` is Borel, so `S′ = B ∩ χ̃⁻¹(S)` is Borel, and on `S′` the outer `χ` may be replaced by `χ̃`.  `y ↦ Dχ(y)v` is measurable for any `χ`, while `(x, u) ↦ DΦ(x)u`, the inner product and the determinant are continuous.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_creg_box_coarea`

#### `slicing_im_creg_box_slice_area` (L45061)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.slice_area-a1` · issue #4866 · PR #5079 · candidate `754abeed9103`
- **Statement and proof**: Area formula on the slices `{y₀ = t}` of a straightened chart `(B, χ)` (Simon Ch. 3, 2.6 on each slice; used for the co-area formula of Ch. 6, 4.1): with `[t, v] = (t, v₀, …, v_{m-1})`, the slice map `σ_t(v) = Φ(χ[t, v])` is Lipschitz and `c`-antilipschitz on the open slice `B_t = {v | [t, v] ∈ B}`, so the chart change of variables gives `∫_{σ_t(S′_t)} g dHᵐ = ∫_{S′_t} g(σ_t(v)) Jσ_t(v) dLᵐ(v)` with `S′ = B ∩ χ⁻¹(S)`, and by the chain rule `Dσ_t(v) eᵢ = DΦ(χ[t, v]) (Dχ([t, v]) eᵢ₊₁)`, i.e. `Jσ_t(v) = 𝒥([t, v])`.
- **Calls**: `lpf_raf_chart_change_of_variables` (A.4)
- **Called by**: `slicing_im_creg_box_coarea`

#### `slicing_im_creg_box_bulk` (L44989)

- `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1.bulk-a1` · issue #4859 · PR #5069 · candidate `93feccc4b332`
- **Statement and proof**: Area formula through a chart composed with an injective `C¹` change of variables (one straightened box of the co-area formula, Simon Ch. 3, 2.7–2.9; used for Ch. 6, §4): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω`, `χ` is `C¹` and injective on the open set `B` with `χ(B) ⊆ Ω`, `S ⊆ χ(B)` is Borel and `ψ ≥ 0` is Borel, then `∫_{Φ(S)} ψ dHⁿ = ∫_{B ∩ χ⁻¹(S)} |det Dχ(y)| ψ(Φ(χ y)) JΦ(χ y) dLⁿ(y)`.  Apply the chart change of variables to `A = Φ(S)` (Borel by Lusin–Souslin, with `Ω ∩ Φ⁻¹(A) = S`), then Mathlib's change of variables along `χ` on the Borel set `B ∩ χ⁻¹(S)`, whose image is `S`.
- **Calls**: `lpf_raf_chart_change_of_variables` (A.4)
- **Called by**: `slicing_im_creg_box_coarea`

#### `slicing_im_st_measure_fields` (L5162)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1` · issue #3395 · PR #5136 · candidate `deae3dc4ec25`
- **Statement and proof**: Measure-theoretic fields of the slice triple (Simon Ch. 6, §4; Steps 2, 4, 5 and 6 of the slice triple): under the co-area identity for `(M, f, G)`, with `f` measurable and `G` Borel and bounded, `|G| ≤ L` (as for the tangential gradient of an `L`-Lipschitz `f`) **[corrected]**, for `L¹`-a.e. `t` the set `M_t = {x ∈ M : f x = t, G x ≠ 0}` is `H^m`-null-measurable, `θ` is `H^m`-integrable on `M_t ∩ K` for every compact `K ⊆ U`, and `ξ_t = ξ ∘ ι(|G|⁻¹ G)` is `H^m⌞M_t`-a.e. strongly measurable.  The null transfer moves the fields of `(M, θ, ξ)` to the whole slice `M ∩ f⁻¹{t}`, and `M_t = (M ∩ f⁻¹{t}) ∩ G⁻¹{0}ᶜ` inherits them.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 5162). The bound on `G` is necessary for the integrability claim: for `M = (0, 1)²` in `U = ℝ²` with `θ ≡ 1` and `ξ = e₁ ∧ e₂`, `f(x) = sin(1/x₁)` and `G = ∇f`, the co-area identity holds, but for every `t ∈ (−1, 1)` the slice `M_t` contains infinitely many segments `{s} × (0, 1)`, so `θ` is not `H¹`-integrable on `M_t ∩ [0, 1]²`.
- **Calls**: `slicing_im_st_ae_transfer`, `slicing_im_st_mf_slice_null_measurable`, `slicing_im_st_mf_slice_integrable`, `slicing_im_st_mf_slice_orientation_aesm`
- **Called by**: `slicing_im_st_slice_geometry`, `slicing_im_slice_triple`

#### `slicing_im_st_ae_transfer` (L5060)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.ae_transfer-a1` · issue #3390 · PR #4011 · candidate `dec06e62f162`
- **Statement and proof**: Null transfer to slices (Simon Ch. 6, §4; Step 1 of the slice triple): under the co-area identity for `(M, f, G)`, a property holding `H^{m+1}`-a.e. on `M` holds `H^m`-a.e. on `M ∩ f⁻¹{t}` for `L¹`-a.e. `t`.  Apply the co-area identity to the indicator of a measurable null hull `Z` of `{¬p}`: the right side vanishes, so `H^m⌞(M ∩ f⁻¹{t})(Z) = 0` for a.e. `t`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_measure_fields`, `slicing_im_st_slice_geometry`, `slicing_im_slice_triple`

#### `slicing_im_st_mf_slice_null_measurable` (L373)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_null_measurable-a1` · issue #4051 · PR #4697 · candidate `8962fd5666e0`
- **Statement and proof**: For a.e. `t`, the slice `M ∩ f⁻¹{t}` of an `Hᵐ⁺¹`-null-measurable `M` by a measurable `f` is `Hᵐ`-null-measurable, given that `Hᵐ⁺¹⌞M`-a.e. properties hold `Hᵐ⌞(M ∩ f⁻¹{t})`-a.e. for a.e. `t`.  With a Borel `B ⊆ M`, `B = M` `Hᵐ⁺¹`-a.e., the slice is the Borel set `B ∩ f⁻¹{t}` plus the part outside `B`, which is `Hᵐ`-null for a.e. `t`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_measure_fields`

#### `slicing_im_st_mf_slice_integrable` (L4992)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_integrable-a1` · issue #4060 · PR #4706 · candidate `079d76f82b5f`
- **Statement and proof**: Let `U` be open and `M ⊆ U`, let `θ` be `Hᵐ⁺¹`-integrable on `M ∩ K` for compact `K ⊆ U`, and let `|G| ≤ L` and the co-area identity and the null transfer hold for `(M, f, G)` **[corrected]**. Then for `L¹`-a.e. `t`, `θ` is `Hᵐ`-integrable on `M ∩ f⁻¹{t} ∩ K` for every compact `K ⊆ U`: co-area with `g = 1_{Kᵢ} |θ₀|` over a compact exhaustion `Kᵢ` of `U` gives `∫∫_{M ∩ f⁻¹{t} ∩ Kᵢ} |θ₀| dHᵐ dt ≤ L ∫_{M ∩ Kᵢ} |θ| dHᵐ⁺¹ < ∞` **[corrected]**, `θ₀` a Borel version of `θ` on `M`, transferred to the slices by the null-transfer hypothesis.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the hypotheses of the Lean statement (line 4992). The bound `|G| ≤ L` and the integrability of `θ` on `M ∩ K` are what make the co-area integrals finite; without the bound the example in the entry `slicing_im_st_measure_fields` applies. The bound displayed in the sketch is added; the Lean proof derives it from the co-area identity (lines 5026–5027).
- **Calls**: `cmb_exists_compactly_contained_exhaustion` (A.1)
- **Called by**: `slicing_im_st_measure_fields`

#### `slicing_im_st_mf_slice_orientation_aesm` (L5126)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_orientation_aesm-a1` · issue #4072 · PR #4945 · candidate `9defddc28bf9`
- **Statement and proof**: For `L¹`-a.e. `t`, the sliced orientation `x ↦ ξ(x) ∘ ι(|G x|⁻¹ G x)`, where `ι v = (v♭ ∧ ·) : Λᵐ → Λᵐ⁺¹`, is a.e. strongly measurable for `Hᵐ` on `M ∩ f⁻¹{t}`: it agrees there with `x ↦ ξ₀(x) ∘ ι(|G x|⁻¹ G x)` for a strongly measurable version `ξ₀` of `ξ`.
- **Calls**: `slicing_im_st_mf_contraction_lipschitz`
- **Called by**: `slicing_im_st_measure_fields`

#### `slicing_im_st_mf_contraction_lipschitz` (L5090)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.contraction_lipschitz-a1` · issue #4068 · PR #4691 · candidate `034bfcd73baa`
- **Statement and proof**: `v ↦ ι(v)`, `ι(v) α = alternatizeUncurryFin ((innerSL ℝ v).smulRight α) = v♭ ∧ α`, is `(m + 1)`-Lipschitz from `ℝ^P` to `Λ^m →L Λ^{m+1}` with the operator norm.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_mf_slice_orientation_aesm`

#### `slicing_im_st_slice_geometry` (L46813)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.slice_geometry-a1` · issue #3426 · PR #5177 · candidate `9a27cfc863f3`
- **Statement and proof**: Simon Ch. 6, Lemma 4.1 (1)–(2) (p. 154), from Ch. 3, 2.10(2) and 1.6 (`n = m + 1`): for `L¹`-a.e. `t` the regular level set `M_t = {x ∈ M : f(x) = t, G(x) ≠ 0}` is countably `m`-rectifiable, and at `H^m`-a.e. `x ∈ M_t` every weighted approximate tangent plane `Q` of `(M, θ)` gives the weighted approximate tangent plane `Q ∩ G(x)^⊥` of `(M_t, θ)`. `M` is covered up to an `Hⁿ`-null set by C¹ antilipschitz charts `Φ j` with `f ∘ Φ j = h j` on `A j`, `h j` C¹, `range DΦ j` the tangent plane, `G ∈ range DΦ j` and `⟪G, DΦ j u⟫ = D(h j) u` (`slicing_im_st_chart_data`). For a.e. `t` these facts hold at `H^m`-a.e. point of `M_t` (`slicing_im_st_ae_transfer`), and `M_t` is `H^m`-null-measurable with `θ` locally integrable (`slicing_im_st_measure_fields`). The images under `Φ j` of the regular parts `{w ∈ Ω j : h j w = t, D(h j)(w) ≠ 0}` of the level sets are covered by C¹ bi-Lipschitz `m`-charts `Ψ` with `range DΨ(v) = DΦ j(w)(ker D(h j)(w))` where `Ψ(v) = Φ j(w)` (`slicing_im_st_level_set_charts`) **[corrected]**. At a good point `G ≠ 0` forces `D(h j) ≠ 0`, and `DΦ j (ker D(h j)) = Q ∩ G^⊥`. Lipschitz extensions of the `Ψ` cover `M_t` up to an `H^m`-null set, and `slicing_im_st_weighted_tangent_on_c1_chart` makes each `range DΨ` a weighted approximate tangent plane of `(M_t, θ)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says that the level sets `{h j = t}` are covered by charts with `range DΨ = DΦ j (ker D(h j))`. At a critical point, `ker D(h j)` is all of `ℝⁿ`, so `DΦ j(w)(ker D(h j)(w))` is `(m + 1)`-dimensional and cannot be the range of the derivative of an `m`-chart; `slicing_im_st_level_set_charts` covers the images of the regular points only, which suffices because `G ≠ 0` forces `D(h j) ≠ 0` (next sentence).
- **Calls**: `slicing_im_st_chart_data`, `slicing_im_st_ae_transfer`, `slicing_im_st_measure_fields`, `slicing_im_st_level_set_charts`, `slicing_im_st_weighted_tangent_on_c1_chart`
- **Called by**: `slicing_im_slice_triple`

#### `slicing_im_st_chart_data` (L45965)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1` · issue #3407 · PR #5163 · candidate `402bc07ae520`
- **Statement and proof**: Simon Ch. 6, 4.1(2) and 4.4 (Step 7 of the slicing argument for `τ(M, θ, ξ)`, `n = m + 1`): countably many `C¹` charts `Φ j`, antilipschitz on open `Ω j ⊆ ℝⁿ`, with sets `A j ⊆ Ω j` and `C¹` functions `h j` such that `f ∘ Φ j = h j` on `A j`, `M ∖ ⋃ j, Φ j (A j)` is `Hⁿ`-null and, at `Hⁿ`-a.e. `x = Φ j w ∈ M` with `w ∈ A j`, `DΦ j (w)(ℝⁿ)` is the weighted approximate tangent plane of `(M, θ)` at `x`, contains the tangential gradient `G x` and `⟨G x, DΦ j (w) u⟩ = Dh j (w) u`. The charts `(Φ' i, Ω' i)` come from Simon Ch. 3, Lemma 1.2, the `C¹` pieces `(h' i k, A' i k)` of `f ∘ Φ' i` from Ch. 2, Theorem 1.5, and the index pairs `(i, k)` are merged by `Nat.unpair`.
- **Calls**: `slicing_im_st_cd_c1_cover`, `slicing_im_st_cd_c1_pieces_of_lipschitzOn`, `slicing_im_st_weighted_tangent_on_c1_chart`, `lpf_ccr_hasDerivAt_line_of_comp` (A.4)
- **Called by**: `slicing_im_st_slice_geometry`

#### `slicing_im_st_cd_c1_cover` (L44494)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1` · issue #4207 · PR #5139 · candidate `7ce14591c40a`
- **Statement and proof**: Simon Ch. 3, Lemma 1.2 ("only if", p. 70) and Remark 1.3: a countably `n`-rectifiable `M ⊆ ℝ^P` is covered, up to an `Hⁿ`-null set, by the images `Φ_j(Ω_j)` of countably many `C¹` maps `Φ_j : ℝⁿ → ℝ^P` on open sets `Ω_j ⊆ ℝⁿ`, each Lipschitz and antilipschitz on `Ω_j`.  With `M ⊆ M₀ ∪ ⋃_j F_j(ℝⁿ)` (Ch. 3, 1.1), `lpf_lipschitz_c1_immersion_pieces` for `F_j` gives `C¹` maps `G_{j,k}`, antilipschitz on open `O_{j,k}`; Rademacher and the critical-image lemma `slicing_im_st_cd_c1c_critical_image_null` show `Hⁿ(F_j(ℝⁿ) ∖ ⋃_k G_{j,k}(O_{j,k})) = 0`; the charts are `G_{j,k}` on `O_{j,k} ∩ B_r(0)`, `r ∈ ℕ`.
- **Calls**: `lpf_lipschitz_c1_immersion_pieces` (A.4), `slicing_im_st_cd_c1c_critical_image_null`
- **Called by**: `slicing_im_st_chart_data`

#### `slicing_im_st_cd_c1c_critical_image_null` (L13234)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.critical_image_null-a1` · issue #4877 · PR #5110 · candidate `ca0d69f9608b`
- **Statement and proof**: Simon Ch. 2, 3.4 (p. 54) on the critical set, the Sard-type step of the proof of Ch. 3, Lemma 1.2 (p. 70): the Jacobian `Jf` vanishes where `Df` is not injective, so if `f : ℝⁿ → ℝ^P` is Lipschitz and `C` is the set of points where `f` is differentiable with non-injective derivative, then `Hⁿ(f(C)) = 0`.  Proved directly: on pieces where `f` is `t²`-close to a non-injective `Df(y)`, `Hⁿ(f(·)) ≤ (L + 1)ⁿ · t · Lⁿ(·)`; sum the pieces and let `t → 0`.
- **Calls**: `slicing_im_st_cd_c1c_singular_compression`
- **Called by**: `slicing_im_st_cd_c1_cover`

#### `slicing_im_st_cd_c1c_singular_compression` (L5187)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.singular_compression-a1` · issue #4874 · PR #5073 · candidate `a7a07277ab92`
- **Statement and proof**: Compression estimate behind the critical-set step of the area formula (Simon Ch. 2, 3.2–3.4, pp. 53–54, via the approximation argument of [Har79], [Fed69]).  If `f` is `t²`-close on `S` to a non-injective linear map `A` (`0 < t ≤ 1`), then `Hⁿ(f(S)) ≤ (‖A‖ + t)ⁿ · t Lⁿ(S)`: for a unit vector `e ∈ ker A`, the compression `T x = x + (t - 1)⟨e, x⟩ e` has `det T = t`, and `f ∘ T⁻¹` is `(‖A‖ + t)`-Lipschitz on `T(S)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_cd_c1c_critical_image_null`

#### `slicing_im_st_cd_c1_pieces_of_lipschitzOn` (L44571)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.lipschitz_on_c1_pieces-a1` · issue #4211 · PR #4766 · candidate `17098070bab1`
- **Statement and proof**: Simon Ch. 2, Theorem 1.5 (C¹ Approximation Theorem), localized to a real function that is Lipschitz on an open set `Ω`: McShane-extend `u|Ω` to a Lipschitz `g : ℝⁿ → ℝ`, apply the C¹ approximation theorem to `g` with `ε_k = 1 / (k + 1)` (sets `C_k`, `C¹` functions `h_k`) and take `A_k = Ω ∩ C_k`.  Since `u = g` on the open set `Ω`, `u` has derivative `Dh_k` on `A_k`, and `Lⁿ(Ω ∖ ⋃ A_l) ≤ Lⁿ(ℝⁿ ∖ C_k) < 1 / (k + 1)` for every `k`.
- **Calls**: `lpf_c1_approximation_real` (A.4)
- **Called by**: `slicing_im_st_chart_data`

#### `slicing_im_st_weighted_tangent_on_c1_chart` (L45248)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.weighted_tangent_chart-a1` · issue #3404 · PR #4325 · candidate `04a776d4541f`
- **Statement and proof**: Weighted approximate tangent planes on a `C¹` antilipschitz chart (Simon Ch. 3, proof of 1.6 "⇒" and Remark 1.8(1); used for the tangent planes of `M` and of the level sets `M_t` in Ch. 6, 4.1(2) and 4.4): let `V` be open, `M ⊆ V` `Hⁿ`-null-measurable and `θ > 0` on `M` with `θ` `Hⁿ`-integrable on `M ∩ K` for compact `K ⊆ V` **[corrected]**. For `Hⁿ`-a.e. `y ∈ M ∩ Φ(Ω)` and every `w ∈ Ω` with `Φ w = y`, `DΦ(w)(ℝⁿ)` is the approximate tangent space of `M` with respect to `θ` at `y`.  Cover `M` up to an `Hⁿ`-null set by compact pieces `C k` on which `θ` is continuous (Lusin).  At `Hⁿ`-a.e. `y ∈ C k ∩ Φ(Ω)` the upper density theorem makes `Hⁿ ⌞ (C k ∖ Φ(Ω))`, `Hⁿ ⌞ (Φ(Ω) ∖ C k)` and `θ Hⁿ ⌞ (M ∖ C k)` of `n`-density `0`, so the tangent plane of the chart image `Φ(Ω)` at `y` passes first to `C k` and then to `(M, θ)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves the hypotheses on `(M, θ)` implicit. Simon's Ch. 3, 1.7 (p. 74) builds them into the definition of the approximate tangent space (for compact `K` in the whole space), but SimonGMT's `HasWeightedApproximateTangentSpaceAt` does not. The Lean statement (lines 45250–45253) assumes them, and they are now stated.
- **Calls**: `lpf_wtc_chart_image_measurable_locally_finite` (A.4), `lpf_wtc_lusin_compact_pieces` (A.4), `lpf_wtc_ae_zero_density_off_set` (A.4), `lpf_wtc_tangent_transfer` (A.4), `lpf_wtc_chart_approx_tangent` (A.4), `lpf_wtc_weighted_tangent_transfer` (A.4)
- **Called by**: `slicing_im_st_chart_data`, `slicing_im_st_slice_geometry`

#### `slicing_im_st_level_set_charts` (L46731)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1` · issue #3419 · PR #4916 · candidate `54d4b4edc3e9`
- **Statement and proof**: Level-set charts (implicit-function step of the slice-triple argument for Simon Ch. 6, §4): the regular points `w ∈ Ω`, `h w = t`, `Dh(w) ≠ 0` of a level set of a `C¹` function are covered, after applying the `C¹` map `Φ` (antilipschitz on the open set `Ω`), by countably many `C¹` charts `Ψ i` that are Lipschitz and antilipschitz on open sets `V i`, with tangent range `DΦ(w)(ker Dh(w))`.  Take the implicit-function chart `ψ x` of `local_graph` at every regular point `x`, keep countably many of the open sets `W x`, enumerated as `W (xs i)` (second countability), and set `Ψ i := Φ ∘ ψ (xs i)`, `V i := B(0, r (xs i))`; the tangent range is `tangent_range` with `c := 1`.
- **Calls**: `slicing_im_st_lsc_local_graph`, `slicing_im_st_lsc_tangent_range`
- **Called by**: `slicing_im_st_slice_geometry`

#### `slicing_im_st_lsc_local_graph` (L44700)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1` · issue #4136 · PR #4839 · candidate `45ba0d8e0ccd`
- **Statement and proof**: Local graph chart of a regular level set (implicit-function step of the level-set charts used for integer multiplicity slices, Simon Ch. 6, §4): if `h` is `C¹`, `U` is open, `w₀ ∈ U` and `Dh(w₀) ≠ 0`, then a `C¹` map `ψ : ℝ^m → ℝ^{m+1}` with `‖v - v'‖ ≤ ‖ψ v - ψ v'‖` maps `B(0, r)` into `U ∩ {h = h(w₀), Dh ≠ 0}` and onto the level set inside an open `W ∋ w₀`.  With the frame `(ι, p, e)` of `Dh(w₀)` (`slicing_im_st_lsc_kernel_frame`), `ψ v = w₀ + ι v + g̃ v • e`, where `g̃` is a `C¹` extension (`slicing_im_st_lsc_c1_extension`) of the implicit function `g` of `H (v, s) = h (w₀ + ι v + s • e)`, obtained from the inverse function theorem for `Φ (v, s) = (v, H (v, s))`.
- **Calls**: `slicing_im_st_lsc_kernel_frame`, `slicing_im_st_lsc_c1_extension`
- **Called by**: `slicing_im_st_level_set_charts`

#### `slicing_im_st_lsc_kernel_frame` (L44595)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.kernel_frame-a1` · issue #4118 · PR #4769 · candidate `942be35ef94e`
- **Statement and proof**: Adapted frame of a nonzero functional (step 1 of the regular level-set charts used for slices of a rectifiable triple, Simon Ch. 6, 4.1–4.4): for `ℓ ≠ 0` on `ℝ^{m+1}` there are a norm-preserving `ι : ℝ^m → ℝ^{m+1}` onto `ker ℓ`, a vector `e ⟂ range ι` with `ℓ e = 1`, and `p` with `ι (p u) + ℓ u • e = u`.  Take `e = ‖a‖⁻² • a` for the Riesz vector `a` of `ℓ`, `ι` from an orthonormal basis of `ker ℓ` (dimension `m` by rank–nullity) and `p u = ι⁻¹ (u - ℓ u • e)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_lsc_local_graph`

#### `slicing_im_st_lsc_c1_extension` (L44662)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.c1_extension-a1` · issue #4123 · PR #4751 · candidate `829465a8a234`
- **Statement and proof**: `C¹` germ extension (steps 1–2 of the level-set chart construction for Simon Ch. 6, 4.1–4.4 **[corrected]**): if `g` is `C¹` at `x`, then some `g'` that is `C¹` on all of `ℝ^m` agrees with `g` on a ball `B(x, ρ)`.  Take `ε` with `g` `C¹` on `B(x, ε)`, `ρ = ε / 3`, a bump `χ` with `χ = 1` on `B̄(x, ρ)` and `χ = 0` off `B(x, 2ρ)`, and `g' = χ g`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "for Simon Ch. 6, 4.6". 4.6 (p. 157) defines the slices of a general current; the level-set charts serve Lemma 4.1 and Definition 4.4, and reach 4.6 only through 4.5(2).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_st_lsc_local_graph`

#### `slicing_im_st_lsc_tangent_range` (L46673)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.tangent_range-a1` · issue #4145 · PR #4759 · candidate `fd6cb8de53c6`
- **Statement and proof**: Tangent range of a level-set chart (step 7 of the level-set charts for the slicing theorem, Simon Ch. 6, §4): if `ψ` is differentiable at `v` and `c`-antilipschitz (`c > 0`) on an open `V ∋ v`, and `h ∘ ψ` is constant on `V` with `Dh(ψ v) ≠ 0`, then `range D(Φ ∘ ψ)(v) = DΦ(ψ v)(ker Dh(ψ v))`.  By the derivative lower bound `Dψ(v)` is injective, by the chain rule its range lies in `ker Dh(ψ v)`, and both subspaces have dimension `m`.
- **Calls**: `lpf_wtc_cat_fderiv_lower_bound` (A.4)
- **Called by**: `slicing_im_st_level_set_charts`

#### `slicing_im_st_interior_product` (L62471)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.interior_product-a1` · issue #3437 · PR #4017 · candidate `c005e98f97c3`
- **Statement and proof**: Interior product of a unit simple `(m+1)`-vector with a unit vector of its plane (Simon Ch. 6, 4.3).  Let `τ` be an orthonormal frame of `T = span τ`, `0 ≠ g ∈ T`, `ν = |g|⁻¹ g`, and `w = ±τ₁ ∧ ⋯ ∧ τₘ₊₁`.  The contraction `w ⌞ ν : α ↦ w(ν♭ ∧ α)`, where `(ν♭ ∧ α)(v) = ∑ᵢ (-1)ⁱ ⟨ν, vᵢ⟩ α(v₀, …, v̂ᵢ, …, vₘ)` (`alternatizeUncurryFin_apply`), is `±τ'₁ ∧ ⋯ ∧ τ'ₘ` for an orthonormal basis `τ'` of `S = T ∩ g^⊥`.  Indeed `S` has dimension `m` (`finrank_add_inf_finrank_orthogonal'`), `σ = (τ', ν)` is an orthonormal basis of `T`, so `w = ±simpleNVector σ` (`Submission.fiw_ims_frame_sign`), and `(ν♭ ∧ α)(σ) = (-1)^m α(τ')` because `⟨ν, τ'ₖ⟩ = 0`, `|ν| = 1` and `removeNth (last m) σ = τ'`.
- **Calls**: `fiw_ims_frame_sign`
- **Called by**: `slicing_im_slice_triple`

#### `fiw_ims_frame_sign` (L36208)

- `root.flat_iff_weak-a1.im_series-a1.frame_sign-a1` · issue #1249 · PR #1761 · candidate `c90a40505abd`
- **Statement and proof**: Orthonormal frames of the same subspace have the same simple `n`-vector up to sign (Simon Ch. 6, 3.1: `ξ(x) = τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` is determined by `TₓM` up to sign).  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q = span τ = span τ'`.  Restricted to `Q`, an `n`-covector `ω` is an alternating `n`-form on the `n`-dimensional space `Q`, so `ω(τ') = b.det(b') ω(τ)` (`AlternatingMap.eq_smul_basis_det`, as in the determinant computation after (3.4), p. 147), and `b.det(b') = ±1` because the change of basis between orthonormal bases is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_isRectifiableTriple_of_eventually_mem`, `fiw_ims_orientation_sign`, `slicing_im_st_interior_product`

#### `slicing_im_slice_identity` (L66589)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1` · issue #2519 · PR #5413 · candidate `ef8a14137aad`
- **Statement and proof**: **Slice identity (Simon Ch. 6, Remark 4.2 and the proof of Lemma 4.5(2)).**  For `T = τ(M, θ, ξ)`, `f` Lipschitz with tangential gradient `G` on `M` and `ω ∈ 𝒟^m(U)`: for a.e. `t`, every slice `S` of `T` by `f` at `t` has `S(ω) = τ(M_t, θ, ξ_t)(ω)`, where `M_t = {x ∈ M : f x = t, G x ≠ 0}` and `ξ_t = ξ ⌞ (G/|G|)`. With `φ(r) = ∫_{M ∩ f⁻¹{r}} g dH^m` (`θ ⟨G♭∧ω, ξ⟩ = |G| g`), the Leibniz identity for the cut-off `h_ε = ψ_ε ∘ f` (tangential gradient `-ε⁻¹ 1_{t-ε<f<t} G`) and the co-area formula give `∫ h_ε ⟨ω, v'⟩ dμ' - ∫ h_ε ⟨dω, v⟩ dμ = -ε⁻¹ ∫_{t-ε}^t φ`; let `ε ↓ 0` at a Lebesgue point `t`.
- **Calls**: `slicing_im_coarea`, `slicing_im_si_coarea_null_sets`, `slicing_im_si_borel_density`, `slicing_im_si_signed_coarea`, `slicing_im_si_slice_ae_transfer`, `slicing_im_si_left_lebesgue_point`, `slicing_im_si_cutoff_tangential_gradient`, `slicing_im_lipschitz_leibniz`, `slicing_mb_pointwise_cutoff_tendsto`
- **Called by**: `slicing_integer_multiplicity_ae`

#### `slicing_im_si_coarea_null_sets` (L4199)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.coarea_null-a1` · issue #3825 · PR #4435 · candidate `977af2fe7e51`
- **Statement and proof**: **Null-set consequences of the co-area identity (Simon Ch. 6, proof of 4.5(2)).**  Assume (CA): for every Borel `g ≥ 0`, `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is a.e.-measurable and `∫_ℝ ∫_{M ∩ f⁻¹{t}} g dν dt = ∫_M |G| g dμ`.  Then (i) `G = 0` `μ⌞M`-a.e. on each level set `{f = c}` (test (CA) with `g = 1_{f = c}`: the slice integrals vanish for `t ≠ c`); and (ii) a `μ`-null `Z ⊆ M` has `ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t` (test (CA) with `g = 1_{Z'}`, `Z' ⊇ Z` a measurable `μ`-null hull).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_si_borel_density` (L18534)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.borel_density-a1` · issue #3830 · PR #4471 · candidate `1f74b5c5bd29`
- **Statement and proof**: **Borel density for `θ⟨ξ, G♭ ∧ ω⟩` (Simon Ch. 6, Remark 4.2 and proof of 4.5).**  For a rectifiable triple `(M, θ, ξ)`, a Borel `G`, `ν := |G|⁻¹G` and `ω ∈ 𝒟ᵐ(U)`, there is a Borel `Hⁿ⌞M`-integrable `g` vanishing on `{G = 0}` with `g = θ⟨ξ⌞ν, ω⟩` where `G ≠ 0` and `θ⟨ξ, G♭ ∧ ω⟩ = |G| g`, `Hⁿ⌞M`-a.e.: `g := 1_{K ∩ {G ≠ 0}} θ' ξ'(ν♭ ∧ ω)` with `K = tsupport ω`, Borel versions `θ'` of `θ` on `M ∩ K` and `ξ'` of `ξ` on `M`, dominated by `(m + 1) sup ‖ω‖ · |1_K θ'|` (unit bound `|ξ(α)| ≤ ‖α‖`).
- **Calls**: `fiw_ims_tt_unit_bound`
- **Called by**: `slicing_im_slice_identity`

#### `fiw_ims_tt_unit_bound` (L1959)

- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1` · issue #1482 · PR #1978 · candidate `27af9b191b73`
- **Statement and proof**: **Unit bound for the orientation `±τ₁ ∧ ⋯ ∧ τₙ` (Simon Ch. 6, 3.1).**  If `τ` is an orthonormal family in `ℝ^P` and `w = ±simpleNVector τ`, then `|w(α)| ≤ ‖α‖` for every `n`-covector `α`: `simpleNVector τ α = α(τ₁, …, τₙ)` and `‖α(τ)‖ ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖` (`ContinuousAlternatingMap.le_opNorm`, each `τᵢ` a unit vector).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_loc_tauAction_current`, `slicing_im_si_borel_density`, `iwl_cr_ci_integral_exchange`, `fiw_ims_tt_term_bound`, `slicing_im_tau_current`

#### `slicing_im_si_signed_coarea` (L18671)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.signed_coarea-a1` · issue #3835 · PR #4484 · candidate `95342e38669e`
- **Statement and proof**: Signed co-area identity on a level band (Simon Ch. 6, Remark 4.2): if the co-area formula `∫ ∫_{M ∩ f⁻¹{t}} h dν dt = ∫_M |G| h dμ` holds for every Borel `h ≥ 0` and `|G| g` is `μ⌞M`-integrable, then `t ↦ ∫_{M ∩ f⁻¹{t}} g dν` is integrable and `∫_{M ∩ f⁻¹(a, b)} |G| g dμ = ∫_{(a, b)} ∫_{M ∩ f⁻¹{t}} g dν dt` (split `g = g⁺ - g⁻`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_si_slice_ae_transfer` (L18768)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.slice_transfer-a1` · issue #3841 · PR #4453 · candidate `9d0e74d0c981`
- **Statement and proof**: Transfer of an a.e. identity on `M` to almost every slice: if `μ`-null subsets `Z ⊆ M` have `ν`-null slices `Z ∩ f⁻¹{t}` for a.e. `t`, `g = 0` off the Borel set `S` and `g = F` on `S` `μ⌞M`-a.e., then `∫_{M ∩ f⁻¹{t}} g dν = ∫_{{x ∈ M : f x = t, x ∈ S}} F dν` for a.e. `t` (Simon 4.5, slice identification).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_si_left_lebesgue_point` (L18822)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.left_lebesgue-a1` · issue #3844 · PR #4415 · candidate `bdf3439a7899`
- **Statement and proof**: One-sided Lebesgue points: for locally integrable `φ : ℝ → ℝ` and a.e. `t`, the left averages `ε⁻¹ ∫_{(t - ε, t)} φ` tend to `φ t` as `ε → 0+` (Lebesgue differentiation along the Vitali family of `volume`; Simon Ch. 6, Remark 4.2 and the proof of 4.5(2)).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_si_cutoff_tangential_gradient` (L18848)

- `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1` · issue #3848 · PR #4430 · candidate `586f960d4585`
- **Statement and proof**: Tangential gradient of the level cut-off `h_ε = ψ ∘ f`, `ψ(s) = max(0, min(1, (t - s)/ε))`: `h_ε` is Lipschitz and, wherever `G` is a tangential gradient of `f` vanishing on the level sets `{f = t - ε}` and `{f = t}`, `G_ε = 1_{t - ε < f < t} · (-ε⁻¹ G)` is a bounded Borel tangential gradient of `h_ε` (Simon Ch. 6, proof of 4.5(2)).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_lipschitz_leibniz` (L66540)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1` · issue #2506 · PR #5386 · candidate `a67b3e1b87f5`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 4.5(2), (1)–(3) (p. 156): Leibniz rule for a Lipschitz `h` with tangential gradient `G_h` on `M`, `T = τ(M, θ, ξ)`: `∫ h ⟨ω, v'⟩ dμ' − ∫ h ⟨dω, v⟩ dμ = ∫_M θ ⟨G_h ∧ ω, ξ⟩ dHⁿ`. For smooth `Lh`-Lipschitz `g_k → h` the smooth identity, rewritten through the tangent field `Y` with `φ(Y) = θ ⟨φ ∧ ω, ξ⟩`, reads `∫_M Dg_k(Y) dHⁿ = ∫ g_k ⟨ω, v'⟩ dμ' − ∫ g_k ⟨dω, v⟩ dμ`; the left side tends to `∫_M ⟨G_h, Y⟩ dHⁿ` and the right side to the left side of the claim.
- **Calls**: `slicing_im_ll_mollify`, `slicing_im_ll_tangent_dual_field`, `slicing_im_ll_smooth_leibniz`, `slicing_im_ll_multiplier_tendsto`, `slicing_im_ll_tangential_weak_limit`
- **Called by**: `slicing_im_slice_identity`

#### `slicing_im_ll_mollify` (L15961)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.mollify-a1` · issue #3629 · PR #4409 · candidate `58e6d1ca65a6`
- **Statement and proof**: Global smooth approximation of a Lipschitz function by mollification: `g k = ρ_k ⋆ h` with a normalized smooth bump `ρ_k ≥ 0`, `∫ ρ_k = 1`, supported in `B(0, 1/(k+1))`.  Each `g k` is `C^∞`, `L`-Lipschitz, and `|g k - h| ≤ L/(k+1)` uniformly.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_lipschitz_leibniz`

#### `slicing_im_ll_tangent_dual_field` (L23142)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangent_field-a1` · issue #3647 · PR #4366 · candidate `f3a3c5910cef`
- **Statement and proof**: The tangent vector field dual to `θ ⟨· ∧ ω, ξ⟩` (Simon Ch. 6, proof of Lemma 4.5(2), (1)–(3)): for a rectifiable triple `(M, θ, ξ)` of dimension `n = m + 1` and `ω ∈ 𝒟ᵐ(U)` there is `Y : ℝ^P → ℝ^P` with `φ(Y(x)) = θ(x) ⟨φ ∧ ω(x), ξ(x)⟩` for all `x` and all functionals `φ`, `Y ∈ L¹(Hⁿ ⌞ M)`, and `Y(x)` lies in every weighted approximate tangent plane at `Hⁿ`-a.e. `x ∈ M`.  Take the Riesz representative `Y(x) = ∑ᵢ θ(x) ⟨eᵢ♭ ∧ ω(x), ξ(x)⟩ eᵢ`.  A.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|ξ(x)(β)| ≤ ‖β‖` and `|Y| ≤ C |θ| 1_{spt ω}`; and for `w ⊥ span τ`, `(w♭ ∧ ω(x))(τ) = ∑ᵢ (-1)ⁱ ⟨w, τᵢ⟩ ω(x)(τ without τᵢ) = 0`, so `Y(x) ∈ (span τ)ᗮᗮ = span τ`, the unique weighted tangent plane (`θ(x) > 0`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_lipschitz_leibniz`

#### `slicing_im_ll_smooth_leibniz` (L16464)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.smooth_identity-a1` · issue #3641 · PR #4333 · candidate `0374472720fd`
- **Statement and proof**: Simon Ch. 6, proof of 4.5(2), (2), for a `C^∞` multiplier `ψ`: the Leibniz rule `∂T(ψ ω) = T(ψ dω) + T(Dψ ∧ ω)`, with `∂T` and `T` evaluated through their measure representations and `T(Dψ ∧ ω) = τ(M, θ, ξ)(Dψ ∧ ω)`.
- **Calls**: `slicing_mb_lb_smul_testForm`, `slicing_mb_lb_wedge_testForm`, `slicing_mb_lb_extDeriv_smul`
- **Called by**: `slicing_im_lipschitz_leibniz`

#### `slicing_im_ll_multiplier_tendsto` (L16029)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.multiplier_limit-a1` · issue #3636 · PR #4424 · candidate `175d7806c319`
- **Statement and proof**: Continuous multipliers `g k → f` converging uniformly on `ℝ^P`, integrated against a `ν`-integrable density `F` vanishing off a compact set `K`: `∫ g k F dν → ∫ f F dν`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_lipschitz_leibniz`

#### `slicing_im_ll_tangential_weak_limit` (L66466)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1` · issue #3668 · PR #5343 · candidate `7fa5d56cb674`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 4.5(2), (1): if the differentiable `L`-Lipschitz `g_k` converge uniformly to `h`, whose tangential gradient on `(M, θ)` is `G`, then `∫_M Dg_k(Y) dHⁿ` tends to `∫_M ⟨G, Y⟩ dHⁿ` for every integrable tangent field `Y`.  `M` is cut into pieces on disjoint `C¹` chart images, where `range DΦ` is the weighted tangent plane; on each piece both integrals are parameter integrals against one integrable field, which converge by the weak-* convergence of the chart gradients, and dominated convergence sums the pieces.
- **Calls**: `lpf_countably_rectifiable_c1_cover` (A.4), `slicing_im_ll_twl_partition_tendsto`, `lpf_weighted_tangent_on_c1_chart` (A.4), `slicing_im_ll_twl_chart_representation`, `slicing_im_ll_gradient_weak_star`
- **Called by**: `slicing_im_lipschitz_leibniz`

#### `slicing_im_ll_twl_partition_tendsto` (L62616)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.partition_tendsto-a1` · issue #4552 · PR #4968 · candidate `2153cd87992b`
- **Statement and proof**: Integrals converge if they converge on every piece of a countable measurable partition, under integrable domination (step 4 of the tangential weak limit argument).  As `ν` lives on `⋃ⱼ Vⱼ`, countable additivity gives `∫ H dν = ∑ⱼ ∫_{Vⱼ} H dν` for integrable `H`; the terms for `H = F_k` are bounded by the summable `∫_{Vⱼ} b dν`, so Tannery's theorem (dominated convergence for series, the `ε / 3` argument of Mathlib's `tendsto_tsum_of_dominated_convergence`, inlined since that file is not available here) passes to the limit termwise.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_ll_tangential_weak_limit`

#### `slicing_im_ll_twl_chart_representation` (L62829)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_representation-a1` · issue #4592 · PR #5303 · candidate `583322f91d4e`
- **Statement and proof**: Slicing (Simon Ch. 6, §4), tangential weak limit, step (9a)–(9b): over a chart piece `A ⊆ Φ(Ω)`, tangential integrals are parameter integrals against one field `c`, `∫_A Df(Y) dHⁿ = ∫_Ω D(f∘Φ)(c)` and `∫_A ⟨G, Y⟩ dHⁿ = ∫_Ω D(h∘Φ)(c)`.  Here `c` is the coefficient field (`DΦ(w) c(w) = JΦ(w) Y(Φ(w))` a.e. on `Ω ∩ Φ⁻¹(A)`, `c = 0` off it); both identities are the chart integral formula combined with the chain rule.
- **Calls**: `slicing_im_ll_twl_coefficient_field`, `slicing_im_ll_twl_chart_hasFDerivAt`, `slicing_im_ll_twl_chart_integral_eq`
- **Called by**: `slicing_im_ll_tangential_weak_limit`

#### `slicing_im_ll_twl_coefficient_field` (L62709)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.coefficient_field-a1` · issue #4575 · PR #5292 · candidate `60c90f12cfef`
- **Statement and proof**: Coefficient field on a chart piece (Simon Ch. 6, proof of 4.5(2)): if `Φ` is `C¹`, Lipschitz and `κ`-antilipschitz on the open `Ω`, `A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable and `Y` is `Hⁿ ⌞ A`-integrable with `Y(x) ∈ range DΦ(w)` for all `w ∈ Ω ∩ Φ⁻¹(x)`, `Hⁿ`-a.e. `x ∈ A`, then `c := 1_D Λ(DΦ)(JΦ · Y ∘ Φ)` (`D = Ω ∩ Φ⁻¹(A)`, `Λ` the continuous left inverse) vanishes off `D`, is `Lⁿ`-integrable (`|c| ≤ κ⁻¹ JΦ |Y ∘ Φ|`) and `DΦ(w) c(w) = JΦ(w) Y(Φ w)` for `Lⁿ`-a.e. `w ∈ D`.
- **Calls**: `lpf_tde_continuous_left_inverse` (A.4), `lpf_wtc_cat_fderiv_lower_bound` (A.4), `lpf_ccr_ae_pullback` (A.4), `slicing_im_ll_twl_chart_integral_eq`
- **Called by**: `slicing_im_ll_twl_chart_representation`

#### `slicing_im_ll_twl_chart_integral_eq` (L62682)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1` · issue #4559 · PR #5235 · candidate `73e7a45462ac`
- **Statement and proof**: Bochner change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6 for integrable integrands; used for Ch. 6, 4.5(2)): if `Φ` is Lipschitz and `κ`-antilipschitz on the open set `Ω`, `A ⊆ Φ(Ω)` is `Hⁿ`-null-measurable and `F` is Banach-valued and `Hⁿ⌞A`-integrable, then `D = Ω ∩ Φ⁻¹(A)` is `Lⁿ`-null-measurable, `JΦ · (F ∘ Φ)` is `Lⁿ`-integrable on `D` and `∫_A F dHⁿ = ∫_D JΦ(w) F(Φ(w)) dLⁿ(w)`.  The nonnegative chart formula, valid for every Borel `g ≥ 0`, says that `Φ` pushes `JΦ · Lⁿ⌞D` forward to `Hⁿ⌞A`.
- **Calls**: `lpf_raf_chart_change_of_variables` (A.4), `slicing_im_ll_twl_cie_weighted_transfer`, `slicing_im_ll_twl_cie_jacobian_measurable`
- **Called by**: `slicing_im_ll_twl_coefficient_field`, `slicing_im_ll_twl_chart_representation`

#### `slicing_im_ll_twl_cie_weighted_transfer` (L44125)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.weighted_transfer-a1` · issue #4904 · PR #5095 · candidate `b66ff150c0b5`
- **Statement and proof**: Bochner change of variables through a Jacobian-weighted push-forward: if `∫⁻ g dν = ∫⁻ g(Φ(x)) J(x) dμ(x)` for every measurable `g : Y → [0, ∞]`, then `Φ` pushes the measure `ρ = J μ` (density `J.toNNReal`) forward to `ν`, so for `ν`-integrable `F`, `J • F ∘ Φ` is `μ`-integrable and `∫ F dν = ∫ F(Φ(x)) dρ(x) = ∫ J(x) • F(Φ(x)) dμ(x)`.  No σ-finiteness is needed.  This passes the area formula on a chart from nonnegative to Bochner integrands.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_ll_twl_chart_integral_eq`

#### `slicing_im_ll_twl_cie_jacobian_measurable` (L44166)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.jacobian_measurable-a1` · issue #4909 · PR #5208 · candidate `379410958dd0`
- **Statement and proof**: Measurability of the Gram-determinant Jacobian (step 2 of the accepted natural-language proof of `slicing_im_ll_twl_chart_integral_eq`, the change of variables of Simon Ch. 3, 2.6 used for Ch. 6, 4.5(2) **[corrected]**): for an arbitrary map `Φ : ℝⁿ → ℝ^P`, `w ↦ √det(⟨DΦ(w)eᵢ, DΦ(w)eⱼ⟩)` is Borel measurable, being the continuous map `L ↦ √det(⟨Leᵢ, Leⱼ⟩)` on `ℝⁿ →L[ℝ] ℝ^P` composed with the Borel map `w ↦ fderiv ℝ Φ w`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 2 of Simon Ch. 6, 3.9 in charts". Lemma 3.9 (p. 148) has no steps, and this declaration is not used for it: its only user is `slicing_im_ll_twl_chart_integral_eq`, and its source is step 2 of the accepted proof of that node.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_ll_twl_chart_integral_eq`

#### `slicing_im_ll_twl_chart_hasFDerivAt` (L62778)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_has_fderiv_at-a1` · issue #4585 · PR #4986 · candidate `9bb46c57022b`
- **Statement and proof**: Chain rule on a `C¹` chart for a Lipschitz function with a tangential gradient (used for Simon Ch. 6, §4): if `h` is `L`-Lipschitz and, for `Hⁿ`-a.e. `x ∈ A`, `s ↦ h(x + s u)` has derivative `⟨G(x), u⟩` at `0` for all `u ∈ range DΦ(w)` with `Φ(w) = x`, then Rademacher's theorem on `Ω` and uniqueness of derivatives give `D(h ∘ Φ)(w) = ⟨G(Φ(w)), DΦ(w) ·⟩` for `Lⁿ`-a.e. `w ∈ Ω ∩ Φ⁻¹(A)`.
- **Calls**: `lpf_ccr_ae_pullback` (A.4)
- **Called by**: `slicing_im_ll_twl_chart_representation`

#### `slicing_im_ll_gradient_weak_star` (L66420)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1` · issue #3657 · PR #5016 · candidate `18e839d9d650`
- **Statement and proof**: Gradients of functions `u_k → u` that converge uniformly on an open `Ω ⊆ ℝⁿ` and are all `C`-Lipschitz on `Ω` converge weakly-* on `Ω`: `∫_Ω Du_k(c) → ∫_Ω Du(c)` for every field `c` integrable on `Ω`.
- **Calls**: `slicing_im_ll_gws_smooth_dense`, `slicing_im_ll_gws_smooth_tendsto`, `slicing_im_ll_gws_pairing_bound`
- **Called by**: `slicing_im_ll_tangential_weak_limit`

#### `slicing_im_ll_gws_smooth_dense` (L40561)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_dense-a1` · issue #4417 · PR #4924 · candidate `c278f023560d`
- **Statement and proof**: `C_c^∞` fields are dense in `L¹(Ω)`: for `Ω ⊆ ℝⁿ` open, `c : ℝⁿ → ℝⁿ` integrable on `Ω` and `δ > 0` there is a smooth `b` with compact support, `spt b ⊆ Ω` and `∫_Ω |c − b| < δ`.  The exhaustion `K_j = F_j ∩ B̄(0, j)` of `Ω` gives a compact `K ⊆ Ω` with `∫_{Ω∖K} |c| < δ/2`; `1_K c` is within `δ/2` in `L¹(ℝⁿ)` of a smooth compactly supported `b₀` (approximate simple functions, using the regularity of `Lⁿ` and the smooth Urysohn lemma); and `b = χ b₀` for a smooth cutoff `0 ≤ χ ≤ 1` with `χ = 1` on `K` and `spt χ ⊆ Ω`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_td_scalar_smooth_dense`, `slicing_im_ll_gradient_weak_star`

#### `slicing_im_ll_gws_smooth_tendsto` (L63024)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_tendsto-a1` · issue #4405 · PR #4949 · candidate `c64806cd2cf9`
- **Statement and proof**: Convergence of the gradient pairings against a `C¹` test field: if `u_k → u` uniformly on the open set `Ω`, all `C`-Lipschitz on `Ω`, and `b` is `C¹` with compact support in `Ω`, then `∫_Ω Du_k(b) → ∫_Ω Du(b)`.  With the weak divergence `g ∈ L¹` of `b` given by `slicing_im_ll_gws_lipschitz_ibp`, `∫_Ω Du_k(b) - ∫_Ω Du(b) = ∫_Ω (u - u_k) g`, which is at most `sup_Ω |u - u_k| · ∫_Ω |g|`.
- **Calls**: `slicing_im_ll_gws_lipschitz_ibp`
- **Called by**: `slicing_im_ll_gradient_weak_star`

#### `slicing_im_ll_gws_lipschitz_ibp` (L62917)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.lipschitz_ibp-a1` · issue #4397 · PR #4914 · candidate `50ef52b3e09d`
- **Statement and proof**: **Integration by parts against a `C¹` field, for functions Lipschitz on `Ω`.**  Let `Ω ⊆ ℝⁿ` be open and `b : ℝⁿ → ℝⁿ` be `C¹` with compact support and `tsupport b ⊆ Ω`.  The divergence `g = ∑ᵢ Dbᵢ(·)(eᵢ)` of `b` is integrable, and for every `f` that is `L`-Lipschitz on `Ω`, `f g` is integrable on `Ω` and `∫_Ω Df(b) = −∫_Ω f g`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not differentiable).  Extend `f` to an `L`-Lipschitz `F` on `ℝⁿ` (McShane); `DF = Df` on the open set `Ω` and `b, g` vanish off `Ω`, so both sides are integrals over `ℝⁿ` with `F` in place of `f`. Expand `b = ∑ᵢ bᵢ eᵢ`: by Rademacher's theorem `DF(w)(eᵢ)` is the line derivative of `F` along `eᵢ` for a.e. `w`, and integration by parts for Lipschitz functions moves it onto the compactly supported Lipschitz coordinate `bᵢ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_ll_gws_smooth_tendsto`

#### `slicing_im_ll_gws_pairing_bound` (L62880)

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.pairing_bound-a1` · issue #4387 · PR #4875 · candidate `50d79ad7aedd`
- **Statement and proof**: **Lipschitz bound, in the field, for the pairing `∫_Ω Df(b)`.**  If `f` is `C`-Lipschitz on the open set `Ω ⊆ ℝⁿ` and `b, b'` are integrable on `Ω`, then `|∫_Ω Df(b) − ∫_Ω Df(b')| ≤ C ∫_Ω |b − b'|`, where `Df(w) = fderiv ℝ f w` (`0` where `f` is not differentiable).  On `Ω` we have `‖Df(w)‖ ≤ C`, so `w ↦ Df(w)(v(w))` is dominated by `C |v|`; it is a.e. strongly measurable because `Df` is Borel, hence integrable for `v = b, b'`, and the estimate follows by linearity of the integral and of `Df(w)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `slicing_im_ll_gradient_weak_star`

#### `slicing_im_tau_current` (L66864)

- `root.slicing-a1.slice_integer_multiplicity-a1.tau_current-a1` · issue #2543 · PR #3757 · candidate `5a70d03c4185`
- **Statement and proof**: **A rectifiable triple defines a current `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a rectifiable triple `(M, θ, ξ)` in `U`, `ω ↦ ∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHᵏ(x)` is a sequentially continuous linear functional on `𝒟ᵏ(U)`.  The integrand is integrable (`ltg_tau_integrable`) and linear in `ω`.  If `ω_j → 0` in `𝒟ᵏ(U)`, all `ω_j` are supported in one compact `K ⊆ U` and `ω_j → 0` uniformly; as `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e. (`fiw_ims_tt_unit_bound`), eventually `|θ ⟨ω_j, ξ⟩| ≤ |θ| 1_K ∈ L¹(Hᵏ⌞M)`, and dominated convergence gives `τ(M, θ, ξ)(ω_j) → 0`.
- **Calls**: `ltg_tau_integrable`, `fiw_ims_tt_unit_bound`
- **Called by**: `slicing_integer_multiplicity_ae`

#### `ltg_tau_integrable` (L1431)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1` · issue #1341 · PR #2152 · candidate `1d327e46e1cf`
- **Statement and proof**: **Integrability of the integrands of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  For a rectifiable triple `(M, θ, ξ)` in `U`: (a) `x ↦ θ(x) ⟨b, ξ(x)⟩` is `Hᵏ`-integrable on `M ∩ K` for every compact `K ⊆ U` and `k`-covector `b`; (b) `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is `Hᵏ`-integrable on `M` for every continuous compactly supported `ω` with `spt ω ⊆ U`.  Since `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` with `τ` orthonormal, `|⟨α, ξ⟩| ≤ ‖α‖` `Hᵏ⌞M`-a.e.; `θ` is integrable on `M ∩ K`, and the integrand of (b) vanishes on `M \ spt ω`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ltg_tau_unique_on_open`, `ltg_tau_local_to_global`, `br_loc_tauAction_current`, `iwl_imc_tau_measure_representation`, `iwl_cr_interval_product_im`, `br_local_finite_mass_extension`, `imc_im_density_limit`, `deformation_im_completeness`, `slicing_im_tau_current`

### A.6 Deformation Theorem 5.1/5.3 (§3.6): `deformation_theorem` and its 188 further declarations

#### `deformation_theorem` (L66990)

- `root.deformation-a1` · issue #325 · PR #7759 · candidate `4efd922c99dc`
- **Statement and proof**: **Simon Ch. 6, 5.3 (Deformation Theorem, scaled version, p. 160); `ρ = 1` is 5.1.** Assembly of the decomposition (Part D and display (38) of the accepted proof): rescale `T` by `x ↦ ρ⁻¹x` (`T′ = (η_{1/ρ})_# T`), deform `T′` onto the unit `n`-skeleton (`T′ − Q = ∂R₁ + S₁`, `deformation_onto_skeleton`, which uses the slicing theorem and Lemma 3.9), replace `Q` by a lattice chain (`Q − P = S′`, `deformation_skeleton_polyhedral`), and push `P`, `R₁`, `S₁ + S′` forward by `x ↦ ρx` (`deformation_dilation`).  With `C₁`, `C₂` the constants of the two deformation steps, `C = C₁ + C₁C₂`; the supports lie within `√n + √(n+ℓ) < 2√(n+ℓ)` of `spt T′`, `spt ∂T′` before rescaling.
- **Calls**: `deformation_onto_skeleton`, `slicing_theorem` (A.5), `lipschitz_pushforward_integer_multiplicity` (A.4), `deformation_skeleton_polyhedral`, `deformation_dilation`, `deformation_im_combination`
- **Called by**: `isoperimetric_theorem`, `polyhedral_approximation`, `boundary_rectifiability`, `flat_convergence_iff_weak_convergence`, `main_theorem`

#### `deformation_onto_skeleton` (L47900)

- `root.deformation-a1.onto_skeleton-a1` · issue #1115 · PR #7347 · candidate `738861e0720c`
- **Statement and proof**: **Deformation onto the `n`-skeleton (Simon Ch. 6, §5, the main step of the proof of 5.1, printed displays (6)–(26)),** conditional on the Slicing Theorem and on Lemma 3.9.  For `n = m + 1`, `d = n + ℓ` there is `C = C(m, ℓ)` such that every `T ∈ 𝒟ₙ(ℝ^d)` with `M(T) + M(∂T) < ∞` satisfies `T − Q = ∂R + S` with `spt Q ⊆ L_n = ⋃_F latticeFace 1 F`, `Q` tangential to the open `n`-faces, `M(Q) ≤ C M(T)`, `M(∂Q) ≤ C M(∂T)`, `M(R) ≤ C M(T)`, `M(S) ≤ C M(∂T)`, supports in the closed `√d`-thickenings of `spt T`, `spt ∂T`, and integrality preserved. Proof (Steps 1–8 of the accepted proof): the centre `a` (`deformation_good_center`, applied to the mass measures of `T`, `∂T` from `deformation_mass_restriction`) and the retraction `ψ` of Lemma 5.4 (`deformation_retraction`); good radii `σ_ν ∈ (2^{-ν-4}, 2^{-ν-3})` for `d_a = dist(·, L_{ℓ-1}(a))` with small slices of `T` and normal truncations of `∂T` (`deformation_good_radius` and the Slicing Theorem, applied to `T` and to `∂T`); the pieces `X_ν = T ⌞ {d_a ≥ σ_ν}`, `Z'_ν = (∂T) ⌞ {d_a ≥ σ_ν}` and their increments, pushed forward by `ψ` and along the affine homotopy to the identity (`deformation_pushforward_homotopy`, whose premise is `deformation_im_pushforward_limit` applied to Lemma 3.9); the estimates (11)–(16) and the limits `Q = lim ψ_# X_ν`, `R = lim H X_ν`, `S = lim H Z'_ν` (`deformation_telescope_limit`); the homotopy formula (20) gives (21); integrality by completeness (`deformation_im_completeness`); supports via the closedness of `L_n` (`deformation_skeleton_isClosed`); and `∂Q = lim ψ_# Z'_ν`.
- **Calls**: `cmb_abs_apply_le_of_massOn_le` (A.1), `deformation_skeleton_isClosed`, `deformation_good_radius`, `deformation_telescope_limit`, `deformation_pushforward_homotopy`, `deformation_good_center`, `deformation_mass_restriction`, `deformation_im_completeness`, `deformation_im_pushforward_limit`, `deformation_retraction`
- **Called by**: `deformation_theorem`

#### `deformation_skeleton_isClosed` (L39435)

- `root.deformation-a1.onto_skeleton-a1.skeleton_closed-a1` · issue #4553 · PR #5035 · candidate `e0ddd8eced47`
- **Statement and proof**: The lattice `n`-skeleton `⋃_{F ∈ 𝓛ₙ(ρ)} F` of the cubical decomposition of `ℝ^N` of side `ρ > 0` is closed (used for `spt Q ⊆ Lₙ`, Simon Ch. 6, §5, (22), in the proof of Theorem 5.1). Each face `ρ (z + F_α)` is an intersection of closed coordinate slabs and hyperplanes; a point `y ∈ ρ (z + F_α)` has `ρ zᵢ ≤ yᵢ ≤ ρ zᵢ + ρ`, so the ball `B(x, ρ)` meets `ρ (z + F_α)` only if `xᵢ/ρ − 2 < zᵢ < xᵢ/ρ + 2` for every `i`.  With finitely many `α`, the faces form a locally finite family, and a locally finite union of closed sets is closed.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_onto_skeleton`

#### `deformation_good_radius` (L39485)

- `root.deformation-a1.onto_skeleton-a1.good_radius-a1` · issue #4561 · PR #4974 · candidate `6097b18c8c43`
- **Statement and proof**: Chebyshev choice of a good slicing radius (step 2 of the proof of the Deformation Theorem, Simon Ch. 6, 5.1, printed (10)).  If `a < b`, `g : ℝ → [0, ∞]` is measurable with `∫⁻_{(a, b)} g ≤ K` and `N` is Lebesgue-null, then some `t ∈ (a, b) \ N` has `g t ≤ 2K/(b − a)`.  With `s = 2K/(b − a)`, the set `B = {t ∈ (a, b) : s < g t}` has measure `< b − a` (it is empty if `K = ∞`, null if `K = 0`, and of measure `≤ (b − a)/2` by Markov's inequality otherwise), so `(a, b) ⊄ B ∪ N`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_onto_skeleton`

#### `deformation_telescope_limit` (L39553)

- `root.deformation-a1.onto_skeleton-a1.telescope_limit-a1` · issue #4576 · PR #5214 · candidate `a008ba30dbd5`
- **Statement and proof**: **Mass limits of currents with summable increments** (Simon Ch. 6, proof of 5.1, I.5, printed (19)).  If `A_{ν+1} = A_ν + B_ν` and `∑_ν M(B_ν) < ∞`, then `A_ν ⇀ A' = A_0 + ∑_μ B_μ`, `M(A') ≤ M(A_0) + ∑_ν M(B_ν)`, `M(A' - A_ν) ≤ ∑_μ M(B_{μ+ν})`, and `spt A' ⊆ F` for every closed `F` containing all `spt A_ν`.  Each tail `∑_μ B_{μ+ν}` is a current of mass at most `∑_μ M(B_{μ+ν})` (`fiw_ims_series_current`); telescoping gives `A_ν(ω) = A_0(ω) + ∑_{μ<ν} B_μ(ω)`, so `A' - A_ν` is the `ν`-th tail; supports pass to weak limits (`iwl_cr_support_lemmas`).
- **Calls**: `fiw_ims_series_current`, `iwl_cr_support_lemmas`
- **Called by**: `deformation_onto_skeleton`

#### `fiw_ims_series_current` (L15531)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1` · issue #1247 · PR #2977 · candidate `2065ad1fee8c`
- **Statement and proof**: Series of currents: if `∑' r, |c_r| M_W(T_r) < ∞` for every `W ⊂⊂ U`, then `∑ c_r T_r` converges unconditionally on every test form to a current `S` with `M_W(S) ≤ ∑' r, |c_r| M_W(T_r)` for every set `W`.
- **Calls**: `fiw_ims_sc_series_bound`, `fiw_ims_mass_bound`, `fiw_ims_sc_testForm_bounded`, `fiw_ims_sc_continuous_of_bound`
- **Called by**: `deformation_telescope_limit`, `fiw_im_series`

#### `fiw_ims_sc_series_bound` (L5364)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.series_bound-a1` · issue #1936 · PR #2350 · candidate `182e22ce5692`
- **Statement and proof**: **Integer-weighted series estimate** (behind the `M`-absolutely convergent integer series `∑_r c_r T_r` of currents, Simon Ch. 6, 3.13, pp. 149–150, used in the proof of 7.2).  If `ofReal |a_r| ≤ m_r · ofReal C` for every `r` and `∑' r, |c_r| m_r < ∞` in `[0, ∞]`, then `r ↦ c_r a_r` is summable and `ofReal |∑' r, c_r a_r| ≤ ofReal C · ∑' r, |c_r| m_r`. Termwise `ofReal |c_r a_r| = |c_r| · ofReal |a_r| ≤ ofReal C · (|c_r| m_r)`, so `∑' r, ofReal |c_r a_r|` is finite; this gives absolute summability, and the estimate follows from `|∑' r, x_r| ≤ ∑' r, |x_r|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_ims_series_current`

#### `fiw_ims_mass_bound` (L5399)

- `root.flat_iff_weak-a1.im_series-a1.mass_bound-a1` · issue #1245 · PR #2044 · candidate `bf9ca0af59c2`
- **Statement and proof**: Mass bound: if `η` is supported in `V` and `|η(x)| ≤ C` everywhere (Euclidean covector norm) with `C > 0`, then `|X(η)| ≤ M_V(X) · C` in `[0, ∞]`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_ims_series_current`

#### `fiw_ims_sc_testForm_bounded` (L5285)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.testform_bounded-a1` · issue #1903 · PR #2653 · candidate `e8e708e479c2`
- **Statement and proof**: **Test forms have bounded Euclidean coefficient norm**: Simon's `|ω| = sup_x √⟨ω(x), ω(x)⟩` (Ch. 6, 1.15, p. 134) is finite, with a positive bound. A test form is smooth, hence continuous, and has compact support, so `‖ω(x)‖ ≤ B` for its operator norm; `|α| ≤ √(Pⁿ) ‖α‖` (`fiw_ims_sc_covectorNorm_le_opNorm`) then gives the bound `C = √(Pⁿ) B + 1 > 0`.
- **Calls**: `fiw_ims_sc_covectorNorm_le_opNorm` (A.3)
- **Called by**: `fiw_ims_series_current`

#### `fiw_ims_sc_continuous_of_bound` (L5337)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.continuity_criterion-a1` · issue #1925 · PR #2815 · candidate `5c2485018f33`
- **Statement and proof**: **Continuity criterion on `𝒟ⁿ(U)`** (the topology of Simon Ch. 6, §1, p. 134, and the continuity required in 2.1): if for each compact `K ⊆ U` there is `A` with `|L(ω)| ≤ A·C` whenever `spt ω ⊆ K` and `|ω(x)| ≤ C` for all `x` (the Euclidean coefficient norm of 1.15), then `L(ω_q) → 0` for every null sequence `ω_q → 0` of test forms.  By `fiw_ims_sc_converges_zero_small` all `spt ω_q` lie in one compact `K ⊆ U` and `sup_x |ω_q(x)| → 0`; for `ε > 0` and `δ = ε / (|A| + 1)`, eventually `|L(ω_q)| ≤ A·δ ≤ |A|·δ < ε`.  Neither linearity of `L` nor a sign of `A` is used.
- **Calls**: `fiw_ims_sc_converges_zero_small`
- **Called by**: `fiw_ims_series_current`, `dph_lpf_current_of_bounded_functional`

#### `fiw_ims_sc_converges_zero_small` (L5304)

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.converges_small-a1` · issue #1914 · PR #2610 · candidate `49ba437cb4c7`
- **Statement and proof**: **A null sequence of test forms is uniformly small (convergence in `𝒟ⁿ(U)`, Simon Ch. 6, §1, p. 134, as used in the definition 2.1 of currents **[corrected]**).**  If `ω_q → 0` in `𝒟ⁿ(U)`, then all `ω_q` are supported in one compact `K ⊆ U` and, for every `ε > 0`, eventually `|ω_q(x)| ≤ ε` for every `x`, in the Euclidean coefficient norm of Remark 2.6.  The `k = 0` part of the convergence makes the operator norm `‖ω_q(x)‖` uniformly small on `K`, and `ω_q = 0` off `K`; `Submission.fiw_ims_sc_covectorNorm_le_opNorm` gives `|α| ≤ √(P^n) ‖α‖`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), cites "Simon Ch. 6, 2.1". 2.1 (p. 135) defines currents as continuous linear functionals; the convergence of test forms used here is defined in §1, p. 134.
- **Calls**: `fiw_ims_sc_covectorNorm_le_opNorm` (A.3)
- **Called by**: `fiw_ims_sc_continuous_of_bound`, `fiw_tb_ext_cutoff_current`

#### `iwl_cr_support_lemmas` (L12654)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1` · issue #2732 · PR #3563 · candidate `02f3305faacf`
- **Statement and proof**: Supports of boundaries, weak limits and linear combinations: `spt ∂Z ⊆ spt Z`; a weak limit of currents supported in a closed `K` is supported in `K`; `spt Z ⊆ spt Z₁ ∪ spt Z₂` when `Z = a Z₁ + b Z₂`.  In each case a point outside the claimed support lies in an open `W ⊂⊂ U` on which the current vanishes, i.e. in its zero region.
- **Calls**: `isoperimetric_apply_eq_zero_of_disjoint_support`
- **Called by**: `iwl_cr_cone_boundary`, `dph_lpf_cmp_core_estimate`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_smooth_homotopy`, `deformation_telescope_limit`, `deformation_pushforward_homotopy`, `iwl_cycle_reduction`

#### `isoperimetric_apply_eq_zero_of_disjoint_support` (L2069)

- `root.isoperimetric-a1.vanish_off_support-a1` · issue #755 · PR #1637 · candidate `3ccbe082e519`
- **Statement and proof**: A current kills every test form whose support misses `spt T`: `tsupport ω` is a compact subset of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms supported in those `W`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_mass_lt_top`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `iwl_cr_support_lemmas`, `iwl_cr_cone_boundary`, `iwl_cr_ci_ps_slice_integral_eq_zero`, `dph_iprod_exists`, `deformation_pushforward_homotopy`, `iwl_positive_density`

#### `deformation_pushforward_homotopy` (L43249)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1` · issue #4586 · PR #6816 · candidate `3e3cf51f15a3`
- **Statement and proof**: **Push-forward operators and the straight-line homotopy (Simon Ch. 6, 2.17–2.29, 3.2(2)).** Assume (S5′), the conclusion of `deformation_im_pushforward_limit`.  For every `D` there are constants `c_k = max(1, c₀(D, k))` (`c₀` the constant of the affine estimate 2.27) such that every `f : ℝ^D → ℝ^D` has operators `P_k X = f_# X` and `H_k X = h_# ([[0,1]] × X)`, the Lipschitz push-forwards characterized in `dph_lipschitz_pushforward`, where `h(t, x) = f(x) + t (x − f(x))` is the straight-line homotopy from `f` to the identity.  On currents with admissible data `(E, Λ, δ, b)` they satisfy the mass, support, integrality, tangential vanishing and linearity clauses, `∂ P = P ∂` and the homotopy formula `X − P X = ∂ H X + H ∂X` (Simon 2.25), the latter as the limit of the smooth homotopy formula for the mollified homotopies `ĥ_n(t, x) = f_n(x) + t (x − f_n(x))`.
- **Calls**: `dph_lipschitz_smooth_approx`, `dph_interval_product`, `dph_interval_product_im`, `dph_smooth_homotopy`, `dph_lipschitz_pushforward`, `dph_lipschitz_pushforward_im`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `cmb_abs_apply_le_of_massOn_le` (A.1), `iwl_sp_exists_compatible_testForm`, `iwl_cr_support_lemmas`, `iwl_cr_ci_slice_testForm`
- **Called by**: `deformation_onto_skeleton`

#### `dph_lipschitz_smooth_approx` (L5584)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1` · issue #5222 · PR #5692 · candidate `133f872db54f`
- **Statement and proof**: The smoothings `f_σ = f ∗ φ_σ` of Simon Ch. 6, 2.29 (p. 141), for the Lipschitz push-forward homotopy of the deformation theorem (§5): extend `G` from `A_δ = thickening δ A` to a Lipschitz `G'` on `ℝ^m` (McShane) and mollify it at the scales `σ_j = (δ / 8) / (j + 1)`.  The `2σ_j`-balls about points of `A_{δ/2}` stay in `A_δ`, where `G' = G` is `Λ`-Lipschitz, so `‖D(Gj j)‖ ≤ Λ` there.  Near `A`, wherever `Gj j` meets `spt ω` the normal coordinates `i ∉ range α` of `G` equal `z i` on a `2σ_j`-ball, so those of `Gj j` are locally constant, `D(Gj j)` maps into `span e_α`, and `ω` without `e_α`-component pulls back to `0`.
- **Calls**: `dph_sa_mollify_lipschitz`, `dph_sa_covector_comp_eq_zero`
- **Called by**: `dph_lipschitz_pushforward`, `dph_lipschitz_pushforward_im`, `deformation_pushforward_homotopy`

#### `dph_sa_mollify_lipschitz` (L5443)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.mollify-a1` · issue #5464 · PR #5616 · candidate `43b4eb53677f`
- **Statement and proof**: Mollifying a Lipschitz map, as for Simon's `f^{(σ)} = f ∗ φ^{(σ)}` (Ch. 6, 2.29, p. 141): for an `L`-Lipschitz `F : ℝ^m → ℝ^{m'}`, `F_σ(x) = ∫ ρ(w) F(x - w) dw`, with `ρ` the mollifier of `slicing_mb_sa_mollifier_exists` at radius `σ/2`, is smooth, `L`-Lipschitz and `Lσ`-close to `F`. If `F` is `Λ'`-Lipschitz on `B(x, 2σ)`, then `F_σ` is `Λ'`-Lipschitz on `B(x, σ)`, `‖DF_σ(x)‖ ≤ Λ'` and `|F_σ(x) - F(x)| ≤ Λ'σ`; a coordinate of `F` constant on `B(x, σ)` keeps its value at `x`.
- **Calls**: `slicing_mb_sa_mollifier_exists` (A.5)
- **Called by**: `dph_lipschitz_smooth_approx`

#### `dph_sa_covector_comp_eq_zero` (L5546)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.covector_vanish-a1` · issue #5474 · PR #5668 · candidate `9696746903a5`
- **Statement and proof**: Multilinear-algebra step of the smoothing argument in the proof of the Deformation Theorem (Simon Ch. 6, §5): a `k`-covector `γ` on `ℝ^{m'}` with `γ(e_{α(0)}, …, e_{α(k-1)}) = 0` pulls back to `0` under every linear `T` with image in `span {e_{α(q)}}`.  With `S c = ∑_q c_q e_{α(q)}` on `ℝ^k`, `T v = S ((T v)_{α(q)})_q`, and the alternating `k`-form `γ ∘ S` on `ℝ^k` vanishes because its value on the standard basis is `γ(e_{α(0)}, …, e_{α(k-1)}) = 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lipschitz_smooth_approx`

#### `dph_interval_product` (L35897)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1` · issue #5233 · PR #6469 · candidate `f0b9e8a43281`
- **Statement and proof**: Simon Ch. 6, 2.17–2.22 (pp. 138–139): the product `[[0,1]] × X` of a finite-mass current `X ∈ 𝒟ₖ(ℝ^m)`, `([[0,1]] × X)(η) = ∫₀¹ X(φ_s) ds`, where `φ_s(x) = η(s, x)(e₀, ι ·)` is the `dt`-slice of `η` at time `s` (`e₀ = (1, 0)`, `ι w = (0, w)`).  (I) It exists and is the unique current with this formula, `M([[0,1]] × X) ≤ M(X)`, `spt([[0,1]] × X) ⊆ [0,1] × spt X`, the integrand `s ↦ X(φ_s)` is continuous on `[0,1]`, and `[[0,1]] × X` is normal when `X` is. (II), (III) Every current `Z` with this formula satisfies the boundary formula `∂Z = {1} × X − {0} × X − [[0,1]] × ∂X` (without the last term for `0`-currents).
- **Calls**: `dph_iprod_boundary`, `dph_iprod_exists`, `dph_iprod_slice_continuity`
- **Called by**: `dph_smooth_homotopy`, `dph_lipschitz_pushforward`, `deformation_pushforward_homotopy`

#### `dph_iprod_boundary` (L35517)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.product_boundary-a1` · issue #5709 · PR #6456 · candidate `38c8c13b65d2`
- **Statement and proof**: Boundary of a current `Z` with the product characterization `ProdChar(X, Z)` of `[[0,1]] × X`: `Z(η) = ∫₀¹ X(φ(s)) ds` whenever `φ(s)(x)(v) = η((s, x))(e₀, ι ∘ v)` on `[0,1]`. With `ψᵢ(x)(v) = ψ((i, x))(ι ∘ v)` and `φ(s)(x)(v) = ψ((s, x))(e₀, ι ∘ v)`: (II) `∂Z(ψ) = X(ψ₁) − X(ψ₀)` in degree `0`; (III) `∂Z(ψ) = X(ψ₁) − X(ψ₀) − ∫₀¹ ∂X(φ(s)) ds` in positive degree; (N) `M(∂Z) ≤ 2 M(X) + M(∂X) < ∞` (no `M(∂X)` term in degree `0`).
- **Calls**: `iwl_cr_ci_slice_testForm`, `dph_iprod_horizontal_slices`, `dph_iprod_slice_continuity`, `dph_iprod_slice_extDeriv`, `dph_iprod_horizontal_ftc`
- **Called by**: `dph_interval_product`

#### `iwl_cr_ci_slice_testForm` (L12943)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.slice_forms-a1` · issue #3624 · PR #4323 · candidate `143edefdefb7`
- **Statement and proof**: Slices of a test form `η` on `ℝ^{P+1} = ℝ × ℝ^P` across the first coordinate: with `e₀ = (1, 0)` and `ι w = (0, w)`, the form `φ s x = η(s, x)(e₀, ι ·)` is the continuous linear contraction `α ↦ α(e₀, ι ·)` applied to `η` along the affine map `x ↦ (s, x) = s • e₀ + ι x`, hence smooth; it vanishes off the preimage of `tsupport η`, which is compact as `‖x‖ ≤ ‖(s, x)‖`; and it depends jointly continuously on `(s, x)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ci_product_support`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_sh_affine_estimate`, `dph_iprod_exists`, `dph_iprod_boundary`, `dph_smooth_homotopy`, `dph_interval_product_im`, `iwl_cr_cone_integer_multiplicity`, `deformation_pushforward_homotopy`

#### `dph_iprod_horizontal_slices` (L32767)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_slices-a1` · issue #5655 · PR #5935 · candidate `e246cb949718`
- **Statement and proof**: Horizontal slices for the product `[[0,1]] × X`: for `ψ ∈ 𝒟^q(ℝ^{m+1})` and `s ∈ ℝ`, the pull-backs `j_s^# ψ` and `j_s^# ∂_s ψ` along `j_s(x) = (s, x)`, i.e. `x ↦ ψ(s, x)(ι ·)` and `x ↦ Dψ(s, x)(e₀)(ι ·)` with `ι v = (0, v)`, are test forms in `𝒟^q(ℝ^m)`.
- **Calls**: `iwl_sp_exists_compatible_testForm`
- **Called by**: `dph_iprod_boundary`

#### `iwl_sp_exists_compatible_testForm` (L28631)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.compatible_form-a1` · issue #2493 · PR #3415 · candidate `fd5f1e29719e`
- **Statement and proof**: Simon Ch. 6, 2.23 (p. 139), cut-off construction: if `f` is `C^∞` and proper on `A ⊆ U`, every `ω ∈ 𝒟ʲ(V)` has a pull-back `η = ζ f^#ω ∈ 𝒟ʲ(U)` with `0 ≤ ζ ≤ 1`, `η = f^#ω` on an open `N ⊇ A`, and `spt η ⊆ f⁻¹(spt ω)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lpf_cmp_core_estimate`, `dph_iprod_horizontal_slices`, `dph_lpfex_bounded_compatible_form`, `dph_lpf_boundary`, `dph_lpf_linearity`, `dph_sh_slice_compatible_testForm`, `dph_sh_affine_estimate`, `dph_smooth_homotopy`, `dph_lipschitz_pushforward_im`, `deformation_pushforward_homotopy`, `ind_pi_projected_limit`, `iwl_sp_massOn_le_of_compatible`

#### `dph_iprod_slice_continuity` (L34678)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_continuity-a1` · issue #5679 · PR #6090 · candidate `13ffabe42267`
- **Statement and proof**: **Continuity along slices** (step 3 of the interval product).  Let `X` be a current in `ℝ^m` with `M(X) < ∞`; write `(s, x) ∈ ℝ^{m+1}` for `Fin.cons s x`, `ι(w) = (0, w)`, `e₀ = (1, 0)`. (D1) If `X ∈ 𝒟_k`, `η ∈ 𝒟^{k+1}(ℝ^{m+1})` and `φ(s)(x)(v) = η(s, x)(e₀, ι ∘ v)` for `s ∈ [0, 1]`, then `s ↦ X(φ(s))` is continuous on `[0, 1]` and `|X(φ(s))| ≤ M(X) · sup |η|`. (D2) If `X ∈ 𝒟_q`, `ω` is a continuous compactly supported `q`-form on `ℝ^{m+1}` and `Ψ(s)(x)(v) = ω(s, x)(ι ∘ v)` for all `s`, then `s ↦ X(Ψ(s))` is continuous and `|X(Ψ(s))| ≤ M(X) · sup |ω|`.  By the mass bound, `X` is `M(X)`-Lipschitz for the sup of the Euclidean covector norm; slices are bounded by the sliced covector (`dph_iprod_slice_covector_norm_le`), and `η`, `ω` are uniformly continuous.
- **Calls**: `dph_iprod_slice_covector_norm_le`, `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `dph_iprod_horizontal_ftc`, `dph_iprod_exists`, `dph_iprod_boundary`, `dph_interval_product`

#### `dph_iprod_slice_covector_norm_le` (L32880)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_norm-a1` · issue #5642 · PR #5984 · candidate `6c5fc81ba5e7`
- **Statement and proof**: Euclidean coefficient norms `|γ| = covectorEuclideanNorm γ` of slices of covectors, with `ι(v) = (0, v) ∈ ℝ^{m+1}` and `e₀ = EuclideanSpace.single 0 1`: (C1) if `γ'(v) = γ(e₀, ι ∘ v)` then `|γ'| ≤ |γ|`; (C2) if `γ'(v) = γ(ι ∘ v)` then `|γ'| ≤ |γ|`; (C3) `|α| ≤ √(P^n) · ‖α‖`. For (C1) and (C2), `e₀ = b_0` and `ι(b_j) = b_{j+1}` for the standard bases `b`, so the coefficients of `γ'` are coefficients of `γ` on distinct strictly increasing multi-indices; for (C3), each of the `P^n` coefficients `α(b_{I(0)}, …, b_{I(n-1)})` is at most `‖α‖ · ∏ ‖b_{I(i)}‖ = ‖α‖`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_iprod_current_of_bound`, `dph_iprod_slice_continuity`, `dph_iprod_horizontal_ftc`

#### `dph_iprod_slice_extDeriv` (L34789)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.slice_ext_deriv-a1` · issue #5688 · PR #5889 · candidate `705d3ebd6a11`
- **Statement and proof**: The `dt`-slice of `dψ` (`e₀ = EuclideanSpace.single 0 1`, `ι(w) = (0, w)`, `(s, x)` the point of `ℝ^{m+1}` with first coordinate `s`): for a `0`-form `ψ`, `dψ(y)(e₀) = Dψ(y)(e₀)`; for a `(j+1)`-form `ψ` whose slice at `s` is `φ(x)(w) = ψ(s, x)(e₀, ι ∘ w)`, `dψ(s, x)(e₀, ι ∘ v) = Dψ(s, x)(e₀)(ι ∘ v) − dφ(x)(v)`. Both exterior derivatives are alternating sums of directional derivatives; by the chain rule along `x ↦ (s, x)` (derivative `ι`), the `l`-th term of `dφ(x)(v)` is the `(l+1)`-st term of `dψ(s, x)(e₀, ι ∘ v)` with the opposite sign, and the `0`-th term is `Dψ(s, x)(e₀)(ι ∘ v)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_iprod_boundary`

#### `dph_iprod_horizontal_ftc` (L34922)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.horizontal_ftc-a1` · issue #5690 · PR #6388 · candidate `1f0b2a6d3435`
- **Statement and proof**: Fundamental theorem of calculus along horizontal slices: for `M(X) < ∞`, the slices `Ψ(s) = ψ(s, ·)` and `Ψ'(s) = ∂ₛψ(s, ·)` of `ψ ∈ 𝒟^q(ℝ^{m+1})` (tested on horizontal vectors) satisfy `d/ds X(Ψ(s)) = X(Ψ'(s))`, with `s ↦ X(Ψ'(s))` continuous and `∫₀¹ X(Ψ'(s)) ds = X(Ψ(1)) - X(Ψ(0))`.
- **Calls**: `cmb_abs_apply_le_of_massOn_le` (A.1), `dph_iprod_slice_covector_norm_le`, `dph_iprod_slice_continuity`
- **Called by**: `dph_iprod_boundary`

#### `dph_iprod_exists` (L35345)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.product_exists-a1` · issue #5698 · PR #6385 · candidate `1f6181bacc73`
- **Statement and proof**: The product `[[0, 1]] × X` of a finite-mass current `X` on `ℝ^m`: with chosen `dt`-slices `φ^η s x = η(s, x)(e₀, ι ·)`, the functional `η ↦ ∫₀¹ X(φ^η s) ds` is linear and bounded by `M(X) · sup |η|`, hence a current `Z` with `M(Z) ≤ M(X)`; the integral does not depend on the slice family, which gives the characterization and uniqueness; and `Z` vanishes on every ball missing the closed cylinder `[0, 1] × spt X`, since there every slice `φ^η s` misses `spt X`.
- **Calls**: `iwl_cr_ci_slice_testForm`, `isoperimetric_apply_eq_zero_of_disjoint_support`, `dph_iprod_current_of_bound`, `dph_iprod_slice_continuity`
- **Called by**: `dph_interval_product`

#### `dph_iprod_current_of_bound` (L33788)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product-a1.current_criterion-a1` · issue #5667 · PR #6095 · candidate `51d9121840c6`
- **Statement and proof**: A linear functional `T₀` on `𝒟^q(U)` with `|T₀(ω)| ≤ B · sup_x |ω(x)|` (Euclidean coefficient norm) for some `B ≥ 0` **[corrected]** is a current of mass at most `B`: test-form convergence makes `sup_x |ω_j(x)| → 0`, since `|α| ≤ √(P^q) ‖α‖` (conjunct (C3) of `Submission.dph_iprod_slice_covector_norm_le`), and every mass-admissible `ω` has `T(ω) ≤ |T₀(ω)| ≤ B`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not say `B ≥ 0`, which the Lean statement (line 33788) assumes; the conclusion "mass at most `B`" needs it when `𝒟^q(U) = {0}`.
- **Calls**: `dph_iprod_slice_covector_norm_le`
- **Called by**: `dph_iprod_exists`

#### `dph_interval_product_im` (L36406)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.interval_product_im-a1` · issue #5242 · PR #5573 · candidate `266616dc3d88`
- **Statement and proof**: **Products with `[[0,1]]` of integer multiplicity currents are integer multiplicity (Simon Ch. 6, 3.2(2)).**  By `iwl_cr_interval_product_im` there is an integer multiplicity `Z' = τ(M̃, θ̃, ξ̃)` with the same product characterization `Z'(η) = ∫₀¹ X(φ(s)) ds`.  For a test form `η`, `iwl_cr_ci_slice_testForm` gives a `dt`-slice family `φ` of `η` on all of `ℝ`, so both characterizations apply and `Z(η) = ∫₀¹ X(φ(s)) ds = Z'(η)`.  Hence `Z = τ(M̃, θ̃, ξ̃)` on every test form, and the triple of `Z'` shows that `Z` is integer multiplicity.
- **Calls**: `iwl_cr_interval_product_im`, `iwl_cr_ci_slice_testForm`
- **Called by**: `deformation_pushforward_homotopy`

#### `iwl_cr_interval_product_im` (L28376)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1` · issue #2777 · PR #5237 · candidate `55f78c3b410c`
- **Statement and proof**: **The product `[[(0,1)]] × X` of an integer multiplicity current (Simon Ch. 6, 3.2(2)).** Write `Φ(s, x) = (s, x)`, `π(Φ(s, x)) = x`, `e₀ = Φ(1, 0)` and `X = τ(M, θ, ξ)` with `θ ∈ ℕ` on `M`, so `θ ≥ 1` on `M`.  The product formula for Hausdorff measure (Federer 3.2.23), in the measure form `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)`, makes `((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` a rectifiable triple; `Z := τ((0,1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a current (integrable, sequentially continuous), integer multiplicity since `θ ∘ π ∈ ℕ`, and Fubini gives `Z(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds = ∫₀¹ X(φ(s)) ds`.
- **Calls**: `iwl_cr_ip_restrict_preimage_eq_map`, `iwl_cr_hausdorff_product_formula`, `iwl_cr_ip_product_triple`, `br_loc_tauAction_current`, `ltg_tau_integrable` (A.5), `iwl_cr_ip_slice_formula`
- **Called by**: `dph_interval_product_im`, `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ip_restrict_preimage_eq_map` (L5695)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.measure_identity-a1` · issue #3637 · PR #4381 · candidate `6424bb62b377`
- **Statement and proof**: **Product formula in measure form (Federer 3.2.23; Simon Ch. 6, 3.2(2)).**  Write `π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`.  If `Hᵐ(A ∩ K) < ∞` for every compact `K ⊆ ℝ^P` and `∫⁻_{π⁻¹(A)} g dH^{m+1} = ∫⁻_ℝ ∫⁻_A g(Φ(s, x)) dHᵐ(x) ds` for every Borel `g ≥ 0`, then `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ × Hᵐ⌞A)`.  Testing the formula with `g = 1_B` gives `(H^{m+1}⌞π⁻¹(A))(B) = ∫⁻_ℝ (Hᵐ⌞A){x : Φ(s, x) ∈ B} ds = (L¹ × Hᵐ⌞A)(Φ⁻¹(B))` for Borel `B`; `Hᵐ⌞A` is finite on compact sets, hence σ-finite, so the product measure is given by sections.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_interval_product_im`

#### `iwl_cr_hausdorff_product_formula` (L28269)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1` · issue #2764 · PR #4879 · candidate `0bfba9891418`
- **Statement and proof**: Product formula for Hausdorff measure on rectifiable sets (Federer 3.2.23), with `π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`, so `{y : π y ∈ S} = Φ(ℝ × S)`: (a) if `Hᵐ(N) = 0` then `Hᵐ⁺¹(ℝ × N) = 0`; (b) if `A ⊆ ℝ^P` is `Hᵐ`-measurable and countably `m`-rectifiable, then `∫_{ℝ × A} g dHᵐ⁺¹ = ∫_ℝ ∫_A g(Φ(s, x)) dHᵐ(x) ds` for Borel `g ≥ 0`, i.e. `Hᵐ⁺¹ ⌞ (ℝ × A) = L¹ ⊗ Hᵐ ⌞ A`.  (a) is `iwl_cr_hp_cylinder_null`.  For (b), `A` is replaced by a Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`, which by (a) changes neither side.  Up to an `Hᵐ`-null set, `A₀` is the disjoint union of the Borel pieces `G p '' B p` with `G p` Lipschitz and injective on `B p` (`iwl_cr_hp_injective_pieces`); the formula holds on each piece (`iwl_cr_hp_piece_product`), and both sides are countably additive over the pieces, the cylinder over the remainder being `Hᵐ⁺¹`-null by (a).  The local finiteness of `Hᵐ ⌞ A` is not needed.
- **Calls**: `iwl_cr_hp_cylinder_null`, `iwl_cr_hp_injective_pieces`, `iwl_cr_hp_piece_product`
- **Called by**: `iwl_cr_interval_product_im`

#### `iwl_cr_hp_cylinder_null` (L26829)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.cylinder_null-a1` · issue #3756 · PR #4465 · candidate `52fc2ee0c0a4`
- **Statement and proof**: Cylinders over `Hᵐ`-null sets are `Hᵐ⁺¹`-null: if `N ⊆ ℝ^P` has `μHE[m] N = 0`, then the cylinder `{y ∈ ℝ^{P+1} | π y ∈ N} = ℝ × N`, `π y = (y₁, …, y_P)`, has `μHE[m + 1]`-measure zero. For `m = 0` the set `N` is empty.  For `m ≥ 1`, each strip `{y | π y ∈ N, a ≤ y₀ ≤ a + 1}` (`a ∈ ℤ`) is covered by the boxes `{y | π y ∈ C i, a + j dᵢ ≤ y₀ ≤ a + (j + 1) dᵢ}`, `j ≤ ⌊1 / dᵢ⌋₊`, where the `C i` cover `N` with `∑ ediam (C i) ^ m` small and `dᵢ ≥ ediam (C i)` is slightly inflated.  The boxes have diameter `≤ 2 dᵢ`, so the sum of `ediam ^ (m + 1)` over them is at most `2 ^ (m + 2) ∑ dᵢ ^ m`, which is arbitrarily small.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_hausdorff_product_formula`, `dph_hausdorff_product_formula` (A.13, unused)

#### `iwl_cr_hp_injective_pieces` (L27106)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1` · issue #3758 · PR #4437 · candidate `d4b1082b0720`
- **Statement and proof** (no doc comment in the source; summary of the Lean proof **[corrected]**): **Disjoint injective Lipschitz pieces of a Borel countably `m`-rectifiable set.** If `A ⊆ ℝ^P` is Borel and countably `m`-rectifiable, there are Lipschitz `G_p : ℝᵐ → ℝ^P` and Borel `B_p ⊆ ℝᵐ` such that `G_p` is injective on `B_p` and differentiable at every point of `B_p`, the images `G_p(B_p) ⊆ A` are Borel and pairwise disjoint, and `Hᵐ(A ∖ ⋃_p G_p(B_p)) = 0`. Proof: Lipschitz maps `F_j` cover `A` up to an `Hᵐ`-null set; the set of points where `F_j` is differentiable with injective derivative is partitioned into Borel pieces on which `F_j` is close to an injective linear map, hence injective (Mathlib's `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`); the images of the remaining points are `Hᵐ`-null: the non-differentiability points by Rademacher's theorem (Mathlib's `LipschitzWith.ae_differentiableAt`) and the bound on `Hᵐ` of Lipschitz images, and the critical points by a compression estimate `Hᵐ(f(S)) ≤ (‖Λ‖ + s)ᵐ s Lᵐ(S)` on pieces where `f` is `s²`-close to a non-injective linear `Λ`, with `s → 0`; images of Borel sets under maps continuous and injective on them are Borel (Lusin–Souslin); finally the pieces are disjointified.
- **Correction**: the previous revision of this file labelled this summary as a summary of the accepted natural-language proof. It summarizes the Lean proof (steps 1–8, lines 27106–27415), which shows that critical images are `Hᵐ`-null by the compression estimate; the accepted natural-language proof (step 5, with its key step 4) cites SimonGMT's `area_image_compl_regularSet_eq_zero` for this.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_hausdorff_product_formula`, `dph_hausdorff_product_formula` (A.13, unused)

#### `iwl_cr_hp_piece_product` (L27515)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.piece_product-a1` · issue #3768 · PR #4752 · candidate `bcc07a06ddc2`
- **Statement and proof**: Product formula `Hᵐ⁺¹ ⌞ (ℝ × G(B)) = L¹ ⊗ Hᵐ ⌞ G(B)` for one injective Lipschitz piece `G : ℝᵐ → ℝ^P` on a Borel set `B`, with `Φ(s, x) = (s, x)` and `π(s, x) = x`: for Borel `g ≥ 0`, `φ(s) = ∫_{G(B)} g(Φ(s, x)) dHᵐ(x)` is measurable and `∫_{π⁻¹(G(B))} g dHᵐ⁺¹ = ∫_ℝ φ(s) ds`. Both sides come from the injective area formula `∫_{f(S)} u dHᵏ = ∫_S J(Df) · u ∘ f` (proved inline: partition `S` into pieces where `f` is almost linear, compare with the linear area formula `Hᵏ(L E) = J(L) |E|`, `J(L) = √det ⟨L eᵢ, L eⱼ⟩`, and let the error go to `0`): in dimension `m` for `G` on `B`, and in dimension `m + 1` for the lift `G̃(v) = Φ(v₀, G(v₁, …, v_m))` on `ℝ × B`, whose Jacobian equals that of `G` (`iwl_cr_hp_lift_gram_det`); Tonelli in `v = (v₀, (v₁, …, v_m))` finishes.
- **Calls**: `iwl_cr_hp_lift_gram_det`
- **Called by**: `iwl_cr_hausdorff_product_formula`, `dph_hausdorff_product_formula` (A.13, unused)

#### `iwl_cr_hp_lift_gram_det` (L27422)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.lift_gram_det-a1` · issue #3765 · PR #4429 · candidate `f70b285845da`
- **Statement and proof**: Gram determinant of the cylinder lift `G̃(v) = (v₀, G(v₁, …, v_m))` (the Jacobian step of the Hausdorff product formula).  With `Λ(s, x) = (s, x)`, `pr₀ v = v₀` and `tl v = (v₁, …, v_m)`, the chain rule gives `DG̃(w) = Λ ∘ (pr₀, DG(b) ∘ tl)`; as `⟨Λ(s, x), Λ(s', x')⟩ = s s' + ⟨x, x'⟩`, the Gram matrix of `DG̃(w)` on the standard basis is `diag(1, Gram(DG(b)))`, and Laplace expansion along row `0` gives `det Gram(DG̃(w)) = det Gram(DG(b))`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_hp_piece_product`

#### `iwl_cr_ip_product_triple` (L26535)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1` · issue #3649 · PR #5197 · candidate `65a29dad072e`
- **Statement and proof**: **The product triple `(0, 1) × (M, θ, ξ)` (Simon Ch. 6, 3.2(2)).**  Write `Φ(s, x) = (s, x)`, `π(y) = (y₁, …, y_P)`, `e₀ = (1, 0)` and `ι(v) = Φ(0, v)`, and assume the product formula (MP) `H^{m+1}⌞{π ∈ A} = Φ_*(L¹ ⊗ Hᵐ⌞A)` for every `Hᵐ`-measurable countably `m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact `K`.  If `(M, θ, ξ)` is a rectifiable `m`-triple in `ℝ^P` with `θ ≥ 1` on `M`, then `((0, 1) × M, θ ∘ π, e₀ ∧ ξ ∘ π)` is a rectifiable `(m + 1)`-triple in `ℝ^{P+1}`; here `e₀ ∧ ξ ∘ π` is characterized by `⟨α, ξ′(Φ(s, x))⟩ = ⟨β, ξ(x)⟩` whenever `β(v) = α(e₀, ιv₁, …, ιvₘ)`.
- **Calls**: `iwl_cr_ip_pt_cylinder_nullMeasurableSet`, `iwl_cr_ip_pt_cylinder_countablyRectifiable`, `iwl_cr_ip_pt_slab_transfer`, `iwl_cr_ip_product_weighted_tangent`, `iwl_cr_ip_pt_frame_orthonormal`
- **Called by**: `iwl_cr_interval_product_im`

#### `iwl_cr_ip_pt_cylinder_nullMeasurableSet` (L5944)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.cylinder_null_measurable-a1` · issue #4394 · PR #4911 · candidate `ecdea5cf8fdc`
- **Statement and proof**: Cylinders over null-measurable sets: let `π(y) = (y_1, …, y_P)` for `y ∈ ℝ^{P+1}`.  If `π⁻¹(N)` is `H^{m+1}`-null for every `Hᵐ`-null `N ⊆ ℝ^P`, then `π⁻¹(M)` is `H^{m+1}`-null-measurable for every `Hᵐ`-null-measurable `M ⊆ ℝ^P`.  `π` is continuous, hence Borel, and the hypothesis makes it quasi-measure-preserving from `H^{m+1}` to `Hᵐ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_product_triple`

#### `iwl_cr_ip_pt_cylinder_countablyRectifiable` (L5972)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.cylinder_rectifiable-a1` · issue #4404 · PR #4856 · candidate `29efe5550b5b`
- **Statement and proof**: Cylinders over countably `m`-rectifiable sets: if `π(y) = (y_1, …, y_P)` pulls `Hᵐ`-null sets of `ℝ^P` back to `H^{m+1}`-null sets of `ℝ^{P+1}`, then for countably `m`-rectifiable `M ⊆ ℝ^P` the cylinder `{y : π(y) ∈ M}` is countably `(m+1)`-rectifiable, parametrized by `G_j(u) = (u_0, F_j(u_1, …, u_m))`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_product_triple`

#### `iwl_cr_ip_pt_slab_transfer` (L5788)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.slab_transfer-a1` · issue #4385 · PR #4903 · candidate `c3e8cccfe06c`
- **Statement and proof**: Integrability and a.e. strong measurability pass from `A ⊆ ℝ^P` to the slab `S_A = {y | π y ∈ A ∧ y₀ ∈ (0, 1)}`, `π y = (y₁, …, y_P)`.  By `slab_restrict_eq_map`, `H^{m+1} ⌞ S_A = Φ'_# ((L¹ ⌞ (0, 1)) ⊗ (Hᵐ ⌞ A))` for `Φ'(s, x) = (s, x₁, …, x_P)`, a homeomorphism (hence a measurable embedding) with `π ∘ Φ' = Prod.snd`.  So (a) is integrability of `f ∘ Prod.snd` for the product of the finite measure `L¹ ⌞ (0, 1)` with `Hᵐ ⌞ A`, and (b) is a.e. strong measurability of `g ∘ Prod.snd`, `Prod.snd` being quasi-measure-preserving onto `Hᵐ ⌞ A`.
- **Calls**: `iwl_cr_ip_pt_slab_restrict_eq_map`
- **Called by**: `iwl_cr_ip_product_triple`

#### `iwl_cr_ip_pt_slab_restrict_eq_map` (L5725)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.slab_measure-a1` · issue #4380 · PR #4869 · candidate `fddc02f51371`
- **Statement and proof**: Measure identity on the slab over `A` (fact (D2) in the proof of the product triple): for `Φ(s, x) = (s, x₁, …, x_P)` and `π(y) = (y₁, …, y_P)`, the cylinder identity `Hᵐ⁺¹ ⌞ {π ∈ A} = Φ_#(L¹ × Hᵐ ⌞ A)` restricts to the slab `{π ∈ A, 0 < y₀ < 1}`.  Restricting both sides to the Borel set `{0 < y₀ < 1}`, whose `Φ`-preimage is `(0, 1) × ℝ^P`, gives `Φ_#((L¹ ⌞ (0, 1)) × Hᵐ ⌞ A)`; `Hᵐ ⌞ A` is finite on compact sets, hence s-finite.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_pt_slab_transfer`

#### `iwl_cr_ip_product_weighted_tangent` (L26428)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1` · issue #3643 · PR #5113 · candidate `76601b1d3ec9`
- **Statement and proof**: Simon Ch. 3, 1.7 for the product of the unit interval with `(M, θ)`: if `span τ` is a weighted approximate tangent space of `(M, θ)` at `x`, then `span (e₀, ιτ)` is one of `(M̃, θ ∘ π)`, `M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}`, at `Φ(s₀, x)` for `0 < s₀ < 1`. By the slice identity the blow-up integrals at `Φ(s₀, x)` are `∫_ℝ 1_{(-s₀/r, (1-s₀)/r]}(σ) a_r(σ) dσ`, where `a_r(σ)` is the blow-up integral of `(M, θ)` at `x` against `f(Φ(σ, ·))`.  Dominated convergence in `σ` (uniform blow-up mass bound, continuity in `σ`) and Fubini on the plane `π⁻¹(span τ) = span (e₀, ιτ)` give the limit `θ(x) ∫_{span (e₀, ιτ)} f dH^{m+1}`.
- **Calls**: `iwl_cr_ip_wt_product_plane`, `iwl_cr_ip_wt_plane_fubini`, `iwl_cr_ip_wt_blowup_mass_bound`, `iwl_cr_ip_wt_slice_identity`, `iwl_cr_ip_wt_slice_continuous`
- **Called by**: `iwl_cr_ip_product_triple`

#### `iwl_cr_ip_wt_product_plane` (L6077)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_plane-a1` · issue #4515 · PR #4975 · candidate `024164877fb4`
- **Statement and proof**: The product frame of `(0, 1) × M` (Simon Ch. 6, Remark 3.2(2), for `[[(0, 1)]] × τ(M, θ, ξ)`). Write `ℝ^{P+1} = ℝ × ℝ^P` with `Φ(s, u) = (s, u₁, …, u_P)` and `π(z) = (z₁, …, z_P)`.  If `τ` is an orthonormal family in `ℝ^P`, then `τ̃ = (e₀, Φ(0, τ₁), …, Φ(0, τ_m))` is orthonormal, its span `Q` has dimension `m + 1`, and `Q = π⁻¹(span τ)` as sets.  In coordinates `⟨Φ(a, u), Φ(b, w)⟩ = ab + ⟨u, w⟩` and `e₀ = Φ(1, 0)`; the generators of `Q` project into `span τ`, and conversely `z = z₀ e₀ + ∑ᵢ cᵢ Φ(0, τᵢ)` whenever `π z = ∑ᵢ cᵢ τᵢ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_product_weighted_tangent`

#### `iwl_cr_ip_wt_plane_fubini` (L25891)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.plane_fubini-a1` · issue #4521 · PR #5025 · candidate `0aea135f9e9c`
- **Statement and proof**: Fubini on the product plane `π⁻¹(T)`, `T = span τ`, for compactly supported continuous `f` (Simon Ch. 6, 3.2(2), product with an interval).  Write `Φ′(s, u) = (s, u) ∈ ℝ^{P+1}` and `π(y) = (y₁, …, y_P)`, and assume the product formula (MP) `H^{m+1} ⌞ π⁻¹(A) = Φ′_#(L¹ × Hᵐ ⌞ A)` for every `Hᵐ`-measurable, countably `m`-rectifiable, locally `Hᵐ`-finite `A ⊆ ℝ^P`.  Then for an orthonormal `τ`, `∫_{π⁻¹(T)} f dH^{m+1} = ∫_ℝ ∫_T f(Φ′(σ, w)) dHᵐ(w) dσ`. `T` is closed, has dimension `m`, is the range of the Lipschitz map `u ↦ ∑ uᵢ τᵢ`, and `Hᵐ ⌞ T` is regular, so (MP) applies to `A = T`.  Change variables along the homeomorphism `Φ′ : ℝ × ℝ^P ≃ ℝ^{P+1}` and apply Fubini to the compactly supported continuous `f ∘ Φ′`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_product_weighted_tangent`

#### `iwl_cr_ip_wt_blowup_mass_bound` (L26056)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.blowup_mass_bound-a1` · issue #4542 · PR #4969 · candidate `639092d37fab`
- **Statement and proof**: Uniform mass bound for the blow-ups `η_r(M)`, `η_r = η_{x,r}` (Ch. 3, §1, p. 71), at a point `x` with a weighted approximate tangent plane `T` (Ch. 3, 1.7), as used for the product with an interval (Ch. 6, 3.2(2)): for every `R` there is `B` such that for all small `r > 0`, every `g` with `|g| ≤ C` vanishing off `B̄(0, R)` satisfies `|∫_{η_r(M)} g(w) θ(x + r w) dHᵐ(w)| ≤ C B`.  Compare with the cut-off `g₀ = max(0, min(1, R + 1 − ‖w‖)) ∈ C_c`: `|g| ≤ C g₀`, `θ ≥ 0` on `M`, and by the change of variables `fiw_tl_blowup_setIntegral` the `g₀`-integral tends to `θ(x) ∫_T g₀ dHᵐ < B`.
- **Calls**: `fiw_tl_blowup_setIntegral`
- **Called by**: `iwl_cr_ip_product_weighted_tangent`

#### `fiw_tl_blowup_setIntegral` (L26010)

- `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1` · issue #2157 · PR #2950 · candidate `91a22d1bfc90`
- **Statement and proof**: Change of variables under Simon's blow-up `η = η_{x,r}`, `η(z) = r⁻¹(z − x)` (Ch. 3, §1, p. 71), as used for the locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)): for `r > 0`, every set `S` and every real function `g`, `∫_{η(S)} g dHⁿ = r⁻ⁿ ∫_S g ∘ η dHⁿ`. `η` is a homeomorphism (inverse `w ↦ x + r w`) and `η⁻¹(F) = x + r F`, so `Hⁿ(η⁻¹ F) = rⁿ Hⁿ(F)` by translation invariance and `n`-homogeneity of `Hⁿ`.  Hence `η_# Hⁿ = rⁿ Hⁿ`, and the change of variables along the measurable embedding `η` needs no integrability.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_wt_blowup_mass_bound`, `iwl_cr_ip_wt_slice_identity`, `iwl_cr_ip_wt_slice_continuous`, `fiw_tl_growth_bound`, `fiw_tl_transfer`

#### `iwl_cr_ip_wt_slice_identity` (L26166)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_identity-a1` · issue #4556 · PR #5082 · candidate `2a4a92124eab`
- **Statement and proof**: Blow-ups of the product `(0, 1) × M ⊆ ℝ^{P+1}` slice into blow-ups of `M` (Simon Ch. 6, 3.2(2)). With `Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)`, `y* = Φ(s₀, x)` and `r > 0`, and assuming the product formula `H^{m+1}⌞π⁻¹(A) = Φ_#(L¹ ⊗ Hᵐ⌞A)` for countably `m`-rectifiable `A`: `∫_{η_{y*,r}((0,1) × M)} f(z) θ(π(y* + r z)) dH^{m+1}(z) = ∫_{(−s₀/r, (1−s₀)/r]} ∫_{η_{x,r}(M)} f(Φ(σ, w)) θ(x + r w) dHᵐ(w) dσ`. Undo both blow-ups (`fiw_tl_blowup_setIntegral`), pass to `(L¹⌞(0,1)) ⊗ Hᵐ⌞M` (`iwl_cr_ip_wt_product_measure`), apply Fubini and substitute `s = s₀ + r σ`.
- **Calls**: `fiw_tl_blowup_setIntegral`, `iwl_cr_ip_wt_product_measure`
- **Called by**: `iwl_cr_ip_product_weighted_tangent`

#### `iwl_cr_ip_wt_product_measure` (L25968)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_measure-a1` · issue #4529 · PR #5047 · candidate `9e7ae814dd79`
- **Statement and proof**: Simon Ch. 6, 3.2(2) (product with an interval), Hausdorff measure on `(0,1) × M`.  Write `Φ(s, u) = (s, u)`, `π(y) = (y₁, …, y_P)` and assume `(MP)`: `H^{m+1} ⌞ π⁻¹(A) = Φ_# (L¹ ⊗ Hᵐ ⌞ A)` for every `Hᵐ`-measurable, countably `m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for compact `K`.  Then every such `M` has `H^{m+1} ⌞ {π(y) ∈ M, y₀ ∈ (0,1)} = Φ_# ((L¹ ⌞ (0,1)) ⊗ Hᵐ ⌞ M)`: restrict `(MP)` for `A = M` to the open slab `O = {y₀ ∈ (0,1)}`, use `Φ⁻¹(O) = (0,1) × ℝ^P`, and split the restricted product, `Hᵐ ⌞ M` being finite on compact sets, hence σ-finite.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_wt_slice_identity`

#### `iwl_cr_ip_wt_slice_continuous` (L26346)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_continuous-a1` · issue #4572 · PR #4944 · candidate `ffd57024c4c6`
- **Statement and proof**: Continuity in `σ` of the blown-up slice integrals (Simon Ch. 6, 3.2(2), product with an interval): if `θ` is `Hᵐ`-integrable on `M ∩ K` for every compact `K`, `f ∈ C_c(ℝ^{P+1})` and `r > 0`, then `σ ↦ ∫_{η(M)} f(σ, w) θ(x + r w) dHᵐ(w)` is continuous, `η = η_{x,r}`.  Undoing the blow-up (`fiw_tl_blowup_setIntegral`) gives `r⁻ᵐ ∫_M f(σ, η u) θ(u) dHᵐ(u)`, continuous by dominated convergence with the `σ`-independent bound `sup |f| · |θ| · 1_{B̄(x, r R)}`, `spt f ⊆ B̄(0, R)`.
- **Calls**: `fiw_tl_blowup_setIntegral`
- **Called by**: `iwl_cr_ip_product_weighted_tangent`

#### `iwl_cr_ip_pt_frame_orthonormal` (L6036)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_triple-a1.frame_orthonormal-a1` · issue #4414 · PR #4892 · candidate `32d81ccbe658`
- **Statement and proof**: Orienting frame of the product triple `(0, 1) × M` (Simon Ch. 6, 3.2(2), used in the proof of 8.2): if `τ₁, …, τₘ` is orthonormal in `ℝ^P`, then `(e₀, ιτ₁, …, ιτₘ)` is orthonormal in `ℝ^{P+1}`, `ι v = (0, v)`.  In coordinates `⟨(a, u), (b, w)⟩ = a b + ⟨u, w⟩` and `e₀ = (1, 0)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ip_product_triple`

#### `br_loc_tauAction_current` (L1977)

- `root.boundary_rectifiability-a1.localization-a1.tau_current-a1` · issue #2475 · PR #3251 · candidate `9c856ad6531d`
- **Statement and proof**: **`τ(M, θ, ξ)` is a current (Simon Ch. 6, 3.1, p. 146).**  For a rectifiable triple `(M, θ, ξ)` in `V` (`V` need not be open), `ω ↦ τ(M, θ, ξ)(ω) = ∫_M θ(x) ⟨ω(x), ξ(x)⟩ dHⁿ(x)` is a current `X ∈ 𝒟ₙ(V)`.  It is linear since the integrands are `Hⁿ`-integrable on `M` (`ltg_tau_integrable`). It is sequentially continuous: if `ω_j → 0` in `𝒟ⁿ(V)`, all supports lie in one compact `K ⊆ V` and `sup_K ‖ω_j‖ → 0`; as `|⟨α, ξ(x)⟩| ≤ ‖α‖` for `Hⁿ⌞M`-a.e. `x` (`fiw_ims_tt_unit_bound`) and `θ > 0` on `M`, `|τ(ω_j)| ≤ (sup_K ‖ω_j‖) ∫_{M ∩ K} θ dHⁿ → 0`.
- **Calls**: `ltg_tau_integrable` (A.5), `fiw_ims_tt_unit_bound` (A.5)
- **Called by**: `iwl_cr_interval_product_im`, `br_local_finite_mass_extension`

#### `iwl_cr_ip_slice_formula` (L5850)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.slice_formula-a1` · issue #3658 · PR #4373 · candidate `e6904fcdefe0`
- **Statement and proof**: **Slice formula for the product `[[(0, 1)]] × τ(M, θ, ξ)` (Simon Ch. 6, 2.17 and 3.2(2), pp. 138, 146).**  Write `Φ(s, x) = (s, x) ∈ ℝ^{P+1}` and `π(y) = (y₁, …, y_P)`, and assume the product formula `H^{m+1}⌞{π ∈ A} = Φ_#(L¹ × Hᵐ⌞A)` for every `Hᵐ`-measurable, countably `m`-rectifiable `A ⊆ ℝ^P` with `Hᵐ(A ∩ K) < ∞` for all compact `K`.  Let `(M, θ, ξ)` be a rectifiable triple in `ℝ^P` with `θ ≥ 1` on `M`, and let `⟨α, ξ'(s, x)⟩ = ⟨β, ξ(x)⟩` whenever `β(v) = α(e₀, (0, v₁), …, (0, vₘ))`.  If `θ(π y) ⟨η(y), ξ'(y)⟩` is `H^{m+1}`-integrable on `M̃ = {y : π y ∈ M, y₀ ∈ (0, 1)}` and `φ(s)(x)(v) = η(s, x)(e₀, (0, v₁), …, (0, vₘ))` for `s ∈ [0, 1]`, then `τ(M̃, θ ∘ π, ξ')(η) = ∫₀¹ τ(M, θ, ξ)(φ(s)) ds`.  As `θ ≥ 1`, `M` has locally finite `Hᵐ`-measure, so `H^{m+1}⌞M̃ = Φ_#(L¹⌞(0, 1) × Hᵐ⌞M)` and Fubini applies.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_interval_product_im`

#### `dph_smooth_homotopy` (L36028)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1` · issue #5252 · PR #6511 · candidate `6c3f4de5c65a`
- **Statement and proof**: Simon Ch. 6, 2.25–2.27: the homotopy formula `(E0)`/`(E1)` and the affine-homotopy estimate `(Aff)`, for `Z = [[0,1]] × X` given by its slice characterization and with push-forwards written as evaluation on compatible forms.  For `(E0)`/`(E1)`, pick a test form `θ = G^#ω` near `[0,1] × spt X` (2.23).  Then `dθ = G^#(dω)` (1.14) **[corrected]**, so `Z(dθ) = Z η'`; the end slices satisfy `θᵢ = (G ∘ jᵢ)^#ω` near `spt X`, so `X θᵢ = X ηᵢ`; and the boundary formula for `[[0,1]] × X` gives `X θ₁ - X θ₀ = Z(dθ) (+ Z' θ)`, with `Z' θ = Z' θ'` by locality.
- **Correction**: the Lean doc comment, kept byte-identical (§9), cites (2.5) for `dθ = G^#(dω)`. In Simon Ch. 6, (2.5) (p. 135) is the definition of `M_W(T)`. The identity used is (1.14) (p. 134): the exterior derivative commutes with pull-back, `d f^# = f^# d`. The proof applies it through `dph_sh_extDeriv_compatible`.
- **Calls**: `dph_sh_slice_compatible_testForm`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`, `dph_sh_affine_estimate`, `iwl_sp_exists_compatible_testForm`, `dph_sh_extDeriv_compatible`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_interval_product`, `iwl_cr_ci_slice_testForm`, `iwl_cr_support_lemmas`
- **Called by**: `dph_lipschitz_pushforward`, `deformation_pushforward_homotopy`

#### `dph_sh_slice_compatible_testForm` (L33708)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_compatible-a1` · issue #5463 · PR #5691 · candidate `b9c2a28d96da`
- **Statement and proof**: Horizontal slices of a compatible form: for `j_s(x) = (s, x)`, the slice `θ_s = j_s^# θ` is a test form on `ℝ^m` with `θ_s(x)(v) = θ(s, x)((0, v₁), …, (0, v_q))`, and `θ_s = (G ∘ j_s)^# ω` at every `x` with `(s, x) ∈ N` whenever `θ = G^# ω` on `N` (chain rule).
- **Calls**: `iwl_sp_exists_compatible_testForm`
- **Called by**: `dph_smooth_homotopy`

#### `iwl_cr_ce_apply_eq_of_eqOn_nhds_support` (L11610)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.locality-a1` · issue #3701 · PR #4361 · candidate `2bb89d471b76`
- **Statement and proof**: Locality of currents: test forms that agree on an open neighbourhood `N` of `spt T` have the same value, since `ψ - φ` vanishes on `N`, so its support lies in the closed set `Nᶜ`, which misses `spt T`.
- **Calls**: `isoperimetric_apply_eq_zero_of_disjoint_support`
- **Called by**: `iwl_cr_cone_exists`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `dph_smooth_homotopy`

#### `dph_sh_affine_estimate` (L35166)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1` · issue #5484 · PR #6121 · candidate `5f368d67e216`
- **Statement and proof**: Simon Ch. 6, 2.27 (p. 140), affine homotopy estimate: let `Z = [[0,1]] × X` (characterized through `dt`-slices) and `G(t, x) = F₀(x) + t (F₁(x) - F₀(x))`, with `|F₁ - F₀| ≤ s` and `|DF₀|, |DF₁| ≤ L` on an open `O ⊇ spt X`.  If `η'` equals `G^#ψ` near `[0,1] × spt X`, then `|Z(η')| ≤ c s L^k B C` whenever `M(X) ≤ B` and `|ψ| ≤ C`, with `c = √(k+1)`.
- **Calls**: `dph_sh_ae_affine_homotopy_contDiff_fderiv`, `dph_sh_ae_affine_homotopy_isCompact_preimage_cyl`, `iwl_sp_exists_compatible_testForm`, `dph_sh_apply_eq_of_eqOn_nhds_cyl`, `iwl_cr_ci_slice_testForm`, `dph_sh_covectorEuclideanNorm_interior_le`, `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `dph_smooth_homotopy`

#### `dph_sh_ae_affine_homotopy_contDiff_fderiv` (L28523)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_fderiv-a1` · issue #5681 · PR #5976 · candidate `0e649498f782`
- **Statement and proof**: The straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`, `tl(y) = (y₁, …, yₘ)`, is built from the continuous linear maps `t`, `tl` and the smooth `F₀`, `F₁`, hence smooth.  By the chain and product rules `DG(y)(w) = DF₀(tl y)(tl w) + t(y) • (DF₁(tl y)(tl w) - DF₀(tl y)(tl w)) + t(w) • (F₁ - F₀)(tl y)`, so at `y = (s, x)` the derivative maps `e₀ ↦ F₁(x) - F₀(x)` and `ι(v) = (0, v) ↦ DF₀(x)(v) + s • (DF₁(x)(v) - DF₀(x)(v)) = (1 - s) • DF₀(x)(v) + s • DF₁(x)(v)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_sh_affine_estimate`

#### `dph_sh_ae_affine_homotopy_isCompact_preimage_cyl` (L28585)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_proper-a1` · issue #5689 · PR #5814 · candidate `7a915c9aa2f7`
- **Statement and proof**: If `F₀`, `F₁` are continuous, `S` is closed, `F₀⁻¹(K) ∩ S` is compact for every compact `K`, and `dist(F₁(x), F₀(x)) ≤ s` for `x ∈ S` **[corrected]**, then the straight-line homotopy `G(y) = F₀(tl y) + t(y) • (F₁(tl y) - F₀(tl y))`, `t(y) = y₀`, `tl(y) = (y₁, …, yₘ)`, is proper on the cylinder `cyl(S) = {t ∈ [0,1], tl ∈ S}`, i.e. `G⁻¹(K) ∩ cyl(S)` is compact for every compact `K` **[corrected]**.  `G` is continuous and `cyl(S)` is closed, so `G⁻¹(K) ∩ cyl(S)` is closed.  For `y` in it, `dist(F₀(tl y), G y) = t(y) · dist(F₁(tl y), F₀(tl y)) ≤ s`, so `F₀(tl y) ∈ cthickening s K` and `y = (t y, tl y)` lies in the compact image of `[0,1] × (F₀⁻¹(cthickening s K) ∩ S)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), states the conclusion without the hypotheses of the Lean statement (line 28585), which the proof sketch uses. Without them it is false: for `m = m′ = 1`, `F₀ = F₁ = 0` and `S = ℝ`, `G ≡ 0` and `G⁻¹({0}) ∩ cyl(S) = [0, 1] × ℝ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_sh_affine_estimate`

#### `dph_sh_apply_eq_of_eqOn_nhds_cyl` (L33661)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.slice_comparison-a1` · issue #5452 · PR #5971 · candidate `12c5eb5f57cb`
- **Statement and proof**: Locality of an interval product: if `Z η = ∫₀¹ X (φ s) ds` for the slices `φ s x = η(s, x)(e₀, ι ·)` of every `η`, then `Z η = Z η'` whenever `η = η'` on an open `N ⊇ [0, 1] × spt X`, since for `s ∈ [0, 1]` the slices of `η` and `η'` agree on the open neighbourhood `j_s⁻¹ N` of `spt X`, where `j_s x = (s, x)`, so locality of `X` makes the two integrands agree on `[0, 1]`.
- **Calls**: `iwl_cr_ci_slice_testForm`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support`
- **Called by**: `dph_sh_affine_estimate`, `dph_smooth_homotopy`

#### `dph_sh_covectorEuclideanNorm_interior_le` (L35142)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1` · issue #5475 · PR #5965 · candidate `da03b6b76312`
- **Statement and proof**: Interior-product bound for the Euclidean coefficient norm: if `β(v₁, …, v_k) = a γ(w, T v₁, …, T v_k)` for a `(k+1)`-covector `γ` on `ℝ^{m′}`, `w ∈ ℝ^{m′}` and `T : ℝ^m → ℝ^{m′}`, then `|β| ≤ |a| √(k+1) ‖w‖ ‖T‖^k |γ|`.  With the contraction `δ := γ(w, ·) = γ.curryLeft w` we have `β = a • T^#δ`, so homogeneity `Submission.fiw_tb_ext_covectorNorm_smul`, the pull-back bound `Submission.iwl_sp_covectorEuclideanNorm_pullback_le` and the contraction bound `Submission.dph_sh_ib_covectorEuclideanNorm_contract_le` give `|β| = |a| |T^#δ| ≤ |a| ‖T‖^k |δ| ≤ |a| ‖T‖^k √(k+1) ‖w‖ |γ|`.
- **Calls**: `dph_sh_ib_covectorEuclideanNorm_contract_le`, `fiw_tb_ext_covectorNorm_smul`, `iwl_sp_covectorEuclideanNorm_pullback_le`
- **Called by**: `dph_sh_affine_estimate`

#### `dph_sh_ib_covectorEuclideanNorm_contract_le` (L35076)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.interior_bound-a1.contraction_bound-a1` · issue #5641 · PR #5915 · candidate `6adf1557d9ef`
- **Statement and proof**: Contraction bound for the Euclidean coefficient norm: if the `k`-covector `δ` is the contraction `γ(w, ·)` of a `(k+1)`-covector `γ` with `w ∈ ℝ^p`, then `|δ| ≤ √(k+1) ‖w‖ |γ|`. Expand `w = ∑_b w_b e_b` in the first slot, so `δ(e_J) = ∑_b w_b γ(e_{(b, J)})`; Cauchy–Schwarz gives `δ(e_J)² ≤ ‖w‖² ∑_b γ(e_{(b, J)})²`.  Summing over all `J` and reindexing `(b, J) ↦ I` yields `k! |δ|² ≤ ‖w‖² (k+1)! |γ|²` by the all-tuples identity; cancel `k!` and take roots.
- **Calls**: `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`
- **Called by**: `dph_sh_covectorEuclideanNorm_interior_le`

#### `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul` (L33001)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.tuple_sum_factorial-a1` · issue #3255 · PR #4119 · candidate `5d1a7f344e2f`
- **Statement and proof**: Full tuple sum of squared coefficients in the standard basis `e` of `ℝ^m`: for a `j`-covector `γ`, `∑_i γ(e_{i 0}, …, e_{i (j-1)})² = j! |γ|²`, the sum over all index maps `i : Fin j → Fin m`. The counting identity turns the left side into `j! ∑_{I increasing} γ(e_I)²`, and the orthonormal-basis formula for `|γ|²`, applied to `e` itself, identifies that sum with `|γ|²`.
- **Calls**: `slicing_mb_wn_norm_sq_eq_onb_sum` (A.5), `slicing_mb_wn_sq_sum_eq_factorial_mul` (A.5)
- **Called by**: `iwl_sp_covectorEuclideanNorm_pullback_le`, `dph_sh_ib_covectorEuclideanNorm_contract_le`

#### `fiw_tb_ext_covectorNorm_smul` (L715)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.norm_smul-a1` · issue #3262 · PR #3755 · candidate `47d3d707ce25`
- **Statement and proof**: Homogeneity of the Euclidean coefficient norm (Simon Ch. 6, 1.15, 2.4–2.5): `|c α| = |c| |α|`.  Every coefficient of `c • α` on an increasing tuple of basis vectors is `c` times that of `α`, so each squared coefficient gains the factor `c²`; pull `c²` out of the finite sum and use `√(c² s) = √(c²) √s = |c| √s`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `dph_sh_covectorEuclideanNorm_interior_le`

#### `iwl_sp_covectorEuclideanNorm_pullback_le` (L33128)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1` · issue #2481 · PR #4332 · candidate `3e52d3e816fb`
- **Statement and proof**: Pullback bound for the Euclidean covector norm: for `L : ℝ^P → ℝ^Q` and a `j`-covector `α` on `ℝ^Q`, `|L^#α| ≤ ‖L‖^j |α|`.  The multilinear bound `Submission.iwl_sp_pn_multilinear_sum_sq_le` for `β := α` gives `∑_i α(L e∘i)² ≤ (‖L‖²)^j ∑_i α(e′∘i)²`, and `α(L e∘i) = (L^#α)(e∘i)` by definition.  By `Submission.iwl_sp_pn_sum_sq_tuples_eq_factorial_mul` the two sums over all index tuples are `j! |L^#α|²` and `j! |α|²`; cancel `j! > 0` and take square roots.
- **Calls**: `iwl_sp_pn_sum_sq_tuples_eq_factorial_mul`, `iwl_sp_pn_multilinear_sum_sq_le`
- **Called by**: `dph_lpfex_bounded_compatible_form`, `dph_sh_covectorEuclideanNorm_interior_le`, `iwl_sp_massOn_le_of_compatible`

#### `iwl_sp_pn_multilinear_sum_sq_le` (L33060)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.multilinear_bound-a1` · issue #3281 · PR #3828 · candidate `82bc30ecd41c`
- **Statement and proof**: Multilinear tensor-power bound: for every continuous linear `L : ℝ^P → ℝ^Q` and every `j`-multilinear `β : (ℝ^Q)^j → ℝ` (not necessarily alternating or continuous), `∑_{i : Fin j → Fin P} β(L e_{i(1)}, …, L e_{i(j)})²` `≤ (‖L‖²)^j ∑_{i : Fin j → Fin Q} β(e′_{i(1)}, …, e′_{i(j)})²`, with `e`, `e′` the standard bases.  Induction on `j`, generalizing `β`: split the sums over `Fin (j + 1) → Fin n` along `Fin.cons`, apply the inductive hypothesis to `β.curryLeft (L e_a)`, exchange the sums and bound each slot functional `y ↦ β(Fin.cons y (e′ ∘ i″))` by the one-slot estimate `Submission.iwl_sp_pn_sum_sq_comp_basis_le`.
- **Calls**: `iwl_sp_pn_sum_sq_comp_basis_le`
- **Called by**: `iwl_sp_covectorEuclideanNorm_pullback_le`

#### `iwl_sp_pn_sum_sq_comp_basis_le` (L33013)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pullback_norm-a1.one_slot_bound-a1` · issue #3267 · PR #3777 · candidate `e37372c4d9bc`
- **Statement and proof**: One-slot bound: for `L : ℝ^P → ℝ^Q` and a linear functional `f` on `ℝ^Q`, `∑_a f(L e_a)² ≤ ‖L‖² ∑_b f(e′_b)²`.  The Riesz vector `g = (f(e′_b))_b` gives `f = ⟨g, ·⟩` and the test vector `u = (f(L e_a))_a` has `f(L u) = |u|²`, so Cauchy–Schwarz and the operator norm give `|u|² = ⟨g, L u⟩ ≤ |g| ‖L‖ |u|`; cancel `|u|` and square.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_sp_pn_multilinear_sum_sq_le`

#### `dph_sh_extDeriv_compatible` (L33775)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.extderiv_compatible-a1` · issue #5473 · PR #5551 · candidate `06e17ac22403`
- **Statement and proof**: Exterior differentiation commutes with pull-back, locally (Simon Ch. 6, §1, (1.14)): if `θ` agrees with the pull-back `G^#ω` of a `C^∞` form `ω` by a `C^∞` map `G` on an open set `N`, then `dθ = G^#(dω)` on `N`.  `dθ(x)` only depends on the germ of `θ` at `x`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_smooth_homotopy`

#### `dph_lipschitz_pushforward` (L36426)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1` · issue #5257 · PR #6616 · candidate `a20cf9c24fee`
- **Statement and proof**: **Lipschitz push-forward of normal currents (Simon Ch. 6, 2.28–2.29).**  (I) the limit `S` of the push-forwards `X(η_n)` along locally admissible smooth approximations `G_n → G` exists, is unique, and has `M(S) ≤ Λ^k M(X)` and `spt S ⊆ closure (G(spt X))`; (II) it commutes with `∂`; (III) it is linear in `X`.  `Submission.dph_lipschitz_smooth_approx` gives the reference sequences (`Submission.dph_lpf_reference_sequence`); the product `[[0,1]] × X` of `Submission.dph_interval_product` and the homotopy formulas `Submission.dph_smooth_homotopy` give the comparison lemma `Submission.dph_lpf_comparison`, from which `Submission.dph_lpf_existence` builds (I); (II) and (III) are `Submission.dph_lpf_boundary` and `Submission.dph_lpf_linearity`.
- **Calls**: `dph_lpf_reference_sequence`, `dph_lipschitz_smooth_approx`, `dph_lpf_comparison`, `dph_interval_product`, `dph_smooth_homotopy`, `dph_lpf_existence`, `dph_lpf_boundary`, `dph_lpf_linearity`
- **Called by**: `deformation_pushforward_homotopy`

#### `dph_lpf_reference_sequence` (L28468)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.reference_sequence-a1` · issue #5559 · PR #5943 · candidate `3ae6d1a24146`
- **Statement and proof**: **Reference smooth approximations near a closed set** (Simon Ch. 6, 2.28–2.29; Step 2 of the Lipschitz push-forward).  Assume the smooth approximation statement (SA) of `dph_lipschitz_smooth_approx`.  If `F` is closed, `G` is `Λ`-Lipschitz on `F_r` (`r > 0`) and proper on `F`, (SA) with `A := F`, `δ := r` gives `C^∞` maps `Gₙ` with `‖DGₙ‖ ≤ Λ` on `F_(r/2)` and `Gₙ → Ĝ` uniformly, where `Ĝ = G` on `F_r ⊇ F_(r/2)`.  So `Gₙ → G` uniformly on `F_(r/2)`, eventually `dist (Gₙ x) (G x) ≤ 1` on `F`, and `dph_lpf_proper_transfer` (a) makes `Gₙ` proper on `F`.
- **Calls**: `dph_lpf_proper_transfer`
- **Called by**: `dph_lipschitz_pushforward`

#### `dph_lpf_proper_transfer` (L28423)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.proper_transfer-a1` · issue #5550 · PR #5780 · candidate `01fc57f4c068`
- **Statement and proof**: Properness transfer (fact (P)); "proper on `F`" means `f⁻¹(K) ∩ F` is compact for every compact `K`.  (a) If `G` is proper on the closed set `F` and the continuous map `g` is `d`-close to `G` on `F`, then `g⁻¹(K) ∩ F` is a closed subset of the compact set `G⁻¹(cthickening d K) ∩ F`.  (b) The affine homotopy `H(y) = F₀(x) + s • (F₁(x) − F₀(x))`, `y = (s, x)`, of two such maps stays in the closed `d`-ball about `G(x)` by convexity, so `H⁻¹(K) ∩ ([0,1] × F)` is a closed subset of the image of the compact set `[0,1] × (G⁻¹(cthickening d K) ∩ F)` under the continuous chart `(s, x) ↦ y`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lpf_reference_sequence`, `dph_lpf_comparison`

#### `dph_lpf_comparison` (L32022)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1` · issue #5565 · PR #6126 · candidate `b258640d1b3d`
- **Statement and proof**: Comparison lemma (Step 1 of the Lipschitz push-forward): for `X` with `M(X) < ∞` and, if `k ≥ 1`, `M(∂X) < ∞` **[corrected]**, if `C^∞` maps `Gₙ`, `G'ₙ` with eventual derivative bounds `L`, `L'` near `spt X` both converge uniformly to a map `G` proper on `spt X`, then pull-backs `ηₙ`, `η'ₙ` of `ω` compatible with `Gₙ`, `G'ₙ` near `spt X` satisfy `X(η'ₙ) − X(ηₙ) → 0`.  For `ε > 0`, eventually `Gₙ` and `G'ₙ` are `ε`-close to `G` on `O ∩ O' ⊇ spt X`; so `Gₙ` is proper on `spt X` and the affine homotopy between `Gₙ` and `G'ₙ` is proper on `[0,1] × spt X` (properness transfer), `dist(G'ₙ, Gₙ) ≤ 2ε` on `O ∩ O'`, and the core estimate gives `|X(η'ₙ) − X(ηₙ)| ≤ 2C₀ε`, which is `< δ` for `ε = δ/(2C₀ + 1)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these two hypotheses of the Lean statement (line 32022); the core estimate `dph_lpf_cmp_core_estimate` uses both masses.
- **Calls**: `dph_lpf_cmp_core_estimate`, `dph_lpf_proper_transfer`
- **Called by**: `dph_lipschitz_pushforward`

#### `dph_lpf_cmp_core_estimate` (L31919)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1.core_estimate-a1` · issue #5874 · PR #5988 · candidate `096c8c29bdaa`
- **Statement and proof**: **Core estimate of the comparison lemma** (Simon Ch. 6, proof of 2.29, p. 141: the homotopy formula 2.25 for the affine homotopy 2.26 and the mass bound 2.27 give `|f_ε# T(ω) − f_δ# T(ω)| ≤ C sup |f_ε − f_δ| (Lip f)ⁿ`).  Assume the interval product (Prod) and the homotopy formulas (E0), (E1) with the affine estimate (Aff).  For `X` with `M(X) < ∞` (and `M(∂X) < ∞` if `k ≥ 1`), `ω` and `L ≥ 0`, everything entering `C₀` is chosen before the maps: `Z` with `ProdChar(X, Z)`, the constant `c` of (Aff), `C₁ ≥ |dω|` and `B = M(X)`; for `k = j + 1` also `Z′` with `ProdChar(∂X, Z′)`, `c′`, `C₂ ≥ |ω|` and `B′ = M(∂X)`.  For the affine homotopy `H = H[F₀, F₁]`, the pull-backs `η′ = H^# dω`, `θ′ = H^# ω` near `[0, 1] × spt X` turn the homotopy formula into `X(η₁) − X(η₀) = Z(η′) (+ Z′(θ′))`, and (Aff) bounds `|Z(η′)|` by `c s L^k M(X) C₁` and, for `k = j + 1`, `|Z′(θ′)|` by `c′ s L^j M(∂X) C₂`, with the constant `c′` of (Aff) in degree `j`; so `C₀ = c L^k M(X) C₁`, plus `c′ L^j M(∂X) C₂` if `k = j + 1` **[corrected]**.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "(Aff) bounds each term by `c s L^k M(·) sup |·|`". The term `Z′(θ′)` concerns the `j`-current `∂X`, `j = k − 1`, so (Aff) is applied in degree `j` with its own constant `c′` and gives the factor `L^j`, not `L^k`. The Lean proof (lines 31971–32013) takes `C₀ = c L^{j+1} B C₁ + c′ L^j B′ C₂` with `B = M(X)` and `B′ = M(∂X)`.
- **Calls**: `br_la_testForm_covectorNorm_bounded`, `dph_lpf_cmp_affine_homotopy`, `iwl_sp_exists_compatible_testForm`, `iwl_cr_support_lemmas`
- **Called by**: `dph_lpf_comparison`

#### `br_la_testForm_covectorNorm_bounded` (L2533)

- `root.boundary_rectifiability-a1.lattice_approximation-a1.testform_bounded-a1` · issue #1189 · PR #2114 · candidate `c34586955a82`
- **Statement and proof**: **Test forms have bounded Euclidean coefficient norm** (the finiteness of `sup_x |ω(x)|` behind "Evidently (1), (2) give `P_k(ω) → T_k(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169, where the printed `T_k(ω)` is a misprint for `T(ω)` **[corrected]**). `x ↦ |ω(x)|` is continuous, since `α ↦ |α|` is the square root of a finite sum of squares of evaluations, and has compact support, since `|0| = 0`.  A continuous compactly supported real function is bounded by some `C₀ ≥ 0`, and `C = C₀ + 1` is positive.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes the sentence of p. 169 with `T(ω)` as the limit. The book prints "Evidently (1), (2) give `P_k(ω) → T_k(ω)` `∀ω ∈ 𝒟ⁿ(ℝ^{n+ℓ})`" (the paragraph after display (2) of the proof of 6.2). No `T_k` is defined there, and `T(ω)` is meant, since display (1) reads `T − P_k = ∂R_k + S_k`. The quotation above now follows the printed text and notes the misprint.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_mass_eq_zero_iff`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `dph_lpf_cmp_core_estimate`, `iwl_restriction_weak_limit`

#### `dph_lpf_cmp_affine_homotopy` (L28492)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1.affine_homotopy-a1` · issue #5858 · PR #5948 · candidate `d3db72734efb`
- **Statement and proof**: **The affine homotopy restricts to its ends and is smooth** (Simon Ch. 6, (2.26), p. 140: `h(t, x) = f(x) + t (g(x) − f(x))`).  On `ℝ^{m+1}` write `t(y) = y₀` and `tl(y) = (y₁, …, y_m)`; `G = F₀ ∘ tl + t • (F₁ ∘ tl − F₀ ∘ tl)`.  For `y = cons(s, x)`, `t(y) = s` and `tl(y) = x` hold definitionally, so `G(cons(0, x)) = F₀(x)` and `G(cons(1, x)) = F₁(x)`.  The maps `t` and `tl` are coordinate projections composed with continuous linear equivalences, hence `C^∞`, so `G` is `C^∞` when `F₀` and `F₁` are.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lpf_cmp_core_estimate`

#### `dph_lpf_existence` (L33293)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1` · issue #5590 · PR #6347 · candidate `73e44feaf098`
- **Statement and proof**: **Lipschitz push-forward, existence** (Simon Ch. 6, 2.29, p. 141; supplied Steps 1–12).  Assume the reference-sequence statement (RS) and the comparison statement (CL).  Let `M(X) < ∞` and, if `k ≥ 1`, `M(∂X) < ∞` **[corrected]**; let `G` be `Λ`-Lipschitz on `(spt X)_r` and proper on `spt X`.  (RS) with `F := spt X` gives `C^∞` maps `G_n` with `‖DG_n‖ ≤ Λ` on `O₀ := (spt X)_{r/2}`, `G_n → G` uniformly there and `G_n` proper on `spt X` for `n ≥ n₀`.  `Submission.dph_lpfex_bounded_compatible_form` gives forms `η_n(ω)`, compatible with `(G_n, ω)` near `spt X` for `n ≥ n₀` (`η_n(ω) := 0` for `n < n₀`), with `|η_n(ω)| ≤ Λ^k C` whenever `|ω| ≤ C`; the mass bound gives `|X(η_n(ω))| ≤ M(X) Λ^k C`. (CL) along pairs of reindexings and `Submission.dph_lpfex_tendsto_of_index_maps` give a limit `S₀(ω) = lim X(η_n(ω))`, and (CL) against `η_n(ω)` shows that every admissible approximation computes `S₀(ω)`; this makes `S₀` linear.  `Submission.dph_lpf_current_of_bounded_functional` turns `S₀` into a current `S` with `M(S) ≤ Λ^k M(X)`; uniqueness is uniqueness of limits, and `Submission.dph_lpfex_support_subset_closure_image` gives `spt S ⊆ closure (G(spt X))`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the hypothesis `M(∂X) < ∞` for `k ≥ 1` of the Lean statement (line 33293), which the comparison statement (CL) needs: the homotopy formula behind it has a boundary term.
- **Calls**: `dph_lpfex_bounded_compatible_form`, `dph_lpfex_tendsto_of_index_maps`, `cmb_abs_apply_le_of_massOn_le` (A.1), `dph_lpf_current_of_bounded_functional`, `dph_lpfex_support_subset_closure_image`
- **Called by**: `dph_lipschitz_pushforward`

#### `dph_lpfex_bounded_compatible_form` (L33161)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.bounded_compatible-a1` · issue #5941 · PR #6339 · candidate `f7dbd7a666a7`
- **Statement and proof**: Bounded compatible pull-back forms (Steps 2–3 of the Lipschitz push-forward construction): if `f` is `C^∞`, proper on `A`, and `‖Df‖ ≤ Λ` on an open `O ⊇ A`, every `ω ∈ 𝒟ᵏ(ℝ^{m′})` has a pull-back `η ∈ 𝒟ᵏ(ℝ^m)` with `η = f^#ω` on an open `N ⊇ A` and `|η(x)| ≤ Λ^k C` whenever `|ω| ≤ C`.  The cut-off pull-back `η = ζ f^#ω ∈ 𝒟ᵏ(O)` of `Submission.iwl_sp_exists_compatible_testForm` is also a test form on `ℝ^m`; on `O`, `|ζ f^#ω| = ζ |f^#ω| ≤ ‖Df‖^k |ω ∘ f| ≤ Λ^k C` by `Submission.iwl_sp_covectorEuclideanNorm_pullback_le`, and off `O ⊇ spt η` it vanishes.
- **Calls**: `iwl_sp_exists_compatible_testForm`, `iwl_sp_covectorEuclideanNorm_pullback_le`
- **Called by**: `dph_lpf_existence`

#### `dph_lpfex_tendsto_of_index_maps` (L33210)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.index_cauchy-a1` · issue #5947 · PR #6034 · candidate `7bee0b9d3976`
- **Statement and proof**: Simon Ch. 6, 2.29, p. 141 **[corrected]** (Lipschitz push-forward, existence), the Cauchy argument of Step 6: a real sequence `a` converges if `a (q i) - a (p i) → 0` for all index maps `p, q → ∞`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), cites 3.6–3.9. Those items (pp. 147–148) define the push-forward of an integer multiplicity current directly by an integral, and they contain no limit argument. The Lipschitz push-forward is obtained as a limit `f_# T(ω) = lim_{σ↓0} f_{σ#} T(ω)`, with a Cauchy estimate, in Lemma 2.29 (p. 141). "Step 6" is a step of the accepted proof of the caller `dph_lpf_existence`, which cites 2.29.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lpf_existence`

#### `dph_lpf_current_of_bounded_functional` (L32073)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.current_criterion-a1` · issue #5572 · PR #5916 · candidate `f5a2520e7214`
- **Statement and proof**: **A bounded linear functional on `𝒟ⁿ(U)` is a current of mass at most `B`** (Simon Ch. 6, 2.1 and 2.4; fact (F5/F6) for the Lipschitz push-forward).  If `T₀` is additive and homogeneous and `|T₀(ω)| ≤ B·C` whenever `|ω(y)| ≤ C` for all `y`, then `T₀` is a current `S`: its sequential continuity is `fiw_ims_sc_continuous_of_bound` with `A := B` on every compact `K ⊆ U`, and every mass-admissible `ω` (`|ω| ≤ 1`) has `S(ω) ≤ |T₀(ω)| ≤ B·1`, so the supremum `M(S)` is at most `B`.
- **Calls**: `fiw_ims_sc_continuous_of_bound`
- **Called by**: `dph_lpf_existence`

#### `dph_lpfex_support_subset_closure_image` (L33236)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.existence-a1.support_closure-a1` · issue #5953 · PR #6131 · candidate `d31416678baa`
- **Statement and proof**: Support of a push-forward (Simon Ch. 6, 2.23 and 3.6, pp. 139, 147): if `S ω` is the limit of `X` on forms equal to the pull-back of `ω` by continuous `G_n` near `spt X`, and `G_n → G` uniformly on `spt X`, then `spt S ⊆ closure (G(spt X))`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dph_lpf_existence`

#### `dph_lpf_boundary` (L33435)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.boundary-a1` · issue #5608 · PR #5930 · candidate `e9411ef3642d`
- **Statement and proof**: Part (II) of the Lipschitz push-forward: if `S` is the Lipschitz push-forward of `X`, with `M(X), M(∂X) < ∞`, then `∂S` is that of `∂X`.  Part (I) applied to `∂X` gives a push-forward `S_∂` of `∂X`.  For a reference sequence `Gₙ` of (RS) on `(spt X)_{r/2}` and forms `θₙ` compatible with `(Gₙ, φ)` near `spt X`, `dθₙ` is compatible with `(Gₙ, dφ)` since `d` commutes with pull-back, so `S_∂(φ) = lim ∂X(θₙ) = lim X(dθₙ) = S(dφ) = ∂S(φ)`.
- **Calls**: `iwl_cr_support_lemmas`, `iwl_sp_exists_compatible_testForm`
- **Called by**: `dph_lipschitz_pushforward`

#### `dph_lpf_linearity` (L33568)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.linearity-a1` · issue #5612 · PR #5890 · candidate `0b11970c705b`
- **Statement and proof**: Linearity of the Lipschitz push-forward in the current (Part (III)).  With `F = spt X ∪ spt X₁ ⊇ spt X₂`, one reference sequence `G_n` for `F` (with `O = F_{r/2}`, `L = Λ`) and one sequence `η_n`, compatible with `(G_n, ω)` near `F` once `G_n` is proper on `F`, are admissible for all three push-forwards; so `X₂(η_n) = a X(η_n) + a₁ X₁(η_n)` tends both to `S₂(ω)` and to `a S(ω) + a₁ S₁(ω)`.
- **Calls**: `iwl_cr_support_lemmas`, `iwl_sp_exists_compatible_testForm`
- **Called by**: `dph_lipschitz_pushforward`

#### `dph_lipschitz_pushforward_im` (L36460)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward_im-a1` · issue #5263 · PR #5768 · candidate `309a1a643b76`
- **Statement and proof**: **Integrality of the Lipschitz push-forward defined by smooth approximation** (step 5.9 of the push-forward homotopy argument; Simon Ch. 6, 2.29 and Lemma 3.9).  Assume (S5′): `g_# X` is an integer multiplicity `S'` with `∫_M θ ⟨ω(g_j x), (Dg_j)_# ξ⟩ dHᵏ → S'(ω)` along `C¹` maps `g_j → g`.  If `S` is the limit of `X(η_n)` for forms `η_n` compatible with smooth approximations `G_n → G` near `spt X`, then `S` is integer multiplicity.  Take `G_n → Ĝ` from `dph_lipschitz_smooth_approx` and `η_n` from `iwl_sp_exists_compatible_testForm`.  As `Hᵏ(M ∖ spt X) = 0` (`iwl_sp_rectifiable_support_null`), `X(η_n)` is the integral for `g_j = G_n`, so `S = S'`.
- **Calls**: `dph_lipschitz_smooth_approx`, `iwl_sp_rectifiable_support_null`, `iwl_sp_exists_compatible_testForm`
- **Called by**: `deformation_pushforward_homotopy`

#### `iwl_sp_rectifiable_support_null` (L36444)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1` · issue #2463 · PR #4341 · candidate `05cea8b8ad1f`
- **Statement and proof**: **A rectifiable representation carries no `Hⁿ`-measure off the support** (step 3 of the smooth push-forward argument; cf. Simon Ch. 6, 2.11 and Lemma 3.9).  If `T = τ(M, θ, ξ)` then `Hⁿ(M ∖ spt T) = 0`.  Testing `T` with `φ b` (`φ ∈ C_c^∞(W)`, `b` an `n`-covector) shows `Hⁿ(M ∩ W) = 0` for every open `W ⊂⊂ U` on which `T` vanishes (`iwl_sp_sn_local_null`).  As `M ⊆ U`, countably many such `W` cover `M ∖ spt T` (`iwl_sp_sn_null_diff_support_of_local_null`).
- **Calls**: `iwl_sp_sn_null_diff_support_of_local_null`, `iwl_sp_sn_local_null`
- **Called by**: `dph_lipschitz_pushforward_im`, `iwl_sp_lipschitzPushforward_apply_eq`

#### `iwl_sp_sn_null_diff_support_of_local_null` (L35718)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.support_cover-a1` · issue #3265 · PR #3941 · candidate `06b135a22629`
- **Statement and proof**: If `M ⊆ U` is `μ`-null on every open `W ⊂⊂ U` on which `T` vanishes, then `μ(M ∖ spt T) = 0`: `M ∖ spt T` lies in the zero region (Simon 2.11), a countable union of such `W` (Lindelöf).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_sp_rectifiable_support_null`

#### `iwl_sp_sn_local_null` (L35844)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.local_null-a1` · issue #3316 · PR #4158 · candidate `ef65e5d55971`
- **Statement and proof**: **A rectifiable representation is null where the current vanishes (a step of the proof that `τ(M, θ, ξ)` lives on `spt T`, used for Simon Ch. 6, Theorem 8.2).**  If `T = τ(M, θ, ξ)` and `T` vanishes on an open `W` with `closure W` a compact subset of `U`, then `Hⁿ(M ∩ W) = 0`.  Testing `T` with `φ α` (`φ ∈ C_c^∞(W)`, `α` an `n`-covector) gives `∫_M θ φ ⟨α, ξ⟩ dHⁿ = 0`, so `⟨α, ξ⟩ = 0` a.e. on `M ∩ W` (`iwl_sp_sn_weighted_fundamental_lemma`; `|⟨α, ξ⟩| ≤ ‖α‖` by `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`).  Finitely many covectors separate `n`-vectors (`iwl_sp_sn_covector_separating_family`), so `ξ = 0` a.e. on `M ∩ W`, while `ξ ≠ 0` a.e. on `M`.
- **Calls**: `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_sp_sn_weighted_fundamental_lemma`, `iwl_sp_sn_covector_separating_family`
- **Called by**: `iwl_sp_rectifiable_support_null`

#### `iwl_sp_sn_signed_simpleNVector_bound_ne_zero` (L35777)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.signed_simple_bound-a1` · issue #3295 · PR #3943 · candidate `b1056f9a9134`
- **Statement and proof**: A signed simple `n`-vector `w = ±τ₁ ∧ ⋯ ∧ τₙ` of an orthonormal frame `τ` (the orientations `ξ(x)` of Simon Ch. 6, 3.1) has `|⟨b, w⟩| ≤ ‖b‖` for every `n`-covector `b` and is nonzero: `|⟨b, w⟩| = |b(τ)| ≤ ‖b‖ ∏ ‖τᵢ‖ = ‖b‖`, and the covector `b_τ = ⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩` has `b_τ(τ) = det(⟨τᵢ, τⱼ⟩) = det 1 = 1` (1.1).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_sp_sn_local_null`

#### `iwl_sp_sn_weighted_fundamental_lemma` (L35812)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.weighted_fundamental_lemma-a1` · issue #3306 · PR #3930 · candidate `fdcd05b897cd`
- **Statement and proof**: **Fundamental lemma of the calculus of variations with a positive weight** (a step of the proof that a rectifiable representation `T = τ(M, θ, ξ)` has `Hⁿ(M ∖ spt T) = 0`, used for the smooth push-forward in Simon Ch. 6, 8.2).  If `θ > 0` on `M`, `θ` is `μ`-integrable on `M ∩ W` with `W` open, `g` is a.e.-strongly measurable and a.e. bounded for `μ ⌞ M`, and `∫_M θ φ g dμ = 0` for every smooth compactly supported `φ` with `tsupport φ ⊆ W`, then `g = 0` `μ ⌞ M`-a.e. on `W`.  Mathlib's fundamental lemma applied to `θ g`, which is integrable on `W` for `μ ⌞ M`, gives `θ g = 0` there; divide by `θ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_sp_sn_local_null`

#### `iwl_sp_sn_covector_separating_family` (L35747)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.support_null-a1.covector_basis-a1` · issue #3280 · PR #3735 · candidate `ff6ccae0f524`
- **Statement and proof**: Finitely many `n`-covectors separate `n`-vectors (Simon Ch. 6, §1; used for Theorem 8.2 to show that a representation `τ(M, θ, ξ)` of `T` lives on `spt T` up to an `Hⁿ`-null set). Evaluation on tuples of standard basis vectors, `Φ(α)(r) = α(e_{r(1)}, …, e_{r(n)})`, embeds `Λⁿ(ℝ^P)` linearly into `ℝ^(Fin n → Fin P)`, since a multilinear map is determined by its values on basis vectors.  So `Λⁿ(ℝ^P)` is finite-dimensional, and an `n`-vector vanishing on a basis `b₁, …, b_N` is zero.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_sp_sn_local_null`

#### `deformation_good_center` (L47744)

- `root.deformation-a1.good_center-a1` · issue #1103 · PR #5122 · candidate `bf5eec48076a`
- **Statement and proof**: **Choice of a good centre** (Simon Ch. 6, proof of the Deformation Theorem 5.1, printed (1)–(7)).  Let `d = m + 1 + ℓ`, `𝒥` the `N` index sets `J ⊆ {1, …, d}` with `|J| = m + 2`, `q = (1/2, …, 1/2)`, `V = L^d(B_{1/4}(q)) ∈ (0, ∞)` and `β = (2 N 10^{m+2} + 1) / V`, so that `2 N 10^{m+2} / β < V`; the constant is `c = N β`.  For `J ∈ 𝒥`, `p_J x = (x_i)_{i ∈ J}` and a finite measure `μ`, `Bad J μ` is the set of centres `g` with `|g - p_J q| < 1/4` such that some `σ ∈ (0, 1/4)` has `μ(T_J(g, σ)) > β σ^{m+2} μ(ℝ^d)`, where `T_J(g, σ) = {x : |p_J x - g - z| < σ for some z ∈ ℤ^J}`.  By `dgc_cylinder_volume` and `dgc_periodic_maximal`, `A J μ = {a ∈ [0,1]^d : p_J a ∈ Bad J μ}` has `L^d(A J μ) ≤ 10^{m+2} / β`, so the `2N` sets `A J μᵢ` miss a point `a` of `B_{1/4}(q) ⊆ [0,1]^d`.  Then `Σᵢ (aᵢ - 1/2)² < 1/16` and `|p_J a - p_J q| < 1/4`, hence `μᵢ(T_J(p_J a, σ)) ≤ β σ^{m+2} μᵢ(ℝ^d)` for every `J ∈ 𝒥` and `σ ∈ (0, 1/4)`.  By `dgc_tube_cover`, `{dist(·, La) < σ} ⊆ ⋃_{J ∈ 𝒥} T_J(p_J a, σ)`, and summing over the `N` sets `J` gives `μᵢ{dist(·, La) < σ} ≤ N β σ^{m+2} μᵢ(ℝ^d)`.
- **Calls**: `dgc_cylinder_volume`, `dgc_periodic_maximal`, `dgc_tube_cover`
- **Called by**: `deformation_onto_skeleton`

#### `dgc_cylinder_volume` (L7889)

- `root.deformation-a1.good_center-a1.cylinder_volume-a1` · issue #4240 · PR #4793 · candidate `750a384555a8`
- **Statement and proof**: Fubini bound for the cylinder over a set of centres (corrected (5) in the proof of Simon Ch. 6, 5.1): for `J ⊆ ι` and any `B ⊆ ℝ^J`, `L^ι({a ∈ [0,1]^ι : (a_i)_{i ∈ J} ∈ B}) ≤ L^J(B)`.  The set lies in the preimage of `B × [0,1]^{ι∖J}` under the measure-preserving equivalence `ℝ^ι ≃ ℝ^J × ℝ^{ι∖J}`, and the product measure of a rectangle of arbitrary sets is the product of the measures.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_good_center`

#### `dgc_periodic_maximal` (L7811)

- `root.deformation-a1.good_center-a1.periodic_maximal-a1` · issue #4231 · PR #5091 · candidate `eb6b2fc0270e`
- **Statement and proof**: Periodic maximal estimate (Simon Ch. 6, §5, proof of the Deformation Theorem, printed (3), (4) and `L^{n+1}(B_j) ≤ β⁻¹5^{n+1}ω_{n+1}`, pp. 163–164), for a finite measure `μ` on `X` and a measurable `p : X → ℝ^ι`, `k = card ι`: the centres `g` with `|g − g₀| < 1/4` at which some `σ ∈ (0, 1/4)` has `μ(p⁻¹ ⋃_{z ∈ ℤ^ι} B_σ(g + z)) > βσ^k μ(X)` have outer Lebesgue measure at most `10^k/β`.  Choosing such a `σ_b` for every bad centre `b`, the periodic tubes of a subfamily with disjoint balls `B̄_{σ_b}(b)` are disjoint, so the subfamily is countable and `Σ σ_b^k ≤ 1/β`; the `5`-times covering bound then gives `10^k/β`.
- **Calls**: `dgc_pm_vitali_volume_bound`, `dgc_pm_lattice_tubes_disjoint`
- **Called by**: `deformation_good_center`

#### `dgc_pm_vitali_volume_bound` (L7767)

- `root.deformation-a1.good_center-a1.periodic_maximal-a1.vitali_bound-a1` · issue #4824 · PR #5045 · candidate `5fd171468962`
- **Statement and proof**: Vitali volume bound (Simon Ch. 6, §5, proof of 5.1, printed (4), pp. 163–164): if `0 < r(b) ≤ R` on `S ⊆ ℝᵏ` and every `u ⊆ S` with pairwise disjoint closed balls `B̄_{r(b)}(b)` is countable with `∑_{b ∈ u} r(b)ᵏ ≤ M`, then `Lᵏ(S) ≤ 10ᵏ M`. The 5-times covering lemma (closed balls, `τ = 5`) gives such a `u` with `S ⊆ ⋃_{b ∈ u} B̄_{5r(b)}(b)`, and `Lᵏ(B̄_{5r(b)}(b)) ≤ (10 r(b))ᵏ`.  Only monotonicity and countable subadditivity of the outer measure are used, so `S` need not be measurable.
- **Calls**: `dgc_pm_ball_volume_le`
- **Called by**: `dgc_periodic_maximal`

#### `dgc_pm_ball_volume_le` (L7696)

- `root.deformation-a1.good_center-a1.periodic_maximal-a1.ball_volume-a1` · issue #4807 · PR #4976 · candidate `f935cd0e258f`
- **Statement and proof**: Ball-volume bound used in step 8 of the accepted natural-language proof of `dgc_periodic_maximal`, for the covering estimate in the proof of Simon Ch. 6, 5.1 (pp. 163–164), where the formal proof replaces the book's ball volume `ω_k rᵏ` by the larger cube volume `(2r)ᵏ`, i.e. uses `ω_k ≤ 2ᵏ` **[corrected]**: a closed Euclidean ball of radius `r ≥ 0` in `ℝ^ι` has Lebesgue measure at most `(2r)^k`, `k = card ι`.  Each coordinate is `1`-Lipschitz, so `B̄_r(c)` lies in the preimage under the measure-preserving coordinate map `ofLp` of the sup-metric cube `∏_i [c_i - r, c_i + r]`, whose volume is `(2r)^k`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 8 of the proof of Simon Ch. 6, 5.1 (pp. 163–164), with the erratum `ω_k ≤ 2^k`". The step number is that of the accepted proof of `dgc_periodic_maximal`. The printed estimate uses the exact ball volume `ω_k rᵏ` and is correct; replacing it by the cube bound `(2r)ᵏ` is a simplification, not an erratum.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dgc_pm_vitali_volume_bound`

#### `dgc_pm_lattice_tubes_disjoint` (L7714)

- `root.deformation-a1.good_center-a1.periodic_maximal-a1.tubes_disjoint-a1` · issue #4814 · PR #4972 · candidate `3546960ffc20`
- **Statement and proof**: Simon Ch. 6, proof of 5.1 (p. 164): `{p_j⁻¹ B_{σ_ℓ}(b_ℓ + z)}_{ℓ = 1, 2, …, z ∈ ℤ^{n+ℓ} ∩ S_j}` is a pairwise disjoint collection.  Stated for the periodic open sets before pulling back by `p_j`: if `|b - g₀|, |b' - g₀| < 1/4`, `0 < σ, σ' < 1/4` and `B̄_σ(b) ∩ B̄_σ'(b') = ∅`, then `⋃_{z ∈ ℤ^ι} B_σ(b + z)` and `⋃_{z ∈ ℤ^ι} B_σ'(b' + z)` are disjoint.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dgc_periodic_maximal`

#### `dgc_tube_cover` (L7664)

- `root.deformation-a1.good_center-a1.tube_cover-a1` · issue #4224 · PR #4767 · candidate `f78b89b01de5`
- **Statement and proof**: Simon Ch. 6, §5, proof of 5.1 (p. 164), the inclusion `⊆` of the identity printed after (5): the `σ`-neighbourhood of `L(a)` lies in the union of the periodic coordinate cylinders `p_J⁻¹(B_σ(p_J(a) + z))`, `|J| = k`, `z ∈ ℤ^J`.  `L(a)` contains `a` (as `k ≤ d`), so `dist(x, L(a)) < σ` gives `y ∈ L(a)` with `|x − y| < σ`; for the `J` and the integers `z_i = y_i − a_i` (`i ∈ J`) witnessing `y ∈ L(a)`, `∑_{i∈J} (x_i − a_i − z_i)² = ∑_{i∈J} (x_i − y_i)² ≤ |x − y|² < σ²`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_good_center`

#### `deformation_mass_restriction` (L34528)

- `root.deformation-a1.mass_restriction-a1` · issue #1104 · PR #4933 · candidate `0b7851dc2aad`
- **Statement and proof**: **Mass measure, representation and restriction, Simon Ch. 6, (2.7)–(2.9), 2.12 and 3.1 (pp. 136–137, 146).**  Let `X ∈ 𝒟_k(ℝ^N)` with `M(X) < ∞`.  Then `M_W(X) ≤ M(X) < ∞` for every `W`, so (R2) of `iwl_restriction_theory` gives the mass measure `μ`, a restriction `Y = X ⌞ A` to every Borel set `A` and `M_W(Y) = μ(W ∩ A)`, and `rectifiability_mass_measure_representation` gives a representation `(μ, v)` of `X`.  `μ` is finite and vanishes off `spt X` (`dmr_massMeasure_support_finite`).  Any two representations of `X` have the same vector measure on Borel sets (`dmr_measureRepresentation_unique`); this is the uniqueness conjunct and gives `Y(ω) = ∫_A ⟨ω, v⟩ dμ`, while restrictions are unique by (R1).  If `X = τ(M, θ, ξ)` is integer multiplicity, then `Y = τ(M ∩ A, θ, ξ)` (`polyhedral_approx_restriction_tau`), `(M ∩ A, θ, ξ)` is a rectifiable triple (`dmr_rectifiableTriple_inter`) and `θ` is still integer-valued on `M ∩ A`.
- **Calls**: `iwl_restriction_theory`, `rectifiability_mass_measure_representation` (A.3), `dmr_massMeasure_support_finite`, `dmr_measureRepresentation_unique`, `dmr_rectifiableTriple_inter`, `polyhedral_approx_restriction_tau`
- **Called by**: `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`

#### `iwl_restriction_theory` (L19780)

- `root.integrality_weak_limits-a1.restriction_theory-a1` · issue #938 · PR #1873 · candidate `b9f9acdc41ea`
- **Statement and proof**: **Restriction theory, Simon Ch. 6, (2.7)–(2.9) (p. 136).** (R0) A current with a measure representation (2.7) has locally finite mass: `M_W(X)` is bounded by `∑_I ∫_{closure W} |v(dx^I)| dμ` **[corrected]**. (R1) Restrictions `X ⌞ A` (2.9) do not depend on the representation: the coefficient densities of two representations agree on `C_c^∞`, hence on `C_c` and on bounded Borel functions. (R2) If `M_W(X) < ∞` for all `W ⊂⊂ U`, the vector Riesz theorem (Ch. 1, 4.14, SimonGMT) applied on `U` to the extension of `X` to continuous compactly supported forms gives the mass measure `μ` and a density `v` with `|v| ≤ 1`, `μ(W) = M_W(X)` by the envelope identity. Then `S_A(ω) = ∫_A ⟨ω, v⟩ dμ` is the restriction, and `M_W(S) = μ(W ∩ A)`: `≤` from `|v| ≤ 1`, `≥` from `X = S_A + S_{Aᶜ}` and inner approximation by compact sets.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says that `M_W(X)` is bounded by "the `μ`-integrals of the coefficients `v(dx^I)` over `closure W`", which read literally omits the absolute values (for `X = −[[(0, 1)]]`, `μ = L¹⌞(0, 1)`, `v = −e₁` and `W = (−1, 2)` that integral is `−1`). The Lean proof (line 19897) uses `C = ∑_I ∫_{closure W} |v(dx^I)| dμ`.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `cmb_exists_compactly_contained_exhaustion` (A.1), `polyhedral_approx_pairing_coordinate_bound`, `slicing_ru_smooth_to_continuous` (A.5), `slicing_ru_continuous_to_bounded` (A.5), `lpf_lli_inner_compact_approx` (A.3), `cmb_abs_apply_le_of_massOn_le` (A.1), `cmb_exists_testForm_uniform_approx` (A.1)
- **Called by**: `br_local_finite_mass_extension`, `deformation_mass_restriction`, `iwl_im_closure`, `iwl_restriction_weak_limit`, `ind_md_mass_measure_balls`, `iwl_localization`, `iwl_positive_density`

#### `polyhedral_approx_pairing_coordinate_bound` (L10731)

- `root.polyhedral_approximation-a1.pairing_expansion-a1.coordinate_bound-a1` · issue #1061 · PR #1503 · candidate `e05c5313237c`
- **Statement and proof**: **Coordinate bound** (for the pairing expansion in the proof of Simon Ch. 6, 6.2, p. 169). Each increasing coordinate `c_I = c(e_{I(1)}, …, e_{I(n)})` of an `n`-covector `c` is bounded in absolute value by the Euclidean coefficient norm `|c|` of Remark 2.6.  Here `|c|² = ∑_J t_J`, with `t_J = c(e_{J(1)}, …, e_{J(n)})²` for strictly increasing `J : Fin n → Fin P` and `t_J = 0` otherwise.  Every `t_J ≥ 0` and `t_I = c_I²`, so `c_I² ≤ |c|²`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_pairing_expansion`, `iwl_restriction_theory`

#### `dmr_massMeasure_support_finite` (L34348)

- `root.deformation-a1.mass_restriction-a1.mass_measure_facts-a1` · issue #4215 · PR #4770 · candidate `84f8d2059dd1`
- **Statement and proof**: Simon Ch. 6, 2.8 and 2.12: a mass measure `μ` of `X ∈ 𝒟ₖ(ℝ^N)` vanishes off `spt X`, and `μ(ℝ^N) ≤ M(X)`, so `μ` is finite when `M(X) < ∞`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_mass_restriction`

#### `dmr_measureRepresentation_unique` (L34390)

- `root.deformation-a1.mass_restriction-a1.representation_unique-a1` · issue #4219 · PR #4853 · candidate `a23ae889fb64`
- **Statement and proof**: **Uniqueness of the vector measure `v μ` of a representation (2.7), Simon Ch. 6, 2.7–2.9 (p. 136).**  Two representations `(μ₁, v₁)`, `(μ₂, v₂)` of `X ∈ 𝒟ₖ(ℝ^N)` have (a) the same set integrals `∫_A ⟨ω, vᵢ⟩ dμᵢ` over every Borel `A`, for every test form `ω` (`slicing_representation_unique` with `U = W = ℝ^N`), and (b) the same `∫_A ⟨α, vᵢ⟩ dμᵢ` over every bounded Borel `A`, for every constant covector `α`: if `A ⊆ closedBall 0 R`, a smooth cutoff `φ` with `support φ = ball 0 (R + 1)` and `φ = 1` on `closedBall 0 R` makes `φ α` a test form equal to `α` on `A`, and (a) applies to it.
- **Calls**: `slicing_representation_unique` (A.5)
- **Called by**: `deformation_mass_restriction`

#### `dmr_rectifiableTriple_inter` (L34495)

- `root.deformation-a1.mass_restriction-a1.triple_inter-a1` · issue #4237 · PR #4850 · candidate `bf2b5c94a944`
- **Statement and proof**: Restriction of a rectifiable triple to a Borel set (Simon Ch. 6, 2.9 for `τ(M, θ, ξ)` of 3.1): `(M ∩ A, θ, ξ)` again satisfies the conditions of 3.1.  Every field passes to the subset `M ∩ A ⊆ M`, the a.e. ones through `Hⁿ⌞(M ∩ A) ≤ Hⁿ⌞M`.  For the orientation, `Submission.dmr_weightedTangent_inter` makes the weighted approximate tangent space `span τ` of `(M, θ)` one of `(M ∩ A, θ)` at `Hⁿ⌞(M ∩ A)`-a.e. `x`, with the same frame `τ`.
- **Calls**: `dmr_weightedTangent_inter`
- **Called by**: `deformation_mass_restriction`

#### `dmr_weightedTangent_inter` (L34431)

- `root.deformation-a1.mass_restriction-a1.tangent_inter-a1` · issue #4228 · PR #4809 · candidate `092432628141`
- **Statement and proof**: Restriction of weighted approximate tangent spaces to a Borel set (orientation step of the proof of Simon Ch. 6, 8.2).  At `Hᵏ`-a.e. `x ∈ M ∩ A` the measure `θ Hᵏ ⌞ (M \ A)` has zero `k`-density (Upper Density Theorem, Simon Ch. 1, 3.6).  As `|1_M θ - 1_{M ∩ A} θ| = 1_{M \ A} θ`, the blow-up defect `(rᵏ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M ∩ A} θ| dHᵏ` then tends to `0`, so by locality (Simon Ch. 3, 1.7) every weighted tangent space of `(M, θ)` at `x` is one of `(M ∩ A, θ)`.
- **Calls**: `lpf_wtc_ae_zero_density_off_set` (A.4), `iwl_weighted_tangent_locality`
- **Called by**: `dmr_rectifiableTriple_inter`

#### `iwl_weighted_tangent_locality` (L11052)

- `root.integrality_weak_limits-a1.tangent_locality-a1` · issue #927 · PR #2748 · candidate `96e830881daf`
- **Statement and proof**: Locality of weighted approximate tangent spaces (Simon Ch. 3, 1.7), in the quantitative form used in the proof of Ch. 6, 8.2.  For `r > 0`, the blow-up `η_{x,r}(z) = r⁻¹(z - x)` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, so the blow-up integral of `(M, θ)` against `f` is `(rⁿ)⁻¹ ∫ f(η_{x,r} z) 1_M θ(z) dHⁿ(z)` (`M` is `Hⁿ`-null-measurable).  If `f = 0` off `B_R(0)` and `|f| ≤ C`, then for `R r ≤ ρ` these integrals exist and those of `(M, θ)` and `(M', θ')` differ by at most `C (rⁿ)⁻¹ ∫_{B̄_{R r}(x)} |1_M θ - 1_{M'} θ'| dHⁿ → 0`; as `θ x = θ' x`, the two tangent-space conditions are equivalent.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_imcomb_subset_locality`, `dmr_weightedTangent_inter`, `iwl_im_patching`, `iwl_im_closure`, `deformation_imcomb_weight_change`, `iwl_top_dim_integrality`

#### `polyhedral_approx_restriction_tau` (L17780)

- `root.polyhedral_approximation-a1.restriction_tau-a1` · issue #530 · PR #2849 · candidate `d0bdb40ee3ab`
- **Statement and proof**: **Simon Ch. 6, (2.9) and 3.1 (pp. 136, 146).**  If `T = τ(M, θ, ξ)` and `S = T ⌞ A`, then `S = τ(M ∩ A, θ, ξ)`.  Let `(μ, v)` be the representation of `T` defining `S`.  For a covector `c`, `⟨c, v⟩` is locally `μ`-integrable and `θ ⟨c, ξ⟩` is locally `Hⁿ ⌞ M`-integrable on `U` (`polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`).  Both pair with every smooth `ψ` to `T(ψ c)`, so `polyhedral_approx_measure_uniqueness` equates their integrals over `A` against continuous compactly supported weights.  Expanding `ω` in the coordinate wedges `dx^I` (`polyhedral_approx_pairing_expansion`), with the coordinates `ω_I` as weights, and summing over `I` gives `S(ω) = ∫_A θ ⟨ω, ξ⟩ d(Hⁿ ⌞ M) = τ(M ∩ A, θ, ξ)(ω)`.
- **Calls**: `polyhedral_approx_rt_integrableOn_apply`, `polyhedral_approx_rt_tau_integrableOn`, `polyhedral_approx_measure_uniqueness`, `polyhedral_approx_pairing_expansion`
- **Called by**: `polyhedral_approx_truncation_seq`, `deformation_mass_restriction`

#### `polyhedral_approx_rt_integrableOn_apply` (L10581)

- `root.polyhedral_approximation-a1.restriction_tau-a1.repr_integrability-a1` · issue #1292 · PR #2226 · candidate `5309966301ae`
- **Statement and proof**: **Local integrability of `⟨c, v⟩` from test forms (Simon Ch. 6, (2.7), p. 136).**  If `⟨ω, v⟩` is `μ`-integrable for every test form `ω ∈ 𝒟ⁿ(U)`, then `⟨c, v⟩` is `μ`-integrable on every compact `K ⊆ U`, for every constant `n`-covector `c`.  With `cthickening δ K ⊆ U` and `r = δ / 2`, the smooth Urysohn lemma gives a smooth `χ` with `χ = 0` off `thickening r K` and `χ = 1` on `K`; its support lies in the compact `cthickening r K ⊆ U`, so `ω_K = χ c` is a test form on `U`, and `⟨ω_K, v⟩ = χ ⟨c, v⟩` agrees with `⟨c, v⟩` on the closed set `K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_restriction_tau`

#### `polyhedral_approx_rt_tau_integrableOn` (L10617)

- `root.polyhedral_approximation-a1.restriction_tau-a1.tau_integrability-a1` · issue #1300 · PR #2117 · candidate `f3e41bc4dfde`
- **Statement and proof**: **Local integrability of `θ ⟨c, ξ⟩` for `τ(M, θ, ξ)` (Simon Ch. 6, 3.1, p. 146).**  If `(M, θ, ξ)` is a rectifiable triple in `U`, then `x ↦ θ(x) ⟨c, ξ(x)⟩` is `Hⁿ⌞M`-integrable on every compact `K ⊆ U`, for every `n`-covector `c`.  For orthonormal `τ`, `‖±τ₁ ∧ ⋯ ∧ τₙ‖ ≤ ∏ᵢ ‖τᵢ‖ = 1`, so `|⟨c, ξ⟩| ≤ ‖c‖` `Hⁿ⌞M`-a.e.; `(Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K)`, on which `θ` is integrable, and an integrable function times an a.e.-bounded one is integrable.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_restriction_tau`

#### `polyhedral_approx_measure_uniqueness` (L17728)

- `root.polyhedral_approximation-a1.measure_uniqueness-a1` · issue #528 · PR #2749 · candidate `d5f2301589a8`
- **Statement and proof**: Uniqueness of the vector measure in Simon Ch. 6, (2.7)–(2.9) (p. 136), which makes `T ⌞ A` well defined: if `g₁ μ₁` and `g₂ μ₂` (`gᵢ` locally `μᵢ`-integrable in `U`) agree on `C^∞` functions with compact support in `U`, then `∫_A u g₁ dμ₁ = ∫_A u g₂ dμ₂` for every Borel `A` and continuous `u` with compact support in `U`.  For an open `O ⊇ tsupport u` with compact `L = closure O ⊆ U`, each `gᵢ` is `μᵢ⌞L`-integrable, the hypothesis passes to `μᵢ⌞L` on `O`, and `1_A u` is bounded, Borel and vanishes outside `O`.
- **Calls**: `polyhedral_approx_integrable_smooth_ext`
- **Called by**: `polyhedral_approx_restriction_tau`

#### `polyhedral_approx_integrable_smooth_ext` (L17686)

- `root.polyhedral_approximation-a1.measure_uniqueness-a1.integrable_smooth_ext-a1` · issue #1178 · PR #2245 · candidate `4279988c51a7`
- **Statement and proof**: Integrable densities `g₁ μ₁`, `g₂ μ₂` that agree on every `C^∞` function with compact support in an open set `O` agree on every bounded Borel `b` vanishing outside `O` (the uniqueness behind Simon Ch. 6, (2.7)–(2.9), p. 136).  Split `gᵢ μᵢ = pᵢ − nᵢ` into finite measures (`polyhedral_approx_density_split`).  The finite measures `λ₁ = p₁ + n₂`, `λ₂ = p₂ + n₁` satisfy `∫ c dλ₁ − ∫ c dλ₂ = ∫ c g₁ dμ₁ − ∫ c g₂ dμ₂` for bounded Borel `c` (★), so they agree on smooth tests in `O`, hence on `b` (`polyhedral_approx_finite_smooth_ext`); (★) with `c = b` concludes.
- **Calls**: `polyhedral_approx_density_split`, `polyhedral_approx_finite_smooth_ext`
- **Called by**: `polyhedral_approx_measure_uniqueness`

#### `polyhedral_approx_density_split` (L17593)

- `root.polyhedral_approximation-a1.measure_uniqueness-a1.density_split-a1` · issue #1177 · PR #1917 · candidate `53e59ae39ad2`
- **Statement and proof**: An integrable density is a difference of two finite measures (used for the uniqueness of the vector measure in Simon Ch. 6, (2.7)–(2.9), p. 136): `ν^± = μ.withDensity (ofReal ∘ (±g))` are finite and `∫ b dν⁺ − ∫ b dν⁻ = ∫ b g dμ` for every bounded Borel `b`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_integrable_smooth_ext`

#### `polyhedral_approx_finite_smooth_ext` (L17626)

- `root.polyhedral_approximation-a1.measure_uniqueness-a1.finite_smooth_ext-a1` · issue #1176 · PR #1959 · candidate `4e5d18cb88b8`
- **Statement and proof**: Finite measures `ν₁, ν₂` on `ℝ^P` that agree on every `C^∞` function with compact support in an open set `O` agree on every function `b` vanishing outside `O` (the uniqueness behind Simon Ch. 6, (2.7)–(2.9), p. 136).  For `ν = ν₁ + ν₂` and the real densities `fᵢ = (dνᵢ/dν).toReal`, the Lebesgue decomposition gives `∫ c dνᵢ = ∫ fᵢ c dν` for every `c`; the fundamental lemma of the calculus of variations gives `f₁ = f₂` `ν`-a.e. on `O`, hence `f₁ b = f₂ b` `ν`-a.e.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_integrable_smooth_ext`

#### `polyhedral_approx_pairing_expansion` (L17563)

- `root.polyhedral_approximation-a1.pairing_expansion-a1` · issue #527 · PR #2131 · candidate `c4c0086a7ea3`
- **Statement and proof**: **Pairing expansion** (Simon Ch. 6, 1.2 and 1.7, pp. 132–133; used for 6.2, p. 169).  For an `n`-vector `w` and an `n`-covector `c` on `ℝ^P`, `w(c) = ∑_I c_I · w(dx^I)`, the sum over the increasing multi-indices `I`, where `c_I = c(e_{I(1)}, …, e_{I(n)})` and `dx^I = dx^{I(1)} ∧ ⋯ ∧ dx^{I(n)}`; moreover `|c_I| ≤ |c|`.  Since `dx^I(e_J) = δ_{IJ}` on increasing multi-indices, `c` and `∑_I c_I dx^I` have the same increasing coordinates, hence are equal (1.2), and `w` is linear.
- **Calls**: `polyhedral_approx_pairing_coordinate_bound`, `polyhedral_approx_pairing_covector_ext` (A.3), `polyhedral_approx_pairing_wedge_kronecker` (A.3)
- **Called by**: `polyhedral_approx_restriction_tau`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `imc_im_density_limit`

#### `deformation_im_completeness` (L47597)

- `root.deformation-a1.im_completeness-a1` · issue #1106 · PR #5258 · candidate `f58460aabccd`
- **Statement and proof**: **Completeness of integer multiplicity currents (Simon Ch. 6, Lemma 3.13, p. 149).**  If `T_j ∈ 𝒟ₖ(ℝ^N)` are integer multiplicity and `M(T − T_j) → 0`, then `T` is integer multiplicity.  Write `T_j = τ(M_j, θ_j, ξ_j)` and `κ_j := 1_{M_j} θ_j ξ_j`.  Along a subsequence with `M(T − T_{φ(p)}) < 2⁻ᵖ`, subadditivity of mass gives `M(T_{φ(p+1)} − T_{φ(p)}) ≤ 2 · 2⁻ᵖ`. As `(Hᵏ, κ_{φ(p+1)} − κ_{φ(p)})` represents `T_{φ(p+1)} − T_{φ(p)}` (2.7), the mass lower bound (printed (1)) makes `∑_p ∫ |κ_{φ(p+1)} − κ_{φ(p)}| dHᵏ` finite.  The densities then converge to an integer multiplicity triple `(M₀, θ₀, ξ₀)` with `τ(M_{φ(p)}, θ_{φ(p)}, ξ_{φ(p)})(ω) → τ(M₀, θ₀, ξ₀)(ω)` (printed (2)–(3)).  Finally `|T(ω) − T_j(ω)| ≤ c · M(T − T_j) → 0` whenever `|ω| ≤ c`, so `T = τ(M₀, θ₀, ξ₀)`.
- **Calls**: `ltg_tau_integrable` (A.5), `imc_lintegral_coordNorm_le_mass`, `imc_im_density_limit`
- **Called by**: `deformation_onto_skeleton`

#### `imc_lintegral_coordNorm_le_mass` (L24303)

- `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1` · issue #3244 · PR #4943 · candidate `c5c589901cff`
- **Statement and proof**: **Lower half of the mass formula `M(T) = ∫ |T⃗| dμ_T` (Simon Ch. 6, 2.7–2.8; display (1) in the proof of Lemma 3.13).**  If `(μ, κ)` represents `Y ∈ 𝒟_k(ℝ^N)` as in (2.7), then `∫ |κ| dμ ≤ M(Y)` in `[0, ∞]`, where `|w| = (∑_γ w(dx^γ)²)^{1/2}` is the Euclidean norm of a `k`-vector.  Let `M(Y) < ∞` and `R ∈ ℕ`.  The coordinates `κ^γ` are `μ`-integrable on `B_R`, so for `ε > 0` there is a continuous form `ω` with `tsupport ω ⊆ B_R`, `|ω| ≤ 1` and `∫_{B_R} |κ| dμ ≤ ∫ κ(ω) dμ + ε`; by (2.7) and the mass bound, `∫ κ(ω) dμ ≤ M(Y)`.  Hence `∫_{B_R} |κ| dμ ≤ M(Y)`; let `R ↑ ∞`.
- **Calls**: `cmb_rb_measureRepresentation_integrableOn_coeff` (A.1), `imc_mlb_exists_form_lintegral_coordNorm_le`, `cmb_measureRepresentation_continuous_bound` (A.1)
- **Called by**: `deformation_im_completeness`

#### `imc_mlb_exists_form_lintegral_coordNorm_le` (L10661)

- `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_form-a1` · issue #4252 · PR #4900 · candidate `f2bdf1e59b90`
- **Statement and proof**: **Polar test form for a `k`-vector field** (Simon Ch. 6, 2.6–2.8).  If the coordinates `κ^γ = κ(dx^γ)` of `κ : ℝ^N → Λ_k(ℝ^N)` are `μ`-integrable on `B = B_R(0)`, then for every `ε > 0` there is a continuous `k`-form `ω` with `tsupport ω ⊆ B` and `|ω| ≤ 1` such that `∫_B |κ| dμ ≤ ∫ κ(ω) dμ + ε`, where `|κ| = (∑_γ (κ^γ)²)^{1/2}`.  Apply `imc_mlb_exists_unit_field_integral_ge` to the coefficient field `c = (κ^γ)_γ ∈ ℝ^I` and put `ω = ∑_γ F^γ dx^γ`, so that `|ω| = |F| ≤ 1` and `κ(ω) = ⟨F, c⟩`.
- **Calls**: `imc_mlb_exists_unit_field_integral_ge`, `smr_ci_coord_sum_smul_wedge` (A.5), `smr_ci_norm_eq_sqrt_sum_coord_sq` (A.5)
- **Called by**: `imc_lintegral_coordNorm_le_mass`

#### `imc_mlb_exists_unit_field_integral_ge` (L10214)

- `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1` · issue #4241 · PR #4854 · candidate `6c052c410ac7`
- **Statement and proof**: **Polar field (Simon Ch. 6, 2.7–2.8; Steps 3, 5 and 6 of the mass lower bound).**  If `g` is `μ`-integrable on `B = B_R(0)` with values in a real inner product space, then for every `ε > 0` there is a continuous `F` with `tsupport F ⊆ B` and `‖F‖ ≤ 1` such that `⟨F, g⟩` is `μ`-integrable and `∫_B ‖g‖ dμ ≤ ∫ ⟨F, g⟩ dμ + ε`.  With `ρ = ‖g‖`, the polar field `u = g / ρ` and the finite measure `ν = ρ μ⌞B`, approximate `u` in `L¹(ν)` by a continuous compactly supported `g₀` (sibling `l1_density`) and take `F = χ · π(g₀)`, where `χ` cuts off near `∂B` and `π(a) = a / max(1, ‖a‖)` is the radial retraction onto the closed unit ball.
- **Calls**: `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le`
- **Called by**: `imc_mlb_exists_form_lintegral_coordNorm_le`

#### `imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le` (L10103)

- `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.l1_density-a1` · issue #4229 · PR #4820 · candidate `0a00d6a3533d`
- **Statement and proof**: **`L¹` density of continuous compactly supported maps for a finite measure on `ℝ^N`.**  For a finite Borel measure `ν` on `ℝ^N` and `f ∈ L¹(ν)` with values in a real normed space `E`, every `ε ≠ 0` admits a continuous compactly supported `g ∈ L¹(ν)` with `‖f - g‖_{L¹(ν)} ≤ ε` (the case `p = 1` of Mathlib's `MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, whose proof is reproduced here **[corrected]**).  Urysohn's lemma and outer regularity approximate `c • 1_s` (`s` closed, `s ⊆ u` open, `ν s < ∞`) by a continuous `L¹` map supported in `u`; inner regularity by compact closed sets treats `c • 1_t` for measurable `t` with `ν t < ∞`; and `MemLp.induction_dense` (density of simple functions) extends this to all of `L¹(ν)`, the class being closed under `+`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says that the Mathlib file is "not imported here". The final `Submission.lean` does import it, transitively: `Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral` imports `Chapter01.VectorFunctionalL1`, which imports `Chapter01.RadonDensity`, which imports `Mathlib.MeasureTheory.Function.ContinuousMapDense`. The reproduced proof does not depend on this.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_mlb_exists_unit_field_integral_ge`

#### `imc_im_density_limit` (L47189)

- `root.deformation-a1.im_completeness-a1.density_limit-a1` · issue #3307 · PR #5251 · candidate `72b1c8658981`
- **Statement and proof**: **Integer multiplicity limit of summably `L¹`-Cauchy densities (Simon Ch. 6, 3.13, printed (2)–(3), pp. 149–150).**  Let `(M_p, θ_p, ξ_p)` be rectifiable triples in `ℝ^N` with natural-valued multiplicities and densities `κ_p = 1_{M_p} θ_p ξ_p`, and suppose `∑_p ∫ |κ_{p+1} - κ_p| dHᵏ < ∞`, where `|w|² = ∑_γ w(dx^γ)²`.  Then some rectifiable triple `(M₀, θ₀, ξ₀)` with natural-valued multiplicity has `τ(M_p, θ_p, ξ_p)(ω) → τ(M₀, θ₀, ξ₀)(ω)` for every continuous compactly supported `ω`.  The coordinates `f_p = (κ_p(dx^γ))_γ` converge a.e. and in `L¹` to some `g`.  As `|ξ_p| = 1`, `‖f_p‖ = 1_{M_p} θ_p` a.e. is natural-valued, hence eventually constant, so `θ₀ = ‖g‖` is natural-valued.  Take `M₀ = {θ₀ ≥ 1}` and `ξ₀ = θ₀⁻¹ L(g)`, where `L(a) = ∑_γ a_γ e^γ` inverts the coordinates.
- **Calls**: `imc_ae_tendsto_of_summable_lintegral`, `imc_isRectifiableTriple_of_eventually_mem`, `polyhedral_approx_pairing_expansion`, `ltg_tau_integrable` (A.5)
- **Called by**: `deformation_im_completeness`

#### `imc_ae_tendsto_of_summable_lintegral` (L24356)

- `root.deformation-a1.im_completeness-a1.l1_cauchy_limit-a1` · issue #3254 · PR #4244 · candidate `08f55173c4b9`
- **Statement and proof**: Riesz–Fischer (the `L¹`-limit step in the proof of Simon Ch. 6, Lemma 3.13): if the `fₙ` are `μ`-a.e. strongly measurable with `∑ₙ ∫⁻ ‖fₙ₊₁ − fₙ‖ₑ dμ < ∞`, then `fₙ → g` `μ`-a.e. for a `μ`-a.e. strongly measurable `g`, and `∫⁻ ‖fₙ − g‖ₑ dμ → 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_im_density_limit`

#### `imc_isRectifiableTriple_of_eventually_mem` (L36264)

- `root.deformation-a1.im_completeness-a1.limit_triple-a1` · issue #3296 · PR #5176 · candidate `dfb7982325af`
- **Statement and proof**: Pointwise eventual limits of rectifiable triples are rectifiable triples (Simon Ch. 6, 3.13, last paragraph of the proof: `ξ_Q(x) ∈ Λₙ(TₓM_Q)`, `TₓM₊ = TₓM_Q` up to small measure, hence `ξ(x) ∈ Λₙ(TₓM₊)`).  With `θⱼ, θ₀ ≥ 1` the sets `Mⱼ`, `M₀` have locally finite `Hᵏ` measure. `M₀` lies in `⋃ⱼ Mⱼ` up to an `Hᵏ`-null set, so it is countably rectifiable, and `ξ₀` is the a.e. limit of `Mⱼ.indicator ξⱼ`, so it is a.e. strongly measurable.  For a.e. `x ∈ M₀ ∩ Mⱼ` a weighted tangent space of `(Mⱼ, θⱼ)` at `x` is one of `(M₀, θ₀)`: weighted and unweighted tangent spaces agree a.e. (Ch. 3, Remark 1.8(1); `imc_weightedTangent_iff_approxTangent`), and the approximate tangent spaces of `Mⱼ ∩ M₀` agree a.e. with those of `Mⱼ` and of `M₀` (`imc_approxTangent_iff_of_subset`).  At such `x`, for `j ≥ J(x)` the frames `τʲ` orienting `ξⱼ(x)` all span the unique weighted tangent space of `(M₀, θ₀)` at `x`, so `ξⱼ(x) ∈ {s, -s}` with `s = simpleNVector τᴶ` (`fiw_ims_frame_sign`); this set is closed, hence contains `ξ₀(x) = lim ξⱼ(x)`.
- **Calls**: `imc_approxTangent_iff_of_subset`, `imc_weightedTangent_iff_approxTangent`, `fiw_ims_frame_sign` (A.5)
- **Called by**: `imc_im_density_limit`

#### `imc_approxTangent_iff_of_subset` (L34563)

- `root.deformation-a1.im_completeness-a1.approx_tangent_locality-a1` · issue #3266 · PR #4498 · candidate `07759cf2463d`
- **Statement and proof**: Locality of approximate tangent spaces (Simon Ch. 3, Def. 1.4): if `E ⊆ E'` are `Hᵏ`-null-measurable and `Hᵏ(E' ∩ K) < ∞` for every compact `K`, then for `Hᵏ`-a.e. `x ∈ E` and every subspace `Q`, `Q` is the approximate tangent space of `E` at `x` iff it is that of `E'` at `x`.  By the Upper Density Theorem `Hᵏ((E' \ E) ∩ B̄_ρ(x)) = o(ρᵏ)` at such `x`, and by the dilation identity the blow-up integrals of `E` and `E'` then differ by `o(1)`.
- **Calls**: `imc_ae_zero_density_off_set`, `lpf_wtc_blowup_setIntegral_image` (A.4)
- **Called by**: `imc_isRectifiableTriple_of_eventually_mem`

#### `imc_ae_zero_density_off_set` (L34191)

- `root.deformation-a1.im_completeness-a1.zero_density-a1` · issue #3336 · PR #4313 · candidate `af9b120b0819`
- **Statement and proof**: Upper Density Theorem on `ℝ^Q` (Simon Ch. 1, 3.6, localized as in Remark 3.7(2)) for `ν = (Hⁿ ⌞ S).withDensity g`: if `S` is `Hⁿ`-null-measurable **[corrected]** and `∫⁻_{S ∩ K} g dHⁿ < ∞` for every compact `K`, then `ν(B̄_ρ(y)) / ρⁿ → 0` as `ρ → 0+` for `Hⁿ`-a.e. `y ∉ S`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the null-measurability of `S`, which the Lean statement (line 34191) assumes (Simon's Ch. 1, 3.6 likewise concerns a measurable set); see the example in the entry `lpf_wtc_ae_zero_density_off_set`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `imc_approxTangent_iff_of_subset`, `imc_weightedTangent_iff_approxTangent`

#### `imc_weightedTangent_iff_approxTangent` (L36142)

- `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1` · issue #3282 · PR #5168 · candidate `af5edcea1275`
- **Statement and proof**: Simon Ch. 3, Remark 1.8(1): for `Hᵏ`-a.e. `x ∈ E` and every subspace `Q`, `Q` is the approximate tangent space of `E` at `x` with respect to `θ` (Definition 1.7) iff it is the approximate tangent space of `E` at `x` (Definition 1.4).  Off an `Hᵏ`-null set, `x` lies in a compact Lusin piece `C ⊆ E` on which `θ` is continuous, and both `Hᵏ ⌞ (E ∖ C)` and `θ Hᵏ ⌞ (E ∖ C)` have `k`-density `0` at `x`.  Both tangent conditions then transfer between `E` and `C`.
- **Calls**: `lpf_wtc_lusin_compact_pieces` (A.4), `imc_ae_zero_density_off_set`, `lpf_wtc_tangent_transfer` (A.4), `imc_wte_approxTangent_of_weightedTangent`, `lpf_wtc_weighted_tangent_transfer` (A.4)
- **Called by**: `imc_isRectifiableTriple_of_eventually_mem`

#### `imc_wte_approxTangent_of_weightedTangent` (L34154)

- `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1.tangent_of_weighted_tangent-a1` · issue #4217 · PR #5036 · candidate `6d508b9e6a78`
- **Statement and proof**: Converse weighted transfer (Simon Ch. 3, Remark 1.8(1)): if `T` is the approximate tangent space of `M` at `y` with respect to `θ` (Def. 1.7), `C ⊆ M`, `θ|C` is continuous at `y` and `θ Hⁿ⌞(M ∖ C)` has `n`-density `0` at `y`, then `T` is the approximate tangent space of `C` at `y` (Def. 1.4).  For `φ ∈ C_c(ℝ^Q)` and small `t > 0`, `θ(y) t⁻ⁿ ∫_C φ(η_t) = t⁻ⁿ ∫_M φ(η_t) θ - t⁻ⁿ ∫_C φ(η_t) (θ - θ(y)) - t⁻ⁿ ∫_{M∖C} φ(η_t) θ`, where the first term tends to `θ(y) ∫_T φ` and the other two tend to `0`.
- **Calls**: `imc_wte_density_bound_of_weightedTangent`, `lpf_wtc_blowup_setIntegral_image` (A.4), `lpf_wtc_wtt_continuity_error_vanishes` (A.4), `lpf_wtc_wtt_remainder_vanishes` (A.4), `lpf_wtc_wtt_blowup_integral_split` (A.4)
- **Called by**: `imc_weightedTangent_iff_approxTangent`

#### `imc_wte_density_bound_of_weightedTangent` (L34042)

- `root.deformation-a1.im_completeness-a1.weighted_tangent_equiv-a1.weighted_density_bound-a1` · issue #4212 · PR #4798 · candidate `883f2ebd12d5`
- **Statement and proof**: Density bound at a weighted tangent point (Simon Ch. 3, Remark 1.8(1)): if `T` is the approximate tangent space of `M` at `y` with respect to `θ` (Definition 1.7), `θ ≥ 0` on `M`, `θ(y) > 0`, `C ⊆ M` is null-measurable with `θ|C` continuous at `y`, `Hⁿ(C ∩ B̄_r(y)) < ∞` and `θ` is `Hⁿ`-integrable on `M ∩ B̄_r(y)` for some `r > 0`, then `Hⁿ(C ∩ B̄_ρ(y)) ≤ K ρⁿ` for all sufficiently small `ρ > 0`.
- **Calls**: `lpf_wtc_blowup_setIntegral_image` (A.4)
- **Called by**: `imc_wte_approxTangent_of_weightedTangent`

#### `deformation_im_pushforward_limit` (L43187)

- `root.deformation-a1.im_pushforward_limit-a1` · issue #1111 · PR #5894 · candidate `64c17f9e467c`
- **Statement and proof**: **Lipschitz push-forward as the limit of `C¹` push-forwards** (the consistency step behind the remark after display (21) in the proof of Simon Ch. 6, 5.1), conditional on Lemma 3.9. Lemma 3.9 gives an integer multiplicity `S = g_# X` with data `(M', θ', ξ', L')`.  Both triples represent `X`, so `Hᵏ(M Δ M') = 0` and `θ = θ'`, `ξ = ξ'` `Hᵏ`-a.e. on `M` (`ltg_tau_unique_on_open`); hence the weighted tangent spaces of `(M, θ)` are those of `(M', θ')` (`br_weightedTangent_congr`) and `L'` has the derivative property on `(M, θ)`.  As `Hᵏ(M \ spt X) = 0` (`lpf_rectifiable_support_null`), `θ` is integrable on `M ∩ g⁻¹(K)` for compact `K`, and `deformation_ipl_chart_convergence` gives convergence of the `C¹` push-forward integrals to `∫_M θ ⟨ω(g), L'_# ξ⟩ dHᵏ = S(ω)`.
- **Calls**: `ltg_tau_unique_on_open`, `br_weightedTangent_congr` (A.3), `lpf_rectifiable_support_null` (A.4), `deformation_ipl_chart_convergence`
- **Called by**: `deformation_onto_skeleton`

#### `ltg_tau_unique_on_open` (L1570)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_unique_on_open-a1` · issue #1365 · PR #2158 · candidate `6e7472481f3b`
- **Statement and proof**: Uniqueness of `τ(M, θ, ξ)` on an open set (Simon Ch. 6, 3.1): if two rectifiable triples define the same current on test forms supported in an open `O ⊆ U`, then `Hᵏ((M₁ Δ M₂) ∩ O) = 0`, and `θ₁ = θ₂`, `ξ₁ = ξ₂` `Hᵏ`-a.e. on `M₁ ∩ O`.  For a covector `b`, testing with `φ b` and the fundamental lemma give `1_{M₁} θ₁ ξ₁(b) = 1_{M₂} θ₂ ξ₂(b)` a.e. on `O`; finitely many separating covectors upgrade this to `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂`, and rigidity of nonnegative multiples of unit simple `k`-vectors concludes.
- **Calls**: `ltg_tau_integrable` (A.5), `ltg_covector_separating`, `ltg_simple_unit_rigidity`
- **Called by**: `br_isIntegerMultiplicity_of_local`, `deformation_im_pushforward_limit`

#### `ltg_covector_separating` (L1485)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.covector_separating-a1` · issue #1344 · PR #1756 · candidate `e4a2285e4918`
- **Statement and proof**: Finitely many covectors separate `k`-vectors (Simon Ch. 6, §1): `Λᵏ(ℝ^P)` is finite-dimensional, and `k`-vectors (continuous linear functionals on it) agreeing on a basis agree.  Evaluation on tuples of standard basis vectors embeds `Λᵏ(ℝ^P)` linearly into `ℝ^(Fin k → Fin P)` (a multilinear map is determined by its values on basis vectors).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ltg_tau_unique_on_open`

#### `ltg_simple_unit_rigidity` (L1510)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.simple_unit_rigidity-a1` · issue #1358 · PR #1755 · candidate `100a3f23645a`
- **Statement and proof**: Nonnegative multiples of unit simple `k`-vectors are rigid (the orientations `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` of Simon Ch. 6, 3.1): if `τ, τ'` are orthonormal, `w = ±τ₁ ∧ ⋯ ∧ τₖ`, `w' = ±τ'₁ ∧ ⋯ ∧ τ'ₖ`, `a, a' ≥ 0` and `a w = a' w'`, then `a = a'`, and `w = w'` when `a ≠ 0`. Evaluate on the dual covectors `α_σ = ⟨σ₁, ·⟩ ∧ ⋯ ∧ ⟨σₖ, ·⟩`, `α_σ(v) = det(⟨σᵢ, vⱼ⟩)` (1.1): with `d = det(⟨τᵢ, τ'ⱼ⟩)`, `α_τ(τ) = α_τ'(τ') = 1` and `α_τ(τ') = α_τ'(τ) = d` give `a = a' |d|` and `a |d| = a'`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ltg_tau_unique_on_open`

#### `deformation_ipl_chart_convergence` (L42953)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1` · issue #4399 · PR #5744 · candidate `9aac4fc5a3d2`
- **Statement and proof**: Convergence of push-forward integrals under `C¹` approximation (Simon Ch. 6, proof of the Deformation Theorem, §5, p. 166: the push-forward limit behind "Q, R₁ are integer multiplicity by (19), 4.4, 4.5 and 3.13", part (I)).  Let `(M, θ, ξ)` be a rectifiable triple in `ℝ^P`, `g` be `Λ`-Lipschitz, `L(x)v` the derivative of `t ↦ g(x + tv)` at `0` along the weighted approximate tangent spaces `TₓM`, `θ` integrable on `M ∩ g⁻¹(K)` for compact `K`, and `C¹` maps `g_j` with a common Lipschitz constant `Λ'` converge uniformly to `g`.  Then for every continuous compactly supported `ω`, `∫_M θ ⟨ω(g_j), (Dg_j)_# ξ⟩ dHᵏ → ∫_M θ ⟨ω(g), L_# ξ⟩ dHᵏ`.  Once `|g_j - g| < 1`, both integrands vanish off `g⁻¹(K)`, `K` the closed `1`-neighbourhood of `spt ω`, and are bounded by `max(Λ, Λ')ᵏ ‖ω‖_∞ θ 1_{g⁻¹(K)}`.  On the disjointed `C¹` chart pieces `E_i` of `M`, one `ψ ∈ L¹(Ω_i)` gives `∫_{E_i} = ∫_{Ω_i} ψ ⟨ω(u), ∂u⟩` for `u = g_j ∘ Φ_i` and `u = g ∘ Φ_i`; these converge by weak continuity of minors, and dominated convergence over the pieces sums them.
- **Calls**: `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `lpf_countably_rectifiable_c1_cover` (A.4), `lpf_wtc_chart_image_measurable_locally_finite` (A.4), `deformation_ipl_cc_chart_integral_representation`, `lpf_chart_chain_rule` (A.4), `deformation_ipl_minor_weak_continuity`, `deformation_ipl_cc_tendsto_setIntegral_of_partition`
- **Called by**: `deformation_im_pushforward_limit`

#### `deformation_ipl_cc_pushforward_integrand_bound` (L40247)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.integrand_bound-a1` · issue #4930 · PR #5135 · candidate `015c6e0e5ba5`
- **Statement and proof**: Push-forward integrands on a rectifiable triple (Simon Ch. 6, 3.6–3.9): if `x ↦ A(x)_# ξ(x)` and `β` are `Hᵏ⌞M`-a.e.-strongly measurable and `|A(x) v| ≤ Λ |v|` on the weighted approximate tangent spaces of `(M, θ)` at `Hᵏ`-a.e. `x ∈ M`, then `θ · ⟨β, A_# ξ⟩` is `Hᵏ⌞M`-a.e.-strongly measurable and bounded by `Λᵏ ‖β‖ θ` at `Hᵏ`-a.e. point of `M`.  Measurability of `θ` comes from exhausting `U` by compact sets; the bound evaluates `β` on the frame `A(x) τ`, where `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₖ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_chart_convergence`

#### `deformation_ipl_tangential_pushforward_aestronglyMeasurable` (L40477)

- `root.deformation-a1.im_pushforward_limit-a1.pushforward_measurable-a1` · issue #4388 · PR #4893 · candidate `47253038859d`
- **Statement and proof**: Measurability of the push-forward `k`-vector field (Simon Ch. 6, (3.6), p. 147, as needed in the proof of the Deformation Theorem, §5, p. 166): for a rectifiable triple `(M, θ, ξ)` in an open `U`, a locally Lipschitz `f` and any `L` with `L(x)v = d/dt f(x + tv)|₀` on the weighted approximate tangent spaces `TₓM`, `x ↦ L(x)_# ξ(x)` is `Hᵏ⌞M`-a.e. strongly measurable.  Off an `Hᵏ`-null set, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₖ` with `span τ = TₓM = DΦ_j(w)(ℝᵏ)` for a `C¹` chart `Φ_j(w) = x` (uniqueness of `TₓM`, `θ x > 0`), so `L x` agrees on `τ` with the Borel chartwise differential `L'` of `lpf_tde_measurable_chart_differential`.
- **Calls**: `lpf_countably_rectifiable_c1_cover` (A.4), `lpf_tde_measurable_chart_differential` (A.4), `lpf_chart_chain_rule` (A.4)
- **Called by**: `deformation_ipl_chart_convergence`

#### `deformation_ipl_cc_chart_integral_representation` (L40113)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_representation-a1` · issue #4925 · PR #5175 · candidate `620950e4ff28`
- **Statement and proof**: Chart representation of push-forward integrals (steps (6a)–(6d) of the chart convergence in the C¹ push-forward limit behind the proof of Simon Ch. 6, 5.1): let `Φ` be C¹, Lipschitz and `c`-antilipschitz (`c > 0`) on the open `Ω ⊆ ℝᵏ`, and let `G ⊆ M ∩ Φ(Ω)` be `Hᵏ`-null-measurable with `θ ∈ L¹(Hᵏ ⌞ G)`.  With `D = Ω ∩ Φ⁻¹(G)` and the chart orientation sign `σ = ±1`, the weight `ψ = 1_D (θ ∘ Φ) σ` is in `L¹(Ω)` (as `JΦ ≥ cᵏ` and `∫_D (θ ∘ Φ) JΦ = ∫_G θ`), and `∫_G θ ⟨α(f), A_# ξ⟩ dHᵏ = ∫_Ω ψ ⟨α(f(Φ)), ∂₀(f ∘ Φ) ∧ ⋯ ∧ ∂ₖ₋₁(f ∘ Φ)⟩ dLᵏ` whenever `D(f ∘ Φ)(w) = A(Φ w) ∘ DΦ(w)` a.e. on `D` and the left integrand is integrable: by the signed change of variables, `JΦ(w) ξ(Φ w) = σ(w) ∂₀Φ(w) ∧ ⋯ ∧ ∂ₖ₋₁Φ(w)` and `A(Φ w) ∂_bΦ = ∂_b(f ∘ Φ)`.
- **Calls**: `deformation_ipl_cc_gram_det_lower_bound`, `lpf_wtc_cat_fderiv_lower_bound` (A.4), `deformation_ipl_cc_chart_orientation_sign`, `lpf_raf_chart_change_of_variables` (A.4), `deformation_ipl_cc_signed_change_of_variables`
- **Called by**: `deformation_ipl_chart_convergence`

#### `deformation_ipl_cc_gram_det_lower_bound` (L9708)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.gram_det_lower_bound-a1` · issue #4915 · PR #5143 · candidate `e6cf424d70b1`
- **Statement and proof**: Gram-determinant lower bound (the Jacobian bound of step 6a): if `0 ≤ c` and `c‖s‖ ≤ ‖T s‖` for all `s ∈ ℝᵏ`, then `cᵏ ≤ √det (⟪T eᵢ, T eⱼ⟫)ᵢⱼ`.  The Gram matrix is the matrix of the symmetric operator `S = T† T` in the standard basis; on an orthonormal eigenbasis `uᵢ` of `S` the eigenvalues are `⟪S uᵢ, uᵢ⟫ = ‖T uᵢ‖² ≥ c²`, and `det S` is their product.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_cc_chart_integral_representation`

#### `deformation_ipl_cc_chart_orientation_sign` (L39938)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1` · issue #4923 · PR #5146 · candidate `714635af911e`
- **Statement and proof**: Measurable relative orientation on a `C¹` antilipschitz chart (step (6c) of the accepted natural-language proof of `deformation_ipl_chart_convergence`, the `C¹` push-forward limit behind the proof of Simon Ch. 6, 5.1 **[corrected]**): for a rectifiable triple `(M, θ, ξ)` and a `C¹` map `Φ` that is antilipschitz on the open set `Ω`, there is a sign `σ = ±1`, a.e.-strongly measurable for `Lᵏ ⌞ (Ω ∩ Φ⁻¹(M))`, with `JΦ(w) ξ(Φ(w)) = σ(w) ∂₁Φ(w) ∧ ⋯ ∧ ∂ₖΦ(w)` for `Lᵏ`-a.e. `w ∈ Ω ∩ Φ⁻¹(M)`.  The sign is that of `⟨ξ(Φ(w)), β_w⟩` for the covector `β_w(u) = det (⟪∂ₐΦ(w), u_b⟫)`, continuous in `w`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Simon Ch. 6, proof of 3.9, step (6c)". The printed discussion of 3.9 (pp. 146–148) has no step (6c). Step (6c) belongs to the accepted proof of the parent node `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`, and the lemma is used only in the formal proof of 5.1.
- **Calls**: `lpf_weighted_tangent_on_c1_chart` (A.4), `lpf_ccr_ae_pullback` (A.4), `lpf_simple_nvector_algebra` (A.4)
- **Called by**: `deformation_ipl_cc_chart_integral_representation`

#### `deformation_ipl_cc_signed_change_of_variables` (L39846)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.signed_change_of_variables-a1` · issue #4918 · PR #5112 · candidate `81af8e83cfa0`
- **Statement and proof**: Signed change of variables along an injective Lipschitz chart (Simon Ch. 3, 2.6; used for the `C¹` push-forward limit behind the proof of Ch. 6, 5.1 **[corrected]**): if `Φ` is Lipschitz and `c`-antilipschitz on the open set `Ω`, `A ⊆ Φ(Ω)` is `Hᵏ`-null-measurable and `h` is `Hᵏ`-integrable on `A`, then `h(Φ(w)) JΦ(w)` is `Lᵏ`-integrable on `D = Ω ∩ Φ⁻¹(A)` and `∫_A h dHᵏ = ∫_D h(Φ(w)) JΦ(w) dLᵏ(w)`.  This is the `[0, ∞]`-valued change of variables applied to the positive and negative parts of `h` and to `|h|`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "used for Ch. 6, 3.9". Its only user is `deformation_ipl_cc_chart_integral_representation`, in the formal proof of 5.1.
- **Calls**: `lpf_raf_chart_change_of_variables` (A.4)
- **Called by**: `deformation_ipl_cc_chart_integral_representation`

#### `deformation_ipl_minor_weak_continuity` (L42839)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1` · issue #4382 · PR #5553 · candidate `ddc5e2e91796`
- **Statement and proof**: **Weak continuity of `ψ · α(u)(∂₀u, …, ∂_{k−1}u)`** (weak continuity of Jacobian minors; used for Lipschitz push-forwards as limits of C¹ push-forwards in the proof of Simon Ch. 6, 5.1, remark after (21)).  By the covector expansion and `wedgeCovectors_apply_det`, `α(y)(∂₀u, …, ∂_{k−1}u) = ∑_γ α_γ(y) M_γ(Du)` with `α_γ = euclideanCovectorCoordinate (α ·) γ` and `M_γ(Du) = det(∂_s u^{γ t})`.  Each summand `ψ (α_γ ∘ u) M_γ(Du)` is integrable on `Ω`: `α_γ` is continuous with compact support, and `‖Du‖ ≤ C` on the open set `Ω` gives `|M_γ(Du)| = |dy^γ(Du e₀, …, Du e_{k−1})| ≤ ‖dy^γ‖ Cᵏ` there.  Each summand converges by `deformation_ipl_mwc_coeff_minor_continuity` with `g = α_γ`, `r = k`, `a = γ`, `b = id`.
- **Calls**: `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `deformation_ipl_mwc_coeff_minor_continuity`
- **Called by**: `deformation_ipl_chart_convergence`

#### `deformation_ipl_mwc_coeff_minor_continuity` (L42710)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.coeff_minor_continuity-a1` · issue #4965 · PR #5542 · candidate `398fc995d0bc`
- **Statement and proof**: Weak continuity of the Jacobian minors `M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}` against a coefficient `ψ (g ∘ u)`, `ψ ∈ L¹(Ω)`, `g ∈ C_c(ℝ^Q)` (step 2 of the proof of `minor_weak_continuity`).  With `η = ψ (g ∘ u₀) ∈ L¹(Ω)`, `∫_Ω ψ (g ∘ u_j) M_{a,b}(u_j) = ∫_Ω ψ (g ∘ u_j - g ∘ u₀) M_{a,b}(u_j) + ∫_Ω η M_{a,b}(u_j)`; the first term tends to `0` because `|M_{a,b}(u_j)| ≤ r! C^r` on `Ω` and `g ∘ u_j → g ∘ u₀` uniformly on `Ω`, the second tends to `∫_Ω η M_{a,b}(u₀)` by `minor_weak_star`.
- **Calls**: `deformation_ipl_mwc_minor_weak_star`
- **Called by**: `deformation_ipl_minor_weak_continuity`

#### `deformation_ipl_mwc_minor_weak_star` (L42469)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_weak_star-a1` · issue #4960 · PR #5516 · candidate `68685c48420b`
- **Statement and proof**: Weak-* continuity of the Jacobian minors (step 3 of the proof of `minor_weak_continuity`; J. M. Ball, ARMA 63 (1977); Fonseca–Leoni–Malý, ARMA 178 (2005)).  Let `v_j, v₀` be `C`-Lipschitz on the open set `Ω` with `v_j → v₀` uniformly on `Ω`, and let `M_{a,b}(u) = det (⟨e_{a t}, Du (e_{b s})⟩)_{t,s}` be the `r × r` minor with rows `a` and columns `b`.  Then `∫_Ω η M_{a,b}(v_j) → ∫_Ω η M_{a,b}(v₀)` for every `η ∈ L¹(Ω)`. Induction on `r`; for `r = 0` both sides equal `∫_Ω η`.  For `r + 1`, `‖Du‖ ≤ C` on `Ω` gives `|M_{a,b}(u)| ≤ (r+1)! C^{r+1}` there, so by `test_density` it suffices to test against `φ ∈ C¹_c(Ω)`.  By `minor_ibp_lipschitz`, `∫_Ω φ M_{a,b}(u) = -∑_q ∫_Ω u^{a 0} (-1)^q M_{a',b^{(q)}}(u) ∂_{b q} φ` with `a' = a ∘ succ`, `b^{(q)} = b ∘ q.succAbove`.  In each term the part carrying `v_j^{a 0} - v₀^{a 0} → 0` (uniformly on `Ω`, while `|M_{a',b^{(q)}}| ≤ r! C^r`) tends to `0`, and the induction hypothesis applies to the rest, tested against `η_q = v₀^{a 0} ∂_{b q} φ ∈ L¹(Ω)`.
- **Calls**: `deformation_ipl_mwc_test_density`, `deformation_ipl_mwc_minor_ibp_lipschitz`
- **Called by**: `deformation_ipl_mwc_coeff_minor_continuity`

#### `deformation_ipl_mwc_test_density` (L42408)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1` · issue #4952 · PR #5304 · candidate `0b52fed5b073`
- **Statement and proof**: Smooth test functions suffice (step (3.0) of the proof of `minor_weak_continuity`): if `Ω ⊆ ℝᵏ` is open, `|f_j|, |f₀| ≤ B` on `Ω` and `∫_Ω φ f_j → ∫_Ω φ f₀` for every `φ ∈ C¹_c(Ω)`, then `∫_Ω η f_j → ∫_Ω η f₀` for every `η ∈ L¹(Ω)`.  Given `δ > 0`, choose `ε > 0` with `2 |B| ε ≤ δ / 2` and, by `scalar_smooth_dense`, `φ ∈ C_c^∞(Ω)` with `∫_Ω |η − φ| < ε`.  Then `|∫_Ω η g − ∫_Ω φ g| ≤ |B| ∫_Ω |η − φ| ≤ |B| ε` for `g = f_j, f₀`, so for large `j` `|∫_Ω η f_j − ∫_Ω η f₀| ≤ |B| ε + |∫_Ω φ f_j − ∫_Ω φ f₀| + |B| ε < δ`.
- **Calls**: `deformation_ipl_mwc_td_scalar_smooth_dense`
- **Called by**: `deformation_ipl_mwc_minor_weak_star`

#### `deformation_ipl_mwc_td_scalar_smooth_dense` (L40714)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1.scalar_dense-a1` · issue #5161 · PR #5291 · candidate `f4c5e5ae53d1`
- **Statement and proof**: `C_c^∞(Ω)` is dense in `L¹(Ω)` for real functions: for `Ω ⊆ ℝᵏ` open, `η` integrable on `Ω` and `ε > 0` there is a smooth `φ` with compact support, `spt φ ⊆ Ω` and `∫_Ω |η − φ| < ε`.  For `k = 0` the space is a point, so `Ω = ∅` (take `φ = 0`) or `Ω = ℝ⁰` (take `φ = η`, a constant). For `k ≥ 1` the field `c = η e₀` is approximated by `b` (`slicing_im_ll_gws_smooth_dense`) and `φ = b₀` is its first coordinate, so `|η − φ| = |(c − b)₀| ≤ |c − b|`.
- **Calls**: `slicing_im_ll_gws_smooth_dense` (A.5)
- **Called by**: `deformation_ipl_mwc_test_density`

#### `deformation_ipl_mwc_minor_ibp_lipschitz` (L42282)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1` · issue #4947 · PR #5497 · candidate `9d1268ce22ea`
- **Statement and proof**: **Integration by parts for the Jacobian minors of a Lipschitz map** (the divergence form of the minors; cf. J. M. Ball, ARMA 63 (1977)).  Let `v` be `C`-Lipschitz on the open set `Ω`, `φ ∈ C¹_c(Ω)`, `M = det (∂_{b s} v^{a t})_{t,s}` the `(r+1) × (r+1)` minor with rows `a` and columns `b`, and `C_q = (-1)^q det (∂_{b (q.succAbove s)} v^{a t.succ})_{t,s}` its cofactors along the first row.  Then `∫_Ω φ M = -∑_q ∫_Ω v^{a 0} C_q ∂_{b q} φ`. Extend each coordinate `v^c|_Ω` to a `C`-Lipschitz `ṽ^c` on `ℝ^k` (McShane) and mollify it (`lipschitz_smooth_approx`): `G^c_m` is `C^∞` and `C`-Lipschitz, `G^c_m → ṽ^c` uniformly and `DG^c_m → Dṽ^c` a.e.  The identity holds on `ℝ^k` for the rows `G^{a t}_m` (`minor_ibp_smooth`); the matrix entries are bounded by `C` and converge a.e., and the scalar factors are dominated by `|φ|` resp. `(|ṽ^{a 0}| + 1) |∂_{b q} φ|` for large `m`, so it passes to the limit (`mil_tendsto_integral_mul_det`).  Finally `Dṽ^c = proj_c ∘ Dv` a.e. on `Ω` (`mil_ae_fderiv_eq_proj`), `ṽ^c = v^c` on `Ω`, and every integrand vanishes off `tsupport φ ⊆ Ω`.
- **Calls**: `deformation_ipl_mwc_lipschitz_smooth_approx`, `deformation_ipl_mwc_minor_ibp_smooth`, `deformation_ipl_mwc_mil_tendsto_integral_mul_det`, `deformation_ipl_mwc_mil_ae_fderiv_eq_proj`
- **Called by**: `deformation_ipl_mwc_minor_weak_star`

#### `deformation_ipl_mwc_lipschitz_smooth_approx` (L42146)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.lipschitz_smooth_approx-a1` · issue #4938 · PR #5189 · candidate `c2e5d50b952a`
- **Statement and proof**: **Smooth approximation of a Lipschitz function with a.e. convergent derivatives** (mollification).  Let `ψ_m` be the kernels of `constancy_mdc_smooth_approx_identity_ae_tendsto` and `G_m(x) = ∫ ψ_m(y) g(x − y) dy = (ψ_m ⋆ g)(x)`.  Then `G_m` is `C^∞`, `L`-Lipschitz (an average of translates of `g`), and `|G_m − g| ≤ 2L/(m+1)` by `slicing_mb_sa_mollify_lipschitz_close`.  Differentiating under the integral sign (`slicing_mb_sa_mollify_lipschitz_hasFDerivAt`), `DG_m(x) e_b = (∂_b g ∗ ψ_m)(x)`, which tends to `∂_b g(x)` for a.e. `x` because `∂_b g` is bounded and measurable; as `‖T‖ ≤ Σ_b |T e_b|` for `T : ℝ^k →L[ℝ] ℝ`, `DG_m(x) → Dg(x)` for a.e. `x`.
- **Calls**: `constancy_mdc_smooth_approx_identity_ae_tendsto` (A.2), `slicing_mb_sa_mollify_lipschitz_close` (A.5), `slicing_mb_sa_mollify_lipschitz_hasFDerivAt` (A.5)
- **Called by**: `deformation_ipl_mwc_minor_ibp_lipschitz`

#### `deformation_ipl_mwc_minor_ibp_smooth` (L41051)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1` · issue #4932 · PR #5478 · candidate `58585f8d0e41`
- **Statement and proof**: Integration by parts for Jacobian minors of `C²` functions (step (3.2)(ii) of the weak continuity of Jacobian minors behind the Lipschitz push-forward limits in the proof of the Deformation Theorem, Simon Ch. 6, 5.1): for `C²` functions `V₀, …, V_r : ℝᵏ → ℝ`, directions `b : Fin (r + 1) → Fin k` and `φ ∈ C¹_c(ℝᵏ)`, with `A = (∂_{b(s)} V_t)_{t,s}` and the signed first-row cofactors `C_q = (-1)^q det(∂_{b(q.succAbove s)} V_{t+1})_{t,s}`, `∫ φ det A = -∑_q ∫ V₀ C_q ∂_{b(q)} φ`. Laplace expansion along row `0` gives `det A = ∑_q ∂_{b(q)} V₀ · C_q`.  The directional derivative `∂_{b(q)}(V₀ φ C_q)` of the compactly supported `C¹` function `V₀ φ C_q` has integral `0`, and the product rule turns this into `∫ ∂_{b(q)} V₀ φ C_q = -∫ V₀ ∂_{b(q)} φ C_q - ∫ V₀ φ ∂_{b(q)} C_q`. Summing over `q`, the last terms cancel by the Piola identity `∑_q ∂_{b(q)} C_q = 0`.
- **Calls**: `deformation_ipl_mwc_mis_det_contDiff`, `deformation_ipl_mwc_mis_integral_fderiv_eq_zero`, `deformation_ipl_mwc_piola_identity`
- **Called by**: `deformation_ipl_mwc_minor_ibp_lipschitz`

#### `deformation_ipl_mwc_mis_det_contDiff` (L40872)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.det_contdiff-a1` · issue #5256 · PR #5389 · candidate `d91c70c26b54`
- **Statement and proof**: **The determinant of a matrix of `C^m` functions is `C^m`.**  Let `M t s : ℝᵏ → ℝ` (`t, s : Fin n`) be `C^m` for some `m : WithTop ℕ∞` (finite, `∞` or `ω`).  Then `w ↦ det (M t s w)ₜₛ` is `C^m`.  By the Leibniz formula `det A = ∑_σ sign σ · ∏ᵢ A (σ i) i`, this function is a finite sum, over the permutations `σ` of `Fin n`, of constant multiples of finite products of entries (for `n = 0` it is the constant `1`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_minor_ibp_smooth`

#### `deformation_ipl_mwc_mis_integral_fderiv_eq_zero` (L40849)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_smooth-a1.integral_fderiv_zero-a1` · issue #5253 · PR #5381 · candidate `f755fa9355f6`
- **Statement and proof**: **A directional derivative of a compactly supported `C¹` function has integral `0`.**  For `h : ℝᵏ → ℝ` of class `C¹` with compact support and `e ∈ ℝᵏ`, `∫ Dh(w)(e) dw = 0`, where `Dh(w) = fderiv ℝ h w`.  `h` is Lipschitz, so integration by parts for Lipschitz functions against the constant function `1` gives `∫ ∂ₑ1 · h = ∫ ∂₋ₑh · 1`.  The left side vanishes and, `h` being differentiable, `∂₋ₑh(w) = Dh(w)(-e) = -Dh(w)(e)`, so the right side is `-∫ Dh(w)(e) dw`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_minor_ibp_smooth`

#### `deformation_ipl_mwc_piola_identity` (L40996)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1` · issue #4929 · PR #5454 · candidate `a4988d1a63a2`
- **Statement and proof**: Piola identity (step (3.2)(i) of the proof of `minor_weak_continuity`; Evans, PDE, §8.1.4(b), Lemma 1): for `C²` functions `W_0, …, W_{r-1}` on `ℝ^k` and `b : Fin (r + 1) → Fin k`, the signed minors `c_q = (-1)^q det (∂_{b (q.succAbove s)} W_t)_{t,s}` satisfy `∑_q ∂_{b q} c_q = 0`. By the cofactor formula `c_q = ∑_{σ 0 = q} sgn σ ∏_t ∂_{b (σ t.succ)} W_t` and the product rule, `∑_q ∂_{b q} c_q = ∑_σ sgn σ ∑_u H_u(σ 0, σ u.succ) ∏_{t ≠ u} ∂_{b (σ t.succ)} W_t` with `H_u(i, j) = ∂_{b i} ∂_{b j} W_u`; this vanishes since `H_u` is symmetric (Schwarz) and `σ ↦ σ * swap 0 u.succ` changes the sign.
- **Calls**: `deformation_ipl_mwc_pi_hessian_symm`, `deformation_ipl_mwc_pi_cofactor_leibniz`, `deformation_ipl_mwc_pi_fderiv_sum_prod`, `deformation_ipl_mwc_pi_swap_cancel`
- **Called by**: `deformation_ipl_mwc_minor_ibp_smooth`

#### `deformation_ipl_mwc_pi_hessian_symm` (L40921)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.hessian_symm-a1` · issue #5224 · PR #5344 · candidate `d4b83da466bf`
- **Statement and proof**: Schwarz symmetry of mixed directional second derivatives of a `C²` function on `ℝ^k`: `∂_v (∂_u f)(x) = ∂_u (∂_v f)(x)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_piola_identity`

#### `deformation_ipl_mwc_pi_cofactor_leibniz` (L40891)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.cofactor_leibniz-a1` · issue #5212 · PR #5438 · candidate `2e78567bf521`
- **Statement and proof**: Signed first-row cofactors as restricted Leibniz sums: `(-1)^q` times the minor of the `r × (r + 1)` array `N` with column `q` deleted is the sum of `sgn σ * ∏ t, N t (σ t.succ)` over the permutations `σ` of `Fin (r + 1)` with `σ 0 = q`.  Both sides are the determinant of the matrix with row `0` equal to `Pi.single q 1` and row `t.succ` equal to `N t`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_piola_identity`

#### `deformation_ipl_mwc_pi_fderiv_sum_prod` (L40938)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.fderiv_sum_prod-a1` · issue #5234 · PR #5394 · candidate `6ede8508d558`
- **Statement and proof**: Product rule for a weighted sum of finite products: if every `g i t` is differentiable at `w`, the derivative of `x ↦ ∑ i, a i * ∏ t, g i t x` at `w` in direction `v` is `∑ i, a i * ∑ u, fderiv ℝ (g i u) w v * ∏ t ≠ u, g i t w`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_piola_identity`

#### `deformation_ipl_mwc_pi_swap_cancel` (L40956)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.piola_identity-a1.swap_cancel-a1` · issue #5243 · PR #5358 · candidate `250d1c58c63b`
- **Statement and proof**: Algebraic core of the Piola identity: an alternating sum over permutations against a kernel `H u` symmetric in its two arguments vanishes, since `σ ↦ σ * swap 0 u.succ` reverses the sign, exchanges the two arguments of `H u` and fixes every other factor.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_piola_identity`

#### `deformation_ipl_mwc_mil_tendsto_integral_mul_det` (L40786)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.det_dominated_convergence-a1` · issue #5187 · PR #5323 · candidate `a145fda2dac3`
- **Statement and proof**: **Dominated convergence for `h_m · det A_m`.**  If the entries of `A_m(x)` are bounded by `C`, `|h_m| ≤ H` with `H` integrable for all large `m`, and `h_m → h₀`, `A_m → A₀` entrywise `μ`-a.e., then `∫ h_m det A_m dμ → ∫ h₀ det A₀ dμ`.  Dominated convergence with the bound `H · n! Cⁿ` (`deformation_ipl_mwc_mil_abs_det_le`); `det A_m` is a.e.-strongly measurable by the Leibniz formula and `det` is continuous in the entries.
- **Calls**: `deformation_ipl_mwc_mil_abs_det_le`
- **Called by**: `deformation_ipl_mwc_minor_ibp_lipschitz`

#### `deformation_ipl_mwc_mil_abs_det_le` (L40760)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.abs_det_le-a1` · issue #5182 · PR #5282 · candidate `d3a1d7652945`
- **Statement and proof**: Leibniz bound for determinants: if every entry of a real `n × n` matrix satisfies `|A i j| ≤ c`, then `|det A| ≤ n! · cⁿ`.  Expand `det A = ∑_σ sgn(σ) • ∏_i A (σ i) i`, apply the triangle inequality, drop the sign `±1`, bound each product of `n` entries by `cⁿ`, and count the `n!` permutations of `Fin n`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_mil_tendsto_integral_mul_det`

#### `deformation_ipl_mwc_mil_ae_fderiv_eq_proj` (L40823)

- `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.minor_ibp_lipschitz-a1.ae_fderiv_extension-a1` · issue #5191 · PR #5357 · candidate `b42e6549be1d`
- **Statement and proof**: A.e. derivative of a coordinate of a Lipschitz map (the Rademacher step, steps 6(a)–(b), of the accepted natural-language proof of the Lipschitz minor integration by parts `deformation_ipl_mwc_minor_ibp_lipschitz`, used for the `C¹` push-forward limit behind the proof of Simon Ch. 6, 5.1 **[corrected]**): if `v : ℝᵏ → ℝ^Q` is `C`-Lipschitz on an open `Ω` and `g = v^c := proj_c ∘ v` on `Ω`, then for Lebesgue-a.e. `w ∈ Ω`, `Dg(w) x = proj_c (Dv(w) x)` for every `x`.  By Rademacher's theorem `v` is differentiable within `Ω` at a.e. `w ∈ Ω`, hence at `w` as `Ω` is open; `g` and `v^c` agree near `w`, so they have the same `fderiv`, which is `proj_c ∘L Dv(w)` by the chain rule.  No regularity of `g` is needed.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), places this step "in the proof of Simon Ch. 6, 3.9". The printed discussion of 3.9 (pp. 146–148) uses the area formula and contains no integration by parts of Jacobian minors; the lemma serves the formal proof of 5.1.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_mwc_minor_ibp_lipschitz`

#### `deformation_ipl_cc_tendsto_setIntegral_of_partition` (L40325)

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.partition_tannery-a1` · issue #4937 · PR #5121 · candidate `2cd5968b05f4`
- **Statement and proof**: Dominated convergence over a countable partition (Tannery's theorem): if `S = ⋃ E i` a.e. for pairwise disjoint null-measurable `E i`, `|f j| ≤ G` eventually in `j` and `|f₀| ≤ G` a.e. on `S` with `G` integrable on `S`, and `∫_{E i} f j → ∫_{E i} f₀` for every `i`, then `∫_S f j → ∫_S f₀`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_ipl_chart_convergence`

#### `deformation_retraction` (L7633)

- `root.deformation-a1.retraction-a1` · issue #1102 · PR #4797 · candidate `4fe470f2bf44`
- **Statement and proof**: **Simon Ch. 6, Lemma 5.4 (p. 160).**  For `a ∈ B_{1/4}(q)`, `q = (1/2, …, 1/2)`, there is `ψ : ℝ^d → ℝ^d` mapping `ℝ^d ∖ L_{ℓ−1}(a)` into the lattice `(m+1)`-skeleton and every closed unit cube `z + [0, 1]^d` into itself off `L_{ℓ−1}(a)`, which is `c / σ`-Lipschitz on `{dist(·, L_{ℓ−1}(a)) ≥ σ}` for `0 < σ ≤ 1/4`.  Printed proof (pp. 161–163): the radial retraction `ψ₀` of `[0, 1]^d ∖ L_{ℓ−1}(a)` with pointwise Lipschitz constant `c₁ / dist(x, L_{ℓ−1}(a))` (claim (3)), its periodic extension `ψ(z + x) = z + ψ₀(x)`, and the passage from pointwise to Lipschitz bounds.
- **Calls**: `deformation_retraction_cube_core`, `deformation_retraction_globalize`, `deformation_retraction_periodic_extension`, `deformation_retraction_skeleton_mem`
- **Called by**: `deformation_onto_skeleton`

#### `deformation_retraction_cube_core` (L7233)

- `root.deformation-a1.retraction-a1.cube_core-a1` · issue #2515 · PR #4661 · candidate `8d2377f428a0`
- **Statement and proof**: **Simon Ch. 6, Lemma 5.4, printed proof pp. 161–163: the radial retraction of the unit cube.** For `1/4 < aᵢ < 3/4` there is `ψ₀` mapping `C ∖ L_{ℓ−1}(a)`, `C = [0, 1]^d`, into `C` with `ℓ` coordinates in `{0, 1}` (α), compatible with integer translations inside `C` (β), and `c₁ / dist(x, L_{ℓ−1}(a))`-Lipschitz at every `x` within `C ∖ L_{ℓ−1}(a)` (γ, claim (3)), with `c₁ = c₁(m, ℓ)` chosen before `a`.  `ψ₀ = ψ^{(n+1)} ∘ ⋯ ∘ ψ^{(d)}` is the composite of the radial retractions `ψ_F` of the faces of `C`; claim (3) holds for every map with its structural properties (S1) (`ψ₀` fixes the points of `C ∖ L_{ℓ−1}(a)` with `ℓ` coordinates in `{0, 1}`) and (S2) (`ψ₀ = ψ₀ ∘ ψ_F` on `F ∖ L_{ℓ−1}(a)` for every face `F` of dimension `≥ m + 2`).
- **Calls**: `dr_cc_pointwise_lip`, `dr_cc_construction`
- **Called by**: `deformation_retraction`

#### `dr_cc_pointwise_lip` (L7012)

- `root.deformation-a1.retraction-a1.cube_core-a1.pointwise_lip-a1` · issue #3620 · PR #4513 · candidate `73bb3e057914`
- **Statement and proof**: Simon Ch. 6, Lemma 5.4, claim (3) (pp. 162–163), as a pointwise upper Lipschitz bound.  Let `ψ₀` satisfy (S1) (`ψ₀ x = x` on `C ∖ La` where `ℓ` coordinates lie in `{0, 1}`) and (S2) (on each face of dimension `≥ m + 2`, `ψ₀` is constant along the rays from its centre `c` up to its boundary).  Then near `x ∈ C ∖ La`, `|ψ₀ x' - ψ₀ x| ≤ (c₁ / dist(x, La) + ε) |x' - x|`. Induction on the dimension `j` of the faces `F` of `C = [0,1]^d`, with `c₁(j) = β r q^(j - (m + 2))`, `r = √d`, `β = 1 + 4r`, `q = 4rβ`.  On `F ∖ La`, `ψ₀ = ψ₀ ∘ g` for the radial projection `g` from `c` onto `∂F` (S2).  For `j = m + 2`, `ψ₀ = g` there (S1).  For `j + 1`, the bound at `g x` on the facets through `g x` glues to `∂F ∖ La` and composes with that of `g`.  Finally `dist(g x, La) ≥ min(1/4, s dist(x, La))` turns `β s c₁(j) / dist(g x, La)` into `c₁(j + 1) / dist(x, La)`.
- **Calls**: `dr_cc_skeleton_facts`, `dr_cc_radial_map`, `dr_cc_lip_at_union`, `dr_cc_lip_at_comp`, `dr_cc_similarity_bound`
- **Called by**: `deformation_retraction_cube_core`

#### `dr_cc_skeleton_facts` (L6208)

- `root.deformation-a1.retraction-a1.cube_core-a1.skeleton_facts-a1` · issue #3606 · PR #4312 · candidate `7e104d9d661f`
- **Statement and proof**: Simon Ch. 6, Lemma 5.4, proof p. 161, displays (1) and (2): elementary facts on the dual skeleton `La = {y : y_i − a_i ∈ ℤ for m + 2 indices i}` of a point `a ∈ (1/4, 3/4)^d`. `La` is a finite union of finite intersections of the closed sets `{y : y_i − a_i ∈ ℤ}`, hence closed; a point agreeing with `a` on `m + 2` coordinates lies in `La`; and if `y ∈ La ∩ [0,1]^d` lies on the ray from the centre `c` of a face of `[0,1]^d` (free coordinates `J`) through `x`, then each witness coordinate `i` of `y` has `y_i − a_i ∈ (−1, 1) ∩ ℤ = {0}`, so `i ∈ J` (else `a_i = y_i = c_i ∈ {0, 1}`) and `x_i = a_i` as `s > 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dr_cc_construction`, `dr_cc_pointwise_lip`

#### `dr_cc_radial_map` (L6788)

- `root.deformation-a1.retraction-a1.cube_core-a1.radial_map-a1` · issue #3616 · PR #4298 · candidate `017a76d5ee3d`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 5.4: the radial retraction `ψ_F` with origin `c` (p. 161) of `F = {x ∈ [0,1]^D : xᵢ = cᵢ (i ∉ J)}` onto its relative boundary, with its pointwise Lipschitz bound (printed (8), p. 163).  Here `g(x) = c + N(x - c)⁻¹ • (x - c)` for the gauge `N(v) = max_{i ∈ J} max (vᵢ/(1 - aᵢ)) (-vᵢ/aᵢ)`, and `s = N(x - c)⁻¹`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dr_cc_pointwise_lip`

#### `dr_cc_lip_at_union` (L6676)

- `root.deformation-a1.retraction-a1.cube_core-a1.lip_at_union-a1` · issue #3599 · PR #4287 · candidate `9fe3ea843dee`
- **Statement and proof**: Union rule for pointwise upper Lipschitz bounds (used for Simon Ch. 6, Lemma 5.4, p. 162, where `y` may lie on several closed faces): if `g` is `K`-Lipschitz at `y` within `G k ∩ B` for every closed piece `G k ∋ y`, and `B ⊆ ⋃ k, G k` with finitely many pieces, then `g` is `K`-Lipschitz at `y` within `B`.  Pieces missing `y` stay a positive distance away from `y`, and the minimum of finitely many radii is a common radius.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dr_cc_pointwise_lip`

#### `dr_cc_lip_at_comp` (L6645)

- `root.deformation-a1.retraction-a1.cube_core-a1.lip_at_comp-a1` · issue #3593 · PR #4314 · candidate `947cb45aeb45`
- **Statement and proof**: Simon Ch. 6, Lemma 5.4, proof p. 163 ("by (7), (8) and the chain rule"), pointwise form: if `f` is `K₁`-Lipschitz at `x` within `A`, `f` maps `A` into `B`, and `g` is `K₂`-Lipschitz at `f x` within `B`, then `g ∘ f` is `K₁ K₂`-Lipschitz at `x` within `A`.  With `η = min{1, ε/(K₁ + K₂ + 1)}` and `δ = min{δ₁, δ₂/(K₁ + η)}` one gets `(K₂ + η)(K₁ + η) = K₁K₂ + η(K₁ + K₂ + η) ≤ K₁K₂ + ε`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dr_cc_pointwise_lip`

#### `dr_cc_similarity_bound` (L6705)

- `root.deformation-a1.retraction-a1.cube_core-a1.similarity_bound-a1` · issue #3614 · PR #4342 · candidate `0d6109c0ff96`
- **Statement and proof**: Simon Ch. 6, Lemma 5.4, displays (4)–(7) (corrected similarity bound): if `y ∈ [0,1]^d` lies on the ray `y = c + s(x - c)` from a face centre `c` (with `c_i = a_i` on `J`, `c_i ∈ {0,1}` and `x_i = c_i` off `J`), then `min{1/4, s·dist(x, La)} ≤ dist(y, La)`; here `1/4 < a_i < 3/4` for all `i` **[corrected]**.  A point `w ∈ La`, `w_i = a_i + k_i` (`k_i ∈ ℤ`) on its witness set, either has a witness coordinate `i` with `|y_i − w_i| > 1/4` (if `i ∉ J`, then `y_i = c_i ∈ {0, 1}`, which is `1/4`-far from `a_i + ℤ`; if `k_i ≠ 0`, then `w_i` is `1/4`-far from `[0, 1]`), or all its witness coordinates are free with zero shift **[corrected]**, and then `w' = c + s⁻¹(w - c) ∈ La` and `y - w = s(x - w')`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), states a dichotomy that misses the case of a free witness coordinate with a nonzero shift `k_i`, where `y_i` may lie in `a_i + ℤ`; there `|y_i − w_i| > 1/4` because `w_i = a_i + k_i` lies outside `(−1/4, 5/4)`. The range `1/4 < a_i < 3/4`, a hypothesis of the Lean statement (line 6705) on which this argument rests, is also stated now. The Lean proof treats the three cases separately (the three cases begin at lines 6722, 6748 and 6765).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `dr_cc_pointwise_lip`

#### `dr_cc_construction` (L6262)

- `root.deformation-a1.retraction-a1.cube_core-a1.construction-a1` · issue #3618 · PR #4505 · candidate `3bac61695a8d`
- **Statement and proof**: Simon Ch. 6, Lemma 5.4, printed proof p. 161 (book `n = m + 1`), in the one-step form `ψ₀ = R^ℓ`.  A point `y ∈ C ∖ La` whose carrier `J(y) = {i : 0 < yᵢ < 1}` has at least `m + 2` elements is pushed radially from the centre `a_F` of its carrier face `F` onto `∂F`, `R(y)ᵢ = aᵢ + (yᵢ - aᵢ) / N(y)` on `J(y)`, with the gauge `N(y) = max_{i ∈ J(y)} max ((yᵢ - aᵢ) / (1 - aᵢ), (aᵢ - yᵢ) / aᵢ)`; `R` fixes every other point. Each step stays in `C ∖ La` (cone property of `dr_cc_skeleton_facts`) and lowers `|J(y)|`, so `R^ℓ` maps `C ∖ La` into the `(m+1)`-skeleton (α) and fixes the `(m+1)`-skeleton (S1); `R` commutes with integer translations (β); and the exit point `y` of the ray from `a_F` through `x ∈ F ∖ La` is `R(x)` or `x` itself (S2).
- **Calls**: `dr_cc_skeleton_facts`
- **Called by**: `deformation_retraction_cube_core`

#### `deformation_retraction_globalize` (L7340)

- `root.deformation-a1.retraction-a1.globalize-a1` · issue #2542 · PR #3567 · candidate `4c4af507c405`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 5.4 (local to global Lipschitz bounds): if `ψ` maps each closed unit cube `z + [0, 1]^N` into itself off `L` and has pointwise Lipschitz constant `c₁ / dist(x, L)` inside each such cube, then `ψ` is `c / σ`-Lipschitz on `{x | σ ≤ dist(x, L)}` for `0 < σ ≤ 1/4`, with `c = max (2 c₁) (1/4 + 4 √N)`.  Far pairs use `|ψ y - y| ≤ √N`; for near pairs the segment stays in `{σ / 2 < dist(·, L)}` and `deformation_retraction_dini_segment` integrates the bound.
- **Calls**: `deformation_retraction_dini_segment`
- **Called by**: `deformation_retraction`

#### `deformation_retraction_dini_segment` (L860)

- `root.deformation-a1.retraction-a1.dini_segment-a1` · issue #2488 · PR #3340 · candidate `9d7e85746c1d`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 5.4 (pointwise bounds integrate along segments): if every point of `[0, 1]` has pointwise upper Lipschitz constant at most `K` for `γ`, then `‖γ 1 - γ 0‖ ≤ K`. For `ε > 0`, continuous induction shows `‖γ s - γ 0‖ ≤ (K + ε) s` on `[0, 1]`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_retraction_globalize`

#### `deformation_retraction_periodic_extension` (L7249)

- `root.deformation-a1.retraction-a1.periodic_extension-a1` · issue #2530 · PR #3483 · candidate `99d239abdb3f`
- **Statement and proof**: Simon Ch. 6, proof of Lemma 5.4 (p. 161): the periodic extension `ψ(z + x) = z + ψ₀(x)` of a map `ψ₀` on `C ∖ La`, `C = [0,1]^d`, satisfying (α) `ψ₀(C ∖ La) ⊆ C` with `ℓ` coordinates in `{0, 1}`, (β) `ψ₀(x') − ψ₀(x) = x' − x` for `x' − x ∈ ℤ^d`, and (γ) the pointwise bound `|ψ₀(x') − ψ₀(x)| ≤ (c₁ / dist(x, La) + ε)|x' − x|` near `x`.  Here `ψ(x) = ⌊x⌋ + ψ₀(x − ⌊x⌋)`; by (β), `ψ = z + ψ₀(· − z)` on each cube `(z + C) ∖ La`, and as `La` is `ℤ^d`-periodic, `dist(x − z, La) = dist(x, La)` transports (γ) to every unit cube.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_retraction`

#### `deformation_retraction_skeleton_mem` (L7611)

- `root.deformation-a1.retraction-a1.skeleton_mem-a1` · issue #2501 · PR #3270 · candidate `1bc3c7e40a8a`
- **Statement and proof**: Simon Ch. 6, §5: a point of `ℝ^{(m+1)+ℓ}` with `ℓ` integer coordinates lies on the lattice `(m+1)`-skeleton.  It lies in the face `⌊x⌋ + F_α`, where `α` enumerates the other `m + 1` coordinates increasingly.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_retraction`

#### `deformation_skeleton_polyhedral` (L49061)

- `root.deformation-a1.skeleton_polyhedral-a1` · issue #1118 · PR #5072 · candidate `261bae15b4dd`
- **Statement and proof**: Replacing a tangential skeleton current by a lattice chain (Simon Ch. 6, proof of 5.1, printed displays (26)–(37)).  Let `n = m + 1` and `Q ∈ 𝒟ₙ(ℝ^{n+ℓ})` with `M(Q) + M(∂Q) < ∞`, supported in the `n`-skeleton `⋃_F F` of the unit lattice and tangential near each face.  Then `Q − P = S` with `P = ∑_F β_F [[F]]`, `M(P) ≤ C M(Q)`, `M(∂P) ≤ C M(∂Q)`, `M(S) ≤ C M(∂Q)`, `spt P` in the closed `√n`-neighbourhood of `spt Q`, `spt ∂P ∪ spt S` in that of `spt ∂Q`, and `β_F ∈ ℤ` with `P` integer multiplicity when `Q` is integer multiplicity. Proof (every auxiliary fact is a local `have`).  Write `Q` and `∂Q` through the measure representations of `deformation_mass_restriction`.  Finite boundary mass forces the `dx^γ`-coefficient of `Q` to vanish a.e. on every hyperplane `{x_{γ i} = c}`, so `Q` does not charge the `(n-1)`-skeleton and is the sum over the open faces `F` of `∫_F ω(e_F) v_F dμ`; in particular the tangentiality hypothesis is not needed.  On the open unit cube a Poincaré inequality (via a smooth divergence solver built from line integrals) and a trace inequality bound `Q⌞F − b_F [[F]]` by `M(∂Q)` near `F`, where `b_F` is a weighted mean of the density. Take `β_F = b_F`, or `β_F = round b_F` when `Q` is integer multiplicity (the density is then integer valued on `F`, so `|b_F − round b_F|` obeys the same bound).  A lattice chain with integer coefficients is integer multiplicity.  Each local lemma starts with `clear * - …; revert …; refine id ?_; intro …`, which makes its proof term closed so that the long chain of local lemmas is elaborated and kernel-checked in linear memory.
- **Calls**: `deformation_mass_restriction`, `cmb_abs_apply_le_of_massOn_le` (A.1), `slicing_ru_smooth_to_continuous` (A.5), `slicing_ru_continuous_to_bounded` (A.5), `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `lpf_simple_nvector_algebra` (A.4), `lpf_raf_chart_preimage_null` (A.4), `isoperimetric_coord_box_measure`, `br_weightedTangent_congr` (A.3)
- **Called by**: `deformation_theorem`

#### `isoperimetric_coord_box_measure` (L9287)

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.box_measure-a1` · issue #1228 · PR #1494 · candidate `eefd7c3e7c63`
- **Statement and proof**: For `a ≤ b` **[corrected]**, the `n`-dimensional coordinate box `{x : c_i + a ≤ x_i ≤ c_i + b (i ∈ range α), x_i = c_i (i ∉ range α)}` in `ℝ^N` has `μHE[n]`-measure `(b - a)^n`.  The map `ι(y)_i = c_i + ∑_j [α j = i] y_j` is an isometry `ℝⁿ → ℝ^N` carrying the cube `[a, b]ⁿ` onto the box; `μHE[n]` is invariant under isometries and equals Lebesgue measure on `ℝⁿ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the hypothesis `a ≤ b` of the Lean statement (line 9288); for `a > b` and `n ≥ 1` the box is empty while `(b − a)ⁿ` may be positive.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_lattice_face_isolating_form`, `deformation_skeleton_polyhedral`

#### `deformation_dilation` (L66406)

- `root.deformation-a1.dilation-a1` · issue #1120 · PR #5466 · candidate `c859568a2876`
- **Statement and proof**: Dilation of currents (Simon Ch. 6, 2.23 and 2.24(1) for `η_ρ(x) = ρx`), the change of scale used to pass from 5.1 to 5.3.  For `ρ > 0` call `(X, Y)` a `ρ`-pair in degree `k` if `Y(ω) = X(η)` whenever `η(x) = ρᵏ ω(ρx)`, i.e. `η = η_ρ^# ω`.  Then: (1) `η_ρ^# ω` is a test form; (2) every `X ∈ 𝒟ₖ(ℝᴺ)` has a push-forward `Y = η_ρ# X`; (3) every `ρ`-pair has `M(Y) = ρᵏ M(X)` and `spt Y = ρ spt X`, `Y` is integer multiplicity if `X` is, and `Y = ∑ β_F [[ρF]]` if `X = ∑ β_F [[F]]`; (4) `∂` commutes with `η_ρ#`.
- **Calls**: `deformation_dilation_calculus`, `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`
- **Called by**: `deformation_theorem`

#### `deformation_dilation_calculus` (L66120)

- `root.deformation-a1.dilation-a1.calculus-a1` · issue #4511 · PR #5054 · candidate `7a748c7e1c8a`
- **Statement and proof**: Dilation calculus on `ℝ^N` for `η_ρ(x) = ρ x`, `ρ > 0` (Simon Ch. 6, 2.23, 2.24(1) and §1, 1.14): `η_ρ^# ω = ρ^k ω(ρ ·)` is a test form; every current `X` has the push-forward `Y = X ∘ η_ρ^#`, i.e. `Y(ω) = X(η_ρ^# ω)`; and push-forward commutes with `∂`, because `d(η_ρ^# ω) = η_ρ^#(dω)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_dilation_mass`, `deformation_dilation_support`, `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`, `deformation_dilation`

#### `deformation_dilation_mass` (L66233)

- `root.deformation-a1.dilation-a1.mass-a1` · issue #4523 · PR #5090 · candidate `92a171794173`
- **Statement and proof**: Mass scaling under dilation (Simon Ch. 6, 2.23 for `η_ρ(x) = ρx`, where `|η_ρ^# ω|(x) = ρᵏ |ω(ρx)|`): if `Y(ω) = X(η)` whenever `η(x) = ρᵏ ω(ρx)`, then `M(Y) = ρᵏ M(X)`. For a `σ`-pair `(A, B)` and `ω` admissible for `M(B)`, the pull-back `η = σᵏ ω(σ ·)` gives the admissible form `σ⁻ᵏ η = ω(σ ·)` for `M(A)` and `B(ω) = σᵏ A(σ⁻ᵏ η)`, so `M(B) ≤ σᵏ M(A)`.  As `(Y, X)` is a `ρ⁻¹`-pair, also `M(X) ≤ ρ⁻ᵏ M(Y)`, and the two bounds give equality in `[0, ∞]`.
- **Calls**: `deformation_dilation_calculus`
- **Called by**: `deformation_dilation`

#### `deformation_dilation_support` (L66285)

- `root.deformation-a1.dilation-a1.support-a1` · issue #4532 · PR #5096 · candidate `dccf6342d5d1`
- **Statement and proof**: Support scaling under dilation (Simon Ch. 6, 2.11, for the change of scale `x ↦ ρx` used to pass from 5.1 to 5.3).  Call `(A, B)` a `σ`-pair if `B(ω) = A(η)` whenever `η(x) = σᵏ ω(σx)`.  If `(A, B)` is a `σ`-pair and `A` vanishes on an open `W` with compact closure, then `B` vanishes on `σW`: the pull-back `η` of `ω` (first conjunct of `Submission.deformation_dilation_calculus`) has `tsupport η ⊆ σ⁻¹ tsupport ω ⊆ W`. Hence `σ zeroRegion(A) ⊆ zeroRegion(B)`.  Since `(Y, X)` is a `ρ⁻¹`-pair, `zeroRegion(Y) = ρ zeroRegion(X)`, and complements commute with the bijection `x ↦ ρx`.
- **Calls**: `deformation_dilation_calculus`
- **Called by**: `deformation_dilation`

#### `deformation_dilation_integer_multiplicity` (L66337)

- `root.deformation-a1.dilation-a1.integer_multiplicity-a1` · issue #4546 · PR #5281 · candidate `55e0df8042b9`
- **Statement and proof**: Dilation preserves integer multiplicity (Simon Ch. 6, 2.23 and Lemma 3.9 for the dilation `η_ρ(x) = ρx`, `ρ > 0`): if `X = τ(M, θ, ξ)` is integer multiplicity and `Y(ω) = X(η)` whenever `η(x) = ρᵏ ω(ρx)`, then `Y = τ(ρM, θ(ρ⁻¹ ·), ξ(ρ⁻¹ ·))` with natural-valued `θ(ρ⁻¹ ·)`.
- **Calls**: `deformation_dilation_hausdorff`, `deformation_dilation_im_rectifiableTriple`, `deformation_dilation_calculus`, `deformation_dilation_im_tauAction`
- **Called by**: `deformation_dilation`

#### `deformation_dilation_hausdorff` (L66210)

- `root.deformation-a1.dilation-a1.hausdorff-a1` · issue #4519 · PR #4951 · candidate `8ae4965a0dae`
- **Statement and proof**: `Hᵏ` scaling law for the dilation `φ(x) = ρ • x`, `ρ > 0`: `φ` is a measurable embedding and pushes `ρᵏ Hᵏ` forward to `Hᵏ`, i.e. `Hᵏ(φ⁻¹(B)) = ρ⁻ᵏ Hᵏ(B)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_dilation_integer_multiplicity`, `deformation_dilation_lattice_chain`

#### `deformation_dilation_im_rectifiableTriple` (L66022)

- `root.deformation-a1.dilation-a1.integer_multiplicity-a1.rectifiable_triple-a1` · issue #4910 · PR #5259 · candidate `003dc0ac1d63`
- **Statement and proof**: Rectifiable triples are invariant under the dilation `φ(x) = ρ x`, `ρ > 0`: `(φ(M), θ ∘ φ⁻¹, ξ ∘ φ⁻¹)` is again a rectifiable triple, where `φ⁻¹(y) = ρ⁻¹ y`. `φ` is a measurable embedding pushing `c Hᵏ`, `c = ρᵏ`, forward to `Hᵏ`, so `Hᵏ(φ(S)) = c Hᵏ(S)` for every `S` and `Hᵏ ⌞ φ(M) = φ_#(c Hᵏ ⌞ M)`; an approximate tangent space of `(M, θ)` at `x` is one of `(φ(M), θ ∘ φ⁻¹)` at `φ(x)`.
- **Calls**: `deformation_dilation_im_weightedTangent`
- **Called by**: `deformation_dilation_integer_multiplicity`

#### `deformation_dilation_im_weightedTangent` (L65983)

- `root.deformation-a1.dilation-a1.integer_multiplicity-a1.weighted_tangent-a1` · issue #4905 · PR #5232 · candidate `4fc201187da5`
- **Statement and proof**: Weighted approximate tangent spaces (Simon Ch. 3, 1.7) are invariant under the dilation `y ↦ ρ y`, `ρ > 0`: if `Q` is the approximate tangent space of `(M, θ)` at `x`, it is the approximate tangent space of `(ρ M, θ(ρ⁻¹ ·))` at `ρ x`.  The blow-up of `ρ M` at `ρ x` with ratio `s` is the blow-up of `M` at `x` with ratio `ρ⁻¹ s`, and `s ↦ ρ⁻¹ s` preserves `𝓝[>] 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_dilation_im_rectifiableTriple`

#### `deformation_dilation_im_tauAction` (L66096)

- `root.deformation-a1.dilation-a1.integer_multiplicity-a1.tau_action-a1` · issue #4917 · PR #5103 · candidate `7939be729e42`
- **Statement and proof**: `τ(M, θ, ξ)` tested against `x ↦ ρᵏ ω(ρx)` equals `τ(φ(M), θ ∘ φ⁻¹, ξ ∘ φ⁻¹)` tested against `ω`, `φ(x) = ρx`, `ρ > 0`, when `φ` is a measurable embedding pushing `ρᵏ Hᵏ` forward to `Hᵏ`: change variables and pull `ρᵏ` out of the linear `ξ(x)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `deformation_dilation_integer_multiplicity`

#### `deformation_dilation_lattice_chain` (L66358)

- `root.deformation-a1.dilation-a1.lattice_chain-a1` · issue #4558 · PR #5124 · candidate `ce4ee5e2a817`
- **Statement and proof**: Dilation of lattice chains (the rescaling `x ↦ ρx` behind Simon Ch. 6, 5.3, p. 160). If `Y(ω) = X(η)` whenever `η(x) = ρᵏ ω(ρx)`, and `X = ∑'_F β_F [[F]]` on the unit lattice, then `Y = ∑'_F β_F [[ρF]]` on the `ρ`-lattice: `ρF` is the image of `F` under `x ↦ ρ • x` and `∫_{ρF} g dHᵏ = ρᵏ ∫_F g(ρx) dHᵏ(x)`, so the two sums agree term by term.
- **Calls**: `deformation_dilation_hausdorff`, `deformation_dilation_calculus`
- **Called by**: `deformation_dilation`

#### `deformation_im_combination` (L65922)

- `root.deformation-a1.im_combination-a1` · issue #1119 · PR #5260 · candidate `bf6aeaf20acf`
- **Statement and proof**: **Integer combinations of integer multiplicity currents, Simon Ch. 6, Remark 3.2(1) (p. 146).**  If `X = τ(M₁, θ₁, ξ₁)` and `Y = τ(M₂, θ₂, ξ₂)` are integer multiplicity and `Z = a X + b Y` with `a, b ∈ ℤ`, then `Z` is integer multiplicity.  Write `a X + b Y` as the integer series with terms `(M₁, θ₁, ξ₁)` (`r = 0`), `(M₂, θ₂, ξ₂)` (`r ≥ 1`) and coefficients `c = (a, b, 0, 0, …)`; it converges absolutely, since only two terms are nonzero and `θᵢ` is integrable on `Mᵢ ∩ W̄`.  The series theorem (Simon 3.13) combines it into one integer multiplicity triple `τ(M', θ', ξ')` whose action is the sum `a X(ω) + b Y(ω) = Z(ω)`.  That theorem needs weighted approximate tangent planes of two carriers to agree `Hᵏ`-a.e. on their overlap; on `ℝ^N` this is the tangent comparison (Simon Ch. 3, 1.8(1)).
- **Calls**: `fiw_ims_combine`, `deformation_imcomb_tangent_overlap`
- **Called by**: `deformation_theorem`

#### `fiw_ims_combine` (L63314)

- `root.flat_iff_weak-a1.im_series-a1.im_combine-a1` · issue #1254 · PR #2679 · candidate `db32c8c94202`
- **Statement and proof**: **Series of integer multiplicity currents, Simon Ch. 6, 3.13 (p. 149), as used in the proof of 7.2 (p. 172 **[corrected]**).**  Under tangent locality in `U`, an `M`-absolutely convergent series `∑ c_r τ(M_r, θ_r, ξ_r)` with `c_r ∈ ℤ` and integer `θ_r` is one integer multiplicity current `τ(M', θ', ξ')`.  Off an `Hⁿ`-null set, only finitely many `M_r` with `c_r ≠ 0` contain `x`, each `ξ_r` orients `M_r` at `x`, and `ξ_r(x) = ±ξ_{r'}(x)` whenever `x ∈ M_r ∩ M_{r'}`.  With `ξ̂ = ξ_{r(x)}` for the first index `r(x)` of an `M_r ∋ x` and `ξ_r = σ_r ξ̂` (`σ_r = ±1`), `θ̂ = ∑' r, 1_{M_r} c_r σ_r θ_r` is an integer-valued finite sum bounded by `∑' r, |c_r| 1_{M_r} θ_r`; then `M' = {θ̂ ≠ 0}`, `θ' = |θ̂|`, `ξ' = (θ̂/|θ̂|) ξ̂` give the sum of the series.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives "p. 170". The statement of 7.2 begins on p. 170, but its proof begins on p. 171, and 3.13 is used on p. 172 ("Therefore by 3.13 we can define …").
- **Calls**: `fiw_ims_overlap_finite`, `fiw_ims_orientation_sign`, `fiw_ims_tsum_tau`
- **Called by**: `fiw_im_series`, `deformation_im_combination`

#### `fiw_ims_overlap_finite` (L63069)

- `root.flat_iff_weak-a1.im_series-a1.overlap_finite-a1` · issue #1252 · PR #1542 · candidate `02fc45016615`
- **Statement and proof**: Local finiteness for an integer series of currents `∑ c_r τ(M_r, θ_r, ξ_r)` (Simon Ch. 6, 3.13, used for `R^(ℓ)`, `S^(ℓ)` in the proof of 7.2): for an open `U`, `Hⁿ`-null-measurable `M_r ⊆ U`, and `θ_r ≥ 1` on `M_r` (e.g. integer multiplicities) and `Hⁿ`-integrable on `M_r ∩ K` for compact `K ⊆ U` **[corrected]**, with `Θ = ∑' r, |c_r| 1_{M_r} θ_r` and `∑' r, |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for each `W ⊂⊂ U`, `Θ` is locally `Hⁿ`-integrable in `U` and `Hⁿ`-a.e. `x` lies in `M_r` for only finitely many `r` with `c_r ≠ 0`.  Termwise integration (`lintegral_tsum`) gives `∫_W Θ dHⁿ < ∞` on each `W ⊂⊂ U`, so `Θ < ∞` a.e. near each point of `U`, hence a.e. on `U` (`ℝ^P` is second countable); at such `x` each such `r` adds at least `1` to `Θ(x)`, and off `U` no `M_r` contains `x`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (lines 63070–63075), and `θ_r ≥ 1` is necessary: the sketch uses that each `r` with `x ∈ M_r` and `c_r ≠ 0` adds at least `1` to `Θ(x)`. For `P = n = 1`, `U = ℝ`, `M_r = [0, 1]`, `θ_r ≡ 2^{−r}` and `c_r = 1`, the summability condition holds but every `x ∈ [0, 1]` lies in every `M_r`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_ims_combine`

#### `fiw_ims_orientation_sign` (L37415)

- `root.flat_iff_weak-a1.im_series-a1.orientation_sign-a1` · issue #1250 · PR #2002 · candidate `6f506c46bb4e`
- **Statement and proof**: Orientations of rectifiable triples agree up to sign on the overlap where every weighted approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)` (Simon Ch. 6, 3.1: `ξ(x)` is `±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`).  At `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂` the `orients` fields give orthonormal frames `τ`, `τ'` with `ξ₁(x) = ±s(τ)` and `ξ₂(x) = ±s(τ')`, where `s = simpleNVector`.  By hypothesis `span τ` is a weighted approximate tangent space of `(M₂, θ₂)` at `x`, so `span τ = span τ'` by uniqueness (Ch. 3, 1.7; `θ₂(x) > 0`), and `Submission.fiw_ims_frame_sign` gives `s(τ') = ±s(τ)`.
- **Calls**: `fiw_ims_frame_sign` (A.5)
- **Called by**: `iwl_imc_lincomb_im`, `fiw_ims_combine`

#### `fiw_ims_tsum_tau` (L63232)

- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1` · issue #1253 · PR #2298 · candidate `a079caed8454`
- **Statement and proof**: **Termwise integration of an integer series of rectifiable triples** (Simon Ch. 6, 3.1 (‡) for the `M`-absolutely convergent series of 3.13 and the proof of 7.2). Let `(M_r, θ_r, ξ_r)` be rectifiable triples in `U` and `c_r ∈ ℤ` with `∑_r |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞` for every `W ⊂⊂ U`.  Then for every `ω ∈ 𝒟ⁿ(U)`, with `F_r := 1_{M_r} c_r θ_r ⟨ω, ξ_r⟩`, the series `∑_r c_r τ(M_r, θ_r, ξ_r)(ω)` has sum `∫ ∑_r F_r dHⁿ`.  Choose an open `W ⊂⊂ U` with `tsupport ω ⊆ W` and a bound `‖ω(x)‖ ≤ B`; `Submission.fiw_ims_tt_term_bound` makes each `F_r` a.e. strongly measurable with `∫ |F_r| dHⁿ ≤ |c_r| B ∫_{M_r ∩ W} θ_r dHⁿ`, so `∑_r ∫ |F_r| dHⁿ < ∞` and the series can be integrated termwise (`hasSum_integral_of_summable_integral_norm`); finally `∫ F_r dHⁿ = c_r ∫_{M_r} θ_r ⟨ω, ξ_r⟩ dHⁿ = c_r τ(M_r, θ_r, ξ_r)(ω)`.
- **Calls**: `fiw_ims_tt_term_bound`
- **Called by**: `fiw_ims_combine`

#### `fiw_ims_tt_term_bound` (L63158)

- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.term_bound-a1` · issue #1484 · PR #2241 · candidate `3446f5312c3a`
- **Statement and proof**: One term of Simon Ch. 6, 3.1 (‡): for a rectifiable triple `(M, θ, ξ)` in `U`, an open `W ⊂⊂ U` and a continuous `n`-form `ω` with `tsupport ω ⊆ W` and `‖ω(x)‖ ≤ B`, the integrand `1_M θ ⟨ω, ξ⟩` is `Hⁿ`-a.e. strongly measurable and `∫ |1_M θ ⟨ω, ξ⟩| dHⁿ ≤ B ∫_{M ∩ W} θ dHⁿ`, since `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖` for `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` (`Submission.fiw_ims_tt_unit_bound`).
- **Calls**: `fiw_ims_tt_unit_bound` (A.5)
- **Called by**: `fiw_ims_tsum_tau`

#### `deformation_imcomb_tangent_overlap` (L65835)

- `root.deformation-a1.im_combination-a1.tangent_overlap-a1` · issue #4627 · PR #5231 · candidate `d3ff54f8631a`
- **Statement and proof**: Weighted approximate tangent spaces (Simon Ch. 3, 1.7) of two carriers agree on their overlap, for arbitrary positive multiplicities.  As in Ch. 3, Remark 1.8(1), the overlap is cut into pieces on which the multiplicities have a positive lower bound: a weight integrable on `M ∩ K` for every compact `K` is `Hᵏ⌞M`-a.e. measurable (`ℝ^N = ⋃ₘ B̄ₘ(0)`), so the sets `E j = M₁ ∩ {θ₁ ≥ 1/(j+1)} ∩ M₂ ∩ {θ₂ ≥ 1/(j+1)}` are `Hᵏ`-null-measurable, they exhaust `M₁ ∩ M₂`, and `Hᵏ(E j ∩ K) ≤ (j+1) ∫_{M₁ ∩ K} θ₁ dHᵏ < ∞` by Chebyshev.  For `Hᵏ`-a.e. `x ∈ E j`, a tangent space of `(M₁, θ₁)` at `x` is one of `(E j, θ₁)` (`deformation_imcomb_subset_locality`), hence of `(E j, θ₂)` (`deformation_imcomb_weight_change`), hence of `(M₂, θ₂)`; a countable union over `j` gives the claim.
- **Calls**: `deformation_imcomb_subset_locality`, `deformation_imcomb_weight_change`
- **Called by**: `deformation_im_combination`

#### `deformation_imcomb_subset_locality` (L32094)

- `root.deformation-a1.im_combination-a1.subset_locality-a1` · issue #4608 · PR #4970 · candidate `7fb98fe53fd7`
- **Statement and proof**: Locality of weighted approximate tangent spaces under passage to a subset, as in Simon Ch. 3, Remark 1.8(1).  For `E ⊆ M` and `θ` locally `Hᵏ`-integrable on `M`, the upper density theorem (Ch. 1, 3.6) gives `∫⁻_{S ∩ B̄_ρ(x)} |θ| dHᵏ = o(ρᵏ)` for `S = M \ E` at `Hᵏ`-a.e. `x ∈ E`.  Since `|1_M θ - 1_E θ| = 1_S |θ|`, rescaling `ρ = R r` turns this into the density hypothesis of the weighted tangent locality lemma for `(M, θ)` and `(E, θ)` at `x`.
- **Calls**: `lpf_wtc_ae_zero_density_off_set` (A.4), `iwl_weighted_tangent_locality`
- **Called by**: `deformation_imcomb_tangent_overlap`

#### `deformation_imcomb_weight_change` (L65761)

- `root.deformation-a1.im_combination-a1.weight_change-a1` · issue #4615 · PR #5172 · candidate `efee9a8cf5a6`
- **Statement and proof**: Simon Ch. 3, Remark 1.8(1): on a set `E` of locally finite `Hᵏ`-measure, weighted approximate tangent spaces do not depend on the positive multiplicity.  At `Hᵏ⌞E`-a.e. `x`, both `θ` and `θ'` have normalized Lebesgue points.  With `c θ(x) = θ'(x)`, Definition 1.7 is homogeneous in the weight, so `Q` is tangent for `(E, c θ)`; and `|c θ - θ'| ≤ |c| |θ - θ(x)| + |θ' - θ'(x)|` lets tangent locality pass from `(E, c θ)` to `(E, θ')`.
- **Calls**: `iwl_imc_normalized_lebesgue_points`, `iwl_weighted_tangent_locality`
- **Called by**: `deformation_imcomb_tangent_overlap`

#### `iwl_imc_normalized_lebesgue_points` (L37760)

- `root.integrality_weak_limits-a1.im_closure-a1.lebesgue_points-a1` · issue #2814 · PR #3733 · candidate `3047dcd2a39a`
- **Statement and proof**: Normalized Lebesgue points (Simon Ch. 1, 3.23 with Theorem 3.3): if `U` is open, `M ⊆ U` is `Hᵏ`-null-measurable with `Hᵏ(M ∩ K) < ∞`, and `f` is `Hᵏ`-integrable on `M ∩ K`, for every compact `K ⊆ U` **[corrected]**, then for `Hᵏ⌞M`-a.e. `x` and every `R > 0`, `r⁻ᵏ ∫_{M ∩ B̄_{Rr}(x)} |f - f(x)| dHᵏ → 0` as `r ↓ 0`.  On a ball `W` with `K = B̄ ⊆ U`, Lebesgue–Besicovitch differentiation for the finite measure `λ = Hᵏ⌞(M ∩ K)` makes the `λ`-averages over `B̄_ρ(x)` tend to `0`, and density comparison gives `Θ*ᵏ(λ, x) < ∞`, so `λ(B̄_ρ(x)) ≤ C ωₖ ρᵏ` for small `ρ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), states no hypotheses; the Lean statement (line 37760) assumes these, and the sketch uses them (the finite measure `λ`).
- **Calls**: `rectifiability_density_comparison` (A.3)
- **Called by**: `iwl_imc_tangent_overlap`, `deformation_imcomb_weight_change`

### A.7 Isoperimetric Theorem 6.1 (§3.7): `isoperimetric_theorem` and its 7 further declarations

#### `isoperimetric_theorem` (L67200)

- `root.isoperimetric-a1` · issue #329 · PR #8118 · candidate `2e7a66f237aa`
- **Statement and proof**: **Simon Ch. 6, 6.1 (Isoperimetric Theorem, pp. 168–169)**, by its printed proof (p. 169): deform `T` by 5.3 in `ℝ^{(m+1)+(ℓ+1)} = ℝ^{m+2+ℓ}` at the scale `ρ` with `ρ^{m+1} = 2(C+1)M(T)`.  Then `S = 0` as `∂T = 0`, and the lattice chain `P` vanishes because a nonzero integer `β_F` would give `M(P) ≥ ρ^{m+1} > C M(T)`; so `T = ∂R`, and `M(R) ≤ Cρ M(T) ≤ ρ^{m+2}` gives `M(R)^{(m+1)/(m+2)} ≤ ρ^{m+1} = 2(C+1)M(T)`.
- **Calls**: `deformation_theorem` (A.6), `isoperimetric_mass_lt_top`, `isoperimetric_mass_eq_zero_iff`, `isoperimetric_lattice_chain_mass_ge`
- **Called by**: `integrality_of_weak_limits`, `main_theorem`

#### `isoperimetric_mass_lt_top` (L2450)

- `root.isoperimetric-a1.finite_mass-a1` · issue #760 · PR #2092 · candidate `1e660afc8717`
- **Statement and proof**: Step 1 of Simon Ch. 6, 6.1: a compactly supported integer multiplicity `T = τ(M, θ, ξ)` in `ℝ^P` has finite mass.  For a bump `χ` equal to `1` near `spt T` and supported in the ball `K`, every admissible `ω` has `T ω = T (χ ω)` by locality, and `|T (χ ω)| ≤ P^n ∫_{M ∩ K} θ dHⁿ`.
- **Calls**: `isoperimetric_apply_eq_zero_of_disjoint_support` (A.6), `isoperimetric_abs_covector_apply_le`
- **Called by**: `isoperimetric_theorem`

#### `isoperimetric_abs_covector_apply_le` (L2379)

- `root.isoperimetric-a1.covector_eval_bound-a1` · issue #757 · PR #1639 · candidate `8c000d1fa9fe`
- **Statement and proof**: **Covector evaluation bound** (for `M(T) < ∞` in the proof of Simon Ch. 6, 6.1, p. 169). If `|τ_j| ≤ 1` for all `j`, then `|α(τ_1, …, τ_n)| ≤ P^n |α|`, `|α|` the Euclidean coefficient norm of Remark 2.6.  Expanding each `τ_j` in the standard basis `e_1, …, e_P` gives `α(τ) = ∑_f (∏_j τ_j(f j)) α(e_f)` over the `P^n` maps `f : Fin n → Fin P`.  Each coefficient has absolute value at most `1`, and `|α(e_f)| ≤ |α|`: `α(e_f) = 0` unless `f` is injective, and then `α(e_f) = ±α(e_{f ∘ σ})` for the permutation `σ` sorting `f`, where `f ∘ σ` is strictly increasing.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_mass_lt_top`, `iwl_cr_cest_radial_coeff_bound`

#### `isoperimetric_mass_eq_zero_iff` (L7542)

- `root.isoperimetric-a1.zero_mass_iff-a1` · issue #762 · PR #2714 · candidate `43971b5da770`
- **Statement and proof**: **A current has zero mass iff it is zero** (used implicitly in Simon Ch. 6, proof of 6.1, p. 169 **[corrected]**).  `M(0)` is a supremum of zeros.  Conversely, every test form `ω` is supported in `U` with Euclidean coefficient norm `|ω(x)| ≤ C`, so the mass estimate gives `|T(ω)| ≤ M_U(T) · C = 0`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), cites "Simon Ch. 6, proof of 6.1, p. 168" with the quotation "if `M(T) = 0` then `|T(ω)| ≤ M(T) ‖ω‖ = 0`". That sentence is not in the book, and the proof of 6.1 is on p. 169 (p. 168 has the introduction of §6 and the statement of 6.1). The proof begins "The case `T = 0` is trivial, so assume `T ≠ 0`" and then chooses `ρ = (2cM(T))^{1/(n−1)}`, which needs `M(T) > 0`. This lemma supplies that implicit step (`T ≠ 0 ⇒ M(T) > 0`). The argument above is the lemma's own.
- **Calls**: `br_la_testForm_covectorNorm_bounded` (A.6), `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `isoperimetric_theorem`

#### `isoperimetric_lattice_chain_mass_ge` (L9544)

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1` · issue #765 · PR #2541 · candidate `b1a770c375be`
- **Statement and proof**: Simon Ch. 6, proof of 6.1, (1) (p. 169): a lattice chain `Pc = ∑_F β_F [[F]]` in `ℝ^N` has mass at least `|β_F| ρ^{m+1}` for every face `F` (`H^{m+1}(F) = ρ^{m+1}`).  For `0 < δ < 1/4` the isolating form `ω` of `F` kills every other face, so testing `Pc` with `±ω` gives `M(Pc) ≥ |β_F| [[F]](ω) ≥ |β_F| (ρ (1 - 2δ))^{m+1}`; then let `δ → 0⁺`.
- **Calls**: `isoperimetric_lattice_face_isolating_form`
- **Called by**: `fiw_tb_lattice_chain_coeff`, `isoperimetric_theorem`

#### `isoperimetric_lattice_face_isolating_form` (L9453)

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.isolating_form-a1` · issue #1230 · PR #2246 · candidate `dded2fa657ff`
- **Statement and proof**: A mass-admissible test form isolating one lattice face: for `ρ > 0`, `0 < δ < 1/4` and the face `F₀ = ρ(z + F_α)`, the form `ω = φ dx^α` (`φ` the cut-off of `F₀`) has `[[F]](ω) = 0` for every other face `F` (`dx^α` kills the faces of other directions, `φ` those of direction `α`), and `[[F₀]](ω) = ∫_{F₀} φ dHⁿ ≥ Hⁿ(K) = (ρ(1 − 2δ))^n`, `K` the shrunken face where `φ = 1`.
- **Calls**: `isoperimetric_coord_covector_eval`, `isoperimetric_lattice_face_cutoff`, `isoperimetric_coord_box_measure` (A.6)
- **Called by**: `isoperimetric_lattice_chain_mass_ge`

#### `isoperimetric_coord_covector_eval` (L7561)

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1` · issue #1227 · PR #2099 · candidate `3d98b1871057`
- **Statement and proof**: The coordinate covector `dx^α = wedgeCovectors n (proj ∘ α)` on `ℝ^N` is dual to the coordinate frames: `dx^α(e_α) = 1`, `dx^α(e_{α'}) = 0` for every other increasing multi-index `α'`, and `covectorEuclideanNorm (c • dx^α) = |c|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_lattice_face_isolating_form`, `fiw_tb_lcc_local_isolating_form`

#### `isoperimetric_lattice_face_cutoff` (L9354)

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.face_cutoff-a1` · issue #1229 · PR #1759 · candidate `b27494a624bd`
- **Statement and proof**: Smooth cut-off for a lattice face: for `ρ, δ > 0` there is a compactly supported smooth `φ : ℝ^N → [0, 1]` equal to `1` on the shrunken face `{x : ρ(zᵢ + δ) ≤ xᵢ ≤ ρ(zᵢ + 1 − δ) (i ∈ α), xᵢ = ρ zᵢ (i ∉ α)}` and vanishing on every other lattice face `ρ (z' + F_α)`, `z' ≠ z`, of the same direction `α`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `isoperimetric_lattice_face_isolating_form`, `fiw_tb_lcc_local_isolating_form`

### A.8 Polyhedral approximation 6.2 (§3.8): `polyhedral_approximation` and its 10 further declarations

#### `polyhedral_approximation` (L67293)

- `root.polyhedral_approximation-a1` · issue #331 · PR #8056 · candidate `786e6c8abe43`
- **Statement and proof**: **Simon Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem, p. 169).**  The printed second paragraph (slicing 4.5 by an exhaustion function) gives integer multiplicity truncations `X_k = T ⌞ {φ > λ_k}`, extended to `ℝ^{m+1+ℓ}`, with `M(X_k) + M(∂X_k) < ∞` and `X_k(ω) = T(ω)` for large `k`; the printed first paragraph (deformation theorem 5.3 at scales `ρ_k ↓ 0`) gives lattice chains `Pc_k` with `Pc_k(ω) - X_k(ω) → 0`.  Then `P_k := Pc_k` restricted to `U` converges weakly to `T` in `U`.
- **Calls**: `polyhedral_approx_truncation_seq`, `slicing_theorem` (A.5), `polyhedral_approx_finite_mass_seq`, `deformation_theorem` (A.6)
- **Called by**: `main_theorem`

#### `polyhedral_approx_truncation_seq` (L18213)

- `root.polyhedral_approximation-a1.truncation_sequence-a1` · issue #536 · PR #2975 · candidate `a4d7cce8f764`
- **Statement and proof**: The truncation sequence of Simon Ch. 6, 6.2 (p. 169, second paragraph of the proof): an integer multiplicity `T ∈ 𝒟_{m+1}(U)` with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U` agrees eventually, on each test form of `U`, with integer multiplicity `X_k ∈ 𝒟_{m+1}(ℝ^P)` such that `M(X_k) + M(∂X_k) < ∞`.  For the exhaustion function `φ`, `X_k = τ(M ∩ {φ > λ_k}, θ, ξ)` is the book's `T ⌞ {φ > λ_k}`; the slicing mass bound (4.10) for `f = -φ` picks `λ_k ∈ (1/(k+2), 1/(k+1))` with `M_{W_k}(⟨T, -φ, -λ_k⟩) < ∞`, `W_k = {φ > 1/(2(k+2))}`.  By (4.6) and a cut-off, `M(∂X_k) ≤ M_{W_k}(⟨T, -φ, -λ_k⟩) + M_{W_k}((∂T) ⌞ {φ > λ_k})`.
- **Calls**: `polyhedral_approx_exhaustion_function`, `polyhedral_approx_restriction_exists`, `polyhedral_approx_open_truncation`, `polyhedral_approx_restriction_tau` (A.6), `polyhedral_approx_boundary_mass_cutoff`
- **Called by**: `polyhedral_approximation`

#### `polyhedral_approx_exhaustion_function` (L447)

- `root.polyhedral_approximation-a1.truncation_sequence-a1.exhaustion_function-a1` · issue #1127 · PR #1758 · candidate `e902cc9324a7`
- **Statement and proof**: The exhaustion function of Simon Ch. 6, 6.2 (p. 169, proof): for open `U ⊆ ℝ^P` there is a 1-Lipschitz `φ` whose superlevel sets `{φ ≥ t}`, `t > 0`, are compact subsets of `U`, and which has a positive lower bound on every compact `K ⊆ U`.  With `g(x) = 1/(1 + |x|)`, take `φ = g` if `U = ℝ^P` and `φ = min(dist(·, ℝ^P ∖ U), g)` otherwise.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_truncation_seq`

#### `polyhedral_approx_restriction_exists` (L17892)

- `root.polyhedral_approximation-a1.restriction_exists-a1` · issue #529 · PR #2197 · candidate `0bff98712e72`
- **Statement and proof**: **Simon Ch. 6, (2.9) (p. 136).**  Restrictions `T ⌞ A` exist for every measure representation `(μ, v)` of `T` and Borel `A`, and every restriction has locally finite mass.  For compact `K ⊆ U`, testing `T` with `χ_K dx^I` (`χ_K` a smooth cut-off equal to `1` on `K`) shows that the coordinates `v(·)(dx^I)` are `μ`-integrable on `K`; by `polyhedral_approx_pairing_expansion`, `|⟨α, v(x)⟩| ≤ b ∑_I |v(x)(dx^I)|` whenever every coefficient satisfies `|α_I| ≤ b`.  Taking `b = ‖α‖` gives the sequential continuity of `ω ↦ ∫_A ⟨ω, v⟩ dμ`; taking `b = 1` bounds `S(ω)` by `∫_{closure W} ∑_I |v(·)(dx^I)| dμ` for every `ω` admissible for `M_W`.
- **Calls**: `polyhedral_approx_pairing_expansion` (A.6)
- **Called by**: `polyhedral_approx_truncation_seq`

#### `polyhedral_approx_open_truncation` (L18022)

- `root.polyhedral_approximation-a1.open_truncation-a1` · issue #533 · PR #2239 · candidate `b3275c855bf2`
- **Statement and proof**: Integer multiplicity truncation to an open `V ⊂⊂ U` (the step `T ⌞ V` of the proof of Simon Ch. 6, 6.2): for `T = τ(M, θ, ξ)` integer multiplicity in `U`, the current `X(ω) = ∫_{M ∩ V} θ ⟨ω, ξ⟩ dHⁿ` on `ℝ^P` is integer multiplicity, witnessed by the triple `(M ∩ V, θ, ξ)`, and has finite mass `M(X) ≤ c_* ∫_{M ∩ V} θ dHⁿ`, `c_* = ∑_I ‖dx^I‖`.
- **Calls**: `polyhedral_approx_pairing_expansion` (A.6)
- **Called by**: `polyhedral_approx_truncation_seq`

#### `polyhedral_approx_boundary_mass_cutoff` (L506)

- `root.polyhedral_approximation-a1.truncation_sequence-a1.boundary_mass_cutoff-a1` · issue #1128 · PR #2006 · candidate `220d968d8bd7`
- **Statement and proof**: Boundary mass transfer through a smooth cut-off (Simon Ch. 6, 6.2, proof): if `X` and `A` agree on any two test forms that coincide on `V`, where `closure V` is a compact subset of the open set `W ⊆ U₂`, then `M(∂X) ≤ M_W(∂A)`.  For `ψ` admissible for `M(∂X)` and a smooth cut-off `χ`, `0 ≤ χ ≤ 1`, `χ = 1` near `closure V` with compact support in `W`, the form `χψ` is admissible for `M_W(∂A)`, and `d(χψ) = dψ` on `V` gives `∂X(ψ) = X(dψ) = A(d(χψ)) = ∂A(χψ)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_truncation_seq`, `br_local_finite_mass_extension`

#### `polyhedral_approx_finite_mass_seq` (L18449)

- `root.polyhedral_approximation-a1.finite_mass_approximation-a1` · issue #539 · PR #3478 · candidate `60949edddf66`
- **Statement and proof**: Simon Ch. 6, 6.2 (p. 169), first paragraph of the proof, for a sequence `X_k` of integer multiplicity currents with `M(X_k) + M(∂X_k) < ∞`: deforming `X_k` at a scale `ρ_k ↓ 0` with `ρ_k (M(X_k) + M(∂X_k)) ≤ 1/(k+1)` gives lattice chains `Pc_k` with integer coefficients and `Pc_k(ω) − X_k(ω) → 0` for every test form `ω`.
- **Calls**: `polyhedral_approx_scale_seq`, `polyhedral_approx_flat_seq_tendsto`
- **Called by**: `polyhedral_approximation`

#### `polyhedral_approx_scale_seq` (L18362)

- `root.polyhedral_approximation-a1.finite_mass_approximation-a1.scale_sequence-a1` · issue #2213 · PR #3092 · candidate `72f53c6507e1`
- **Statement and proof**: Scales for the polyhedral approximation (Simon Ch. 6, 6.2, choice of `ρ_k ↓ 0`): for any real sequence `a` there are scales `ρ_k > 0` decreasing to `0` with `ρ_k a_k ≤ 1/(k+1)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_finite_mass_seq`

#### `polyhedral_approx_flat_seq_tendsto` (L18413)

- `root.polyhedral_approximation-a1.finite_mass_approximation-a1.flat_convergence-a1` · issue #2223 · PR #3252 · candidate `ca2d03cda38d`
- **Statement and proof**: Simon Ch. 6, 6.2 (p. 169), "(1), (2) give `P_k(ω) → T_k(ω)`", where the printed `T_k(ω)` is a misprint for `T(ω)` **[corrected]**: if `X_k − Pc_k = ∂R_k + S_k` with `M(R_k) → 0` and `M(S_k) → 0`, then `Pc_k(ω) − X_k(ω) → 0` for every test form `ω`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes the sentence of p. 169 with `T(ω)` as the limit. The book prints "Evidently (1), (2) give `P_k(ω) → T_k(ω)` `∀ω ∈ 𝒟ⁿ(ℝ^{n+ℓ})`" (the paragraph after display (2) of the proof of 6.2). No `T_k` is defined there, and `T(ω)` is meant, since display (1) reads `T − P_k = ∂R_k + S_k`. The quotation above now follows the printed text and notes the misprint.
- **Calls**: `polyhedral_approx_testForm_covectorNorm_bounded`, `br_la_abs_apply_le_mul_mass`
- **Called by**: `polyhedral_approx_finite_mass_seq`

#### `polyhedral_approx_testForm_covectorNorm_bounded` (L18339)

- `root.polyhedral_approximation-a1.finite_mass_approximation-a1.testform_bounded-a1` · issue #2195 · PR #2910 · candidate `7110c9805fef`
- **Statement and proof**: **Test forms have bounded Euclidean coefficient norm** (Simon Ch. 6, 1.15 and 2.4; the finiteness of `sup_x |ω(x)|` behind "Evidently (1), (2) give `Pₖ(ω) → Tₖ(ω)`" in the proof of 6.2, p. 169, where the printed `Tₖ(ω)` is a misprint for `T(ω)` **[corrected]**): for `ω ∈ 𝒟ⁿ(U)` there is `C > 0` with `|ω(x)| ≤ C` for all `x`. `α ↦ |α|` is continuous (a square root of a finite sum of squares of evaluations) and `ω` is smooth, so `x ↦ |ω(x)|` is continuous; it has compact support since `|0| = 0`.  Hence it is bounded by some `C₀ ≥ 0`, and `C = C₀ + 1` works.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes the sentence of p. 169 with `T(ω)` as the limit. The book prints "Evidently (1), (2) give `P_k(ω) → T_k(ω)` `∀ω ∈ 𝒟ⁿ(ℝ^{n+ℓ})`" (the paragraph after display (2) of the proof of 6.2). No `T_k` is defined there, and `T(ω)` is meant, since display (1) reads `T − P_k = ∂R_k + S_k`. The quotation above now follows the printed text and notes the misprint.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `polyhedral_approx_flat_seq_tendsto`

#### `br_la_abs_apply_le_mul_mass` (L726)

- `root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1` · issue #1188 · PR #2012 · candidate `d771ac3ae563`
- **Statement and proof**: Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Y) < ∞` and `|ω(x)| ≤ C` everywhere (Euclidean coefficient norm) with `C > 0`, then `|Y(ω)| ≤ C · M(Y)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_ext_cutoff_current`, `polyhedral_approx_flat_seq_tendsto`, `br_la_weaklyConvergesOn_of_flat_decomposition`

### A.9 Theorem 8.2 (§3.9): `integrality_of_weak_limits` and its 89 further declarations

#### `integrality_of_weak_limits` (L68796)

- `root.integrality_weak_limits-a1` · issue #341 · PR #8548 · candidate `036fb2d84e9c`
- **Statement and proof**: **Simon Ch. 6, Theorem 8.2 (pp. 176–179)**, by induction on `n = m + 1` (all `U` at once). In degree `n` the boundary-limit hypothesis (BLI) — weak limits in `ℝ^P` of integer multiplicity boundaries `∂Y_j` with `sup_j M(∂Y_j) < ∞` are integer multiplicity — is the case `n − 1 = 0` (`iwl_zero_dim_integrality`) for `n = 1` and the inductive hypothesis (with `∂∂ = 0`) for `n ≥ 2`.  Given BLI: * `P < n`: every `n`-covector on `ℝ^P` vanishes, so `T = 0 = τ(∅, 1, 0)`; * `P = n`: Remark 3.12 (`iwl_top_dim_integrality`); * `P ≥ n + 1`: localize to compactly supported currents in `ℝ^P` (Remark 8.3(1), `iwl_localization`) and reduce to cycles by cones (`iwl_cycle_reduction`).  For cycles, `Θ*ⁿ(μ_T, ·) > 0` `μ_T`-a.e. (printed (1)–(6), `iwl_positive_density`), so `T` is rectifiable by 8.1, and its multiplicity is integer valued (printed (7)–(10), `iwl_integer_density`).
- **Calls**: `iwl_top_dim_integrality`, `iwl_localization`, `slicing_theorem` (A.5), `iwl_cycle_reduction`, `lipschitz_pushforward_integer_multiplicity` (A.4), `rectifiability_theorem` (A.3), `iwl_positive_density`, `isoperimetric_theorem` (A.7), `iwl_integer_density`, `iwl_zero_dim_integrality`
- **Called by**: `boundary_rectifiability`, `federer_fleming_compactness`, `main_theorem`

#### `iwl_top_dim_integrality` (L67311)

- `root.integrality_weak_limits-a1.top_dim-a1` · issue #934 · PR #4089 · candidate `e7ec1ab7ad46`
- **Statement and proof** (no doc comment in the source; summary of the Lean proof **[corrected]**): **Remark 3.12: Theorem 8.2 in top dimension.** If `U ⊆ ℝⁿ`, `n = m + 1`, is open, the `T_j ∈ 𝒟ₙ(U)` are integer multiplicity, `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for every `W ⊂⊂ U` and `T_j ⇀ T`, then `T` is integer multiplicity. Proof (BV compactness, proved here): every `T_j` acts as `ω ↦ ∫ β_j ω(e) dLⁿ` with `β_j` Borel, integer valued and locally integrable, since the orientation of a top-dimensional triple is `±e₁ ∧ ⋯ ∧ eₙ`; the translation estimate (Remark 2.35) bounds `∫_K |β_j(· + z) − β_j|` by a multiple of `|z| M_V(∂T_j)` for `|z| ≤ δ`, where `V ⊆ U` is open and contains the closed `2δ`-neighbourhood of `K` **[corrected]**; with `L¹` duality against smooth functions and mollification, weak convergence makes `(β_j)` Cauchy in `L¹` on compact subsets of `U`; a fast subsequence converges a.e. and in `L¹_loc` to an integer-valued Borel `β`; `T(ω) = ∫ β ω(e)`; at Lebesgue points of `β` the weighted tangent space of `({β ≠ 0}, |β|)` is `ℝⁿ` (`iwl_weighted_tangent_locality`), so `T = τ({β ≠ 0}, |β|, sign(β) e₁ ∧ ⋯ ∧ eₙ)`.
- **Correction**: the previous revision of this file labelled this summary as a summary of the accepted natural-language proof. It summarizes the Lean proof, which proves the BV compactness for this sequence through a translation estimate; the accepted natural-language proof (step 4) cites the Compactness Theorem for BV functions, Simon Ch. 2, 2.6, instead. The summary also stated the translation estimate without its smallness condition; the Lean proof (lines 67709–67716) proves it for `|z| ≤ δ` with `cthickening(2δ, K) ⊆ V`, and it fails for large `z`: for `U = B₁(0)`, `T_j = [[U]]` (`β_j = 1` on `U`, `0` off `U`), `K = B̄_{1/2}(0)` and `V = B_{3/4}(0)`, `M_V(∂T_j) = 0` but `∫_K |β_j(· + e₁) − β_j| > 0`.
- **Calls**: `iwl_weighted_tangent_locality` (A.6)
- **Called by**: `iwl_integer_density`, `integrality_of_weak_limits`

#### `iwl_localization` (L57577)

- `root.integrality_weak_limits-a1.localization-a1` · issue #951 · PR #5185 · candidate `f49fc62e2a30`
- **Statement and proof**: **Simon Ch. 6, Remark 8.3(1) (p. 176).**  Assuming the slicing theorem, Theorem 8.2 on an open `U ⊆ ℝ^P` follows from its case for currents in `ℝ^P` supported in a fixed compact set. Near each `ξ₀ ∈ U`: slice the `T_j` by `|x - ξ₀|`; choose (Fatou, Helly) a radius `r` with integer multiplicity slices of bounded mass along a subsequence on which `T_j ⌞ B_r(ξ₀) ⇀ T ⌞ B_r(ξ₀)`; extend these integral currents to `ℝ^P` by a cutoff `χ` (`Z ↦ Z(χ ·)`, continuous by the mass bound), apply the compact case and restrict back to `U`. Then `T = T ⌞ B_r(ξ₀)` near `ξ₀`, and the local representations patch together (`iwl_im_patching`).  The auxiliary facts are local steps.
- **Calls**: `cmb_abs_apply_le_of_massOn_le` (A.1), `br_weightedTangent_congr` (A.3), `iwl_restriction_theory` (A.6), `iwl_im_closure`, `iwl_im_patching`, `iwl_restriction_weak_limit`
- **Called by**: `integrality_of_weak_limits`

#### `iwl_im_closure` (L54313)

- `root.integrality_weak_limits-a1.im_closure-a1` · issue #940 · PR #4963 · candidate `4c06fc8afebf`
- **Statement and proof**: **Integer multiplicity currents (Simon Ch. 6, 3.2 Remarks (1), (3) and 2.9).**  For open `U ⊆ ℝ^P`: (a) an integer multiplicity `X = τ(M, θ, ξ)` has `M_W(X) < ∞` for `W ⊂⊂ U`, since `(Hᵏ ⌞ M, θ ξ)` represents `X` (2.7) and (R0) of `iwl_restriction_theory` applies; (b) a restriction `S = X ⌞ A` is `τ(M ∩ A, θ, ξ)` by uniqueness of the representation, and the tangent comparison principle (T) (`iwl_imc_tangent_overlap`, fed by the locality of weighted tangent spaces `iwl_weighted_tangent_locality`) transfers the tangent spaces of `(M, θ)` to `(M ∩ A, θ)` a.e. on `M ∩ A`; (c) `Z = aX + bY` is integer multiplicity by `iwl_imc_lincomb_im`, again fed by (T).
- **Calls**: `iwl_imc_tangent_overlap`, `iwl_weighted_tangent_locality` (A.6), `iwl_restriction_theory` (A.6), `iwl_imc_tau_measure_representation`, `slicing_representation_unique` (A.5), `iwl_imc_lincomb_im`
- **Called by**: `iwl_localization`, `iwl_cycle_reduction`

#### `iwl_imc_tangent_overlap` (L37885)

- `root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1` · issue #2820 · PR #4894 · candidate `840ab47ea3d0`
- **Statement and proof**: Tangent planes agree on the overlap (for Simon Ch. 6, 3.2 (1); Ch. 3, 1.7): given the tangent locality (TL), an open `U` and `Hᵏ`-null-measurable `M₁, M₂ ⊆ U` with `θ_l ≥ 1` on `M_l` and `θ_l` integrable on `M_l ∩ K` for compact `K ⊆ U` **[corrected]**, for `Hᵏ⌞(M₁ ∩ M₂)`-a.e. `x` every weighted approximate tangent plane of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  At normalized Lebesgue points of `θ₁, θ₂` on `M₁ ∩ M₂` where `M₁ Δ M₂` has density zero, (TL) compares each `(M_l, θ_l)` with the constant weight `θ_l(x)` on `M₁ ∩ M₂`, and a nonzero constant factor does not change the tangent condition.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not introduce the pairs `(M_l, θ_l)`; the Lean statement (line 37885) assumes these hypotheses.
- **Calls**: `iwl_imc_normalized_lebesgue_points` (A.6), `iwl_imc_density_zero_off_set`
- **Called by**: `iwl_im_closure`

#### `iwl_imc_density_zero_off_set` (L37453)

- `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1` · issue #2799 · PR #4846 · candidate `4eb4d55a3670`
- **Statement and proof**: Upper density theorem at every scale `Rr` (Simon Ch. 1, 3.6 with Remark 3.7(2)): if `U` is open, `S` is `Hᵏ`-null-measurable **[corrected]** and `∫⁻_{S ∩ K} g dHᵏ < ∞` for every compact `K ⊆ U`, then for `Hᵏ`-a.e. `x ∈ U \ S` and every `R > 0`, `r⁻ᵏ ∫⁻_{S ∩ B̄_{Rr}(x)} g dHᵏ → 0` as `r → 0+`.  The unit-scale case `ρ⁻ᵏ ∫⁻_{S ∩ B̄_ρ(x)} g dHᵏ → 0` is `lpf_wtc_ae_zero_density_off_set`; the change of scale `ρ = Rr` is `iwl_imc_quotient_rescale_tendsto_zero`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 37453); Simon's Ch. 1, 3.6 likewise concerns a measurable set. See the example in the entry `lpf_wtc_ae_zero_density_off_set`.
- **Calls**: `lpf_wtc_ae_zero_density_off_set` (A.4), `iwl_imc_quotient_rescale_tendsto_zero`
- **Called by**: `iwl_imc_tangent_overlap`

#### `iwl_imc_quotient_rescale_tendsto_zero` (L11439)

- `root.integrality_weak_limits-a1.im_closure-a1.density_zero_off_set-a1.quotient_rescale-a1` · issue #4144 · PR #4696 · candidate `02defef5b53b`
- **Statement and proof**: Rescaling a vanishing normalized quotient: if `F(ρ) / ρᵏ → 0` as `ρ → 0+`, then `r⁻ᵏ · F(R r) → 0` as `r → 0+` for every `R > 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_imc_density_zero_off_set`

#### `iwl_imc_tau_measure_representation` (L11472)

- `root.integrality_weak_limits-a1.im_closure-a1.tau_repr-a1` · issue #2809 · PR #3694 · candidate `3b2abc0b5a5e`
- **Statement and proof**: **`(Hᵏ⌞M, θξ)` represents `τ(M, θ, ξ)` as in (2.7) (Simon Ch. 6, 3.1, p. 146).**  If `X(ω) = τ(M, θ, ξ)(ω)` for every `ω ∈ 𝒟ᵏ(U)` and `(M, θ, ξ)` is a rectifiable triple in `U`, then `⟨ω, θξ⟩` is `Hᵏ⌞M`-integrable and `X(ω) = ∫ ⟨ω, θξ⟩ d(Hᵏ⌞M)`.  Pointwise `⟨ω(x), θ(x)ξ(x)⟩ = θ(x)⟨ω(x), ξ(x)⟩`, which is integrable on `M` by `ltg_tau_integrable` since a test form is continuous with compact support in `U`.
- **Calls**: `ltg_tau_integrable` (A.5)
- **Called by**: `iwl_imc_lincomb_im`, `iwl_imc_restriction_im` (A.13, unused), `iwl_im_closure`

#### `iwl_imc_lincomb_im` (L37473)

- `root.integrality_weak_limits-a1.im_closure-a1.lincomb_im-a1` · issue #2832 · PR #4290 · candidate `99bffd2f215d`
- **Statement and proof**: **Integer linear combinations of integer multiplicity currents (Simon Ch. 6, 3.2 Remark (1), p. 146), given tangent comparison.**  Assume (T): for null-measurable `M₁, M₂ ⊆ U` and `θ₁, θ₂ ≥ 1` on them, locally `Hᵏ`-integrable in `U`, at `Hᵏ`-a.e. `x ∈ M₁ ∩ M₂` every weighted approximate tangent space of `(M₁, θ₁)` is one of `(M₂, θ₂)`.  Let `X = τ(M₁, θ₁, ξ₁)`, `Y = τ(M₂, θ₂, ξ₂)` and `Z = aX + bY` with `a, b ∈ ℤ`.  By (T) and `fiw_ims_orientation_sign`, `ξ₁ = ±ξ₂` a.e. on `M₁ ∩ M₂`.  With `σ = -1` on the anti-aligned part of the overlap and `1` elsewhere, `c = a 1_{M₁}θ₁ + bσ 1_{M₂}θ₂` is integer-valued, and `Z = τ(M, θ, ξ)` for `M = {c ≠ 0}`, `θ = |c|`, `ξ = sgn(c) ξ₀` (`ξ₀ = ξ₁` on `M₁`, `ξ₂` on `M₂ \ M₁`): a.e. `a 1_{M₁}θ₁⟨ω, ξ₁⟩ + b 1_{M₂}θ₂⟨ω, ξ₂⟩ = 1_M θ⟨ω, ξ⟩`, integrable by `iwl_imc_tau_measure_representation`.  (T) for `(M_l, θ_l)` and `(M, θ)` transfers the orientations, so `(M, θ, ξ)` is a rectifiable triple.
- **Calls**: `fiw_ims_orientation_sign` (A.6), `iwl_imc_tau_measure_representation`
- **Called by**: `iwl_im_closure`

#### `iwl_im_patching` (L36691)

- `root.integrality_weak_limits-a1.patching-a1` · issue #928 · PR #2913 · candidate `c9a4db0e8a68`
- **Statement and proof**: **Patching lemma** (P4) of the proof of Simon Ch. 6, 8.2 (Remark 8.3(1)): a current that agrees near every point of `U` with an integer multiplicity current is integer multiplicity. By Lindelöf, countably many `V (e i)` cover `U`, with `X = Y (e i) = τ(Mᵢ, θᵢ, ξᵢ)` on forms supported in `V (e i)`.  On overlaps the vector densities `1_{Mᵢ} θᵢ ξᵢ` agree `Hᵏ`-a.e. (test with `g dx^β`, `g ∈ C_c^∞`, and expand covectors by `Submission.slicing_ru_covector_expansion`), hence so do the multiplicities `1_{Mᵢ} θᵢ`, since `‖ξᵢ‖ = 1` a.e. (`Submission.lpf_simple_nvector_algebra`).  The triple `(M, θ, ξ)` glued along `D i = V (e i) \ ⋃_{j < i} V (e j)` therefore agrees a.e. with `(Mᵢ, θᵢ, ξᵢ)` on `V (e i)`; `Submission.iwl_weighted_tangent_locality` transfers the orientation condition from `(Mᵢ, θᵢ)` to `(M, θ)`, and `X = τ(M, θ, ξ)` by a smooth partition of unity.
- **Calls**: `lpf_simple_nvector_algebra` (A.4), `slicing_ru_covector_expansion` (A.5), `iwl_weighted_tangent_locality` (A.6)
- **Called by**: `iwl_zero_dim_integrality`, `iwl_localization`

#### `iwl_restriction_weak_limit` (L54463)

- `root.integrality_weak_limits-a1.restriction_limit-a1` · issue #942 · PR #3781 · candidate `e20506c047f7`
- **Statement and proof**: **Restrictions of weakly convergent currents converge on forms supported in `W`, along a subsequence and for all but countably many levels (weakly if `{φ ≤ s}` lies in a compact subset of `W`)** **[corrected]** (Simon Ch. 6, Remark 8.3(1) and (1), (8) in the proof of 8.2, pp. 176 and 178 **[corrected]**: "4.5(1) and a selection arguments [sic] in 6.7(2) of Ch. 2").  `F_j(t) = M_{W ∩ {φ < t}}(X_j)` is nondecreasing in `t` and bounded by `sup_j M_W(X_j)`, so Helly selection gives `ψ` and a countable `E` such that for `s ∉ E` the increments `F_{ψ j}(b) - F_{ψ j}(a)` over some `a < s < b` are eventually small.  The restrictions give measure representations, hence mass measures (restriction theory). (A) For `tsupport ω ⊆ W` and `a < s`, a smooth cutoff `ω'` of `ω` vanishes on `{φ ≥ s}` and equals `ω` near `tsupport ω ∩ {φ ≤ a}`; the cutoff estimate bounds `|R_j ω - X_{ψ j} ω'|` by `c (F_{ψ j}(s) - F_{ψ j}(a))` and `|R ω - X ω'|` by `c (M_{W_s}(X) - M_{W_a}(X))`, which is small for `a` near `s` by continuity of `t ↦ M_{W_t}(X)` from below, while `X_{ψ j} ω' → X ω'`. (B) If `{φ ≤ s} ⊆ K ⊆ W`, a cutoff `ω''` equal to `ω` near `K` and supported in `W` has the same restrictions to `{φ < s}`, so (A) applied to `ω''` gives `R_j ω → R ω`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), gives p. 176 for all of these. Remark 8.3(1) and display (1) are on p. 176. Display (8) and the quoted phrase are on p. 178, where the book prints "justified by 4.5(1) and a selection arguments in 6.7(2) of Ch. 2". Remark 8.3(1) has the similar "an argument like that in 6.7(2) of Ch. 2". The title of the doc comment claims the convergence without qualification, which is false: for `X_j = δ_{1/j} ⇀ X = δ₀` in `ℝ` and `φ(x) = −x`, the restrictions to `{φ < 0} = {x > 0}` are `δ_{1/j} ⇀ δ₀`, while `X ⌞ {x > 0} = 0`. The Lean statement (line 54463) gives it along a subsequence `ψ`, for levels `s` outside a countable set, on forms supported in `W` (and weakly if `{φ ≤ s}` lies in a compact subset of `W`). The quotation also read "a selection argument as in 6.7(2)"; it now follows the printed wording.
- **Calls**: `iwl_rl_monotone_helly_selection`, `iwl_restriction_theory` (A.6), `br_la_testForm_covectorNorm_bounded` (A.6), `iwl_rl_massOn_iUnion_monotone`, `iwl_rl_testForm_smooth_cutoff`, `iwl_rl_restriction_cutoff_estimate`
- **Called by**: `iwl_localization`, `iwl_positive_density`, `iwl_integer_density`

#### `iwl_rl_monotone_helly_selection` (L11495)

- `root.integrality_weak_limits-a1.restriction_limit-a1.helly_selection-a1` · issue #2477 · PR #3497 · candidate `a66a1c569019`
- **Statement and proof**: **Helly selection with a countable exceptional set** (the selection step in the proof of Simon Ch. 6, 8.2 and Remark 8.3(1), p. 176: "an argument like that in 6.7(2) of Ch. 2"). Nondecreasing `F j : ℝ → ℝ` with `|F j t| ≤ C` have a subsequence `F (ψ j)` converging at every rational to a nondecreasing `g` (Tychonoff for `∏_{q ∈ ℚ} [-C, C]`).  The left envelope `F⁻(t) = sup_{q < t} g(q)` is nondecreasing, so its discontinuity set `E` is countable; for `s ∉ E`, rationals `a < s < b` near `s` give `g(b) - g(a) < ε`, hence `F (ψ j) b - F (ψ j) a < ε` for all large `j`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_restriction_weak_limit`

#### `iwl_rl_massOn_iUnion_monotone` (L11596)

- `root.integrality_weak_limits-a1.restriction_limit-a1.mass_iunion-a1` · issue #2496 · PR #3480 · candidate `fc246393d257`
- **Statement and proof**: **Local mass along increasing unions of open sets** (continuity from below of `W ↦ M_W(T)` on open sets, used in the selection argument of Simon Ch. 6, Remark 8.3(1), p. 176).  If `O₀ ⊆ O₁ ⊆ ⋯` are open, then `M_{⋃ᵢ Oᵢ}(T) = supᵢ M_{Oᵢ}(T)` in `[0, ∞]`.  `≥` is monotonicity of `M`.  For `≤`, a form admissible for `⋃ᵢ Oᵢ` has compact support, which the increasing open cover `(Oᵢ)` covers by a single `Oᵢ`; the form is then admissible for that `Oᵢ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_restriction_weak_limit`

#### `iwl_rl_testForm_smooth_cutoff` (L11547)

- `root.integrality_weak_limits-a1.restriction_limit-a1.testform_cutoff-a1` · issue #2487 · PR #3469 · candidate `95d4fa1296da`
- **Statement and proof**: **Smooth cutoff of a test form between two disjoint closed sets** (the cutoffs `ω′`, `ω″` of steps (A), (B) of `iwl_restriction_weak_limit`, which formalizes the selection step of Simon Ch. 6, Remark 8.3(1), p. 176 **[corrected]**).  Normality of `ℝ^P` gives open `N₀ ⊇ C₀` and `N₁ ⊇ C₁` with disjoint closures, and the smooth Urysohn lemma gives a `C^∞` function `χ : ℝ^P → [0, 1]` with `χ = 0` on `closure N₀` and `χ = 1` on `closure N₁`.  Then `ω' = χ ω` is a test form in `U` with `tsupport ω' ⊆ tsupport ω`, and `|ω - ω'| = (1 - χ) |ω| ≤ |ω|` by homogeneity of the Euclidean coefficient norm.
- **Correction**: the Lean doc comment, kept byte-identical (§9), says "the cutoffs `χω` and `ζω` in the proof of Simon Ch. 6, 8.2, p. 176". Simon's proof of 8.2 (pp. 176–179) contains no cutoffs `χω`, `ζω` between two disjoint closed sets; its only modification of test forms, the extension `ω̃` of a form on `Ω` by `0` (p. 179), serves to define the currents `S̃_j`. The cutoff is a device of the formal proof, used only in `iwl_restriction_weak_limit`. That lemma formalizes the selection argument of Remark 8.3(1) and the choice of subsequence for (8) in the proof of 8.2.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_restriction_weak_limit`

#### `iwl_rl_restriction_cutoff_estimate` (L54369)

- `root.integrality_weak_limits-a1.restriction_limit-a1.cutoff_estimate-a1` · issue #2516 · PR #3562 · candidate `9ca4ad88cb32`
- **Statement and proof**: Cutoff estimate: let `W ⊆ U` be open, `φ` continuous on `U`, `a < s` and `M_W(Y) < ∞`, and let a measure give the masses of the restrictions of `Y` **[corrected]**. If `S = Y ⌞ {φ < s}`, `ω'` vanishes where `φ ≥ s`, and `ω - ω'` is supported in `{x ∈ W : a < φ x}` with `|ω - ω'| ≤ c`, then `|S(ω) - Y(ω')| ≤ c (M_{W ∩ {φ < s}}(Y) - M_{W ∩ {φ < a}}(Y))`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (lines 54371–54375). `a < s` is necessary: for `P = 1`, `k = 0`, `W = U = ℝ`, `φ(x) = x`, `s = 0`, `a = 1`, `Y = δ_{1/2}`, `ω′ = 0` and `ω` a bump with `0 ≤ ω ≤ 1` supported in `(1, 3)`, all other hypotheses hold with `c = 1`, but the claim reads `0 ≤ −1`.
- **Calls**: `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `iwl_restriction_weak_limit`

#### `iwl_cycle_reduction` (L58218)

- `root.integrality_weak_limits-a1.cycle_reduction-a1` · issue #953 · PR #5368 · candidate `9801717d461a`
- **Statement and proof**: **Reduction to cycles** in the proof of Simon Ch. 6, Theorem 8.2 (p. 176, the paragraph after display (1) **[corrected]**): the general case follows from the case `∂T = 0`.  Let `T_j ⇀ T` with `T_j, ∂T_j` integer multiplicity, `spt T_j ⊆ K` compact and `Λ = sup_j (M(T_j) + M(∂T_j)) < ∞`.  By the boundary hypothesis (BLI), `∂T` is integer multiplicity.  All supports lie in a ball `B̄_R(0) ⊇ K`, and the cones `C_j = 0 ⨯ ∂T_j`, `C = 0 ⨯ ∂T` are integer multiplicity with `∂C_j = ∂T_j`, `spt C_j ⊆ B̄_R(0)`, `M(C_j) ≤ cR M(∂T_j)` and `C_j ⇀ C`.  Hence the `T'_j = T_j - C_j` are integer multiplicity cycles in `B̄_R(0)` with `M(T'_j) ≤ (1 + cR) Λ` and `T'_j ⇀ T' = T - C`, so `T'` is integer multiplicity by the cycle hypothesis (Cyc), and so is `T = T' + C`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "the paragraph before (2)". The reduction to `∂T = 0` is the paragraph after display (1) on p. 176; the text before display (2) defines `f(r) = M(T ⌞ B_r(ξ))`.
- **Calls**: `iwl_cr_support_lemmas` (A.6), `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_cone_integer_multiplicity`, `iwl_im_closure`, `iwl_smooth_pushforward`
- **Called by**: `integrality_of_weak_limits`

#### `iwl_cr_cone_exists` (L12725)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1` · issue #2737 · PR #4818 · candidate `3a7a4af18cf4`
- **Statement and proof**: The cone `0 ⨯ X` over `X ∈ 𝒟ₘ(ℝ^P)` with `spt X ⊆ B̄_R(0)` (**Simon Ch. 6, 2.23, 2.30**): `C(ω) := X(Φ ω)` for the cut-off radial operator `Φ ω = ζ · Hω`, which satisfies `Hω(x)(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` on `B_r(0)`, `r = max R 0 + 1`.  `Φ` maps null sequences to null sequences, so `C` is a current; a test form `ψ` with the `Hω`-formula on an open `N ⊇ spt X` agrees with `Φ ω` on the open `N ∩ B_r(0) ⊇ spt X`, so `X ψ = X (Φ ω) = C ω` by locality.
- **Calls**: `iwl_cr_ce_cutoff_radial_operator`, `iwl_cr_radial_operator`, `iwl_cr_ce_apply_eq_of_eqOn_nhds_support` (A.6)
- **Called by**: `iwl_cycle_reduction`

#### `iwl_cr_ce_cutoff_radial_operator` (L11734)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_radial-a1` · issue #3724 · PR #4520 · candidate `36fae233c91b`
- **Statement and proof**: **The cut-off radial operator** behind the cone `h#([[(0,1)]] × T)`, `h(t, x) = t x` (Simon Ch. 6, 2.30), with `h#` taken through a cut-off `ζ` as in 2.23.  Choose `ψ_ω` as in (H) for each `ω ∈ 𝒟ᵐ⁺¹(ℝ^P)`; by (i), `ω ↦ ψ_ω` is linear.  For `r₀ = max r 0` and a bump `ζ` with `ζ = 1` on `B̄_{r₀+1}(0)` and `spt ζ = B̄_{r₀+2}(0)`, `Φ(ω) = ζ ψ_ω` is a linear map `𝒟ᵐ⁺¹(ℝ^P) → 𝒟ᵐ(ℝ^P)` agreeing with `ψ_ω` on `B_r(0)`.  If `ω_l → 0`, then for `i ≤ j` eventually `‖Dⁱω_l‖ ≤ ε / (r₀ + 2 + j)` on all of `ℝ^P`, so (iii) gives `‖Dʲψ_{ω_l}‖ ≤ ε` on `spt ζ`, and `iwl_cr_ce_cutoff_converges_zero` yields `Φ(ω_l) → 0`.
- **Calls**: `iwl_cr_ce_cutoff_converges_zero`
- **Called by**: `iwl_cr_cone_exists`

#### `iwl_cr_ce_cutoff_converges_zero` (L11634)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_null-a1` · issue #3711 · PR #4473 · candidate `1ce45c2246fb`
- **Statement and proof**: Cut-off of a null sequence: let `ζ` be smooth with compact support in `U` and the `ψ_l` smooth **[corrected]**. If every derivative of `ψ_l` tends to `0` uniformly on `K = tsupport ζ`, then the test forms `φ_l = ζ ψ_l` tend to `0` in `𝒟ᵏ(U)`.  By the Leibniz rule, `D^j φ_l` is controlled on `K` by the bounded derivatives of `ζ` and the derivatives of `ψ_l` of order `≤ j`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves these hypotheses of the Lean statement (line 11634) implicit.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ce_cutoff_radial_operator`

#### `iwl_cr_radial_operator` (L12404)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1` · issue #2723 · PR #4671 · candidate `17ec2f4cdda3`
- **Statement and proof**: The radial homotopy operator `ψ(x) = ∫₀¹ tᵃ x ⌟ ω(t x) dt` (Part I of the accepted natural-language proof of `iwl_cycle_reduction`, in the proof of Simon Ch. 6, 8.2 **[corrected]**): for a smooth `(k + 1)`-form `ω`, `ψ` is a smooth `k`-form with (i) `ψ(x)(v) = ∫₀¹ tᵃ ω(t x)(x, v) dt`, (ii) `Dψ(x)[w](v) = ∫₀¹ tᵃ (t Dω(t x)[w](x, v) + ω(t x)(w, v)) dt`, and (iii) `‖Dʲψ(x)‖ ≤ (R + j) D` on `B̄_R(0)` whenever `‖Dⁱω‖ ≤ D` there for all `i ≤ j`. The integrand `F(t, x) = tᵃ • (ω(t x)).curryLeft x` is jointly smooth, so `ψ = ∫₀¹ F(t, ·) dt` is smooth with `Dʲψ = ∫₀¹ Dʲ_x F dt`; evaluation commutes with the integral.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "proof of Simon Ch. 6, 8.2, Part I". The printed proof has no parts; Part I ("the cone") is part of the accepted proof of `root.integrality_weak_limits-a1.cycle_reduction-a1`.
- **Calls**: `iwl_cr_ro_integrand_contDiff_fderiv`, `iwl_cr_ro_intervalIntegral_contDiff`, `iwl_cr_ro_integrand_iteratedFDeriv_le`
- **Called by**: `iwl_cr_cone_exists`, `iwl_cr_cone_estimates`, `iwl_cr_cone_boundary`, `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ro_integrand_contDiff_fderiv` (L12172)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_derivative-a1` · issue #3645 · PR #4470 · candidate `12cdbc2068ea`
- **Statement and proof**: Integrand of the radial homotopy operator.  For a `C^∞` `(k + 1)`-form `ω` and `a ∈ ℕ`, the map `F(t, x) = tᵃ • (ω(t • x)).curryLeft x`, i.e. `F(t, x)(v) = tᵃ ω(tx)(x, v)`, is `C^∞` on `ℝ × ℝ^P`, and for fixed `t` the derivative of `F(t, ·)` at `x` is `w ↦ (v ↦ tᵃ (t Dω(tx)[w](x, v) + ω(tx)(w, v)))`, where `(y, v) = Fin.cons y v`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_operator`

#### `iwl_cr_ro_intervalIntegral_contDiff` (L12060)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.parametric_integral-a1` · issue #3639 · PR #4402 · candidate `8eb2f9c26c58`
- **Statement and proof**: Smoothness of a parametric interval integral, with all derivatives under the integral sign: for `G : ℝ × ℝ^P → V` of class `C^∞` (`V` complete), `g x = ∫_a^b G(t, x) dt` is `C^∞`, every `x`-derivative `(t, x) ↦ ∂_x^j G(t, x)` is continuous, and `D^j g(x) = ∫_a^b ∂_x^j G(t, x) dt`. Proof.  For smooth `H : ℝ × ℝ^P → W` the `x`-derivative `H'(t, x) = DH(t, x) ∘ inr` is smooth with values in the complete space `ℝ^P →L W`.  Bounding `‖H'‖` on the compact set `[[a, b]] × closedBall x₀ 1` and differentiating under the integral sign gives `D(∫_a^b H(t, ·) dt) = ∫_a^b H'(t, ·) dt`.  Induction on `j`, over all complete codomains at once, identifies `D^{j+1}` with `D^j ∘ D` through the currying isometry, which commutes with the interval integral; `C^j` for every `j` is `C^∞`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_operator`

#### `iwl_cr_ro_integrand_iteratedFDeriv_le` (L12239)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1` · issue #3652 · PR #4425 · candidate `a318ea6a76a5`
- **Statement and proof**: Bound on the `j`-th derivative of the radial-homotopy integrand: for `t ∈ [0, 1]` and `‖x‖ ≤ R`, `‖D^j (z ↦ t^a • ι_z ω(t z))(x)‖ ≤ (R + j) D` when `‖D^i ω‖ ≤ D` on `closedBall 0 R` for all `i ≤ j`.  Writing the integrand as `t^a • B (g z) z` with `g z = ω (t • z)` and `B` the interior product (`‖B u v‖ ≤ ‖u‖ ‖v‖`), the Leibniz rule for `z ↦ B (g z) z`, proved below by induction on the order, gives `‖D^j (B (g ·) ·)(x)‖ ≤ ‖x‖ ‖D^j g(x)‖ + j ‖D^(j-1) g(x)‖`, and `‖D^i g(x)‖ ≤ ‖D^i ω(t x)‖ ≤ D` since `‖t x‖ ≤ R`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_operator`

#### `iwl_cr_cone_estimates` (L12750)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1` · issue #2743 · PR #4825 · candidate `ea4ec8d78d8b`
- **Statement and proof**: **Cone estimates** (items 3–4 of the cycle reduction; cf. the cone 2.30 and the mass bound 2.27 of Simon Ch. 6).  With `c = P^{2m+1}` and `R ≥ 0`: if `spt X ⊆ B̄_R(0)` and `C` is a cone over `X`, i.e. `C(ω) = X(ψ)` whenever `ψ(x)(v) = ∫₀¹ t^m ω(tx)(x, v) dt` near `spt X`, then `spt C ⊆ B̄_R(0)` and, if `M(X) < ∞` **[corrected]**, `M(C) ≤ c R M(X)`; and if `X_j ⇀ X` (all supported in `B̄_R(0)`), the cones `C_j` over `X_j` converge weakly to `C`.  Each `ω` is tested through one cut-off radial form `ψ = ζ ψ_ω`, with `ζ = 1` near `B̄_R(0)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), states the mass bound without the hypothesis `M(X) < ∞` of the Lean statement (line 12750); for `R = 0` and `M(X) = ∞` the right side would be read as `0`.
- **Calls**: `iwl_cr_radial_operator`, `iwl_cr_cest_cutoff_radial_form`, `iwl_cr_cest_cone_support`, `iwl_cr_cest_mass_le_of_forms`
- **Called by**: `iwl_cycle_reduction`

#### `iwl_cr_cest_cutoff_radial_form` (L11923)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cutoff_radial_form-a1` · issue #3831 · PR #4489 · candidate `6b30182501b5`
- **Statement and proof**: **Cut-off radial form** (cone construction, Simon Ch. 6, 2.30–2.32 (pp. 141–142), as used in the proof of 8.2).  Let `ψ₀(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt` be smooth and `0 < r < s`.  For the bump function `ζ` equal to `1` on `B̄_r(0)` with support `B_s(0)`, `ψ = ζ ψ₀` is a test form agreeing with `ψ₀` on `B_r(0)`.  If `|ω| ≤ 1`, then `|ψ(x)| = ζ(x) |ψ₀(x)|`, which is at most `P^{2m+1} ‖x‖ ≤ P^{2m+1} s` for `‖x‖ < s` and `0` otherwise.
- **Calls**: `iwl_cr_cest_radial_coeff_bound`
- **Called by**: `iwl_cr_cone_estimates`

#### `iwl_cr_cest_radial_coeff_bound` (L11846)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.radial_coeff_bound-a1` · issue #3827 · PR #4466 · candidate `2b063dab92a3`
- **Statement and proof**: **Radial coefficient bound** (for the cone mass estimate, Simon Ch. 6, 2.27 and 2.30, pp. 140–141, in the proof of 8.2, p. 177).  If `|ω(y)| ≤ 1` for all `y` and `β(v) = ∫₀¹ tᵐ ω(tx)(x, v) dt` for all `v`, then `|β| ≤ P^{2m+1} |x|`, `|·|` the Euclidean coefficient norm of Remark 2.6.  Put `K = P^{m+1} |x|`.  If `|u_i| ≤ 1` for all `i`, then `α(x, u) = |x| α(x/|x|, u)`, so `|α(x, u)| ≤ K |α|` by `isoperimetric_abs_covector_apply_le`. Hence `|β(e_I)| ≤ K` for each of the `P^m` maps `I : Fin m → Fin P`, and `|β| ≤ (P^m K²)^{1/2} ≤ P^m K = P^{2m+1} |x|`.
- **Calls**: `isoperimetric_abs_covector_apply_le` (A.7)
- **Called by**: `iwl_cr_cest_cutoff_radial_form`

#### `iwl_cr_cest_cone_support` (L11970)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cone_support-a1` · issue #3836 · PR #4458 · candidate `87574e154778`
- **Statement and proof**: **Support of the cone** (the cone `0 ⨯ X` of Simon Ch. 6, 2.30, p. 141).  Suppose `spt X ⊆ B̄_R(0)` and `C(ω) = X(ψ)` whenever `ψ` agrees on an open neighbourhood of `spt X` with the radial form `x ↦ ∫_0^1 t^m ω(tx)(x, ·) dt`.  Then `spt C ⊆ B̄_R(0)`: for `‖p‖ > R` and `r = (‖p‖ − R)/2`, a test form `ω` supported in `B_r(p)` vanishes at `tx` for `x ∈ B_{R+r}(0)`, `t ∈ [0, 1]`, so `ψ = 0` is admissible and `C(ω) = X(0) = 0`; thus `C` vanishes on `B_r(p)` and `p ∉ spt C`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_cone_estimates`

#### `iwl_cr_cest_mass_le_of_forms` (L12013)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.mass_le_of_forms-a1` · issue #3840 · PR #4428 · candidate `9635524d1d0b`
- **Statement and proof**: Mass comparison through bounded transfer forms: let `c, R ≥ 0` and `M(X) < ∞` **[corrected]**. If for every mass-admissible `ω` and `δ > 0` there is a test form `ψ` with `C(ω) = X(ψ)` and `|ψ(x)| ≤ c (R + δ)` everywhere, then `M(C) ≤ c R · M(X)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 12015).
- **Calls**: `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `iwl_cr_cone_estimates`

#### `iwl_cr_cone_boundary` (L12789)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_boundary-a1` · issue #2754 · PR #4828 · candidate `0b613484ca22`
- **Statement and proof**: Simon 2.31 for `X = ∂Y` with `spt Y` compact: the cone `C = 0 ⨯ ∂Y` (`C(ω) = ∂Y(ψ)` whenever `ψ = H(ω)` near `spt ∂Y`) has `∂C = ∂Y`.  For `φ ∈ 𝒟ᵐ` the radial form `χ = H(dφ)` satisfies `dχ = dφ` by the radial homotopy formula, and `ζχ`, with a cut-off `ζ = 1` near `spt Y`, is admissible in the cone identity, so `∂C(φ) = C(dφ) = Y(d(ζχ)) = Y(dφ) = ∂Y(φ)`.
- **Calls**: `iwl_cr_radial_homotopy`, `iwl_cr_radial_operator`, `iwl_cr_support_lemmas` (A.6), `isoperimetric_apply_eq_zero_of_disjoint_support` (A.6)
- **Called by**: `iwl_cycle_reduction`

#### `iwl_cr_radial_homotopy` (L12610)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1` · issue #2729 · PR #4464 · candidate `0ca2206b7fe4`
- **Statement and proof**: **Radial homotopy formula on `ℝ^P`** (the form version of Simon Ch. 6, 2.25–2.26 and 2.31 for the homotopy `(t, x) ↦ t x`, used by the cone construction in the proof of 8.2). (a) If `φ` is a smooth `(k + 1)`-form, `Dψ(x)[w](v) = ∫₀¹ tᵏ (t Dφ(tx)[w](x, v) + φ(tx)(w, v)) dt` and `χ(x)(v) = ∫₀¹ tᵏ⁺¹ dφ(tx)(x, v) dt`, then `χ + dψ = φ`, i.e. `H(dφ) + d(H′φ) = φ`. (b) For a smooth `0`-form `φ`, `H(dφ)(x) = φ(x) − φ(0)`. For (a), `dψ(x)(u) = ∑ⱼ (-1)ʲ Dψ(x)[uⱼ](ûⱼ)` with `ûⱼ = removeNth j u`.  All integrands are continuous, so `χ(x)(u) + dψ(x)(u)` is a single integral over `[0, 1]`.  The cross terms cancel and `∑ⱼ (-1)ʲ α(uⱼ, ûⱼ) = (k + 1) α(u)`, so its integrand is `tᵏ⁺¹ Dφ(tx)[x](u) + (k + 1) tᵏ φ(tx)(u)`, the derivative of `t ↦ tᵏ⁺¹ φ(tx)(u)`, whose integral over `[0, 1]` is `φ(x)(u)`.
- **Calls**: `iwl_cr_rh_degree_zero`, `iwl_cr_rh_radial_ftc`, `iwl_cr_rh_integrand_identity`
- **Called by**: `iwl_cr_cone_boundary`

#### `iwl_cr_rh_degree_zero` (L12565)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.degree_zero-a1` · issue #3520 · PR #4109 · candidate `4f025a59c215`
- **Statement and proof**: Radial homotopy formula in degree zero: if `χ(x)(v) = ∫₀¹ t⁰ dφ(t x)(x, v) dt` for a smooth `0`-form `φ`, then `χ(x) = φ(x) - φ(0)` (fundamental theorem of calculus along `t ↦ t x`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_homotopy`

#### `iwl_cr_rh_radial_ftc` (L12523)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.radial_ftc-a1` · issue #3513 · PR #4283 · candidate `af76167caf31`
- **Statement and proof**: Radial fundamental theorem of calculus: for a smooth form `φ`, `∫₀¹ (t^(m+1) Dφ(t x)[x](u) + (m + 1) t^m φ(t x)(u)) dt = φ(x)(u)`, since the integrand is the derivative of `g(t) = t^(m+1) φ(t x)(u)` and `g(1) - g(0) = φ(x)(u)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_homotopy`

#### `iwl_cr_rh_integrand_identity` (L12475)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1.integrand_identity-a1` · issue #3503 · PR #4243 · candidate `79f67f54610d`
- **Statement and proof**: Pointwise integrand identity of the radial homotopy formula: for `L : E →L[ℝ] Λ^{k+1}(E)`, `α ∈ Λ^{k+1}(E)`, `x ∈ E`, `u ∈ E^{k+1}`, `t ∈ ℝ` and `û_j = removeNth j u`, `t^{k+1} Alt(L)(x, u) + ∑_j (-1)^j t^k (t L(u_j)(x, û_j) + α(u_j, û_j)) = t^{k+1} L(x)(u) + (k + 1) t^k α(u)`. Expanding `Alt(L)(x, u) = L(x)(u) - ∑_j (-1)^j L(u_j)(x, û_j)` cancels the `t^{k+1}` cross terms, and `alternatizeUncurryFin (curryLeft α) = (k + 1) • α` evaluates the `α`-sum.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_radial_homotopy`

#### `iwl_cr_cone_integer_multiplicity` (L36560)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1` · issue #2781 · PR #5305 · candidate `45a90f14d36d`
- **Statement and proof**: The cone `0 ⨯ X` over an integer multiplicity `X` with `spt X ⊆ B̄_R(0)` is integer multiplicity.  `Z = [[(0,1)]] × X` is integer multiplicity with compact support, so `H_push` gives its integer multiplicity push-forward `S` by the cone map `h(y) = y₀ • π(y)`.  Testing with `η = ϑ(y₀) ζ(π y) • h^# ω`, which agrees with `h^# ω` near `spt Z`, the slices of `η` are `ζ(x) sᵐ ω(s x)(x, ·)`, so `S(ω) = Z(η) = ∫₀¹ X(η_s) ds = X(ζ ψ_ω) = C(ω)` for the radial integral `ψ_ω(x)(v) = ∫₀¹ tᵐ ω(t x)(x, v) dt`.
- **Calls**: `iwl_cr_interval_product_im` (A.6), `iwl_cr_ci_product_support`, `iwl_cr_ci_cone_map`, `iwl_cr_ci_product_cutoff`, `iwl_cr_ci_cutoff_pullback_testForm`, `iwl_cr_ci_slice_testForm` (A.6), `iwl_cr_radial_operator`, `iwl_cr_ci_integral_exchange`
- **Called by**: `iwl_cycle_reduction`

#### `iwl_cr_ci_product_support` (L13041)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1` · issue #3627 · PR #4902 · candidate `340c43fe9003`
- **Statement and proof**: **Support of the product current `[[(0,1)]] × X`.**  With `Φ(s, x) = (s, x)`, the set `L = Φ([0, 1] × B̄_R(0))` is compact as a continuous image of a compact set, hence closed.  If `tsupport η` misses `L`, the slices `φ s = η(Φ(s, ·))(e₀, ι ·)` are annihilated by `X` (whose support lies in `B̄_R(0)`), so `Z η = ∫₀¹ X (φ s) ds = 0`; by the support criterion, `spt Z ⊆ L`.
- **Calls**: `fiw_tb_ext_support_subset`, `iwl_cr_ci_slice_testForm` (A.6), `iwl_cr_ci_ps_slice_integral_eq_zero`
- **Called by**: `iwl_cr_cone_integer_multiplicity`

#### `fiw_tb_ext_support_subset` (L692)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.support_subset-a1` · issue #3248 · PR #3752 · candidate `3d64216fd707`
- **Statement and proof**: **Support of a current vanishing off a closed set (Simon Ch. 6, 2.11).**  If `Z ∈ 𝒟_q(V)`, `V` open, kills every test form whose support misses the closed set `K`, then `spt Z ⊆ K`.  A point `x ∈ V \ K` has a ball `B_ε(x) ⊆ V \ K`; `W = B_{ε/2}(x)` is open with compact closure `closure W ⊆ B_ε(x) ⊆ V`, and `Z` vanishes on `W`, so `x` lies in the zero region of `Z`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ci_product_support`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`, `ind_pi_localized_cycles`

#### `iwl_cr_ci_ps_slice_integral_eq_zero` (L12884)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_support-a1.slice_integral_vanish-a1` · issue #4227 · PR #4864 · candidate `5570cd6a944d`
- **Statement and proof**: Slices of a form supported off `Φ([0, 1] × B̄_R(0))`, `Φ(s, x) = (s, x) ∈ ℝ^{P+1}`, are annihilated by `X`: for `s ∈ [0, 1]`, `tsupport (φ s)` lies in the closed set `{x | Φ(s, x) ∈ tsupport η}`, which misses `B̄_R(0) ⊇ spt X`, so `X (φ s) = 0` and the integral over `[0, 1]` vanishes.
- **Calls**: `isoperimetric_apply_eq_zero_of_disjoint_support` (A.6)
- **Called by**: `iwl_cr_ci_product_support`

#### `iwl_cr_ci_cone_map` (L13084)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cone_map-a1` · issue #3631 · PR #4364 · candidate `61b7d3fe17a4`
- **Statement and proof**: The cone map `h(y) = y₀ • π(y)`, `π(y) = (y₁, …, y_P)`, is a product of continuous linear maps, hence smooth, and `h(Φ(s, x)) = s • x` for `Φ(s, x) = (s, x)`.  By the product rule `Dh(y)(w) = y₀ • π(w) + w₀ • π(y)`, so `Dh(Φ(s, x))` maps `e₀ ↦ x` and `ι(w) = Φ(0, w) ↦ s • w`; multilinearity then gives `α(x, s • v₁, …, s • vₘ) = s ^ m * α(x, v₁, …, vₘ)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ci_product_cutoff` (L13161)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.product_cutoff-a1` · issue #3638 · PR #4286 · candidate `b4056df8fa7b`
- **Statement and proof**: The product `χ(y) = ϑ(y₀) ζ(π y)` of cut-offs on `ℝ` and `ℝ^P`, `π y = (y₁, …, y_P)`, is a cut-off on `ℝ^{P+1}`: `y ↦ y₀` and `π` are linear, so `χ` is smooth, and `‖y‖ ≤ |y₀| + ‖π y‖` puts `support χ` inside the compact ball `B̄_{a+b}(0)`, where `tsupport ϑ ⊆ B̄_a(0)` and `tsupport ζ ⊆ B̄_b(0)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ci_cutoff_pullback_testForm` (L13060)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.cutoff_pullback-a1` · issue #3628 · PR #4334 · candidate `15be873de6f5`
- **Statement and proof**: Cut-off pull-backs of smooth forms are test forms (step 5 of the accepted natural-language proof of `iwl_cr_cone_integer_multiplicity`, in the proof of Simon Ch. 6, 8.2 **[corrected]**): for smooth `f : ℝ^P → ℝ^Q`, a smooth form `ω` and a smooth compactly supported `χ`, `η(y) = χ(y) ω(f(y)) ∘ Df(y)` is smooth (the pull-back `B ↦ (α ↦ α ∘ B)` is analytic) and has compact support.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "step 5 of the proof of Simon Ch. 6, 8.2". The step is Step 5 ("A good `η`") of the accepted proof of `iwl_cr_cone_integer_multiplicity`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ci_integral_exchange` (L26756)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1` · issue #3644 · PR #4887 · candidate `533e83aac5a2`
- **Statement and proof**: **Exchange of an integer multiplicity current with `∫₀¹ ds` (Simon Ch. 6, 8.2, cone construction).**  Let `X = τ(M, θ, ξ)` be integer multiplicity, `(s, x) ↦ φ(s)(x)` continuous with `spt φ(s) ⊆ K` (`K` compact) for `s ∈ [0, 1]`, and `ψ(x)(v) = ∫₀¹ φ(s)(x)(v) ds`.  Then `∫₀¹ X(φ(s)) ds = X(ψ)`: `μ_K := Hᵐ⌞(M ∩ K)` is finite (`θ ≥ 1` on `M`), every `φ(s)` and `ψ` vanish off `K`, so `X(φ(s))` and `X(ψ)` are `μ_K`-integrals, and Fubini applies to `θ(x) ξ(x)(φ(s)(x))`, dominated by `B |θ(x)|` with `B = sup_{[0,1] × K} ‖φ‖` and `|ξ(x)(α)| ≤ ‖α‖`.
- **Calls**: `iwl_cr_ci_ie_measure_inter_compact_lt_top`, `fiw_ims_tt_unit_bound` (A.5), `iwl_cr_ci_ie_param_fubini`
- **Called by**: `iwl_cr_cone_integer_multiplicity`

#### `iwl_cr_ci_ie_measure_inter_compact_lt_top` (L13205)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.finite_measure-a1` · issue #4221 · PR #4808 · candidate `e3840f8472f6`
- **Statement and proof**: **`Hⁿ(M ∩ K) < ∞` for integer multiplicity triples (Simon Ch. 6, 3.1).**  If `(M, θ, ξ)` is a rectifiable triple in `U` and `θ` is integer-valued on `M`, then `θ ≥ 1` on `M` (`θ > 0`), so for compact `K ⊆ U`: `Hⁿ(M ∩ K) = ∫⁻_{M ∩ K} 1 dHⁿ ≤ ∫⁻_{M ∩ K} |θ| dHⁿ < ∞` (`θ` is `Hⁿ`-integrable on `M ∩ K`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ci_integral_exchange`

#### `iwl_cr_ci_ie_param_fubini` (L26706)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.param_fubini-a1` · issue #4242 · PR #4817 · candidate `db77a916adae`
- **Statement and proof**: **Fubini for `∫ θ ⟨Φ(s), ξ⟩ dμ` over `s ∈ [0, 1]`.**  Let `μ` be s-finite, `θ ∈ L¹(μ)`, `ξ` `μ`-a.e. strongly measurable **[corrected]** and `|ξ(x)(α)| ≤ ‖α‖` for `μ`-a.e. `x`, let `(s, x) ↦ Φ(s)(x)` be continuous with `‖Φ(s)(x)‖ ≤ B` on `[0, 1] × ℝ^P`, and `Ψ(x) = ∫₀¹ Φ(s)(x) ds`.  Then `∫₀¹ ∫ θ ξ(Φ(s)) dμ ds = ∫ θ ξ(Ψ) dμ`: the integrand is dominated by `B |θ(x)|` for `𝓛¹ ⌞ (0, 1] × μ`-a.e. `(s, x)`, so Fubini applies (`integral_integral_swap`), and the inner integral is `θ(x) ∫₀¹ ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x))` (`iwl_cr_ci_ie_nvector_intervalIntegral`).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the measurability of `ξ`, which the Lean statement (line 26706) assumes and Fubini's theorem needs.
- **Calls**: `iwl_cr_ci_ie_nvector_intervalIntegral`
- **Called by**: `iwl_cr_ci_integral_exchange`

#### `iwl_cr_ci_ie_nvector_intervalIntegral` (L26683)

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.nvector_integral-a1` · issue #4230 · PR #4760 · candidate `2136a7f0eda5`
- **Statement and proof**: **An `n`-vector commutes with the interval integral of a continuous covector family.**  If `f : ℝ → Λᵐ(ℝ^P)` is continuous and `c(v) = ∫_a^b f(s)(v) ds` for every `v`, then `∫_a^b w(f(s)) ds = w(c)` for every `w ∈ Λₘ(ℝ^P)`: evaluation at `v` is a continuous linear functional, so `(∫_a^b f)(v) = ∫_a^b f(s)(v) ds = c(v)` and `∫_a^b f = c`; then `w` commutes with the integral (`ContinuousLinearMap.intervalIntegral_comp_comm`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_cr_ci_ie_param_fubini`

#### `iwl_smooth_pushforward` (L57550)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1` · issue #950 · PR #4746 · candidate `cec1a3ca9165`
- **Statement and proof**: **Smooth push-forward of an integer multiplicity current** (Simon Ch. 6, 2.23–2.24, p. 139, and Lemma 3.9, p. 148).  Assume Lemma 3.9 (`LipschitzPushforwardIntegerMultiplicity`).  Let `X ∈ 𝒟_{k+1}(U)` be integer multiplicity and `f` be `C^∞` with `f(U) ⊆ V` and `f | spt X` proper. Then the integer multiplicity push-forward `S = f_# X` of 3.9 is the push-forward of 2.23 (remark after 3.10, p. 148): (1) `S(ω) = X(η)` whenever `η = f^# ω` on an open set containing `spt X`; (2) `∂S(ω) = ∂X(η)` likewise (2.24(1)); (3) if `‖Df‖ ≤ c`, then `M_W(S) ≤ c^{k+1} M_{f⁻¹(W) ∩ U}(X)` and `M_W(∂S) ≤ c^k M_{f⁻¹(W) ∩ U}(∂X)`.
- **Calls**: `iwl_sp_lipschitzPushforward_apply_eq`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_sp_massOn_le_of_compatible`
- **Called by**: `iwl_cycle_reduction`, `iwl_positive_density`, `iwl_integer_density`

#### `iwl_sp_lipschitzPushforward_apply_eq` (L54651)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.pushforward_formula-a1` · issue #2471 · PR #4547 · candidate `67ffac86a718`
- **Statement and proof**: **The Lipschitz push-forward by a differentiable map is the classical one** (Simon Ch. 6, remark after 3.10, p. 148: for `f` of class `C¹`, `f_# T` of 3.6 agrees with 2.23).  If `S = f_# X` in the sense of 3.6 with `X = τ(M, θ, ξ)`, and `η = Df^# (ω ∘ f)` on an open set `N ⊇ spt X`, then `S(ω) = X(η)`.  `Hⁿ`-a.e. point of `M` lies in `spt X ⊆ N` (`Submission.iwl_sp_rectifiable_support_null`) and has `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for a frame `τ` of `TₓM`.  There the derivative of `t ↦ f(x + tτᵢ)` at `0` is both `L(x)τᵢ` and `Df(x)τᵢ`, so `⟨ω(f(x)), L(x)_# ξ(x)⟩ = ⟨Df(x)^# ω(f(x)), ξ(x)⟩ = ⟨η(x), ξ(x)⟩`.
- **Calls**: `iwl_sp_rectifiable_support_null` (A.6)
- **Called by**: `iwl_smooth_pushforward`

#### `iwl_sp_boundary_apply_eq_of_compatible` (L57527)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.boundary_formula-a1` · issue #2521 · PR #3479 · candidate `06e3ced73016`
- **Statement and proof**: **Boundary commutes with smooth push-forward** (Simon Ch. 6, 2.24(1), p. 139 **[corrected]**: `∂ f_# T = f_# ∂T`).  Let `f` be `C^∞`.  If `S(ω′) = X(η′)` whenever `η′ = f^# ω′` on an open set containing `spt X` (degree `k + 1`), then `∂S(ω) = ∂X(η)` whenever `η = f^# ω` on an open set `N` containing `spt X` (degree `k`), where `(f^# ω)(x) = Df(x)^# ω(f(x))`.  On `N`, `dη = d(f^# ω) = f^# dω` by locality of `d` and its naturality under pull-back (`extDeriv_pullback`), so the hypothesis applies to `(dω, dη)`: `∂S(ω) = S(dω) = X(dη) = ∂X(η)`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), gives p. 141. Remark 2.24(1) is printed on p. 139, with 2.23, where `iwl_smooth_pushforward` cites it.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_smooth_pushforward`

#### `iwl_sp_massOn_le_of_compatible` (L57452)

- `root.integrality_weak_limits-a1.smooth_pushforward-a1.mass_bound-a1` · issue #2507 · PR #4596 · candidate `31e47f0afb18`
- **Statement and proof**: Mass bound for currents related by compatible pull-backs (step 6 of the smooth push-forward step in the proof of Simon Ch. 6, 8.2): let `U` be open, `A ⊆ U`, `f` of class `C^∞` with `f|A` proper (`f⁻¹(K) ∩ A` compact for compact `K ⊆ V`) and `c ≥ 0` **[corrected]**. If `Y(ω) = Z(η)` whenever `η = f^#ω` near `A`, and `‖Df‖ ≤ c`, then `M_W(Y) ≤ c^j M_{f⁻¹(W) ∩ U}(Z)`.  For `ω` admissible for `M_W(Y)`, the compatible form `η = ζ f^#ω` (`Submission.iwl_sp_exists_compatible_testForm`) has `Y(ω) = Z(η)`, `spt η ⊆ f⁻¹(W) ∩ U` and `|η| ≤ ‖Df‖^j |ω ∘ f| ≤ c^j` (`Submission.iwl_sp_covectorEuclideanNorm_pullback_le`), so `c^{-j} η` is admissible for `M_{f⁻¹(W) ∩ U}(Z)`; if `c^j = 0`, then `j ≥ 1`, `Df = 0` and `η = 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits these hypotheses of the Lean statement (line 57452). Properness is needed for the compatible forms `η` (`iwl_sp_exists_compatible_testForm`), and the claim fails without it: for `P = Q = j = c = 1`, `U = A = (0, 1)`, `V = ℝ`, `f = id`, `Z = 0` and `Y(ω) = ω(0)(e₁)`, every `ω` with a compatible `η ∈ 𝒟¹(U)` agrees with `η` on `(0, 1)`, and `η` vanishes on some `(0, ε)` because `spt η` is a compact subset of `(0, 1)`; so `ω(0) = 0` by continuity and the hypothesis holds, but `M(Y) = 1`.
- **Calls**: `iwl_sp_exists_compatible_testForm` (A.6), `iwl_sp_covectorEuclideanNorm_pullback_le` (A.6)
- **Called by**: `iwl_smooth_pushforward`

#### `iwl_positive_density` (L58345)

- `root.integrality_weak_limits-a1.positive_density-a1` · issue #954 · PR #4855 · candidate `3a6ac5216e97`
- **Statement and proof**: **Positive density** (Steps 6–9 of the proof of Simon Ch. 6, Theorem 8.2, pp. 176–178).  If `m + 2 ≤ P`, `T_j ∈ 𝒟_{m+1}(ℝ^P)` are integer multiplicity cycles with `sup_j M(T_j) < ∞`, `T_j ⇀ T`, and (BLI) holds, then the mass measure `μ = μ_T` has positive upper density `Θ*^{m+1}(μ, x)` at `μ`-a.e. `x`. * (1) `∂(T ⌞ B_r(x))` is integer multiplicity for a.e. `r > 0`: slices of the `T_j` by `|· - x|`, Fatou, `iwl_restriction_weak_limit` and (BLI). * (2)–(3) If `μ(B_δ(x)) < (κδ/(4·2^m(m+1)))^{m+1}`, some good `r ∈ (0, δ)` has `M(∂(T ⌞ B_r(x))) ≤ κ F(r)^m`, `F(r) = μ(B_r(x))^{1/(m+1)}`.  Otherwise the integrated slicing inequality (4.10) gives `F(b)^{m+1} - F(a)^{m+1} ≥ κ (b - a) F(a)^m`, hence uniform increments `F(a + s) ≥ F(a) + κ s/(2^m(m+1))`, and iterating them contradicts the smallness of `μ(B_δ(x))`. * (4) For such `r` there is `S_r` with `∂S_r = ∂(T ⌞ B_r(x))`, `spt S_r ⊆ B̄_{3r}(x)` and `M(S_r) ≤ μ(B_r(x))/2`: for `m = 0` the boundary is an integer multiplicity `0`-current of mass `< 1`, hence `0` (footnote 5); for `m ≥ 1` the isoperimetric filling is compressed into `B_{3r}(x)` by `iwl_smooth_pushforward` along `y ↦ x + r Φ₀((y - x)/r)`, `Φ₀ = id` near `B̄₂(0)`. * (5)–(6) Besicovitch disjoint closed balls cover `μ`-almost all of `{Θ* < ε₀}`; the cycles `S_i - T ⌞ B_i` satisfy the cone estimate `|Z(ω)| ≤ K L_ω R` (constant forms are exact), so `T(ω) ≤ μ(ℝ^P) - μ(⋃ B_i)/2 + O(δ)` for `|ω| ≤ 1`; lower semicontinuity of mass then forces `μ({Θ* < ε₀}) = 0`.
- **Calls**: `iwl_restriction_weak_limit`, `iwl_smooth_pushforward`, `iwl_restriction_theory` (A.6), `cmb_exists_compactly_contained_exhaustion` (A.1), `slicing_ru_smooth_to_continuous` (A.5), `slicing_ru_continuous_to_bounded` (A.5), `cmb_covector_eq_sum_coord_smul_wedge` (A.1), `cmb_abs_apply_le_of_massOn_le` (A.1), `isoperimetric_apply_eq_zero_of_disjoint_support` (A.6)
- **Called by**: `integrality_of_weak_limits`

#### `iwl_integer_density` (L68671)

- `root.integrality_weak_limits-a1.integer_density-a1` · issue #955 · PR #5271 · candidate `914dbf6c21ef`
- **Statement and proof**: **Rectifiable weak limits of integer multiplicity cycles `T_j ∈ 𝒟ₙ(ℝ^P)` with `sup_j M(T_j) < ∞` are integer multiplicity** **[corrected]** (Simon Ch. 6, proof of Theorem 8.2, printed (7)–(10), pp. 178–179, with the documented corrections). Write `T = τ(M, θ, ξ)`; it suffices that `θ(x) ∈ ℕ` for `Hⁿ`-a.e. `x ∈ M`.  After passing to a subsequence, at a.e. `x` we have `M_{B_r(x)}(T_j) ≤ C rⁿ` for small `r` and large `j`, the blow-ups `(η_{x,λ})_# T` converge to `θ(x) ∫_{TₓM} ⟨·, ξ(x)⟩ dHⁿ` as `λ ↓ 0`, and `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `TₓM = span τ`.  For `λ_k ↓ 0` the rescalings `Y_{k,j} = (η_{x,λ_k})_# T_j` are integer multiplicity cycles with `M_{B_2(0)}(Y_{k,j}) ≤ λ_k⁻ⁿ M_{B_{2λ_k}(x)}(T_j) ≤ 2ⁿ C` for large `j`, and `Y_{k,j} → (η_{x,λ_k})_# T` as `j → ∞`.  A diagonal sequence `Y_{k,φ'(k)}` converges in `B_2(0)` to `c [[span τ]]` with `c = ±θ(x)`, so the planar integrality theorem gives `c ∈ ℤ`, hence `θ(x) = |c| ∈ ℕ` as `θ(x) > 0`.  The hypothesis `m + 2 ≤ P` is not needed.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits the mass bound `sup_j M(T_j) < ∞` of the Lean statement (line 68671), which the proof uses at once (`ind_mass_density_bound`). Without it the claim fails: for `P = 2`, `n = 1`, the unit disc `D` and `E_j = {x ∈ D : ⌊j x₁⌋ even}`, the cycles `T_j = ∂[[E_j]]` are integer multiplicity and converge weakly to `½ ∂[[D]] = ½ [[∂D]]`, which is rectifiable with multiplicity `½`.
- **Calls**: `ind_mass_density_bound`, `ind_ae_integer_multiplicity`, `ind_ae_blowup_limit`, `ind_rescaled_current`, `ind_diagonal_weak_limit`, `ind_plane_multiplicity_integer`, `iwl_restriction_weak_limit`, `iwl_smooth_pushforward`, `iwl_top_dim_integrality`
- **Called by**: `integrality_of_weak_limits`

#### `ind_mass_density_bound` (L55623)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1` · issue #2476 · PR #4858 · candidate `8a48d5a6777e`
- **Statement and proof**: **Subsequential mass density bound** (the bound behind "(8) remains valid with `T_{j′}`" in the proof of Simon Ch. 6, 8.2, p. 178).  If `sup_j M(T_j) < ∞`, then along a subsequence `T_{φ(j)}`, for `Hⁿ`-a.e. `x` there are `C` and `r₀ > 0` with `M_{B_r(x)}(T_{φ(j)}) ≤ C rⁿ` for every `r ∈ (0, r₀)` and all large `j`.  The mass measures `μ_j` of the `T_j` have a diagonal subsequence whose closed-set limsups on every `B̄_R(0)` are bounded by finite measures `ν_R` (Simon Ch. 1, 4.16), and `ν_R(B̄_r(x)) < C rⁿ` for small `r` at `Hⁿ`-a.e. `x` (Ch. 1, 3.3).
- **Calls**: `ind_md_mass_measure_balls`, `ind_md_diagonal_weak_subseq`, `ind_md_ae_closedBall_growth`
- **Called by**: `iwl_integer_density`

#### `ind_md_mass_measure_balls` (L55292)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1` · issue #3258 · PR #4665 · candidate `c4ef827537f1`
- **Statement and proof**: **Mass measure of a current of finite mass on balls** (Step 1, (1a)–(1b), of the proof of the mass density bound in Simon Ch. 6, 8.2, for one current).  If `T ∈ 𝒟ₙ(ℝ^P)` has `M(T) < ∞`, then `M_W(T) ≤ M(T) < ∞` for every `W` (`massOn_mono`), so (R2) of the restriction theory (2.7)–(2.9) with `U = ℝ^P` gives a mass measure `μ` of `T`.  Every mass measure satisfies `μ(B_r(x)) = M_{B_r(x)}(T)` for all `x, r` and `μ(ℝ^P) ≤ M(T)`.
- **Calls**: `iwl_restriction_theory` (A.6), `ind_md_mmb_massMeasure_balls`
- **Called by**: `ind_mass_density_bound`

#### `ind_md_mmb_massMeasure_balls` (L55274)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.mass_measure_balls-a1.mass_measure_ball_values-a1` · issue #3857 · PR #4497 · candidate `08dc308eae08`
- **Statement and proof**: Simon Ch. 6, (2.8) (p. 136) for `U = ℝ^P`: a mass measure `μ` of `T` satisfies `μ(B_r(x)) = M_{B_r(x)}(T)` on every open ball, as `B_r(x) ⊂⊂ ℝ^P`; and `μ(ℝ^P) ≤ M(T)`, by continuity from below along `ℝ^P = ⋃_k B_k(0)` and `M_{B_k(0)}(T) ≤ M(T)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_md_mass_measure_balls`

#### `ind_md_diagonal_weak_subseq` (L55413)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.diagonal_weak_subseq-a1` · issue #3292 · PR #3876 · candidate `93e13175da02`
- **Statement and proof**: Diagonal extraction over the closed balls `B̄_R(0)`, `R ∈ ℕ` (steps (2b)–(2c) and 3 of the accepted natural-language proof of `ind_mass_density_bound`, within the proof of Simon Ch. 6, 8.2 **[corrected]**, carrying the closed-set `limsup` bound instead of weak convergence).  Apply `ind_md_closedBall_weak_subseq` to the nested subsequences `p₀ = id`, `p_{R+1} = p_R ∘ χ_{R, p_R}` and take the diagonal `φ(j) = p_{j+1}(j)`.  For `j ≥ R`, `φ(j) = p_{R+1}(i)` with `i ≥ j`, so the bound `limsup_i μ_{p_{R+1}(i)}(F) ≤ ν_R(F)` for closed `F ⊆ B̄_R(0)` passes to `φ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Simon Ch. 6, proof of 8.2, steps (2b)–(2c) and 3". The printed proof of 8.2 is labelled only by its displays (1)–(10); the steps are those of the accepted proof of the parent node `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`.
- **Calls**: `ind_md_closedBall_weak_subseq`
- **Called by**: `ind_mass_density_bound`

#### `ind_md_closedBall_weak_subseq` (L55308)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ball_weak_subseq-a1` · issue #3276 · PR #3766 · candidate `7c4d6e5f527b`
- **Statement and proof**: Simon Ch. 1, 4.16 on the ball `B̄_R(0)` combined with the closed-set half of the portmanteau theorem: measures `μ_j` on `ℝ^P` with `sup_j μ_j(ℝ^P) < ∞` have a subsequence `μ_{χ(i)}` and a finite measure `ν` with `limsup_i μ_{χ(i)}(F) ≤ ν(F)` for every closed `F ⊆ B̄_R(0)`. `ν` is the measure of the content `K ↦ lim_𝒰 μ_j(K)` on compact sets, `𝒰` an ultrafilter finer than `atTop`; the subsequence is extracted along a countable family of finite unions of closed balls, and outer regularity of `ν` reduces a closed `F` to such a union.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_md_diagonal_weak_subseq`

#### `ind_md_ae_closedBall_growth` (L55467)

- `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ae_ball_growth-a1` · issue #3304 · PR #3778 · candidate `1a0587a2278f`
- **Statement and proof**: Simon Ch. 1, Theorem 3.3 with `t = ∞`, followed by unpacking the finite upper density: if `ν(ℝ^P) < ∞`, then for `Hⁿ`-a.e. `x` there are `C` and `r₀ > 0` with `ν(B̄ᵣ(x)) < C rⁿ` for `0 < r < r₀`.  The infinite-density set `A = {Θ*ⁿ(ν, ·) = ∞}` is `μH[n]`-null: at each scale the five-times covering lemma selects disjoint balls `B̄ᵣ(x)`, `x ∈ A`, with `M ωₙ rⁿ ≤ ν(B̄ᵣ(x))` whose enlargements cover `A`, so `M ωₙ μH[n](A) ≤ 10ⁿ ν(ℝ^P)` for every `M ∈ ℕ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_mass_density_bound`

#### `ind_ae_integer_multiplicity` (L57386)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_integer-a1` · issue #2546 · PR #3551 · candidate `0213342518a9`
- **Statement and proof**: A rectifiable current whose multiplicity is `Hⁿ`-a.e. a natural number on `M` is integer multiplicity (Simon Ch. 6, proof of 8.2, conclusion).  The exceptional set `N = {x ∈ M : θ(x) ∉ ℕ}` is `Hⁿ`-null, so `M' = M ∖ N` carries the same current and, as `Hⁿ(η_{x,r} N) = r⁻ⁿ Hⁿ(N) = 0`, the same weighted approximate tangent spaces.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_integer_density`

#### `ind_ae_blowup_limit` (L56121)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1` · issue #2486 · PR #4309 · candidate `a3152bb94953`
- **Statement and proof**: Blow-up of `τ(M, θ, ξ)` at a.e. point (Simon Ch. 6, proof of 8.2, display (7)): for a rectifiable triple `(M, θ, ξ)` in `ℝ^P` **[corrected]** and `Hⁿ`-a.e. `x ∈ M`, every weighted approximate tangent space `Q` of `(M, θ)` at `x` and every continuous compactly supported `n`-form `ω`, `τ(M, θ, ξ)(r⁻ⁿ ω ∘ η_{x,r}) → θ(x) ∫_Q ⟨ω, ξ(x)⟩ dHⁿ` as `r ↓ 0`, `η_{x,r}(y) = r⁻¹(y − x)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), does not state that `(M, θ, ξ)` is a rectifiable triple, which the Lean statement (line 56123) assumes.
- **Calls**: `ind_ab_rescaled_tangent_limit`, `ind_ab_weighted_ball_growth`, `ind_ab_weighted_lebesgue_point`, `ind_ab_orientation_error_vanishes`
- **Called by**: `iwl_integer_density`

#### `ind_ab_rescaled_tangent_limit` (L55657)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.rescaled_tangent_limit-a1` · issue #3293 · PR #4005 · candidate `63de75d44548`
- **Statement and proof**: Simon Ch. 6, proof of 8.2 (the blow-up step): if `Q` is the weighted approximate tangent space of `(M, θ)` at `x` (Ch. 3, 1.7), then for every continuous compactly supported `f`, `(rⁿ)⁻¹ ∫_M θ(y) f(r⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f dHⁿ` as `r ↓ 0`.  The change of variables `z = η_{x,r}(y) = r⁻¹(y − x)` turns the left side into the blow-up integral `∫_{η_{x,r}(M)} f(z) θ(x + r z) dHⁿ(z)` of the tangent condition.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_ab_weighted_ball_growth`, `ind_ae_blowup_limit`

#### `ind_ab_weighted_ball_growth` (L55802)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_ball_growth-a1` · issue #3305 · PR #4126 · candidate `b235347887c4`
- **Statement and proof**: Weighted ball growth at a point with a weighted approximate tangent space `Q`: `∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`.  Test the rescaled tangent limit `(sⁿ)⁻¹ ∫_M θ(y) f₀(s⁻¹(y − x)) dHⁿ(y) → θ(x) ∫_Q f₀ dHⁿ` against the bump `f₀(z) = max(0, min(1, 2 − ‖z‖))`, which is `1` on `B̄_1(0)` and `0` off `B̄_2(0)`.
- **Calls**: `ind_ab_rescaled_tangent_limit`
- **Called by**: `ind_ae_blowup_limit`

#### `ind_ab_weighted_lebesgue_point` (L55893)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.weighted_lebesgue_point-a1` · issue #3313 · PR #3940 · candidate `d054ee15516d`
- **Statement and proof**: Weighted Lebesgue points of the orientation of a rectifiable triple (Simon Ch. 1, 3.23 with 3.11(3); Steps 1–3 of the accepted natural-language proof of `ind_ae_blowup_limit`, in the proof of Ch. 6, 8.2 **[corrected]**).  For `Hⁿ⌞M`-a.e. `x`, `(∫_{M ∩ B̄_s(x)} θ(y) ‖ξ(y) − ξ(x)‖ dHⁿ(y)) / (∫_{M ∩ B̄_s(x)} θ dHⁿ) → 0` as `s ↓ 0` (`ℝ≥0∞`-valued).  With `λ = (Hⁿ⌞M) ⌞ θ`, `λ(B̄_s(x))` is the denominator, `λ` is locally finite and mutually absolutely continuous with `Hⁿ⌞M` (`θ > 0` on `M`), and `ξ` is locally `λ`-integrable as `‖ξ‖ ≤ 1` a.e.; the claim is Lebesgue differentiation of `ξ` with respect to `λ` along the Besicovitch Vitali family of closed balls.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Steps 1–3 of the proof of Ch. 6, 8.2". The printed proof has no numbered steps; the steps are those of the accepted proof of the parent node `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_ae_blowup_limit`

#### `ind_ab_orientation_error_vanishes` (L55975)

- `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1` · issue #3322 · PR #3946 · candidate `0f20feb1d8e8`
- **Statement and proof**: The orientation error term of the blow-up (Simon Ch. 6, proof of 8.2): write `b(s) = ∫⁻_{M ∩ B̄_s(x)} θ dHⁿ` and `a(s) = ∫⁻_{M ∩ B̄_s(x)} θ ‖ξ - ξ(x)‖ₑ dHⁿ`.  If `b(s) ≤ C sⁿ` for small `s > 0` and `a(s) / b(s) → 0`, then for every continuous compactly supported `ω`, `∫_M θ(y) (ξ(y) - ξ(x))(r⁻ⁿ ω(r⁻¹(y - x))) dHⁿ(y) → 0` as `r → 0⁺`. With `tsupport ω ⊆ B̄_R(0)` and `‖ω‖ ≤ B`, the integral has extended norm at most `B Rⁿ · a(R r) / (R r)ⁿ`, and `a(s) / sⁿ ≤ C · a(s) / b(s) → 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_ae_blowup_limit`

#### `ind_rescaled_current` (L56388)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1` · issue #2495 · PR #4395 · candidate `36b130395d1b`
- **Statement and proof**: Rescaling about `x` by `r > 0`: `Y = η_# X` for the dilation `η(y) = r⁻¹(y − x)`, the push-forward along the proper affine map `η = b + L` with `L = r⁻¹ • id`, `b = −(r⁻¹ • x)` (`GeometricCurrentOn.affinePushforward`).  The pull-back of `ω` is `η^# ω = r⁻ⁿ ω ∘ η`, so `Y(ω) = X(η^# ω)`; `∂Y = η_#(∂X)`; `Y = τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` if `X = τ(M, θ, ξ)`; and `M_W(Y) ≤ r⁻ⁿ M_{η⁻¹(W)}(X)`.
- **Calls**: `ind_rs_rectifiableTriple_dilation`, `ind_rs_tauAction_dilation`, `ind_rs_massOn_dilation_le`
- **Called by**: `iwl_integer_density`

#### `ind_rs_rectifiableTriple_dilation` (L56266)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.triple_image-a1` · issue #3310 · PR #4205 · candidate `49800702c686`
- **Statement and proof**: Rectifiable triples are invariant under the dilations `η(y) = r⁻¹(y − x)`, `r > 0`: `(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` is again a rectifiable triple, where `η⁻¹(z) = x + r z`. `η` is a measurable embedding pushing `c Hⁿ`, `c = (rⁿ)⁻¹`, forward to `Hⁿ`, so `Hⁿ(η(S)) = c Hⁿ(S)` for every `S` and `Hⁿ ⌞ η(M) = η_#(c Hⁿ ⌞ M)`; the weighted approximate tangent spaces of `(η(M), θ ∘ η⁻¹)` at `η(y)` are those of `(M, θ)` at `y`.
- **Calls**: `ind_rs_dilation_measurePreserving`, `ind_rs_weightedTangent_dilation`
- **Called by**: `ind_rescaled_current`

#### `ind_rs_dilation_measurePreserving` (L55708)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.dilation_measure-a1` · issue #3286 · PR #3956 · candidate `45b4ab0d7c67`
- **Statement and proof**: `Hⁿ` scaling law for the dilation `η(y) = r⁻¹(y − x)`, `r > 0`: `η` is a measurable embedding and pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ`, i.e. `Hⁿ(η⁻¹(B)) = rⁿ Hⁿ(B)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_rs_rectifiableTriple_dilation`

#### `ind_rs_weightedTangent_dilation` (L56227)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.weighted_tangent-a1` · issue #3298 · PR #3767 · candidate `1633a21d7a93`
- **Statement and proof**: Weighted approximate tangent spaces (Simon Ch. 3, 1.7) are invariant under the dilation `η(w) = r⁻¹(w − x)`, `r > 0`: if `Q` is the approximate tangent space of `(M, θ)` at `y`, it is the approximate tangent space of `(η(M), θ ∘ η⁻¹)` at `η(y)`.  The blow-up of `η(M)` at `η(y)` with ratio `s` is the blow-up of `M` at `y` with ratio `r s`, and `s ↦ r s` preserves `𝓝[>] 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_rs_rectifiableTriple_dilation`

#### `ind_rs_tauAction_dilation` (L55749)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.tau_action-a1` · issue #3317 · PR #3939 · candidate `f01106583c89`
- **Statement and proof**: `τ(M, θ, ξ)` tested against `(rⁿ)⁻¹ ω ∘ η`, `η(y) = r⁻¹(y − x)`, `r > 0`, equals `τ(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` tested against `ω`: `η` pushes `(rⁿ)⁻¹ Hⁿ` forward to `Hⁿ` and `ξ(y)` is linear.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_rescaled_current`

#### `ind_rs_massOn_dilation_le` (L56347)

- `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.mass_bound-a1` · issue #3325 · PR #3959 · candidate `fe04133f0e47`
- **Statement and proof**: Mass bound for a current `Y` obtained from `X` by pull-back along the dilation `φ(y) = r⁻¹(y − x)`, `r > 0`: if every test form `ω` has a test form `η = (rⁿ)⁻¹ ω ∘ φ` and `Y ω = X η` for all such pairs, then `M_W(Y) ≤ (rⁿ)⁻¹ M_{φ⁻¹(W)}(X)` for every `W`, since `rⁿ η = ω ∘ φ` is admissible for `M_{φ⁻¹(W)}(X)` whenever `ω` is admissible for `M_W(Y)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_rescaled_current`

#### `ind_diagonal_weak_limit` (L56486)

- `root.integrality_weak_limits-a1.integer_density-a1.diagonal-a1` · issue #2508 · PR #3499 · candidate `b37cb947f505`
- **Statement and proof**: **Diagonal selection of a weakly convergent sequence with a mass bound** (the selection in the proof of Simon Ch. 6, Theorem 8.2, p. 178 **[corrected]**: "(8) remains valid with `T_{j'}` instead of `T`"). Let `closure W` be compact.  Suppose that for every test form `ω` supported in `W`, `X_{k,j}(ω) → Z_k(ω)` as `j → ∞` and `Z_k(ω) → L(ω)` as `k → ∞`, and that for each `k`, `M_W(X_{k,j}) ≤ C` for all large `j`.  Then some strictly increasing `φ` gives `M_W(X_{k,φ(k)}) ≤ C` for every `k` and `X_{k,φ(k)}(ω) → L(ω)` for every such `ω`.  With `C⁺ = max C 0`, the mass bound gives `|X(ω) - X(ω')| ≤ C⁺ sup |ω - ω'|`, and `Z_k`, `L` inherit this bound in the limit.  Choose `φ(k)` with `|X_{k,φ(k)}(ωᵢ) - Z_k(ωᵢ)| < 1/(k+1)` for `i ≤ k`, where `(ωᵢ)` is a countable sup-norm-dense family.  A four-term estimate then gives convergence for every `ω`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), gives p. 176. Display (8) and the quoted sentence are on p. 178, where `ind_mass_density_bound` cites them; p. 176 has the statement of 8.2 and the start of its proof.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `iwl_integer_density`

#### `ind_plane_multiplicity_integer` (L57351)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1` · issue #2520 · PR #5229 · candidate `885b2beaddfa`
- **Statement and proof**: **Integrality of a planar weak limit of integer multiplicity cycles** (Simon Ch. 6, Proof of 8.2, displays (8)–(10), and Remark 3.12).  Let `Q = span τ` be the `(m + 1)`-plane spanned by an orthonormal `τ`, and let `Y_k` be integer multiplicity cycles with `sup_k M_{B_2(0)}(Y_k) < ∞` and `Y_k ⇀ c[[Q]]` on forms supported in `B_2(0)`.  Then `c ∈ ℤ`.  Take the coordinates `p(y) = (⟪τ_i, y⟫)_i` and the distance `d` to `Q`.  Slicing by `d` localizes the `Y_k` to integer multiplicity currents `Z_k` with bounded mass and boundary mass on the cylinder `{|p| < 1, d < 3/4}` (`ind_pi_localized_cycles`).  Their push-forwards by `p` converge weakly to `c[[B_1(0)]]` in `ℝ^{m+1}` (`ind_pi_projected_limit`).  So `c[[B_1(0)]]` is integer multiplicity by the top-dimensional case of 8.2, and `c ∈ ℤ` (`ind_const_multiple_integer`).
- **Calls**: `ind_pi_localized_cycles`, `ind_pi_constant_vector_current`, `ind_pi_projected_limit`, `ind_const_multiple_integer`
- **Called by**: `iwl_integer_density`

#### `ind_pi_localized_cycles` (L56910)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.localized_cycles-a1` · issue #4044 · PR #5194 · candidate `205c2f1bc9ea`
- **Statement and proof**: Simon Ch. 6, proof of 8.2, displays (8)–(9): localization of the cycles `Y_k ⇀ c [[Q]]`, `Q = span τ`, to the thin cylinder `W' = {‖p‖ < 1, d < 3/4} ⊂⊂ B₂(0)`.  The current `X = c [[Q]] ∈ 𝒟ₙ(B₂(0))` has the representation `(Hⁿ ⌞ Q, c τ₁ ∧ ⋯ ∧ τₙ)`, and `X_k = Y_k|_{B₂(0)}` are integer multiplicity cycles with `X_k ⇀ X`.  A good level `γ ∈ (1/4, 1/2)` of `d` gives restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` with bounded `M_{W'}(R_k) + M_{W'}(∂R_k)` and `R_k → X ⌞ {d < γ} = X` on forms supported in `W'` (the measure of `X` lives on `Q ⊆ {d = 0}`).  Then `Z_k = R_k|_{W'}` are integer multiplicity, supported in `{d ≤ γ}`, and converge to `c [[Q]]` in `W'`.
- **Calls**: `ind_pi_frame_geometry`, `ind_pi_span_integral`, `ind_pi_constant_vector_current`, `br_restrictDomain_isIntegerMultiplicity`, `ind_pi_good_slice_selection`, `ind_pi_restriction_open_im`, `fiw_tb_ext_support_subset`
- **Called by**: `ind_plane_multiplicity_integer`

#### `ind_pi_frame_geometry` (L54757)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.frame_geometry-a1` · issue #4002 · PR #4699 · candidate `0015dc978bea`
- **Statement and proof**: Geometry of an orthonormal frame `τ` in `ℝ^P`: with `π y = ∑ ⟪τᵢ, y⟫ τᵢ`, `p y = (⟪τᵢ, y⟫)ᵢ` and `d y = ‖y − π y‖`, Pythagoras gives `‖y‖² = ‖p y‖² + d(y)²`; hence `‖p‖ ≤ 1`, `d` is `1`-Lipschitz, `p` inverts `a ↦ ∑ aᵢ τᵢ`, `d = 0` on `span τ`, the cylinder `{‖p‖ < 1, d < 3/4}` lies in `closedBall 0 (5/4) ⊆ B₂(0)`, and `p⁻¹(K) ∩ {d ≤ γ}` is a compact subset of it for compact `K ⊆ B₁(0)` and `γ < 3/4`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_localized_cycles`, `ind_pi_projected_limit`

#### `ind_pi_span_integral` (L54862)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.span_integral-a1` · issue #4009 · PR #4677 · candidate `c763e84863a7`
- **Statement and proof**: Simon Ch. 6, proof of 8.2: for an orthonormal frame `τ₁, …, τₙ` of `Q = span τ ⊆ ℝ^P`, the parametrization `ι(a) = ∑ᵢ aᵢ τᵢ` is a linear isometry `ℝⁿ → ℝ^P` with range `Q`, so it pushes Lebesgue measure on `ℝⁿ` (`= Hⁿ`) forward to `Hⁿ ⌞ Q`.  As a closed, hence measurable, embedding it gives `∫_Q h dHⁿ = ∫_{ℝⁿ} h(ι(a)) da` for every `h`, and `(Hⁿ ⌞ Q)(K) = Lⁿ(ι⁻¹ K) < ∞` for compact `K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_localized_cycles`, `ind_pi_projected_limit`

#### `ind_pi_constant_vector_current` (L54902)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.const_vector_current-a1` · issue #4018 · PR #4693 · candidate `daec5514531c`
- **Statement and proof**: Simon Ch. 6, (2.7) (p. 136) for a constant `n`-vector: if `μ` is finite on compact sets and `w ∈ Λₙ(ℝ^P)`, then `T(ω) = ∫ ⟨ω(x), w⟩ dμ(x)` defines a current `T ∈ 𝒟ₙ(U)` with representation `(μ, w)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_localized_cycles`, `ind_plane_multiplicity_integer`

#### `br_restrictDomain_isIntegerMultiplicity` (L2230)

- `root.boundary_rectifiability-a1.restrict_domain_im-a1` · issue #852 · PR #2238 · candidate `03443db0c607`
- **Statement and proof**: Simon Ch. 6, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of an integer multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟ₖ(U)` to an open `W ⊆ U` is the integer multiplicity current `τ(M ∩ W, θ, ξ)`.
- **Calls**: `br_weightedTangent_congr` (A.3)
- **Called by**: `fiw_tb_restrictDomain_mass_im`, `ind_pi_localized_cycles`, `boundary_rectifiability`

#### `ind_pi_good_slice_selection` (L56851)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1` · issue #4034 · PR #6446 · candidate `afa97e5c91a5`
- **Statement and proof**: Simon Ch. 6, proof of 8.2, display (8) for a subsequence (which the book justifies "by 4.5(1) and a selection arguments [sic] in 6.7(2) of Ch. 2") **[corrected]**: for `W ⊂⊂ U`, `d` Lipschitz, `a < b` and cycles `X_k ⇀ X` with `M_V(X_k) < ∞` for `V ⊂⊂ U` and `sup_k M_W(X_k) < ∞` **[corrected]** there are a level `γ ∈ (a, b)` and a subsequence `κ` such that the restrictions `R_k = X_{κ(k)} ⌞ {d < γ}` satisfy `M_W(R_k) ≤ M_W(X_{κ(k)})`, `sup_k M_W(∂R_k) < ∞` and `R_k(ω) → (X ⌞ {d < γ})(ω)` for `spt ω ⊆ W`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes the book as "by 4.5(1) and a selection argument as in 6.7(2) of Ch. 2"; p. 178 prints "justified by 4.5(1) and a selection arguments in 6.7(2) of Ch. 2", as the justification that (8) remains valid for a subsequence `T_{j′}`. It also omits the hypotheses `W ⊂⊂ U`, `d` Lipschitz, `a < b` and the local finiteness of the masses of the `X_k` of the Lean statement (lines 56866–56868).
- **Calls**: `ind_pi_ss_cycle_slice_family`, `ind_pi_ss_fatou_level_selection`, `ind_pi_ss_restriction_massOn_le`
- **Called by**: `ind_pi_localized_cycles`

#### `ind_pi_ss_cycle_slice_family` (L56757)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_family-a1` · issue #4633 · PR #5162 · candidate `e768182b2864`
- **Statement and proof**: **Slices of a cycle (Simon Ch. 6, 4.5(1)–(2), 4.6, 4.10).**  For `X ∈ 𝒟_{m+1}(U)` with `∂X = 0` and locally finite mass, `d` `L`-Lipschitz and `a < b`, there are restrictions `A_t = X ⌞ {d < t}` and a measurable `g` with `M_W(∂A_t) ≤ g(t)` on `(a, b)` and `∫⁻_{(a,b)} g ≤ L · M_W(X)`.  As `M_V(∂X) = M_V(0) = 0`, `SlicingTheorem` gives slices `S_t = ⟨X, d, t⟩`, and `∂A_t = S_t` by `ind_pi_ss_cycle_slice_boundary`.  The band `{a < d < b} = {|d - (a + b)/2| < (b - a)/2}` is a sublevel set of an `L`-Lipschitz function, so the same lemma gives the restriction `R = X ⌞ {a < d < b}` used by the mass clause of 4.10 (`‖Dd‖ ≤ L`); finally `M_W(R) ≤ M_W(X)` by `ind_pi_ss_restriction_massOn_le`.
- **Calls**: `ind_pi_ss_cycle_slice_boundary`, `ind_pi_ss_restriction_massOn_le`
- **Called by**: `ind_pi_good_slice_selection`

#### `ind_pi_ss_cycle_slice_boundary` (L55138)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.cycle_slice_boundary-a1` · issue #4628 · PR #5137 · candidate `014fdc802b43`
- **Statement and proof** (no doc comment in the source; summary of the Lean proof **[corrected]**): **A slice of a cycle is the boundary of the restriction.** If `∂T = 0` and `IsSlice T f t S`, then some restriction `A` of `T` to `{x ∈ U : f(x) < t}` has `∂A = S`. Proof: unfolding (4.6), `S = ∂A − B` with `B(ω) = ∫_{A_t} ⟨ω, v⟩ dμ` for a representation `(μ, v)` of `∂T`; testing `∂T = 0` with `g ω`, `g ∈ C_c^∞(U)`, and the fundamental lemma of the calculus of variations (Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) give `⟨ω, v⟩ = 0` `μ`-a.e. on `U ⊇ A_t`, so `B = 0` and `∂A = S`.
- **Correction**: the previous revision of this file labelled this summary as a summary of the accepted natural-language proof. It summarizes the Lean proof, which shows `B = 0` with the fundamental lemma of the calculus of variations; the accepted natural-language proof (steps 2–3) obtains `B = 0` from the uniqueness (R1) of restrictions in `iwl_restriction_theory`, since `0` is also a restriction of `∂T = 0` to `A_t`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_ss_cycle_slice_family`

#### `ind_pi_ss_restriction_massOn_le` (L55172)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.restriction_mass_le-a1` · issue #4616 · PR #5085 · candidate `6bffed6a5c5b`
- **Statement and proof**: Simon Ch. 6, (2.8)–(2.9): for `W ⊂⊂ U` and `S = X ⌞ A`, `M_W(S) ≤ M_W(X)`.  For an admissible `ω`, `S(ω) = ∫_A ⟨ω, v⟩ dμ`.  By regularity of the finite measure `|⟨ω, v⟩| μ` there are a closed `F ⊆ A` and an open `G ⊇ A` with `∫_{G \ F} |⟨ω, v⟩| dμ < ε`; a smooth `ψ : ℝ^P → [0, 1]` equal to `1` on `F` with support `G` makes `ψ ω` admissible and `S(ω) ≤ X(ψ ω) + ε ≤ M_W(X) + ε`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_ss_cycle_slice_family`, `ind_pi_good_slice_selection`

#### `ind_pi_ss_fatou_level_selection` (L56818)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.fatou_level_selection-a1` · issue #4641 · PR #5027 · candidate `fbecac1595ff`
- **Statement and proof**: Fatou selection of a good level (the selection argument that the proof of Simon Ch. 6, 8.2 (p. 178) cites from 6.7(2) of Ch. 2 **[corrected]**): if `a < b`, the `g_k` are measurable **[corrected]** and `∫⁻_{(a,b)} g_k ≤ C < ∞` for all `k` and `E` is countable, there are `γ ∈ (a, b) \ E`, a subsequence `σ` and `G < ∞` with `g_{σ(k)}(γ) ≤ G` for all `k`.  By Fatou, `∫⁻_{(a,b)} liminf_k g_k ≤ C`, so `liminf_k g_k(γ) < ∞` for some `γ ∈ (a, b) \ E` (`E` is Lebesgue-null); with `G = liminf_k g_k(γ) + 1`, `g_k(γ) < G` for infinitely many `k`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes "selection argument as in 6.7(2) of Ch. 2"; p. 178 prints "a selection arguments in 6.7(2) of Ch. 2". It also omits the hypotheses `a < b` and the measurability of the `g_k` (used for Fatou) of the Lean statement (line 56819).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_good_slice_selection`

#### `ind_pi_restriction_open_im` (L54958)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.restriction_open_im-a1` · issue #4026 · PR #4754 · candidate `da35ec9455ab`
- **Statement and proof**: **Restriction of an integer multiplicity current to an open set** (Simon Ch. 6, (2.9) and 3.1, pp. 136, 146; used for the restrictions to open sets in the proof of 8.2, pp. 176–179).  If `X = τ(M, θ, ξ)` is integer multiplicity and `R = X ⌞ A` with `A` open, then `R = τ(M ∩ A, θ, ξ)` is integer multiplicity.  With smooth cutoffs `φ_j → 1_A` pointwise, `X(φ_j ω)` tends both to `∫_A ⟨ω, v⟩ dμ = R(ω)` and to `τ(M ∩ A, θ, ξ)(ω)` (dominated convergence); and the weighted tangent planes of `(M, θ)` at `x ∈ A` are those of `(M ∩ A, θ)`, since the blow-ups of `M` and `M ∩ A` agree near the origin.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_localized_cycles`

#### `ind_pi_projected_limit` (L57021)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1` · issue #4053 · PR #5053 · candidate `363a55563e32`
- **Statement and proof**: Simon Ch. 6, proof of 8.2 (display (10) and `p_# S̃_j ⇀ θ [[ℝⁿ]]`): push the localized currents `Z_k ⇀ c [[Q]]` (`Q = span τ`) in the cylinder `W′ = {‖p‖ < 1, d < 3/4}` forward by the frame coordinates `p`.  The push-forwards `S′_k = p_# Z_k` are integer multiplicity currents in `B₁(0) ⊆ ℝⁿ` with `M_W(S′_k) ≤ M(Z_k)` and `M_W(∂S′_k) ≤ M(∂Z_k)`, and `S′_k(ω) = Z_k(η)` for a cut-off pull-back `η = ζ p^#ω ∈ 𝒟ⁿ(W′)` independent of `k`.  On `Q`, `η(τ) = ω(p ·)(e)`, so `S′_k(ω) → c ∫_Q ω(p z)(e) dHⁿ(z) = c ∫_{B₁(0)} ω(e) dx = S(ω)`.
- **Calls**: `ind_pi_frame_geometry`, `ind_pi_pl_linear_pushforward_family`, `iwl_sp_exists_compatible_testForm` (A.6), `ind_pi_span_integral`
- **Called by**: `ind_plane_multiplicity_integer`

#### `ind_pi_pl_linear_pushforward_family` (L54686)

- `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.projected_limit-a1.linear_pushforward_family-a1` · issue #4617 · PR #4964 · candidate `71c08df2ed2c`
- **Statement and proof**: Simon Ch. 6, proof of 8.2 (p. 179), `p_# S̃_j` and display (10): if `p` is linear with `‖p‖ ≤ 1` and proper on `F`, integer multiplicity `X_k ∈ 𝒟_{m+1}(U)` with `spt X_k ⊆ F` push forward (by the smooth push-forward, `f := p`) to integer multiplicity `S_k ∈ 𝒟_{m+1}(V)` with `S_k(ω) = X_k(p^#ω)`, `M_W(S_k) ≤ M(X_k)` and `M_W(∂S_k) ≤ M(∂X_k)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_pi_projected_limit`

#### `ind_const_multiple_integer` (L57320)

- `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1` · issue #2534 · PR #4449 · candidate `3cf5b3cf1bbd`
- **Statement and proof**: A constant multiple `c [[U]]` of a nonempty open `U ⊆ ℝⁿ` is integer multiplicity only if `c ∈ ℤ` (Simon Ch. 6, the end of the proof of 8.2, p. 179, where the `L¹`-limit of the integer-valued densities of the projected currents is shown to be the constant `θ(x)`, so that `θ(x) ∈ ℤ` **[corrected]**).  An integer multiplicity `X ∈ 𝒟ₙ(U)` acts as `X(ω) = ∫_U u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` with `u` a.e. integer-valued and integrable on compact subsets of `U`; the constant `c` is a second such density of `X`, so `c = u` a.e. on `U`, and `Lⁿ(U) > 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes p. 179 as "`θ ≡ θ(x)` in `B₁ⁿ(0)`; thus `θ(x) ∈ ℤ`". In the book the function that is identically `θ(x)` is the `L¹`-limit of the densities of the projected currents, not the multiplicity `θ` of `T`; the reference is paraphrased instead.
- **Calls**: `ind_top_dim_integer_density`, `ind_top_form_density_ae_unique`
- **Called by**: `ind_plane_multiplicity_integer`

#### `ind_top_dim_integer_density` (L57219)

- `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_integer_density-a1` · issue #3525 · PR #4291 · candidate `5d7d2e528f96`
- **Statement and proof**: A top-dimensional integer multiplicity current has an integer density (Simon Ch. 6, 2.35 (‡) **[corrected]**, `T(ω) = ∫ aθ dLⁿ` for `ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, with `θ` integer-valued as at the end of the Proof of 8.2, p. 179).  Write `X = τ(M, θ, ξ)` in `U ⊆ ℝⁿ`, `n = m + 1`, and `e = (e₁, …, eₙ)`; on `ℝⁿ`, `Hⁿ = μHE[n]` is Lebesgue measure.  By `Submission.ind_top_orthonormal_frame_sign`, `ξ = ±e₁ ∧ ⋯ ∧ eₙ` a.e. on `M`, so `ξ(x)(α) = σ(x) α(e)` with the sign `σ(x) = ξ(x)(dx¹ ∧ ⋯ ∧ dxⁿ) = ±1`.  The density is `u = θσ` on `M` and `u = 0` off `M`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), labels the display of 2.35 (p. 143) `(∗)`. The book marks this display with the same symbol as the display of 3.1, which the contract (`tauAction`) and §1.3 write as (‡): in the PDF of the book both markers are the same glyph of the same font. The formula quoted next to the label identifies the display in any case.
- **Calls**: `ind_top_orthonormal_frame_sign`
- **Called by**: `ind_const_multiple_integer`

#### `ind_top_orthonormal_frame_sign` (L57096)

- `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.frame_sign_top-a1` · issue #3511 · PR #4108 · candidate `520cbc1489b5`
- **Statement and proof**: An orthonormal `n`-frame in `ℝⁿ` has simple `n`-vector `±e₁ ∧ ⋯ ∧ eₙ` (Simon Ch. 6, 3.1 in top dimension: an orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` is `±e₁ ∧ ⋯ ∧ eₙ`, so `⟨ω, ξ⟩ = ±a` for `ω = a dx¹ ∧ ⋯ ∧ dxⁿ`, as in the proof of 8.2, p. 179).  `τ` is linearly independent with `n = dim ℝⁿ` members, hence an orthonormal basis of `ℝⁿ`, as is the standard basis `e`.  An `n`-covector `α` is an alternating `n`-form on `ℝⁿ`, so `α(τ) = α(e) det_e(τ)` (`AlternatingMap.eq_smul_basis_det`), and `det_e(τ) = ±1` because the change of basis between orthonormal bases is orthogonal (`OrthonormalBasis.det_to_matrix_orthonormalBasis_real`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_top_dim_integer_density`

#### `ind_top_form_density_ae_unique` (L57137)

- `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_density_unique-a1` · issue #3518 · PR #4159 · candidate `38e98aa2eb31`
- **Statement and proof**: Densities of top-degree test-form functionals on an open set are unique a.e. (Simon Ch. 6, the end of the proof of 8.2, p. 179, where the `L¹`-limit of the integer-valued densities of the projected currents is shown to be the constant `θ(x)`, so that `θ(x) ∈ ℤ` **[corrected]**; top-dimensional currents acting by `ω = a dx¹ ∧ ⋯ ∧ dxⁿ ↦ ∫ a θ dLⁿ` as in 2.35 (‡) **[corrected]**).  For `a ∈ C_c^∞(U)`, the form `ω = a • vol` with `vol = dx¹ ∧ ⋯ ∧ dxⁿ` is a test form on `U` with `ω(x)(e₁, …, eₙ) = a(x)` (`wedgeCovectors_apply_det`: `vol(e) = det 1 = 1`), so the hypothesis gives `∫ a (u - v) = ∫_U u a - ∫_U v a = 0`.  As `u - v` is locally integrable on the open set `U`, the fundamental lemma of the calculus of variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `u = v` a.e. on `U`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), writes "2.35 (∗)". The display of 2.35 (p. 143) carries the marker (‡), the same symbol as the display of 3.1 (see the correction in the entry `ind_top_dim_integer_density`). It also quotes p. 179 as "`θ ≡ θ(x)` in `B₁ⁿ(0)`"; the function there is the `L¹`-limit of the densities of the projected currents, so the reference is paraphrased (see `ind_const_multiple_integer`).
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `ind_const_multiple_integer`

#### `iwl_zero_dim_integrality` (L37113)

- `root.integrality_weak_limits-a1.zero_dim-a1` · issue #931 · PR #3241 · candidate `86ccbcdc8dea`
- **Statement and proof**: Simon Ch. 6, 8.2 in the case `n = 0` (p. 176, "the theorem is trivial in case `n = 0`"): a weak limit `X` of integer multiplicity `X_j ∈ 𝒟₀(U)` with `sup_j M_W(X_j) < ∞` for all `W ⊂⊂ U` is integer multiplicity.  Each `X_j = τ(M_j, θ_j, ξ_j)` is a locally finite sum `X_j(ω) = ∑_{x ∈ M_j} c_j(x) ω(x)` with `c_j = ±θ_j ∈ ℤ ∖ {0}`, and testing with signed bumps gives `∑_{x ∈ S} |c_j(x)| ≤ M_W(X_j)` for finite `S ⊆ M_j ∩ W`.  On `W = B_{ε/2}(x₀) ⊂⊂ U`, `br_zd_dirac_local_limit` makes `X` a finite integer Dirac sum on forms supported in `W`, which is integer multiplicity by `br_zd_finite_dirac_im`, and `iwl_im_patching` globalizes.
- **Calls**: `iwl_im_patching`, `br_zd_dirac_local_limit`, `br_zd_finite_dirac_im`
- **Called by**: `integrality_of_weak_limits`

#### `br_zd_dirac_local_limit` (L1190)

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_local_limit-a1` · issue #1097 · PR #1535 · candidate `e8520f03dafa`
- **Statement and proof**: The case `n = 0` of Simon Ch. 6, 8.2 (p. 176, "trivial in case `n = 0`"), on a set `W` with `closure W` compact (used for 6.3): let `X_j ⇀ X` and, on test forms supported in `W`, let `X_j(ω) = ∑ᶠ_{x ∈ N_j} c_j(x) ω(x)` with integers `c_j ≠ 0` on `N_j`, `N_j ∩ W` finite and `∑_{x ∈ N_j ∩ W} |c_j(x)| ≤ Λ`.  Then on such forms `X(ω) = ∑_{x ∈ D} a(x) ω(x)` for a finite `D ⊆ W` and integers `a`.  Each `N_j ∩ W` has at most `Q = ⌊Λ⌋₊` points, with `|c_j| ≤ ⌊Λ⌋`; padding with `0`-weighted copies of `0` gives configurations of length `Q` in a compact set, a subsequence converges, limit points outside `W` contribute `0` and equal ones are grouped.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_zero_dim_weak_limit_isIntegerMultiplicity`, `iwl_zero_dim_integrality`

#### `br_zd_finite_dirac_im` (L1302)

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.finite_dirac_im-a1` · issue #1095 · PR #1515 · candidate `360df6808c71`
- **Statement and proof**: Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): a finite integer combination of point masses `Y(ω) = ∑_{x ∈ D} a(x) ω(x)`, `D ⊆ U`, is the integer multiplicity current `τ(M, θ, ξ)` with `M = {x ∈ D : a(x) ≠ 0}`, `θ = |a|` and `ξ = ±1` the sign of `a`.  `Y` is continuous since convergence of test forms gives pointwise convergence.  `M` is finite, so it is `H⁰`-measurable and countably `0`-rectifiable and `H⁰`-integrals over it are finite sums; at `x ∈ M`, for small `r` the blow-up `η_{x,r}(M)` meets the support of a given `f ∈ C_c` only in `0`, so the weighted tangent space is `{0}`, spanned by the empty frame.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_zero_dim_weak_limit_isIntegerMultiplicity`, `iwl_zero_dim_integrality`

### A.10 Boundary rectifiability 6.3 (§3.10): `boundary_rectifiability` and its 19 further declarations

#### `boundary_rectifiability` (L68901)

- `root.boundary_rectifiability-a1` · issue #334 · PR #8641 · candidate `8f66d3bbc008`
- **Statement and proof**: **Simon Ch. 6, 6.3 (Boundary Rectifiability Theorem, p. 170).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U`, then `∂T` is integer multiplicity (`n = m + 1`).  Integer multiplicity is local, so fix `x₀ ∈ U`.  By slicing there are `r > 0` and an integer multiplicity `X ∈ 𝒟ₙ(ℝ^P)` with `M(X) + M(∂X) < ∞` that agrees with `T` on forms supported in `B_r(x₀)`.  Polyhedral approximation (deformation theorem) and compactness for cycles (8.2) make `∂X` integer multiplicity, hence also its restriction to `U`.  For `ω` supported in `B_r(x₀)`, `spt dω ⊆ spt ω`, so `∂T(ω) = T(dω) = X(dω) = ∂X(ω)`.
- **Calls**: `br_isIntegerMultiplicity_of_local`, `br_local_finite_mass_extension`, `slicing_theorem` (A.5), `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_theorem` (A.6), `integrality_of_weak_limits` (A.9), `br_restrictDomain_isIntegerMultiplicity` (A.9)
- **Called by**: `flat_convergence_iff_weak_convergence`, `federer_fleming_compactness`, `main_theorem`

#### `br_isIntegerMultiplicity_of_local` (L2270)

- `root.boundary_rectifiability-a1.local_to_global_im-a1` · issue #857 · PR #2309 · candidate `4fb91bc57693`
- **Statement and proof**: Integer multiplicity is local (the patching step in the proof of Simon Ch. 6, 6.3): if every `x ∈ U` has an open `V ∋ x` on which `X` agrees with an integer multiplicity current, then `X` is integer multiplicity.  By Lindelöf countably many such `V_i`, with `Y_i = τ(M_i, θ_i, ξ_i)`, cover `U`.  Two of these triples agree up to null sets on `V_i ∩ V_j`, where both represent `X`, so they glue to one integer multiplicity triple `(M₀, θ₀, ξ₀)` that agrees with each on its `V_i`; then `X = τ(M₀, θ₀, ξ₀)` on forms supported in some `V_i`, hence on all forms.
- **Calls**: `ltg_tau_local_to_global`, `ltg_tau_unique_on_open` (A.6), `ltg_glue_triples`, `br_weightedTangent_congr` (A.3), `ltg_tau_congr_on_open`
- **Called by**: `br_zero_dim_weak_limit_isIntegerMultiplicity`, `boundary_rectifiability`

#### `ltg_tau_local_to_global` (L1893)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_local_to_global-a1` · issue #1377 · PR #2196 · candidate `0ab0bebaeb02`
- **Statement and proof**: **Local-to-global for `τ(M, θ, ξ)` via a smooth partition of unity** (Simon Ch. 6, 3.1 (‡); used in the local-to-global step of the proof of 6.3).  If every `x ∈ U` has an open `V_x ∋ x` such that `X ∈ 𝒟ₖ(U)` agrees with `τ(M, θ, ξ)` on the test forms supported in `V_x`, then `X = τ(M, θ, ξ)` on `𝒟ᵏ(U)`. Cover the compact `K = spt ω ⊆ U` by finitely many `V_y` (`y ∈ K`), take a smooth partition of unity `χ_y` on `K` subordinate to them and split `ω = ∑_y χ_y ω`: each `χ_y ω ∈ 𝒟ᵏ(U)` has support in `V_y`, so `X(χ_y ω) = τ(χ_y ω)`; conclude by linearity of `X` and of the integral, each `θ ⟨χ_y ω, ξ⟩` being `Hᵏ`-integrable on `M` by `Submission.ltg_tau_integrable`.
- **Calls**: `ltg_tau_integrable` (A.5)
- **Called by**: `br_isIntegerMultiplicity_of_local`

#### `ltg_glue_triples` (L1693)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.glue_triples-a1` · issue #1372 · PR #2221 · candidate `c1a7e6bba84a`
- **Statement and proof**: Gluing compatible integer multiplicity triples along a countable open cover (Simon Ch. 6, 6.3): if `U ⊆ ⋃ᵢ Vᵢ` with `Vᵢ` open, `(Mᵢ, θᵢ, ξᵢ)` are triples in `U` with `θᵢ ∈ ℕ` on `Mᵢ`, and any two agree `Hᵏ`-a.e. on `Vᵢ ∩ Vⱼ`, then one triple `(M₀, θ₀, ξ₀)` with `θ₀ ∈ ℕ` on `M₀` agrees with each `(Mᵢ, θᵢ, ξᵢ)` `Hᵏ`-a.e. on `Vᵢ`.  The hypothesis (TL) is locality of weighted approximate tangent spaces.  `M₀ = ⋃ᵢ Mᵢ ∩ Dᵢ` with `Dᵢ = Vᵢ \ ⋃_{j<i} Vⱼ`, and on `Dᵢ` the triple is `(Mᵢ, θᵢ, ξᵢ)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_isIntegerMultiplicity_of_local`

#### `ltg_tau_congr_on_open` (L1844)

- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_congr_on_open-a1` · issue #1373 · PR #1522 · candidate `bf2b276506a5`
- **Statement and proof**: Locality of `τ(M, θ, ξ)` (Simon Ch. 6, 3.1 (‡)), the locality step in the proof of 6.3: on forms `ω` with `tsupport ω ⊆ V`, `V` open, `τ(M, θ, ξ)(ω)` only depends on `M ∩ V` up to `Hᵏ`-null sets and on `θ, ξ` up to `Hᵏ ⌞ (M ∩ V)`-null sets.  Both integrands vanish off `V`, so `∫_M = ∫_{M ∩ V}` and `∫_{M'} = ∫_{M' ∩ V}`; these agree since `M ∩ V`, `M' ∩ V` are `Hᵏ`-a.e. equal and the integrands agree a.e. on `M ∩ V`.  No integrability is needed.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_isIntegerMultiplicity_of_local`, `br_local_finite_mass_extension`

#### `br_local_finite_mass_extension` (L31744)

- `root.boundary_rectifiability-a1.localization-a1` · issue #880 · PR #3730 · candidate `d559c74c7b3f`
- **Statement and proof**: **Localization of `T` with finite boundary mass (Simon Ch. 6, proof of 6.3, via slicing 4.5–4.10 and the cut-off argument of 6.2).**  Assume the slicing theorem.  Let `T = τ(M, θ, ξ) ∈ 𝒟ₙ(U)` (`n = m + 1`) be integer multiplicity with `M_W(∂T) < ∞` for all `W ⊂⊂ U`, and `x₀ ∈ U`.  Then for some `r > 0` with `B_r(x₀) ⊆ U`, `X = τ(M ∩ B_r(x₀), θ, ξ)` is an integer multiplicity current in `ℝ^P` with `M(X) < ∞`, `M(∂X) < ∞` and `X = T` on forms supported in `B_r(x₀)`.  `T` has the representation `(Hⁿ ⌞ M, θ ξ)`, hence locally finite mass. With `f = |· - x₀|`, `W = B_{2r₀}(x₀) ⊂⊂ U` and `R = T ⌞ {r₀/2 < f < r₀}`, (4.10) gives `∫_{r₀/2}^{r₀} M_W(⟨T, f, t₋⟩) dt ≤ M_W(R) < ∞`; fix `r` with `M_W(⟨T, f, r₋⟩) < ∞`.  By uniqueness of restrictions `T ⌞ B_r = X` on `𝒟ⁿ(U)`, so `∂X = ⟨T, f, r₋⟩ + (∂T) ⌞ B_r` on forms in `W`, and the cut-off lemma gives `M(∂X) ≤ M_W(⟨T, f, r₋⟩) + M_W(∂T) < ∞`.
- **Calls**: `ltg_tau_integrable` (A.5), `iwl_restriction_theory` (A.6), `br_loc_triple_inter_open`, `br_loc_tauAction_current` (A.6), `fiw_im_mass_formula`, `ltg_tau_congr_on_open`, `polyhedral_approx_boundary_mass_cutoff` (A.8)
- **Called by**: `boundary_rectifiability`

#### `br_loc_triple_inter_open` (L11010)

- `root.boundary_rectifiability-a1.localization-a1.triple_inter_open-a1` · issue #2484 · PR #3461 · candidate `980bf2f0ffdd`
- **Statement and proof**: Restriction of a triple `(M, θ, ξ)` (Simon Ch. 6, 3.1) to an open set `V`, the localization step in the proof of Ch. 6, 6.3: if `M ∩ V ⊆ U'` and `θ` is locally `Hⁿ`-integrable on `M ∩ V` in `U'`, then `(M ∩ V, θ, ξ)` satisfies the triple conditions in `U'`.  As `(M ∆ (M ∩ V)) ∩ V = ∅`, at `x ∈ V` the weighted tangent spaces of `(M, θ)` are those of `(M ∩ V, θ)` (`Submission.br_weightedTangent_congr`).
- **Calls**: `br_weightedTangent_congr` (A.3)
- **Called by**: `br_local_finite_mass_extension`

#### `fiw_im_mass_formula` (L31087)

- `root.flat_iff_weak-a1.im_mass_formula-a1` · issue #814 · PR #1823 · candidate `83e1f61809c1`
- **Statement and proof**: **Mass of `τ(M, θ, ξ)` (Simon Ch. 6, Remark 3.2(3), with 2.7–2.8).**  If `T = τ(M, θ, ξ)` for a rectifiable triple in `U`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  For `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal; with `dx^β` the coordinate wedges, the Cauchy–Binet identity `∑_β ξ(x)(dx^β)² = 1` (from the expansion `α = ∑_β α(e_β) dx^β` applied to `⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τₙ, ·⟩`) gives `|ξ(x)(α)| ≤ |α|`, hence `≤`, and makes `b = (ξ(dx^β))_β` a unit vector with `ξ(∑_β b_β dx^β) = 1`.  For `≥`, exhaust `W ∩ U` by compact sets `K`; approximate `1_K b` in `L¹(θ Hⁿ ⌞ K')`, `K'` a compact neighbourhood of `K`, by a continuous compactly supported map, cut it off near `K`, retract it radially onto the unit ball, mollify and rescale. The resulting test form `ω`, with `|ω| ≤ 1` and `spt ω ⊆ W`, has `T(ω) ≥ ∫_{K ∩ M} θ dHⁿ - ε`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_local_finite_mass_extension`, `fiw_im_series`, `fiw_im_lincomb`, `fiw_localization`, `fiw_total_boundedness`

#### `br_boundary_isIntegerMultiplicity_of_finite_mass` (L31037)

- `root.boundary_rectifiability-a1.finite_mass_boundary_im-a1` · issue #877 · PR #4351 · candidate `4f122ed465fe`
- **Statement and proof**: Simon Ch. 6, 6.3 for `U = ℝ^P` and finite masses (proof of 6.3 and Remark 6.4): integer lattice chains `P_k ⇀ X` with `sup_k M(∂P_k) < ∞` (deformation theorem); the `∂P_k` are integer multiplicity cycles with `∂P_k ⇀ ∂X` and `M_W(∂P_k) ≤ M(∂P_k)`, so `∂X` is integer multiplicity by the zero-dimensional case for `m = 0` and by 8.2 for `m ≥ 1`.
- **Calls**: `br_lattice_approximation`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_zero_dim_weak_limit_isIntegerMultiplicity`
- **Called by**: `boundary_rectifiability`

#### `br_lattice_approximation` (L30990)

- `root.boundary_rectifiability-a1.lattice_approximation-a1` · issue #873 · PR #4129 · candidate `e0e5bf49d43e`
- **Statement and proof**: **Lattice approximation with bounded boundary masses** (the first paragraph of the proof of Simon Ch. 6, 6.2, p. 169, for `M(X), M(∂X) < ∞`).  If `P < m + 1` every `(m+1)`-current on `ℝ^P` vanishes and `P_k = 0` works; `P = m + 1` is `br_top_dim_lattice_approximation`.  If `P = m + 1 + ℓ` with `ℓ ≥ 1`, the Deformation Theorem 5.3 at scale `ρ_k = 1/(k+1)` gives `X − P_k = ∂R_k + S_k` with integer `β_F`, `M(∂P_k) ≤ C M(∂X)`, `M(R_k) ≤ C ρ_k M(X) → 0` and `M(S_k) ≤ C ρ_k M(∂X) → 0`, so `P_k ⇀ X`.
- **Calls**: `br_la_apply_eq_zero_of_lt_degree` (A.3), `br_top_dim_lattice_approximation`, `br_la_weaklyConvergesOn_of_flat_decomposition`
- **Called by**: `br_boundary_isIntegerMultiplicity_of_finite_mass`

#### `br_top_dim_lattice_approximation` (L29923)

- `root.boundary_rectifiability-a1.top_dim_lattice_approx-a1` · issue #871 · PR #3942 · candidate `15d1b4cf7f39`
- **Statement and proof** (no doc comment in the source; summary of the accepted natural-language proof): **Codimension-zero integer lattice approximation** (printed (27)–(37) of the proof of 5.1 with `Q = X`). If `X ∈ 𝒟ₙ(ℝⁿ)`, `n = m + 1`, is integer multiplicity with `M(X), M(∂X) < ∞`, there are scales `ρ_k > 0`, integer coefficients `β_k` and lattice chains `P_k = ∑_F β_k(F) [[F]]` over the cubes of `𝓛ₙ(ρ_k)` with `P_k ⇀ X` and `sup_k M(∂P_k) < ∞`. Proof: `X(ω) = ∫ u ω(e₀, …, e_{n−1}) dLⁿ` with `u` integer valued and integrable; the variation of `u` on an open `V` is bounded by `M_V(∂X)`; a localized translation inequality on boxes; integer medians `β_C` on the cubes `C` give `M(X − P) ≤ cρ M(∂X)`, and comparing the medians of adjacent cubes, with Stokes on lattice faces (`br_lattice_face_stokes`), gives `M(∂P) ≤ c M(∂X)`; take `ρ_k = 1/(k+1)`.
- **Calls**: `br_lattice_face_stokes`
- **Called by**: `br_lattice_approximation`

#### `br_lattice_face_stokes` (L28910)

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1` · issue #863 · PR #2192 · candidate `c6266655f0f0`
- **Statement and proof**: Stokes' theorem on a lattice face (Simon Ch. 6, §5 and the proof of 6.3): for `F = (z, α) ∈ 𝓛ₘ₊₁(ρ)` and a smooth `m`-form `ω`, `[[F]](dω) = ∑ᵢ (-1)ⁱ ([[(z + e_{α(i)}, α ∘ succAboveᵢ)]](ω) - [[(z, α ∘ succAboveᵢ)]](ω))`. Every face integral is the integral over its parameter cube `[0, ρ]ᵈ`, and on the cube this is Stokes' theorem (Fubini and the fundamental theorem of calculus).
- **Calls**: `br_latticeFace_setIntegral_eq_cube`, `br_cube_stokes_lattice`
- **Called by**: `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`

#### `br_latticeFace_setIntegral_eq_cube` (L14757)

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1.lattice_face_param-a1` · issue #975 · PR #1510 · candidate `0561b355216f`
- **Statement and proof**: Integrals over a lattice face as integrals over the parameter cube: for every `g`, `∫_{latticeFace ρ G} g dHᵈ = ∫_{[0,ρ]^d} g(∑_l ρ w_l e_l + ∑_j s_j e_{γ(j)}) ds`, `G = (w, γ)`. The map `L(t) = ∑_l ρ w_l e_l + ∑_j t_j e_{γ(j)}` is an isometry (`(e_{γ(j)})_j` is orthonormal) whose range contains the face, so `L_* Hᵈ = Hᵈ ⌞ range L` and the integral is pulled back along `L` and then along the volume-preserving `toLp : (Fin d → ℝ) → ℝᵈ`; the face pulls back to `[0,ρ]^d`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_lcc_face_integral_pos`, `br_lattice_face_stokes`

#### `br_cube_stokes_lattice` (L28802)

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1.cube_stokes-a1` · issue #977 · PR #2148 · candidate `b16cb9a923c3`
- **Statement and proof**: Stokes' theorem on the parameter cube of the lattice face `ρ (z + F_α)`, `F = (z, α)`.  Put `p = ρ z`, `v_j = e_{α j}`, `A(s) = p + ∑_j s_j v_j` and `α_i = α ∘ succAbove_i`; then `∫_{[0,ρ]^{m+1}} dω(A(s))(v) ds` is the alternating sum over `i` of the integrals of `ω(·)(e_{α_i})` over the faces `s_i = ρ` and `s_i = 0`, i.e. of `∫_{[0,ρ]^m} ω(ρ (z + e_{α i}) + ∑_k s_k e_{α_i k})(e_{α_i})` minus `∫_{[0,ρ]^m} ω(p + ∑_k s_k e_{α_i k})(e_{α_i})`. By `exteriorDerivative_apply` and the chain rule, `dω(A(s))(v) = ∑_i (-1)^i Dφ_i(s)(e_i)` for `φ_i(s) = ω(A(s))(removeNth_i v)`; `br_cube_integral_fderiv_eq_faces` integrates each term, and `A(insertNth_i(t, s')) = p + t v_i + ∑_k s'_k e_{α_i k}` identifies the two faces.
- **Calls**: `br_cube_integral_fderiv_eq_faces`
- **Called by**: `br_lattice_face_stokes`

#### `br_cube_integral_fderiv_eq_faces` (L28745)

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1.cube_ftc-a1` · issue #976 · PR #1450 · candidate `f63b90975870`
- **Statement and proof**: Fubini and the fundamental theorem of calculus on the cube `[0,ρ]^{n+1}`: for `φ` of class `C¹` and `e_i = Pi.single i 1`, `∫_{[0,ρ]^{n+1}} Dφ(s)(e_i) ds = ∫_{[0,ρ]^n} (φ(insertNth_i(ρ, s')) - φ(insertNth_i(0, s'))) ds'`. The measure-preserving map `(t, s') ↦ insertNth_i(t, s')` pulls the cube back to `[0,ρ] × [0,ρ]^n`, Fubini puts the `t`-integral inside, and `d/dt φ(insertNth_i(t, s')) = Dφ(insertNth_i(t, s'))(e_i)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_cube_stokes_lattice`

#### `br_la_weaklyConvergesOn_of_flat_decomposition` (L28710)

- `root.boundary_rectifiability-a1.lattice_approximation-a1.flat_to_weak-a1` · issue #1190 · PR #2140 · candidate `d3d5fa610f70`
- **Statement and proof**: **Flat decompositions with vanishing masses converge weakly** (the step "Evidently (1), (2) give `P_k(ω) → T_k(ω)`" in the proof of Simon Ch. 6, 6.2, p. 169, where the printed `T_k(ω)` is a misprint for `T(ω)` **[corrected]**).  Let `X − P_k = ∂R_k + S_k` with `M(R_k), M(S_k) → 0`, and fix `ω` with `|ω| ≤ C₁` and `|dω| ≤ C₂`.  Since `∂R_k(ω) = R_k(dω)`, once both masses are finite `|X(ω) − P_k(ω)| ≤ |R_k(dω)| + |S_k(ω)| ≤ C₂ M(R_k) + C₁ M(S_k)`, and the right-hand side tends to `0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes the sentence of p. 169 with `T(ω)` as the limit. The book prints "Evidently (1), (2) give `P_k(ω) → T_k(ω)` `∀ω ∈ 𝒟ⁿ(ℝ^{n+ℓ})`" (the paragraph after display (2) of the proof of 6.2). No `T_k` is defined there, and `T(ω)` is meant, since display (1) reads `T − P_k = ∂R_k + S_k`. The quotation above now follows the printed text and notes the misprint.
- **Calls**: `br_la_testForm_covectorNorm_bounded` (A.6), `br_la_abs_apply_le_mul_mass` (A.8)
- **Called by**: `br_lattice_approximation`

#### `br_lattice_chain_boundary_isIntegerMultiplicity` (L28933)

- `root.boundary_rectifiability-a1.lattice_boundary_im-a1` · issue #868 · PR #2332 · candidate `37bba5ece947`
- **Statement and proof**: Boundaries of integer lattice chains are integer multiplicity (Simon Ch. 6, §5 and the proof of 6.3).  If `Pc = ∑_F β_F [[F]]` with `β_F ∈ ℤ`, Stokes on each face (`Submission.br_lattice_face_stokes`) and regrouping by `m`-faces give `∂Pc = ∑_G γ_G [[G]]` with `γ_G ∈ ℤ`; only finitely many faces meet the support of a test form, so all sums are finite.  An integer lattice chain `∑_G γ_G [[G]]` is `τ(M, θ, ξ)` with `M` the union of the relative interiors `G°` with `γ_G ≠ 0`, `θ = |γ_G|` and `ξ = sign(γ_G) e_{γ'(0)} ∧ ⋯ ∧ e_{γ'(m-1)}` on `G°`: relative interiors of distinct faces are disjoint, relative boundaries are `Hᵐ`-null, and near a point of `G°` the set `M` is the affine plane of `G` with constant multiplicity, which is therefore the weighted approximate tangent space there.
- **Calls**: `br_lattice_face_stokes`
- **Called by**: `br_boundary_isIntegerMultiplicity_of_finite_mass`

#### `br_zero_dim_weak_limit_isIntegerMultiplicity` (L2343)

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1` · issue #859 · PR #2773 · candidate `66b929ec8db4`
- **Statement and proof**: The case `n = 0` of Simon Ch. 6, 3.11 and 8.2 (p. 176, "trivial in case `n = 0`"), used for 6.3: a weak limit `X` of integer multiplicity `X_j ∈ 𝒟₀(U)` with `sup_j M_W(X_j) < ∞` for every `W ⊂⊂ U` is integer multiplicity.  Each `X_j` is a locally finite integer Dirac sum `∑ᶠ_{x ∈ N_j} c_j(x) ω(x)`.  Near `x₀ ∈ U` take `W = B_{ε/2}(x₀) ⊂⊂ U`; testing with signed bumps, `∑_{x ∈ S} |c_j(x)| ≤ Λ = sup_j M_W(X_j)` for finite `S ⊆ N_j ∩ W`, so on forms supported in `W` the limit `X` is a finite integer Dirac sum, which is an integer multiplicity current.  These local representations patch together.
- **Calls**: `br_zd_im_dirac_repr`, `br_isIntegerMultiplicity_of_local`, `br_zd_dirac_local_limit` (A.9), `br_zd_dirac_massOn_ge`, `br_zd_finite_dirac_im` (A.9)
- **Called by**: `br_boundary_isIntegerMultiplicity_of_finite_mass`

#### `br_zd_im_dirac_repr` (L917)

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_repr-a1` · issue #1092 · PR #2150 · candidate `a530e777eaab`
- **Statement and proof**: Simon Ch. 6, 3.1 with `n = 0` (the `0`-dimensional step in the proof of 6.3): an integer multiplicity `Y = τ(M, θ, ξ) ∈ 𝒟₀(U)` is a locally finite integer combination of point masses, `Y(ω) = ∑_{x ∈ N} c(x) ω(x)` with `c(x) ≠ 0` on `N = M`.  `H⁰` is counting measure, so `H⁰`-null sets are empty and sets of finite `H⁰` measure are finite.  As `θ ≥ 1` on `M` and `θ` is locally `H⁰`-integrable, `M ∩ K` is finite for compact `K ⊆ U`; the orientation condition holds at every point of `M`, where `ξ(x) = ±1` (the empty wedge) **[corrected]**, so `c(x) = θ(x) ξ(x)(1) = ±θ(x)` is a nonzero integer, and the integral over `M` reduces to the finite sum over `M ∩ spt ω`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), writes `ξ(x) = ±[[x]]`. `ξ(x)` is a `0`-vector, i.e. `±1`; `[[x]]` is the Dirac current at `x`, and the same sentence evaluates `ξ(x)(1)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_zero_dim_weak_limit_isIntegerMultiplicity`

#### `br_zd_dirac_massOn_ge` (L1064)

- `root.boundary_rectifiability-a1.zero_dim_weak_limit-a1.dirac_mass_bound-a1` · issue #1094 · PR #2281 · candidate `6b7f8aea1c33`
- **Statement and proof**: The mass lower bound for a locally finite Dirac sum (the `0`-dimensional step in the proof of Simon Ch. 6, 6.3): if `Y(ω) = ∑ᶠ_{x ∈ N} c(x) ω(x)` with `N ∩ K` finite for compact `K ⊆ U`, then `∑_{x ∈ S} |c(x)| ≤ M_W(Y)` for every finite `S ⊆ N ∩ W`, `W ⊆ U` open.  Test with `ω = ∑_{x ∈ S} sign(c(x)) φₓ`, where the bumps `φₓ` (`φₓ(x) = 1`) have pairwise disjoint supports `B(x, δ) ⊆ W` meeting `N` only in `x`: then `|ω| ≤ 1` and `Y(ω) = ∑_{x ∈ S} |c(x)|`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `br_zero_dim_weak_limit_isIntegerMultiplicity`

### A.11 Theorem 7.2 (§3.11): `flat_convergence_iff_weak_convergence` and its 58 further declarations

#### `flat_convergence_iff_weak_convergence` (L69448)

- `root.flat_iff_weak-a1` · issue #338 · PR #8796 · candidate `7c119a556b4c`
- **Statement and proof**: **Simon Ch. 6, Theorem 7.2 (pp. 170–172).**  For integer multiplicity `T, T_j ∈ 𝒟ₙ(U)` with `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`, `T_j ⇀ T` iff `d_W(T_j, T) → 0` for every `W ⊂⊂ U`.  The "if" part is `fiw_flat_to_weak`.  For "only if", fix `W ⊂⊂ U`; by the subsequence principle it suffices that every subsequence `T_{ns j}` has a further subsequence with `d_W(·, T) → 0`.  Localization (printed (4)) gives integral currents `T'_j ⇀ T'` with supports in a fixed compact `K ⊆ U` and bounded `M(T'_j) + M(∂T'_j)`, such that every decomposition `T'_j − T' = ∂R + S` with `R`, `S` integer multiplicity **[corrected]** bounds `d_W(T_{ns(ψ j)}, T)` by `M_W(S) + M_W(R)`.  Total boundedness ((1)–(3), from the Deformation Theorem) and the series of 3.13 ((5) and `R^(ℓ)`, `S^(ℓ)`) give such decompositions with `M(R) + M(S) ≤ 2 · 2^{-ℓ}` along a subsequence `φ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), omits that `R` and `S` are integer multiplicity, as `d_W` (7.1) and the Lean statement of `fiw_localization` require.
- **Calls**: `fiw_flat_to_weak`, `fiw_localization`, `slicing_theorem` (A.5), `boundary_rectifiability` (A.10), `fiw_flat_cauchy_limit`, `fiw_total_boundedness`, `deformation_theorem` (A.6)
- **Called by**: `main_theorem`

#### `fiw_flat_to_weak` (L15470)

- `root.flat_iff_weak-a1.flat_to_weak-a1` · issue #806 · PR #1760 · candidate `92fbe5f913e3`
- **Statement and proof**: Flat convergence implies weak convergence (Simon Ch. 6, proof of 7.2, the "if" part): for `ω ∈ 𝒟ⁿ(U)` take `W ⊂⊂ U` containing `spt ω ⊇ spt dω`; a decomposition `T_j − T = ∂R + S` with `M_W(S) + M_W(R) < δ` gives `|T_j(ω) − T(ω)| = |R(dω) + S(ω)| ≤ δ (sup |dω| + sup |ω|)`.
- **Calls**: `cmb_exists_compactly_contained_exhaustion` (A.1), `cmb_abs_apply_le_of_massOn_le` (A.1)
- **Called by**: `flat_convergence_iff_weak_convergence`

#### `fiw_localization` (L64437)

- `root.flat_iff_weak-a1.localization-a1` · issue #824 · PR #5105 · candidate `7ece361b32af`
- **Statement and proof**: **Localization step in the proof of Simon Ch. 6, Theorem 7.2 (stated on pp. 170–171), reduction (4) (pp. 171–172) **[corrected]**.** Given integer multiplicity `T_j ⇀ T` with locally bounded `M_V(T_j) + M_V(∂T_j)` and `W ⊂⊂ U`, pass to a subsequence `ψ` and cut every `T_{ψ(j)}` (and `T`) along a level set `{φ = s}` of `φ = δ - dist(·, closure W)`: * Helly selection (diagonal subsequence along which `μ_{T_j}({φ ≥ q})` converges for rational `q`) and Fatou's lemma applied to the slice masses (4.10 clause of the Slicing Theorem) give a level `s` that is a continuity point of the limit and along which the slices have bounded mass; * `T'_j = T_{ψ(j)} ⌞ {φ ≥ s}` and `T' = T ⌞ {φ ≥ s}` are integer multiplicity (restriction calculus: uniqueness of the representing vector measure (2.7)–(2.9) and locality of approximate tangent spaces), `∂T'_j = (∂T_{ψ(j)}) ⌞ {φ ≥ s} - ⟨T_{ψ(j)}, φ, s⟩` is integer multiplicity by Boundary Rectifiability (6.3), `spt T'_j ⊆ {φ ≥ s}`, and the masses are uniformly bounded; * `T'_j ⇀ T'` by smooth cutoffs between rational levels around `s`; * a flat decomposition `T'_j - T' = ∂R + S` transfers to `T_{ψ(j)} - T = ∂R + Ŝ` with `Ŝ` agreeing with `S` on forms supported in `W`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), gives p. 170, where the statement of 7.2 begins. The proof begins on p. 171, and the reduction leading to display (4) runs from p. 171 to p. 172.
- **Calls**: `fiw_tangent_locality`, `fiw_im_lincomb`, `fiw_im_mass_formula` (A.10)
- **Called by**: `flat_convergence_iff_weak_convergence`

#### `fiw_tangent_locality` (L64325)

- `root.flat_iff_weak-a1.tangent_locality-a1` · issue #809 · PR #4919 · candidate `e508153288a8`
- **Statement and proof**: Locality of weighted approximate tangent spaces (Simon Ch. 3, Remarks 1.5(2), 1.8(1); the step `T_x M_+ = T_x M_Q`, `M_+ = {θ > 0}`, in the proof of Ch. 6, Lemma 3.13, p. 150 **[corrected]**): for `Hⁿ`-a.e. `x ∈ M₁ ∩ M₂`, every weighted approximate tangent space of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  By `fiw_tl_ae_l1_density`, a.e. `x ∈ M₁ ∩ M₂` has `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ = o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` as `s ↓ 0`, where `c = θ₂(x) / θ₁(x)`, so `θ₂(x) = c θ₁(x)`.  As `x ∈ U`, some compact `B̄_ρ(x)` lies in `U`, so `θᵢ` is integrable on `Mᵢ ∩ B̄_ρ(x)`, and `fiw_tl_transfer` carries the tangent space from `(M₁, θ₁)` to `(M₂, θ₂)`.  The exceptional null set does not depend on `Q`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), writes "`T_x M_C`". The book has no set `M_C`: the proof of 3.13 defines `M_+ = {x ∈ U : θ(x) > 0}` (p. 150) and states "(by (3)) `T_x M_+ = T_x M_Q`"; the text extraction of the book renders `+` as `C`.
- **Calls**: `fiw_tl_ae_l1_density`, `fiw_tl_transfer`
- **Called by**: `fiw_im_series`, `fiw_localization`

#### `fiw_tl_ae_l1_density` (L64288)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1` · issue #2187 · PR #4860 · candidate `13182a2385ff`
- **Statement and proof**: Relative `L¹` density of the weighted measures `θᵢ Hⁿ ⌞ Mᵢ`, as used for the locality of approximate tangent spaces (Simon Ch. 3, Remark 1.8(1)): for `Hⁿ ⌞ (M₁ ∩ M₂)`-a.e. `x` and every `ε > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − (θ₂(x)/θ₁(x)) 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ` for all small `s > 0`.  Cover `U` by balls `B_r(y)` with `B̄_r(y) ⊆ U`.  On each, `θᵢ` is integrable on `Mᵢ ∩ B̄_r(y)`, since `B̄_r(y) ⊆ U` is compact **[corrected]**, so the weighted Lebesgue-point and Besicovitch density limits hold a.e. on `M₁ ∩ M₂ ∩ B_r(y)`; at such `x` they give the estimate, with `ρ = r − dist(x, y)`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), calls `Mᵢ ∩ B̄_r(y)` compact; `Mᵢ` is only null-measurable, so this set need not be compact. Only the compactness of `B̄_r(y) ⊆ U` is used.
- **Calls**: `fiw_tl_ald_ball_reduction`, `fiw_tl_ald_local_differentiation`, `fiw_tl_ald_pointwise_estimate`
- **Called by**: `fiw_tangent_locality`

#### `fiw_tl_ald_ball_reduction` (L63892)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.ball_reduction-a1` · issue #3174 · PR #3646 · candidate `92d0d93e6471`
- **Statement and proof**: Reduction of an almost-everywhere property to balls: if `Φ` holds `μ ⌞ (A ∩ B_r(y))`-a.e. for every ball with `B̄_r(y) ⊆ U`, then `Φ` holds `μ ⌞ A`-a.e. for `A ⊆ U`, `U` open.  Countably many such balls cover `A` (`ℝ^P` is second countable), and `μ ⌞ A`-a.e. is checked on the pieces of a countable cover without any measurability assumption.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_ae_l1_density`

#### `fiw_tl_ald_local_differentiation` (L64064)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1` · issue #3194 · PR #4541 · candidate `f7b69229c6f2`
- **Statement and proof**: Local differentiation on a ball: let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on `Mᵢ ∩ B̄_r(y)` and `g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  For `Hⁿ ⌞ (M₁ ∩ M₂ ∩ B_r(y))`-a.e. `x`, as `s → 0⁺`, `x` is a Lebesgue point of `g` for `θ₁ Hⁿ ⌞ M₁` and `M₁ ∩ M₂` has density `1` at `x` for `θ₂ Hⁿ ⌞ M₂`, both along the closed balls `B̄_s(x)`.  Since `θ₁ g = 1_{M₁ ∩ M₂} θ₂` is integrable on `M₁ ∩ B̄_r(y)`, these are the weighted Lebesgue-point lemma for `(M₁, θ₁, g)`, with `g(x) = θ₂(x)/θ₁(x)` on `M₁ ∩ M₂`, and the weighted density lemma for `M₁ ∩ M₂ ⊆ M₂`.
- **Calls**: `fiw_tl_ald_ld_weighted_lebesgue_point`, `fiw_tl_ald_ld_weighted_density_point`
- **Called by**: `fiw_tl_ae_l1_density`

#### `fiw_tl_ald_ld_weighted_lebesgue_point` (L63921)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_lebesgue_point-a1` · issue #3622 · PR #4293 · candidate `19e517b0daf0`
- **Statement and proof**: Weighted Lebesgue points (for the locality of weighted approximate tangent spaces, Simon Ch. 3, 1.5(2), 1.8(1)).  Let `M ⊆ ℝ^P` be `μ`-null-measurable, `θ > 0` on `M`, and `θ`, `θ f` `μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ M ∩ B_r(y)`, `∫_{M ∩ B̄_s(x)} θ |f - f(x)| dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 0` as `s ↓ 0`.  The measure `ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite, `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, and `f ∈ L¹(ν)` as `θ f ∈ L¹(μ ⌞ (M ∩ B̄_r(y)))`.  So the Lebesgue differentiation theorem for `ν` along closed balls (Simon Ch. 1, 3.17; `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div` for `Besicovitch.vitaliFamily ν`) holds `μ ⌞ (M ∩ B_r(y))`-a.e.; for `0 < s < r - |x - y|`, `B̄_s(x) ⊆ B̄_r(y)`, so the two `ν`-integrals over `B̄_s(x)` are the two integrals above.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_ald_local_differentiation`

#### `fiw_tl_ald_ld_weighted_density_point` (L63995)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_density_point-a1` · issue #3626 · PR #4372 · candidate `fa6e66cc9288`
- **Statement and proof**: Weighted density points (for the locality of weighted approximate tangent spaces, Simon Ch. 3, 1.5(2), 1.8(1)).  Let `M, E ⊆ ℝ^P` be `μ`-null-measurable with `E ⊆ M`, `θ > 0` on `M` and `θ` `μ`-integrable on `M ∩ B̄_r(y)`.  Then for `μ`-a.e. `x ∈ E ∩ B_r(y)`, `∫_{E ∩ B̄_s(x)} θ dμ / ∫_{M ∩ B̄_s(x)} θ dμ → 1` as `s ↓ 0`.  The measure `ν = θ⁺ μ ⌞ (M ∩ B̄_r(y))` is finite and `μ ⌞ (M ∩ B̄_r(y)) ≪ ν` as `θ > 0` on `M`, so `μ ⌞ (E ∩ B_r(y)) ≪ ν ⌞ E` and the Besicovitch density theorem for `ν` and `E` (`Besicovitch.ae_tendsto_measure_inter_div`) applies; for `0 < s < r - |x - y|`, `B̄_s(x) ⊆ B̄_r(y)`, so `ν(E ∩ B̄_s(x))` and `ν(B̄_s(x))` are the two integrals.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_ald_local_differentiation`

#### `fiw_tl_ald_pointwise_estimate` (L64115)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.pointwise_estimate-a1` · issue #3205 · PR #3964 · candidate `77e959a3b214`
- **Statement and proof**: Relative `L¹` estimate at a point.  Let `θᵢ > 0` on `Mᵢ` be `Hⁿ`-integrable on `Mᵢ ∩ B̄_ρ(x)`, `x ∈ M₁ ∩ M₂`, `c = θ₂(x)/θ₁(x)` and `g = 1_{M₁ ∩ M₂} θ₂/θ₁`.  If, as `s ↓ 0`, (L) `∫_{M₁ ∩ B̄_s(x)} θ₁ |g − c| dHⁿ / ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ → 0` and (D) `∫_{M₁ ∩ M₂ ∩ B̄_s(x)} θ₂ dHⁿ / ∫_{M₂ ∩ B̄_s(x)} θ₂ dHⁿ → 1`, then for every `ε > 0` and all small `s > 0`, `∫_{B̄_s(x)} |1_{M₂} θ₂ − c 1_{M₁} θ₁| dHⁿ ≤ ε ∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ`. Pointwise `|1_{M₂} θ₂ − c 1_{M₁} θ₁| = 1_{M₁} θ₁ |g − c| + 1_{M₂ ∖ M₁} θ₂`.  With `bᵢ = ∫_{Mᵢ ∩ B̄_s(x)} θᵢ dHⁿ`, (L) bounds the first part by `δ b₁` and (D) bounds the second by `δ b₂ ≤ 2δ(c + δ) b₁`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_ae_l1_density`

#### `fiw_tl_transfer` (L63833)

- `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1` · issue #2173 · PR #3907 · candidate `f79cbc10fe41`
- **Statement and proof**: Simon Ch. 3, Remarks 1.5(2), 1.8(1): pointwise transfer of a weighted approximate tangent space.  If `θ₂(x) = c θ₁(x)` and `h = 1_{M₂}θ₂ − c 1_{M₁}θ₁` is `o(∫_{M₁ ∩ B̄_s(x)} θ₁ dHⁿ)` in `L¹(B̄_s(x))` as `s ↓ 0`, then every tangent space `Q` of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`. For `f ∈ C_c(ℝ^P)` (`f = 0` off `B_R(0)`, `|f| ≤ K`) the tangent integrals are `I_i(r) = r⁻ⁿ ∫_{M_i} f(η_r z) θ_i(z) dHⁿ(z)` by `fiw_tl_blowup_setIntegral`, so `|I₂(r) − c I₁(r)| ≤ r⁻ⁿ K ∫_{B̄_{Rr}(x)} |h| dHⁿ` (`fiw_tl_tr_weighted_diff_bound`), which tends to `0` by `fiw_tl_growth_bound` and `fiw_tl_tr_scaling_limit`.  Hence `I₂(r) → c θ₁(x) ∫_Q f dHⁿ = θ₂(x) ∫_Q f dHⁿ`.
- **Calls**: `fiw_tl_growth_bound`, `fiw_tl_tr_scaling_limit`, `fiw_tl_blowup_setIntegral` (A.6), `fiw_tl_tr_weighted_diff_bound`
- **Called by**: `fiw_tangent_locality`

#### `fiw_tl_growth_bound` (L63748)

- `root.flat_iff_weak-a1.tangent_locality-a1.growth_bound-a1` · issue #2161 · PR #3273 · candidate `2a9dc9351920`
- **Statement and proof**: Simon Ch. 3, 1.7 and Remark 1.8(2) **[corrected]**: if `M` has weighted approximate tangent space `Q` at `x` and `θ ≥ 0` is `Hⁿ`-integrable on `M ∩ B̄_ρ(x)`, then `∫_{M ∩ B̄_s(x)} θ dHⁿ ≤ C sⁿ` for all small `s > 0`. Test with the cut-off `f₀ = max 0 (min 1 (2 - ‖·‖))` (`= 1` on `B̄₁(0)`, `= 0` off `B₂(0)`): by `fiw_tl_blowup_setIntegral` the tangent integrals equal `s⁻ⁿ ∫_M f₀(η_s z) θ(z) dHⁿ(z)`, which dominate `s⁻ⁿ ∫_{M ∩ B̄_s(x)} θ dHⁿ` and converge as `s ↓ 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), cites only Ch. 3, 1.7, the definition. The bound is the upper half of the density statement of Remark 1.8(2) (p. 75), proved as there with a cut-off test function.
- **Calls**: `fiw_tl_blowup_setIntegral` (A.6)
- **Called by**: `fiw_tl_transfer`

#### `fiw_tl_tr_scaling_limit` (L63689)

- `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.scaling_limit-a1` · issue #3275 · PR #3717 · candidate `0f6aba64e395`
- **Statement and proof**: Little-o scaling limit (step 7 of the proof of `fiw_tl_transfer`): if `R > 0`, `E = o(G)` and `G(s) ≤ C sⁿ` as `s → 0⁺`, and `‖D(r)‖ₑ ≤ (rⁿ)⁻¹ · K · E(R r)` for small `r > 0`, then `D(r) → 0` as `r → 0⁺`.  With `K₁ = max(K, 0)`, `C₁ = max(C, 0)`, `A = K₁ C₁ Rⁿ` and `ε' = ε / (2(A + 1))`, for small `r > 0`: `|D(r)| ≤ (rⁿ)⁻¹ · K₁ · ε' · C₁ (R r)ⁿ = A ε' < ε`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_transfer`

#### `fiw_tl_tr_weighted_diff_bound` (L63620)

- `root.flat_iff_weak-a1.tangent_locality-a1.pointwise_transfer-a1.weighted_diff_bound-a1` · issue #3257 · PR #3743 · candidate `0b194113f2f0`
- **Statement and proof**: `L¹` comparison of two weighted integrals against a bounded continuous test weight `φ` vanishing off `B̄_s(x)`, `s ≤ ρ`: with `h = 1_{M₂} θ₂ - c 1_{M₁} θ₁`, `‖∫_{M₂} φ θ₂ - c ∫_{M₁} φ θ₁‖ₑ ≤ K · ∫⁻_{B̄_s(x)} ‖h‖ₑ`. Both integrals are integrals of `φ · 1_{M_i} θ_i = φ · 1_{M_i ∩ B̄_ρ(x)} θ_i`, which are integrable, so the difference is `∫ φ h`, and `‖φ h‖ₑ ≤ 1_{B̄_s(x)} K ‖h‖ₑ` pointwise.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tl_transfer`

#### `fiw_im_lincomb` (L64380)

- `root.flat_iff_weak-a1.im_lincomb-a1` · issue #819 · PR #5044 · candidate `fbf0e325eb4f`
- **Statement and proof**: Simon Ch. 6, Remark 3.2(1): if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and `a, b ∈ ℤ`, then `S = a T₁ + b T₂` is integer multiplicity.  This is the finite case of `Submission.fiw_im_series`, for the family `(T₁, T₂, T₁, T₁, …)` with coefficients `(a, b, 0, 0, …)`; its mass hypothesis holds because integer multiplicity currents have `M_W < ∞` for `W ⊂⊂ U` (`Submission.fiw_im_mass_formula`).
- **Calls**: `fiw_im_mass_formula` (A.10), `fiw_im_series`
- **Called by**: `fiw_localization`, `fiw_total_boundedness`

#### `fiw_im_series` (L64348)

- `root.flat_iff_weak-a1.im_series-a1` · issue #817 · PR #4956 · candidate `986c7e45798f`
- **Statement and proof**: **Integer series of integer multiplicity currents (Simon Ch. 6, Lemma 3.13 for `M`-absolutely convergent series, as used for `R^(ℓ)`, `S^(ℓ)` in the proof of 7.2; contains Remark 3.2(1)).** If the `T_r` are integer multiplicity and `∑ |c_r| M_W(T_r) < ∞` for every `W ⊂⊂ U`, then `S(ω) = ∑ c_r T_r(ω)` (unconditionally) defines an integer multiplicity current with `M_W(S) ≤ ∑ |c_r| M_W(T_r)` for every `W`.  `Submission.fiw_ims_series_current` gives the current `S` and the mass bound.  Writing `T_r = τ(M_r, θ_r, ξ_r)`, the mass formula 3.2(3) (`Submission.fiw_im_mass_formula`) turns the hypothesis into `∑ |c_r| ∫_{M_r ∩ W} θ_r dHⁿ < ∞`, so `Submission.fiw_ims_combine`, with tangent locality `Submission.fiw_tangent_locality`, gives an integer rectifiable triple `(M', θ', ξ')` with `∑ c_r T_r(ω) = τ(M', θ', ξ')(ω)`.  By uniqueness of sums `S = τ(M', θ', ξ')`.
- **Calls**: `fiw_ims_series_current` (A.6), `fiw_im_mass_formula` (A.10), `fiw_ims_combine` (A.6), `fiw_tangent_locality`
- **Called by**: `fiw_im_lincomb`, `fiw_flat_cauchy_limit`

#### `fiw_flat_cauchy_limit` (L65704)

- `root.flat_iff_weak-a1.flat_cauchy_limit-a1` · issue #828 · PR #5080 · candidate `25b4585dc2a4`
- **Statement and proof**: Simon Ch. 6, proof of 7.2 (p. 172), from (5) to `T − T_{j_ℓ} = ∂R^(ℓ) + S^(ℓ)`: if `T_j ⇀ T` and, for every `ε > 0` **[corrected]**, every infinite `J ⊆ ℕ` contains an infinite `J'` with `T_i − T_j = ∂R + S` for `i, j ∈ J'` (`R`, `S` integer multiplicity, `M(R) + M(S) < ε`), then for some subsequence `T_{φ(ℓ)}`, `T_{φ(ℓ)} − T = ∂R + S` with `R`, `S` integer multiplicity and `M(R) + M(S) ≤ 2 · 2^{-ℓ}`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), leaves `ε` unquantified; in the Lean statement (line 65706) the hypothesis holds for every `ε > 0`.
- **Calls**: `fiw_fcl_nested_subseq`, `fiw_im_series`, `fiw_fcl_telescope_limit`
- **Called by**: `flat_convergence_iff_weak_convergence`

#### `fiw_fcl_nested_subseq` (L803)

- `root.flat_iff_weak-a1.flat_cauchy_limit-a1.nested_subseq-a1` · issue #1051 · PR #1600 · candidate `ca04907a3867`
- **Statement and proof**: Diagonal extraction from nested infinite index sets (Simon Ch. 6, proof of 7.2): with `J 0 = ℕ` and infinite `J (r + 1) ⊆ J r` on which `Q r` holds for all pairs, an increasing choice `φ r ∈ J (r + 1)` puts both `φ r` and `φ (r + 1)` in `J (r + 1)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_flat_cauchy_limit`

#### `fiw_fcl_telescope_limit` (L831)

- `root.flat_iff_weak-a1.flat_cauchy_limit-a1.telescope_limit-a1` · issue #1053 · PR #1748 · candidate `d757828a49ef`
- **Statement and proof**: Simon Ch. 6, proof of 7.2 (last paragraph, from (5)): if `T_r − T_{r+1} = ∂R_r + S_r`, `T_r ⇀ T`, and `X = ∑_k R_{ℓ+k}`, `Y = ∑_k S_{ℓ+k}` pointwise on test forms, then `T_ℓ − T = ∂X + Y`.  With `∂Z(ω) = Z(dω)`, telescoping gives `T_ℓ(ω) − T_{ℓ+N}(ω) = ∑_{k<N} (R_{ℓ+k}(dω) + S_{ℓ+k}(ω))`; as `N → ∞` the left side tends to `T_ℓ(ω) − T(ω)` and the right side to `X(dω) + Y(ω)`, and limits in `ℝ` are unique.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_flat_cauchy_limit`

#### `fiw_total_boundedness` (L69407)

- `root.flat_iff_weak-a1.total_boundedness-a1` · issue #826 · PR #5211 · candidate `efabafdb22bd`
- **Statement and proof**: **Total boundedness (Simon Ch. 6, proof of 7.2, (1)–(3)).**  Assume the Deformation Theorem, and let `T_j ∈ 𝒟_{m+1}(U)` be integer multiplicity with `∂T_j` integer multiplicity, `spt T_j ⊆ K` (`K ⊆ U` compact) and `M(T_j) + M(∂T_j) ≤ B < ∞`.  For `ε > 0` and infinite `J ⊆ ℕ` there is an infinite `J' ⊆ J` such that for `i, j ∈ J'`, `T_i − T_j = ∂R + S` with `R, S` integer multiplicity and `M(R) + M(S) < ε`.  With `C` from the finite flat net (`fiw_tb_finite_net`), pick `ρ > 0` with `ρ · 2CB < ε`; the net at scale `ρ` gives finitely many centres `Q` and, for each `j`, a centre `Q_j` with `T_j − Q_j = ∂R_j + S_j`, `M(R_j) + M(S_j) ≤ CρB`.  By the pigeonhole principle some fibre `J' = {j ∈ J : Q_j = q}` is infinite, and for `i, j ∈ J'` the difference of the two decompositions (`fiw_tb_flat_sub`) has `T_i − T_j = ∂R + S` and `M(R) + M(S) ≤ 2CρB < ε`.
- **Calls**: `fiw_tb_finite_net`, `fiw_im_mass_formula` (A.10), `fiw_im_lincomb`, `fiw_tb_flat_sub`
- **Called by**: `flat_convergence_iff_weak_convergence`

#### `fiw_tb_finite_net` (L69233)

- `root.flat_iff_weak-a1.total_boundedness-a1.finite_net-a1` · issue #2393 · PR #5123 · candidate `16bd0f6600e7`
- **Statement and proof**: Simon Ch. 6, proof of 7.2 (p. 171, (1)–(3)): for `K ⊆ U` compact there is `C` such that for every `B < ∞` and `ρ > 0` there is a finite set `𝒬 ⊆ 𝒟_{m+1}(U)` such that every `T` with `T`, `∂T` integer multiplicity, `spt T ⊆ K` and `M(T) + M(∂T) ≤ B` satisfies `T − Q = ∂R + S` for some `Q ∈ 𝒬` **[corrected]**, with `R`, `S` integer multiplicity and `M(R) + M(S) ≤ C ρ B`.  If `P < m + 1` then `T = 0`; otherwise the centres `Q` are restrictions to `U` of lattice chains, from the Deformation Theorem (`P ≥ m + 2`) or `fiw_tb_top_dim_approx` (`P = m + 1`), whose integer coefficients range over a finite set (`fiw_tb_lattice_coeff_finite`).
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says that finitely many `Q` "have the property that every `T` … is `T − Q = ∂R + S`", which read literally puts every `T` near every `Q`. The Lean statement (lines 69245–69248) gives a finite set `Qs` such that every admissible `T` is near some `Q ∈ Qs`.
- **Calls**: `fiw_tb_extend_to_univ`, `fiw_tb_restrictDomain_mass_im`, `fiw_tb_top_dim_approx`, `fiw_tb_lattice_coeff_finite`, `fiw_tb_lattice_chain_coeff`
- **Called by**: `fiw_total_boundedness`

#### `fiw_tb_extend_to_univ` (L14702)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1` · issue #2359 · PR #4122 · candidate `f174a9de703a`
- **Statement and proof**: **Extension of a compactly supported current to `ℝ^P` (preliminary (G3) of the accepted proof of `fiw_total_boundedness`, the formal version of Simon Ch. 6, proof of 7.2, (1)–(3) **[corrected]**).** If `spt X ⊆ K` with `K ⊆ U` compact and `M(X) < ∞`, then `Y(ω) = X(χ ω)`, `χ` a smooth cutoff with `tsupport χ ⊆ U` and `χ = 1` on an open `N ⊇ K`, is a current on `ℝ^P` (`fiw_tb_ext_cutoff`, `fiw_tb_ext_cutoff_current`).  Since `X` kills test forms whose support misses `K` (`fiw_tb_apply_eq_zero_of_disjoint_support`) and `χ ω = ω` on `N`, `Y|_U = X` (`fiw_tb_ext_apply_eq_of_eqOn`); `Y` and `∂Y` kill test forms whose support misses `K`, as `tsupport (χ ω) ⊆ tsupport ω` and `tsupport dω ⊆ tsupport ω`, and `(∂Y)|_U = ∂X`.  Support, mass and integer multiplicity of `Y` and `∂Y` are then controlled by those of their restrictions `X` and `∂X` (`fiw_tb_ext_support_subset`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`).  The mass formula (MF) is not needed.
- **Correction**: the Lean doc comment, kept byte-identical (§9), says "(Simon Ch. 6, proof of 7.2, (G3))". Simon's proof of 7.2 (pp. 171–172) is labelled only (1)–(5). (G3) is preliminary (G3) of the accepted natural-language proof of the parent node `root.flat_iff_weak-a1.total_boundedness-a1` (`fiw_total_boundedness`). Simon's text leaves this step implicit: it applies 5.3, which concerns currents in `ℝ^{n+ℓ}`, to currents in `U` in (1)–(3).
- **Calls**: `fiw_tb_apply_eq_zero_of_disjoint_support`, `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_apply_eq_of_eqOn`, `fiw_tb_ext_support_subset` (A.9), `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`
- **Called by**: `fiw_tb_finite_net`

#### `fiw_tb_apply_eq_zero_of_disjoint_support` (L14579)

- `root.flat_iff_weak-a1.total_boundedness-a1.vanish_off_support-a1` · issue #2338 · PR #2949 · candidate `702dace4538c`
- **Statement and proof**: Simon Ch. 6, 2.11: a current kills every test form whose support misses `spt T`. `tsupport ω` is a compact subset of the zero region, so finitely many open `W ⊂⊂ U` on which `T` vanishes cover it, and a smooth partition of unity `ψᵢ` on `tsupport ω` subordinate to them splits `ω = ∑ᵢ ψᵢ ω` into test forms supported in those `W`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_rectifiable_support_null`, `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_cutoff` (L622)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff-a1` · issue #3227 · PR #3759 · candidate `ecf4b9ac471b`
- **Statement and proof**: Smooth cutoff: for a compact `K` inside an open `U ⊆ ℝ^P` there is a `C^∞` function `0 ≤ χ ≤ 1` with compact support in `U` that equals `1` on an open neighbourhood `N` of `K`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_smul_testForm` (L642)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.smul_testform-a1` · issue #3232 · PR #3821 · candidate `681990946892`
- **Statement and proof**: Products with a cutoff (Simon Ch. 6, §2): if `χ` is `C^∞` with `tsupport χ ⊆ W`, then `ω ↦ χ ω` is a linear map `𝒟^q(V) → 𝒟^q(W)`, acting pointwise on the underlying forms.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_cutoff_current` (L13363)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.cutoff_current-a1` · issue #3291 · PR #3885 · candidate `d39fb30b5115`
- **Statement and proof**: **Cut-off of a finite-mass current (Simon Ch. 6, 2.1, 2.4).**  If `χ` is smooth with `tsupport χ ⊆ U` and `|χ| ≤ 1`, and `X ∈ 𝒟_q(U)` has `M(X) < ∞`, then `Y(ω) = X(χ ω)` is a current in `ℝ^P`.  If `ω_j → 0` in `𝒟^q(ℝ^P)`, eventually `|χ ω_j(x)| ≤ |ω_j(x)| ≤ δ` for every `x` (`Submission.fiw_ims_sc_converges_zero_small`), so `|Y(ω_j)| ≤ δ · M(X)` by `Submission.br_la_abs_apply_le_mul_mass`.
- **Calls**: `fiw_tb_ext_smul_testForm`, `fiw_ims_sc_converges_zero_small` (A.6), `fiw_tb_ext_covectorNorm_smul` (A.6), `br_la_abs_apply_le_mul_mass` (A.8)
- **Called by**: `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_apply_eq_of_eqOn` (L673)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.eq_near-a1` · issue #3238 · PR #3772 · candidate `366a98283620`
- **Statement and proof**: Locality of a current (cf. the support `spt T`, Simon Ch. 6, 2.11): if `Z` vanishes on every test form whose support misses `K`, and `η = ω` on an open `N ⊇ K`, then `Z(η) = Z(ω)`.  The difference `η - ω` vanishes on `N`, so its support lies in the closed set `ℝ^P ∖ N`, which misses `K`; by linearity `Z(η) - Z(ω) = Z(η - ω) = 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_mass_le_restrictDomain` (L13407)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.mass_le_restrict-a1` · issue #3303 · PR #3947 · candidate `35ad818f31a0`
- **Statement and proof**: **Mass does not drop under restriction near the support (Simon Ch. 6, 2.4–2.5).**  If `Z ∈ 𝒟_q(ℝ^P)` vanishes on every test form whose support misses a compact `K ⊆ U` (`U` open), then `M(Z) ≤ M(Z|_U)` for `Z|_U = Z.restrictDomain`.  With a cutoff `χ` (`0 ≤ χ ≤ 1`, `tsupport χ ⊆ U`, `χ = 1` on an open `N ⊇ K`), every `ω` admissible for `M(Z)` gives the form `χ ω ∈ 𝒟^q(U)`, admissible for `M(Z|_U)` as `|χ ω| = χ |ω| ≤ 1`, and `χ ω = ω` on `N`, so `Z(ω) = Z(χ ω) = Z|_U(χ ω) ≤ M(Z|_U)`.
- **Calls**: `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_covectorNorm_smul` (A.6), `fiw_tb_ext_apply_eq_of_eqOn`
- **Called by**: `fiw_tb_extend_to_univ`

#### `fiw_tb_ext_isIntegerMultiplicity` (L13437)

- `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1.im_extend-a1` · issue #3312 · PR #3927 · candidate `51907ff085ab`
- **Statement and proof**: **Integrality of the extension (Lemma B of the accepted proof of `fiw_tb_extend_to_univ`, the extension step of the formal proof of Simon Ch. 6, Theorem 7.2 **[corrected]**).**  Let `U` be open, `K ⊆ U` compact and `Z ∈ 𝒟_q(ℝ^P)` vanish on test forms whose support misses `K`.  If `Z|_U = τ(M, θ, ξ)` is integer multiplicity in `U`, then `Z = τ(M ∩ K, θ, ξ)` is integer multiplicity in `ℝ^P`.  As `spt Z|_U ⊆ K` (`fiw_tb_ext_support_subset`), `H^q(M ∖ K) = 0` (`lpf_rectifiable_support_null`), so `(M ∩ K, θ, ξ)` is a rectifiable triple whose tangent spaces are those of `(M, θ)` (`br_weightedTangent_congr`).  For `χ ∈ C_c^∞(U)` with `χ = 1` on an open `N ⊇ K` (`fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`), `Z(ω) = Z|_U(χ ω) = ∫_M θ ⟨χ ω, ξ⟩ dH^q = ∫_{M ∩ K} θ ⟨ω, ξ⟩ dH^q`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), says "Lemma B of the extension step in the proof of Simon Ch. 6, Theorem 7.2". Simon's proof has no such lemma. "Lemma B" is a lemma of the accepted natural-language proof of the parent node `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1` (`fiw_tb_extend_to_univ`). That extension step is a step of the formal proof that Simon leaves implicit (see the entry `fiw_tb_extend_to_univ`).
- **Calls**: `fiw_tb_ext_support_subset` (A.9), `lpf_rectifiable_support_null` (A.4), `br_weightedTangent_congr` (A.3), `fiw_tb_ext_cutoff`, `fiw_tb_ext_smul_testForm`, `fiw_tb_ext_apply_eq_of_eqOn`
- **Called by**: `fiw_tb_extend_to_univ`

#### `fiw_tb_restrictDomain_mass_im` (L14684)

- `root.flat_iff_weak-a1.total_boundedness-a1.restrict_im-a1` · issue #2351 · PR #3878 · candidate `d0e028370d07`
- **Statement and proof**: Simon Ch. 6, 2.4, 2.16 and 3.1: the restriction `Y|_W ∈ 𝒟ₖ(W)` of `Y ∈ 𝒟ₖ(U)` to an open `W ⊆ U` has `M_W(Y|_W) ≤ M_U(Y)`, since every admissible form for `M_W` is admissible for `M_U`, and it is integer multiplicity when `Y` is: `Y|_W = τ(M ∩ W, θ, ξ)` for `Y = τ(M, θ, ξ)`.
- **Calls**: `fiw_tb_ri_restrictDomain_mass_le`, `br_restrictDomain_isIntegerMultiplicity` (A.9)
- **Called by**: `fiw_tb_finite_net`

#### `fiw_tb_ri_restrictDomain_mass_le` (L13348)

- `root.flat_iff_weak-a1.total_boundedness-a1.restrict_im-a1.mass_le-a1` · issue #3214 · PR #3699 · candidate `c666a7bc5b72`
- **Statement and proof**: Simon Ch. 6, 2.4–2.5 and 2.16: restricting `Y ∈ 𝒟ₖ(U)` to a smaller domain `W ⊆ U` does not increase mass, `M(Y|_W) ≤ M(Y)`.  Every `ω` admissible for `M_W(Y|_W)`, regarded as the test form `ιω` on `U` with the same underlying form, is admissible for `M_U(Y)`, and `Y|_W(ω) = Y(ιω)`.  `W` need not be open.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_restrictDomain_mass_im`

#### `fiw_tb_top_dim_approx` (L69167)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1` · issue #2384 · PR #4931 · candidate `9cc90cbe2d04`
- **Statement and proof**: **Top-dimensional approximation by a lattice chain (Simon Ch. 6, proof of 5.1, (27)–(37) with `Q := X`, `R := 0`).**  An integer multiplicity `X ∈ 𝒟ₙ(ℝⁿ)` (`n = m + 1`) with `M(X), M(∂X) < ∞` has an integer `L¹` density `u`: `X(ω) = ∫ u ω(e)`, `∫ |u| = M(X)` and `u = 0` a.e. off `spt X`. Integer medians `β_F` of `u` on the cubes `F ∈ 𝓛ₙ(ρ)` give the lattice chain `Pc = ∑ β_F [[F]]`, integer multiplicity with density `v = β_F` on `F`.  `S = X − Pc` is integer multiplicity (LC) and `M(S) ≤ ∫ |u − v| = ∑_F ∫_F |u − β_F| ≤ ∑_F ρ⁻ⁿ ∫_F ∫_F |u(x) − u(y)| ≤ c ρ M(∂X)` by the translation estimate `∫ |u(· + h) − u| ≤ ‖h‖ M(∂X)`.  A cube with `β_F ≠ 0` meets `{u ≠ 0}` in positive measure, hence meets `spt X`, and has diameter `√n ρ`.
- **Calls**: `fiw_tb_tda_poincare_sum`, `fiw_tb_tda_density`, `fiw_tb_rectifiable_support_null`, `fiw_tb_tda_lattice_cubes`, `fiw_tb_tda_integer_median`, `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_sub_mass`, `fiw_tb_translation_estimate`
- **Called by**: `fiw_tb_finite_net`

#### `fiw_tb_tda_poincare_sum` (L14520)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1` · issue #3284 · PR #4567 · candidate `314f515e2ee4`
- **Statement and proof**: Summed Poincaré bound over the top-dimensional lattice cubes of `ℝⁿ`, `n = m + 1`, with `c = (2√n)ⁿ √n`.  A cube lies in the closed ball of radius `√n ρ` about any of its points, so summing over the a.e. partition into cubes bounds the left side by `ρ⁻ⁿ ∫⁻ₓ ∫⁻_{B(x, √n ρ)} |u x - u y|`.  The translation estimate bounds this double integral by `√n ρ Λ L(B(0, √n ρ))`, and `L(B(0, r)) ≤ (2r)ⁿ`.
- **Calls**: `fiw_tb_tda_lattice_cubes`, `fiw_tb_tda_ps_translation_ball`, `fiw_tb_tda_ps_ball_volume_le`
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_tda_lattice_cubes` (L13969)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_cubes-a1` · issue #3229 · PR #3985 · candidate `890c3df1bb86`
- **Statement and proof**: Top-dimensional lattice cubes in `ℝⁿ`, `n = m + 1`, `ρ > 0`.  The only order embedding `Fin n ↪o Fin n` is the identity, so `latticeFace ρ F` is the closed cube `ρ (F.1 + [0, 1]ⁿ)`: it is closed, has volume `ρⁿ` and diameter at most `√n ρ`.  The hyperplanes `{xᵢ = ρ k}` are null, the cubes cover `ℝⁿ` and two distinct cubes only meet inside these hyperplanes, so lower integrals and integrals of integrable functions split as sums over the cubes.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_lattice_chain`, `fiw_tb_tda_poincare_sum`, `fiw_tb_top_dim_approx`

#### `fiw_tb_tda_ps_translation_ball` (L13893)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.translation_ball-a1` · issue #3651 · PR #4410 · candidate `77269f38dfbf`
- **Statement and proof**: A translation estimate `∫ |u(x + h) − u(x)| dx ≤ ‖h‖ Λ` bounds the double integral over `r`-balls: `∫_x ∫_{closedBall(x, r)} |u(x) − u(y)| dy dx ≤ r Λ |closedBall(0, r)|`. Substituting `y = x + h` turns the inner integral into `∫ 1_B(h) |u(x + h) − u(x)| dh` with `B = closedBall(0, r)`; Tonelli swaps the integrals, and on `B` the hypothesis and `‖h‖ ≤ r` bound the inner `x`-integral by `r Λ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_poincare_sum`

#### `fiw_tb_tda_ps_ball_volume_le` (L13943)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.poincare_sum-a1.ball_volume-a1` · issue #3660 · PR #4316 · candidate `a5b46600e539`
- **Statement and proof**: Box bound for the volume of a Euclidean ball, used in `fiw_tb_tda_poincare_sum`: `closedBall(0, r) ⊆ [-r, r]ⁿ`, hence `Lⁿ(closedBall(0, r)) ≤ (2r)ⁿ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_poincare_sum`

#### `fiw_tb_tda_density` (L13500)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density-a1` · issue #3220 · PR #3807 · candidate `dedd6091ba85`
- **Statement and proof**: Integer `L¹` density of a top-dimensional integer multiplicity current (Simon Ch. 6, proof of 5.1, (27)–(28)).  Let `X ∈ 𝒟ₙ(ℝⁿ)` be integer multiplicity with `M(X) < ∞` such that (H) every representation `X = τ(M, θ, ξ)` has `M(X) = ∫_M θ dHⁿ` and `Hⁿ(M ∖ spt X) = 0`.  Then `X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` for a Borel integer-valued `u ∈ L¹(ℝⁿ)` with `∫ |u| = M(X)` and `u = 0` a.e. off `spt X`.  With `Δ = dx¹ ∧ ⋯ ∧ dxⁿ`, every `n`-covector is `α = α(e) Δ` and `Δ(τ) = ±1` for orthonormal `τ`, so `⟨ω, ξ⟩ = ω_e s` with `s = ⟨Δ, ξ⟩ = ±1` `Hⁿ`-a.e. on `M`; `u` is a Borel integer-valued version of `1_{M'} θ s`, `M' ⊆ M` a measurable core of `M`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_rectifiable_support_null` (L14642)

- `root.flat_iff_weak-a1.total_boundedness-a1.support_null-a1` · issue #2343 · PR #3216 · candidate `590fa7737e34`
- **Statement and proof**: **A rectifiable representation lives on the support (preliminary (G2) of the accepted proof of `fiw_total_boundedness`, the formal version of Simon Ch. 6, proof of 7.2, (1)–(3) **[corrected]**).** Under the mass formula `M_W(T) = ∫_{M ∩ W} θ dHⁿ` (MF), `T = τ(M, θ, ξ)` has `Hⁿ(M ∖ spt T) = 0`. Let `V = U ∩ Z`, `Z` the zero region of `T`.  An admissible form for `M_V(T)` is supported in `V ⊆ Z`, which misses `spt T = U ∖ Z`, so `T` kills it (`fiw_tb_apply_eq_zero_of_disjoint_support`): `M_V(T) = 0`, and `∫_{M ∩ V} θ dHⁿ = 0` by MF.  For compact `K ⊆ U`, `θ` is integrable on `M ∩ K`, hence a.e.-measurable, and positive on `M`, so `Hⁿ(M ∩ V ∩ K) = 0`.  The compact sets `F i ∩ closedBall 0 j` (`F i ⊆ U` closed, `⋃ i, F i = U`) cover `M ∩ V ⊇ M ∖ spt T`.
- **Correction**: the Lean doc comment, kept byte-identical (§9), says "(Simon Ch. 6, proof of 7.2, (G2))". Simon's proof of 7.2 (pp. 171–172) is labelled only (1)–(5). (G2) is preliminary (G2) of the accepted natural-language proof of the parent node `root.flat_iff_weak-a1.total_boundedness-a1` (`fiw_total_boundedness`).
- **Calls**: `fiw_tb_apply_eq_zero_of_disjoint_support`
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_tda_integer_median` (L13877)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1` · issue #3222 · PR #4891 · candidate `9aeb32700cfa`
- **Statement and proof**: **Integer medians** (Simon Ch. 6, proof of 5.1, (31) and (35), on an arbitrary measure space).  If `μ(F) = a > 0` and `u` is measurable, integer-valued and integrable on `F`, some integer `β` has `|β| a ≤ 2 ∫_F |u|`, `β ≠ 0 → μ(F ∩ {u ≠ 0}) ≠ 0` and `∫_F |u - β| ≤ a⁻¹ ∫_F ∫_F |u(x) - u(y)| dμ(y) dμ(x)`.  Take an integer median `β`, i.e. `μ(F ∩ {u ≤ β}) ≥ a/2` and `μ(F ∩ {u ≥ β}) ≥ a/2` (`fiw_tb_tda_im_median_exists`).  The first two estimates hold for every median (`fiw_tb_tda_im_median_bounds`).  A median minimizes `c ↦ ∫_F |u - c|` (`fiw_tb_tda_im_median_minimizes`), so comparing with the mean `c = a⁻¹ ∫_F u` (`fiw_tb_tda_im_mean_deviation`) gives the third.
- **Calls**: `fiw_tb_tda_im_median_exists`, `fiw_tb_tda_im_median_bounds`, `fiw_tb_tda_im_median_minimizes`, `fiw_tb_tda_im_mean_deviation`
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_tda_im_median_exists` (L13637)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_exists-a1` · issue #3875 · PR #4565 · candidate `4fe6eeba5edf`
- **Statement and proof**: An integer median of an integer-valued function on a set of positive finite measure (Simon Ch. 6, proof of 5.1, (31): the choice of `β_F`).  With `A k = F ∩ {u ≤ k}`, `μ (A k)` increases to `μ F = a` as `k → ∞` and decreases to `0` as `k → -∞` (continuity of `μ` from below and from above), so there is a least integer `β` with `μ (A β) ≥ a/2`.  Then `μ (A (β - 1)) < a/2`, and since `u` is integer-valued, `F ⊆ A (β - 1) ∪ (F ∩ {β ≤ u})`, which forces `μ (F ∩ {β ≤ u}) ≥ a/2`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_integer_median`

#### `fiw_tb_tda_im_median_bounds` (L13710)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_bounds-a1` · issue #3884 · PR #4848 · candidate `4e72b5fdaf9e`
- **Statement and proof**: **Size and support bounds for a median** (Simon Ch. 6, 5.1, (31) and (35)).  Let `c` be a median of a measurable `u` on a measurable `F`: both `F ∩ {u ≤ c}` and `F ∩ {c ≤ u}` have measure at least `a / 2`, where `a > 0`.  Then `|c| a ≤ 2 ∫_F |u| dμ`, and if `c ≠ 0` then `u` is not `μ`-a.e. zero on `F`.  On the half-measure set `S = F ∩ {c ≤ u}` (if `c ≥ 0`) or `S = F ∩ {u ≤ c}` (if `c < 0`) one has `|c| ≤ |u|`, and `u ≠ 0` when `c ≠ 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_integer_median`

#### `fiw_tb_tda_im_median_minimizes` (L13748)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.median_minimizes-a1` · issue #3887 · PR #4587 · candidate `b7b7a81541f2`
- **Statement and proof**: Median minimization: if `c₀` is a median of `u` on `F` (each of `F ∩ {u ≤ c₀}` and `F ∩ {u ≥ c₀}` has measure at least `a / 2`, where `μ F = a`), then `c₀` minimizes `c ↦ ∫_F |u - c| dμ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_integer_median`

#### `fiw_tb_tda_im_mean_deviation` (L13834)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.integer_median-a1.mean_deviation-a1` · issue #3896 · PR #4618 · candidate `130b23e22587`
- **Statement and proof**: **Mean deviation bound** (the comparison of `u` with its mean `ū = a⁻¹ ∫_F u dμ` on `F`, `μ(F) = a`, in the integer-median step that feeds the Poincaré inequality, Simon Ch. 6, (32)). For each `x`, `u(x) − ū = a⁻¹ ∫_F (u(x) − u(y)) dμ(y)`, so `|u(x) − ū| ≤ a⁻¹ ∫_F |u(x) − u(y)| dμ(y)`; integrating over `x ∈ F` gives `∫_F |u − ū| dμ ≤ a⁻¹ ∫_F ∫_F |u(x) − u(y)| dμ(y) dμ(x)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_integer_median`

#### `fiw_tb_tda_lattice_chain` (L14320)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_chain-a1` · issue #3256 · PR #4127 · candidate `81167a2ae0e1`
- **Statement and proof**: **Top-dimensional lattice chains** (Simon Ch. 6, proof of 5.1, (29) and (34), in `ℝⁿ` with `n = m + 1`).  If `β_F ∈ ℤ` and `∑_F |β_F| ρⁿ < ∞`, let `v = ∑_F β_F 1_{F̊}`, i.e. `v(x) = β(⌊x/ρ⌋, id)` when no coordinate of `x` lies in `ρℤ` and `v(x) = 0` otherwise. Then `v` is integrable and integer-valued, `v = β_F` a.e. on each closed cube `F`, and `v` is locally constant where it is nonzero.  The current `Pc(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` of `fiw_tb_tda_density_current` is `∑_F β_F [[F]]` (split the integral over the cubes with `fiw_tb_tda_lattice_cubes`) and is integer multiplicity by `fiw_tb_tda_locally_constant_im`.
- **Calls**: `fiw_tb_tda_lattice_cubes`, `fiw_tb_tda_density_current`, `fiw_tb_tda_locally_constant_im`
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_tda_density_current` (L14110)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density_current-a1` · issue #3245 · PR #3763 · candidate `70c43b4108de`
- **Statement and proof**: Simon Ch. 6, (2.7) with `μ = Lⁿ` (`n = m + 1`): an integrable density `v` on `ℝⁿ` defines the top-dimensional current `ω ↦ ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` in `𝒟ₙ(ℝⁿ)`.  Since `‖eᵢ‖ = 1`, `|⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩| ≤ ‖ω(x)‖`, so the integrand is dominated by `(sup ‖ω‖)·|v|`; linearity is `integral_add`/`integral_const_mul`, and for a null sequence `ω_j → 0` of test forms `sup ‖ω_j‖ → 0`, whence `|T(ω_j)| ≤ sup ‖ω_j‖ · ∫ |v| → 0`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_lattice_chain`

#### `fiw_tb_tda_locally_constant_im` (L14195)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.locally_constant_im-a1` · issue #3235 · PR #3747 · candidate `c25a422643ef`
- **Statement and proof**: A top-dimensional current with an integrable integer density `v` that is locally constant where it is nonzero is integer multiplicity (Simon Ch. 6, 3.1): `T(ω) = ∫ v ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ = τ(M, θ, ξ)(ω)` with `M = {v ≠ 0}` (open), `θ = |v|` and `ξ = ±e₁ ∧ ⋯ ∧ eₙ` according to the sign of `v`.  Near each `x ∈ M` the multiplicity `θ` is constant, so the weighted blow-up integrals of Ch. 3, 1.7 are eventually equal to `θ(x) ∫ f dLⁿ` and the approximate tangent space is `ℝⁿ = span(e)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_tda_lattice_chain`

#### `fiw_tb_tda_sub_mass` (L14458)

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.sub_mass-a1` · issue #3269 · PR #3774 · candidate `91ab1f42b165`
- **Statement and proof**: **Difference of two top-dimensional density currents.**  On `ℝⁿ` (`n = m + 1`) let `X(ω) = ∫ u ω_e dLⁿ` and `Pc(ω) = ∫ v ω_e dLⁿ` with `u, v ∈ L¹`, where `ω_e(x) = ⟨ω(x), e₁ ∧ ⋯ ∧ eₙ⟩`.  Then `X − Pc` is a current `S` with `M(S) ≤ ∫ |u − v| dLⁿ`. In top degree the Euclidean coefficient norm (Simon Ch. 6, 1.15 and Remark 2.6) of `ω(x)` is `|ω_e(x)|`, so every form admissible for the mass (2.4) has `|ω_e| ≤ 1` and `S(ω) = ∫ (u − v) ω_e dLⁿ ≤ ∫ |u − v| dLⁿ`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_translation_estimate` (L69113)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1` · issue #2375 · PR #4676 · candidate `026be1addf72`
- **Statement and proof**: Translation estimate (Step 2(b) of the accepted natural-language proof of `fiw_total_boundedness`, in the formal proof of Simon Ch. 6, 7.2; it gives the summed form of 5.1 (32)) **[corrected]**: if the top-dimensional current `X ∈ 𝒟ₙ(ℝⁿ)` is `X(ω) = ∫ u ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ` with `u ∈ L¹`, then `∫ |u(x + h) − u(x)| dx ≤ |h| M(∂X)` for every `h ∈ ℝⁿ`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Simon Ch. 6, proof of 7.2". The printed proof of 7.2 (pp. 171–172) has no translation estimate; it is Step 2(b) of the accepted proof of the parent node `root.flat_iff_weak-a1.total_boundedness-a1`, which treats the case `P = m + 1`.
- **Calls**: `fiw_tb_te_directional_form`, `fiw_tb_te_abs_apply_le_mul_mass`, `fiw_tb_te_translation_dual`, `fiw_tb_te_l1_le_of_smooth_dual`
- **Called by**: `fiw_tb_top_dim_approx`

#### `fiw_tb_te_directional_form` (L15071)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.directional_form-a1` · issue #3226 · PR #3803 · candidate `31080f006414`
- **Statement and proof**: Steps 2(a)–(d) of the accepted natural-language proof of the translation estimate `fiw_tb_translation_estimate` **[corrected]**: for `φ ∈ C_c^∞(ℝⁿ)`, `n = m + 1`, and `h ∈ ℝⁿ`, the test `m`-form `ω = φ α` with `α = ∑ₖ (-1)ᵏ hₖ dx⁽ᵏ⁾`, where `dx⁽ᵏ⁾` is the wedge of the coordinate covectors `dxʲ`, `j ≠ k`, in increasing order (indices `0, …, m`), satisfies `|ω(x)| = ‖h‖ |φ(x)|` and `dω(x)(e₀, …, eₘ) = ∑ᵢ hᵢ ∂ᵢφ(x) = Dφ(x) h`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), says "Simon Ch. 6, proof of 7.2 (translation estimate)". The printed proof of 7.2 has no translation estimate; the source is Steps 2(a)–(d) of the accepted proof of `fiw_tb_translation_estimate`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_translation_estimate`

#### `fiw_tb_te_abs_apply_le_mul_mass` (L764)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.mass_bound-a1` · issue #3221 · PR #3686 · candidate `caf42bc49b2c`
- **Statement and proof**: Mass estimate (Simon Ch. 6, 2.4–2.5): if `M(Z) < ∞` and `|η(x)| ≤ c` everywhere (Euclidean coefficient norm) with `c > 0`, then `|Z(η)| ≤ c · M(Z)`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_translation_estimate`

#### `fiw_tb_te_translation_dual` (L15200)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.translation_dual-a1` · issue #3231 · PR #3957 · candidate `2cdc05826715`
- **Statement and proof**: Weak translation estimate: if `|∫ u · Dφ(h)| ≤ B` for every `C^∞` compactly supported `φ` with `|φ| ≤ 1`, then `|∫ (u(· + h) − u) · g| ≤ B` for every such `g`.  For `φ_t = g(· − t h)`, `F(t) = ∫ u(y) g(y − t h) dy` has `F'(t) = −∫ u(y) Dφ_t(y)(h) dy`, so `|F'| ≤ B`, and `F(1) − F(0) = ∫ (u(x + h) − u(x)) g(x) dx` by translation invariance.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_translation_estimate`

#### `fiw_tb_te_l1_le_of_smooth_dual` (L69096)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1` · issue #3237 · PR #4570 · candidate `58888e426fc3`
- **Statement and proof**: **`L¹` norm by duality with smooth test functions** (proof of the translation estimate, Step 4).  If `w : ℝⁿ → ℝ` is integrable and `∫ w g ≤ C` for every `C^∞` compactly supported `g` with `|g| ≤ 1`, then `∫ |w| ≤ C`.  Given `ε > 0`, inner regularity of the finite measure `|w| dx` gives disjoint compact sets `K₁, K₂`, approximating `{w > 0}` and `{w < 0}`, such that `∫ |w| < ∫ w g + ε` for every measurable `g` with `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`. Smooth Urysohn functions on disjoint thickenings of `K₁, K₂` give such a `g ∈ C_c^∞`, so `∫ |w| < C + ε`.
- **Calls**: `fiw_tb_te_l1d_compact_sign_approx`, `fiw_tb_te_l1d_smooth_sign_sep`
- **Called by**: `fiw_tb_translation_estimate`

#### `fiw_tb_te_l1d_compact_sign_approx` (L15330)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.compact_sign_approx-a1` · issue #3719 · PR #4412 · candidate `dd6b43de71c2`
- **Statement and proof**: Compact approximation of the sign of an integrable `w : ℝ^n → ℝ`: for `ε > 0` there are disjoint compact sets `K₁, K₂` such that every a.e.-strongly measurable `g` with `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂` satisfies `∫ |w| < ∫ w g + ε`. For a Borel representative `v` of `w`, the finite measure `ν = |v| dx` is inner regular, so there are compact `K₁ ⊆ {v > 0}` and `K₂ ⊆ {v < 0}` with `ν({v > 0} \ K₁), ν({v < 0} \ K₂) < ε/4`. Off `S = ({v > 0} \ K₁) ∪ ({v < 0} \ K₂)` we have `v g = |v|`, and on `S` we have `v g ≥ -|v|`, so `∫ |v| ≤ ∫ v g + 2 ν(S) < ∫ v g + ε`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_te_l1_le_of_smooth_dual`

#### `fiw_tb_te_l1d_smooth_sign_sep` (L15274)

- `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.smooth_sign_sep-a1` · issue #3704 · PR #4369 · candidate `2d57eebed04b`
- **Statement and proof**: Smooth `±1` separation of two disjoint compact sets `K₁, K₂ ⊆ ℝ^n`: a `C^∞` function `g : ℝ^n → ℝ` with compact support, `|g| ≤ 1`, `g = 1` on `K₁` and `g = -1` on `K₂`. `Disjoint.exists_thickenings` gives `δ > 0` with disjoint open thickenings `Vᵢ ⊇ Kᵢ`; the smooth Urysohn lemma `exists_contDiff_support_eq_eq_one_iff` gives `gᵢ : ℝ^n → [0, 1]` with `support gᵢ = Vᵢ` and `gᵢ = 1` on `Kᵢ`, compactly supported since `closure Vᵢ ⊆ cthickening δ Kᵢ`. At each point one of `g₁, g₂` vanishes, and `g = g₁ - g₂`.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_te_l1_le_of_smooth_dual`

#### `fiw_tb_lattice_coeff_finite` (L15005)

- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_coeff_finite-a1` · issue #2369 · PR #3065 · candidate `c9c7285ac3ad`
- **Statement and proof**: Simon Ch. 6, proof of 7.2 (p. 171, "only finitely many `P_1, …, P_N` currents `P` as in (2)" **[corrected]**): for `ρ > 0`, a bounded `Y ⊆ ℝ^N` and `A ∈ ℝ`, only finitely many integer coefficient families `β` have the face `F` inside `Y` and `|β_F| ≤ A` whenever `β_F ≠ 0`.
- **Correction**: the Lean doc comment, kept byte-identical as part of the accepted declaration text (§9), quotes "only finitely many currents `P` as in (2)"; the book prints "only finitely many `P_1, …, P_N` currents `P` as in (2)".
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_tb_finite_net`

#### `fiw_tb_lattice_chain_coeff` (L14985)

- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1` · issue #2364 · PR #4146 · candidate `5bfbfcbc2a75`
- **Statement and proof**: Simon Ch. 6, proof of 7.2, (2) (p. 171): every face `F` of a lattice chain `Pc = ∑_F β_F [[F]]` in `ℝ^N` with `β_F ≠ 0` lies in `spt Pc`, and `|β_F| ρ^{m+1} ≤ M(Pc)`.  If a point `x ∈ F` were outside `spt Pc`, then `Pc` would vanish on some open `W ∋ x`; the isolating form `ω` of `F` localized at `x` (`tsupport ω ⊆ W`, `[[G]](ω) = 0` for `G ≠ F`, `[[F]](ω) > 0`) would give `0 = Pc(ω) = β_F [[F]](ω) ≠ 0`.  The mass bound is `isoperimetric_lattice_chain_mass_ge`.
- **Calls**: `isoperimetric_lattice_chain_mass_ge` (A.7), `fiw_tb_lcc_local_isolating_form`
- **Called by**: `fiw_tb_finite_net`

#### `fiw_tb_lcc_local_isolating_form` (L14898)

- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1` · issue #3240 · PR #3926 · candidate `52bf7c0a0b80`
- **Statement and proof**: Local isolating form for a lattice face: near any point `x` of the face `F₀ = ρ (z + F_α)` and inside any open `W ∋ x` there is a test form `ω = (ψ φ) • dx^α` on `ℝ^N` with `tsupport ω ⊆ W`, `[[F]](ω) = 0` for every other face `F ≠ F₀` and `[[F₀]](ω) > 0`.
- **Calls**: `isoperimetric_lattice_face_cutoff` (A.7), `isoperimetric_coord_covector_eval` (A.7), `fiw_tb_lcc_face_integral_pos`
- **Called by**: `fiw_tb_lattice_chain_coeff`

#### `fiw_tb_lcc_face_integral_pos` (L14854)

- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.face_integral_pos-a1` · issue #3233 · PR #3716 · candidate `0f587a14d3c1`
- **Statement and proof**: A continuous `g ≥ 0` that is positive at a relative-interior point `p` of the face `latticeFace ρ F` (`ρ > 0`) has positive integral over the face: by `br_latticeFace_setIntegral_eq_cube` the integral is `∫_{[0,ρ]^n} g(ι(s)) ds`, the point `s₀ = (p_{α(j)} − ρ z_{α(j)})_j` lies in the open cube `(0,ρ)^n` with `ι(s₀) = p`, and `support (g ∘ ι) ∩ (0,ρ)^n` is open and nonempty, hence of positive Lebesgue measure.
- **Calls**: `br_latticeFace_setIntegral_eq_cube` (A.10)
- **Called by**: `fiw_tb_lcc_local_isolating_form`

#### `fiw_tb_flat_sub` (L15415)

- `root.flat_iff_weak-a1.total_boundedness-a1.flat_sub-a1` · issue #2403 · PR #3177 · candidate `9dc32d5162c1`
- **Statement and proof**: Difference of two integral flat decompositions (Simon Ch. 6, proof of 7.2): `R := R₁ − R₂` and `S := S₁ − S₂` are integer multiplicity (by the linear-combination hypothesis with `a = 1`, `b = −1`), `∂R + S = (∂R₁ + S₁) − (∂R₂ + S₂)`, and `M(R) + M(S) ≤ (M(R₁) + M(S₁)) + (M(R₂) + M(S₂))` by subadditivity of mass.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: `fiw_total_boundedness`

### A.12 Federer–Fleming 3.11 (§3.12): `federer_fleming_compactness` and its 0 further declarations

#### `federer_fleming_compactness` (L69482)

- `root.federer_fleming-a1` · issue #342 · PR #8802 · candidate `5abeab044087`
- **Statement and proof**: **Simon Ch. 6, Theorem 3.11 (p. 149)**, proved as in Remark 8.3(2) (p. 176): Lemma 2.15 gives a weakly convergent subsequence, 6.3 makes every `∂T_j` integer multiplicity, and 8.2 shows that the weak limit is integer multiplicity.
- **Calls**: `compactness_under_mass_bounds` (A.1), `boundary_rectifiability` (A.10), `integrality_of_weak_limits` (A.9)
- **Called by**: `main_theorem`

### A.13 Accepted but unused declarations (3)

These are not referenced by any proof (§6); they are kept so that their accepted interfaces are preserved.

#### `dph_hausdorff_product_formula` (L28324)

- `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1` · issue #5270 · PR #5552 · candidate `cdb962226fc8`
- **Statement and proof**: Product formula for Hausdorff measure on rectifiable sets (Federer 3.2.23), with `π(y₀, …, y_P) = (y₁, …, y_P)` and `Φ(s, x) = (s, x₁, …, x_P)`, so `{y : π y ∈ S} = Φ(ℝ × S)`: (a) if `Hᵐ(N) = 0` then `Hᵐ⁺¹(ℝ × N) = 0`; (b) if `A ⊆ ℝ^P` is `Hᵐ`-measurable and countably `m`-rectifiable, then `∫_{ℝ × A} g dHᵐ⁺¹ = ∫_ℝ ∫_A g(Φ(s, x)) dHᵐ(x) ds` for Borel `g ≥ 0`, i.e. `Hᵐ⁺¹ ⌞ (ℝ × A) = L¹ ⊗ Hᵐ ⌞ A`.  (a) is `iwl_cr_hp_cylinder_null`.  For (b), `A` is replaced by a Borel `A₀ ⊆ A` with `Hᵐ(A ∖ A₀) = 0`, which by (a) changes neither side.  Up to an `Hᵐ`-null set, `A₀` is the disjoint union of the Borel pieces `G p '' B p` with `G p` Lipschitz and injective on `B p` (`iwl_cr_hp_injective_pieces`); the formula holds on each piece (`iwl_cr_hp_piece_product`), and both sides are countably additive over the pieces, the cylinder over the remainder being `Hᵐ⁺¹`-null by (a).  The local finiteness of `Hᵐ ⌞ A` is not needed.
- **Calls**: `iwl_cr_hp_cylinder_null` (A.6), `iwl_cr_hp_injective_pieces` (A.6), `iwl_cr_hp_piece_product` (A.6)
- **Called by**: — (unused)

#### `iwl_imc_restriction_im` (L38058)

- `root.integrality_weak_limits-a1.im_closure-a1.restriction_im-a1` · issue #2825 · PR #3911 · candidate `5d533f06b26a`
- **Statement and proof**: **Restriction of an integer multiplicity current (Simon Ch. 6, 2.9 and 3.1).**  Assume the tangent comparison principle (T) in `U`: for `Hᵏ ⌞ (M₁ ∩ M₂)`-a.e. `x`, every weighted approximate tangent space of `(M₁, θ₁)` at `x` is one of `(M₂, θ₂)`.  If `X = τ(M, θ, ξ)` is integer multiplicity and `S = X ⌞ A`, then `S = τ(M ∩ A, θ, ξ)` is integer multiplicity.  Both `(μ, v)` and `(Hᵏ ⌞ M, θ ξ)` represent `X`, so by uniqueness of the representation (2.7) `S(ω) = ∫_A θ ⟨ω, ξ⟩ d(Hᵏ ⌞ M)`.  The triple `(M ∩ A, θ, ξ)` inherits every condition from `(M, θ, ξ)`; for the orientation, (T) applied to `(M, θ)` and `(M ∩ A, θ)` transfers the tangent spaces.
- **Calls**: `iwl_imc_tau_measure_representation` (A.9), `slicing_representation_unique` (A.5)
- **Called by**: — (unused)

#### `fiw_tl_ald_closedBall_lebesgue_point` (L64049)

- `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.closed_ball_lebesgue_point-a1` · issue #3185 · PR #3625 · candidate `053bc37acaf4`
- **Statement and proof**: Lebesgue differentiation along closed balls: for a finite measure `ν` on `ℝ^P` and `g ∈ L¹(ν)`, `ν`-a.e. `x` satisfies `⨍_{B̄_s(x)} |g - g(x)| dν → 0` as `s → 0⁺`.  The closed balls `B̄_s(x)` form the Besicovitch Vitali family of `ν` (`ℝ^P` has the Besicovitch covering property), along which every locally integrable function has Lebesgue points `ν`-a.e.
- **Calls**: — (no accepted declaration; Mathlib and SimonGMT only)
- **Called by**: — (unused)

## Appendix B. SimonGMT constants used directly

Read from the compiled environment of `GMT.Ch06.Submission` (§9). For every constant of the module, including the auxiliary constants (`_proof_i`, `match_i`) that Lean generates for a declaration, which are attributed to that declaration, the program listed the constants of modules `Poincare.*` that occur in its type or value. Equation and congruence lemmas that Lean generated in this module for library or contract definitions (for example `Poincare.SimonGMT.Chapter06.GeometricCurrentOn.massOn.eq_1`) belong to no single declaration and are left out. The result: 164 distinct SimonGMT constants from 26 modules, used directly by 440 of the 692 theorems (the 691 children and `main_theorem`). Names are relative to `Poincare.SimonGMT.`; uses through other declarations are not repeated.

### B.1 Theorems (77)

| Theorem | Module | Declarations using it directly |
| --- | --- | --- |
| `Chapter01.measure_toOuterMeasure_isBorelRegular` | `Chapter01.Basic` | `rectifiability_weighted_tangent_ae` |
| `Chapter01.dimensionalDensityQuotient.eq_1` | `Chapter01.Densities` | `ind_md_ae_closedBall_growth`, `rectifiability_density_comparison` |
| `Chapter01.volume_closedBall_eq_densityNormalization` | `Chapter01.Densities` | `rectifiability_density_comparison` |
| `Chapter01.ae_dimensionalUpperDensity_eq_zero_outside` | `Chapter01.DensityComparison` | `rectifiability_weighted_tangent_ae` |
| `Chapter01.exists_fiveTimesCovering` | `Chapter01.DensityCovering` | `rectifiability_density_comparison` |
| `Chapter01.fiveTimesCovering_finite_remainder` | `Chapter01.DensityCovering` | `rectifiability_density_comparison` |
| `Chapter01.realUnitBallVolume.eq_1` | `Chapter01.Hausdorff` | `rectifiability_bf_cone_ratio_reduction` |
| `Chapter01.realUnitBallVolume_eq` | `Chapter01.Hausdorff` | `rectifiability_density_comparison` |
| `Chapter01.realUnitBallVolume_ne_top` | `Chapter01.Hausdorff` | `ind_md_ae_closedBall_growth`, `iwl_imc_normalized_lebesgue_points`, `iwl_positive_density`, `rectifiability_density_comparison`, `rectifiability_orientation`, `rectifiability_weighted_tangent_ae` |
| `Chapter01.realUnitBallVolume_pos` | `Chapter01.Hausdorff` | `ind_md_ae_closedBall_growth`, `iwl_imc_normalized_lebesgue_points`, `iwl_positive_density`, `rectifiability_density_comparison`, `rectifiability_orientation`, `rectifiability_weighted_tangent_ae` |
| `Chapter01.realUnitBallVolume_zero` | `Chapter01.Hausdorff` | `rectifiability_density_comparison` |
| `Chapter01.ae_radonCaratheodoryMeasure_iff` | `Chapter01.RadonCaratheodoryIntegral` | `rectifiability_mass_measure_representation` |
| `Chapter01.compactL1DualField_represents_test` | `Chapter01.RadonCaratheodoryIntegral` | `iwl_restriction_theory` |
| `Chapter01.integral_radonCaratheodoryMeasure` | `Chapter01.RadonCaratheodoryIntegral` | `rectifiability_mass_measure_representation` |
| `Chapter01.compactL1DualField_ae_eq_inter` | `Chapter01.RadonLocalDualField` | `iwl_restriction_theory` |
| `Chapter01.compactL1DualField_norm_le_one` | `Chapter01.RadonLocalDualField` | `iwl_restriction_theory` |
| `Chapter01.compactL1DualField_stronglyMeasurable` | `Chapter01.RadonLocalDualField` | `iwl_restriction_theory` |
| `Chapter01.simon_theorem_4_14_caratheodory` | `Chapter01.RadonPolarRepresentation` | `rectifiability_mass_measure_representation` |
| `Chapter01.simon_theorem_4_14_positive_envelope` | `Chapter01.VectorFunctionalEnvelope` | `iwl_restriction_theory`, `rectifiability_mass_measure_representation` |
| `Chapter01.vectorFunctionalEnvelopeMeasure_regular` | `Chapter01.VectorFunctionalEnvelope` | `iwl_restriction_theory`, `rectifiability_mass_measure_representation` |
| `Chapter01.simon_theorem_4_14_l1_extension` | `Chapter01.VectorFunctionalL1` | `iwl_restriction_theory` |
| `Chapter02.areaJacobianAt_eq_normDet` | `Chapter02.Area` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.area_image_criticalSet_eq_zero` | `Chapter02.AreaCritical` | `slicing_im_coarea_chart_cover` |
| `Chapter02.ae_fderivWithin_eq_of_lipschitz_extension` | `Chapter02.AreaDomain` | `lpf_raf_local_lipschitz_area` |
| `Chapter02.aemeasurable_weightedAreaFiberSum_lipschitzOn` | `Chapter02.AreaDomain` | `lpf_raf_local_lipschitz_area` |
| `Chapter02.areaJacobianWithin.eq_1` | `Chapter02.AreaDomain` | `lpf_raf_local_lipschitz_area` |
| `Chapter02.exists_lipschitz_extension_finiteDimensional` | `Chapter02.AreaDomain` | `lpf_raf_local_lipschitz_area` |
| `Chapter02.weighted_area_formula_lipschitzOn_fiberSum` | `Chapter02.AreaDomain` | `lpf_raf_local_lipschitz_area`, `lpf_wtc_chart_area_formula` |
| `Chapter02.measurePreserving_linearMap_normDet_smul` | `Chapter02.AreaLinearWeighted` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.area_image_compl_regularSet_eq_zero` | `Chapter02.AreaLipschitz` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.measurableSet_areaRegularSet` | `Chapter02.AreaLipschitz` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.simonAreaNormalization_pos` | `Chapter02.AreaNormalization` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure` | `Chapter02.AreaNormalization` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn` | `Chapter02.Lipschitz` | `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `iwl_cr_hp_injective_pieces`, `lpf_countably_rectifiable_c1_cover`, `lpf_locally_lipschitz_image`, `lpf_pi_source_charts`, `lpf_raf_chart_preimage_null`, `lpf_tde_chart_nondiff_image_null`, `rectifiability_bf_infinite_fibre_null`, `rectifiability_bf_projection_null_ae`, `rectifiability_mass_measure_abs_continuous`, `rectifiability_structure_projection`, `rectifiability_weighted_tangent_ae`, `slicing_im_coarea_chart_cover`, `slicing_im_coarea_chart_critical`, `slicing_im_coarea_pieces`, `slicing_im_st_cd_c1_cover`, `slicing_im_st_cd_c1c_singular_compression`, `slicing_im_st_chart_data`, `slicing_im_tg_cc_contDiff_range_chart_cover`, `slicing_im_tg_cc_lipschitz_range_c1_cover` |
| `Chapter02.integrableOn_image_iff_integrableOn_areaJacobian_smul` | `Chapter02.WeightedArea` | `rectifiability_weighted_tangent_ae` |
| `Chapter02.integral_area_formula_of_injective_derivative` | `Chapter02.WeightedArea` | `rectifiability_weighted_tangent_ae` |
| `Chapter03.CountablyRectifiable.congr_simp` | `Chapter03.Rectifiable` | `iwl_imc_lincomb_im` |
| `Chapter03.CountablyRectifiable.mono` | `Chapter03.Rectifiable` | `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_loc_triple_inter_open`, `br_restrictDomain_isIntegerMultiplicity`, `dmr_rectifiableTriple_inter`, `dph_hausdorff_product_formula`, `fiw_ims_combine`, `fiw_localization`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_tda_locally_constant_im`, `imc_isRectifiableTriple_of_eventually_mem`, `ind_ae_integer_multiplicity`, `ind_pi_restriction_open_im`, `iwl_cr_hausdorff_product_formula`, `iwl_cr_ip_product_triple`, `iwl_im_closure`, `iwl_im_patching`, `iwl_imc_lincomb_im`, `iwl_imc_restriction_im`, `iwl_localization`, `lpf_pi_chart_image_rectifiable`, `lpf_pi_im_of_chart_density`, `ltg_glue_triples`, `polyhedral_approx_open_truncation`, `rectifiability_bf_cone_density`, `rectifiability_mass_measure_rectifiable`, `rectifiability_structure_projection`, `rectifiability_weighted_tangent_ae` |
| `Chapter03.HasWeightedApproximateTangentSpaceAt.unique` | `Chapter03.Rectifiable` | `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `fiw_ims_orientation_sign`, `imc_isRectifiableTriple_of_eventually_mem`, `lpf_pi_im_of_chart_density`, `lpf_pi_source_charts`, `lpf_raf_chart_jacobian_ae`, `lpf_tangential_differential_exists`, `slicing_im_ll_tangent_dual_field`, `slicing_im_st_slice_geometry`, `slicing_im_tangential_gradient` |
| `Chapter03.PurelyUnrectifiable.mono` | `Chapter03.Rectifiable` | `rectifiability_bf_projection_null_ae`, `rectifiability_structure_projection` |
| `Chapter03.countablyRectifiable_iUnion` | `Chapter03.Rectifiable` | `fiw_ims_combine`, `imc_isRectifiableTriple_of_eventually_mem`, `iwl_im_patching`, `iwl_imc_lincomb_im`, `lpf_pi_chart_image_rectifiable`, `lpf_pi_im_of_chart_density`, `ltg_glue_triples` |
| `Chapter03.countablyRectifiable_of_measure_zero` | `Chapter03.Rectifiable` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `br_isIntegerMultiplicity_of_local`, `fiw_localization`, `fiw_tb_finite_net`, `imc_isRectifiableTriple_of_eventually_mem`, `integrality_of_weak_limits`, `iwl_cr_ip_product_triple`, `iwl_im_patching`, `rectifiability_mass_measure_rectifiable` |
| `Chapter03.countablyRectifiable_range` | `Chapter03.Rectifiable` | `br_lattice_chain_boundary_isIntegerMultiplicity`, `fiw_tb_tda_locally_constant_im`, `iwl_cr_ip_wt_plane_fubini`, `lpf_pi_chart_image_rectifiable`, `rectifiability_bf_cone_density` |
| `Chapter03.countablyRectifiable_sUnion` | `Chapter03.Rectifiable` | `br_lattice_chain_boundary_isIntegerMultiplicity`, `rectifiability_mass_measure_rectifiable` |
| `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` | `Chapter03.Rectifiable` | `rectifiability_mass_measure_rectifiable`, `rectifiability_structure_projection` |
| `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule` | `Chapter03.Rectifiable` | `iwl_cr_ip_wt_plane_fubini`, `rectifiability_orientation` |
| `Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover` | `Chapter03.Rectifiable` | `rectifiability_mass_measure_rectifiable` |
| `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule` | `Chapter03.Rectifiable` | `rectifiability_orientation` |
| `Chapter06.GeometricCurrentOn.boundary_affinePushforward` | `Chapter06.AffineCurrentPushforward` | `ind_rescaled_current` |
| `Chapter06.affinePullbackTestOn_coe` | `Chapter06.AffineCurrentPushforward` | `ind_rescaled_current` |
| `Chapter06.GeometricCurrentOn.isOpen_zeroRegion` | `Chapter06.CurrentLocalEquality` | `deformation_onto_skeleton`, `deformation_pushforward_homotopy`, `deformation_skeleton_polyhedral`, `dph_iprod_exists`, `dph_lipschitz_pushforward_im`, `dph_lpf_boundary`, `dph_lpf_cmp_core_estimate`, `dph_lpf_comparison`, `dph_lpf_existence`, `dph_lpf_linearity`, `dph_sh_affine_estimate`, `fiw_tb_rectifiable_support_null`, `ind_pi_pl_linear_pushforward_family`, `isoperimetric_theorem`, `iwl_cr_cone_integer_multiplicity`, `iwl_cr_support_lemmas`, `iwl_positive_density` |
| `Chapter06.GeometricCurrentOn.restrictDomain_apply` | `Chapter06.CurrentLocalEquality` | `br_local_finite_mass_extension`, `br_restrictDomain_isIntegerMultiplicity`, `fiw_tb_ext_isIntegerMultiplicity`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_extend_to_univ` |
| `Chapter06.GeometricCurrentOn.support.eq_1` | `Chapter06.CurrentLocalEquality` | `deformation_dilation_support`, `dmr_massMeasure_support_finite` |
| `Chapter06.GeometricCurrentOn.support_subset_domain` | `Chapter06.CurrentLocalEquality` | `ind_pi_projected_limit`, `iwl_smooth_pushforward`, `lpf_pi_local_finite_weight`, `lpf_pushforward_is_current` |
| `Chapter06.testFormOnInclusion_coe` | `Chapter06.CurrentLocalEquality` | `br_local_finite_mass_extension`, `fiw_tb_ext_mass_le_restrictDomain`, `ind_pi_localized_cycles` |
| `Chapter06.GeometricCurrentOn.boundary_apply` | `Chapter06.Currents` | `boundary_rectifiability`, `br_la_weaklyConvergesOn_of_flat_decomposition`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `br_top_dim_lattice_approximation`, `constancy_closed_kills_partial_derivatives`, `deformation_dilation_calculus`, `deformation_pushforward_homotopy`, `deformation_skeleton_polyhedral`, `dph_iprod_boundary`, `dph_smooth_homotopy`, `fiw_flat_to_weak`, `fiw_tb_flat_sub`, `fiw_tb_translation_estimate`, `iwl_cr_cone_boundary`, `iwl_cr_support_lemmas`, `iwl_cycle_reduction`, `iwl_localization`, `iwl_positive_density`, `iwl_sp_boundary_apply_eq_of_compatible`, `iwl_top_dim_integrality`, `polyhedral_approx_boundary_mass_cutoff`, `polyhedral_approx_flat_seq_tendsto`, `rectifiability_orientation`, `rpn_pullback_top_form_bound`, `slicing_im_ll_smooth_leibniz`, `slicing_mb_leibniz_bound`, `slicing_mb_pointwise`, `slicing_support_subset` |
| `Chapter06.GeometricCurrentOn.boundary_boundary` | `Chapter06.Currents` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_onto_skeleton`, `deformation_pushforward_homotopy`, `dph_lpf_boundary`, `integrality_of_weak_limits`, `iwl_positive_density` |
| `Chapter06.GeometricCurrentOn.continuous'` | `Chapter06.Currents` | `constancy_topForm_scalar_reduction`, `deformation_dilation_calculus`, `deformation_im_completeness`, `deformation_skeleton_polyhedral`, `deformation_telescope_limit`, `deformation_theorem`, `fiw_localization`, `fiw_tb_flat_sub`, `fiw_tb_tda_sub_mass`, `iwl_cr_cone_exists`, `iwl_cycle_reduction`, `iwl_positive_density`, `slicing_exists`, `slicing_im_td_current_tendsto` |
| `Chapter06.GeometricCurrentOn.ext` | `Chapter06.Currents` | `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `deformation_telescope_limit`, `dph_iprod_exists`, `dph_lpf_existence`, `fiw_im_lincomb`, `fiw_localization`, `fiw_tb_extend_to_univ`, `fiw_tb_finite_net`, `ind_pi_localized_cycles`, `ind_pi_ss_cycle_slice_boundary`, `ind_rescaled_current`, `integrality_of_weak_limits`, `isoperimetric_mass_eq_zero_iff`, `isoperimetric_theorem`, `iwl_cr_cone_boundary`, `iwl_cycle_reduction`, `iwl_positive_density`, `iwl_restriction_theory`, `slicing_im_testform_determining` |
| `Chapter06.GeometricCurrentOn.zero_apply` | `Chapter06.Currents` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_onto_skeleton`, `deformation_pushforward_homotopy`, `ind_pi_ss_cycle_slice_boundary`, `iwl_cycle_reduction`, `iwl_positive_density` |
| `Chapter06.WeaklyConvergesOn.boundary` | `Chapter06.Currents` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_onto_skeleton`, `integrality_of_weak_limits`, `iwl_cycle_reduction`, `iwl_positive_density` |
| `Chapter06.exteriorDerivative_isTestForm` | `Chapter06.Currents` | `rectifiability_orientation`, `slicing_im_lipschitz_leibniz` |
| `Chapter06.tsupport_exteriorDerivative_subset` | `Chapter06.Currents` | `boundary_rectifiability`, `br_lattice_chain_boundary_isIntegerMultiplicity`, `deformation_skeleton_polyhedral`, `fiw_flat_to_weak`, `fiw_tb_extend_to_univ`, `iwl_cr_support_lemmas`, `iwl_localization`, `rectifiability_orientation`, `slicing_im_slice_identity`, `slicing_mb_cutoff_defect_bound`, `slicing_mb_pointwise`, `slicing_support_subset` |
| `Chapter06.exteriorDerivative_apply` | `Chapter06.Forms` | `br_cube_stokes_lattice`, `br_top_dim_lattice_approximation`, `constancy_closed_kills_partial_derivatives`, `dph_iprod_slice_extDeriv`, `fiw_tb_te_directional_form`, `iwl_top_dim_integrality` |
| `Chapter06.covectorPullback_apply` | `Chapter06.FormsDuality` | `deformation_ipl_cc_chart_integral_representation` |
| `Chapter06.covectorPullback_wedgeCovectors` | `Chapter06.FormsDuality` | `rectifiability_orientation`, `rpn_covector_rotated_expansion` |
| `Chapter06.nVectorPushforward_simple` | `Chapter06.FormsDuality` | `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_ipl_tangential_pushforward_aestronglyMeasurable`, `lpf_pi_induced_orientation`, `lpf_pi_jacobian_local_bound`, `lpf_raf_jacobian_identity` |
| `Chapter06.simpleNVector_apply` | `Chapter06.FormsDuality` | `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_cc_pushforward_integrand_bound`, `deformation_skeleton_polyhedral`, `fiw_ims_frame_sign`, `fiw_ims_tt_unit_bound`, `fiw_localization`, `imc_im_density_limit`, `ind_ab_weighted_lebesgue_point`, `ind_ae_blowup_limit`, `ind_top_dim_integer_density`, `ind_top_orthonormal_frame_sign`, `iwl_localization`, `lpf_simple_nvector_algebra`, `polyhedral_approx_open_truncation`, `rectifiability_orientation` |
| `Chapter06.wedgeCovectors.eq_2` | `Chapter06.FormsDuality` | `rpn_pfd_extDeriv_sum_smul_wedge` |
| `Chapter06.wedgeCovectors_apply_det` | `Chapter06.FormsDuality` | `br_top_dim_lattice_approximation`, `cmb_covector_eq_sum_coord_smul_wedge`, `constancy_closed_kills_partial_derivatives`, `constancy_exists_topTestForm_integral_eq_one`, `constancy_topForm_scalar_reduction`, `deformation_ipl_cc_chart_orientation_sign`, `deformation_ipl_minor_weak_continuity`, `deformation_skeleton_polyhedral`, `fiw_im_mass_formula`, `fiw_localization`, `fiw_tb_tda_density`, `fiw_tb_te_directional_form`, `imc_im_density_limit`, `ind_top_dim_integer_density`, `ind_top_form_density_ae_unique`, `isoperimetric_coord_covector_eval`, `iwl_localization`, `iwl_restriction_theory`, `iwl_sp_sn_signed_simpleNVector_bound_ne_zero`, `iwl_top_dim_integrality`, `lpf_simple_nvector_algebra`, `ltg_simple_unit_rigidity`, `polyhedral_approx_pairing_wedge_kronecker`, `rectifiability_mass_measure_representation`, `rectifiability_orientation`, `rpn_pfd_wedge_cons_succAbove_sign`, `slicing_ru_covector_expansion`, `smr_ci_coord_sum_smul_wedge` |
| `Chapter06.GeometricCurrentOn.le_massOn` | `Chapter06.Mass` | `br_la_abs_apply_le_mul_mass`, `br_local_finite_mass_extension`, `br_top_dim_lattice_approximation`, `br_zd_dirac_massOn_ge`, `cmb_abs_apply_le_of_massOn_le`, `deformation_dilation_mass`, `deformation_im_completeness`, `deformation_onto_skeleton`, `deformation_skeleton_polyhedral`, `deformation_telescope_limit`, `deformation_theorem`, `fiw_im_mass_formula`, `fiw_ims_mass_bound`, `fiw_localization`, `fiw_tb_ext_mass_le_restrictDomain`, `fiw_tb_flat_sub`, `fiw_tb_ri_restrictDomain_mass_le`, `fiw_tb_te_abs_apply_le_mul_mass`, `ind_diagonal_weak_limit`, `ind_pi_localized_cycles`, `ind_pi_ss_restriction_massOn_le`, `ind_rs_massOn_dilation_le`, `isoperimetric_lattice_chain_mass_ge`, `iwl_cycle_reduction`, `iwl_localization`, `iwl_positive_density`, `iwl_restriction_theory`, `iwl_rl_massOn_iUnion_monotone`, `iwl_sp_massOn_le_of_compatible`, `iwl_top_dim_integrality`, `iwl_zero_dim_integrality`, `polyhedral_approx_boundary_mass_cutoff`, `polyhedral_approx_truncation_seq`, `smr_exists_continuous_extension`, `smr_ofReal_integral_le_massOn` |
| `Chapter06.GeometricCurrentOn.massOn_mono` | `Chapter06.Mass` | `br_boundary_isIntegerMultiplicity_of_finite_mass`, `deformation_mass_restriction`, `deformation_onto_skeleton`, `deformation_telescope_limit`, `dmr_massMeasure_support_finite`, `fiw_flat_cauchy_limit`, `fiw_localization`, `flat_convergence_iff_weak_convergence`, `imc_lintegral_coordNorm_le_mass`, `ind_md_mass_measure_balls`, `ind_md_mmb_massMeasure_balls`, `ind_pi_localized_cycles`, `ind_pi_pl_linear_pushforward_family`, `integrality_of_weak_limits`, `iwl_integer_density`, `iwl_positive_density`, `iwl_restriction_theory`, `iwl_restriction_weak_limit`, `iwl_rl_massOn_iUnion_monotone`, `iwl_rl_restriction_cutoff_estimate` |
| `Chapter06.WeaklyConvergesOn.massOn_le_liminf` | `Chapter06.Mass` | `cmb_tendsto_integral_of_weaklyConvergesOn`, `fiw_localization`, `integrality_of_weak_limits`, `iwl_localization`, `iwl_positive_density`, `iwl_restriction_weak_limit` |
| `Chapter06.covectorEuclideanNorm.eq_1` | `Chapter06.Mass` | `br_zd_dirac_massOn_ge`, `cmb_rb_abs_euclideanCovectorCoordinate_le`, `cmb_rb_covectorEuclideanNorm_add_le`, `dph_iprod_slice_covector_norm_le`, `fiw_ims_sc_covectorNorm_le_opNorm`, `isoperimetric_coord_covector_eval`, `iwl_zero_dim_integrality`, `rectifiability_mass_measure_representation`, `slicing_mb_wn_norm_sq_eq_onb_sum` |
| `Chapter06.covectorEuclideanNorm_neg` | `Chapter06.Mass` | `br_la_abs_apply_le_mul_mass`, `cmb_measureRepresentation_continuous_bound`, `deformation_im_completeness`, `deformation_onto_skeleton`, `fiw_localization`, `fiw_tb_flat_sub`, `fiw_tb_te_abs_apply_le_mul_mass`, `isoperimetric_lattice_chain_mass_ge`, `iwl_cycle_reduction`, `smr_ofReal_integral_le_massOn` |
| `Chapter06.covectorEuclideanNorm_nonneg` | `Chapter06.Mass` | `cmb_abs_apply_le_of_massOn_le`, `deformation_skeleton_polyhedral`, `dph_lpf_existence`, `dph_lpfex_bounded_compatible_form`, `dph_sh_affine_estimate`, `dph_sh_ib_covectorEuclideanNorm_contract_le`, `fiw_flat_to_weak`, `fiw_tb_ext_cutoff_current`, `fiw_tb_ext_mass_le_restrictDomain`, `ind_diagonal_weak_limit`, `ind_pi_ss_restriction_massOn_le`, `isoperimetric_abs_covector_apply_le`, `iwl_cr_cest_cutoff_radial_form`, `iwl_cr_cest_radial_coeff_bound`, `iwl_positive_density`, `iwl_restriction_theory`, `iwl_rl_restriction_cutoff_estimate`, `iwl_rl_testForm_smooth_cutoff`, `iwl_sp_covectorEuclideanNorm_pullback_le`, `iwl_sp_massOn_le_of_compatible`, `iwl_top_dim_integrality`, `polyhedral_approx_boundary_mass_cutoff`, `polyhedral_approx_open_truncation`, `rectifiability_orientation`, `slicing_mb_wedge_norm_le`, `smr_exists_continuous_extension` |
| `Chapter06.covectorEuclideanNorm_zero` | `Chapter06.Mass` | `br_la_testForm_covectorNorm_bounded`, `cmb_exists_weakly_convergent_subseq`, `deformation_im_completeness`, `dph_iprod_current_of_bound`, `dph_lpf_existence`, `dph_lpfex_bounded_compatible_form`, `dph_sh_affine_estimate`, `fiw_flat_to_weak`, `imc_im_density_limit`, `iwl_restriction_theory`, `polyhedral_approx_testForm_covectorNorm_bounded`, `rectifiability_mass_measure_representation`, `slicing_mb_cdb_grad_lintegral_le`, `smr_exists_continuous_extension` |

### B.2 Definitions, structures and constructors (57)

These are the vocabulary of currents, forms, rectifiable sets and Hausdorff measure; most of them occur in the contract's statement. The table gives the number of declarations that mention each directly.

| Constant | Kind | Module | Declarations |
| --- | --- | --- | --- |
| `Chapter01.IsCaratheodoryMeasurable` | def | `Chapter01.Basic` | 1 |
| `Chapter01.dimensionalDensityQuotient` | def | `Chapter01.Densities` | 7 |
| `Chapter01.dimensionalUpperDensity` | def | `Chapter01.Densities` | 12 |
| `Chapter01.realUnitBallVolume` | def | `Chapter01.Hausdorff` | 7 |
| `Chapter01.simonHausdorffMeasureReal` | def | `Chapter01.Hausdorff` | 1 |
| `Chapter01.radonCaratheodoryMeasure` | def | `Chapter01.RadonCaratheodoryIntegral` | 1 |
| `Chapter01.compactL1DualField` | def | `Chapter01.RadonLocalDualField` | 1 |
| `Chapter01.IsLocallyBoundedCcFunctional` | def | `Chapter01.VectorFunctionalEnvelope` | 2 |
| `Chapter01.vectorFunctionalEnvelopeMeasure` | def | `Chapter01.VectorFunctionalEnvelope` | 2 |
| `Chapter01.compactlySupportedToL1` | def | `Chapter01.VectorFunctionalL1` | 1 |
| `Chapter02.areaJacobianAt` | def | `Chapter02.Area` | 1 |
| `Chapter02.areaJacobianWithin` | def | `Chapter02.AreaDomain` | 2 |
| `Chapter02.areaRegularSet` | def | `Chapter02.AreaLipschitz` | 1 |
| `Chapter02.areaFiber` | def | `Chapter02.AreaMultiplicity` | 1 |
| `Chapter02.weightedAreaFiberSum` | def | `Chapter02.AreaMultiplicity` | 2 |
| `Chapter02.simonAreaNormalization` | def | `Chapter02.AreaNormalization` | 1 |
| `Chapter03.CountablyRectifiable` | def | `Chapter03.Rectifiable` | 35 |
| `Chapter03.HasApproximateTangentSpaceAt` | def | `Chapter03.Rectifiable` | 12 |
| `Chapter03.HasWeightedApproximateTangentSpaceAt` | def | `Chapter03.Rectifiable` | 105 |
| `Chapter03.PurelyUnrectifiable` | def | `Chapter03.Rectifiable` | 4 |
| `Chapter03.blowUpMap` | def | `Chapter03.Rectifiable` | 35 |
| `Chapter06.GeometricCurrentOn.affinePushforward` | def | `Chapter06.AffineCurrentPushforward` | 1 |
| `Chapter06.affinePullbackForm` | def | `Chapter06.AffineCurrentPushforward` | 1 |
| `Chapter06.affinePullbackTestOn` | def | `Chapter06.AffineCurrentPushforward` | 1 |
| `Chapter06.GeometricCurrentOn.VanishesOn` | def | `Chapter06.CurrentLocalEquality` | 22 |
| `Chapter06.GeometricCurrentOn.restrictDomain` | def | `Chapter06.CurrentLocalEquality` | 11 |
| `Chapter06.GeometricCurrentOn.support` | def | `Chapter06.CurrentLocalEquality` | 73 |
| `Chapter06.GeometricCurrentOn.zeroRegion` | def | `Chapter06.CurrentLocalEquality` | 31 |
| `Chapter06.testFormOnInclusion` | def | `Chapter06.CurrentLocalEquality` | 12 |
| `Chapter06.CurrentOn` | def | `Chapter06.Currents` | 193 |
| `Chapter06.GeometricCurrentOn` | inductive | `Chapter06.Currents` | 207 |
| `Chapter06.GeometricCurrentOn.boundary` | def | `Chapter06.Currents` | 83 |
| `Chapter06.GeometricCurrentOn.mk` | ctor | `Chapter06.Currents` | 29 |
| `Chapter06.GeometricCurrentOn.toCurrent` | def | `Chapter06.Currents` | 193 |
| `Chapter06.TestFormOn` | def | `Chapter06.Currents` | 233 |
| `Chapter06.TestFormOnConverges` | def | `Chapter06.Currents` | 36 |
| `Chapter06.WeaklyConvergesOn` | def | `Chapter06.Currents` | 38 |
| `Chapter06.exteriorDerivativeTestOn` | def | `Chapter06.Currents` | 41 |
| `Chapter06.instZeroGeometricCurrentOn` | def | `Chapter06.Currents` | 22 |
| `Chapter06.testFormOnSubmodule` | def | `Chapter06.Currents` | 7 |
| `Chapter06.Covector` | def | `Chapter06.Forms` | 345 |
| `Chapter06.DifferentialForm` | def | `Chapter06.Forms` | 249 |
| `Chapter06.IsSmoothForm` | def | `Chapter06.Forms` | 112 |
| `Chapter06.IsTestForm` | def | `Chapter06.Forms` | 126 |
| `Chapter06.exteriorDerivative` | def | `Chapter06.Forms` | 26 |
| `Chapter06.NVector` | def | `Chapter06.FormsDuality` | 180 |
| `Chapter06.SimonMultiIndex` | def | `Chapter06.FormsDuality` | 67 |
| `Chapter06.covectorPullback` | def | `Chapter06.FormsDuality` | 10 |
| `Chapter06.euclideanCovectorCoordinate` | def | `Chapter06.FormsDuality` | 32 |
| `Chapter06.euclideanNVectorCoordinate` | def | `Chapter06.FormsDuality` | 14 |
| `Chapter06.nVectorPushforward` | def | `Chapter06.FormsDuality` | 23 |
| `Chapter06.simpleNVector` | def | `Chapter06.FormsDuality` | 79 |
| `Chapter06.wedgeCovectors` | def | `Chapter06.FormsDuality` | 51 |
| `Chapter06.GeometricCurrentOn.mass` | def | `Chapter06.Mass` | 73 |
| `Chapter06.GeometricCurrentOn.massOn` | def | `Chapter06.Mass` | 87 |
| `Chapter06.covectorEuclideanNorm` | def | `Chapter06.Mass` | 118 |
| `Chapter06.massAdmissibleOn` | def | `Chapter06.Mass` | 60 |

### B.3 Auxiliary proof constants of SimonGMT definitions (30)

Lean stores the proof obligations of a definition as auxiliary theorems `<definition>._proof_i`; they occur wherever the definition is unfolded. Number of declarations mentioning each: `Chapter01.IsLocallyBoundedCcFunctional._proof_1` (2), `Chapter01.IsLocallyBoundedCcFunctional._proof_2` (2), `Chapter01.realUnitBallVolume._proof_1` (1), `Chapter06.IsSmoothForm._proof_1` (88), `Chapter06.NVector._proof_1` (158), `Chapter06.NVector._proof_2` (158), `Chapter06.NVector._proof_3` (160), `Chapter06.TestFormConverges._proof_2` (23), `Chapter06.TestFormConverges._proof_3` (23), `Chapter06.massAdmissibleOn._proof_1` (45), `Chapter06.massAdmissibleOn._proof_2` (45), `Chapter06.massAdmissibleOn._proof_3` (45), `Chapter06.nVectorPushforward._proof_1` (3), `Chapter06.simpleNVector._proof_1` (3), `Chapter06.simpleNVector._proof_2` (3), `Chapter06.simpleNVector._proof_3` (3), `Chapter06.testFormOnInclusion._proof_1` (11), `Chapter06.testFormOnInclusion._proof_2` (11), `Chapter06.testFormOnInclusion._proof_3` (11), `Chapter06.testFormSubmodule._proof_4` (197), `Chapter06.testFormSubmodule._proof_5` (197), `Chapter06.testFormSubmodule._proof_6` (197), `Chapter06.wedgeCovectors._proof_1` (2), `Chapter06.wedgeCovectors._proof_10` (2), `Chapter06.wedgeCovectors._proof_2` (2), `Chapter06.wedgeCovectors._proof_3` (2), `Chapter06.wedgeCovectors._proof_4` (2), `Chapter06.wedgeCovectors._proof_5` (2), `Chapter06.wedgeCovectors._proof_6` (2), `Chapter06.wedgeCovectors._proof_9` (2).


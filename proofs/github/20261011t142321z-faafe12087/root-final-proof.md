# Final proof of `GMT.Ch05.main_theorem` (root node)

Run `20261011T142321Z-faafe12087`, node `root`, issue
<https://github.com/ZhengyangZhang06/gmt-formalize/issues/4>.
Lean target `GMT/Ch05/Submission.lean`; frozen contract `GMT/Ch05/Contract.lean` at the frozen
commit `ea5607598f3133b40a13241f2e51517a8c6423cd` (Lean `v4.35.0-rc3`, Mathlib `25730c7c759d`,
`simongmt` package `2b3663083f3f`). Book: Simon, *Introduction to Geometric Measure Theory*,
Ch. 5, "The Allard Regularity Theorem" (`book/sources/chapter-05-source.txt`, sha256
`f2b3cadaebc7373e8a2768bdbd3b0cb0d3b357552bd9981b707c00a709ad9da8`; line numbers below refer to
this file). A public copy of the same text is the PDF
<https://web.stanford.edu/class/math285/ts-gmt>, which the prose audit also cites. I checked
its decompressed text streams: the title page reads "Introduction to Geometric Measure Theory,
Leon Simon, © Leon Simon 2014", and the table of contents lists §6 "Conical Approximation,
Extension of Allard's Th." on p. 124, as in the local source.

## 1. Statement

```lean
theorem main_theorem : TiltExcessHeightEstimate ∧ AffineApproximationLemma ∧
    LipschitzApproximationLemma ∧ LipschitzGraphCorollary ∧ HarmonicApproximationLemma ∧
    TiltExcessDecayTheorem ∧ AllardRegularityTheorem ∧ AllardRegularityAnyRadius ∧
    ConicalApproximationTheorem ∧ DensityOneRegularity ∧ DensityOneHigherRegularity ∧
    RegularSetOpenDense
```

Each conjunct is a closed proposition (`def … : Prop`) of the frozen contract, and
`main_theorem` has no hypotheses. The conjuncts formalize Simon Ch. 5:

* Lemma 2.1 (l. 193)
* Lemma 2.5 (l. 294)
* Lemma 2.6 (l. 377)
* Corollary 2.7 (l. 565)
* Lemma 3.1 (l. 592)
* Theorem 4.5 (l. 747)
* Theorem 5.2 (l. 1022)
* Remark 5.3 (l. 1035)
* Theorem 6.1 (l. 1157)
* the first and second assertions of Theorem 7.1 (l. 1312)
* Corollary 7.3 (l. 1378), with Definition 7.2 (l. 1368).

The contract's docstrings record the normalizations and errata that the frozen statements
already include. Examples are the mean-curvature term in the first inequality of 2.5, the
`ℝ^ℓ` target in 7.1, and the restriction of `Θ ≡ 1` to `spt V` in 7.1(ii). This proof uses the
statements exactly as frozen.

## 2. The Lean argument actually used

The proof of `main_theorem` (line 67601 of the final `Submission.lean`) is:

```lean
  exact ⟨Submission.tilt_excess_height_estimate,
    Submission.affine_approximation_lemma,
    Submission.lipschitz_approximation_lemma,
    Submission.lipschitz_graph_corollary,
    Submission.harmonic_approximation_lemma,
    Submission.tilt_excess_decay_theorem,
    Submission.allard_regularity_theorem,
    Submission.allard_regularity_any_radius,
    Submission.conical_approximation_theorem,
    Submission.density_one_regularity,
    Submission.density_one_higher_regularity,
    Submission.regular_set_open_dense⟩
```

`∧` is right-associative. So this twelve-component anonymous constructor elaborates to eleven
nested `And.intro`s, and component `i` must have type conjunct `i`. Each component is an
accepted child theorem whose declared type is exactly that conjunct. All names are in namespace
`GMT.Ch05`.

| # | Conjunct (book item) | Accepted child (declared type) | line |
|---|---|---|---|
| 1 | `TiltExcessHeightEstimate` (Lemma 2.1) | `Submission.tilt_excess_height_estimate : TiltExcessHeightEstimate` | 22528 |
| 2 | `AffineApproximationLemma` (Lemma 2.5) | `Submission.affine_approximation_lemma : AffineApproximationLemma` | 25151 |
| 3 | `LipschitzApproximationLemma` (Lemma 2.6) | `Submission.lipschitz_approximation_lemma : LipschitzApproximationLemma` | 29701 |
| 4 | `LipschitzGraphCorollary` (Cor. 2.7) | `Submission.lipschitz_graph_corollary : LipschitzGraphCorollary` | 31642 |
| 5 | `HarmonicApproximationLemma` (Lemma 3.1) | `Submission.harmonic_approximation_lemma : HarmonicApproximationLemma` | 29115 |
| 6 | `TiltExcessDecayTheorem` (Thm 4.5) | `Submission.tilt_excess_decay_theorem : TiltExcessDecayTheorem` | 29972 |
| 7 | `AllardRegularityTheorem` (Thm 5.2) | `Submission.allard_regularity_theorem : AllardRegularityTheorem` | 39913 |
| 8 | `AllardRegularityAnyRadius` (Rem. 5.3) | `Submission.allard_regularity_any_radius : AllardRegularityAnyRadius` | 51302 |
| 9 | `ConicalApproximationTheorem` (Thm 6.1) | `Submission.conical_approximation_theorem : ConicalApproximationTheorem` | 48197 |
| 10 | `DensityOneRegularity` (Thm 7.1, first assertion) | `Submission.density_one_regularity : DensityOneRegularity` | 67560 |
| 11 | `DensityOneHigherRegularity` (Thm 7.1, second assertion) | `Submission.density_one_higher_regularity : DensityOneHigherRegularity` | 64292 |
| 12 | `RegularSetOpenDense` (Cor. 7.3) | `Submission.regular_set_open_dense : RegularSetOpenDense` | 67536 |

The assembly uses no mathematics beyond `And.intro`. All of the mathematical content is in the
twelve accepted children, which are summarized in §4.

### Assumptions

* **No hypotheses beyond the frozen contract.** Lines 1–460 of `Contract.lean` (everything
  before `main_theorem`) appear byte-for-byte as lines 1–472 of `Submission.lean`. The only
  difference is twelve additional imports:
  * `Poincare.SimonGMT.Chapter02.WeightedArea` and `Poincare.SimonGMT.Chapter02.AreaLipschitz`
    from the pinned `simongmt` package;
  * ten Mathlib modules: `IntervalIntegral.AbsolutelyContinuousFun`,
    `Covering.BesicovitchVectorSpace`, `Covering.Differentiation`, `Covering.DensityTheorem`,
    `Function.Jacobian`, `Constructions.Polish.Basic`, `Calculus.FDeriv.Measurable`,
    `Measure.Lebesgue.VolumeOfBalls`, `BumpFunction.Normed` and `BumpFunction.InnerProduct`.

  I checked that these imports do not change how any frozen constant elaborates. I elaborated
  two scratch files with the pinned toolchain:
  * `Contract.lean` itself;
  * lines 1–472 of `Submission.lean`, followed by the contract's `main_theorem := by sorry`
    stub.

  For every constant in `GMT.Ch05` that each file adds, I compared the structural hashes
  (`Expr.hash`) of its type and value, and its universe parameters. All 80 constants are
  identical. They include all definitions, the structure `RectifiableVarifold` with its
  projections, the auxiliary declarations, and the statement of `main_theorem`. The comparator
  independently checks that every constant used by the statement is the same in `Contract` and
  `Submission` (§8).
* **Axioms:** only `propext`, `Classical.choice` and `Quot.sound` (§8).
* **No proof shortcuts:** the file contains no `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `extern`, `unsafe` or `opaque` declaration. No definition or assumption is
  changed.
* **Build settings (not mathematics).** All accepted declarations except
  `density_one_regularity` sit inside an
  `elaborate_without_info_trees … end_elaborate_without_info_trees` block. Lines 473–488 define
  the command and lines 493–67551 use it. `density_one_regularity` (lines 67553–67599) and
  `main_theorem` follow the block.
  * This command elaborates the enclosed commands as at top level, but it switches
    info-tree recording off (`withEnableInfoTree false`) and sets `Elab.async` to false.
  * It was introduced in the accepted checkpoint `14b7adf1a28b` of node `root.tilt_excess_decay-a1`
    (PR #5200), because the verification sandbox ran out of memory while Lean kept the info tree
    of every command.
  * Info trees are editor metadata only. Every enclosed declaration is still elaborated and
    added to the environment through the kernel.

  The file also has these settings:
  * `set_option linter.unusedTactic false` and `set_option linter.unreachableTactic false`.
    These two linters read info trees, so without info trees they would flag every tactic.
  * Local `set_option maxHeartbeats …` and `set_option maxSynthPendingDepth 3` on some
    declarations.
  * The core tactic `as_aux_lemma` inside the proof of Theorem 6.1, which stores finished
    subproofs as auxiliary theorems.

  None of these settings affects what the kernel checks. `main_theorem` is elaborated after the
  block, at top level. Its settings are the defaults except for the two linter options above,
  which stay off for the rest of the file.

## 3. This candidate: integration repair

**Rejected base.** The controller built this branch's base `14edad132e7d` by overlaying the
accepted child checkpoints (merges plus "re-merge declarations" commits). The comparator
rejected it with

```
GMT/Ch05/Submission.lean:18198:8: error:
  `GMT.Ch05.Submission.lipts_rectifiable_tangent_chart_cover` has already been declared
```

This is the only error (log line 495). The full log is `comparator.log` in the evidence
directory `cluster-state/verification/results/hoa63/20261013T133825Z-ch05-root-ds67xlr5`.
The first version of this document cited the run's `nodes/root/comparator-v1.log` for this
log. That file now holds the controller's later passing run on `dc91aaf9` (§8), so the
evidence directory is the record of the rejection.

**Repair.** Commit `26012c4ae4071cbf92436dec796a678f939b243e` changes only the Lean target
(2 insertions, 32 deletions):

1. **Removed the repeated chart cover.** I deleted lines 18190–18219 of `14edad13`, which hold
   the second copy of `lipts_rectifiable_tangent_chart_cover` (docstring and proof) and a
   repeated section note `/-! ### lip_approx_tangent_structure … -/`. This copy is identical to
   the first copy at lines 11153–11181 apart from one blank line. The first copy stays at line
   11161, before its user `lip_approx_tangent_structure` (line 12081). The controller's
   deduplication commit `59a90554` had already removed a third copy of the same block in the
   same way.
2. **Restored two accepted names.** In their accepted checkpoints, two declarations are written
   at the top level of namespace `GMT.Ch05` as `theorem Submission.X`:
   * `tdo_ods_integrableOn_norm_deriv`, checkpoint `07483dd7d591`, node
     `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1.ftc_bound-a1.deriv_norm_integrable-a1`;
   * `dohr_eb_elc2_averaged_hessian`, checkpoint `dbd206dd8e88`, node
     `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.averaged_hessian-a1`.

   The overlay placed them inside `namespace Submission` blocks (now lines 15237–15955 and
   56759–60682), so they were declared as `GMT.Ch05.Submission.Submission.X`. The two
   `linter.dupNamespace` warnings in the rejected run's `comparator.log` show this. I renamed
   them to `theorem tdo_ods_integrableOn_norm_deriv` (line 15790) and
   `theorem dohr_eb_elc2_averaged_hessian` (line 57501), which gives them their accepted names
   `GMT.Ch05.Submission.X` again.

   Each name has one call site, written `Submission.X …`: line 15908, and line 63840 in
   `dohr_eb_el_c2alpha_regularity`. Both call sites are inside `namespace GMT.Ch05.Submission`,
   where `Submission.X` resolves to `GMT.Ch05.Submission.X`.

No statement and no proof body was changed.

**Checks on the committed file.**

* After the contract preamble there are 562 declarations, all theorems:
  * `main_theorem`;
  * the 541 accepted DAG theorems (every accepted node below the root);
  * 20 helpers `liptsp_*` (lines 11183–12018). These belong to the accepted checkpoint
    `6c95c30c9b06` of node `root.lipschitz_approximation-a1.tangent_structure-a1` (PR #2840),
    whose `lip_approx_tangent_structure` uses them. All 20 are identical to that checkpoint, and
    this repair added none of them.
* Every accepted `lean_name` occurs exactly once, as `GMT.Ch05.Submission.<lean_name>`. There
  are no duplicate declarations and no `Submission.Submission.*` names. There is no repeated
  placeholder scaffold: `main_theorem` occurs once, the contract's `:= by sorry` stub was
  replaced, and there is no `sorry` anywhere.
* Each of the 541 accepted declarations, from its `theorem` line to the end of its proof, is
  textually identical to the declaration in its own accepted candidate commit (`candidate_commit`
  in `dag.json`). The comparison ignores trailing whitespace. It also treats
  `theorem Submission.X` at top level as equal to `theorem X` inside `namespace Submission`,
  since both declare `GMT.Ch05.Submission.X`.

### Revision of this document (prose only)

The first version of this document was committed in `dc91aaf9`. The controller's prose audit
`nodes/root/publication-prose-audit-v1.json` reviewed exactly that version: its `proof_blob`
`e3d4f77233cd` is the blob of this file in `dc91aaf9`. It did not accept that version. Its two
issues both concern the conical-approximation exposition in §4.9, and ask to:

1. state a support condition that makes the field `X(x) = x ∫_1^{1/τ} s^{n−1} g(sx) ds`
   admissible in `U`, and check it for the cutoffs used;
2. keep the dimensional constant in the bound for `∫_{B_1 ∖ B_λ} |x|^{1−n} |H| dμ`, and define
   the three annular integrals.

This revision rewrites §4.9 to follow the Lean proof step by step:

* Step 2 states the hypothesis `tsupport g ⊆ B_β(0) ⊆ U` of `conical_P1` and explains why it is
  needed.
* Steps 4 and 8 check it for the radial cutoffs (`β = 1 + ε`) and for the conical test
  functions (`β = b ≤ 1`).
* Step 7 defines `I_⊥`, `I_0` and `I_H` and gives the bounds proved in Lean:
  `(ω_n + 3) δL`, `(Λ + 3)(1 + nL)` and `δ(1 + (n − 1)L) ≤ nδL`.
* Step 9 absorbs these constants into the final `C`.

The revision also makes these changes:

* §6 and §7 list the Mathlib declarations that §4.9 now names.
* The header cites the public copy of the book.
* §3 points to the evidence directory for the rejected run's log.
* §8 describes this commit.

The audit record and the root's historical outline and plan are unchanged.
`GMT/Ch05/Submission.lean` and every other comparator input are byte-identical to `dc91aaf9`
and `26012c4a`.

## 4. Proof of each conjunct (the accepted children)

Each child has the following:

* its own reviewed natural-language proof, in the run's
  `nodes/root-<child>-a1/parent-supplied-natural-proof.md`, taken from the accepted
  decomposition `nodes/root/decomposition-v2.json`;
* its own tree of accepted descendants (541 accepted nodes in total, depth ≤ 6);
* a kernel-checked Lean proof that passed the comparator for its frozen type.

The summaries below describe the routes of the Lean proofs, as documented in the declarations'
docstrings and the accepted decomposition. Departures from the printed proofs are stated. "Uses"
lists the sibling conjuncts that the Lean proof references directly.

### 4.1 Lemma 2.1 — `tilt_excess_height_estimate` (issue #112, PR #3357, checkpoint `ed867b35a45e`)

**Claim.** `E(ξ, ρ/2, T) ≤ C ρ^{-n} ∫_{B_ρ(ξ)} (dist(x−ξ, T)/ρ)² dμ + C ρ^{2−n} ∫_{B_ρ(ξ)} |H|² dμ`
for every `n`-plane `T` with `B_ρ(ξ) ⊆ U`, with `C = 146·2^{n+1}`.

**Proof.**
1. If `∫|H|² = ∞` there is nothing to prove.
2. Otherwise, test the first-variation identity with the `C¹` field `X = ζ² p_{T⊥}(x − ξ)`. Here
   `ζ` is a cutoff that equals `1` on `B_{ρ/2}(ξ)` and vanishes off `B̆_ρ(ξ)`.
3. Wherever `T_x M` exists,
   `div_M X = ζ²|p_x − p_T|²/2 + 2ζ Dζ((p_x − p_T) p_{T⊥}(x − ξ))`
   (`divM_height_test_field_eq`).
4. Young's inequality absorbs the cross term, and
   `|x′||H| ≤ ρ^{-2}|x′|²/2 + ρ²|H|²/2` handles the curvature term.

**Uses:** none.

### 4.2 Lemma 2.5 — `affine_approximation_lemma` (issue #113, PR #4183, checkpoint `bee03434612e`)

**Claim.** This is the corrected statement of the contract.

**Proof.**
1. **Corrected monotonicity.** Monotonicity is used with the constant of Ch. 4, 4.2 read
   correctly: `κ = (p−n)/(4p)`, i.e. `Λ = 4pδ/(p−n)`. This gives a mass bound for every
   `δ ≤ 1/4`, and the pinched density bounds 2.4 for `δ` below a threshold depending only on
   `n` and `p`.
2. **First inequality, for every `n`-plane.** It follows from an `L¹` form of 2.1 ("Lemma A",
   `aal_l1_tilt_height`) together with Hölder's inequality (`aal_tilt_height_curvature_bound`).
3. **Large `δ`.** For `δ > δ₁`, the plane `ℝⁿ × {0}` has height `≤ σ`, and
   `1 ≤ δ₁^{-1/(2n+2)} δ^{1/(2n+2)}`.
4. **Small `δ`.** For `δ ≤ δ₁`, combine three ingredients: the `O(δ)` conical excess at each
   point, a maximal disjoint family of radius `δ^α σ/2` (`aal_packing_finite_net`), and a
   Chebyshev choice of a point `x₀` where `T_{x₀}M` exists. Together they give `T = T_{x₀}M`
   with height `≤ C δ^{1/(2n+2)} σ`, where `α = 1/(2n+2)` (`aal_height_bound_small_delta`).

**Uses:** none.

### 4.3 Lemma 2.6 — `lipschitz_approximation_lemma` (issue #114, PR #4438, checkpoint `f15e34061dc3`)

**Case 1.** The tilt of `T₀ = q(ℝⁿ × {0})` on `B_{σ₀}(0)` exceeds `β²L²σ₀ⁿ`. Then `f = 0`
works, by the pinched density bounds and the graph-measure bound.

**Case 2.** Otherwise:
1. The good set `G` is a Lipschitz graph over `T₀` with constant `2C₈βL`
   (`lip_approx_good_set_flat`, which uses Lemma 2.5).
2. `f` is a bounded Lipschitz extension of it (`lip_approx_bounded_extension`). Each coordinate
   is extended by McShane's construction (Mathlib `LipschitzOnWith.extend_real`), and the result
   is composed with the radial retraction onto `B_{R₀}(0)`, which is `1`-Lipschitz. This
   retraction replaces the book's componentwise truncation in (7).
3. The two error terms are bounded by a five-times covering estimate
   (`lip_approx_good_set_complement`) and by the monotonicity "hole" estimate
   (`lip_approx_graph_hole_measure`).

**Uses:** 2.5.

### 4.4 Corollary 2.7 — `lipschitz_graph_corollary` (issue #115, PR #4360, checkpoint `3f540aeba8ce`)

1. **Height cone.** `lgc_height_cone` applies 2.5 with `τ = βL`.
2. **Graph and extension.** `lgc_cone_graph_extension` shows that `spt V ∩ B_{σ₀/2}(0)` is a
   small-Lipschitz graph over `T₀`, and extends it to `f` with `Lip f ≤ L` and the sup bound.
3. **Forward inclusion.** This is immediate.
4. **Reverse inclusion.** Take a graph point over `Bⁿ_{σ₀/4}(0)` that is off `spt V`. Move it
   along the graph (intermediate value theorem) to a point at distance `d ∈ (0, σ₀/64]` from
   `spt V`. There, the hole estimate `lgc_hole_estimate` contradicts the tilt hypothesis on
   `B_{5d/2}(y)`.

**Uses:** 2.5.

### 4.5 Lemma 3.1 — `harmonic_approximation_lemma` (issue #116, PR #3958, checkpoint `6dd3d3a30cac`)

This follows the book's compactness argument.
1. Take a counterexample sequence for `δ = 1/(k+1)`, normalized by its means over `B`.
2. Three tools give a subsequence converging to some `w ∈ W^{1,2}(B)` with weak gradient `g`
   and `∫_B |g|² ≤ 1`:
   * the Poincaré inequality on balls (`w12_ball_poincare_inequality`);
   * Rellich's theorem (`w12_ball_rellich_compactness`);
   * weak compactness of `L²(B; ℝⁿ)`.
3. The defect bound `|∫ g_k · ∇ζ| ≤ sup|∇ζ|/(k+1)` makes `w` weakly harmonic.
4. Weyl's lemma (`w12_ball_weyl_lemma`) gives a harmonic `u₀` with `u₀ = w` a.e.
5. Then `u₀` plus the mean contradicts the choice of the sequence.

**Uses:** none.

### 4.6 Theorem 4.5 — `tilt_excess_decay_theorem` (issue #118, PR #5200, checkpoint `14b7adf1a28b`)

1. **Re-centre at `ξ`.** Use `ted_translate_varifold` with `δ″ = C_P δ`, where `C_P` comes from
   the mass bound of `ted_allard_density_bounds`, and with `ρ″ = σ/δ″`.
2. **Decay at the origin.** `ted_decay_at_origin` with contraction `η` runs through these steps:
   * reduce to `E(0, σ, T) ≤ Cδ^{1/(n+1)}`;
   * apply the Lipschitz approximation 2.6 with `L = 1`;
   * derive the weak equation for `f`, localized to `B_{σ/2}(0)`. Since `Lip f ≤ 1` is an
     operator-norm bound, `|Df|²_HS ≤ n` and `1 ≤ J_F ≤ 2^{n/2}`;
   * apply the harmonic approximation 3.1;
   * obtain affine approximation from the mean-value estimates 3.2–3.4;
   * bound the tilt by the height: by 2.1 if `p ≥ 2`, and by Lemma A plus a one-dimensional sup
     bound if `n = 1 < p < 2`.
3. **Choose `η`.** Pick `η` with `Cη² ≤ η^{2(1−n/p)}`. The curvature term scales as
   `K(ξ, ησ) ≤ η^{1−n/p} K(ξ, σ)`.

**Uses:** 2.1, 2.5, 2.6, 3.1.

### 4.7 Theorem 5.2 — `allard_regularity_theorem` (issue #119, PR #5480, checkpoint `4b5746e68ccd`)

1. Fix `δ₀(n, ℓ, p)` and `γ = δ₀/8192`.
2. Lemma 2.5 at `(0, 2δ₀ρ)` and the iteration of 4.5 give planes `S(ξ)` with tilt decay.
3. Corollary 2.7, with `T₀ = S(0)` and `L = min{L_c, L₀/√n}`, makes `spt V` a Lipschitz graph
   over `B_{δ₀ρ/4}(0)`. The factor `1/√n` turns the operator-norm bound into the
   Hilbert–Schmidt bound that the Campanato step needs.
4. The Campanato estimate (`allard52_graph_campanato`, `allard52_campanato_*`) makes the graph
   `C^{1,1−n/p}` with `Df(0) = 0`.
5. The conical excess at `0` bounds the height by `Cδ^{1/(2n+2)}|x|`, via monotonicity with the
   true `δ` and radial integration.
6. Lemma A then bounds the tilt at a fixed scale by `Cδ^{1/(n+1)}`. Restarting the decay
   iteration there gives the `C^{1,1−n/p}` estimate with rate `δ^{1/(2n+2)}`.

**Uses:** 2.5, 2.7, 4.5.

### 4.8 Remark 5.3 — `allard_regularity_any_radius` (issue #121, PR #5942, checkpoint `96627165d312`)

1. Theorem 5.2 at `(0, ρ)` gives `q₀, u₀`. With the mean value inequality this yields the
   thin-cone hypothesis of `any_radius_cone` around `T₀`.
2. Two results give local graphs of slope `≤ 1/24` at a fixed scale around every
   `y ∈ spt V ∩ B_{(1+3γ)ρ/4}(0)`:
   * pinching (`any_radius_pinching`), which applies Theorem 6.1 after dilation;
   * Theorem 5.2 applied to the translates `V − y` (`any_radius_rescaled_varifold`).
3. `any_radius_patching` glues these into a single graph over `T₀` on `B̆_{(1+7γ)ρ/8}(0)`.
4. `any_radius_graph_rate` gives the height, slope and Hölder bounds on `B_{γρ}(0)`, through
   conical excess, Lemma A, the 4.5 iteration and Campanato.

The sibling theorems enter as explicit hypotheses:
* `any_radius_pinching`, `any_radius_cone` and `any_radius_graph_rate` each take
  `ConicalApproximationTheorem` as a hypothesis;
* `any_radius_graph_rate` also takes `TiltExcessDecayTheorem`.

The proof of 5.3 supplies `Submission.conical_approximation_theorem` and
`Submission.tilt_excess_decay_theorem` for these hypotheses (lines 51420, 51447, 51450–51451).
It calls `Submission.allard_regularity_theorem` directly.

**Uses:** 5.2, 6.1, 4.5.

### 4.9 Theorem 6.1 — `conical_approximation_theorem` (issue #123, PR #3057, checkpoint `0f113e83c542`)

This section was rewritten in this revision (§3). It follows the Lean proof: the local lemmas
`conical_P1` (step 2 below, line 48199), `conical_P3` (step 3, line 48466), `conical_P2`
(step 4, line 48686), `conical_P4` (step 8, line 49255), the tangent-plane lemma `lemmaT`
(step 1, line 49747) and the final assembly (steps 0 and 5–12, from line 50462).

**Claim.** Fix `n ≥ 1`, `ℓ` and `Λ > 0`. Let `λ, θ, δ ∈ (0, 1/4)` and `|ξ| = 1 − θ`. Let
`U ⊇ B_1(0)` be open. Let `V` have generalized mean curvature `H` in `U`, and write
`μ = μ_V`. Assume `μ(B_1) ≤ Λ` and

* (H) `|μ(B_1)/ω_n − μ(B_λ)/(ω_n λⁿ)| + r^{1−n} ∫_{B_r} |H| dμ ≤ δ` for every `r ∈ [λ, 1]`.

Then for all `ρ ∈ (0, θ]` and `τ ∈ [2λ, 1]`:

* `μ(B_{(1−d)ρ}(ξ)) ≤ τ^{-n} μ(B_{τρ}(τξ)) + C d L`;
* `τ^{-n} μ(B_{τρ}(τξ)) ≤ μ(B_{(1+d)ρ}(ξ)) + C d L`.

Here `d = δ^{1/4}` and `L = |log λ|`. The constant `C` is given in step 9 and depends only on
`n` and `Λ`. All balls are closed, `B_r = B_r(0)`, and `ω_n = unitBallVolume n`.

**Notation.**

* `p_x = p_{T_x M}` (`V.tangentProj x`) and `x^⊥ = x − p_x x`.
* For every `x`, `p_x` is either `0` or an orthogonal projection, by the definition of
  `tangentProj`. Hence, for all `x`:
  * (i) `|x^⊥| ≤ |x|`;
  * (ii) `⟨x, x^⊥⟩ = |x^⊥|²`.
* `S` is Mathlib's smooth step `Real.smoothTransition`. It is `C^∞` and nondecreasing, takes
  values in `[0, 1]`, and has `S = 0` on `(−∞, 0]` and `S = 1` on `[1, ∞)`.
* `K_S = sup |S′|`. This is finite, because `S′` is continuous and vanishes outside `[0, 1]`.

0. **Consequences of the hypotheses.**
   * (a) The first summand in (H) is nonnegative. So `∫_{B_t} |H| dμ ≤ δ t^{n−1}` for every
     `t ∈ [λ, 1]`.
   * (b) Take `r = 1` in (H) and multiply by `ω_n`: `|μ(B_1) − λ^{-n} μ(B_λ)| ≤ ω_n δ`.
   * (c) `μ(B_r) < ∞` for `r ≤ 1`, because the multiplicity `θ_V` of `V = v(M, θ_V)` is
     integrable on compact subsets of `U` (`V.integrableOn_mult`). Also, `H` is `μ`-integrable
     on every compact subset of `U`; this is part of `HasGeneralizedMeanCurvature`.
   * (d) `L = log(1/λ) > log 4 > 1`.
   * (e) Geometry:
     * `|ξ| + ρ ≤ (1 − θ) + θ = 1`, so `B_ρ(ξ) ⊆ B_1`;
     * `|ξ| − ρ ≥ 1 − 2θ > 1/2`;
     * `B_{τρ}(τξ) ⊆ B_τ`;
     * `λ ≤ τ/2`.
1. **Tangent planes (Simon Ch. 3, 1.9).** `lemmaT` proves two facts:
   * `μ`-a.e., `p_x` is the orthogonal projection onto an `n`-plane (the weighted approximate
     tangent space);
   * `x ↦ p_x` is `μ`-a.e. strongly measurable.

   It uses these accepted lemmas, all declared before this theorem (lines 8241–14812):
   * `aetp_lusin_compact_exhaustion`, `aetp_upper_density_zero_ae`,
     `aetp_starProjection_range_continuousOn` and `aetp_weightedTangent_of_lusin_compact`,
     from the subtree of `tilt_excess_height_estimate`;
   * `rsod_blowUp_setIntegral_eq`, from the subtree of `regular_set_open_dense`.

   It also uses the `simongmt` results listed in §6.
2. **(P1) First variation of the radial field `X(x) = F(x) x`.**

   *Hypotheses.* `g ∈ C¹(ℝ^{n+ℓ})`, a radius `β` with `tsupport g ⊆ B_β(0)` and
   `B_β(0) ⊆ U`, and `τ ∈ (0, 1]`. Put `F(x) = ∫_1^{1/τ} s^{n−1} g(sx) ds`.

   *Conclusion.* Put `J(x) = ∫_1^{1/τ} sⁿ Dg(sx)(x^⊥) ds`. Then
   `∫ (τ^{-n} g(x/τ) − g(x)) dμ = ∫ J dμ − ∫ F(x) ⟨x, H(x)⟩ dμ`.

   *Proof.*
   * **Admissibility.** Let `|x| > β`. For every `s ∈ [1, 1/τ]`, `|sx| ≥ |x| > β`, so
     `g(sx) = 0` and `Dg(sx) = 0`. Hence `F` and `DF` vanish there, and
     `tsupport X ⊆ B_β(0) ⊆ U`. In particular `X` has compact support.
     Differentiation under the integral sign gives `F ∈ C¹` with
     `DF(x) = ∫_1^{1/τ} sⁿ Dg(sx) ds`; the `x`-derivative `sⁿ Dg(sx)` of the integrand is
     bounded by `τ^{-n} sup|Dg|`. So `X ∈ C¹_c` with `tsupport X ⊆ U`, and `X` is a valid test
     field in the definition of generalized mean curvature.

     The support hypothesis is needed. `X` vanishes outside the radial contractions
     `{y/s : g(y) ≠ 0, s ∈ [1, 1/τ]}` of the support of `g`, but in general not on them. These
     points need not lie in `U`, even when `tsupport g` is a compact subset of `U`, because `U`
     is not assumed to be invariant under radial contractions. The hypothesis
     `tsupport g ⊆ B_β(0) ⊆ U` keeps all of them inside `U`. Steps 4 and 8 check it for every
     test function used.
   * **FTC in `s`.** `d/ds [sⁿ g(sx)] = n s^{n−1} g(sx) + sⁿ Dg(sx) x`. Integrating over
     `[1, 1/τ]` gives `τ^{-n} g(x/τ) − g(x) = n F(x) + DF(x) x`.
   * **Divergence.** `DX(x) v = F(x) v + (DF(x) v) x`. Wherever `p_x` is the projection onto an
     `n`-plane, which holds `μ`-a.e. by step 1,
     `div_M X = trace(DX(x) ∘ p_x) = n F(x) + DF(x)(p_x x) = τ^{-n} g(x/τ) − g(x) − DF(x)(x^⊥)`.
   * **First variation.** `∫ div_M X dμ = −∫ ⟨X, H⟩ dμ = −∫ F(x) ⟨x, H(x)⟩ dμ`.
     * Every integrand vanishes off `B_β(0)`.
     * On `B_β(0)`, each integrand is either bounded (by (i) and the bounds on `g` and `Dg`) or
       at most a constant times `|H|`.
     * `μ(B_β(0)) < ∞` and `H ∈ L¹(B_β(0), μ)`.

     So all integrals are finite. Substituting the formula for `div_M X` gives the conclusion.
3. **(P3) Layer-cake bound (Ch. 4, 4.11).**

   *Hypotheses.*
   * `ν` is a measure with `ν(B_R) < ∞`;
   * `w ≥ 0` is `ν`-integrable on `B_R`;
   * `m ∈ ℕ` and `0 < a ≤ R`;
   * `∫_{B_t} w dν ≤ K t^m` for every `t ∈ [a, R]`.

   *Conclusion.* `∫_{B_R ∖ B_a} |x|^{-m} w dν ≤ K (1 + m log(R/a))`.

   *Proof.* For `a < |x| ≤ R`,
   `|x|^{-m} = R^{-m} + ∫_a^R m t^{-m−1} 1{|x| < t} dt`.
   Integrate this against `w dν` over `B_R ∖ B_a`, and exchange the integrals by Fubini. The
   integrand is bounded by `m a^{-m−1} w`, so Fubini applies. The result is at most
   `R^{-m} · K R^m + ∫_a^R m t^{-m−1} · K t^m dt = K (1 + m log(R/a))`.
4. **(P2) Monotonicity identity (Ch. 4, 3.18; the book's (1)–(2), ll. 1184–1190).**

   For `σ ∈ [λ, 1]`, put `I_⊥(σ) = ∫_{B_1 ∖ B_σ} |x^⊥|² |x|^{-n−2} dμ`. Then
   `|(μ(B_1) − σ^{-n} μ(B_σ)) − I_⊥(σ)| ≤ δ (2 + log σ^{-1})`.

   *Proof.*
   * **Support ball.** `B_1` is compact and `U` is open. So some closed `ε`-thickening of
     `B_1` lies in `U` (`IsCompact.exists_cthickening_subset_open`). This thickening is
     `B_{1+ε}(0)` (`cthickening_closedBall`). Put `R′ = 1 + ε`.
   * **Cutoffs.** Put `η_k = ε/(k+1)`, `γ_k(u) = 1 − S((u − 1)/η_k)` and `g_k(y) = γ_k(|y|)`.
     * `g_k` is `C¹`: it is `≡ 1` near `0`, and it is a composition of `C¹` maps away from `0`.
     * `g_k` takes values in `[0, 1]`, equals `1` on `B_1`, and equals `0` for
       `|y| ≥ 1 + η_k`.

     So `tsupport g_k ⊆ B_{1+η_k}(0) ⊆ B_{R′}(0) ⊆ U`, and step 2 applies with `β = R′` and
     `τ = σ`.
   * **Radial reduction.** Put `q(x) = |x^⊥|²/|x|²`, which lies in `[0, 1]` by (i). Let
     `x ≠ 0`. By (ii), `Dg_k(sx)(x^⊥) = γ_k′(s|x|) ⟨x, x^⊥⟩/|x| = q(x) Dg_k(sx)(x)`.

     Put `L_k(x) = σ^{-n} g_k(x/σ) − g_k(x)`. The FTC identity of step 2 gives
     `J_k = q (L_k − n F_k)`. So step 2 reads
     `∫ L_k dμ = ∫ q (L_k − n F_k) dμ − ∫ F_k ⟨x, H⟩ dμ`.
   * **Limit `k → ∞`.** `g_k → 1_{B_1}` pointwise. Hence `L_k → L_∞ = σ^{-n} 1_{B_σ} − 1_{B_1}`
     and `F_k → F_∞`, where:
     * `F_∞ = (σ^{-n} − 1)/n` on `B_σ`;
     * `F_∞ = (|x|^{-n} − 1)/n` on `B_1 ∖ B_σ`;
     * `F_∞ = 0` off `B_1`.

     All integrands vanish off `B_{R′}(0)`. On `B_{R′}(0)` they are bounded by constants
     (`|L_k| ≤ σ^{-n} + 1` and `|F_k| ≤ σ^{1−n}(σ^{-1} − 1)`), or by a constant times `|H|`. So
     dominated convergence applies.
   * **Evaluation.** `∫ L_∞ dμ = σ^{-n} μ(B_σ) − μ(B_1)`, and
     `q (L_∞ − n F_∞) = −1_{B_1 ∖ B_σ} |x^⊥|² |x|^{-n−2}`. Therefore
     `(μ(B_1) − σ^{-n} μ(B_σ)) − I_⊥(σ) = ∫ F_∞ ⟨x, H⟩ dμ`.
   * **Error.** `|F_∞ ⟨x, H⟩| ≤ σ^{1−n}|H|/n` on `B_σ`, and `≤ |x|^{1−n}|H|/n` on
     `B_1 ∖ B_σ`. Use 0(a) at `t = σ`, and step 3 with `w = |H|`, `m = n − 1`, `K = δ`,
     `a = σ`, `R = 1` (its hypothesis is 0(a) for `t ∈ [σ, 1]`). The error is at most
     `δ/n + δ(1 + (n − 1) log σ^{-1})/n ≤ δ (2 + log σ^{-1})`.
5. **Mass bounds from (3.18).**
   * (a) For `σ ∈ [λ, 1]`: `σ^{-n} μ(B_σ) ≤ μ(B_1) + δ (2 + log σ^{-1}) ≤ Λ + 3δL`. This uses
     `I_⊥(σ) ≥ 0`, `log σ^{-1} ≤ L` and `L > 1`.
   * (b) `I_⊥(λ) ≤ |μ(B_1) − λ^{-n} μ(B_λ)| + δ (2 + L) ≤ ω_n δ + 2δ + δL ≤ (ω_n + 3) δ L`.
     This uses 0(b) and `L > 1`.
6. **Trivial case `dL > 1`.** The constant `C` of step 9 satisfies `C ≥ Λ + 3`.
   * *First inequality.* `μ(B_{(1−d)ρ}(ξ)) ≤ μ(B_1) ≤ Λ ≤ C ≤ C d L`.
   * *Second inequality.* Use 5(a) with `σ = τ`, then `δ ≤ d` and `dL ≥ 1`:
     `τ^{-n} μ(B_{τρ}(τξ)) ≤ τ^{-n} μ(B_τ) ≤ Λ + 3δL ≤ Λ + 3dL ≤ (Λ + 3) dL ≤ C d L`.

   The remaining steps treat the case `dL ≤ 1`.
7. **The three annular integrals.** Since `dL ≤ 1`, also `δL ≤ dL ≤ 1`. So 5(a) gives
   `μ(B_t) ≤ (Λ + 3) tⁿ` for every `t ∈ [λ, 1]`. Define
   * `I_⊥ = ∫_{B_1 ∖ B_λ} |x^⊥|² |x|^{-n−2} dμ`,
   * `I_0 = ∫_{B_1 ∖ B_λ} |x|^{-n} dμ`,
   * `I_H = ∫_{B_1 ∖ B_λ} |x|^{1−n} |H| dμ`.

   Their bounds are:
   * `I_⊥ ≤ (ω_n + 3) δ L`, by 5(b);
   * `I_0 ≤ (Λ + 3)(1 + nL) ≤ (Λ + 3)(n + 1) L`, by step 3 with `w ≡ 1`, `m = n`,
     `K = Λ + 3`, `a = λ`, `R = 1`;
   * `I_H ≤ δ (1 + (n − 1) L) ≤ n δ L`, by step 3 with `w = |H|`, `m = n − 1`, `K = δ`,
     `a = λ`, `R = 1`, using 0(a).

   The bound for `I_H` is `nδL`, not `δL`. Step 3 gives only `δ(1 + (n − 1)L)`, which exceeds
   `δL` when `n ≥ 2`. This dimensional factor is the constant `C = C(n)` of the book's (3)
   (l. 1197), `∫_{B_1 ∖ B_λ} r^{1−n} |H| dμ ≤ C δ |log λ|`. Step 9 absorbs it into the final
   constant.
8. **(P4) Comparison for conical test functions.**

   *Hypotheses.*
   * `0 < λ ≤ τa`, `b ≤ 1`, `τ ∈ (0, 1]`, `ρ > 0`, `ε > 0` and `κ ≥ 0`;
   * `χ, φ : ℝ → [0, 1]` are `C¹`;
   * `∫_α^β |χ′| ≤ 2` for all `α ≤ β`;
   * `|φ′| ≤ κ/ρ`, and `φ(t) = 0` for `t ≥ 2ρ`;
   * `g(y) = χ(|y|) φ(|y − ξ|)` is `C¹`, and `g(y) ≠ 0` implies `a < |y| < b`.

   *Conclusion.*
   `|τ^{-n} ∫ g(x/τ) dμ − ∫ g dμ| ≤ (2 + 2κε) I_⊥ + (2κ/ε) I_0 + 4ρ I_H`.

   *Proof.*
   * **Support hypothesis of step 2.** `{g ≠ 0} ⊆ {a < |y| < b}`. So
     `tsupport g ⊆ {a ≤ |y| ≤ b} ⊆ B_b(0) ⊆ B_1(0) ⊆ U`, using `b ≤ 1`. Hence step 2 applies
     with `β = b`, and the left side equals `|∫ J dμ − ∫ F ⟨x, H⟩ dμ|`.
   * **Localization to `B_1 ∖ B_λ`.** Let `x ∉ B_1 ∖ B_λ`. Then for every `s ∈ [1, 1/τ)`,
     `sx ∉ tsupport g`, so `g(sx) = 0` and `Dg(sx) = 0`:
     * if `|x| > 1`, then `|sx| > 1 ≥ b`;
     * if `|x| ≤ λ`, then `|sx| < λ/τ ≤ a`.

     Hence `J(x) = F(x) = 0`. Now let `x ∈ B_1 ∖ B_λ`, and let `s ≥ 1` with `sx ∈ tsupport g`.
     Then `s|x| ≤ b ≤ 1`, so `sⁿ ≤ |x|^{-n}` and `s^{n−1} ≤ |x|^{1−n}`.
   * **Ray segments.** If `|sx − ξ| < 2ρ`, then `|s − ⟨x, ξ⟩/|x|²| < 2ρ/|x|`. So these `s` lie
     in an interval of length `4ρ/|x|`.
   * **Derivative.** Let `sx ∉ {0, ξ}`; only one `s` has `sx = ξ`, a null set. By (ii),
     `Dg(sx)(x^⊥) = χ′(s|x|) φ(|sx − ξ|) |x^⊥|²/|x| + χ(s|x|) φ′(|sx − ξ|) ⟨(sx − ξ)/|sx − ξ|, x^⊥⟩`.
     A zero of the nonnegative `C¹` function `φ` is a minimum. So `φ′(t) ≠ 0` forces
     `φ(t) ≠ 0`, and hence `t < 2ρ`. Therefore
     `|Dg(sx)(x^⊥)| ≤ |χ′(s|x|)| |x^⊥|²/|x| + (κ/ρ) |x^⊥| 1{|sx − ξ| < 2ρ}`.
   * **Integration in `s`.** The change of variables `s ↦ s|x|` and the total-variation bound
     give `∫_1^{1/τ} |χ′(s|x|)| ds ≤ 2/|x|`. Put `u = |x^⊥|/|x|`. With the previous two bullets
     and `sⁿ ≤ |x|^{-n}`,
     `|J(x)| ≤ |x|^{-n} ((|x^⊥|²/|x|)(2/|x|) + (κ/ρ)|x^⊥|(4ρ/|x|)) = |x|^{-n} (2u² + 4κu)`.
   * **Young's inequality.** `2u² + 4κu ≤ (2 + 2κε) u² + 2κ/ε`, since the difference is
     `2κ(εu − 1)²/ε ≥ 0`. So
     `|J(x)| ≤ (2 + 2κε) |x^⊥|² |x|^{-n−2} + (2κ/ε) |x|^{-n}`.
   * **Curvature term.** `0 ≤ g ≤ 1`, and `g(sx) ≠ 0` forces `|sx − ξ| < 2ρ`. So
     `|F(x)| ≤ |x|^{1−n} · 4ρ/|x| = 4ρ |x|^{-n}`, and
     `|F(x) ⟨x, H(x)⟩| ≤ 4ρ |x|^{1−n} |H(x)|`.

   Integrating the bounds for `J` and `F ⟨x, H⟩` over `B_1 ∖ B_λ` proves the conclusion.
9. **Constants.** Put `κ = K_S/d` and `ε = d^{-2}`. Then `κεδ = K_S d` and `2κ/ε = 2 K_S d`.
   Use step 7, `δ ≤ d`, `ρ ≤ θ < 1` and `L > 1`. The error term of step 8 satisfies
   `E := (2 + 2κε) I_⊥ + (2κ/ε) I_0 + 4ρ I_H ≤ C′ d L`, where
   `C′ = 2(ω_n + 3)(1 + K_S) + 2 K_S (Λ + 3)(n + 1) + 4n`.
   The three terms of `C′` bound the three terms of `E`, in order.

   The constant of the theorem is `C = Λ + 3 + C′`. It depends only on `n` and `Λ`. The frozen
   statement allows `C = C(n, ℓ, Λ)`.
10. **First inequality.** For `c > dρ`, put `φ_c(t) = S((c − t)/(dρ))`. Apply step 8 with
    `a = 1/2`, `b = |ξ| + ρ`, `χ ≡ 1` (total variation `0`) and `φ = φ_ρ`. The hypotheses
    hold:
    * `λ ≤ τ/2` and `b ≤ 1`, by 0(e);
    * `|φ_ρ′| ≤ K_S/(dρ) = κ/ρ`;
    * `φ_ρ = 0` on `[ρ, ∞) ⊇ [2ρ, ∞)`, and `φ_ρ = 1` on `(−∞, (1−d)ρ]`;
    * `y ↦ φ_ρ(|y − ξ|)` is `C¹`, being `≡ 1` near `ξ`;
    * if `g(y) ≠ 0`, then `|y − ξ| < ρ`, so `1/2 < |ξ| − ρ < |y| < b`.

    Since `φ_ρ(|x/τ − ξ|) ≤ 1_{B_{τρ}(τξ)}(x)`,
    `μ(B_{(1−d)ρ}(ξ)) ≤ ∫ φ_ρ(|x − ξ|) dμ ≤ τ^{-n} ∫ φ_ρ(|x/τ − ξ|) dμ + E ≤ τ^{-n} μ(B_{τρ}(τξ)) + C d L`.
11. **Second inequality.** For `k ≥ 1`, apply step 8 with `a = 1/2`, `b = |ξ| + ρ`,
    `φ = φ_{(1+d)ρ}` and `χ_k(u) = S(k(u − 1/2)) · S(k(b − u))`. The hypotheses hold:
    * `χ_k = f₁ f₂`, where `f₁` is nondecreasing, `f₂` is nonincreasing, and both take values
      in `[0, 1]`. So `|χ_k′| ≤ f₁′ − f₂′`, and `∫_α^β |χ_k′| ≤ 2`.
    * `χ_k(u) = 0` unless `1/2 < u < b`, and `χ_k(u) → 1_{(1/2, b)}(u)` as `k → ∞`.
    * `φ_{(1+d)ρ} = 1` on `[0, ρ]`, and `φ_{(1+d)ρ} = 0` on `[(1+d)ρ, ∞) ⊇ [2ρ, ∞)`, because
      `d < 1`.
    * `g_k(y) = χ_k(|y|) φ_{(1+d)ρ}(|y − ξ|)` is `C¹`. It vanishes on the open ball
      `B̆_{1/2}(0)`, hence near `0`. Away from `0`, `χ_k(|y|)` is a composition of `C¹` maps,
      and `φ_{(1+d)ρ}(|y − ξ|)` is `C¹` because it is `≡ 1` near `ξ`.

    Step 8 gives
    `τ^{-n} ∫ g_k(x/τ) dμ ≤ ∫ g_k dμ + E ≤ μ(B_{(1+d)ρ}(ξ) ∩ B_1) + C′ d L`.
    Let `k → ∞`, with dominating function `1_{B_1}`. Then
    `g_k(x/τ) → G(x) = 1{1/2 < |x/τ| < b} φ_{(1+d)ρ}(|x/τ − ξ|)`.

    Next, `G = 1` on `B_{τρ}(τξ) ∖ {p}`, where `p = τ(1 + ρ/|ξ|)ξ`. Indeed, let `y = x/τ` with
    `|y − ξ| ≤ ρ`. Then:
    * `|y| ≥ |ξ| − ρ > 1/2`;
    * `|y| ≤ |ξ| + ρ = b`, with equality only if `y − ξ` is the nonnegative multiple of `ξ` of
      length `ρ`, i.e. `y = (1 + ρ/|ξ|)ξ`;
    * `φ_{(1+d)ρ}(|y − ξ|) = 1`.

    Also `μ({p}) = 0`, since `μ ≪ Hⁿ` and `Hⁿ{p} = 0` for `n ≥ 1`. Hence
    `μ(B_{τρ}(τξ)) ≤ ∫ G dμ`, and
    `τ^{-n} μ(B_{τρ}(τξ)) ≤ μ(B_{(1+d)ρ}(ξ)) + C d L`.
12. **Extended reals.** All sets involved lie in `B_1`, and `μ(B_1) < ∞`. So the real
    inequalities give the frozen inequalities in `[0, ∞]`.

**Relation to the book.** The book's proof (ll. 1182–1300) combines (1)–(3) with first
variation for homogeneous degree-zero test functions, the co-area formula 2.9 of Ch. 3
(ll. 1229 and 1272) and Cauchy–Schwarz. The Lean proof uses the same estimates (1)–(3), as
steps 4, 5 and 7. In place of the homogeneous-function and co-area argument, it uses the direct
comparison of step 8: the radial field `F(x) x` of step 2, the test functions
`χ(|y|) φ(|y − ξ|)`, and Young's inequality. It does not use the co-area formula.

**Uses:** no sibling conjunct. The only accepted lemmas it uses are those of step 1.

### 4.10 Theorem 7.1, first assertion — `density_one_regularity` (issue #124, PR #5781, checkpoint `63173e03f8f2`)

1. Since `Θ = 1` and `H ∈ Lᵖ_loc`, there is a scale `r` at which the hypotheses 5.1 hold at
   `ξ` (`density_one_allard_scale`).
2. Theorem 5.2 applied to `V − ξ` (`exists_translated_varifold_allardHypotheses`) makes
   `(spt V − ξ) ∩ B_{γr}(0)` a rotated `C^{1,1−n/p}` graph.
3. On the open ball this graph is `graph_W u` for an open `W ∋ 0`
   (`exists_open_graph_domain_of_closedBall_graph`). The Hölder class follows from the finite
   scaled norm.
4. `Hⁿ(M ∆ spt V) = 0`, because `Θ ≥ 1` on `spt V`
   (`one_le_density_on_support_of_locallyLp`, `hausdorff_carrier_symmDiff_support_null`). This
   null set is transported by the isometry `x ↦ q⁻¹(x − ξ)`.

**Uses:** 5.2.

### 4.11 Theorem 7.1, second assertion — `density_one_higher_regularity` (issue #126, PR #5782, checkpoint `9c5cefba8e3e`)

1. Take `p = 2n/(1−α) > n`, so that `β = 1 − n/p = (1+α)/2`.
2. Theorem 5.2 at the density-one point gives a `C^{1,β}` graph.
3. Integrality of `θ` and monotonicity give `θ = 1`, `μ_V = Hⁿ ⌞ spt V` and `Θ = 1` on `spt V`
   near `ξ`. This uses the corrected monotonicity constant with an `ω_n`-normalized error.
4. Vertical test fields give the Euler–Lagrange (prescribed mean curvature) system for `u`.
5. Difference quotients and the Schauder interior estimate
   (`dohr_eb_schauder_interior_estimate`) bootstrap `u` to `C^{q+2,α}`.
6. Shrink to `ρ = min(r′, s)` and `W = {x ∈ B̆ⁿ_ρ(0) : |(x, u(x))| < ρ}`.

**Uses:** 5.2.

### 4.12 Corollary 7.3 — `regular_set_open_dense` (issue #128, PR #5582, checkpoint `7eeea44c01db`)

1. **`reg V` is relatively open.** `reg V = O ∩ spt V`, where `O` is the union of the regular
   balls (`rsod_regularSet_relOpen`). This uses the fact that `C¹` submanifolds restrict to open
   subsets.
2. **Every ball meets `reg V`.** Every open ball centred on `spt V` meets `reg V`
   (`rsod_regularSet_meets_ball`). Normalize `θ` by the least integer density `N` in the ball,
   then apply Theorem 5.2 at a point of density one.
3. **Closure.** `spt V = U ∩ spt μ_V` is closed in `U`, so `closure(reg V) ∩ U ⊆ spt V`.

**Uses:** 5.2.

### Dependency structure (extracted from the Lean source)

These are the direct references among the twelve conjunct theorems, read from the
comment-stripped source:

* 2.1, 2.5, 3.1 and 6.1 use none of the others;
* 2.6 ← 2.5;
* 2.7 ← 2.5;
* 4.5 ← 2.1, 2.5, 2.6, 3.1;
* 5.2 ← 2.5, 2.7, 4.5;
* 5.3 ← 5.2, 6.1, 4.5;
* 7.1(i) ← 5.2;
* 7.1(ii) ← 5.2;
* 7.3 ← 5.2.

This equals the `depends_on` lists of the accepted decomposition (`decomposition-v2.json`). The
graph is acyclic. No declaration refers to `main_theorem`, which is the last declaration of the
module, and Lean environments admit no forward references.

## 5. Historical decomposition versus lemmas actually used

* **Root history is unchanged.** The root's accepted outline
  (`nodes/root/natural-proof-source.md`: "follow the published proof" for each of the twelve
  conjuncts) and plan (`nodes/root/plan-source.md`: decompose along the conjuncts) are kept as
  history.
* **Decomposition history.** The first decomposition, `decomposition-v1.json`, was rejected with
  three required changes (`decomposition-review-receipt-v1.json`). The revision
  `decomposition-v2.json` was accepted (`decomposition-review-receipt-v2.json`). The final Lean
  route is exactly decomposition v2: twelve children, with the dependencies listed above.
* **Unused accepted lemmas.** Of the 541 accepted theorems, 533 are reachable from
  `main_theorem` in the source-level reference graph. The other 8 are accepted descendants of
  `density_one_higher_regularity` whose parents' final Lean proofs took other routes:
  * `dohr_translate_varifold` and its five children `dohr_tv_exists_translate`,
    `dohr_tv_weight_eq_map`, `dohr_tv_support_map_sub`, `dohr_tv_tangentProj_eq` and
    `dohr_tv_gmc_transfer`. The final proof of 7.1(ii) translates through
    `dohr_allard_graph_at_density_one` instead, which uses the accepted lemma
    `exists_translated_varifold_allardHypotheses`; 7.1(i) uses the same lemma.
  * `dohr_tp_weighted_tangent_of_lebesgue_point` and its child
    `dohr_tp_wtlp_ball_comparison_le`. Their parent `dohr_graph_tangent_planes` instead uses
    `dohr_tp_ae_weighted_tangent_of_growth`, `dohr_tp_graph_ball_growth`,
    `dohr_tp_graph_approx_tangent`, `dohr_tp_approx_tangent_affine_isometry` and
    `dohr_tp_projection_continuousOn`.

  They are kept unchanged, with their accepted names and types, to preserve the accepted child
  interfaces.
* **No root-level helper lemmas.** The root itself introduces no named helper lemma. The only
  root-level proof step is the anonymous constructor.

## 6. Library reuse provenance

All reused library results are existing, pinned declarations, used with their own proofs. None
of them is presented as new work.

* **Lean core:**
  * `And` (anonymous constructor, root step);
  * the tactic `as_aux_lemma` (child 6.1);
  * `Lean.Elab.Command.elabCommand`, `withEnableInfoTree` and the option `Elab.async`, used by
    the `elaborate_without_info_trees` command.
* **`simongmt`** (`Poincare.SimonGMT`, rev `2b3663083f3f`, from `lake-manifest.json`; `rg` finds
  no `sorry` and no `axiom` declaration in its sources):
  * Chapter 3:
    * `CountablyRectifiable` (used by the contract)
    * `HasApproximateTangentSpaceAt`
    * `HasWeightedApproximateTangentSpaceAt` and `HasWeightedApproximateTangentSpaceAt.unique`
    * `blowUpMap`
    * `regular_euclideanHausdorffMeasure_restrict_submodule`
  * Chapter 2:
    * `euclideanHausdorffMeasure_image_le_of_lipschitzOn`
    * `areaJacobianAt`, with `areaJacobianAt_nonneg`, `areaJacobianAt_eq_normDet` and
      `measurable_areaJacobianAt`
    * `areaRegularSet`, with `measurableSet_areaRegularSet` and
      `area_image_compl_regularSet_eq_zero`
    * `injective_area_formula_lipschitz`
    * `weighted_area_formula_lipschitz_injOn`
    * `integral_area_formula_of_injective_derivative`
    * `continuous_normDet`

  All of these are referenced by fully qualified name.
* **Mathlib** (rev `25730c7c`), for example:
  * Besicovitch differentiation: `Besicovitch.vitaliFamily`, `Besicovitch.ae_tendsto_rnDeriv`;
  * Vitali covering: `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`;
  * `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`;
  * Rademacher: `LipschitzWith.ae_differentiableAt`,
    `LipschitzOnWith.ae_differentiableWithinAt_of_mem`;
  * `lintegral_image_eq_lintegral_abs_deriv_mul`;
  * Lusin–Souslin: `MeasurableSet.image_of_continuousOn_injOn`;
  * `LipschitzOnWith.extend_real`;
  * `ContDiffBump`;
  * `InnerProductSpace.HarmonicOnNhd`;
  * `InnerProductSpace.volume_closedBall`;
  * `tendsto_integral_of_dominated_convergence`;
  * `intervalIntegral.integral_eq_sub_of_hasDerivAt`;
  * Fubini–Tonelli: `integral_prod`, `lintegral_prod`;
  * additionally named in §4.9 (Theorem 6.1):
    * the smooth step `Real.smoothTransition`, with its lemmas `contDiff`, `monotone`,
      `zero_of_nonpos`, `one_of_one_le`, `nonneg` and `le_one`;
    * `IsCompact.exists_cthickening_subset_open` and `cthickening_closedBall` (the ball
      `B_{1+ε}(0) ⊆ U`);
    * `hasFDerivAt_integral_of_dominated_of_fderiv_le` (differentiation under the integral sign
      in step 2);
    * `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` and
      `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`;
    * `MeasureTheory.integral_integral_swap` (Fubini in step 3);
    * `MeasureTheory.Measure.nullSingletonClass_hausdorff` (`Hⁿ{p} = 0` in step 11).
* **Proved in this run, not reused.** Several results are not in Mathlib or `simongmt`; they are
  proved by accepted nodes of this run:
  * the Poincaré inequality on balls (`w12_ball_poincare_inequality`);
  * Rellich compactness (`w12_ball_rellich_compactness`);
  * Weyl's lemma (`w12_ball_weyl_lemma`);
  * the Campanato estimates (`allard52_campanato_from_tilt`, `allard52_campanato_center_holder`,
    `allard52_campanato_ae_center`, `allard52_graph_campanato`, `any_radius_campanato`);
  * the Schauder interior estimate (`dohr_eb_schauder_interior_estimate`).

## 7. Reference use

`reference_use` (exactly one entry):

* **source:** `local-project`. Snapshot
  `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7`;
  `manifest.json` gives project `ea5607598f3133b40a13241f2e51517a8c6423cd` (the frozen commit)
  and mathlib `25730c7c759d108ef87ab70af2342a196760f79d` (the `lakefile.toml` pin).
* **Queries and findings** (paths relative to the snapshot):
  * `cmp project/GMT/Ch05/Submission.lean project/GMT/Ch05/Contract.lean`: identical. The
    snapshot's Submission is the 463-line byte copy of the contract, with
    `main_theorem := by sorry`.
  * `rg -n "theorem main_theorem" project`: 8 matches. These are the `Contract.lean` and
    `Submission.lean` stubs of Ch01, Ch02, Ch05 and Ch08. Ch05 has them at line 461 of both
    files. The snapshot contains no proof of the root.
  * `rg -c "TiltExcessHeightEstimate|…|RegularSetOpenDense"` (the twelve conjunct names):
    `project/GMT/Ch05/Contract.lean:14`, `project/GMT/Ch05/Submission.lean:14` and
    `project/GMT/Ch05/README.md:12`. Nowhere else.
  * `rg -l "tilt_excess_height_estimate|affine_approximation_lemma|…|regular_set_open_dense"`
    (the twelve child names): **no match**. Every child proof comes from this run's accepted
    checkpoints.
  * `rg -n "lipts_rectifiable_tangent_chart_cover|tdo_ods_integrableOn_norm_deriv|dohr_eb_elc2_averaged_hessian"`:
    **no match**. The three declarations touched by this repair exist only in this run's
    checkpoints.
  * `rg -n "elaborate_without_info_trees"`: **no match**. The command comes from the accepted
    checkpoint `14b7adf1a28b`.
  * `rg -l "withEnableInfoTree" mathlib/Mathlib`: `Tactic/DeriveCountable.lean` and
    `Tactic/DeriveEncodable.lean`. Mathlib's own command elaborators use the same core
    combinator.
  * Locations of the Mathlib items cited in §6:
    * `Analysis/Calculus/Rademacher.lean`: `LipschitzOnWith.ae_differentiableWithinAt_of_mem`
      (l. 361) and `LipschitzWith.ae_differentiableAt` (l. 385);
    * `MeasureTheory/Covering/Besicovitch.lean`: `Besicovitch.vitaliFamily` (l. 1021) and
      `ae_tendsto_rnDeriv` (l. 1078);
    * `MeasureTheory/Covering/Vitali.lean`:
      `exists_disjoint_subfamily_covering_enlargement_closedBall` (l. 158);
    * `MeasureTheory/Function/Jacobian.lean`:
      `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` (l. 255);
    * `MeasureTheory/Function/JacobianOneDim.lean`:
      `lintegral_image_eq_lintegral_abs_deriv_mul` (l. 44);
    * `MeasureTheory/Constructions/Polish/Basic.lean`:
      `MeasurableSet.image_of_continuousOn_injOn` (l. 821);
    * `Topology/MetricSpace/Lipschitz.lean`: `LipschitzOnWith.extend_real` (l. 308);
    * `Analysis/InnerProductSpace/Harmonic/Basic.lean`: `HarmonicAt` (l. 41) and
      `HarmonicOnNhd` (l. 48);
    * `MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`: `InnerProductSpace.volume_closedBall`
      (l. 354);
    * `MeasureTheory/Integral/DominatedConvergence.lean`:
      `tendsto_integral_of_dominated_convergence` (l. 57);
    * `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`:
      `integral_eq_sub_of_hasDerivAt` (l. 1148);
    * `Analysis/Calculus/BumpFunction/Basic.lean`: `ContDiffBump` (l. 70).
  * Locations of the Mathlib items added for §4.9:
    * `Analysis/SpecialFunctions/SmoothTransition.lean`: `def Real.smoothTransition` (l. 146),
      with `one_of_one_le` (l. 161), `zero_of_nonpos` (l. 168), `le_one` (l. 187), `nonneg`
      (l. 190), `contDiff` (l. 205) and `monotone` (l. 222);
    * `Topology/MetricSpace/Thickening.lean`: `IsCompact.exists_cthickening_subset_open`
      (l. 426);
    * `Analysis/Normed/Module/Ball/Pointwise.lean`: `cthickening_closedBall` (l. 318);
    * `Analysis/Calculus/ParametricIntegral.lean`:
      `hasFDerivAt_integral_of_dominated_of_fderiv_le` (l. 208);
    * `MeasureTheory/Integral/DominatedConvergence.lean`:
      `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` (l. 170) and
      `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` (l. 619);
    * `MeasureTheory/Integral/Prod.lean`: `integral_integral_swap` (l. 478);
    * `MeasureTheory/Measure/Hausdorff.lean`: `nullSingletonClass_hausdorff` (l. 615).
  * `rg -n "conical_approximation_theorem|conical_P1|conical_P2|conical_P3|conical_P4" project`:
    **no match**. `rg -n "ConicalApproximationTheorem" project` finds only the frozen definition
    (`Contract.lean` and `Submission.lean`, l. 391), the `main_theorem` stubs (l. 461) and the
    README row for Theorem 6.1 (`project/GMT/Ch05/README.md:26`). The proof of §4.9 comes from
    the accepted checkpoint `0f113e83c542`.
* **Compatibility.** Every cited declaration comes from the pinned Mathlib and `simongmt`
  revisions used by the build. The comparator's axiom check covers them.

**Mathematical citation (not a `reference_use` entry).** Simon, *Introduction to Geometric
Measure Theory* (© Leon Simon 2014), <https://web.stanford.edu/class/math285/ts-gmt>. This is
the public copy that the prose audit cites for equation (3) of §6. I checked its title page and
table of contents (see the header of this document). Line numbers in this document refer to the
local source text.

## 8. Verification

All results below are for the final Lean file `GMT/Ch05/Submission.lean` (67617 lines, sha256
`ac23060c847cd402dc25b50bffa9413fa16281a4dd0689304cc280d5b76aaeb6`, first committed in
`26012c4a`).

### Exact configured comparator: passed

* **Run.** `env -u HF_TOKEN HUMANIZE_NODE_ID=root … python3 verifier/gmt-compare.py
  --lean-target GMT/Ch05/Submission.lean … --frozen-commit
  ea5607598f3133b40a13241f2e51517a8c6423cd root`, on candidate
  `26012c4ae4071cbf92436dec796a678f939b243e` (tree `22d3ec3778bc`).
* **Output.** "GMT comparator: comparator and Lean kernel accepted GMT.Ch05.main_theorem",
  "Your solution is okay!", exit 0.
* **Checks.** `exit_zero`, `lean_kernel_accepted` and `final_marker` are all true, with no
  post-check failures.
* **Configuration.** Challenge `GMT.Ch05.Contract`; solution `GMT.Ch05.Submission`; theorem
  `GMT.Ch05.main_theorem`; permitted axioms `propext`, `Quot.sound` and `Classical.choice`.
* **Evidence.** `cluster-state/verification/results/hoa63/20261013T143228Z-ch05-root-jq_k7qwl`,
  verdict key `bdb024590ba7fbf13282b2ca2a07bf69ad51a5c54d69eacf7a550703383470de`. The log
  contains no error, no redeclaration and no `dupNamespace` diagnostic.
* **Later commits.** Two later commits change only this document, so no comparator input
  changes:
  * `dc91aaf9` added it;
  * the prose-only revision described in §3 revised it.

  Their Lean and Lake inputs are byte-identical to `26012c4a`, and the comparator's verdict key
  depends only on those inputs and the pinned verifier, so they have the same verdict key. The
  controller's run of the same comparator on `dc91aaf9` confirms this:
  `cluster-state/verification/results/hoa63/20261013T164526Z-ch05-root-tqevxcdb` has status
  `passed` with the same verdict key, reusing the evidence above ("identical inputs already
  passed every check"). Its log is the run's `nodes/root/comparator-v1.log`, and
  `nodes/root/isolated-comparator-result.json` records `passed: true` for candidate `dc91aaf9`.

### Child interfaces and axioms (scratch compile)

I made a scratch copy of the final file and compiled it with the pinned toolchain (`lean`
v4.35.0-rc3, with `LEAN_PATH` set to the pinned package builds). The copy adds the following
after `main_theorem`, inside `namespace GMT.Ch05`, which is the contract's scope at
`main_theorem`:

* 541 checks, one for each accepted DAG node below the root, each of the form
  `theorem _root_.ChildCheck.<lean_name> : (<lean_statement>) := by exact Submission.<lean_name>`.
  This is the comparator's own child-check form. Each `lean_statement` is the frozen one from
  `dag.json`, normalized by the verifier's `lean_contract.validate_lean_statement`.
* `#print axioms GMT.Ch05.main_theorem`.

Results:

* **Build.** Exit 0, no errors, no `sorry`.
* **Child checks.** 541/541 succeed: there is no diagnostic of any kind after line 67600. The
  only diagnostics in the whole file are 48 deprecation and style warnings inside child proofs.
* **Axioms.** `#print axioms` prints
  `'GMT.Ch05.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### Other checks

* **Contract constants.** All 80 `GMT.Ch05` constants of the contract preamble are identical
  under the contract's imports and the Submission's imports (§2).
* **Source checks.** Every accepted name is declared exactly once; there are no duplicates, no
  doubled namespace and no untracked helper added by the root; all 541 declarations are verbatim
  copies of their accepted checkpoints (§3).

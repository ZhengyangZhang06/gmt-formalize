# Final proof of `GMT.Ch05.main_theorem` (root node)

Run `20261011T142321Z-faafe12087`, node `root`, issue
<https://github.com/ZhengyangZhang06/gmt-formalize/issues/4>.
Lean target `GMT/Ch05/Submission.lean`; frozen contract `GMT/Ch05/Contract.lean` at the frozen
commit `ea5607598f3133b40a13241f2e51517a8c6423cd` (Lean `v4.35.0-rc3`, Mathlib `25730c7c759d`,
`simongmt` package `2b3663083f3f`). Book: Simon, *Introduction to Geometric Measure Theory*,
Ch. 5, "The Allard Regularity Theorem" (`book/sources/chapter-05-source.txt`, sha256
`f2b3cadaebc7373e8a2768bdbd3b0cb0d3b357552bd9981b707c00a709ad9da8`; line numbers below refer to
this file).

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

This is the only error. The log is `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root/comparator-v1.log`
and the evidence is
`cluster-state/verification/results/hoa63/20261013T133825Z-ch05-root-ds67xlr5`.

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
   56759–60682), so they were declared as `GMT.Ch05.Submission.Submission.X`. Lean's
   `linter.dupNamespace` warnings in `comparator-v1.log` show this. I renamed them to
   `theorem tdo_ods_integrableOn_norm_deriv` (line 15790) and
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

Write `μ = μ_V`, `p_x = p_{T_x M}`, `x^⊥ = x − p_x x`, `d = δ^{1/4}` and `L = |log λ|`.

1. **Tangent planes.** `p_x` is `μ`-a.e. the projection onto an `n`-plane, and it is `μ`-a.e.
   strongly measurable (Simon Ch. 3, 1.9, via the accepted `aetp_*` lemmas and
   `rsod_blowUp_setIntegral_eq`).
2. **Homogeneous first variation.** For `g ∈ C¹_c` and `τ ∈ (0, 1]`, use the field
   `X(x) = F(x)x` with `F(x) = ∫_1^{1/τ} s^{n−1} g(sx) ds`. This field is admissible. By the
   fundamental theorem of calculus in `s`,
   `div_M X = τ^{-n}g(x/τ) − g(x) − ∫_1^{1/τ} sⁿ Dg(sx)(x^⊥) ds` a.e.
3. **Monotonicity identity (3.18).** Radial cutoffs `g_k → 1_{B_1}` and dominated convergence
   give
   `|(μ(B_1) − σ^{-n}μ(B_σ)) − ∫_{B_1∖B_σ} |x^⊥|²|x|^{-n-2} dμ| ≤ δ(2 + log σ^{-1})`.
   The layer-cake bound (4.11) also holds.
4. **Annular test functions.** Take `g(y) = χ(|y|) φ(|y − ξ|)` supported in the annulus. The
   integrand is bounded by `2|x^⊥|²|x|^{-n-2} + 4κ|x^⊥||x|^{-n-1}`, and `|F| ≤ 4ρ|x|^{-n}`.
5. **Assembly.**
   * If `dL > 1`, both inequalities follow from `μ(B_1) ≤ Λ` and (3.18).
   * Otherwise, (3.18) and (4.11) bound the three annular integrals by `CδL`, `CL` and `δL`.
   * Step 4 with a cutoff `φ` of width `dρ` at radius `ρ` and `χ ≡ 1` gives the first
     inequality.
   * Step 4 with `φ` at radius `(1+d)ρ` and annular cutoffs `χ_k`, with `k → ∞`, gives the
     second inequality.

The book's proof of 6.1 uses the co-area formula 2.9 of Ch. 3 (book ll. 1229 and 1272). The
Lean proof does not use it. Its dependency closure consists of the tangent-plane lemmas of
step 1, and the radial integrations are done through the first-variation identity of step 2.

**Uses:** none.

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
  * Fubini–Tonelli: `integral_prod`, `lintegral_prod`.
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
* **Compatibility.** Every cited declaration comes from the pinned Mathlib and `simongmt`
  revisions used by the build. The comparator's axiom check covers them.

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
* **Later commits.** The commit that adds this document changes no comparator input. Its Lean
  and Lake inputs are byte-identical to `26012c4a`, so it has the same verdict key.

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

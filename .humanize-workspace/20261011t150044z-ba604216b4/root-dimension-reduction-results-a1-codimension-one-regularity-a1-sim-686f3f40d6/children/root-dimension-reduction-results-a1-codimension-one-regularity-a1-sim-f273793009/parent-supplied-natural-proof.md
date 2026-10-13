# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.piece_pushforward-a1.signed_area_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent step 11: "Apply (3.1) with B₀ = B to g = ofReal∘f and g = ofReal∘(−f): since J ≥ 0, ∫_{C′} ofReal(±f) dH^m = ∫_B ofReal(J(x))·ofReal(±f(Φ(x))) dH^m = ∫_B ofReal(±h_ω) dH^m. Writing the integrals of the integrable functions f (on C′) and h_ω (on B) as differences of the integrals of their positive and negative parts (integral_eq_lintegral_pos_part_sub_lintegral_neg_part), …", abstracted from the data (C′, B, J, f, H^m) to arbitrary data. The integrability of J·(f∘Φ), which the parent obtained in step 10, is derived here from the same identity applied to g = |f|. This is the standard passage from the nonnegative area formula (Simon Ch. 2, 3.5 and 4.13, chapter-02.txt lines 788–797 and 975–981, stated there for non-negative functions) to integrable real-valued functions.

Notation. ν_B := ν⌞B = ν.restrict B and μ_A := μ⌞A = μ.restrict A; F(x) := J(x)·f(Φ(x)); for t ∈ ℝ, ‖t‖ₑ = |t| ∈ [0, ∞) is its extended norm and ofReal t = max(t, 0) ∈ [0, ∞), so that ofReal(t) and ofReal(−t) are the positive and negative parts of t.

Proof.
1. (The hypothesis.) (H): for every g : β → [0, ∞], ∫⁻ g dν_B = ∫⁻ ofReal(J(x))·g(Φ(x)) dμ_A(x). No measurability of g is required by (H), so it may be applied to any of the functions below.
2. (Integrability of F.) For every x, ‖F(x)‖ₑ = ‖J(x)‖ₑ·‖f(Φ(x))‖ₑ (extended norm of a product, enorm_mul), and ‖J(x)‖ₑ = ofReal(J(x)) because J(x) ≥ 0 (Real.enorm_of_nonneg). Applying (H) to g := (y ↦ ‖f(y)‖ₑ):
 ∫⁻ ‖F‖ₑ dμ_A = ∫⁻ ofReal(J(x))·‖f(Φ(x))‖ₑ dμ_A(x) = ∫⁻ ‖f‖ₑ dν_B < ∞,
 the last inequality because f is ν_B-integrable (finite integral of its extended norm). So F has finite integral for μ_A; together with the hypothesis that F is a.e.-strongly measurable for μ_A, F is μ_A-integrable. This is the first conclusion.
3. (Positive parts.) Applying (H) to g := ofReal∘f gives
 ∫⁻ ofReal(f) dν_B = ∫⁻ ofReal(J(x))·ofReal(f(Φ(x))) dμ_A(x) = ∫⁻ ofReal(F(x)) dμ_A(x),
 because ofReal(a)·ofReal(b) = ofReal(a·b) whenever a ≥ 0 (ENNReal.ofReal_mul), applied pointwise with a = J(x) ≥ 0.
4. (Negative parts.) Applying (H) to g := ofReal∘(−f) gives
 ∫⁻ ofReal(−f) dν_B = ∫⁻ ofReal(J(x))·ofReal(−f(Φ(x))) dμ_A(x) = ∫⁻ ofReal(J(x)·(−f(Φ(x)))) dμ_A(x) = ∫⁻ ofReal(−F(x)) dμ_A(x),
 again by ENNReal.ofReal_mul (J(x) ≥ 0) and J(x)·(−f(Φ(x))) = −F(x).
5. (Conclusion.) For a real function h integrable with respect to a measure λ, ∫ h dλ = (∫⁻ ofReal(h) dλ).toReal − (∫⁻ ofReal(−h) dλ).toReal (integral_eq_lintegral_pos_part_sub_lintegral_neg_part). Apply this to f and ν_B (f is ν_B-integrable by hypothesis) and to F and μ_A (F is μ_A-integrable by step 2), and substitute steps 3 and 4:
 ∫_B f dν = (∫⁻ ofReal(f) dν_B).toReal − (∫⁻ ofReal(−f) dν_B).toReal = (∫⁻ ofReal(F) dμ_A).toReal − (∫⁻ ofReal(−F) dμ_A).toReal = ∫_A F dμ.
 This is the second conclusion. ∎

Lean note. The following proof was compiled (Lean v4.35.0-rc3, Mathlib 25730c7c; #print axioms: propext, Classical.choice, Quot.sound):
  intro α β _ _ μ ν Φ A B J f hJ harea hf hmeas
  have hint : Integrable (fun x => J x * f (Φ x)) (μ.restrict A) := by
    refine ⟨hmeas, ?_⟩
    have h1 : ∫⁻ x in A, ‖J x * f (Φ x)‖ₑ ∂μ = ∫⁻ y in B, ‖f y‖ₑ ∂ν := by
      rw [harea (fun y => ‖f y‖ₑ)]
      congr 1
      funext x
      rw [enorm_mul, Real.enorm_of_nonneg (hJ x)]
    rw [HasFiniteIntegral, h1]
    exact hf.2
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    harea (fun y => ENNReal.ofReal (f y)), harea (fun y => ENNReal.ofReal (-f y))]
  congr 2
  · congr 1
    funext x
    rw [ENNReal.ofReal_mul (hJ x)]
  · congr 1
    funext x
    rw [← ENNReal.ofReal_mul (hJ x), mul_neg]

## Key steps

1. Since J ≥ 0, ‖J(x)f(Φ(x))‖ₑ = ofReal(J(x))·‖f(Φ(x))‖ₑ; the identity with g = ‖f‖ₑ gives ∫⁻_A ‖J·f∘Φ‖ₑ dμ = ∫⁻_B ‖f‖ₑ dν < ∞, so J·f∘Φ is integrable on A.
2. The identity with g = ofReal∘f and g = ofReal∘(−f), together with ofReal(J)·ofReal(t) = ofReal(J·t) for J ≥ 0, identifies the positive and negative parts: ∫⁻_B ofReal(±f) dν = ∫⁻_A ofReal(±J·f∘Φ) dμ.
3. integral_eq_lintegral_pos_part_sub_lintegral_neg_part on both sides gives ∫_B f dν = ∫_A J·f∘Φ dμ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum of snapshot vs workspace GMT/Ch07/{Contract,Submission}.lean and of 8 cited Mathlib files (snapshot vs .lake/packages/mathlib)`
- `rg -n 'theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part|theorem withDensity_one|theorem restrict_apply'' |theorem setLIntegral_const|theorem setLIntegral_one|lemma enorm_of_nonneg|lemma enorm_mul|lemma Homeomorph.measurableEmbedding' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul|theorem integral_image_eq_integral_abs_det_fderiv_smul' <snapshot>/mathlib/Mathlib (same-dimension Lebesgue Jacobian formula only)`
- `grep -n 'continuous_compContinuousLinearMapCLM|def compContinuousLinearMapCLM|to_rightInverse|norm_fderiv_le_of_lipschitz|theorem setLIntegral_mono|theorem ContinuousOn.aestronglyMeasurable|pseudoMetrizableSpace' in Mathlib Alternating/Basic, Alternating/Topology, Antilipschitz, FDeriv/Basic, Lebesgue/Basic, IntegrableOn, Metrizable/Basic`
- `rg -n 'structure IMRep|def IMRep.measure|def IsIntegerMultiplicity|def IsEmbeddedSubmanifold|def IsOrientation' <snapshot>/project/GMT/Ch07/Contract.lean; rg -n 'codim1_ac_pp_' <snapshot>/project (no match); rg -c CountablyRectifiable <snapshot>/mathlib/Mathlib (no match); rg -n IsSimonSubmanifold <snapshot>/project (GMT/Ch02 only)`
- `rg -n 'theorem countablyRectifiable_of_isSimonSubmanifold|theorem measurableSet_of_isSimonSubmanifold|def IsSimonSubmanifold|def IsProperOnInto|theorem CountablyRectifiable.mono' SimonGMT; sed SimonGMT Chapter06/{Forms,Currents,Mass}.lean (IsTestForm, TestFormOn, GeometricCurrentOn, covectorEuclideanNorm, massAdmissibleOn, massOn)`
- `python scans of dag.json (1514 nodes): accepted statements mentioning massOn+IMRep, ∃ current + Represents, Integrable + orient, IsEmbeddedSubmanifold + MeasurableSet/CountablyRectifiable; lean_name uniqueness and status of dtc_imrep_current, regcomp_rim_action_integrable, dor_ims_massOn_le_measure, dor_ims_unitOrientation_dual, dor_ims_action_eq_integral; duplicates rsd_cmr_imrep_represents_exists, rsd_cmr_ic_action_integrable, regcomp_imrep_massOn_le_measure, rsd_mw_massOn_le_measure, dimred_rpd_embedded_locally_closed, dpfir_ii_countablyRectifiable_image_of_lipschitz, cmcdt_ims_imrep_of_int_density considered`
- `git show <candidate>:GMT/Ch07/Submission.lean for 642d7450f79f, f1339f96a29c, fae4fd1e831d, c2e1da27351f, 9c8432cb0101, 863f6d9cf603, 3de784c0d8f0 (declaration present, type byte-identical, no extra imports); declarations added per candidate; git grep codim1_ac_pp_ over 2580 distinct ref tips (no match; control codim1_ac_perturbation_diffeo found)`
- `runtime.py: _decompose (max_depth 6), _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children, _merge_candidate_history/_union_lean_conflicts, _reference_use_problem`
- `lean -DautoImplicit=false /tmp/pp-split/check/{Types,Child1,Child2,Child3,Assembly,AssemblyAx}.lean and /tmp/pp-split/full/{Full,FullAssembly}.lean`
- `book: chapter-03.txt 12–60 (3.1.1, Lemma 1.2 'if' part); chapter-06.txt 203 (2.2), 733–768 (3.1, 3.2(3)), 770–859 (3.3–3.9); chapter-02.txt 776–797 (3.4–3.5), 960–981 (4.11–4.13)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-686f3f40d6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f448992aee/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-imrep-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-restriction-integer-multipl-1450eb50b9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-mass-up-4048586780/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-action-188f3b5994/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pp-split/check/Types.lean`
- `/tmp/pp-split/check/Child1.lean`
- `/tmp/pp-split/check/Child2.lean`
- `/tmp/pp-split/check/Child3.lean`
- `/tmp/pp-split/check/Assembly.lean`
- `/tmp/pp-split/check/AssemblyAx.lean`
- `/tmp/pp-split/full/Full.lean`
- `/tmp/pp-split/full/FullAssembly.lean`

Pins match.
- The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- The snapshot and workspace GMT/Ch07/Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
- The cited Mathlib files are byte-identical between snapshot and workspace.
Library facts used by the split, all present in the snapshot Mathlib:
- Bochner/Basic.lean:486 integral_eq_lintegral_pos_part_sub_lintegral_neg_part (signed integral as a difference of positive and negative parts).
- WithDensity.lean:175 withDensity_one; Restrict.lean:111 restrict_apply' (needs only the measurability of the restricting set).
- Lebesgue/Basic.lean:121/124 setLIntegral_const and setLIntegral_one; :246 setLIntegral_mono.
- Normed/Group/Real.lean:95 Real.enorm_of_nonneg; Normed/Ring/Basic.lean:735 enorm_mul.
- BorelSpace/Basic.lean:567 Homeomorph.measurableEmbedding.
- Alternating/Basic.lean:437 continuous_compContinuousLinearMapCLM; Alternating/Topology.lean:281 compContinuousLinearMapCLM (simps apply).
- Antilipschitz.lean:137 AntilipschitzWith.to_rightInverse; FDeriv/Basic.lean:947 norm_fderiv_le_of_lipschitz.
- IntegrableOn.lean:791 ContinuousOn.aestronglyMeasurable, which needs PseudoMetrizableSpace. The instance is not found for MultiVector P m, so it is supplied explicitly as PseudoEMetricSpace.pseudoMetrizableSpace, the workaround used in accepted branches.
What the libraries lack:
- Mathlib's Jacobian.lean has only the same-dimension Lebesgue change of variables. Nothing transfers signed integrands through an H^m area formula on submanifolds, hence the new child signed_area_transfer.
- SimonGMT SubmanifoldCover.lean proves measurableSet_of_isSimonSubmanifold and countablyRectifiable_of_isSimonSubmanifold for IsSimonSubmanifold (Submanifold.lean, with IsProperOnInto). The contract's IsEmbeddedSubmanifold differs only by the smoothness-order cast and the order of the properness hypotheses, hence the new child embedded_rectifiable.
- Snapshot Mathlib has no CountablyRectifiable (no match); the snapshot project has no codim1_ac_pp_ names (no match).
DAG.
- Accepted, reusable, byte-identical: dtc_imrep_current (IMRep ⇒ represented current), regcomp_rim_action_integrable (integrability of θ⟨ω, ξ⟩ on the carrier), dor_ims_massOn_le_measure (M_W(T) ≤ μ_R(W) for all W), and its prerequisites dor_ims_unitOrientation_dual and dor_ims_action_eq_integral.
- Each maps to a unique accepted node whose candidate commit contains the declaration and adds no imports.
- With these, the new child unit_piece_current (Simon 6.2.2/6.3.1/6.3.2(3) with θ ≡ 1) has a short proof.
- The node's unaccepted prerequisites (submanifold_approx_tangent, submanifold_area) cannot be shared by children, so the geometric glue stays in this node. image_submanifold was accepted only during this session.
Lean.
- Types.lean elaborates all 8 child types.
- Child1–3 and Full.lean (real accepted declarations, textual union of their candidate commits) prove the 3 new children with axioms propext, Classical.choice and Quot.sound.
- FullAssembly.lean proves the selected frozen type from the children and the 4 used prerequisite types (as axioms).
- All of these exit 0.

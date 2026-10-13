# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1.cycle_slices-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 5 and 6 (slices of the cycle X via (SL) with the zero representation of ∂X, and the ISP of X), with an arbitrary Lipschitz g in place of f∘η.
Fix L ≥ 0 and an L-Lipschitz g : ℝ^P → ℝ.
1. The zero pair represents ∂X admissibly. Let 0_μ be the zero measure on ℝ^P and 0_ξ : ℝ^P → Λ_d(ℝ^P) the zero map.
(i) 0_μ(K) = 0 < ∞ for every K (simp).
(ii) 0_ξ is 0_μ-a.e. strongly measurable: every function is a.e. strongly measurable for the zero measure (aestronglyMeasurable_zero_measure).
(iii) ∀ᵐ x ∂0_μ, ∀α, |0_ξ(x)(α)| ≤ |α|. This holds because the zero measure's a.e. filter is trivial (simp); also |0| = 0 ≤ |α| pointwise.
(iv) For every test d-form η on ℝ^P: ∂X(η) = 0, since ∂X = 0 and the zero current evaluates to 0 (GeometricCurrentOn.zero_apply). Also ∫0_ξ(x)(η(x)) d0_μ(x) = 0 (integral_zero_measure). So ∂X(η) = ∫0_ξ(η) d0_μ (rw [hX]; simp).
2. Slices from (SL). Apply (SL) with U := ℝ^P (isOpen_univ), k := d, T := X, (μ, ξ) := (μX, ξX), (μ', ξ') := (0_μ, 0_ξ), f := g and Lipschitz constant L. The hypotheses are:
- compact-finiteness of μX on compact K ⊆ ℝ^P, i.e. the hypothesis on μX with the clause K ⊆ univ ignored;
- compact-finiteness of 0_μ (step 1(i));
- a.e. strong measurability of ξX (hypothesis) and of 0_ξ (step 1(ii));
- the a.e. bounds (hypothesis; step 1(iii));
- the representation X(ω) = ∫ξX(ω)dμX (hypothesis);
- the representation of ∂X by (0_μ, 0_ξ) (step 1(iv));
- LipschitzWith L g.
(SL) yields families A(t) ∈ 𝒟_{d+1}(ℝ^P), B(t) ∈ 𝒟_d(ℝ^P), t ∈ ℝ, with A(t)(ω) = ∫_{{g<t}} ξX(x)(ω(x)) dμX(x) and B(t)(η) = ∫_{{g<t}} 0_ξ(x)(η(x)) d0_μ(x) for all t, ω, η. The remaining three conclusions of (SL) are discarded.
3. Each B(t) is zero. For every t and η, B(t)(η) = ∫ 0_ξ(x)(η(x)) d(0_μ⌞{g<t}) = 0: the restriction of the zero measure is the zero measure (Measure.restrict_zero), the integral against it vanishes (integral_zero_measure), and the integrand is 0 anyway (simp). Since B(t) and the zero current agree on every test form, B(t) = 0 by extensionality of currents (GeometricCurrentOn.ext).
4. ISP of X. Apply the ISP hypothesis of X with (μ, μ', ξ, ξ') := (μX, 0_μ, ξX, 0_ξ), using the facts listed in step 2 (here compact-finiteness has no K ⊆ U clause: it is exactly the hypothesis on μX and step 1(i)), and with f := g, L and LipschitzWith L g. It yields: for L¹-a.e. t, every A₁ ∈ 𝒟_{d+1}(ℝ^P) and B₁ ∈ 𝒟_d(ℝ^P) with A₁(ω) = ∫_{{g<t}}ξX(ω)dμX for all ω and B₁(η) = ∫_{{g<t}}0_ξ(η)d0_μ for all η have ∂A₁ − B₁ integer multiplicity. It therefore suffices to prove the existence claim for each t in this full-measure set (filter_upwards).
5. Fix such a t. By step 2, A₁ := A(t) and B₁ := B(t) satisfy the two integral identities, so ∂A(t) − B(t) is integer multiplicity.
6. ∂A(t) − B(t) = ∂A(t). For every test d-form η, (∂A(t) − B(t))(η) = ∂A(t)(η) − B(t)(η), because the difference of currents is evaluated pointwise (the contract's Sub instance on GeometricCurrentOn subtracts the underlying linear maps). By step 3 this equals ∂A(t)(η) − 0 = ∂A(t)(η). By extensionality, ∂A(t) − B(t) = ∂A(t). Hence ∂A(t) is integer multiplicity (rewrite step 5 with this equality).
7. Conclusion. A := A(t) satisfies A(ω) = ∫_{{x : g(x) < t}} ξX(x)(ω(x)) dμX(x) for every test (d+1)-form ω (step 2), and ∂A is integer multiplicity (step 6). Since this holds for every t in the full-measure set of step 4, the conclusion holds for L¹-a.e. t. ∎

## Key steps

1. The zero measure with the zero field is an admissible representation of ∂X = 0.
2. (SL) applied to X with (μX, ξX), (0, 0) and g gives slice families A(t), B(t).
3. B(t) = 0 because it integrates against the zero measure; extensionality.
4. The ISP of X with the same data gives, for a.e. t, that ∂A(t) − B(t) is integer multiplicity.
5. ∂A(t) − B(t) = ∂A(t) by extensionality, so A := A(t) witnesses the claim for a.e. t.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); sed -n 120,457p GMT/Ch07/Submission.lean (dilation, dilationCLM, IsIntegerMultiplicity, Sub instance on GeometricCurrentOn)`
- `grep -n 'structure GeometricCurrentOn|def TestFormOn|def IsTestForm|GeometricCurrentOn.ext|zero_apply|boundary_apply|covectorEuclideanNorm' in lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass}.lean`
- `python3 -I scan of dag.json: frozen lean_statement of the selected node (equal to the handoff), of sibling cbr_ci_dilation_calculus, and of cmc_slice_mass_bounds and cbr_setIntegral_eq_of_integral_eq ('(' + frozen + ')' is exactly the SL and RU hypotheses); all 1316 lean_names (no 'cbr_ci_dsp' prefix); no node with a type identical to a child; related nodes dtc_blowUp_testForm_corr, dtc_hausdorff_dilation, cbrld_sphere_slice_isIntegerMultiplicity (other branches, different types)`
- `rg -n --fixed-strings in .../123e8435b4a2469b/mathlib/Mathlib: '_root_.MeasurableEmbedding.setIntegral_map', '_root_.MeasurableEmbedding.aestronglyMeasurable_map_iff', 'theorem ae_map_iff', 'theorem ae_smul_measure', 'theorem integral_smul_measure', 'theorem restrict_smul', 'theorem restrict_zero', 'theorem integral_zero_measure', 'theorem aestronglyMeasurable_zero_measure', 'Homeomorph.smulOfNeZero', 'lemma Homeomorph.measurableEmbedding', 'theorem isCompact_preimage', 'comp_homeomorph', 'lemma LipschitzWith.mul' (all found); literal 'theorem HasCompactSupport.comp_homeomorph' (no match: it is the to_additive form of HasCompactMulSupport.comp_homeomorph, Support.lean:562, and #check confirms it); 'LipschitzWith.const_add' (does not exist, per Lean error; LipschitzWith.const.add is used)`
- `lake env lean /tmp/dilisp-decomp/lean/Probe.lean (#check of the cited lemmas, all reachable from import GMT.Ch07.Submission; MeasurableEquiv.setIntegral_map and unqualified ae_smul_measure unknown, replaced by MeasurableEmbedding.setIntegral_map and Measure.ae_smul_measure)`
- `lake env lean /tmp/dilisp-decomp/lean/{Stmts,Children,Assembly,Emul}.lean plus set_option maxHeartbeats {8000,15000,25000,40000} probes and #print axioms`
- `python3 -I validate_lean_statement from verifier/lean_contract.py on the three child types; check_source_delta (extracted with ast from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py) on the three child proofs and on the parent assembly`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-474ece9e64/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-474ece9e64/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Homeomorph/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dilisp-decomp/lean/Stmts.lean`
- `/tmp/dilisp-decomp/lean/Children.lean`
- `/tmp/dilisp-decomp/lean/Assembly.lean`
- `/tmp/dilisp-decomp/lean/Emul.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). No existing declaration or DAG node uses the proposed names (prefix cbr_ci_dsp_) or has any of the three child types. The related accepted nodes (dtc_blowUp_testForm_corr, dtc_hausdorff_dilation, cbrld_sphere_slice_isIntegerMultiplicity) live in other branches with different types, so they are not prerequisites here. In the parent type, the SL and RU hypotheses are exactly the parenthesized frozen statements of cmc_slice_mass_bounds and cbr_setIntegral_eq_of_integral_eq. Every Mathlib lemma used by the child proofs exists in the snapshot and is reachable from import GMT.Ch07.Submission. Each of the three child types elaborates and was fully proven in scratch (axioms propext, Classical.choice, Quot.sound; each within 15000 heartbeats), and all three pass validate_lean_statement and the leaf source-delta check. The exact frozen parent type was proven from the exact child types and the exact frozen sibling type cbr_ci_dilation_calculus (assembly within 40000 heartbeats; only standard axioms besides the sorry placeholder for the unproven sibling).

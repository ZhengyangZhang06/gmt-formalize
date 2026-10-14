# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_calculus-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_calculus-a1.dilation_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (∂X'(ω) = X'(dω) and d(ω∘η) = λ⁻¹(dω)∘η, i.e. d commutes with the affine pull-back by η), carried out through the identification X' = η_#X of the sibling dilation_blowup and the commutation ∂η_# = η_#∂ of the sibling blowup_structure (iv), which is exactly the statement that d commutes with the affine pull-back by η (SimonGMT exteriorDerivative_affinePullbackForm / boundary_affinePushforward).
Conventions. ℝ^P = Euclid P; η := dilation a λ, η(y) = −λ⁻¹a + λ⁻¹y = λ⁻¹(y − a), λ > 0. For V ⊆ ℝ^P, 𝒟^k(V) = TestFormOn V k is the space of C^∞ k-forms ω on ℝ^P (maps to k-covectors) with compact tsupport ω ⊆ V; its elements are determined by their underlying forms. 𝒟_k(V) = GeometricCurrentOn V k. For X, X' ∈ 𝒟_k(ℝ^P), X' is a dilation of X when X'(ω) = λ^{−k}X(ω') for all ω, ω' ∈ 𝒟^k(ℝ^P) with ω'(y) = ω(η(y)) for every y. η_#Y := η_{a,λ#}Y = blowUp Y a λ ∈ 𝒟_k(η(U)) for Y ∈ 𝒟_k(U). Sibling names refer to the children of this decomposition: testform_correspondence = dtc_blowUp_testForm_corr, blowup_structure = dtc_blowUp_algebra, rep_pushforward = dtc_blowUp_imrep, mass_scaling = dtc_blowUp_massOn_image, dilation_blowup = cbr_cidc_dilation_exists_eq_blowUp.
Let X, X' be as in the statement and let ω, ω' ∈ 𝒟^m(ℝ^P) with ω'(y) = ω(η(y)) for all y. For a current Y in a domain V and φ ∈ 𝒟^k(V), ∂Y(φ) := Y(dφ), where dφ ∈ 𝒟^{k+1}(V) has underlying form the exterior derivative of the underlying form of φ (SimonGMT exteriorDerivativeTestOn); so dφ depends only on the underlying form of φ.
1. η is onto ℝ^P: for y ∈ ℝ^P, η(a + λy) = −λ⁻¹a + λ⁻¹(a + λy) = −λ⁻¹a + λ⁻¹a + (λ⁻¹λ)y = y because λ ≠ 0. Hence ℝ^P ⊆ η(ℝ^P), i.e. η(ℝ^P) = ℝ^P, so every ω ∈ 𝒟^k(ℝ^P) is also an element of 𝒟^k(η(ℝ^P)) with the same underlying form (tsupport ω ⊆ ℝ^P ⊆ η(ℝ^P); SimonGMT testFormOnInclusion), and every element of 𝒟^k(η(ℝ^P)) is an element of 𝒟^k(ℝ^P) with the same underlying form. Let ω₁ ∈ 𝒟^m(η(ℝ^P)) be ω regarded in η(ℝ^P).
2. ∂X'(ω) = X'(dω) with dω ∈ 𝒟^{m+1}(ℝ^P). The test form dω₁ ∈ 𝒟^{m+1}(η(ℝ^P)) has the same underlying form as dω (both are the exterior derivative of the same form). By dilation_blowup (ii) in degree m + 1 (applied to X, X', which by hypothesis is a dilation of X in degree m + 1, and to the pair dω, dω₁): X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁).
3. By blowup_structure (iv) with U = ℝ^P, x = a and T = X ∈ 𝒟_{m+1}(ℝ^P): ∂(η_#X) = η_#(∂X). Hence ∂X'(ω) = η_#(∂X)(ω₁).
4. Since ω₁ and ω have the same underlying form, ω'(y) = ω(η(y)) = ω₁(η(y)) for all y. testform_correspondence (c) with U = ℝ^P, x = a, n = m, T = ∂X ∈ 𝒟_m(ℝ^P) and the pair ω₁, ω' gives η_#(∂X)(ω₁) = λ^{−m}∂X(ω').
5. Combining steps 2–4, ∂X'(ω) = λ^{−m}∂X(ω'). ∎
Formalization notes (proved in a scratch build from the exact sibling types): h1 := (dilation_blowup P (m+1) a λ hlam).2 X X' hX (exteriorDerivativeTestOn univ m ω) (exteriorDerivativeTestOn _ m (testFormOnInclusion hsurj m ω)) rfl; then rw [GeometricCurrentOn.boundary_apply, h1, ← GeometricCurrentOn.boundary_apply, (blowup_structure P univ a λ hlam).2.2.2 m X] and close with part (c) of testform_correspondence for X.boundary.

## Key steps

1. ∂X'(ω) = X'(dω), and dω has the same underlying form as dω₁ for the copy ω₁ of ω in 𝒟^m(η(ℝ^P)).
2. dilation_blowup (ii) in degree m + 1: X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁).
3. blowup_structure (iv): ∂(η_#X) = η_#(∂X).
4. testform_correspondence (c) for ∂X: η_#(∂X)(ω₁) = λ^{−m}∂X(ω∘η).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n 'def blowUp|def dilation |def dilationCLM' project/GMT/Ch07/Contract.lean (lines 175, 179, 184: blowUp T x λ = (T.restrictDomain _).affinePushforward (dilationCLM P λ) (-(λ⁻¹ • x)) _)`
- `rg -n 'theorem _root_.MeasurableEmbedding.integral_map|theorem integral_smul_measure|lemma Homeomorph.measurableEmbedding' mathlib/Mathlib (found: MeasureTheory/Integral/Bochner/Basic.lean:1093 and :1052, MeasureTheory/Constructions/BorelSpace/Basic.lean:567)`
- `rg -n 'cbr_cidc_|dtc_blowUp_testForm_corr' project (no match); python3 -I scan of dag.json: lean_name in {dtc_hausdorff_dilation, dtc_blowUp_testForm_corr, dtc_approxTangent_dilation, dtc_blowUp_imrep, dtc_blowUp_massOn_image, dtc_blowUp_algebra} each exactly one node, status accepted, candidate_commit set, lean_statement byte-identical; no node with prefix cbr_cidc_`
- `git show 6cdd2c0a916b259c47744f21c1f8501c98dce2c7:GMT/Ch07/Submission.lean (this node's proof base: bare contract); git show cb3c7f3eda7f74be829e1ae3271494c85af94319, 17c63f22cc8bff3693345ac9074b98fadbf16246, f64597f33dbddb264b249a7f03156a1073cce7da :GMT/Ch07/Submission.lean (accepted proofs of the six dtc_* theorems)`
- `sed of SimonGMT Chapter06 Currents.lean, Forms.lean, Mass.lean, AffineCurrentPushforward.lean, CurrentLocalEquality.lean (GeometricCurrentOn, boundary_apply, exteriorDerivativeTestOn, massOn, massAdmissibleOn, affinePushforward_apply, boundary_affinePushforward, restrictDomain_apply, testFormOnInclusion_coe)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children) and leaf_verification.py check_source_delta; python3 -I read of decomposition-v2.json and decomposition-audit-v2.json of root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1 (accepted precedent of cross-branch reuse)`
- `lake env lean /tmp/dilcalc-decomp/Check1.lean (new children from reused types as hypotheses), /tmp/dilcalc-decomp/FinalAssembly.lean (frozen parent type from the 11 child types), /tmp/dilcalc-decomp/Full.lean (accepted dtc_* proofs + five new single-theorem proofs + parent assembly); #print axioms: propext, Classical.choice, Quot.sound; verifier/lean_contract.py validate_lean_statement on all 11 types (pass)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3e82e4b03e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-hausdorff-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-tangent-invariance-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-rep-pushforward-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-mass-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-blowup-structure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dilation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dilcalc-decomp/Check1.lean`
- `/tmp/dilcalc-decomp/FinalAssembly.lean`
- `/tmp/dilcalc-decomp/Full.lean`

Snapshot and project facts:
- The snapshot contract is byte-identical to Submission.lean (project b4d606db, Mathlib 25730c7c).
- This node's base 6cdd2c0a is the bare contract, so an unsplit leaf would have no helper declarations.

Reused declarations. Six comparator-accepted declarations of root.density_and_tangent_cones-a1.blowup_scaling-a1 prove the supplied steps 2–7 and 9 for blowUp in an arbitrary domain: dtc_hausdorff_dilation, dtc_blowUp_testForm_corr, dtc_approxTangent_dilation, dtc_blowUp_imrep, dtc_blowUp_massOn_image and dtc_blowUp_algebra. Each:
- is unique in the DAG;
- is accepted with a candidate commit;
- is reused here with its byte-identical type.
The runtime allows this reuse; cmcdt_dilation_pushforward is a precedent.

New declarations. The five new names (prefix cbr_cidc_) occur nowhere in the DAG or the snapshot. The Mathlib lemmas they use exist in the snapshot: MeasurableEmbedding.integral_map, integral_smul_measure, Homeomorph.measurableEmbedding and ENNReal.toReal_ofReal.

Lean checks:
- All 11 types elaborate after `import GMT.Ch07.Submission` and pass the verifier's lexical check.
- The frozen parent type follows from the 11 types by a one-line assembly.
- An end-to-end build compiles: the real accepted proofs, plus single-theorem proofs of the five new children, plus the parent. #print axioms gives only propext, Classical.choice, Quot.sound.

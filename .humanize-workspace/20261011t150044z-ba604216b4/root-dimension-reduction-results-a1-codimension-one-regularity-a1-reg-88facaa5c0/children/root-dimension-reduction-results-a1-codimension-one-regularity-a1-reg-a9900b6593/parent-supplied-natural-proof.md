# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.mollifier_adjoint-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof step 2: ∇u_ε = (∇η_ε) * u, ∇η_ε is odd, and Fubini. This is the chain ∫ g·∇u^(ε) = −∫ u div(φ_ε * g) in Simon's proof of Ch. 2, Lemma 2.5 (chapter-02.txt lines 543–596), written for a single even kernel η.

Conventions. For f : R^P → R and h scalar- or vector-valued, (f * h)(x) := ∫ f(t) h(x − t) dt = ∫ f(x − t) h(t) dt. This is Mathlib's convolution with L = lsmul ℝ ℝ and μ = volume; the second form is convolution_eq_swap, valid because Lebesgue measure is invariant under translations and under x ↦ −x. Dη denotes the derivative of η.

0. Dη is continuous (η is C¹) and vanishes outside the compact set tsupport η. So there is C ≥ 0 with |Dη(y)| ≤ C for all y, and Dη has compact support.

1. Oddness. η(−y) = η(y) for all y. Differentiating y ↦ η(−y) by the chain rule gives Dη(−y) ∘ (−id) = Dη(y), i.e. Dη(−y) = −Dη(y) for all y.

2. Derivative of η*u. u is integrable, hence locally integrable, and η is C¹ with compact support. So η*u is differentiable at every x with D(η*u)(x) = (Dη * u)(x) = ∫ Dη(x − z) u(z) dz (Mathlib HasCompactSupport.hasFDerivAt_convolution_left, then convolution_eq_swap). The integrand z ↦ Dη(x − z) u(z) is integrable: it is the swapped convolution integrand of the continuous, compactly supported Dη with the locally integrable u (HasCompactSupport.convolutionExists_left and ConvolutionExistsAt.integrable_swap). Evaluation at the fixed vector s(x) is a continuous linear map, so it commutes with the Bochner integral (ContinuousLinearMap.integral_apply). Hence D(η*u)(x)(s(x)) = ∫ Dη(x − z)(s(x)) u(z) dz.

3. Divergence of η*s. Likewise s is locally integrable, so η*s : R^P → R^P is differentiable with D(η*s)(z) = ∫ A_{z,x} dx, where A_{z,x}(v) := Dη(z − x)(v) s(x). This is (Dη * s)(z) for the bilinear map precompL of lsmul, after convolution_eq_swap; its integrand is integrable as in step 2. View the trace as a continuous linear functional T on the finite-dimensional space of linear maps R^P → R^P (LinearMap.toContinuousLinearMap of trace ∘ coercion). Then T commutes with the Bochner integral (ContinuousLinearMap.integral_comp_comm). A_{z,x} is the map v ↦ a(v) w (of rank at most one) with a = Dη(z − x) and w = s(x), so trace(A_{z,x}) = Dη(z − x)(s(x)) (LinearMap.trace_smulRight). Hence div(η*s)(z) = trace D(η*s)(z) = ∫ Dη(z − x)(s(x)) dx.

4. Fubini. Let H(x, z) := Dη(x − z)(s(x)) u(z) on R^P × R^P. H is a.e. strongly measurable for the product measure L^P ⊗ L^P. Indeed, (x, z) ↦ Dη(x − z) is continuous. s and u are integrable, hence a.e. strongly measurable. Composition with the coordinate projections (x, z) ↦ x and (x, z) ↦ z preserves this (AEStronglyMeasurable.comp_fst and comp_snd), so (x, z) ↦ s(x) and (x, z) ↦ u(z) are a.e. strongly measurable on the product. H is obtained from these three maps by the continuous bilinear evaluation (A, v) ↦ A(v), followed by multiplication. Moreover |H(x, z)| ≤ C |s(x)| |u(z)|, and (x, z) ↦ |s(x)| |u(z)| is integrable for the product measure because s and u are integrable (Integrable.mul_prod). So H is integrable on the product, and ∫_x (∫_z H(x, z) dz) dx = ∫_z (∫_x H(x, z) dx) dz (integral_integral_swap).

5. Conclusion. By step 2, the left side of step 4 equals ∫ D(η*u)(x)(s(x)) dx. On the right side, step 1 gives Dη(x − z) = Dη(−(z − x)) = −Dη(z − x). So ∫_x H(x, z) dx = u(z) ∫_x Dη(x − z)(s(x)) dx = −u(z) ∫_x Dη(z − x)(s(x)) dx = −u(z) div(η*s)(z), by step 3. Therefore ∫ D(η*u)(x)(s(x)) dx = −∫ u(z) div(η*s)(z) dz. ∎

## Key steps

1. η even implies Dη(−y) = −Dη(y).
2. D(η*u)(x)(v) = ∫ Dη(x − z)(v) u(z) dz (derivative of a convolution, swap, evaluation commutes with the integral).
3. div(η*s)(z) = ∫ Dη(z − x)(s(x)) dx (the trace commutes with the integral, and the trace of v ↦ a(v)w is a(w)).
4. Fubini on R^P × R^P with the dominating function C|s(x)||u(z)|.
5. Use oddness to identify the swapped integral with −∫ u div(η*s).

## Reference use

### local-project

Queries:
- `cat nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-88facaa5c0/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json,parent-supplied-plan.md}`
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git show 5900180377298da556c85bb52c494b4e691baed4:GMT/Ch07/Submission.lean | sha256sum`
- `rg -n '^theorem lintegral_pow_le_pow_lintegral_fderiv |irreducible_def lintegralPowLePowLIntegralFDerivConst' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `rg -n 'theorem ae_convolution_tendsto_right_of_locallyIntegrable|theorem normed_neg|theorem integral_normed|theorem nonneg_normed|theorem contDiff_normed|theorem hasCompactSupport_normed' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/{Convolution,Normed}.lean`
- `rg -n 'hasFDerivAt_convolution_left|contDiff_convolution_left|HasCompactSupport.convolution|convolution_eq_swap|ConvolutionExistsAt.integrable_swap|trace_smulRight|theorem lintegral_liminf_le|theorem integral_integral_swap|theorem Measurable.inv|theorem integrable_indicator_iff' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -l 'SobolevInequality|BumpFunction.Convolution' local-references/123e8435b4a2469b/project/GMT/Ch07 (no match)`
- `lake env lean /tmp/sp-split-v2/Avail2.lean (#check of 46 candidate declarations after import GMT.Ch07.Submission)`
- `python3 -I scope.py: verifier gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem')`
- `grep/sed /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/{leaf_verification.py check_source_delta, parent_verification.py check_parent_git_delta, runtime.py _decompose/_machine_git_check/_existing_lean_name_problem, prompts.py DECOMPOSE/SPECULATIVE_PARENT_TASK/RLCR_LEAN_TASK, lean_contract.py}`
- `python3 -I leafcheck.py and leafneg.py (runtime check_source_delta on each child inserted into the base Submission; negative control adding an import)`
- `git log --all -S 'import Mathlib.Analysis' -- GMT/Ch07/Submission.lean; git show -s 8abce3204 bff81d31e 58a0bf378; lean-audit-v1.json review_method of dtc_mass_eq_measure and dtc_isIntegerMultiplicity_sub`
- `python3 scans of dag.json (995 nodes) for codim1_rdo_dg_sp_* names and identical types; git log --all -S codim1_rdo_dg_sp_; grep -r codim1_rdo_dg_sp_ .lake/packages/simongmt`
- `lake env lean -DautoImplicit=false /tmp/sp-split-v2/{Challenges,Full,FullNode,ChildrenOnly,ParentFull}.lean /tmp/sp-split-v2/final/{FinalChallenges,FinalNode}.lean`
- `lake env lean /tmp/sp-split-v2/hashcheck/{Orig,SubX}.lean (hashes of every GMT.Ch07 constant with and without the two parent imports)`
- `sed -n 686,714p book/chapter-03.txt; sed -n 540,600p book/chapter-02.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Arithmetic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-88facaa5c0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-88facaa5c0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-88facaa5c0/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/lean-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/sp-split-v2/Avail2.lean`
- `/tmp/sp-split-v2/ChildrenOnly.lean`
- `/tmp/sp-split-v2/ParentFull.lean`
- `/tmp/sp-split-v2/final/FinalChallenges.lean`
- `/tmp/sp-split-v2/final/FinalNode.lean`
- `/tmp/sp-split-v2/final/subproblems.json`
- `/tmp/sp-split-v2/hashcheck/Orig.lean`
- `/tmp/sp-split-v2/hashcheck/SubX.lean`

Pins. The snapshot manifest pins project b4d606db and Mathlib 25730c7c, the same as the workspace. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean, and the Submission.lean at the children's proof base 590018037 are byte-identical (sha256 e4148e7f…). None of them imports SobolevInequality or BumpFunction.Convolution.

Library reachability. The snapshot Mathlib contains lintegral_pow_le_pow_lintegral_fderiv (SobolevInequality.lean:371), lintegralPowLePowLIntegralFDerivConst (:358), ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103) and normed_neg/integral_normed/hasCompactSupport_normed (Normed.lean:49,68,79). All are absent from the GMT.Ch07.Submission import closure. In the closure: hasFDerivAt_convolution_left (ContDiff/Convolution.lean:91), contDiff_convolution_left (:427), HasCompactSupport.convolution (Convolution.lean:568), convolution_eq_swap (:693), trace_smulRight (Trace.lean:272), lintegral_liminf_le, integral_integral_swap, Measurable.inv and integrable_indicator_iff.

Runtime rules. Leaves get only a single-theorem insertion (leaf_verification.check_source_delta); simulated, it rejects an added import. Non-leaves may add imports (parent_verification.check_parent_git_delta; accepted machine-nonleaf precedents bff81d31e and 77fcc7d4e). Depth-6 children are always leaves. Hence v1's import-dependent gns_real and bv_sobolev were unimplementable, and the new split keeps all five children import-free, with the Mathlib GNS and normed-bump calls in the parent's own proof.

Lean checks. Adding the two parent imports leaves the type/value hashes of all 103 GMT.Ch07 constants unchanged. All five child types elaborate in the comparator scope. Complete proofs of the five children compile with only `import GMT.Ch07.Submission`, pass check_source_delta and the NodeSolution `exact Submission.X`, and use only propext/Classical.choice/Quot.sound. The parent's exact frozen type is proved from them, with the two imports, using the same axioms.

Names and sources. The five names are fresh; no identical accepted type exists, so nothing is reused. The book citations checked are chapter-03.txt 689–712 (Sobolev step of 4.3) and chapter-02.txt 543–596 (Lemma 2.5, formula (4) at line 568).

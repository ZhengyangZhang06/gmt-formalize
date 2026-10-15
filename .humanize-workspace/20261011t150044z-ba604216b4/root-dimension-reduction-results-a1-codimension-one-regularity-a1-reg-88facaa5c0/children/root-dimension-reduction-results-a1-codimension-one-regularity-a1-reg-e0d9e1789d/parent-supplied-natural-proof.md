# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.sobolev_perimeter-a1.mollify_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof step 2: the choice s := 1_S ∇u_ε/|∇u_ε| and g := η_ε * s. This is Simon Ch. 2, Lemma 2.5, formula (4) and the chain after it (chapter-02.txt lines 543–596), for a single even mollifier η. The Fubini identity used here is the sibling theorem mollifier_adjoint.

Fix P, u, M and η as in the statement. f*h denotes the convolution ∫ f(t) h(x − t) dt of the Lean statement, L = volume, and div X = trace DX.

1. Let w := η*u. η is C¹ with compact support and u is locally integrable, so w is C¹ (HasCompactSupport.contDiff_convolution_left). η and u both have compact support, so w has compact support (HasCompactSupport.convolution). Let S := tsupport w; S is compact and closed, hence measurable, and Dw is continuous.

2. Gradient. For each x, let ∇w(x) ∈ R^P be the unique vector with Dw(x)(v) = ⟨∇w(x), v⟩ for all v. By Riesz, ∇w(x) = (InnerProductSpace.toDual ℝ R^P)⁻¹(Dw(x)). The map x ↦ ∇w(x) is continuous, being Dw followed by a linear isometry. Moreover |∇w(x)| = |Dw(x)| (operator norm) and Dw(x)(∇w(x)) = |∇w(x)|².

3. Unit field. Let f(x) := |∇w(x)|⁻¹ ∇w(x), where t⁻¹ is the total real inverse with 0⁻¹ := 0. Thus f(x) = 0 when ∇w(x) = 0. f need not be continuous at zeros of ∇w, and no continuity of f is used. f is Borel measurable. ∇w is continuous by step 2, hence Borel. x ↦ |∇w(x)| is continuous, hence Borel. The real inverse t ↦ t⁻¹ (0⁻¹ = 0) is Borel measurable on R (Measurable.inv), so x ↦ |∇w(x)|⁻¹ is Borel. The product of this Borel scalar function with the Borel field ∇w is Borel (Measurable.smul). Next, |f(x)| = |∇w(x)|⁻¹ |∇w(x)| is 0 if ∇w(x) = 0 and 1 otherwise, so |f(x)| ≤ 1 for all x. Define s := 1_S f, i.e. s(x) := f(x) for x ∈ S and s(x) := 0 for x ∉ S. S is closed, hence a Borel set, so s is Borel (Measurable.indicator). Also |s(x)| ≤ 1 for all x, and s = 0 outside the compact set S, so s has compact support. s is integrable: S is compact, so L(S) < ∞. On S, s = f is measurable and bounded by 1, so f is integrable on S (Measure.integrableOn_of_bounded). Since s is the indicator of the measurable set S applied to f, s is integrable on R^P (integrable_indicator_iff).

4. Dw(x)(s(x)) = |Dw(x)| for all x. If x ∈ S and ∇w(x) ≠ 0, then Dw(x)(s(x)) = |∇w(x)|⁻¹ |∇w(x)|² = |∇w(x)| = |Dw(x)|. If x ∈ S and ∇w(x) = 0, both sides are 0. If x ∉ S = tsupport w, then w vanishes on a neighbourhood of x, so Dw(x) = 0 (support of Dw ⊆ tsupport w, support_fderiv_subset) and both sides are 0. Consequently ∫ |Dw| dL = ∫ Dw(x)(s(x)) dx.

5. Admissible field. Let g := η*s : R^P → R^P, so g(z) = ∫ η(t) s(z − t) dt. g is C¹ (η is C¹ with compact support, s is locally integrable), and g has compact support (η and s do). η is continuous with compact support, hence integrable, with ∫ η = 1. Since η ≥ 0 and |s| ≤ 1, for all z: |g(z)| ≤ ∫ η(t)|s(z − t)| dt ≤ ∫ η(t) dt = 1.

6. Adjoint identity. η is C¹, compactly supported and even, and u and s are integrable. So the sibling mollifier_adjoint gives ∫ Dw(x)(s(x)) dx = −∫ u(z) div g(z) dz.

7. Conclusion. g is admissible by step 5, so the hypothesis applies to it. With steps 4 and 6: ∫ |D(η*u)| dL = −∫ u div g dL ≤ |∫ u div g dL| ≤ M. ∎

## Key steps

1. w := η*u is C¹ with compact support S := tsupport w.
2. s := 1_S |∇w|⁻¹∇w (0⁻¹ = 0) is Borel by measurable inversion and product (not by continuity), satisfies |s| ≤ 1, has compact support, is integrable, and Dw(s) = |Dw| everywhere.
3. g := η*s is C¹, compactly supported and satisfies |g| ≤ ∫η = 1.
4. The sibling mollifier_adjoint gives ∫|Dw| = ∫Dw(s) = −∫u div g ≤ |∫u div g| ≤ M.

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

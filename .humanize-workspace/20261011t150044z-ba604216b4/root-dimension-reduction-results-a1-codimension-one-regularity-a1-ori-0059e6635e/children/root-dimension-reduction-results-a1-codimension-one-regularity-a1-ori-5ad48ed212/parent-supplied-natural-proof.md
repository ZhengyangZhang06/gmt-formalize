# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.oriented_piece_mass-a1.oriented_mass_upper-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 6, 2.5 (the mass M_W(T), chapter-06.txt lines 224–240) and 3.2(3) (M_W(T) = ∫_{M∩W} θ dH^n for T = τ(M, θ, ξ), chapter-06.txt lines 755–770). This is the upper half of the parent proof: its step 1 (1a) and step 2, specialized to a measurable W ⊆ V. Two simplifications relative to the parent's step 2: no case distinction on whether I(W) is finite is needed, and no measurability of θ' or ξ' is used, because the estimate goes through the inequality |∫ g| ≤ ∫⁻ |g|, which holds for every function g (step 5).

Sibling child used (an accepted declaration, reused with its identical frozen type):
- unit_orientation_dual (Submission.dor_ims_unitOrientation_dual), part (a) only: if ξ ∈ Λ_k(ℝ^P) is a unit orientation of some subspace Q (IsUnitOrientationOf ξ Q), then |ξ(α)| ≤ |α| for every k-covector α.

Notation.
- H^k := μHE[k] and μ := H^k⌞M' (μHE[k].restrict M'). For α ∈ Λ^k := Covector (Euclid P) k, |α| := covectorEuclideanNorm α.
- ∫ g dμ is the Bochner integral, as in the frozen statement; by definition it is 0 when g is not μ-integrable.
- I(W) := ∫⁻_{M'∩W} ofReal(θ') dH^k ∈ [0, ∞].
- ω ∈ 𝒟^k(U) is admissible for M_W(T) if tsupport ω ⊆ W and |ω(x)| ≤ 1 for every x. M_W(T) = T.massOn W is the supremum of ofReal(T(ω)) over admissible ω.

Proof. Fix the data and hypotheses of the statement and a measurable set W ⊆ V.

1. (Pointwise duality bound.) Call x good if |ξ'(x)(α)| ≤ |α| for every α ∈ Λ^k. By hypothesis, for μ-a.e. x there is a subspace Q with IsUnitOrientationOf (ξ'(x)) Q, and then x is good by unit_orientation_dual (a). Hence μ-a.e. x is good.

2. (Reduction to one admissible form.) M_W(T) is the supremum of ofReal(T(ω)) over admissible ω, so it suffices to prove ofReal(T(ω)) ≤ I(W) for every admissible ω. Fix one.

3. (Representation.) tsupport ω ⊆ W ⊆ V, so the representation hypothesis gives T(ω) = ∫ g dμ with g(x) := θ'(x)·ξ'(x)(ω(x)).

4. (Domination.) For every good x, |g(x)| ≤ 1_W(x)·θ'(x):
 - if x ∉ W, then x ∉ tsupport ω because tsupport ω ⊆ W; a function vanishes outside its topological support, so ω(x) = 0, hence ξ'(x)(ω(x)) = 0 by linearity of ξ'(x), and g(x) = 0;
 - if x ∈ W, then, since θ'(x) ≥ 0, |g(x)| = θ'(x)·|ξ'(x)(ω(x))| ≤ θ'(x)·|ω(x)| ≤ θ'(x), by step 1 and |ω(x)| ≤ 1.
 By step 1, ofReal|g(x)| ≤ 1_W(x)·ofReal(θ'(x)) for μ-a.e. x.

5. (Estimate.) In [0, ∞],
 ofReal(T(ω)) ≤ ofReal|T(ω)| = ofReal|∫ g dμ| ≤ ∫⁻ ofReal|g| dμ.
 The last inequality is the triangle inequality ofReal|∫ g dμ| ≤ ofReal(∫ |g| dμ) = ∫⁻ ofReal|g| dμ when g is μ-integrable, and it is trivial when g is not μ-integrable, since then ∫ g dμ = 0 (in Mathlib: enorm_integral_le_lintegral_enorm, valid for every g). By step 4 and monotonicity of the lower Lebesgue integral under a.e. inequalities,
 ∫⁻ ofReal|g| dμ ≤ ∫⁻ 1_W·ofReal(θ') dμ = ∫⁻_W ofReal(θ') dμ = ∫⁻ ofReal(θ') d(H^k⌞(W ∩ M')) = I(W).
 Here W is measurable: the integral of 1_W·f is the integral of f over W (lintegral_indicator), (H^k⌞M')⌞W = H^k⌞(W ∩ M') (Measure.restrict_restrict), and W ∩ M' = M' ∩ W. Hence ofReal(T(ω)) ≤ I(W).

6. (Conclusion.) Taking the supremum over all admissible ω gives M_W(T) ≤ I(W). ∎

## Key steps

1. unit_orientation_dual (a): |ξ'(x)(α)| ≤ |α| for every α at H^k⌞M'-a.e. x.
2. For admissible ω (tsupport ω ⊆ W ⊆ V, |ω| ≤ 1): T(ω) = ∫_{M'} g with g = θ'·ξ'(ω), and |g| ≤ 1_W·θ' a.e. on M' because ω = 0 off W.
3. ofReal T(ω) ≤ ofReal|∫ g| ≤ ∫⁻ ofReal|g| ≤ ∫⁻_{M'} 1_W·ofReal θ' = I(W) for measurable W; take the supremum over admissible ω.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C lake-packages-25730c7c/mathlib rev-parse HEAD; git -C lake-packages-25730c7c/simongmt rev-parse HEAD; python3 read of snapshot project/lake-manifest.json (mathlib and simongmt revs)`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem .*[Ll]usin' mathlib/Mathlib; rg -ln Lusin mathlib/Mathlib; rg -n Lusin mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean (snapshot)`
- `rg -n 'theorem enorm_integral_le_lintegral_enorm|theorem integral_withDensity_eq_integral_toReal_smul |theorem lintegral_indicator |theorem restrict_restrict |theorem exists_measurable_superset_of_null|theorem isBoundedBilinearMap_apply|theorem le_of_forall_nnreal_lt|theorem withDensity_apply |theorem withDensity_absolutelyContinuous|image_eq_zero_of_notMem_tsupport' mathlib/Mathlib (snapshot)`
- `rg -n 'instance.*InnerRegular' mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `rg -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; read Chapter06/Currents.lean and Forms.lean (TestFormOn, IsTestForm, DifferentialForm, Covector)`
- `python3 scan of dag.json: subtree root.density_one_implies_regular-a1.imrep_mass_and_support-a1 (statuses, candidate commits, exact lean_statement of unit_orientation_duality, lusin_covector, smooth_unit_approximation, mass_upper_bound, mass_lower_bound) and their parent-child-handoff.json proofs`
- `git show 57cebee2fbae5e013e3b0e4191cd38bc03b89473:GMT/Ch07/Submission.lean (accepted Lean proofs of dor_ims_measure_le_massOn and of the three reused declarations)`
- `grep -c codim1_oriented_rep dag.json; grep -rn 'codim1_oriented_rep|oriented_rep_massOn|oriented_rep_lintegral' GMT/ simongmt/Poincare and the snapshot; git grep -l codim1_oriented_rep over all 1193 distinct ref commits -- 'GMT/*.lean'`
- `lean -DautoImplicit=false /tmp/opm-decomp-check/Check.lean and /tmp/opm-decomp-check/CheckAx.lean with #print axioms (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `sed -n 220,242p and 750,772p book/chapter-06.txt (Simon 6.2.5 and 6.3.2(3))`
- `runtime.py: _solve_children, _existing_lean_name_problem, _accepted_checkpoint, _install_parent_supplied_child_handoff`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-ori-0059e6635e/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-lusin-covector-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/opm-decomp-check/Check.lean`
- `/tmp/opm-decomp-check/CheckAx.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`

Pins match.
- The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to the workspace HEAD and lake-packages mathlib.
- The snapshot lake-manifest pins simongmt 2b366308, equal to the installed package.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library.
- The snapshot Mathlib has no Lusin continuity theorem: only Lusin separation and Lusin–Souslin in Constructions/Polish/Basic.lean. Hence the reuse of the accepted dor_ims_lusin_continuousOn.
- It provides everything the new children use: enorm_integral_le_lintegral_enorm (Integral/Bochner/Basic.lean:333), integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318), lintegral_indicator (Lebesgue/Basic.lean:510), Measure.restrict_restrict (Restrict.lean:205), exists_measurable_superset_of_null (MeasureSpaceDef.lean:219), withDensity_apply / withDensity_absolutelyContinuous (WithDensity.lean:44/146), isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391), Real.enorm_eq_ofReal_abs (Group/Real.lean:110), ENNReal.le_of_forall_nnreal_lt (ENNReal/Inv.lean:487) and image_eq_zero_of_notMem_tsupport.
- SimonGMT Chapter06/Mass.lean supplies massAdmissibleOn, massOn (sSup of ofReal T ω), le_massOn and covectorEuclideanNorm.

DAG.
- dor_ims_unitOrientation_dual, dor_ims_lusin_continuousOn and dor_ims_smooth_unit_approx are status accepted with candidate commits 9c8432cb0101, 83274ea8a2c7 and 89e4c45cd3c1. Their lean_statement strings are copied byte-for-byte. Their reviewed handoff proofs are copied verbatim; the accepted Lean proofs are in 57cebee2fbae:GMT/Ch07/Submission.lean.
- The accepted IMRep mass lemmas (dor_ims_massOn_le_measure, dor_ims_measure_le_massOn) do not apply to a real weight with a representation only on V.
- The new names codim1_oriented_rep_massOn_le_lintegral and codim1_oriented_rep_lintegral_le_massOn are free in dag.json (578 nodes), GMT/, SimonGMT, the snapshot and all 1193 distinct ref commits.
- runtime.py allows reuse of accepted checkpoints with identical types, and _install_parent_supplied_child_handoff returns early for them.

Lean.
- Check.lean elaborates all 5 child types after import GMT.Ch07.Submission. It fully proves both new children and the selected frozen theorem from them, exiting 0 with only the 3 reused stand-in sorries.
- CheckAx.lean shows the axioms are propext, Classical.choice, Quot.sound and the reused declarations only.

Book. chapter-06.txt lines 224–240 (6.2.5) and 755–770 (6.3.2(3)) are the cited sources.

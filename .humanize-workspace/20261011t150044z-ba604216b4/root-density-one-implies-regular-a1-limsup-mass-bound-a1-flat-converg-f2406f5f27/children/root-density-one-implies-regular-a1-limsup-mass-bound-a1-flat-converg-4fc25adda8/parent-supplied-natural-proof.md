# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.skeleton_deformation-a1.zero_neg-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 7 of the parent proof (the zero current is IM with empty carrier; M(0 − X) = M(X) because admissible forms are closed under negation; |T(ω)| ≤ M(T)·sup|ω| after scaling ω to be admissible). Dependency: im_calculus ((IMC)(c)).
1. (a) Define an IMRep R₀ in U with carrier ∅, mult ≡ 0 and orient ≡ 0. Its fields: ∅ is measurable and ∅ ⊆ U; CountablyRectifiable k ∅ by countablyRectifiable_of_measure_zero (μHE[k] ∅ = 0); the constant mult is measurable; mult_pos is vacuous; ∫⁻_{∅∩K} 0 dμHE[k] = 0 ≠ ∞; the constant orient is a.e.-strongly measurable; the orientation condition holds a.e. because μHE[k].restrict ∅ = 0. R₀ represents 0: 0(ω) = 0 and R₀.action ω = ∫_∅ … = 0. So 0 is IM.
2. (b) If X is IM, (IMC)(c) with A = 0 (IM by (a)) and B = X, on the open U, shows that 0 − X is IM.
3. (c) For ω ∈ 𝒟^k(U), (0 − X)(ω) = 0 − X(ω) = −X(ω) = X(−ω): the contract subtraction is pointwise and X.toCurrent is linear (map_neg). The map ω ↦ −ω sends massAdmissibleOn U k G into itself, because tsupport(−ω) = tsupport ω (tsupport_neg) and covectorEuclideanNorm((−ω)(x)) = covectorEuclideanNorm(−ω(x)) = covectorEuclideanNorm(ω(x)) (covectorEuclideanNorm_neg); it is an involution. Hence {ofReal((0 − X)(ω)) : ω admissible} = {ofReal(X(ω′)) : ω′ admissible} (ω′ = −ω), and taking suprema gives M_G(0 − X) = M_G(X).
4. Homogeneity of the coefficient norm: for c ∈ ℝ and a k-covector α, covectorEuclideanNorm(c·α) = |c|·covectorEuclideanNorm(α), since (c·α)(e_I) = c·α(e_I), the sum of squares is multiplied by c², and Real.sqrt(c²·S) = |c|·Real.sqrt(S).
5. (d) Let s > 0, M(X) < ∞ and |ω(x)| ≤ s for all x. Then ω′ := s⁻¹·ω ∈ 𝒟^k(U) (submodule), tsupport ω′ ⊆ tsupport ω ⊆ U and |ω′(x)| = s⁻¹|ω(x)| ≤ 1 (step 4), so ω′ and −ω′ are admissible for M(X) = M_U(X). By le_massOn, ofReal(X(ω′)) ≤ M(X) and ofReal(X(−ω′)) ≤ M(X); since M(X) < ∞ this gives X(ω′) ≤ M(X).toReal and −X(ω′) ≤ M(X).toReal (ENNReal.ofReal_le_iff_le_toReal). By linearity X(ω′) = s⁻¹X(ω), so |X(ω)| = s·|X(ω′)| ≤ s·M(X).toReal. ∎

## Key steps

1. The empty IMRep represents 0, so 0 is IM; (IMC)(c) gives 0 − X IM.
2. ω ↦ −ω preserves admissibility, so M_G(0 − X) = M_G(X).
3. covectorEuclideanNorm is absolutely homogeneous; ±s⁻¹ω are admissible, giving |X(ω)| ≤ s·M(X).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n "theorem LipschitzOnWith.extend_real|theorem LipschitzOnWith.extend_pi" mathlib/Mathlib`
- `rg -n "theorem mul_meas_ge_le_lintegral₀|theorem meas_ge_le_lintegral_div|theorem lintegral_eq_zero_iff'" mathlib/Mathlib`
- `rg -n "theorem integral_inter_add_sdiff|theorem lipschitz_infDist_pt|theorem mem_cthickening_of_dist_le|theorem tprod_eq_zero_mul'" mathlib/Mathlib`
- `rg -n "tsum_geometric |theorem one_sub_inv_two|le_sum_of_subadditive|bddAbove_range_of_hasCompactSupport|theorem setLIntegral_le_lintegral|theorem ae_restrict_iff'" mathlib/Mathlib`
- `rg -n "dor_lmb_fcd_sd_|skeleton_deformation|good_slice|shell" project -g "*.lean" (no match)`
- `grep -n "^def |^theorem |^structure |^instance" .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,FormSupNorm,CurrentLocalEquality,Forms}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, ext, Zero, boundary, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset, WeaklyConvergesOn.boundary, massAdmissibleOn, massOn, le_massOn, WeaklyConvergesOn.massOn_le_liminf, covectorEuclideanNorm_neg, countablyRectifiable_of_measure_zero)`
- `python3 -I scans of dag.json: frozen types of dor_lmb_fcd_good_center, dor_lmb_fcd_retraction, dor_lmb_fcd_pushforward_homotopy (decomposing siblings), dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub (accepted, byte-identical types), accepted helpers cmc_fc_cs_massOn_sub_le, cmc_fc_sc_abs_le_mul_mass, dor_lmb_imrep_restrict_current; freshness of the ten dor_lmb_fcd_sd_* names`
- `sed -n 1651,1860p book/chapter-06.txt (Simon 5.1 proof, displays (1)-(25)); sed of runtime.py (_decompose depth check, _overlay_accepted_children, _existing_lean_name_problem) and verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/skd-decomp/final/AllChallenges.lean (12 exact challenge types), /tmp/skd-decomp/Assembly.lean (parent frozen type from children + GC/RET/PF/C1 stand-ins), CoreCheck, SeriesCheck, TeleCheck, GSCheck, SHCheck, ICCheck, Leaf, Bound2 with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-f2406f5f27/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/skd-decomp/Assembly.lean`
- `/tmp/skd-decomp/CoreCheck.lean`
- `/tmp/skd-decomp/final/AllChallenges.lean`

Snapshot project b4d606db / mathlib 25730c7c; its Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. No project file contains a skeleton deformation, good-slice or shell lemma (no match for dor_lmb_fcd_sd_*, skeleton_deformation, good_slice, shell). SimonGMT supplies the current API used by the children (GeometricCurrentOn with ext and Zero, boundary via exteriorDerivativeTestOn whose underlying form is exteriorDerivative ω by definition, tsupport_exteriorDerivative_subset, massAdmissibleOn/massOn/le_massOn, WeaklyConvergesOn.massOn_le_liminf, covectorEuclideanNorm_neg, countablyRectifiable_of_measure_zero) but no Lipschitz push-forward, homotopy, slicing or restriction lemma, so those enter through the DAG siblings (GC, RET, PF) and the reused accepted (C1) dor_imrep_massOn_eq_measure_and_support and (IMC) cmc_imRep_locality_restrict_sub (byte-identical frozen types). Every Mathlib lemma cited in the child proofs exists in the pinned snapshot: LipschitzOnWith.extend_real (Lipschitz.lean:308), lintegral_eq_zero_iff', setLIntegral_le_lintegral, integral_inter_add_sdiff (Bochner/Set.lean:114), lipschitz_infDist_pt, mem_cthickening_of_dist_le, tsum_eq_zero_add' (to_additive of tprod_eq_zero_mul'), ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, Finset.le_sum_of_subadditive, ae_restrict_iff', Continuous.bddAbove_range_of_hasCompactSupport. Lean: all 12 child types elaborate as exact comparator challenges; the parent frozen type compiles from the four used children plus stand-ins for GC, RET, PF and C1 with no sorry in the assembly body; core compiles from telescoping and series_limit, series_limit from zero_neg, telescoping from (IMC) and zero_neg, good_slice from markov_point, im_concentrated and (C1), shells from im_restrict, im_concentrated from (C1) (axioms propext, Classical.choice, Quot.sound, plus sorryAx only from the stand-ins).

# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.opnorm_basis_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0(c) of the parent proof of regcomp_exists_smooth_unit_form_approx. There the bound |α(e∘j)| ≤ |α|_E for every j (from regcomp_covector_eval_orthonormal_le if j is injective, and from the alternating property if not) is fed into a multilinear expansion; here that bound is abstracted as the hypothesis C, and the parent applies this lemma with C := |α|_E. Notation: e_i := EuclideanSpace.basisFun (Fin P) ℝ i; e∘r := (k ↦ e_{r(k)}) for r : Fin n → Fin P; w_i denotes the i-th coordinate of w ∈ Euclid P; ‖α‖ is the Mathlib (operator) norm of Covector (Euclid P) n.

1. (Reduction.) Since P^n·C ≥ 0, by ContinuousAlternatingMap.opNorm_le_bound it suffices to show |α(v)| ≤ P^n·C·Π_k ‖v_k‖ for every v : Fin n → Euclid P.

2. (Basis expansion.) Every w ∈ Euclid P satisfies w = Σ_{i : Fin P} w_i • e_i (OrthonormalBasis.sum_repr together with EuclideanSpace.basisFun_repr, which identifies the basis coordinates of w with its coordinates w_i). Apply this to each v_k.

3. (Multilinear expansion.) By multilinearity of α in each of its n arguments (ContinuousMultilinearMap.map_sum applied to α.toContinuousMultilinearMap, or ContinuousAlternatingMap.map_sum), α(v) = Σ_{r : Fin n → Fin P} α(k ↦ (v_k)_{r(k)} • e_{r(k)}). Pulling the scalars out of all slots (ContinuousMultilinearMap.map_smul_univ), α(k ↦ (v_k)_{r(k)} • e_{r(k)}) = (Π_k (v_k)_{r(k)})·α(e∘r). Hence α(v) = Σ_r (Π_k (v_k)_{r(k)})·α(e∘r).

4. (Coordinate bound.) For w ∈ Euclid P and i : Fin P, |w_i| ≤ ‖w‖ (PiLp.norm_apply_le; equivalently w_i² ≤ Σ_l w_l² = ‖w‖²).

5. (Estimate.) By the triangle inequality (norm_sum_le), |Π_k a_k| = Π_k |a_k| (Finset.abs_prod), step 4 together with monotonicity of finite products of nonnegative reals, and the hypothesis |α(e∘r)| ≤ C:
 |α(v)| ≤ Σ_r (Π_k |(v_k)_{r(k)}|)·|α(e∘r)| ≤ Σ_r (Π_k ‖v_k‖)·C = #(Fin n → Fin P)·C·Π_k ‖v_k‖ = P^n·C·Π_k ‖v_k‖,
 where #(Fin n → Fin P) = P^n (Finset.card_univ, Fintype.card_fun, Fintype.card_fin). This is the bound required in step 1, so ‖α‖ ≤ P^n·C. ∎

(The same argument covers the degenerate cases: for n = 0 the only r is the empty tuple and empty products equal 1; for P = 0 < n the index set of r is empty, so α(v) = 0 ≤ 0.)

## Key steps

1. Reduce, via ContinuousAlternatingMap.opNorm_le_bound, to |α(v)| ≤ P^n·C·Π_k ‖v_k‖.
2. Expand each v_k in the standard basis and use multilinearity: α(v) = Σ_r (Π_k (v_k)_{r(k)})·α(e∘r).
3. Bound |(v_k)_i| ≤ ‖v_k‖ and |α(e∘r)| ≤ C, and count the P^n tuples r.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (IDENTICAL)`
- `rg -n 'theorem Integrable.exists_hasCompactSupport_lintegral_sub_le' mathlib/Mathlib`
- `rg -n 'theorem Continuous.exists_contDiff_approx ' mathlib/Mathlib`
- `rg -n 'theorem dist_normed_convolution_le|theorem _root_.HasCompactSupport.contDiff_convolution_left' mathlib/Mathlib`
- `rg -n 'theorem support_convolution_subset|HasCompactSupport.convolution' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem opNorm_le_bound|theorem map_eq_zero_of_not_injective|lemma Integrable.of_bound' mathlib/Mathlib`
- `rg -n 'theorem exists_compact_between|theorem exists_continuous_one_zero_of_isCompact|exists_cthickening_subset_open|uniformContinuous_of_continuous' mathlib/Mathlib`
- `rg -n 'theorem norm_sub_sq_real|theorem real_inner_le_norm|theorem norm_apply_le|theorem EuclideanSpace.norm_eq|theorem basisFun_repr|protected def equiv' mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem map_sum|theorem map_smul_univ' mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'theorem nonneg_normed|theorem contDiff_normed|theorem integral_normed|theorem support_normed_eq|theorem hasCompactSupport_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -ln 'covectorEuclideanNorm' project/ ; rg -n 'radial|retraction|max 1' project/GMT (no reusable project lemma; definition lives in simongmt Chapter06/Mass.lean)`
- `grep -n 'covectorEuclideanNorm|massAdmissibleOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' .../Chapter06/Forms.lean`
- `python3 -I scans of dag.json for lean_name and normalized lean_statement collisions with the five proposed children (final: 278 nodes, none) and for related nodes (dor_ims_sua_*, rsd_mw_exists_testForm_approx, covectorEuclideanNorm_gram_bounds)`
- `grep of .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean for the five proposed names (no hits) and for extra imports / helper modules`
- `lake env lean /tmp/smooth-form-split/{Stmts,C13,C2,C4,C4conv,C5,Assembly,Full,Full2,Assembly2,Assembly2Base,Assembly2Exact}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-6b0404974b/parent-child-handoff.json`
- `/tmp/smooth-form-split/Full2.lean`
- `/tmp/smooth-form-split/Assembly2Exact.lean`
- `/tmp/smooth-form-split/C4conv.lean`
- `/tmp/smooth-form-split/review/children2.json`

Snapshot and contract. The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean. The snapshot project has no reusable lemma about covectorEuclideanNorm (only the Ch07 contract mentions it). The definition is in simongmt Chapter06/Mass.lean, which provides only _zero, _nonneg and _neg.

Mathlib support. The snapshot Mathlib supplies everything the children cite:
- Integrable.exists_hasCompactSupport_lintegral_sub_le (ContinuousMapDense.lean:211; needs NormedSpace ℝ E but no separability of E).
- The Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure instance (Regular.lean:1183).
- Continuous.exists_contDiff_approx, which also gives support g ⊆ support f (Geometry/Manifold/SmoothApprox.lean:132).
- Bump-convolution lemmas (BumpFunction/Convolution.lean:71, ContDiff/Convolution.lean:427, Convolution.lean:568/670).
- ContinuousAlternatingMap.opNorm_le_bound, map_eq_zero_of_not_injective, map_sum and ContinuousAlternatingMap.apply.
- ContinuousMultilinearMap.map_smul_univ.
- EuclideanSpace.norm_eq, equiv and basisFun_repr; PiLp.norm_apply_le; norm_sub_sq_real and real_inner_le_norm.
- exists_compact_between, exists_continuous_one_zero_of_isCompact, IsCompact.exists_cthickening_subset_open, HasCompactSupport.uniformContinuous_of_continuous and Integrable.of_bound.
CompleteSpace and NormedSpace instances for Covector (Euclid P) n resolve. ContinuousMapDense and SmoothApprox are outside the contract import closure; other worktrees do add imports.

Reuse and collisions. No comparator-accepted declaration with an identical type exists to reuse. The near-duplicates found mid-session (dor_ims_sua_coeff_norm_rep, dor_ims_sua_mollify_unit_field) are only decomposing; they were avoided by restating the two affected children. Final scans found no name or statement collisions and no hits in the worktrees.

Lean checks. The five children are fully proved in Full2.lean using only standard axioms. The frozen parent type is proved from them plus regcomp_covector_eval_orthonormal_le with only the contract import (Assembly2Exact.lean). An independent reviewer re-ran these checks and accepted the revised split.

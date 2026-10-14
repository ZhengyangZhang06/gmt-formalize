# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.pushforward-a1.smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling child: Submission.cmcdt_lpo_pf_approx_data (AD).
1. AD, applied to Λ, F and K := spt X, gives maps F_j that are C^∞ and Λ-Lipschitz, with ‖fderiv ℝ F_j x‖ ≤ Λ for all j and x, and F_j → F uniformly on ℝ^N. Take these F_j; the first three requirements are AD's conclusions.
2. Given ω ∈ 𝒟^k(ℝ^{N'}), AD (in degree k, for ω) gives test forms η_j and open sets W_j ⊇ spt X on which η_j = F_j^#ω; the dη_j clause is dropped. Take these η_j.
3. (PA) with Λ' := Λ (the derivative bound from step 1), uniform convergence on spt X (TendstoUniformly.tendstoUniformlyOn) and the agreement from step 2 gives X(η_j) → lpush(F, X)(ω). □

Lean proof script. It compiled with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens, against the exact frozen type of AD. It is the tactic body of theorem Submission.cmcdt_lpo_pf_smooth_approx : <lean_statement> := by
  intro lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨Fs, hFs, hLip, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  refine ⟨Fs, hFs, hLip, hU, fun ω => ?_⟩
  obtain ⟨ηs, hηs⟩ := hη k ω
  have hη' : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hKW, h1⟩
  exact ⟨ηs, hη', hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn hη'⟩

## Key steps

1. AD gives C^∞ Λ-Lipschitz maps F_j → F uniformly, with ‖DF_j‖ ≤ Λ.
2. For each ω, AD gives η_j = F_j^#ω near spt X.
3. (PA) gives X(η_j) → lpush(F, X)(ω).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical)`
- `rg -n cmcdt_lpo_pf local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n IsLipschitzPushforward local-references/123e8435b4a2469b/project -g '*.lean' (GMT/Ch06/Contract.lean:144, GMT/Ch06/Submission.lean:144)`
- `rg -n 'theorem (add_compContinuousLinearMap|smul_compContinuousLinearMap|compContinuousLinearMap_apply|zero_compContinuousLinearMap|compContinuousLinearMap_id)' mathlib/Mathlib -g '*.lean' (only ContinuousAlternatingMap.compContinuousLinearMap_apply, Topology/Algebra/Module/Alternating/Basic.lean:319)`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz|theorem tendstoUniformly_iff|theorem tendstoUniformlyOn_iff|theorem TendstoUniformly.tendstoUniformlyOn' mathlib/Mathlib -g '*.lean'`
- `rg -n 'def apply|ContinuousEvalConst|continuous_eval_const' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean (instContinuousEvalConst at line 189)`
- `rg -n 'theorem continuous_if_const|theorem Continuous.if_const' mathlib/Mathlib -g '*.lean' (Topology/Piecewise.lean:116)`
- `rg -n infDist_pos mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean (IsClosed.notMem_iff_infDist_pos at line 584)`
- `rg -n 'theorem image_eq_zero_of|theorem image_eq_one_of' mathlib/Mathlib -g '*.lean' (Topology/Algebra/Support.lean:111, to_additive image_eq_zero_of_notMem_tsupport)`
- `rg -n 'theorem (IsClosed.notMem_iff_infDist_pos|infDist_le_dist_of_mem|closure_ball_subset_closedBall|ofReal_coe_nnreal|ofReal_pow|ofReal_toReal)' mathlib/Mathlib -g '*.lean'`
- `sed/grep of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormSupNorm}.lean`
- `sed -n 475,530p book/chapter-06.txt (Simon 6.2.28-2.29)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: lean_name prefix cmcdt_lpo_pf unused (rechecked before submission); selected node depth 5, max_depth 6; Lean names in the ancestors' depends_on collected so that each child cites only the interfaces it uses`
- `grep of /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/{inherited.py,runtime.py,prompts.py} (a child's parent-supplied-natural-proof.md is natural_proof + key steps + this ledger; ancestor-dependency names cited there become inherited prerequisites; depth >= max_depth disables further splitting)`
- `lake env lean /tmp/pf-decomp-x9/Check.lean (eleven child types elaborate; assembly_check proves the exact selected frozen type from them; #print axioms)`
- `lake env lean /tmp/pf-decomp-x9/P_<child>.lean for every child and lake env lean /tmp/pf-decomp-x9/AllAx.lean (all child proofs and the parent assembly compile with the parent-level sibling interfaces stated as axioms of their exact frozen types; per-declaration #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-f91696716e/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/runtime.py`
- `/tmp/pf-decomp-x9/Check.lean`
- `/tmp/pf-decomp-x9/AllAx.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) contains the same Ch07 contract as the workspace Submission.lean. Its only Lipschitz push-forward material is the unproved Ch06 specification IsLipschitzPushforward, which is stated over another Euclidean type and cannot be imported into Ch07, so no proof can be reused. No snapshot declaration and no DAG node uses the prefix cmcdt_lpo_pf, so the eleven proposed names are free. Every library fact the child proofs cite was found in the frozen import closure and confirmed by compilation. From Mathlib: norm_fderiv_le_of_lipschitz, tendsto_one_div_add_atTop_nhds_zero_nat, Metric.tendstoUniformly_iff and Metric.tendstoUniformlyOn_iff, TendstoUniformly.tendstoUniformlyOn, TendstoUniformlyOn.congr_right, Continuous.eval_const (instContinuousEvalConst), continuous_if_const, continuous_finsetSum, Continuous.bounded_above_of_compact_support, HasCompactSupport.comp_left, cauchySeq_of_le_tendsto_0, cauchySeq_tendsto_of_complete, IsClosed.notMem_iff_infDist_pos, infDist_le_dist_of_mem, image_eq_zero_of_notMem_tsupport, closure_ball_subset_closedBall, ContinuousAlternatingMap.compContinuousLinearMap_apply, fderiv_fun_id, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal and ENNReal.coe_pow. From SimonGMT Chapter06: GeometricCurrentOn.ext, boundary, zero_apply, le_massOn, isOpen_zeroRegion, exteriorDerivativeTestOn, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, exteriorDerivative_sq and covectorEuclideanNorm_zero/_neg/_nonneg. FormSupNorm.lean defines a sup norm but proves no boundedness, so form_bounds is a genuine obligation. All eleven child types elaborate, and the exact selected frozen type follows from them alone. Every child proof compiles against the exact frozen types of the parent-level sibling interfaces it cites. Simon 6.2.28-2.29 in book/chapter-06.txt matches the construction: the Lipschitz push-forward is the limit of mollified push-forwards, made Cauchy by the homotopy estimate, with spt contained in f(spt T) and the mass bound.

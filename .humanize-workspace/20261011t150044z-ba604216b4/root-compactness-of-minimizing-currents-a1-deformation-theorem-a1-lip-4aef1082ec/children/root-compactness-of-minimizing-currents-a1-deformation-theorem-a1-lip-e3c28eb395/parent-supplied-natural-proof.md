# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.coords-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (Coordinates) of the parent proof, packaged as one continuous linear equivalence. Fix N.
1. Linear equivalence. Let e : ℝ × ℝ^N ≃ₗ[ℝ] ℝ^{N+1} be the composite (LinearEquiv.trans) of three linear equivalences:
 (a) (LinearEquiv.refl ℝ ℝ).prodCongr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)), which sends (t, x) to (t, WithLp.ofLp x);
 (b) Fin.consLinearEquiv ℝ (fun _ : Fin (N + 1) => ℝ), which sends (t, y) to Fin.cons t y;
 (c) (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℝ)).symm, which sends z to WithLp.toLp 2 z.
 Unfolding the three maps gives e (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) for all t and x; this is a definitional equality, closed by rfl.
2. Continuity. ℝ × ℝ^N is finite-dimensional, and both sides are Hausdorff topological vector spaces over the complete field ℝ. So L := e.toContinuousLinearEquiv (LinearEquiv.toContinuousLinearEquiv) is a continuous linear equivalence with the same underlying function. By step 1 this proves (i).
3. Property (ii). By (i), L (1, 0) = WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp 0)). Two points of ℝ^{N+1} are equal when all their coordinates agree; split the index with Fin.cases.
 - At index 0 the left side is Fin.cons 1 _ 0 = 1, and EuclideanSpace.single 0 1 also has coordinate 1 there.
 - At index j.succ the left side is (WithLp.ofLp 0) j = 0, and single 0 1 has coordinate 0 there because j.succ ≠ 0 (Fin.succ_ne_zero).
 Hence L (1, 0) = EuclideanSpace.single 0 1.
4. Property (iii). By (i) and EuclideanSpace.norm_eq, ‖L (0, x)‖ = √(Σ_{i : Fin (N+1)} ‖Fin.cons 0 (WithLp.ofLp x) i‖²). Split the sum with Fin.sum_univ_succ and use Fin.cons_zero and Fin.cons_succ: the sum becomes ‖0‖² + Σ_{j : Fin N} ‖x_j‖² = Σ_j ‖x_j‖². Its square root is ‖x‖ by EuclideanSpace.norm_eq again (simp closes the goal).
5. Steps 2–4 give a continuous linear equivalence L with (i), (ii) and (iii). □

## Key steps

1. Compose (refl × WithLp.linearEquiv), Fin.consLinearEquiv and (WithLp.linearEquiv).symm into a linear equivalence e with e(t, x) = toLp 2 (Fin.cons t (ofLp x)) by rfl.
2. Finite dimension upgrades e to a continuous linear equivalence L (LinearEquiv.toContinuousLinearEquiv), which gives (i).
3. L(1, 0) = EuclideanSpace.single 0 1 by comparing coordinates with Fin.cases and Fin.succ_ne_zero.
4. ‖L(0, x)‖ = ‖x‖ by EuclideanSpace.norm_eq and Fin.sum_univ_succ.

## Reference use

### local-project

Queries:
- `cat nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-4aef1082ec/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, as in manifest.json)`
- `rg -n 'cmcdt_lpo_slice_' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'contDiff_parametric|theorem ContDiff.intervalIntegral|contDiff_integral|hasFDerivAt_integral_of_dominated_of_fderiv_le' mathlib/Mathlib -g '*.lean'`
- `rg -n 'integral_of_contDiff|ContDiff\.integral|contDiff_integral|ContDiff.*intervalIntegral|theorem .*parametric.*contDiff|contDiffOn_parametric' mathlib/Mathlib -g '*.lean' (no match: no C^∞ parametric-integral lemma)`
- `sed -n 195,260p mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `sed -n 180,275p mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'def removeNth|theorem removeNth_zero' mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `rg -n 'theorem extDeriv_apply|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le..|theorem contDiff_succ_iff_hasFDerivAt|theorem contDiff_infty|theorem curryLeft_apply_apply|theorem integral_deriv_eq_sub|theorem norm_integral_le_of_norm_le_const|theorem isProperMap_iff_isCompact_preimage' mathlib/Mathlib -g '*.lean'`
- `grep -n 'def TestFormOn|abbrev DifferentialForm|abbrev Covector|def covectorEuclideanNorm|abbrev exteriorDerivative|theorem exteriorDerivative_apply|affinePullbackForm_isTestForm' -r lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06`
- `python3 scans of runs/20261011T150044Z-ba604216b4/dag.json: lean_name collisions for the 8 proposed names (none); nodes under lipschitz_pushforward; lean_statements containing parametric integrals or ≃L[ℝ] coordinate maps (no identical accepted declaration)`
- `sed -n 1370,1600p /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py; grep -n 'reached the limit' prompts.py (depth 5 < max_depth 6)`
- `lake env lean /tmp/slice-decomp-q7w3/Avail.lean (#check of every cited lemma in the frozen import closure)`
- `lake env lean /tmp/slice-decomp-q7w3/Children.lean (all 8 child types elaborate; sorry-free assembly of the exact selected type from the 5 conjunct child types; #print axioms)`
- `lake env lean /tmp/slice-decomp-q7w3/{Coords,Param,DSplit,Fiber,EndForm,HomSucc,HomZero,Bound}.lean and AllProof.lean (complete sorry-free proofs of all 8 children and of the exact selected frozen type; exit 0, 0 errors, 0 sorry)`
- `python3: textual equality of the frozen parent lean_statement with '(' + fiber_form + ') ∧ (' + end_form + ') ∧ (' + homotopy_succ + ') ∧ (' + homotopy_zero + ') ∧ ' + covector_bound (True)`
- `sed -n 345,460p book/chapter-06.txt (Simon 6.2.17-2.25)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-4aef1082ec/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-4aef1082ec/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Maps/Proper/CompactlyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/slice-decomp-q7w3/Avail.lean`
- `/tmp/slice-decomp-q7w3/Children.lean`
- `/tmp/slice-decomp-q7w3/AllProof.lean`

The snapshot (project b4d606d; its Ch07 Contract.lean is identical to workspace GMT/Ch07/Submission.lean; Mathlib 25730c7c) has no cmcdt_lpo_slice_* declaration. It also has no slice/fiber-integration lemma and no C^∞ parametric-integral lemma.
- Mathlib provides only the pointwise interval lemma hasFDerivAt_integral_of_dominated_of_fderiv_le'' (ParametricIntegral.lean:235). The C^∞ statement is therefore the genuine child param_integral, proved by induction with contDiff_succ_iff_hasFDerivAt (ContDiff/Defs.lean:1171) and contDiff_infty (:1114).
- extDeriv_apply (DifferentialForm/Basic.lean:198) fixes the sign convention Σ_i (−1)^i • fderiv (ω · (i.removeNth v)) x (v i), and Fin.removeNth p f = f ∘ p.succAbove (Data/Fin/Tuple/Basic.lean:845). Together these determine the exact form of extderiv_split.
- SimonGMT Chapter06 (lake-packages-25730c7c/simongmt) supplies TestFormOn (C^∞ compactly supported forms with tsupport ⊆ U), exteriorDerivative = extDeriv with exteriorDerivative_apply, affinePullbackForm_isTestForm (which needs IsProperMap (x ↦ b + Lx)) and covectorEuclideanNorm.
- Every other cited lemma is in the frozen import closure (Avail.lean): curryLeftLI, curryLeft_apply_apply, compContinuousLinearMapCLM, ContinuousAlternatingMap.apply, intervalIntegral_comp_comm, intervalIntegral_apply, integral_deriv_eq_sub, norm_integral_le_of_norm_le_const, isProperMap_iff_isCompact_preimage, Fin.consLinearEquiv, LinearEquiv.toContinuousLinearEquiv and EuclideanSpace.norm_eq.
- dag.json shows no collision for the 8 proposed names and no accepted declaration with an identical type to reuse.
- All 8 child types elaborate. AllProof.lean compiles complete sorry-free proofs of all 8 children and of a declaration whose type is textually identical to the selected frozen type, using only propext, Classical.choice and Quot.sound.
- Simon 6.2.17–2.22 (book/chapter-06.txt:350–401) is the source of the decomposition: the slice form defining [[0,1]] × T, ∂([[0,1]] × T) = {1} × T − {0} × T − [[0,1]] × ∂T, and {p} × T(ω) = T(ω(p, ·)).

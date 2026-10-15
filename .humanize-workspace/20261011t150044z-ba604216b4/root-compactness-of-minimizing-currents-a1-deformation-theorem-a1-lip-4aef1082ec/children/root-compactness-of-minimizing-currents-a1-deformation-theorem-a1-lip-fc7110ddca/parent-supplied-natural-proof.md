# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.end_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5 (Simon 6.2.22, {p} × T(ω) = T(ω(p, ·)): the end slices of [[0,1]] × T). Fix N, k, s, ω, and let ω̃ := (ω : DifferentialForm (Euclid (N+1)) k), a test form (ω.property.1).
1. Coordinates. By sibling coords (Submission.cmcdt_lpo_slice_coords N), take L with L(t, y) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp y)) and ‖L(0, y)‖ = ‖y‖. Let J := (L : ℝ × ℝ^N →L[ℝ] ℝ^{N+1}).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)), so that J y = L(0, y), and let b := L(s, 0). Then b + J x = L((s, 0) + (0, x)) = L(s, x) for all x (map_add).
2. Properness. a(x) := b + J x is continuous. Let K ⊆ ℝ^{N+1} be compact. K is bounded, so K ⊆ closedBall(0, R) for some R (IsCompact.isBounded, Bornology.IsBounded.subset_closedBall). For x ∈ a⁻¹' K:
 ‖x‖ = ‖L(0, x)‖ = ‖J x‖ = ‖(b + J x) − b‖ ≤ ‖b + J x‖ + ‖b‖ ≤ R + ‖b‖.
 So a⁻¹' K is bounded. It is closed as the preimage of the closed set K under a continuous map, so in the proper space ℝ^N it is compact (Metric.isCompact_of_isClosed_isBounded). ℝ^{N+1} is Hausdorff and compactly coherent, so isProperMap_iff_isCompact_preimage shows that fun x => b + J x is a proper map.
3. The pull-back is a test form. By SimonGMT affinePullbackForm_isTestForm J b (with the properness of step 2) applied to the test form ω̃, ρ̃ := affinePullbackForm J b ω̃ is a test form. Explicitly ρ̃(x) = (ω̃(b + J x)).compContinuousLinearMap J. Since tsupport ρ̃ ⊆ univ, ρ := ⟨ρ̃, ⟨that, subset_univ _⟩⟩ ∈ TestFormOn univ k.
4. Values. For x and v: ρ̃(x)(v) = ω̃(b + J x)(J ∘ v) by compContinuousLinearMap_apply. By step 1 and the formula for L this is ω̃(L(s, x))(i ↦ L(0, v_i)) = ω̃(WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))(i ↦ WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))), which is the claim. □

## Key steps

1. With sibling coords set J := L ∘ inr and b := L(s, 0), so that b + Jx = L(s, x).
2. x ↦ b + Jx is proper: preimages of compact sets are closed and bounded because ‖x‖ = ‖Jx‖ ≤ ‖b + Jx‖ + ‖b‖ (isProperMap_iff_isCompact_preimage).
3. affinePullbackForm_isTestForm makes ρ := affinePullbackForm J b ω a test form.
4. ρ(x)(v) = ω(b + Jx)(J ∘ v) = ω(ι(s, x))(Jv).

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

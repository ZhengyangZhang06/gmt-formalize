# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.fiber_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 2 and 4 (Simon 6.2.17 with S = [[0,1]]: the slice form whose pairing with T defines [[0,1]] × T). Fix N, k, ω, and let ω̃ := (ω : DifferentialForm (Euclid (N+1)) (k+1)). Membership in TestFormOn univ (k+1) gives ContDiff ℝ ∞ ω̃ (ω.property.1.1) and HasCompactSupport ω̃ (ω.property.1.2).
1. Coordinates. By sibling coords (Submission.cmcdt_lpo_slice_coords N), take L with L(t, y) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp y)) and L(1, 0) = EuclideanSpace.single 0 1. Rewrite the goal right-to-left with these identities, so that ι(t, x) = L(t, x), Jv_i = L(0, v_i) and e₀ = L(1, 0). Let J := (L : ℝ × ℝ^N →L[ℝ] ℝ^{N+1}).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)); then J y = L(0, y) by definition.
2. Contraction. Define Φ : Λ^{k+1}(ℝ^{N+1})* →L[ℝ] Λ^k(ℝ^N)* as the composite of three continuous linear maps:
 - (ContinuousAlternatingMap.curryLeftLI).toContinuousLinearMap, γ ↦ γ.curryLeft;
 - ContinuousLinearMap.apply ℝ (Covector (Euclid (N+1)) k) (L(1, 0)), evaluation at L(1, 0);
 - ContinuousAlternatingMap.compContinuousLinearMapCLM J.
 For γ and v ∈ (ℝ^N)^k this gives Φ(γ)(v) = (γ.curryLeft L(1, 0))(J ∘ v) = γ(Matrix.vecCons L(1, 0) (J ∘ v)) = γ(Fin.cons L(1, 0) (i ↦ L(0, v_i))). This uses compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply and curryLeft_apply_apply; Matrix.vecCons is Fin.cons.
3. Smoothness. For p ∈ ℝ × ℝ^N let g(p) := Φ(ω̃(L p)). g is C^∞ as the composite of Φ.contDiff, ω̃ and L.contDiff. Define η̃(x) := ∫_0^1 g(t, x) dt ∈ Λ^k(ℝ^N)*. Covector (Euclid N) k is a complete real normed space in Type, so sibling param_integral (Submission.cmcdt_lpo_slice_param_integral N (Covector (Euclid N) k) g) shows that η̃ is C^∞.
4. Values. Fix x and v. t ↦ g(t, x) is continuous, hence interval integrable on [0, 1]. Evaluation at v (ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ v) is continuous linear, so it commutes with the interval integral (ContinuousLinearMap.intervalIntegral_comp_comm): η̃(x)(v) = ∫_0^1 g(t, x)(v) dt. By step 2 the integrand equals ω̃(L(t, x))(Fin.cons L(1, 0) (i ↦ L(0, v_i))) for every t (intervalIntegral.integral_congr). This is the first conjunct.
5. A compact set containing the support. Let K := {x | ∃ t ∈ [0, 1], L(t, x) ∈ tsupport ω̃}. Then K = (fun y => (L.symm y).2) '' (tsupport ω̃ ∩ (fun y => (L.symm y).1) ⁻¹' [0, 1]):
 - (⊆) if t ∈ [0, 1] and L(t, x) ∈ tsupport ω̃, then y := L(t, x) satisfies L.symm y = (t, x);
 - (⊇) if y ∈ tsupport ω̃ and (L.symm y).1 ∈ [0, 1], then (t, x) := L.symm y satisfies L(t, x) = y.
 tsupport ω̃ is compact because ω̃ has compact support. The preimage of [0, 1] under the continuous map fst ∘ L.symm is closed, so the intersection is compact (IsCompact.inter_right). Its image under the continuous map snd ∘ L.symm is therefore compact. Hence K is compact, and closed because ℝ^N is Hausdorff.
6. Support. Let x ∉ K. For every t ∈ uIcc 0 1 = [0, 1], L(t, x) ∉ tsupport ω̃, so ω̃(L(t, x)) = 0 (image_eq_zero_of_notMem_tsupport) and g(t, x) = Φ 0 = 0. Hence η̃(x) = ∫_0^1 0 dt = 0 (intervalIntegral.integral_congr). So support η̃ ⊆ K, and since K is closed, tsupport η̃ = closure (support η̃) ⊆ K (closure_minimal). This is the second conjunct.
7. Test form. tsupport η̃ is a closed subset of the compact set K, so it is compact (IsCompact.of_isClosed_subset), i.e. HasCompactSupport η̃. Together with step 3, η̃ is a test form, and tsupport η̃ ⊆ univ holds trivially. So η := ⟨η̃, ⟨⟨smoothness, compact support⟩, subset_univ _⟩⟩ ∈ TestFormOn univ k, and its underlying form η̃ satisfies steps 4 and 6. □

## Key steps

1. Rewrite with sibling coords and set J := L ∘ inr.
2. The contraction Φ = compContinuousLinearMapCLM J ∘ apply(e₀) ∘ curryLeftLI is continuous linear with Φ(γ)(v) = γ(Fin.cons e₀ (J ∘ v)).
3. g(p) := Φ(ω(L p)) is C^∞, so η(x) := ∫_0^1 g(t, x) dt is C^∞ by sibling param_integral (V = Covector (Euclid N) k).
4. Evaluation at v commutes with the interval integral (intervalIntegral_comp_comm), which gives the value formula.
5. K = (snd ∘ L⁻¹) '' (tsupport ω ∩ (fst ∘ L⁻¹)⁻¹[0, 1]) is compact; η vanishes off K, so tsupport η ⊆ K and η has compact support.

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

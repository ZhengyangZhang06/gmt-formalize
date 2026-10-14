# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.slice-a1.homotopy_succ-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6, (c1)–(c5) (Simon 6.2.19/2.21 at the level of forms: S_{dβ} = i_1^#β − i_0^#β − dS_β). Fix N, k, β, θ satisfying the hypothesis (H): θ̃(x')(u) = ∫_0^1 β̃(ι(t, x'))(e₀, Ju) dt for all x' and u ∈ (ℝ^N)^k, where β̃ := (β : DifferentialForm) and θ̃ := (θ : DifferentialForm). Fix x and v ∈ (ℝ^N)^{k+1}. β̃ and θ̃ are C^∞ because they are test forms (β.property.1.1, θ.property.1.1), hence differentiable.
1. Pointwise split. By sibling extderiv_split (Submission.cmcdt_lpo_slice_extDeriv_split N k β̃ applied to the differentiability of β̃), for every t:
 dβ̃(ι(t, x))(e₀, Jv) = deriv φ t − Σ_{j : Fin (k+1)} (−1)^j • D[x' ↦ β̃(ι(t, x'))(e₀, J(removeNth j v))](x)(v_j),
 where φ(s) := β̃(ι(s, x))(Jv). Replace the integrand by the right-hand side (intervalIntegral.integral_congr).
2. Coordinates. By sibling coords (Submission.cmcdt_lpo_slice_coords N), take L with L(s, y) = ι(s, y) and L(1, 0) = e₀, and rewrite (H) and the goal right-to-left with these identities. For u ∈ (ℝ^N)^k and p ∈ ℝ × ℝ^N put H_u(p) := β̃(L p)(Fin.cons L(1, 0) (i ↦ L(0, u_i))). H_u is C^∞: it is β̃ ∘ L followed by evaluation at a fixed tuple (ContinuousAlternatingMap.apply), a continuous linear map. By (H), (x' ↦ θ̃(x')(u)) = (x' ↦ ∫_0^1 H_u(t, x') dt) as functions (funext).
3. Derivative of the slice. Let D_u(t) := fderiv ℝ (x' ↦ H_u(t, x')) x ∈ L(ℝ^N, ℝ). By sibling param_integral (Submission.cmcdt_lpo_slice_param_integral N ℝ H_u), x' ↦ ∫_0^1 H_u(t, x') dt has derivative ∫_0^1 D_u(t) dt at x. By step 2, fderiv ℝ (x' ↦ θ̃(x')(u)) x = ∫_0^1 D_u(t) dt.
4. Continuity in t. x' ↦ (t, x') has derivative ι₂ := ContinuousLinearMap.inr ℝ ℝ (Euclid N), so by the chain rule D_u(t) = (fderiv ℝ H_u (t, x)).comp ι₂. fderiv ℝ H_u is continuous (ContDiff.continuous_fderiv), and A ↦ A.comp ι₂ is continuous linear ((ContinuousLinearMap.compL ℝ _ _ ℝ).flip ι₂). So t ↦ D_u(t) is continuous, hence interval integrable, and ContinuousLinearMap.intervalIntegral_apply gives (∫_0^1 D_u(t) dt)(w) = ∫_0^1 D_u(t)(w) dt for every w.
5. dθ̃. By exteriorDerivative_apply (θ̃ is differentiable at x), dθ̃(x)(v) = Σ_j (−1)^j • fderiv ℝ (x' ↦ θ̃(x')(removeNth j v)) x (v_j). By steps 3 and 4 this equals Σ_j (−1)^j • ∫_0^1 D_{removeNth j v}(t)(v_j) dt. After the rewriting of step 2, D_{removeNth j v}(t)(v_j) is by definition of H exactly the j-th summand of step 1, D[x' ↦ β̃(L(t, x'))(Fin.cons L(1, 0) (i ↦ L(0, (removeNth j v) i)))](x)(v_j).
6. Fundamental theorem of calculus. φ(s) = β̃(L(s, x))(i ↦ L(0, v_i)) is C^∞, as evaluation at a fixed tuple composed with β̃, L and s ↦ (s, x). So φ is differentiable and deriv φ is continuous (ContDiff.continuous_deriv). By intervalIntegral.integral_deriv_eq_sub, ∫_0^1 deriv φ t dt = φ(1) − φ(0).
7. Integration. Each summand t ↦ (−1)^j • D_{removeNth j v}(t)(v_j) is continuous by step 4 (Continuous.clm_apply, Continuous.const_smul), so the finite sum is continuous (continuous_finsetSum), and deriv φ is continuous. Apply intervalIntegral.integral_sub and intervalIntegral.integral_finsetSum, and pull out the constant (−1)^j with zsmul_eq_mul and intervalIntegral.integral_const_mul:
 ∫_0^1 [deriv φ t − Σ_j (−1)^j • D_j(t)(v_j)] dt = (φ(1) − φ(0)) − Σ_j (−1)^j • ∫_0^1 D_j(t)(v_j) dt.
 By step 5 the right-hand side is φ(1) − φ(0) − dθ̃(x)(v). Finally φ(1) = β̃(ι(1, x))(Jv) and φ(0) = β̃(ι(0, x))(Jv), which is (c). □

## Key steps

1. Replace the integrand using sibling extderiv_split: deriv φ t − Σ_j (−1)^j D_x[β(ι(t, ·))(e₀, J v̂_j)](x)(v_j).
2. With sibling coords define H_u(t, x') := β(L(t, x'))(e₀, Ju); the hypothesis says θ(·)(u) = ∫_0^1 H_u(t, ·) dt.
3. Sibling param_integral (V = ℝ) gives fderiv of θ(·)(u) at x as ∫_0^1 D_x H_u(t, x) dt; t ↦ D_x H_u(t, x) is continuous, so evaluation commutes with the integral.
4. exteriorDerivative_apply for θ gives dθ(x)(v) = Σ_j (−1)^j ∫_0^1 D_x H_{v̂_j}(t, x)(v_j) dt.
5. The FTC for φ(s) = β(ι(s, x))(Jv) and linearity of the interval integral give φ(1) − φ(0) − dθ(x)(v).

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

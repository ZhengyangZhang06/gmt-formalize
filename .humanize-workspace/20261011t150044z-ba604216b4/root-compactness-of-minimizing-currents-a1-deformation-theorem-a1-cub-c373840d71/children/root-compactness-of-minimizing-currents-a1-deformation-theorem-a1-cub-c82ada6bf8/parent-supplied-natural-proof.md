# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (Poincaré inequality for u via the limits σ ↓ 0, δ ↓ 0), run with the double-integral form of step 2 so that no means over Q_δ are needed; the final c is the mean u_{Q₁} = ∫_{Q₁} u, as in the parent proof. In Simon this is the BV Poincaré inequality Ch. 2, 2.7 (book/chapter-02.txt lines 629–661) as used for the first line of display (32) in the proof of Ch. 6, 5.1 (book/chapter-06.txt lines 1883–1892).

Notation (used throughout). m ∈ ℕ and n := m + 1 ≥ 1. ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with its Lebesgue measure (volume); y_i is the i-th coordinate. Q₁ := {y : 0 < y_i < 1 for all i}; for δ ∈ ℝ, Q_δ := {y : δ < y_i < 1 − δ for all i} (so Q_0 = Q₁). div G(x) := trace DG(x) (LinearMap.trace of fderiv). Integrals over a set are Lebesgue (Bochner) integrals of the restricted measure. Under the measure-preserving linear isometry Euclid n ≃ (Fin n → ℝ) (Mathlib EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp / PiLp.volume_preserving_ofLp) Q_δ corresponds to the box ∏_i (δ, 1 − δ), so vol(Q_δ) = (1 − 2δ)ⁿ for 0 ≤ δ < 1/2, vol(Q₁) = 1, and Q_δ = ∅ for δ ≥ 1/2. Each Q_δ is open, convex and bounded; for 0 ≤ δ' ≤ δ, Q_δ ⊆ Q_δ' ⊆ Q₁. "hyp(u, V)" abbreviates: ∫_{Q₁} u · div g ≤ V for every C^∞ (ContDiff ℝ (⊤ : ℕ∞)) map g : ℝⁿ → ℝⁿ with compact support, tsupport g ⊆ Q₁ and |g(y)| ≤ 1 for all y.

Sibling results used. smooth_approx (cmcdt_cbm_smooth_approx): for u integrable on Q₁ with hyp(u, V) and δ > 0 there are C¹ functions v_k with ∫_{Q_δ}‖Dv_k‖ ≤ V and ∫_{Q_δ}|v_k − u| → 0. smooth_poincare (cmcdt_cbm_smooth_poincare): for C¹ v and δ ≥ 0, ∫_{x∈Q_δ}∫_{y∈Q_δ}|v(x) − v(y)| dy dx ≤ K₀ ∫_{Q_δ}‖Dv‖ with K₀ := 2ⁿ√n = 2^{m+1}√(m+1).

Fix u integrable on Q₁ and V with hyp(u, V).

0. V ≥ 0: apply hyp to g ≡ 0 (C^∞, compact support, tsupport ∅ ⊆ Q₁, |0| ≤ 1; D0 = 0, trace 0 = 0): 0 = ∫_{Q₁} u·0 ≤ V.

1. Finiteness. Since u is integrable on Q₁ and vol(Q₁) = 1 < ∞, the function (x, y) ↦ |u(x) − u(y)| ≤ |u(x)| + |u(y)| is integrable on Q₁ × Q₁ (product of the restricted measures; it is a.e.-strongly measurable as a composition of the a.e.-strongly measurable functions (x, y) ↦ u(x) and (x, y) ↦ u(y)). For every x and every δ ≥ 0 the function y ↦ |u(x) − u(y)| is integrable on Q_δ ⊆ Q₁ (u is integrable there and constants are integrable on sets of finite measure), so h_δ(x) := ∫_{Q_δ} |u(x) − u(y)| dy is finite, 0 ≤ h_δ(x) ≤ |u(x)| + ∫_{Q₁}|u|, and by Fubini x ↦ h_δ(x) is a.e.-strongly measurable on Q₁; hence h_δ is integrable on Q₁. Put D(δ) := ∫_{Q_δ} h_δ(x) dx = ∫_{x∈Q_δ}∫_{y∈Q_δ} |u(x) − u(y)| dy dx.

2. D(δ) ≤ K₀ V for every δ ∈ (0, 1/2). Fix such δ and take v_k from smooth_approx (δ > 0). Each v_k is continuous, hence bounded on the bounded set Q_δ, so v_k − u is integrable on Q_δ and ε_k := ∫_{Q_δ}|v_k − u| → 0 is the L¹(Q_δ) distance. By smooth_poincare (δ ≥ 0), D_k := ∫_{x∈Q_δ}∫_{y∈Q_δ}|v_k(x) − v_k(y)| dy dx ≤ K₀∫_{Q_δ}‖Dv_k‖ ≤ K₀V. For all x, y: |u(x) − u(y)| ≤ |v_k(x) − v_k(y)| + |u(x) − v_k(x)| + |v_k(y) − u(y)|. Integrating in y over Q_δ (all three terms are integrable in y) and then in x over Q_δ, and using vol(Q_δ) ≤ 1: D(δ) ≤ D_k + vol(Q_δ) ε_k + vol(Q_δ) ε_k ≤ K₀V + 2ε_k. Letting k → ∞ gives D(δ) ≤ K₀V.

3. D(0) ≤ K₀ V. Let δ_j := 1/(j + 3) for j ∈ ℕ; then δ_j ∈ (0, 1/2), δ_j ↓ 0, and every x ∈ Q₁ lies in Q_{δ_j} for all large j. For x ∈ Q₁, 1_{Q_{δ_j}}(y)|u(x) − u(y)| → 1_{Q₁}(y)|u(x) − u(y)| for every y ∈ Q₁, dominated by |u(x) − u(y)|, which is integrable in y over Q₁ for every x (step 1); so by dominated convergence h_{δ_j}(x) → h_0(x) for every x ∈ Q₁. Moreover 0 ≤ 1_{Q_{δ_j}}(x) h_{δ_j}(x) ≤ h_0(x) with h_0 integrable on Q₁, and 1_{Q_{δ_j}}(x) h_{δ_j}(x) → h_0(x) for every x ∈ Q₁. By dominated convergence D(δ_j) = ∫_{Q₁} 1_{Q_{δ_j}} h_{δ_j} → ∫_{Q₁} h_0 = D(0). Since D(δ_j) ≤ K₀V for all j by step 2, D(0) ≤ K₀V.

4. Choice of c. Let c := ∫_{Q₁} u. Since vol(Q₁) = 1, for a.e. x ∈ Q₁: u(x) − c = ∫_{Q₁}(u(x) − u(y)) dy, hence |u(x) − c| ≤ ∫_{Q₁}|u(x) − u(y)| dy = h_0(x). Integrating over Q₁: ∫_{Q₁}|u − c| ≤ D(0) ≤ K₀V = 2ⁿ√n V ≤ 2^{n+1}√n V, the last step because V ≥ 0 (step 0). With n = m + 1, 2^{n+1}√n = 2^{m+2}√(m + 1). ∎

## Key steps

1. V ≥ 0 from g ≡ 0; |u(x) − u(y)| is integrable on Q₁ × Q₁, so D(δ) := ∫_{Q_δ}∫_{Q_δ}|u(x) − u(y)| is finite.
2. For δ ∈ (0, 1/2): smooth_approx gives v_k, smooth_poincare gives D_k ≤ 2ⁿ√n V, and D(δ) ≤ D_k + 2∫_{Q_δ}|v_k − u|; letting k → ∞, D(δ) ≤ 2ⁿ√n V.
3. δ_j = 1/(j+3) ↓ 0 and dominated convergence give D(0) = ∫_{Q₁}∫_{Q₁}|u(x) − u(y)| ≤ 2ⁿ√n V.
4. With c = ∫_{Q₁}u (vol Q₁ = 1), ∫_{Q₁}|u − c| ≤ D(0) ≤ 2ⁿ√n V ≤ 2^{n+1}√n V.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n 'cmcdt_cbm' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (902 nodes) for the seven proposed lean names and all theorems fields (no collision)`
- `rg -n -i 'poincar[eé] inequality|poincare_ineq|median|trace inequality|mollif|bounded variation|IsLocallyBV|integral_divergence' local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n -i 'mollif|poincar[eé]_ineq|poincare inequality|median|integral_divergence|divergence theorem|trace_ineq|convolution_tendsto|tendsto_convolution' lake-packages-25730c7c/simongmt/Poincare -g '*.lean'`
- `rg -n 'theorem (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable|integral_bilinear_fderiv_right_eq_neg_left_of_integrable|integral_fderiv_eq_zero|integral_lineDeriv_eq_zero)' mathlib/Mathlib`
- `rg -n 'theorem (_root_\.)?HasCompactSupport\.(hasFDerivAt_convolution_right|hasFDerivAt_convolution_left|contDiff_convolution_right|contDiff_convolution_left|fderiv_convolution_right)' mathlib/Mathlib`
- `rg -n 'convolution_tendsto|tendsto_convolution|eLpNorm.*convolution|convolution.*eLpNorm|integral_norm_convolution|norm_convolution_le' mathlib/Mathlib`
- `rg -n 'exists_hasCompactSupport_integral_sub_le|exists_hasCompactSupport_eLpNorm_sub_le|exists_continuous_integral_sub_le' mathlib/Mathlib`
- `rg -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' mathlib/Mathlib`
- `rg -n 'theorem (EuclideanSpace\.)?volume_preserving|PiLp.volume_preserving_ofLp|theorem volume_preserving_piFinSuccAbove|theorem integral_comp_smul\b|theorem setIntegral_comp_smul_of_pos|addHaar_preimage_smul|theorem support_fderiv_subset|lemma trace_eq_sum_inner|theorem volume_pi_Ioo' mathlib/Mathlib`
- `lake env lean /tmp/cbm-decomp/build/ExactTypes.lean (seven child types elaborate after import GMT.Ch07.Submission in the contract namespace/opens); lake env lean /tmp/cbm-decomp/PPCheck.lean (iterated set integrals as intended; ContDiff ℝ (⊤ : ℕ∞) is C^∞, not ω; C^∞ → C¹ via of_le); lake env lean /tmp/cbm-decomp/build/AssemblyExact.lean (frozen parent type from the exact child types; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cbm-decomp/imports/Avail.lean and /tmp/cbm-decomp/imports/Names2.lean (which cited lemmas lie in the import closure of GMT.Ch07.Submission); lake env lean /tmp/cbm-decomp/imports/WithImports.lean (with LineDeriv.IntegrationByParts, BumpFunction.Normed, BumpFunction.Convolution, ContinuousMapDense, Integral.DivergenceTheorem and Gradient.Basic imported, every cited lemma and HasContDiffBump (Euclid n) resolve and the seven child types elaborate unchanged)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean over accepted DAG nodes (17 accepted nodes add imports to Submission.lean, e.g. Mathlib.MeasureTheory.Function.ContinuousMapDense); read verifier/gmt-compare.py candidate_inputs (only the frozen contract and build inputs are byte-checked)`
- `grep -n '(26)|(27)|(28)|(29)|(30)|(31)|(32)|(33)|2.35|2.36|2.37' book/chapter-06.txt; grep -n '^2\.[5-9] |Poincar' book/chapter-02.txt (Simon Ch. 6 proof of 5.1 displays (26)-(36) at chapter-06.txt lines 1841-1913; Ch. 2, 2.5 and 2.7-2.9 at chapter-02.txt lines 543-676)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/cbm-decomp/build/ExactTypes.lean`
- `/tmp/cbm-decomp/build/AssemblyExact.lean`
- `/tmp/cbm-decomp/PPCheck.lean`
- `/tmp/cbm-decomp/imports/WithImports.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean.

Nothing in the snapshot can be reused for this node:
- The only BV Poincaré and BV extension statements are the Ch02 contracts BVPoincare (Simon 2.7) and BVExtensionEstimate (2.8). They are unsolved (main_theorem := by sorry), belong to another chapter, and cannot be imported into Ch07.
- SimonGMT Chapter02/BV.lean has only definitions (IsLocallyBV, bvVariationOn). Chapter08 has only an a.e. mollifier convergence.
- Mathlib has no BV Poincaré, BV trace inequality, integer median or L¹ convergence of mollifiers.

Mathlib does supply every tool the child proofs cite:
- integration by parts against a constant;
- convolution smoothness and derivatives (already in the Submission closure);
- normed bumps and dist_normed_convolution_le;
- density of continuous compactly supported functions in L¹ (ContinuousMapDense);
- the box divergence theorem;
- Euclidean and pi volume preservation and piFinSuccAbove Fubini;
- the scaling change of variables;
- support_fderiv_subset and trace_eq_sum_inner.

Six of these modules are outside the frozen Submission import closure. Importing them works: all cited lemmas resolve, and the seven child types elaborate unchanged. Accepted nodes of this run already add imports this way, and each affected child proof carries an explicit import note.

No cmcdt_cbm_* name exists in the snapshot or the DAG. The parent's frozen type is derived in Lean from the exact child types integral_div_zero, bv_poincare, integer_median and bv_trace, using standard axioms only.

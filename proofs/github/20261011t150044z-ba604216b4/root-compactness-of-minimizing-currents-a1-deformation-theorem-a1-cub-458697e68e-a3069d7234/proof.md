# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (gradient bound for the mollified u_σ by duality with the fields φ̌_σ ∗ g, which are supported in Q₁) together with the convergence u_σ → u·1_{Q₁} in L¹ used in its steps 3 and 5. The duality is applied directly to a bounded measurable field g (the smoothing is carried by φ̌_σ), so the smooth cut-offs g_k and the monotone-convergence step of the parent proof are not needed. In Simon this is the mollification fact Ch. 2, 2.5 (book/chapter-02.txt lines 543–545) as used in the proof of Ch. 2, 2.7 (lines 651–661).

Notation (used throughout). m ∈ ℕ and n := m + 1 ≥ 1. ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with its Lebesgue measure (volume); y_i is the i-th coordinate. Q₁ := {y : 0 < y_i < 1 for all i}; for δ ∈ ℝ, Q_δ := {y : δ < y_i < 1 − δ for all i} (so Q_0 = Q₁). div G(x) := trace DG(x) (LinearMap.trace of fderiv). Integrals over a set are Lebesgue (Bochner) integrals of the restricted measure. Under the measure-preserving linear isometry Euclid n ≃ (Fin n → ℝ) (Mathlib EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp / PiLp.volume_preserving_ofLp) Q_δ corresponds to the box ∏_i (δ, 1 − δ), so vol(Q_δ) = (1 − 2δ)ⁿ for 0 ≤ δ < 1/2, vol(Q₁) = 1, and Q_δ = ∅ for δ ≥ 1/2. Each Q_δ is open, convex and bounded; for 0 ≤ δ' ≤ δ, Q_δ ⊆ Q_δ' ⊆ Q₁. "hyp(u, V)" abbreviates: ∫_{Q₁} u · div g ≤ V for every C^∞ (ContDiff ℝ (⊤ : ℕ∞)) map g : ℝⁿ → ℝⁿ with compact support, tsupport g ⊆ Q₁ and |g(y)| ≤ 1 for all y.

Fix u, V with u integrable on Q₁ and hyp(u, V), and fix δ > 0.

0. V ≥ 0: the map g ≡ 0 is C^∞, has compact support, tsupport 0 = ∅ ⊆ Q₁ and |0| ≤ 1; D0 = 0 and trace 0 = 0, so hyp gives 0 = ∫_{Q₁} u · 0 ≤ V.

1. Mollifier. Fix φ : ℝⁿ → ℝ, C^∞, φ ≥ 0, ∫φ = 1, with support in the open unit ball (e.g. the normalized Mathlib ContDiffBump with rIn = 1/2, rOut = 1). For σ > 0 put φ_σ(z) := σ^{−n} φ(z/σ): φ_σ is C^∞, φ_σ ≥ 0, ∫φ_σ = 1, support φ_σ ⊆ B_σ(0) := {|z| < σ}, and A_σ := sup_z ‖Dφ_σ(z)‖ < ∞ (Dφ_σ is continuous with compact support). (One may equally take the normalized ContDiffBump with rIn = σ/2, rOut = σ.) Let ū := 1_{Q₁} u, which is integrable on ℝⁿ, and u_σ(x) := ∫ ū(y) φ_σ(x − y) dy (the convolution ū ⋆ φ_σ).
Import note: the convolution lemmas HasCompactSupport.contDiff_convolution_right/left and HasCompactSupport.hasFDerivAt_convolution_right/left used below are already available under `import GMT.Ch07.Submission`, but ContDiffBump.normed (Mathlib.Analysis.Calculus.BumpFunction.Normed), ContDiffBump.dist_normed_convolution_le (Mathlib.Analysis.Calculus.BumpFunction.Convolution), Integrable.exists_hasCompactSupport_integral_sub_le (Mathlib.MeasureTheory.Function.ContinuousMapDense) and, if used, gradient (Mathlib.Analysis.Calculus.Gradient.Basic; InnerProductSpace.toDual, already available, suffices) are not. Add these imports to GMT/Ch07/Submission.lean (accepted nodes of this run already import Mathlib.MeasureTheory.Function.ContinuousMapDense); with them the instances HasContDiffBump (Euclid n), IsAddHaarMeasure, Measure.Regular and IsNegInvariant for volume on Euclid n all resolve, and the frozen child types still elaborate unchanged.

2. Smoothness and derivative of u_σ. Since φ_σ is C^∞ with compact support and ū is locally integrable, u_σ is C^∞ and Du_σ(x)h = ∫ ū(y) Dφ_σ(x − y)h dy for all x, h (differentiation under the integral sign; Mathlib HasCompactSupport.contDiff_convolution_right and HasCompactSupport.hasFDerivAt_convolution_right with L = ContinuousLinearMap.lsmul ℝ ℝ). Also |u_σ(x)| ≤ (sup φ_σ) ∫|ū|, so u_σ is bounded.

3. Gradient bound: for 0 < σ < δ, ∫_{Q_δ} ‖Du_σ‖ ≤ V.
 (a) Let ∇u_σ(x) ∈ ℝⁿ be the gradient (Du_σ(x)h = ⟨∇u_σ(x), h⟩, |∇u_σ(x)| = ‖Du_σ(x)‖; it is continuous). Define g(x) := ∇u_σ(x)/|∇u_σ(x)| if x ∈ Q_δ and ∇u_σ(x) ≠ 0, and g(x) := 0 otherwise. Then g is Borel measurable, |g| ≤ 1, g = 0 off Q_δ (so g is integrable on ℝⁿ), and Du_σ(x)(g(x)) = 1_{Q_δ}(x) ‖Du_σ(x)‖ for every x.
 (b) Define g̃(y) := ∫ φ_σ(x − y) g(x) dx. With φ̌_σ(z) := φ_σ(−z) (C^∞, compact support) this is the convolution g̃(y) = ∫ φ̌_σ(y − x) g(x) dx = (φ̌_σ ⋆ g)(y). (i) g̃ is C^∞ and Dg̃(y)h = ∫ (Dφ̌_σ(y − x)h) g(x) dx = −∫ (Dφ_σ(x − y)h) g(x) dx (Mathlib HasCompactSupport.contDiff_convolution_left and HasCompactSupport.hasFDerivAt_convolution_left; chain rule Dφ̌_σ(z) = −Dφ_σ(−z)). Taking the trace in the standard orthonormal basis (trace T = Σ_j ⟨e_j, T e_j⟩): div g̃(y) = −∫ Σ_j (Dφ_σ(x − y)e_j) g_j(x) dx = −∫ Dφ_σ(x − y)(g(x)) dx. (ii) |g̃(y)| ≤ ∫ φ_σ(x − y)|g(x)| dx ≤ ∫ φ_σ = 1. (iii) If g̃(y) ≠ 0 there is x ∈ Q_δ with φ_σ(x − y) ≠ 0, i.e. |x − y| < σ; then |x_i − y_i| < σ, so δ − σ < y_i < 1 − δ + σ for all i. Hence tsupport g̃ ⊆ P := {y : δ − σ ≤ y_i ≤ 1 − δ + σ for all i}, a closed bounded (hence compact) set with P ⊆ Q₁ because 0 < δ − σ and 1 − δ + σ < 1. So g̃ has compact support and tsupport g̃ ⊆ Q₁. The same holds for −g̃, and D(−g̃) = −Dg̃, div(−g̃) = −div g̃.
 (c) Applying hyp(u, V) to −g̃: −∫_{Q₁} u · div g̃ ≤ V.
 (d) Identity. The function (x, y) ↦ ū(y) Dφ_σ(x − y)(g(x)) is a.e.-strongly measurable on ℝⁿ × ℝⁿ and bounded in absolute value by A_σ |ū(y)| 1_{Q_δ}(x), which is integrable on ℝⁿ × ℝⁿ (its integral is A_σ ‖ū‖₁ vol(Q_δ) < ∞). By step 2 and Fubini, ∫_{ℝⁿ} Du_σ(x)(g(x)) dx = ∫_x ∫_y ū(y) Dφ_σ(x − y)(g(x)) dy dx = ∫_y ū(y) (∫_x Dφ_σ(x − y)(g(x)) dx) dy = ∫_y ū(y)(−div g̃(y)) dy = −∫_{Q₁} u · div g̃, by (b)(i) and ū = 1_{Q₁}u.
 (e) By (a), (d), (c): ∫_{Q_δ} ‖Du_σ‖ = ∫_{ℝⁿ} Du_σ(x)(g(x)) dx = −∫_{Q₁} u · div g̃ ≤ V. (If δ ≥ 1/2 then Q_δ = ∅, g = g̃ = 0, and the bound reads 0 ≤ V, which is step 0.)

4. L¹ convergence: ∫_{ℝⁿ} |u_σ − ū| → 0 as σ → 0⁺ (continuity of translation in L¹).
 (a) L¹ contraction. For f integrable on ℝⁿ and f_σ := f ⋆ φ_σ, Tonelli and ∫φ_σ = 1 give ∫|f_σ| ≤ ∫∫ |f(y)| φ_σ(x − y) dy dx = ∫|f|. By linearity of convolution, ∫|u_σ − h_σ| ≤ ∫|ū − h| for every integrable h, where h_σ := h ⋆ φ_σ.
 (b) Continuous compactly supported h. Let h be continuous with compact support S. Then h is uniformly continuous; put ω(σ) := sup{|h(x − z) − h(x)| : x ∈ ℝⁿ, |z| ≤ σ}, so ω(σ) → 0 as σ → 0. Since h_σ(x) − h(x) = ∫ φ_σ(z)(h(x − z) − h(x)) dz, |h_σ(x) − h(x)| ≤ ω(σ) for all x (Mathlib ContDiffBump.dist_normed_convolution_le gives exactly this bound for normed bumps). For σ ≤ 1, h_σ − h vanishes outside the compact set S₁ := {x : dist(x, S) ≤ 1}. Hence ∫|h_σ − h| ≤ vol(S₁) ω(σ) → 0.
 (c) Given ε > 0 choose h continuous with compact support and ∫|ū − h| < ε (density; Mathlib Integrable.exists_hasCompactSupport_integral_sub_le). Then ∫|u_σ − ū| ≤ ∫|u_σ − h_σ| + ∫|h_σ − h| + ∫|h − ū| ≤ 2ε + ∫|h_σ − h|, so limsup_{σ→0⁺} ∫|u_σ − ū| ≤ 2ε. As ε > 0 is arbitrary, ∫|u_σ − ū| → 0.

5. Conclusion. Put σ_k := δ/(k + 2) (so 0 < σ_k < δ and σ_k → 0) and v_k := u_{σ_k}. By step 2 each v_k is C^∞, in particular C¹ (ContDiff ℝ 1). By step 3, ∫_{Q_δ} ‖Dv_k‖ ≤ V for every k. Since Q_δ ⊆ Q₁ and ū = u on Q₁, and v_k is bounded while u is integrable on Q_δ (so v_k − u is integrable on Q_δ), 0 ≤ ∫_{Q_δ}|v_k − u| = ∫_{Q_δ}|v_k − ū| ≤ ∫_{ℝⁿ}|u_{σ_k} − ū| → 0 by step 4. Hence ∫_{Q_δ}|v_k − u| → 0 as k → ∞. ∎

## Key steps

1. V ≥ 0 from the test field g ≡ 0.
2. u_σ := (1_{Q₁}u) ⋆ φ_σ is C^∞ with Du_σ(x)h = ∫ ū(y) Dφ_σ(x − y)h dy.
3. For σ < δ, with g := 1_{Q_δ}∇u_σ/|∇u_σ| and g̃ := φ̌_σ ⋆ g (C^∞, |g̃| ≤ 1, tsupport in a compact subset of Q₁), Fubini gives ∫_{Q_δ}‖Du_σ‖ = −∫_{Q₁} u div g̃ ≤ V.
4. u_σ → 1_{Q₁}u in L¹(ℝⁿ) by L¹ contraction plus density of continuous compactly supported functions.
5. v_k := u_{δ/(k+2)} are C¹, satisfy the gradient bound and converge to u in L¹(Q_δ).

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

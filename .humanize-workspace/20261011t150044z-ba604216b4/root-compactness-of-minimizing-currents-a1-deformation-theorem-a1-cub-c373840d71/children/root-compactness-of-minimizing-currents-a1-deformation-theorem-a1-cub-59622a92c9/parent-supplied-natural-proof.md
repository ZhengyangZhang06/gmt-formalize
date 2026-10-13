# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (trace estimate; limits σ ↓ 0, then δ ↓ 0), with the mollified functions supplied by the sibling smooth_approx and the smooth estimate by the sibling smooth_trace. In Simon this replaces the appeal to Ch. 2, 2.8–2.9 (book/chapter-02.txt lines 663–676) for the second line of display (32) in the proof of Ch. 6, 5.1 (book/chapter-06.txt lines 1883–1892).

Notation (used throughout). m ∈ ℕ and n := m + 1 ≥ 1. ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with its Lebesgue measure (volume); y_i is the i-th coordinate. Q₁ := {y : 0 < y_i < 1 for all i}; for δ ∈ ℝ, Q_δ := {y : δ < y_i < 1 − δ for all i} (so Q_0 = Q₁). div G(x) := trace DG(x) (LinearMap.trace of fderiv). Integrals over a set are Lebesgue (Bochner) integrals of the restricted measure. Under the measure-preserving linear isometry Euclid n ≃ (Fin n → ℝ) (Mathlib EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp / PiLp.volume_preserving_ofLp) Q_δ corresponds to the box ∏_i (δ, 1 − δ), so vol(Q_δ) = (1 − 2δ)ⁿ for 0 ≤ δ < 1/2, vol(Q₁) = 1, and Q_δ = ∅ for δ ≥ 1/2. Each Q_δ is open, convex and bounded; for 0 ≤ δ' ≤ δ, Q_δ ⊆ Q_δ' ⊆ Q₁. "hyp(u, V)" abbreviates: ∫_{Q₁} u · div g ≤ V for every C^∞ (ContDiff ℝ (⊤ : ℕ∞)) map g : ℝⁿ → ℝⁿ with compact support, tsupport g ⊆ Q₁ and |g(y)| ≤ 1 for all y.

Sibling results used. smooth_approx (cmcdt_cbm_smooth_approx): for w integrable on Q₁ with hyp(w, V) and δ > 0 there are C¹ functions v_k with ∫_{Q_δ}‖Dv_k‖ ≤ V and ∫_{Q_δ}|v_k − w| → 0. smooth_trace (cmcdt_cbm_smooth_trace): for C¹ v, C¹ G with |G| ≤ 1 and 0 ≤ δ ≤ 1/4, |∫_{Q_δ} v div G| ≤ (2n + 1)∫_{Q_δ}‖Dv‖ + 4n∫_{Q_δ}|v|.

Fix w integrable on Q₁ with hyp(w, V), and G C¹ with |G| ≤ 1.

0. Boundedness of div G. DG is continuous and A ↦ trace A is linear on the finite-dimensional space L(ℝⁿ, ℝⁿ), so div G is continuous; it is therefore bounded on the compact set [0, 1]ⁿ ⊇ Q₁: |div G| ≤ M on Q₁ for some M ≥ 0. Hence w · div G is integrable on Q₁ and on every Q_δ ⊆ Q₁ (|w div G| ≤ M|w|).

1. Fix δ ∈ (0, 1/4] and take v_k from smooth_approx (δ > 0). Each v_k is continuous, hence bounded on the bounded set Q_δ; so v_k, v_k div G and v_k − w are integrable on Q_δ and ε_k := ∫_{Q_δ}|v_k − w| → 0. By smooth_trace (0 ≤ δ ≤ 1/4): |∫_{Q_δ} v_k div G| ≤ (2n + 1)∫_{Q_δ}‖Dv_k‖ + 4n∫_{Q_δ}|v_k| ≤ (2n + 1)V + 4n∫_{Q_δ}|v_k|.

2. Limit k → ∞. |∫_{Q_δ} v_k div G − ∫_{Q_δ} w div G| ≤ ∫_{Q_δ}|v_k − w||div G| ≤ M ε_k → 0 and |∫_{Q_δ}|v_k| − ∫_{Q_δ}|w|| ≤ ε_k → 0. Passing to the limit in the inequality of step 1: |∫_{Q_δ} w div G| ≤ (2n + 1)V + 4n∫_{Q_δ}|w| ≤ (2n + 1)V + 4n∫_{Q₁}|w| (Q_δ ⊆ Q₁, |w| ≥ 0).

3. Limit δ ↓ 0. Let δ_j := 1/(j + 4) ∈ (0, 1/4], δ_j ↓ 0; every point of Q₁ lies in Q_{δ_j} for all large j. The functions 1_{Q_{δ_j}} w div G converge pointwise on Q₁ to w div G and are dominated by M|w|, which is integrable on Q₁. By dominated convergence, ∫_{Q_{δ_j}} w div G → ∫_{Q₁} w div G. Each term satisfies the bound of step 2, hence so does the limit: |∫_{Q₁} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w| = (2(m + 1) + 1)V + 4(m + 1)∫_{Q₁}|w|. ∎

## Key steps

1. div G is continuous, hence bounded by M on the closed unit cube.
2. For δ ∈ (0, 1/4]: smooth_approx gives v_k and smooth_trace gives |∫_{Q_δ} v_k div G| ≤ (2n + 1)V + 4n∫_{Q_δ}|v_k|.
3. L¹(Q_δ) convergence and |div G| ≤ M pass this to w: |∫_{Q_δ} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w|.
4. Dominated convergence as δ ↓ 0 gives the bound on Q₁.

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

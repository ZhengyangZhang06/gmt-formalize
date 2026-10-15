# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (the supplied proof of dimred_mbl_dt_cube_bv_median: trace estimate |∫_{Q₁} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w|, with the limits σ ↓ 0 and then δ ↓ 0), with the mollified functions supplied by the sibling smooth_approx and the smooth estimate by the sibling smooth_trace; G need only be C¹ (the parent applies it to C^∞ fields). In Simon this replaces the appeal to Ch. 2, 2.8–2.9 (book/chapter-02.txt lines 663–676) for the second line of display (32) in the proof of Ch. 6, 5.1 (book/chapter-06.txt lines 1883–1892).

Notation (used throughout). m ∈ ℕ and n := m + 1 ≥ 1. ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with its Lebesgue measure (volume); y_i is the i-th coordinate and e_1, …, e_n is the standard orthonormal basis. Q₁ := {y : 0 < y_i < 1 for all i}; for δ ∈ ℝ, Q_δ := {y : δ < y_i < 1 − δ for all i} (so Q_0 = Q₁). div G(x) := trace DG(x) (LinearMap.trace of fderiv ℝ G x, viewed as a linear map). For v : ℝⁿ → ℝ, ‖Dv(x)‖ is the operator norm of fderiv ℝ v x, which equals the Euclidean length |∇v(x)| of the gradient. Integrals over a set are Bochner integrals for the restricted Lebesgue measure. Under the measure-preserving, coordinate-preserving continuous linear equivalence WithLp.ofLp : Euclid n ≃ (Fin n → ℝ) (Mathlib PiLp.volume_preserving_ofLp / EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp; it is not an isometry for the sup norm of Fin n → ℝ, and no isometry property is used) Q_δ corresponds to the box ∏_i (δ, 1 − δ); hence vol(Q_δ) = (1 − 2δ)ⁿ for 0 ≤ δ < 1/2, vol(Q₁) = 1, and Q_δ = ∅ for δ ≥ 1/2. Each Q_δ is open, convex and bounded, and Q_δ ⊆ Q_δ' ⊆ Q₁ for 0 ≤ δ' ≤ δ. "hyp(u, V)" abbreviates: ∫_{Q₁} u · div g ≤ V for every C^∞ (ContDiff ℝ (⊤ : ℕ∞)) map g : ℝⁿ → ℝⁿ with compact support, tsupport g ⊆ Q₁ and |g(y)| ≤ 1 for all y.

Sibling results used. smooth_approx (dimred_mbl_dt_cbm_smooth_approx): for w integrable on Q₁ with hyp(w, V) and δ > 0 there are C¹ functions v_k with ∫_{Q_δ}‖Dv_k‖ ≤ V for all k and ∫_{Q_δ}|v_k − w| → 0. smooth_trace (dimred_mbl_dt_cbm_smooth_trace): for C¹ v, C¹ G with |G| ≤ 1 and 0 ≤ δ ≤ 1/4, |∫_{Q_δ} v div G| ≤ (2n + 1)∫_{Q_δ}‖Dv‖ + 4n∫_{Q_δ}|v|.

Fix w integrable on Q₁ with hyp(w, V), and G C¹ with |G| ≤ 1.

0. Boundedness of div G. DG is continuous and A ↦ trace A is linear on the finite-dimensional space L(ℝⁿ, ℝⁿ), so div G is continuous; it is therefore bounded on the compact set [0, 1]ⁿ ⊇ Q₁: |div G| ≤ M on Q₁ for some M ≥ 0. Hence w · div G is integrable on Q₁ and on every Q_δ ⊆ Q₁ (it is a.e.-strongly measurable and |w div G| ≤ M|w|).

1. Fix δ ∈ (0, 1/4] and take v_k from smooth_approx (δ > 0). Each v_k is continuous, hence bounded on the bounded set Q_δ; so v_k, v_k div G and v_k − w are integrable on Q_δ, and ε_k := ∫_{Q_δ}|v_k − w| → 0. By smooth_trace (0 ≤ δ ≤ 1/4) and 2n + 1 > 0: |∫_{Q_δ} v_k div G| ≤ (2n + 1)∫_{Q_δ}‖Dv_k‖ + 4n∫_{Q_δ}|v_k| ≤ (2n + 1)V + 4n∫_{Q_δ}|v_k|.

2. Limit k → ∞. |∫_{Q_δ} v_k div G − ∫_{Q_δ} w div G| ≤ ∫_{Q_δ}|v_k − w||div G| ≤ Mε_k → 0, and |∫_{Q_δ}|v_k| − ∫_{Q_δ}|w|| ≤ ε_k → 0. Passing to the limit in the inequality of step 1: |∫_{Q_δ} w div G| ≤ (2n + 1)V + 4n∫_{Q_δ}|w| ≤ (2n + 1)V + 4n∫_{Q₁}|w| (Q_δ ⊆ Q₁, |w| ≥ 0).

3. Limit δ ↓ 0. Let δ_j := 1/(j + 4) ∈ (0, 1/4], δ_j ↓ 0; every point of Q₁ lies in Q_{δ_j} for all large j. The functions 1_{Q_{δ_j}}w div G converge pointwise on Q₁ to w div G and are dominated by M|w|, which is integrable on Q₁. By dominated convergence, ∫_{Q_{δ_j}} w div G → ∫_{Q₁} w div G. Each term satisfies the bound of step 2, hence so does the limit: |∫_{Q₁} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w| = (2(m + 1) + 1)V + 4(m + 1)∫_{Q₁}|w|. ∎

## Key steps

1. div G is continuous, hence bounded by M on the closed unit cube, so w div G is integrable on Q₁.
2. For δ ∈ (0, 1/4]: smooth_approx gives v_k and smooth_trace gives |∫_{Q_δ} v_k div G| ≤ (2n + 1)V + 4n∫_{Q_δ}|v_k|.
3. L¹(Q_δ) convergence and |div G| ≤ M pass this to w: |∫_{Q_δ} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w|.
4. Dominated convergence as δ ↓ 0 gives the bound on Q₁.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5d…, mathlib_commit 25730c7c759d…); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `rg -n -i 'poincar|median|BVPoincare|BVExtension|integral_div|divergence' SNAPSHOT/project/GMT -g '*.lean'; rg -n '^def |^theorem ' SNAPSHOT/project/GMT/Ch02/Contract.lean (BVPoincare, BVExtensionEstimate are unproved Props under main_theorem := by sorry; Ch07 does not import Ch02); rg -n '^theorem |^lemma ' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean (no Poincaré or trace inequality)`
- `rg -n -i -l 'poincare inequality|poincaré inequality' SNAPSHOT/mathlib/Mathlib -g '*.lean' (no match)`
- `rg -l over SNAPSHOT/mathlib/Mathlib for: theorem integral_divergence_of_hasFDerivAt_off_countable, integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, _root_.HasCompactSupport.contDiff_convolution_left/right, _root_.HasCompactSupport.hasFDerivAt_convolution_left/right, integral_normed, dist_normed_convolution_le, Integrable.exists_hasCompactSupport_integral_sub_le, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, trace_eq_sum_inner, exists_least_of_bdd, setIntegral_comp_smul_of_pos, support_fderiv_subset, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_eq_zero_of_hasDerivAt_of_integrable, integral_eq_sub_of_hasDerivAt, tendsto_setIntegral_of_monotone, integral_prod, MeasurePreserving.setIntegral_preimage_emb, convolution_flip, AEStronglyMeasurable.integral_prod_right' (all found)`
- `grep -n '^import\|^public import' on Mathlib Analysis/Calculus/BumpFunction/{Convolution,Normed,SmoothApprox}.lean, MeasureTheory/Integral/DivergenceTheorem.lean, Analysis/Calculus/LineDeriv/IntegrationByParts.lean, MeasureTheory/Function/ContinuousMapDense.lean`
- `lake env lean /tmp/dmdtcbm/lean/Avail.lean … Avail6.lean (#check under bare import GMT.Ch07.Submission: convolution lemmas, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_ofLp, LinearMap.trace_eq_sum_inner, Int.exists_least_of_bdd, Measure.setIntegral_comp_smul_of_pos, integral_add_left_eq_self, support_fderiv_subset, intervalIntegral.integral_eq_sub_of_hasDerivAt available; ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, Integrable.exists_hasCompactSupport_integral_sub_le, integral_divergence_of_hasFDerivAt_off_countable, integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable unknown)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for all 1030 accepted DAG nodes (29 add imports: Poincare.SimonGMT.Chapter02.AreaLipschitz ×17, Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox ×10, Mathlib.MeasureTheory.Function.ContinuousMapDense ×10, …)`
- `python3 scans of RUN/dag.json (1613 nodes): selected node status decomposing, children []; nodes with identical lean_statement: only twin cmcdt_cube_bv_median (waiting-children) and its seven unaccepted cmcdt_cbm_* children, one per proposed type; substring 'dimred_mbl_dt_cbm' occurs 0 times; rg -n 'dimred_mbl_dt_cbm' SNAPSHOT lake-packages-25730c7c/simongmt GMT (no match)`
- `python3/cat of twin nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/{decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1,decomposition-scope-v1}.json and nodes/…-cub-b03c1fa602/decomposition-v1.json (integral_div_zero judged atomic, ~35-line Lean proof); sha256 + difflib of the twin's and this node's parent-supplied natural proofs (same argument, steps 0–6)`
- `python3 -I importing verifier/gmt-compare.py contract_scope/child_modules to emit NodeChallenge text for each child and the parent; lake env lean /tmp/dmdtcbm/chal/Challenge_<key>.lean for integral_div_zero, smooth_approx, smooth_poincare, bv_poincare, integer_median, smooth_trace, bv_trace, parent (only 'declaration uses sorry')`
- `lake env lean /tmp/dmdtcbm/lean/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `validate_lean_statement from verifier/lean_contract.py and /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py on all seven types (accepted, unchanged); grep -n '_existing_lean_name_problem' -A40 runtime.py`
- `sed -n 538,680p book/chapter-02.txt (Simon Ch. 2, 2.5, 2.7–2.9); sed -n 1855,1912p book/chapter-06.txt (Ch. 6, 5.1 displays (28)–(35))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b452cdcca2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b452cdcca2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-b03c1fa602/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmdtcbm/chal/Challenge_integral_div_zero.lean`
- `/tmp/dmdtcbm/chal/Challenge_smooth_approx.lean`
- `/tmp/dmdtcbm/chal/Challenge_smooth_poincare.lean`
- `/tmp/dmdtcbm/chal/Challenge_bv_poincare.lean`
- `/tmp/dmdtcbm/chal/Challenge_integer_median.lean`
- `/tmp/dmdtcbm/chal/Challenge_smooth_trace.lean`
- `/tmp/dmdtcbm/chal/Challenge_bv_trace.lean`
- `/tmp/dmdtcbm/chal/Challenge_parent.lean`
- `/tmp/dmdtcbm/lean/Assembly.lean`
- `/tmp/dmdtcbm/lean/Avail.lean`

Pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project, Mathlib nor SimonGMT contains a usable BV Poincaré inequality, trace inequality or integer median. The snapshot's Ch02 BVPoincare and BVExtensionEstimate are unproved specifications that Ch07 does not import. SimonGMT's Chapter02/BV.lean has only semicontinuity and compactness facts, and Mathlib has no Poincaré inequality. The seven obligations are therefore new. They are built from Mathlib lemmas that all exist at the pinned revision. Lemmas outside the bare Submission import closure are flagged together with the import to add, as 29 accepted nodes already do. The seven child types are byte-identical to the audited split of the unaccepted twin cmcdt_cube_bv_median. That twin is owned by another parent, so the fresh names dimred_mbl_dt_cbm_* are required; they collide with nothing. All seven types and the parent elaborate in the exact comparator challenge form, and both statement validators accept them. A compiled Lean assembly proves the exact parent type from the seven child types using only propext, Classical.choice and Quot.sound.

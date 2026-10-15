# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.radial_homotopy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.radial_homotopy-a1.extderiv_param_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the supplied proof of radial_homotopy. The specific integrand h(t, x) = t^q ι_x β(t x) is replaced by an arbitrary C^∞ family; the argument is unchanged.

Notation.
- Λ^j := Covector (Euclid N) j, the continuous alternating j-linear forms on ℝ^N with the operator norm. It is finite-dimensional, hence complete.
- alt := ContinuousAlternatingMap.alternatizeUncurryFin : L(ℝ^N, Λ^k) → Λ^{k+1}. It is a continuous linear map (alternatizeUncurryFinCLM ℝ (Euclid N) ℝ).
- D := fderiv ℝ. For every ω : ℝ^N → Λ^k and every y, dω(y) = exteriorDerivative ω y = extDeriv ω y = alt(Dω(y)). This holds by unfolding the definitions and needs no differentiability hypothesis.
- h_t(y) := h(t, y) for t ∈ ℝ, and F(y) := ∫_0^1 h(t, y) dt.
- inr := ContinuousLinearMap.inr ℝ ℝ (Euclid N) : ℝ^N →L ℝ × ℝ^N, v ↦ (0, v).

1. Derivative of F. Apply the sibling param_integral (the accepted cmcdt_lpo_slice_param_integral) with this N, V := Λ^k (a complete real normed space) and this h. Its second conclusion at x says that F has Fréchet derivative ∫_0^1 Dh_t(x) dt at x, where Dh_t(x) = fderiv ℝ (y ↦ h(t, y)) x. The Fréchet derivative is unique (HasFDerivAt.fderiv), so DF(x) = ∫_0^1 Dh_t(x) dt, an interval integral in L(ℝ^N, Λ^k).
2. Partial derivative. Fix t. Since h is C^∞, it is differentiable at (t, x). The map y ↦ (t, y) has derivative inr at x (hasFDerivAt_prodMk_right t x). By the chain rule, y ↦ h(t, y) has derivative Dh(t, x) ∘L inr at x. Hence Dh_t(x) = Dh(t, x) ∘L inr.
3. Continuity in t. Since h is C^∞, in particular C^1, Dh : ℝ × ℝ^N → L(ℝ × ℝ^N, Λ^k) is continuous (ContDiff.continuous_fderiv). The map t ↦ (t, x) is continuous, and right composition with the fixed map inr is continuous (Continuous.clm_comp with a constant). By step 2, t ↦ Dh_t(x) = Dh(t, x) ∘L inr is a continuous map ℝ → L(ℝ^N, Λ^k). Hence it is interval integrable on [0, 1] (Continuous.intervalIntegrable).
4. alt commutes with the integral. alt is a continuous linear map between complete spaces, and t ↦ Dh_t(x) is interval integrable. So ∫_0^1 alt(Dh_t(x)) dt = alt(∫_0^1 Dh_t(x) dt) (ContinuousLinearMap.intervalIntegral_comp_comm).
5. Conclusion.
 dF(x) = alt(DF(x))
  = alt(∫_0^1 Dh_t(x) dt)   (step 1)
  = ∫_0^1 alt(Dh_t(x)) dt   (step 4)
  = ∫_0^1 dh_t(x) dt   (definition of d).
 This is the claim. ∎

Implementation note (verified in Lean during decomposition, about 20 lines, standard axioms only; not part of the proof):
- After intro N k h hh x, put hpi := (Submission.cmcdt_lpo_slice_param_integral N (Covector (Euclid N) k) h hh).2 x and hdiff := hh.differentiable (by simp).
- Step 2: ((hdiff (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv.
- Step 3: simp_rw with step 2, then ((hh.continuous_fderiv (by simp)).comp (continuous_id.prodMk continuous_const)).clm_comp continuous_const.
- Unfold the goal with show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ _ x) = ∫ t in (0 : ℝ)..1, ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y : Euclid N => h (t, y)) x), then rw [hpi.fderiv].
- Covector is an abbrev that carries the ContinuousAlternatingMap instances, so unification with the normed-space instances fails unless the types are given explicitly. Use:
 - Continuous.intervalIntegrable (μ := volume) (E := Euclid N →L[ℝ] Covector (Euclid N) k) hcont 0 1;
 - ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (E := Euclid N →L[ℝ] Covector (Euclid N) k) (F := Covector (Euclid N) (k + 1)) (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid N) ℝ (n := k)) hint;
 - then finish with simpa using this.symm.

## Key steps

1. By the sibling param_integral with V := Λ^k, F(y) = ∫_0^1 h(t, y) dt has DF(x) = ∫_0^1 D[y ↦ h(t, y)](x) dt.
2. Chain rule: D[y ↦ h(t, y)](x) = Dh(t, x) ∘L inr. It is continuous in t because h is C^1, hence interval integrable on [0, 1].
3. alt = alternatizeUncurryFin is a continuous linear map, so it commutes with the interval integral (intervalIntegral_comp_comm).
4. dF(x) = alt(DF(x)) = alt(∫_0^1 Dh_t(x) dt) = ∫_0^1 alt(Dh_t(x)) dt = ∫_0^1 dh_t(x) dt.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD (b4d606db, 25730c7c: pins match); cmp snapshot project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `sed -n 1,160p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean (Covector, DifferentialForm, exteriorDerivative := extDeriv, exteriorDerivative_smul, exteriorDerivative_apply)`
- `grep -n 'theorem|def' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (extDeriv ω x = alternatizeUncurryFin (fderiv 𝕜 ω x); extDeriv_smul/extDeriv_fun_smul without hypotheses; extDeriv_add)`
- `grep -n 'def|theorem|lemma' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean (curryLeft, curryLeft_smul, curryLeftLI, curryLeft_apply_apply)`
- `grep -rl extDeriv mathlib/Mathlib | xargs grep -l 'intervalIntegral|∫' (no match); grep -rln 'Poincare lemma|Poincaré lemma|homotopy operator' mathlib/Mathlib (only MeasureTheory/Integral/CurveIntegral/{Basic,Poincare}.lean); grep -rn 'exteriorDerivative.*∫|extDeriv.*∫|homotopy' .lake/packages/simongmt/Poincare (no match)`
- `python3 over dag.json: frozen types/statuses of param_integral-a1 (cmcdt_lpo_slice_param_integral, accepted, 445fb90) and euler_cartan-a1 (dtc_cone_euler_cartan, accepted, 77ba671); regex over all lean_statements for 'exteriorDerivative (fun y : Euclid _ => ∫', '(t • x)).curryLeft', 'fderiv ℝ β (t • x)' (only radial_homotopy, cone_current, cone_param match)`
- `git show 445fb9017470896594b24d5d23bf892b8796493b:GMT/Ch07/Submission.lean; git show 77ba6718296797531c46092c9edeed99a93d1890:GMT/Ch07/Submission.lean (accepted proofs, theorem headers byte-identical to the dag.json types); python3 comparison of the parent's decomposition-v1.json reuse entries with the accepted nodes' parent-supplied-natural-proof.md (identical)`
- `lake env lean /tmp/rh-decomp/Probe0.lean, Probe1.lean (#check fderiv_comp_smul, extDeriv_fun_smul, alternatizeUncurryFin_smul, alternatizeUncurryFinCLM(_apply), curryLeft_smul, curryLeftLI(_apply), ContinuousLinearMap.intervalIntegral_comp_comm, intervalIntegral.integral_eq_sub_of_hasDerivAt, integral_sub, integral_congr, HasDerivAt.smul, hasDerivAt_pow, HasFDerivAt.comp_hasDerivAt, ContDiff.continuous_fderiv, ContDiff.clm_apply, hasFDerivAt_prodMk_right, LinearIsometry.contDiff; CompleteSpace (Covector (Euclid P) q))`
- `lake env lean /tmp/rh-decomp/Check1.lean … Check4.lean (iterations), then /tmp/rh-decomp/Check5_stub.lean and /tmp/rh-decomp/Check5_full.lean generated by python3 -I /tmp/rh-scripts/gen_check.py from the exact JSON lean_statement strings, with #print axioms`
- `grep -c dimred_cs_sos_cfs_rh_ dag.json issue-workers.json; grep -rl over nodes/, decomposition-reopenings/, operator-dependency-edits/, operator-repairs/; git grep -l dimred_cs_sos_cfs_rh_ over all refs (0 hits)`
- `python3 over dag.json: depth/status counts (max depth 6; 779 accepted depth-6 nodes; no depth-6 node has children)`
- `grep -n '^2\.25|^2\.26|homotopy formula' book/chapter-06.txt (lines 441–456)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e486a1b156/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e486a1b156/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-e486a1b156/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-2cc8704e5d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/rh-decomp/Check5_stub.lean`
- `/tmp/rh-decomp/Check5_full.lean`

Pins and contract. The pins match (project b4d606d, mathlib 25730c7c). The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical.

Library gaps.
- Mathlib has no lemma moving extDeriv inside an integral, and no homotopy operator for k-forms. Its only Poincaré-lemma file, MeasureTheory/Integral/CurveIntegral/Poincare.lean, treats closed 1-forms written as E → E →L F, via curve integrals.
- SimonGMT has no homotopy or d-of-integral lemma.
- No DAG node states either new child.

Available API. The proofs use:
- extDeriv = alternatizeUncurryFin ∘ fderiv (by definition);
- extDeriv_fun_smul and fderiv_comp_smul (no differentiability hypotheses);
- alternatizeUncurryFin_smul, alternatizeUncurryFinCLM, curryLeft_smul, curryLeftLI;
- ContinuousLinearMap.intervalIntegral_comp_comm, intervalIntegral.integral_eq_sub_of_hasDerivAt, HasDerivAt.smul, ContDiff.continuous_fderiv.

Reuse. The accepted cmcdt_lpo_slice_param_integral (445fb90) and dtc_cone_euler_cartan (77ba671) are reused with byte-identical frozen types and identical copied natural proofs.

Lean checks.
- Check5_stub: all 4 child types elaborate after import GMT.Ch07.Submission with the contract opens, and the frozen parent type is proved from them.
- Check5_full: with the real accepted proofs and full proofs of the 2 new children, the parent is sorry-free; the axioms are propext, Classical.choice and Quot.sound only.
- Implementation pitfall (recorded in the child notes): Covector's ContinuousAlternatingMap instances unify with the normed-space instances only when the lemma's type arguments are given explicitly. fun_prop fails on DifferentialForm.

Names. The new names are unused across the run records and all git refs.

Depth. Depth 6 is terminal: 779 accepted depth-6 nodes, none with children.

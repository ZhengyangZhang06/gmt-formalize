# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.scaling_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- μ := V.weight.
- I(y, r) := ∫⁻_{B̄_r(y)} ‖H‖ₑ^p dμ ∈ [0, ∞]: a lower integral, with H arbitrary.
- Unfolding RectifiableVarifold.scaledLpNorm gives K(y, r) = (ofReal(r^{p-n}) · I(y, r))^{1/p}.
- Real powers of nonnegative reals are Real.rpow; powers of elements of [0, ∞] are ENNReal.rpow. n stands for (n : ℝ).

1. Since 0 < s ≤ t, we have t > 0 and s/t > 0.

2. Monotonicity in the domain. B̄_s(z) ⊆ B̄_t(w) gives I(z, s) ≤ I(w, t) (lintegral_mono_set; no measurability is needed).

3. Splitting the weight.
   - Real.div_rpow (s, t ≥ 0) gives (s/t)^{p-n} = s^{p-n} / t^{p-n}.
   - t^{p-n} > 0 (Real.rpow_pos_of_pos), so (s/t)^{p-n} · t^{p-n} = s^{p-n} (div_mul_cancel₀).
   - (s/t)^{p-n} ≥ 0 (Real.rpow_nonneg), so ENNReal.ofReal_mul gives ofReal(s^{p-n}) = ofReal((s/t)^{p-n}) · ofReal(t^{p-n}).

4. By step 3, associativity, step 2 and monotonicity of multiplication in [0, ∞]:
   ofReal(s^{p-n}) · I(z, s) = ofReal((s/t)^{p-n}) · (ofReal(t^{p-n}) · I(z, s))
   ≤ ofReal((s/t)^{p-n}) · (ofReal(t^{p-n}) · I(w, t)).

5. Taking 1/p-th powers. Since 1/p > 0, the map x ↦ x^{1/p} on [0, ∞] is monotone (ENNReal.rpow_le_rpow) and multiplicative (ENNReal.mul_rpow_of_nonneg). Hence
   K(z, s) = (ofReal(s^{p-n}) · I(z, s))^{1/p}
   ≤ (ofReal((s/t)^{p-n}) · (ofReal(t^{p-n}) · I(w, t)))^{1/p}
   = ofReal((s/t)^{p-n})^{1/p} · (ofReal(t^{p-n}) · I(w, t))^{1/p}
   = ofReal((s/t)^{p-n})^{1/p} · K(w, t).

6. The coefficient.
   - ENNReal.ofReal_rpow_of_nonneg ((s/t)^{p-n} ≥ 0 and 1/p ≥ 0) gives ofReal((s/t)^{p-n})^{1/p} = ofReal(((s/t)^{p-n})^{1/p}).
   - Real.rpow_mul (s/t ≥ 0) gives ((s/t)^{p-n})^{1/p} = (s/t)^{(p-n)·(1/p)} = (s/t)^{(p-n)/p} (mul_one_div).
   Substituting into step 5 gives K(z, s) ≤ ofReal((s/t)^{(p-n)/p}) · K(w, t). Every step holds in [0, ∞], also when I(w, t) = ∞. ∎

## Key steps

1. t > 0 and s/t > 0
2. I(z,s) ≤ I(w,t) by lintegral_mono_set
3. ofReal(s^{p-n}) = ofReal((s/t)^{p-n}) · ofReal(t^{p-n}) via Real.div_rpow and ENNReal.ofReal_mul
4. Take 1/p-th powers: monotone and multiplicative (ENNReal.rpow_le_rpow, ENNReal.mul_rpow_of_nonneg)
5. ofReal((s/t)^{p-n})^{1/p} = ofReal((s/t)^{(p-n)/p}) via ENNReal.ofReal_rpow_of_nonneg and Real.rpow_mul

## Reference use

### local-project

Queries:
- `rg -n "theorem lintegral_mul_norm_pow_le|theorem lintegral_mul_le_Lp_mul_Lq|theorem exists_measurable_le_lintegral_eq|theorem lintegral_mono_set|theorem lintegral_mono\b|theorem lintegral_mono \{|theorem lintegral_rpow_le|lintegral_Lp_mul_le_Lq_mul_Lr" <snapshot>/mathlib/Mathlib`
- `sed -n 60,160p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean; sed -n 195,260p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `grep -n "^namespace\|^end\|^section\|^variable" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `rg -n "theorem setLIntegral_one|theorem exists_measurable_le_lintegral_eq|theorem lintegral_mono_set |theorem lintegral_mono ⦃" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean; rg -n "theorem div_rpow|theorem rpow_add \(|theorem rpow_mul \{" <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `rg -n 'setLIntegral_rpow_le|lintegral_rpow_le_lintegral_rpow|lintegral_rpow_le_' <snapshot>/mathlib/Mathlib (no match)`
- `rg -l -e 'tdo_slb_setLIntegral_rpow_le_holder|tdo_slb_scaledLpNorm_le_of_subset|tdo_slb_lintegral_rpow_le_scaledLpNorm|tdo_slb_' <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt (no match)`
- `python3 -I scans of <run>/dag.json: lean_name uniqueness (386/386), nodes with lintegral-rpow/Hoelder statements, nodes mentioning ‖H x‖ₑ ^ q or tdo_scaledLpNorm_bounds`
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `lake env lean -o /tmp/slb-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; LEAN_PATH=/tmp/slb-decomp/olean:$(lake env printenv LEAN_PATH) lake env lean /tmp/slb-decomp/checks/{Avail,Children,NoOpen}.lean`
- `grep -n -i "lder" book/chapter-05.txt; sed -n 190,225p book/chapter-05.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-scaled-lp-bounds-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1-rotation-onto-plane-a1/comparison-identity-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/slb-decomp/checks/Avail.lean`
- `/tmp/slb-decomp/checks/Children.lean`
- `/tmp/slb-decomp/checks/NoOpen.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean and Contract.lean and the snapshot Contract.lean all have sha256 c966f51e... .

Relevant Mathlib declarations (snapshot paths). All are available after import GMT.Ch05.Submission alone, as Avail.lean confirmed with #check:
- MeasureTheory/Integral/Lebesgue/Basic.lean:
  - lintegral_mono:84, which holds without measurability.
  - lintegral_mono_set:98.
  - setLIntegral_one:124.
  - exists_measurable_le_lintegral_eq:139.
- MeasureTheory/Integral/MeanInequalities.lean (namespace ENNReal):
  - lintegral_mul_le_Lp_mul_Lq:202.
  - lintegral_mul_norm_pow_le:222, the two-exponent Hoelder with AEMeasurable f and g, 0 <= p, q and p + q = 1.
- Analysis/SpecialFunctions/Pow/Real.lean: Real.rpow_add:207, Real.rpow_mul:414, Real.div_rpow:487.
- ENNReal power lemmas: rpow_mul, mul_rpow_of_nonneg, rpow_le_rpow, ofReal_rpow_of_nonneg, one_rpow, rpow_one, ofReal_mul.

No-match results:
- No Mathlib Hoelder lemma for non-measurable integrands exists (setLIntegral_rpow_le and lintegral_rpow_le_ do not occur).
- No accepted DAG node provides one. The accepted aal_curvature_pairing_holder_bound is a Bochner-integral pairing bound with a different type.
- The proposed names tdo_slb_* occur nowhere searched.

Simon Ch. 5, Remark 2.2 (book/chapter-05.txt:200-215) uses exactly this Hoelder step for q = 2.

Lean check:
- All three child types were fully proved in /tmp/slb-decomp/checks/Children.lean against the compiled Submission olean.
- The frozen parent type was proved there as ⟨tdo_slb_scaledLpNorm_le_of_subset, tdo_slb_lintegral_rpow_le_scaledLpNorm⟩, with axioms propext, Classical.choice and Quot.sound only.
- The parent string equals '(' + C2 + ') ∧ (' + C3 + ')' byte-for-byte.
- NoOpen.lean elaborates all types without open RectifiableVarifold.

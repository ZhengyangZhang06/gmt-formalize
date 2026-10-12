# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.holder_scaled_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- μ := V.weight.
- I := ∫⁻_{B̄_t(w)} ‖H‖ₑ^p dμ ∈ [0, ∞].
- Unfolding RectifiableVarifold.scaledLpNorm gives K(w, t) = (ofReal(t^{p-n}) · I)^{1/p}.
- a := q/p and b := 1 - q/p. n stands for (n : ℝ).
- Real powers of nonnegative reals are Real.rpow; powers in [0, ∞] are ENNReal.rpow.

1. Exponents. From p ≥ q > 0: p > 0, a > 0 (div_pos) and a ≤ 1 (div_le_one), so b ≥ 0.

2. Hoelder. Apply the sibling theorem tdo_slb_setLIntegral_rpow_le_holder with X := Amb n ℓ (its Borel measurable-space instance), μ := V.weight, B := B̄_s(z), g := (x ↦ ‖H x‖ₑ), and the given p, q (0 < q and q ≤ p). It gives
   ∫⁻_{B̄_s(z)} ‖H‖ₑ^q dμ ≤ (∫⁻_{B̄_s(z)} ‖H‖ₑ^p dμ)^a · μ(B̄_s(z))^b.

3. Domain and mass.
   - lintegral_mono_set with B̄_s(z) ⊆ B̄_t(w) gives ∫⁻_{B̄_s(z)} ‖H‖ₑ^p dμ ≤ I.
   - By hypothesis μ(B̄_s(z)) ≤ ofReal(m).
   - Since a, b ≥ 0, ENNReal.rpow_le_rpow on both factors and mul_le_mul' give
     ∫⁻_{B̄_s(z)} ‖H‖ₑ^q dμ ≤ I^a · ofReal(m)^b.

4. ofReal(m)^b = ofReal(m^b) (ENNReal.ofReal_rpow_of_nonneg, with m ≥ 0 and b ≥ 0).

5. Key identity: I^a = ofReal(t^{q(n-p)/p}) · K(w, t)^q.
   - First, K(w, t)^q = ((ofReal(t^{p-n}) · I)^{1/p})^q = (ofReal(t^{p-n}) · I)^{(1/p)·q} (ENNReal.rpow_mul).
   - (1/p)·q = a (one_div_mul_eq_div), and ENNReal.mul_rpow_of_nonneg (a ≥ 0) gives (ofReal(t^{p-n}) · I)^a = ofReal(t^{p-n})^a · I^a.
   - Next, ofReal(t^{p-n})^a = ofReal((t^{p-n})^a) (ENNReal.ofReal_rpow_of_nonneg, t^{p-n} ≥ 0) = ofReal(t^{(p-n)·a}) (Real.rpow_mul, t ≥ 0).
   - Hence ofReal(t^{q(n-p)/p}) · K(w, t)^q = (ofReal(t^{q(n-p)/p}) · ofReal(t^{(p-n)·a})) · I^a.
   - The bracket equals ofReal(t^{q(n-p)/p} · t^{(p-n)·a}) (ENNReal.ofReal_mul, t^{q(n-p)/p} ≥ 0), which is ofReal(t^{q(n-p)/p + (p-n)(q/p)}) (Real.rpow_add, t > 0).
   - Since p ≠ 0, q(n-p)/p + (p-n)(q/p) = 0 (field_simp; ring), so the bracket is ofReal(t^0) = ofReal(1) = 1.
   - Therefore ofReal(t^{q(n-p)/p}) · K(w, t)^q = I^a. These are identities in [0, ∞], valid also when I = ∞.

6. Right-hand side. m^b ≥ 0 (Real.rpow_nonneg), so ENNReal.ofReal_mul and associativity give
   ofReal(m^b · t^{q(n-p)/p}) · K(w, t)^q = ofReal(m^b) · (ofReal(t^{q(n-p)/p}) · K(w, t)^q)
   = ofReal(m^b) · I^a (step 5)
   = ofReal(m)^b · I^a (step 4)
   = I^a · ofReal(m)^b (commutativity).

7. Conclusion. Steps 3 and 6 give
   ∫⁻_{B̄_s(z)} ‖H‖ₑ^q dμ ≤ I^a · ofReal(m)^b = ofReal(m^{1-q/p} · t^{q(n-p)/p}) · K(w, t)^q.
   No hypothesis on s is used: if s < 0 the ball B̄_s(z) is empty and the argument still applies. ∎

## Key steps

1. p > 0, a = q/p > 0, b = 1 - q/p ≥ 0
2. Sibling Hoelder lemma with μ = V.weight, B = B̄_s(z), g = ‖H‖ₑ
3. lintegral_mono_set and μ(B̄_s(z)) ≤ ofReal m give LHS ≤ I^a · ofReal(m)^b with I = ∫⁻_{B̄_t(w)} ‖H‖ₑ^p
4. ofReal(m)^b = ofReal(m^b)
5. I^a = ofReal(t^{q(n-p)/p}) · K(w,t)^q via ENNReal.rpow_mul, mul_rpow_of_nonneg, ofReal_rpow_of_nonneg, Real.rpow_mul, Real.rpow_add and q(n-p)/p + (p-n)q/p = 0
6. Recombine with ENNReal.ofReal_mul and commutativity

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

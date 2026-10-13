# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.scaled_lp_bounds-a1.lintegral_holder-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- ν := μ.restrict B. For every f : X → [0, ∞], ∫⁻_B f dμ is by definition ∫⁻ f dν.
- ∫⁻ 1 dν = μ(B) (setLIntegral_one).
- All powers of elements of [0, ∞] are ENNReal.rpow with real exponents.
- ∫⁻ is Mathlib's lower Lebesgue integral: the supremum of the integrals of measurable simple functions below the integrand. It is monotone in the integrand without any measurability assumption (lintegral_mono).

1. Exponents. Since 0 < q ≤ p:
   - p > 0 and p/q > 0;
   - a := q/p satisfies 0 < a ≤ 1 (div_pos, div_le_one);
   - b := 1 - q/p satisfies b ≥ 0, and a + b = 1;
   - (p/q)·(q/p) = 1 and q·(p/q) = p, because p ≠ 0 and q ≠ 0.

2. Measurable minorant. Apply exists_measurable_le_lintegral_eq to the measure ν and the function x ↦ g(x)^q. It gives a measurable G : X → [0, ∞] with G(x) ≤ g(x)^q for all x and ∫⁻ g^q dν = ∫⁻ G dν. Hence the left side of the claim equals ∫⁻ G dν.

3. Rewriting G. Put F(x) := G(x)^{p/q}.
   - F is measurable (Measurable.pow_const), hence AEMeasurable for ν. The constant function 1 is AEMeasurable.
   - For every x, F(x)^a · 1^b = (G(x)^{p/q})^{q/p} · 1 = G(x)^{(p/q)(q/p)} = G(x)^1 = G(x). This uses ENNReal.one_rpow, ENNReal.rpow_mul (x^{y z} = (x^y)^z), step 1 and ENNReal.rpow_one.

4. Hoelder. Apply ENNReal.lintegral_mul_norm_pow_le to the measure ν, f := F, g := 1 and the exponents a, b ≥ 0 with a + b = 1:
   ∫⁻ F^a · 1^b dν ≤ (∫⁻ F dν)^a · (∫⁻ 1 dν)^b.
   By step 3 and ∫⁻ 1 dν = μ(B), this reads
   ∫⁻ G dν ≤ (∫⁻ G^{p/q} dν)^{q/p} · μ(B)^{1-q/p}.
   - The lemma is the two-exponent form of Hoelder's inequality ENNReal.lintegral_mul_le_Lp_mul_Lq with the conjugate exponents p/q and p/(p - q).
   - It handles the degenerate cases itself. If q = p, then b = 0 and μ(B)^0 = 1. The values 0 and ∞ of the integrals and of μ(B) are allowed.

5. Comparison with g^p.
   - For each x, G(x) ≤ g(x)^q and p/q ≥ 0. By ENNReal.rpow_le_rpow, G(x)^{p/q} ≤ (g(x)^q)^{p/q} = g(x)^{q·(p/q)} = g(x)^p (ENNReal.rpow_mul and step 1).
   - By monotonicity of the lower integral (lintegral_mono, no measurability needed), ∫⁻ G^{p/q} dν ≤ ∫⁻ g^p dν.
   - Since q/p ≥ 0, ENNReal.rpow_le_rpow gives (∫⁻ G^{p/q} dν)^{q/p} ≤ (∫⁻ g^p dν)^{q/p}.
   - Multiplying both sides by μ(B)^{1-q/p} keeps the inequality in [0, ∞] (monotonicity of multiplication).

6. Conclusion. Chain steps 2, 4 and 5:
   ∫⁻_B g^q dμ = ∫⁻ G dν
   ≤ (∫⁻ G^{p/q} dν)^{q/p} · μ(B)^{1-q/p}
   ≤ (∫⁻ g^p dν)^{q/p} · μ(B)^{1-q/p}
   = (∫⁻_B g^p dμ)^{q/p} · μ(B)^{1-q/p}. ∎

## Key steps

1. Exponents: p > 0, a = q/p ∈ (0,1], b = 1 - q/p ≥ 0, a + b = 1, (p/q)(q/p) = 1
2. exists_measurable_le_lintegral_eq on μ.restrict B gives measurable G ≤ g^q with ∫⁻_B g^q = ∫⁻_B G
3. G = (G^{p/q})^{q/p} · 1^{1-q/p} pointwise
4. ENNReal.lintegral_mul_norm_pow_le with f = G^{p/q}, g = 1: ∫⁻_B G ≤ (∫⁻_B G^{p/q})^{q/p} μ(B)^{1-q/p}
5. G^{p/q} ≤ (g^q)^{p/q} = g^p, then monotonicity of the lower integral and of x ↦ x^{q/p} and multiplication

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

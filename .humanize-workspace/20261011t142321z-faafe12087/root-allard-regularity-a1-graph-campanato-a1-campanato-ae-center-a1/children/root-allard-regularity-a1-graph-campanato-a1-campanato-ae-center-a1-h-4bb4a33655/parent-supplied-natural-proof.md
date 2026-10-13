# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1.hs_lebesgue_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(b) and 3 of the parent proof (Lebesgue points by Lebesgue's differentiation theorem in R^n), together with the operator-norm comparison used in its step 4, stated for the quadratic Hilbert-Schmidt oscillation.

Notation.
- L = L(R^m, R^k) with the operator norm ||.||.
- e_i = EuclideanSpace.single i 1 (i < m) is the standard basis of R^m, with ||e_i|| = 1.
- hsNormSq(T) = sum_{i<m} ||T e_i||^2.
- B_t(z) is the closed ball; L^n is Lebesgue measure (volume) on R^n; integral^- is the lower Lebesgue integral (lintegral).
- ||w||_e = ofReal(||w||) is the extended norm (Mathlib: ofReal_norm).
- Integrals and averages are computed in [0, infinity], where a / c = a * c^(-1).

1. Hilbert-Schmidt versus operator norm. For T in L and i < m, ||T e_i|| <= ||T|| ||e_i|| = ||T|| (ContinuousLinearMap.le_opNorm). Squaring and summing over the m indices gives hsNormSq(T) <= m ||T||^2.

2. Size of the oscillation. B >= ||G(0)|| >= 0. For all x, w in R^n, ||G(x) - G(w)|| <= ||G(x)|| + ||G(w)|| <= 2B.

3. Local integrability. L is a finite-dimensional normed space, hence second countable, so the Borel measurable map G is almost everywhere strongly measurable (Measurable.aestronglyMeasurable). For a compact K in R^n, L^n(K) < infinity and ||G(x)|| <= B for all x, so G is integrable on K (Measure.integrableOn_of_bounded). Since R^n is locally compact, G is locally integrable (locallyIntegrable_iff).

4. Lebesgue differentiation along closed balls.
 - L^n is an additive Haar measure on the finite-dimensional space R^n, hence uniformly locally doubling (instance isUnifLocDoublingMeasureOfIsAddHaarMeasure). Let V be the Vitali family IsUnifLocDoublingMeasure.vitaliFamily L^n 1.
 - By the Lebesgue differentiation theorem along V, applied to the locally integrable G (VitaliFamily.ae_tendsto_lintegral_enorm_sub_div), there is an L^n-null set N such that for every z not in N, (integral^-_a ||G(y) - G(z)||_e dy) / L^n(a) -> 0 as a -> V.filterAt z.
 - Fix z not in N. The closed balls B_t(z) tend to V.filterAt z as t -> 0+. This is IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt with K = 1, index filter l = 𝓝[>]0 on R, centres w(t) = z and radii delta(t) = t: delta tends to 0 within (0, infinity) along l, and for t > 0 the point z lies in B_{1*t}(z).
 - Composing the two limits:
  b(t) := (integral^-_{B_t(z)} ||G(y) - G(z)||_e dy) / L^n(B_t(z)) -> 0 as t -> 0+.
 This is the parent's step 3 in extended-real form. Equivalently, one may use IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub for the real averages and convert with ofReal_integral_eq_lintegral_ofReal.

5. Pointwise comparison. Let z be as in step 4 and x in R^n, and put d := ||G(x) - G(z)||, so 0 <= d <= 2B by step 2. By step 1, hsNormSq(G(x) - G(z)) <= m d^2 = (m d) d <= (2mB) d. Now:
 - ofReal is monotone;
 - ofReal(p q) = ofReal(p) ofReal(q) for p = 2mB >= 0 (ENNReal.ofReal_mul);
 - ofReal(d) = ||G(x) - G(z)||_e.
 Hence
  ofReal(hsNormSq(G(x) - G(z))) <= ofReal(2mB) * ||G(x) - G(z)||_e.

6. Averaged comparison. Fix a real t. Take lower integrals over B_t(z) of the inequality in step 5 and multiply by L^n(B_t(z))^(-1). This is valid because:
 - the lower integral is monotone for arbitrary functions (lintegral_mono);
 - multiplication in [0, infinity] is monotone;
 - the finite constant ofReal(2mB) can be pulled out of a lower integral without any measurability (lintegral_const_mul', since ofReal(2mB) != infinity).
 Hence
  L^n(B_t(z))^(-1) * integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - G(z))) dx <= L^n(B_t(z))^(-1) * ofReal(2mB) * integral^-_{B_t(z)} ||G(x) - G(z)||_e dx = ofReal(2mB) * b(t).

7. Squeeze. Because ofReal(2mB) != infinity and b(t) -> 0, ofReal(2mB) * b(t) -> ofReal(2mB) * 0 = 0 as t -> 0+ (ENNReal.Tendsto.const_mul). The left side of step 6 is bounded below by the constant 0. By the squeeze theorem (tendsto_of_tendsto_of_tendsto_of_le_of_le),
  L^n(B_t(z))^(-1) * integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - G(z))) dx -> 0 as t -> 0+.

8. Conclusion. Step 7 holds for every z outside the L^n-null set N, that is, for L^n-almost every z in R^n. This is the claim.

## Key steps

1. hsNormSq(T) <= m ||T||^2 and ||G(x) - G(z)|| <= 2B give ofReal(hsNormSq(G(x) - G(z))) <= ofReal(2mB) ||G(x) - G(z)||_e
2. A bounded Borel operator field G is locally integrable on R^n
3. Lebesgue differentiation along the Vitali family of the doubling measure L^n, composed with the closed balls B_t(z) as t -> 0+, gives (lintegral over B_t(z) of ||G - G(z)||_e) / L^n(B_t(z)) -> 0 off a null set
4. Averaging the pointwise comparison over B_t(z) and squeezing shows the quadratic Hilbert-Schmidt average tends to 0 for a.e. z

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean; cat <snapshot>/manifest.json`
- `rg -n 'theorem|lemma' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `rg -n 'theorem ae_tendsto_lintegral|theorem ae_tendsto_average|lintegral_enorm_sub_div' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n "theorem addHaar_closedBall'|theorem addHaar_closedBall |instance.*isUnifLocDoubling|isUnifLocDoublingMeasureOfIsAddHaarMeasure|^variable" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n "theorem integrableOn_of_bounded|theorem locallyIntegrable_iff|theorem lintegral_const_mul'|theorem setLIntegral_const |theorem lintegral_add_left |theorem ofReal_norm_eq_enorm|theorem Tendsto.const_mul|theorem measure_closedBall_pos|theorem measure_closedBall_lt_top|theorem finrank_euclideanSpace_fin" <snapshot>/mathlib/Mathlib`
- `grep -n 'theorem le_div_iff_mul_le|theorem ofReal_mul|theorem ofReal_eq_zero|theorem inv_ne_top|theorem ofReal_add |protected theorem mul_inv |ofReal_ne_top' <snapshot>/mathlib/Mathlib/Basic/ENNReal/*.lean (Mathlib/Data/ENNReal/*.lean are deprecated 5-line stubs)`
- `rg -n 'theorem continuousAt_rpow_const|theorem zero_rpow ' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/*.lean`
- `rg -n 'theorem sum_repr|theorem basisFun_apply' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `python: scan dag.json nodes (lean_statement/title containing hsNormSq, ae_tendsto, Lebesgue, Campanato) and list all 339 reserved lean_name values`
- `for nm in allard52_cae_hsNormSq_lebesgue_ae allard52_cae_center_eq_at_lebesgue_point allard52_cae_: grep -c nm dag.json; rg -l nm <snapshot>; grep -rl nm GMT lake-packages-25730c7c/simongmt --include=*.lean; grep -rl nm <run>/nodes`
- `git for-each-ref refs/heads refs/remotes | xargs -n 200 git grep -l -e allard52_cae_ -- 'GMT/Ch05/*.lean'`
- `git show humanize-recursive/.../root-allard-any-radius-a1-campanato-a1-a1:GMT/Ch05/Submission.lean | grep -n 'namespace|^end|^open' (child placement: namespace Submission inside GMT.Ch05 after open RectifiableVarifold)`
- `sed -n 2750,2850p runtime.py; sed -n 120,200p speculation.py (child declaration placement)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = scratch build + lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `lean check/Assembly.lean; lean check/Child1.lean; lean check/Child2.lean; lean check/Full.lean (with #print axioms)`
- `python -I: _recursive_lean.lean_contract.validate_lean_statement on both child types`
- `grep -n -i 'lebesgue point|differentiation theorem' book/*.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-ae-center-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-ae-center-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-campanato-ae-center-a1/parent-supplied-plan.md`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/speculation.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/cae-decomp-uj0eXm/check/Assembly.lean`
- `/tmp/cae-decomp-uj0eXm/check/Child1.lean`
- `/tmp/cae-decomp-uj0eXm/check/Child2.lean`
- `/tmp/cae-decomp-uj0eXm/check/Full.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, Contract.lean and snapshot Submission.lean are identical (sha256 c966f51e...1e12).

Usable Mathlib lemmas, all used in verified scratch proofs:
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (Differentiation.lean:818);
- IsUnifLocDoublingMeasure.vitaliFamily and tendsto_closedBall_filterAt (DensityTheorem.lean:50,108); ae_tendsto_average_norm_sub (:150) is the Bochner-average alternative;
- instance isUnifLocDoublingMeasureOfIsAddHaarMeasure (EqHaar.lean:550);
- Measure.addHaar_closedBall' (EqHaar.lean:475), which needs no Nontrivial hypothesis, so n = 0 is fine;
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716) and locallyIntegrable_iff (LocallyIntegrable.lean:332);
- setLIntegral_const, lintegral_add_left, lintegral_const_mul and lintegral_const_mul';
- measure_closedBall_pos and measure_closedBall_lt_top;
- ofReal_norm (ofReal_norm_eq_enorm is deprecated);
- ENNReal.le_div_iff_mul_le, mul_inv, inv_ne_top, ofReal_mul', ofReal_add, ofReal_eq_zero and Tendsto.const_mul/mul_const (now under Mathlib/Basic/ENNReal);
- Real.continuousAt_rpow_const (hypothesis x != 0 or 0 <= q) and Real.zero_rpow;
- OrthonormalBasis.sum_repr with EuclideanSpace.basisFun_apply;
- finrank_euclideanSpace_fin.

No existing declaration is citable:
- Children may cite only siblings.
- Related DAG nodes are in other branches: anyrad_gc_hsNormSq_lebesgue_ae (general measure on Amb n ℓ, decomposing), lgc_hsNormSq_bounds (rlcr-lean) and dohr_tp_ae_lebesgue_point_of_growth (accepted, but real-valued, integrable f on Amb n ℓ).
- No Mathlib, SimonGMT or snapshot lemma states the HS-quadratic Lebesgue-point property or the pointwise Campanato identification.

Name and placement checks:
- The proposed names allard52_cae_hsNormSq_lebesgue_ae and allard52_cae_center_eq_at_lebesgue_point occur nowhere (dag.json, nodes, GMT, SimonGMT, snapshot, all git branches).
- Accepted branches place child theorems in namespace Submission inside GMT.Ch05, after open RectifiableVarifold.

Lean checks:
- Both child types elaborate in that context.
- Assembly.lean proves the byte-identical frozen parent type from the two child types.
- Child1.lean and Child2.lean contain complete proofs.
- Full.lean (children plus assembly) compiles, and #print axioms gives [propext, Classical.choice, Quot.sound].
- validate_lean_statement accepts both types.

Book: Simon Ch. 1, Theorem 3.23 (Differentiation Theorem) is the source-level reference for the Lebesgue differentiation step.

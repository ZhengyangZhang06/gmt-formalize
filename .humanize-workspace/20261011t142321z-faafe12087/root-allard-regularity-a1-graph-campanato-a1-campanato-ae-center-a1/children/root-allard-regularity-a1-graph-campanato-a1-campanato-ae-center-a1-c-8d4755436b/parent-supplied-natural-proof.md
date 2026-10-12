# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.campanato_ae_center-a1.center_eq_at_lebesgue_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1(a), 1(c), 1(d), 2, 4 and 5 of the parent proof, carried out at one point z that is assumed to be a quadratic Hilbert-Schmidt Lebesgue point (hypothesis (i)). With this hypothesis the operator-norm bound B of the parent's step 4 is not needed.

Notation.
- L = L(R^m, R^k); e_i = EuclideanSpace.single i 1; hsNormSq(S) = sum_{i<m} ||S e_i||^2.
- B_t(z) are closed balls; L^n = volume on R^n; integral^- = lintegral; v := L^n(B_1(0)).
- Integrals are computed in [0, infinity], where a / c = a * c^(-1).
- a(t) := L^n(B_t(z))^(-1) * integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - G(z))) dx, which tends to 0 as t -> 0+ by hypothesis (i).
- Hypothesis (ii): integral^-_{B_{s/2}(z)} ofReal(hsNormSq(G(x) - T)) dx <= ofReal(A s^n (s/R)^(2 alpha)) for 0 < s <= s0.

1. Hilbert-Schmidt facts. For S, S' in L:
 (a) hsNormSq(S) >= 0, since it is a sum of squares.
 (b) hsNormSq(S - S') <= 2 hsNormSq(S) + 2 hsNormSq(S'). For each i, (S - S') e_i = a - b with a = S e_i and b = S' e_i, and ||a - b||^2 <= (||a|| + ||b||)^2 <= 2||a||^2 + 2||b||^2; the last inequality holds because (||a|| - ||b||)^2 >= 0. Sum over i.
 (c) hsNormSq(S) = 0 implies S = 0. A vanishing finite sum of nonnegative terms has every term zero, so S e_i = 0 for all i. Every w in R^m equals sum_i w_i e_i (expansion in the orthonormal basis EuclideanSpace.basisFun, whose i-th vector is EuclideanSpace.single i 1; OrthonormalBasis.sum_repr). Hence S w = sum_i w_i S e_i = 0.
 (d) S -> hsNormSq(S) is continuous, being a finite sum of squared norms of the continuous evaluations S -> S e_i. Hence x -> ofReal(hsNormSq(G(x) - T)) is measurable: it is the measurable G followed by the continuous map S -> ofReal(hsNormSq(S - T)), and L carries its Borel sigma-algebra.

2. Ball volumes. L^n is an additive Haar measure on R^n.
 - 0 < v < infinity: closed balls of positive radius contain a nonempty open ball, so they have positive measure (measure_closedBall_pos); they are compact, so they have finite measure (measure_closedBall_lt_top).
 - For every t >= 0, L^n(B_t(z)) = ofReal(t^n) * v (Measure.addHaar_closedBall' with finrank R^n = n, finrank_euclideanSpace_fin).
 - In particular 0 < L^n(B_t(z)) < infinity for t > 0. No assumption n >= 1 is needed.

3. Pointwise inequality. Put h := hsNormSq(G(z) - T), so h >= 0 by 1(a). For every x in R^n, G(z) - T = (G(x) - T) - (G(x) - G(z)), so 1(b) gives
  h <= 2 hsNormSq(G(x) - T) + 2 hsNormSq(G(x) - G(z)).
 Both summands are nonnegative, ofReal is monotone, ofReal(p + q) = ofReal(p) + ofReal(q) for p, q >= 0, and ofReal(2p) = 2 ofReal(p). Therefore
  ofReal(h) <= 2 ofReal(hsNormSq(G(x) - T)) + 2 ofReal(hsNormSq(G(x) - G(z))).

4. Integrated inequality. Fix s with 0 < s <= s0 and put t := s/2 > 0. Take lower integrals of step 3 over B_t(z):
 - the left side becomes ofReal(h) * L^n(B_t(z)) (setLIntegral_const);
 - the inequality is preserved because integrals are monotone (lintegral_mono);
 - on the right, the first summand is measurable by 1(d), so the lower integral of the sum is the sum of the lower integrals (lintegral_add_left);
 - the factor 2 comes out of both integrals (lintegral_const_mul for the measurable first summand, and lintegral_const_mul' with the finite constant 2 for the second).
 Applying hypothesis (ii) at s to the first integral:
  ofReal(h) * L^n(B_t(z)) <= 2 integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - T)) dx + 2 integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - G(z))) dx
   <= 2 ofReal(A s^n (s/R)^(2 alpha)) + 2 integral^-_{B_t(z)} ofReal(hsNormSq(G(x) - G(z))) dx.

5. Normalisation.
 - Since 0 < L^n(B_t(z)) < infinity, dividing by it (ENNReal.le_div_iff_mul_le, then ENNReal.add_div) gives
  ofReal(h) <= 2 ofReal(A s^n (s/R)^(2 alpha)) / L^n(B_t(z)) + 2 a(t).
 - Since s = 2t, s^n = 2^n t^n, so A s^n (s/R)^(2 alpha) = (2^n A (s/R)^(2 alpha)) * t^n. Because t^n >= 0, ofReal(A s^n (s/R)^(2 alpha)) = ofReal(2^n A (s/R)^(2 alpha)) * ofReal(t^n) (ENNReal.ofReal_mul').
 - By step 2, L^n(B_t(z)) = ofReal(t^n) * v with 0 < ofReal(t^n) < infinity. So (ofReal(t^n) v)^(-1) = ofReal(t^n)^(-1) v^(-1) (ENNReal.mul_inv) and ofReal(t^n) ofReal(t^n)^(-1) = 1 (ENNReal.mul_inv_cancel). Hence
  2 ofReal(A s^n (s/R)^(2 alpha)) / L^n(B_t(z)) = 2 ofReal(2^n A (s/R)^(2 alpha)) * v^(-1).
 - Therefore, for every 0 < s <= s0,
  ofReal(h) <= beta(s) := 2 ofReal(2^n A (s/R)^(2 alpha)) * v^(-1) + 2 a(s/2).
 No sign condition on A is used: if A <= 0 the first term is 0.

6. Limit of the bound as s -> 0+.
 (a) s/R -> 0. Since 2 alpha > 0, the map u -> u^(2 alpha) is continuous at 0 (Real.continuousAt_rpow_const, using 0 <= 2 alpha), and 0^(2 alpha) = 0 (Real.zero_rpow, since 2 alpha != 0). So (s/R)^(2 alpha) -> 0 and 2^n A (s/R)^(2 alpha) -> 0. Since ofReal is continuous (ENNReal.tendsto_ofReal), ofReal(2^n A (s/R)^(2 alpha)) -> ofReal(0) = 0. Since v != 0, v^(-1) != infinity (ENNReal.inv_ne_top), so 2 ofReal(2^n A (s/R)^(2 alpha)) * v^(-1) -> 2 * 0 * v^(-1) = 0 (ENNReal.Tendsto.const_mul and ENNReal.Tendsto.mul_const).
 (b) The map s -> s/2 sends 𝓝[>]0 into 𝓝[>]0: it is continuous with value 0 at 0, and s/2 > 0 for s > 0. By hypothesis (i), a(s/2) -> 0, and so 2 a(s/2) -> 0.
 Hence beta(s) -> 0 + 0 = 0 as s -> 0+.

7. Conclusion. The interval (0, s0] belongs to 𝓝[>]0 because s0 > 0 (Ioc_mem_nhdsGT), and ofReal(h) <= beta(s) on it by step 5. Passing to the limit (ge_of_tendsto) gives ofReal(h) <= 0. So ofReal(h) = 0, that is h <= 0 (ENNReal.ofReal_eq_zero). Together with h >= 0 from 1(a), hsNormSq(G(z) - T) = h = 0. Then G(z) - T = 0 by 1(c), i.e. G(z) = T.

## Key steps

1. Hilbert-Schmidt facts: hsNormSq >= 0; hsNormSq(S - S') <= 2 hsNormSq(S) + 2 hsNormSq(S'); hsNormSq(S) = 0 gives S = 0; x -> ofReal(hsNormSq(G(x) - T)) is measurable
2. Ball volumes: L^n(B_t(z)) = ofReal(t^n) v with 0 < v = L^n(B_1(0)) < infinity
3. Pointwise ofReal(h) <= 2 ofReal(hsNormSq(G(x) - T)) + 2 ofReal(hsNormSq(G(x) - G(z))), integrated over B_{s/2}(z) and combined with the Campanato bound (ii)
4. Dividing by L^n(B_{s/2}(z)) gives ofReal(h) <= 2 ofReal(2^n A (s/R)^(2 alpha)) v^(-1) + 2 a(s/2) for 0 < s <= s0
5. As s -> 0+ the bound tends to 0, so hsNormSq(G(z) - T) = 0 and G(z) = T

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

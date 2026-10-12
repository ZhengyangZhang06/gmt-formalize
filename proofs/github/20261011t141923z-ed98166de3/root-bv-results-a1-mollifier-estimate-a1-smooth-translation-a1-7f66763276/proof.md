# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.mollifier_estimate-a1`
- Child DAG node: `root.bv_results-a1.mollifier_estimate-a1.smooth_translation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1(c) of the parent-supplied proof (fundamental theorem of calculus along segments, Tonelli and translation invariance). The gradient bound of step 1(b) on the translates Q − s z, which the parent obtains from its sibling theorem bv_mollifier_fderiv_lintegral_le, is here the hypothesis. The details are filled in below so that the argument is self-contained.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n) with Lebesgue measure vol (= volume). Dw := fderiv ℝ w, and ‖Dw(y)‖ is the operator norm. All ∫⁻ are lower Lebesgue integrals with values in [0,∞]. I := [0,1] = Icc 0 1 ⊆ ℝ. For a real number a, ‖a‖ₑ = ofReal|a|. For z ∈ E, ‖z‖ₑ = ofReal ‖z‖. For s ∈ ℝ, T_s(x) := x − s•z, so the hypothesis reads ∫⁻_{T_s(Q)} ‖Dw(y)‖ₑ dy ≤ M for every s ∈ I. No measurability of Q is used anywhere.

1. Regularity. Since w is C¹, w is differentiable at every point and y ↦ Dw(y) is continuous (ContDiff.differentiable and ContDiff.continuous_fderiv, with 1 ≠ 0).

2. Pointwise FTC bound. Fix x ∈ E. For s ∈ ℝ put g(s) := w(x − s•z) and g'(s) := Dw(x − s•z)(−z).
   (a) The map s ↦ x − s•z has derivative −z at every s. So by the chain rule g has derivative g'(s) at every s (HasFDerivAt.comp_hasDerivAt).
   (b) g' is continuous: it is the composition of the continuous maps s ↦ x − s•z and Dw, followed by evaluation at the fixed vector −z. So g' is interval integrable on [0,1].
   (c) By the fundamental theorem of calculus (intervalIntegral.integral_eq_sub_of_hasDerivAt),
       w(x − z) − w(x) = g(1) − g(0) = ∫_0^1 g'(s) ds = ∫_{Ioc 0 1} g'(s) ds.
   (d) Chain of bounds:
       ‖w(x − z) − w(x)‖ₑ
         ≤ ∫⁻_{Ioc 0 1} ‖g'(s)‖ₑ ds   (‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ, enorm_integral_le_lintegral_enorm)
         ≤ ∫⁻_I ‖g'(s)‖ₑ ds   (monotonicity in the set, since Ioc 0 1 ⊆ I)
         ≤ ∫⁻_I ofReal(‖z‖)·‖Dw(x − s•z)‖ₑ ds   (operator-norm bound ‖Dw(y)(−z)‖ₑ ≤ ‖Dw(y)‖ₑ·‖−z‖ₑ = ofReal(‖z‖)·‖Dw(y)‖ₑ, ContinuousLinearMap.le_opENorm)
         = ofReal(‖z‖)·∫⁻_I ‖Dw(x − s•z)‖ₑ ds   (the constant ofReal(‖z‖) ≠ ∞ is pulled out, lintegral_const_mul').

3. Integration over Q. Integrate the bound of step 2 over Q with respect to vol|_Q, using monotonicity of ∫⁻. Then pull out the finite constant ofReal(‖z‖) again:
   ∫⁻_Q ‖w(x − z) − w(x)‖ₑ dx ≤ ofReal(‖z‖)·∫⁻_Q ∫⁻_I ‖Dw(x − s•z)‖ₑ ds dx.

4. Tonelli. Φ(x, s) := ‖Dw(x − s•z)‖ₑ is continuous on E × ℝ by step 1, hence measurable. The measures vol|_Q and vol|_I are s-finite, being restrictions of σ-finite measures. By Tonelli (lintegral_lintegral_swap),
   ∫⁻_Q ∫⁻_I Φ(x, s) ds dx = ∫⁻_I ∫⁻_Q Φ(x, s) dx ds.

5. Translation invariance. Fix s ∈ I. T_s is a measurable embedding, since it is a homeomorphism of E (measurableEmbedding_subRight). It preserves Lebesgue measure (measurePreserving_sub_right). Hence, by MeasurePreserving.setLIntegral_comp_emb (valid for an arbitrary set Q),
   ∫⁻_Q Φ(x, s) dx = ∫⁻_Q ‖Dw(T_s x)‖ₑ dx = ∫⁻_{T_s(Q)} ‖Dw(y)‖ₑ dy ≤ M,
   where the last inequality is the hypothesis, applied with this s ∈ [0,1].

6. Conclusion.
   (a) I is measurable. So step 5 and monotonicity of the set integral (setLIntegral_mono') give
       ∫⁻_I ∫⁻_Q Φ(x, s) dx ds ≤ ∫⁻_I M ds = M·vol(I) = M·ofReal(1 − 0) = M   (setLIntegral_const, Real.volume_Icc).
   (b) Combine steps 3 and 4 with (a), using that multiplication by ofReal(‖z‖) is monotone on [0,∞]:
       ∫⁻_Q ‖w(x − z) − w(x)‖ₑ dx ≤ ofReal(‖z‖)·M.
   The argument holds for every M ∈ [0,∞], including M = ∞. ∎

## Key steps

1. C¹ regularity: w is differentiable everywhere and Dw = fderiv ℝ w is continuous.
2. FTC along s ↦ x − s•z on [0,1] with the operator-norm bound: ‖w(x − z) − w(x)‖ₑ ≤ ofReal‖z‖·∫⁻_{[0,1]} ‖Dw(x − s•z)‖ₑ ds for every x.
3. Integrate over Q, pull out ofReal‖z‖, and swap the order by Tonelli (the integrand is continuous in (x, s)).
4. Translation x ↦ x − s•z is a measure-preserving measurable embedding: ∫⁻_Q ‖Dw(x − s•z)‖ₑ dx = ∫⁻_{(·−s•z)''Q} ‖Dw‖ₑ ≤ M for s ∈ [0,1].
5. Integrate the constant bound M over [0,1], which has measure 1, to get ofReal‖z‖·M.

## Reference use

### local-project

Queries:
- `rg -n 'theorem (contDiff_normed|nonneg_normed|support_normed_eq|integral_normed|continuous_normed|tsupport_normed_eq|hasCompactSupport_normed)' Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right' Mathlib`
- `rg -n 'setLIntegral_comp_emb|setLIntegral_comp_preimage_emb' Mathlib`
- `rg -n 'lintegral_sub_right_eq_self|lintegral_add_right_eq_self' Mathlib; rg -n 'lintegral_div_right_eq_self' Mathlib/MeasureTheory`
- `rg -n 'theorem measurePreserving_div_right' Mathlib/MeasureTheory; rg -n 'quasiMeasurePreserving_sub_of_right_invariant|quasiMeasurePreserving_div_of_right_invariant' Mathlib/MeasureTheory`
- `rg -n 'ConvolutionExistsAt|convolution_def|convolution_lsmul|HasCompactSupport.convolutionExists' Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem (lintegral_lintegral_swap|enorm_integral_le_lintegral_enorm|ofReal_integral_eq_lintegral_ofReal)' Mathlib`
- `rg -n 'AbsolutelyContinuous.prod' Mathlib/MeasureTheory; rg -n 'enorm_add₃_le' Mathlib/Analysis/Normed; rg -n 'theorem le_opENorm' Mathlib/Analysis`
- `rg -n 'theorem .*lintegral.*fderiv|theorem .*fderiv.*lintegral' Mathlib; rg -n 'theorem .*(translate|comp_add_right|comp_sub_right).*(eLpNorm|Lp|lintegral)' Mathlib/MeasureTheory Mathlib/Analysis; rg -n 'theorem .*(convolution|normed_convolution).*(eLpNorm|lintegral|dist_le|_le)' Mathlib/Analysis/Convolution.lean Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; rg -iln 'mollif' Mathlib`
- `cmp project/GMT/Ch02/Contract.lean against the workspace GMT/Ch02/Contract.lean; rg -n 'namespace Submission|Submission\.' project --glob '*.lean'`
- `grep -l <each proposed lean_name> dag.json DAG.md dag.mmd nodes/*/*`
- `lean (pinned v4.35.0-rc3, LEAN_PATH = scratch build + lake-packages-25730c7c/*/.lake/build/lib/lean) on Stmts.lean, Avail2.lean (#check ContDiffBump.normed after import GMT.Ch02.Submission), Assembly.lean, Assembly2.lean, truth/A,B,C, a simulated Submission.lean, and the NodeChallenge/NodeSolution modules generated by gmt-compare.py child_modules`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/VectorMeasure/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/NNNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-mollifier-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/mollest-decomp-fLuVoN/checks/Assembly.lean`
- `/tmp/mollest-decomp-fLuVoN/checks/Assembly2.lean`
- `/tmp/mollest-decomp-fLuVoN/truth/A/A.lean`
- `/tmp/mollest-decomp-fLuVoN/truth/B/B.lean`
- `/tmp/mollest-decomp-fLuVoN/truth/C/C.lean`
- `/tmp/mollest-decomp-fLuVoN/sim/src/GMT/Ch02/Submission.lean`

The snapshot Contract.lean is byte-identical to the workspace contract, and the snapshot project declares no Submission.* names.

The pinned Mathlib supplies everything the three children use, and each lemma is available in the frozen import closure (checked with #check after import GMT.Ch02.Submission):
- ContDiff.differentiable, ContDiff.continuous_fderiv and intervalIntegral.integral_eq_sub_of_hasDerivAt;
- enorm_integral_le_lintegral_enorm and ContinuousLinearMap.le_opENorm;
- lintegral_lintegral_swap (Measure/Prod.lean);
- MeasurePreserving.setLIntegral_comp_emb (Integral/Lebesgue/Map.lean);
- measurePreserving_sub_right, lintegral_sub_right_eq_self and quasiMeasurePreserving_sub_of_right_invariant, the to_additive forms of the div lemmas in Group/Measure.lean, Group/LIntegral.lean and Group/Prod.lean;
- Measure.AbsolutelyContinuous.prod and enorm_add₃_le;
- convolution_lsmul, ConvolutionExistsAt and HasCompactSupport.convolutionExists_left (Analysis/Convolution.lean);
- ofReal_integral_eq_lintegral_ofReal.

The parent glue additionally uses:
- HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean), which is in the frozen closure;
- ContDiffBump.normed with contDiff_normed, nonneg_normed, support_normed_eq and integral_normed (BumpFunction/Normed.lean). These are not in the frozen closure: Avail2.lean reports an unknown constant. The parent must therefore add import Mathlib.Analysis.Calculus.BumpFunction.Normed, which alone suffices (Assembly2.lean).

None of the three child estimates exists in Mathlib:
- there is no L¹ or Lp translation lemma;
- the only lintegral bounds in terms of fderiv are the Jacobian change-of-variables lemmas;
- no file mentions 'mollif';
- the existing convolution error bounds (dist_convolution_le, dist_normed_convolution_le, enorm_convolution_le) are pointwise.
The three children are therefore genuine new obligations.

Machine checks:
- all three child statements elaborate in the replayed contract scope;
- the assembly proves the selected type from the sibling frozen types (as hypotheses) and the three children, with standard axioms;
- full proofs of all three children compile with standard axioms;
- the three names are unused in dag.json, DAG.md, dag.mmd and nodes/*/*.

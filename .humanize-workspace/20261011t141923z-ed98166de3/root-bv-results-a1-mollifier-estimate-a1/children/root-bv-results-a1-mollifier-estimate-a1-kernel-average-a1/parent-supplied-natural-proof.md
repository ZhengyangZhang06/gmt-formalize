# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.mollifier_estimate-a1`
- Child DAG node: `root.bv_results-a1.mollifier_estimate-a1.kernel_average-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent-supplied proof (pointwise representation via ∫ρ = 1, Tonelli, and the bound on the support of ρ). F is in place of 1_W u and a general constant C is in place of ofReal(σ)·|Du|(W). The step 1 translation estimate is here the hypothesis.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n) with Lebesgue measure vol (= volume). All ∫⁻ are lower Lebesgue integrals with values in [0,∞]. ρ * F := convolution ρ F (lsmul ℝ ℝ) vol, so (ρ * F)(x) = ∫ ρ(t)•F(x − t) dt = ∫ ρ(t)F(x − t) dt (convolution_lsmul, smul_eq_mul). For real a, ‖a‖ₑ = ofReal|a|; since ρ ≥ 0, ‖ρ(t)‖ₑ = ofReal(ρ(t)). No measurability of Q is used.

1. Kernel facts. support ρ ⊆ B(0,σ) ⊆ B̄(0,σ), and B̄(0,σ) is compact because E is finite dimensional (isCompact_closedBall). So ρ has compact support (HasCompactSupport.of_support_subset_isCompact). Being continuous with compact support, ρ is integrable (Continuous.integrable_of_hasCompactSupport). If ρ(t) ≠ 0 then t ∈ support ρ ⊆ B(0,σ), i.e. ‖t‖ < σ.

2. Pointwise representation. Fix x ∈ E.
   (a) ρ is continuous with compact support, and F is integrable, hence locally integrable. So the convolution integrand t ↦ ρ(t)F(x − t) is integrable (HasCompactSupport.convolutionExists_left).
   (b) t ↦ ρ(t)F(x) is integrable, being ρ times a constant. Since ∫ρ = 1, ∫ ρ(t)F(x) dt = (∫ρ)·F(x) = F(x) (integral_mul_const).
   (c) By linearity of the integral (integral_sub),
       (ρ * F)(x) − F(x) = ∫ (ρ(t)F(x − t) − ρ(t)F(x)) dt.
   (d) By ‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ (enorm_integral_le_lintegral_enorm) and ‖ρ(t)(F(x − t) − F(x))‖ₑ = ‖ρ(t)‖ₑ·‖F(x − t) − F(x)‖ₑ (mul_sub, enorm_mul):
       ‖(ρ * F)(x) − F(x)‖ₑ ≤ ∫⁻ ‖ρ(t)‖ₑ·‖F(x − t) − F(x)‖ₑ dt.   (∗)

3. Joint measurability. Let Ψ(x, t) := ‖ρ(t)‖ₑ·‖F(x − t) − F(x)‖ₑ on E × E.
   (a) The map (x, t) ↦ x − t is quasi-measure-preserving from vol ⊗ vol to vol (quasiMeasurePreserving_sub_of_right_invariant). The projection (x, t) ↦ x is quasi-measure-preserving (Measure.quasiMeasurePreserving_fst).
   (b) F is a.e.-strongly measurable. Composing with the maps in (a) (AEStronglyMeasurable.comp_quasiMeasurePreserving), (x, t) ↦ F(x − t) and (x, t) ↦ F(x) are a.e.-strongly measurable for vol ⊗ vol.
   (c) t ↦ ‖ρ(t)‖ₑ is measurable because ρ is continuous. So Ψ is a.e.-measurable for vol ⊗ vol.
   (d) vol|_Q ≤ vol, so vol|_Q ⊗ vol is absolutely continuous with respect to vol ⊗ vol (Measure.AbsolutelyContinuous.prod). Hence Ψ is a.e.-measurable for vol|_Q ⊗ vol (AEMeasurable.mono_ac).

4. Integration over Q and Tonelli.
   (a) Integrate (∗) over Q, using monotonicity of ∫⁻.
   (b) Apply Tonelli (lintegral_lintegral_swap, by step 3; both measures are s-finite).
   (c) Pull the finite constant ‖ρ(t)‖ₑ out of the inner integral (lintegral_const_mul').
   Together:
   ∫⁻_Q ‖(ρ * F)(x) − F(x)‖ₑ dx ≤ ∫⁻_Q ∫⁻_E Ψ(x, t) dt dx = ∫⁻_E ∫⁻_Q Ψ(x, t) dx dt = ∫⁻_E ‖ρ(t)‖ₑ·(∫⁻_Q ‖F(x − t) − F(x)‖ₑ dx) dt.

5. Pointwise bound in t. For every t ∈ E,
   ‖ρ(t)‖ₑ·∫⁻_Q ‖F(x − t) − F(x)‖ₑ dx ≤ ‖ρ(t)‖ₑ·C.
   If ρ(t) = 0, both sides are 0. Otherwise ‖t‖ < σ by step 1, so the inner integral is ≤ C by the hypothesis, and multiplication by ‖ρ(t)‖ₑ is monotone.

6. Conclusion.
   (a) Steps 4–5 and monotonicity give
       ∫⁻_Q ‖(ρ * F)(x) − F(x)‖ₑ dx ≤ ∫⁻_E ‖ρ(t)‖ₑ·C dt = (∫⁻_E ‖ρ(t)‖ₑ dt)·C   (lintegral_mul_const; t ↦ ‖ρ(t)‖ₑ is measurable).
   (b) ∫⁻ ‖ρ(t)‖ₑ dt = ∫⁻ ofReal(ρ(t)) dt   (ρ ≥ 0, Real.enorm_eq_ofReal)
       = ofReal(∫ρ)   (ofReal_integral_eq_lintegral_ofReal; ρ is integrable and ≥ 0)
       = ofReal(1) = 1.
   (c) Hence ∫⁻_Q ‖(ρ * F)(x) − F(x)‖ₑ dx ≤ 1·C = C. This holds for every C ∈ [0,∞], including C = ∞.
   If σ ≤ 0 the hypotheses are inconsistent (then ρ = 0 and ∫ρ = 0 ≠ 1), and the argument above covers this case without separate treatment. ∎

## Key steps

1. support ρ ⊆ B(0,σ) ⊆ B̄(0,σ) compact, so ρ is compactly supported and integrable, and ρ(t) ≠ 0 implies ‖t‖ < σ.
2. For each x, using ∫ρ = 1 and integrability of both integrands: (ρ*F)(x) − F(x) = ∫ ρ(t)(F(x−t) − F(x)) dt, hence ‖(ρ*F)(x) − F(x)‖ₑ ≤ ∫⁻ ‖ρ(t)‖ₑ‖F(x−t) − F(x)‖ₑ dt.
3. Joint a.e.-measurability of (x,t) ↦ ‖ρ(t)‖ₑ‖F(x−t) − F(x)‖ₑ for vol|_Q ⊗ vol, via quasi-measure-preserving subtraction and projection.
4. Integrate over Q, swap by Tonelli, and bound the inner translation integral by C wherever ρ(t) ≠ 0 (there ‖t‖ < σ).
5. ∫⁻ ‖ρ‖ₑ = ofReal(∫ρ) = 1, so the total is ≤ C.

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

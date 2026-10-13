# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.translation_estimate-a1.ball_translate_lintegral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is the translation-invariance step that the parent proof (Evans, PDE, 5.8.2 Theorem 3(i); Gilbarg-Trudinger, section 7.11) uses twice: in its step 1 with w = t z, t in [0,1] ("B_r - tz lies in B_(r+|z|)"), and in its step 2 with w = z ("for x in B_r we have x - z in B_(r'), so by translation invariance ..."). The siblings contDiff_one_ball_translation_estimate and lintegral_ball_translation_difference_le call it (T).

Notation used throughout: R^n is EuclideanSpace R (Fin n) (the contract's Rn n) with Lebesgue measure lambda (Mathlib volume); B_rho := ball(0,rho), the open ball, which is empty when rho <= 0; ||v||_e denotes the extended norm in [0,infinity] (Mathlib enorm, written with subscript e); int^- denotes Mathlib's lintegral, which is defined for every [0,infinity]-valued function as the supremum of integrals of measurable simple minorants; arithmetic in [0,infinity] follows Mathlib ENNReal conventions (in particular 0*infinity = 0). 1_A denotes the indicator function of A. Fix n, F : R^n -> [0,infinity] (arbitrary, no measurability), r, s in R and w in R^n with r + |w| <= s.

Proof.
1. Inclusion. If x is in B_r then |x - w| <= |x| + |w| < r + |w| <= s, so x - w is in B_s.
2. Pointwise comparison. For every x in R^n: 1_(B_r)(x) F(x - w) <= (1_(B_s) F)(x - w). Indeed, if x is in B_r then both sides equal F(x - w), because x - w is in B_s by step 1; if x is not in B_r the left side is 0.
3. Indicator form. Open balls are measurable sets, and for a measurable set A and an arbitrary H : R^n -> [0,infinity] one has int^-_A H d lambda = int^- 1_A H d lambda (no measurability of H is needed). Hence int^-_(B_r) F(x - w) dx = int^- 1_(B_r)(x) F(x - w) dx and int^-_(B_s) F = int^- (1_(B_s) F)(y) dy.
4. Monotonicity. The lintegral is monotone for arbitrary functions, so step 2 gives int^- 1_(B_r)(x) F(x - w) dx <= int^- (1_(B_s) F)(x - w) dx.
5. Translation invariance. lambda is invariant under translations (it is an additive Haar measure on the commutative group R^n, hence right-invariant), and x |-> x - w is a measurable equivalence of R^n (inverse x |-> x + w) that maps lambda to lambda. Change of variables along a measurable equivalence holds for every [0,infinity]-valued function, so int^- H(x - w) dx = int^- H(y) dy for every H : R^n -> [0,infinity]. Apply this with H := 1_(B_s) F.
6. Conclusion. By steps 3, 4, 5 and 3 again: int^-_(B_r) F(x - w) dx = int^- 1_(B_r)(x) F(x - w) dx <= int^- (1_(B_s) F)(x - w) dx = int^- (1_(B_s) F)(y) dy = int^-_(B_s) F(y) dy. QED

Formalization note (checked against the pinned Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; a complete Lean proof of exactly this type compiled in the scratch file /tmp/te-decomp/src/Final.lean). Rewrite both sides with `rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]`; prove step 2 under `lintegral_mono` by `by_cases hx : x ∈ ball (0 : Rn n) r`, using `mem_ball_zero_iff`, `norm_sub_le`, `indicator_of_mem`, `indicator_of_notMem` and `simp`; step 5 is `lintegral_sub_right_eq_self _ w` (additive version of `lintegral_div_right_eq_self`, MeasureTheory/Group/LIntegral.lean, valid for every f).

## Key steps

1. For x in B_r: |x - w| <= |x| + |w| < r + |w| <= s, so x - w lies in B_s
2. Pointwise 1_(B_r)(x) F(x - w) <= (1_(B_s) F)(x - w); rewrite both set lintegrals as lintegrals of indicators (balls are measurable)
3. Translation invariance of Lebesgue measure for arbitrary [0,infinity]-valued functions (measurable equivalence x |-> x - w) turns the right side into int^-_(B_s) F

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; sha256sum GMT/Ch05/{Contract,Submission}.lean`
- `git -C .lake/packages/mathlib rev-parse HEAD (compared with manifest.json mathlib_commit)`
- `python3 scan of dag.json lean_name fields + rg -l '\b<proposed name>\b' over the run directory, .lake/packages/mathlib/Mathlib, .lake/packages/simongmt, GMT`
- `rg -n -e 'theorem lintegral_div_right_eq_self' -e 'theorem lintegral_indicator ' -e 'theorem restrict_preimage \{f' -e 'theorem eLpNorm_add_le \(hp1' -e 'lemma eLpNorm_nnreal_pow_eq_lintegral' -e 'theorem rpow_add_le_mul_rpow_add_rpow' -e 'lemma two_two' -e 'theorem lintegral_mul_le_Lp_mul_Lq ' -e 'theorem lintegral_lintegral_swap' -e 'theorem integral_eq_sub_of_hasDerivAt ' -e 'theorem enorm_integral_le_lintegral_enorm' -e 'theorem setLIntegral_mono \{' -e 'theorem setLIntegral_const' -e "theorem lintegral_add_right'" -e "theorem lintegral_const_mul' " -e 'theorem mul_le_mul_right \[MulLeftMono' -e 'theorem ContDiff.continuous_fderiv ' -e 'theorem ContDiff.differentiable \(h' -e 'def gradient \(f' -e 'theorem lintegral_mono_set ' <snapshot>/mathlib/Mathlib`
- `rg -n 'measurePreserving_div_right|comp_measurePreserving|ofReal_norm_eq_enorm|eLpNorm_of_not_aestronglyMeasurable|theorem volume_Ioc' <snapshot>/mathlib/Mathlib`
- `rg -n 'add_sq_le|two_mul_le_add_sq|pow_le_pow_iff_left' Mathlib/Algebra/Order (generic lemmas need IsStrictOrderedRing / PosMulStrictMono, which ENNReal lacks)`
- `lake env lean -o /tmp/te-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=/tmp/te-decomp/olean:$LEAN_PATH lean /tmp/te-decomp/src/Final.lean'  (import GMT.Ch05.Submission; five children proved; parent assembled; #print axioms; parenthesization rfl checks)`
- `lake env bash -c 'LEAN_PATH=/tmp/te-decomp/olean:$LEAN_PATH lean /tmp/te-decomp/src/JsonCheck.lean'  (exact returned lean_statement strings re-elaborated, standalone and as Submission.X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-translation-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/MeanInequalitiesPow.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/tmp/te-decomp/src/Final.lean`
- `/tmp/te-decomp/src/JsonCheck.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Mathlib checkout has the same HEAD. Contract.lean and Submission.lean are byte-identical to the snapshot copies (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12), so Lean checks against the scratch olean apply to the frozen contract.

No ready-made match: the snapshot has no W^{1,p} difference-quotient or translation estimate (consistent with the parent audit's 0-file results for Sobolev/weak-derivative APIs). All five children therefore have to be proved, but every ingredient exists. Locations:
- Translation invariance for arbitrary [0,inf]-valued functions: lintegral_div_right_eq_self and its additive version lintegral_sub_right_eq_self (MeasureTheory/Group/LIntegral.lean:69); measurePreserving_div_right/sub_right (MeasureTheory/Group/Measure.lean:228).
- Restriction and composition: MeasurePreserving.restrict_preimage (Dynamics/Ergodic/MeasurePreserving.lean:77); AEStronglyMeasurable.comp_measurePreserving (MeasureTheory/Function/StronglyMeasurable/Lemmas.lean:38).
- Set lintegrals: lintegral_indicator (Integral/Lebesgue/Basic.lean:510); setLIntegral_mono and setLIntegral_const (same file, :246 and :121); lintegral_add_right' and lintegral_const_mul' (Integral/Lebesgue/Add.lean:331 and :420).
- L^2 seminorm: eLpNorm_nnreal_pow_eq_lintegral needs a measurability argument (LpSeminorm/Defs.lean:169), because in this version eLpNorm is infinity for non-AEStronglyMeasurable functions (eLpNorm_of_not_aestronglyMeasurable, :96). eLpNorm_add_le takes only 1 <= p (LpSeminorm/TriangleInequality.lean:54).
- Hoelder and power-mean inequalities: ENNReal.lintegral_mul_le_Lp_mul_Lq (Integral/MeanInequalities.lean:202) with Real.HolderConjugate.two_two (Basic/Real/ConjExponents.lean:137); ENNReal.rpow_add_le_mul_rpow_add_rpow (Analysis/MeanInequalitiesPow.lean:272).
- Calculus and Tonelli: lintegral_lintegral_swap (Measure/Prod.lean:1071); intervalIntegral.integral_eq_sub_of_hasDerivAt (IntervalIntegral/FundThmCalculus.lean:1148); enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333); ContDiff.continuous_fderiv and ContDiff.differentiable, which take n != 0 (ContDiff/Defs.lean:1271 and :1159).
- Gradient: gradient = (toDual).symm o fderiv (Gradient/Basic.lean:83).
- Order lemmas: mul_le_mul_right : b <= c -> a*b <= a*c (Algebra/Order/Monoid/Unbundled/Basic.lean:58); ofReal_norm, with ofReal_norm_eq_enorm deprecated (Analysis/Normed/Group/Basic.lean:389). The generic add_sq_le and pow_le_pow_iff_left0 do not apply to ENNReal.

Lean result: Final.lean and JsonCheck.lean compile (exit 0). All five child types elaborate after import GMT.Ch05.Submission, in namespace GMT.Ch05 and as Submission.X, and each child is fully proved using only propext, Classical.choice and Quot.sound. w12_ball_translation_estimate, with its exact frozen type, is proved from the five children plus the sibling w12_ball_smooth_approximation (exact frozen type, the only sorry).

Sources: the textbook citations (Evans, PDE 5.8.2 Thm 3(i); Gilbarg-Trudinger section 7.11) come from the parent's supplied proof. No web search was needed, since every child and the assembly were machine-checked.

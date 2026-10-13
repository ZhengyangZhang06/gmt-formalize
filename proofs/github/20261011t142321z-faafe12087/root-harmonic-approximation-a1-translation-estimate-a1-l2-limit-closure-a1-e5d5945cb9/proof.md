# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.translation_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.translation_estimate-a1.l2_limit_closure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This abstracts the end of step 2 of the parent proof ("u_j -> u in L^2(B_r), hence int_(B_r)|u_j|^2 -> int_(B_r)|u|^2; also int_(B_(r'))|grad phi_j|^2 -> int_(B_(r'))|g|^2, by Minkowski; letting j -> infinity in step 1 ..."). It proves the inequality for the limits directly with Minkowski's inequality in L^2, which also handles infinite integrals. The parent theorem applies it with mu = lambda restricted to B_r, nu = lambda restricted to B_(r+|z|), c = ENNReal.ofReal(|z|^2), a_j(x) = phi_j(x - z) - phi_j(x), a_0(x) = f(x - z) - f(x), b_j = grad phi_j, b_0 = g.

Notation. int^- denotes Mathlib's lintegral (all integrals here are lintegrals in [0,infinity], with Mathlib ENNReal arithmetic, in particular 0*infinity = 0); ||v||_e is the extended norm (Mathlib enorm). For a measure m on alpha and an m-a.e.-strongly measurable u with values in a normed additive commutative group put N_m(u) := (int^- ||u||_e^2 dm)^(1/2) in [0,infinity]; this is Mathlib's eLpNorm u 2 m, and N_m(u)^2 = int^- ||u||_e^2 dm. Fix alpha, mu, nu, E, F, c != infinity and a_j, a_0, b_j, b_0 as in the statement.

Proof.
1. Minkowski. For m-a.e.-strongly measurable u, v (same codomain): N_m(u + v) <= N_m(u) + N_m(v) (triangle inequality of the L^2 seminorm; exponent 2 >= 1). Sums and differences of a.e.-strongly measurable functions are a.e.-strongly measurable.
2. Square root of c. Put gamma := c^(1/2) in [0,infinity]. Then gamma != infinity because c != infinity and the exponent 1/2 is nonnegative, and gamma^2 = c^((1/2)*2) = c.
3. Square roots are monotone. For x, y in [0,infinity], x^2 <= y^2 implies x <= y: apply the monotone map t |-> t^(1/2) and use (t^2)^(1/2) = t.
4. Fix j. Writing a_0 = (a_0 - a_j) + a_j, step 1 gives N_mu(a_0) <= N_mu(a_0 - a_j) + N_mu(a_j).
5. By hypothesis and step 2, N_mu(a_j)^2 = int^- ||a_j||_e^2 dmu <= c int^- ||b_j||_e^2 dnu = gamma^2 N_nu(b_j)^2 = (gamma N_nu(b_j))^2, so N_mu(a_j) <= gamma N_nu(b_j) by step 3.
6. Writing b_j = (b_j - b_0) + b_0, step 1 gives N_nu(b_j) <= N_nu(b_j - b_0) + N_nu(b_0).
7. Combining 4, 5, 6 (multiplication by gamma and addition are monotone on [0,infinity]): for every j, N_mu(a_0) <= N_mu(a_0 - a_j) + gamma (N_nu(b_j - b_0) + N_nu(b_0)).
8. The error terms tend to 0. Since ||a_0(x) - a_j(x)||_e = ||a_j(x) - a_0(x)||_e for every x, N_mu(a_0 - a_j) = (int^- ||a_j - a_0||_e^2 dmu)^(1/2). The map t |-> t^(1/2) is continuous on [0,infinity] with 0^(1/2) = 0, so the hypothesis int^- ||a_j - a_0||_e^2 dmu -> 0 gives N_mu(a_0 - a_j) -> 0. Likewise N_nu(b_j - b_0) = (int^- ||b_j - b_0||_e^2 dnu)^(1/2) -> 0.
9. Passage to the limit. Addition on [0,infinity] is continuous, and multiplication by the finite constant gamma is continuous, so the right side of step 7 converges to 0 + gamma (0 + N_nu(b_0)) = gamma N_nu(b_0). A constant bounded by every term of a convergent sequence is bounded by its limit, hence N_mu(a_0) <= gamma N_nu(b_0).
10. Squaring (monotone on [0,infinity]) and step 2: int^- ||a_0||_e^2 dmu = N_mu(a_0)^2 <= (gamma N_nu(b_0))^2 = gamma^2 N_nu(b_0)^2 = c int^- ||b_0||_e^2 dnu. QED

Formalization notes (checked against the pinned Mathlib 25730c7c759d108ef87ab70af2342a196760f79d; a complete Lean proof of exactly this type compiled in the scratch file /tmp/te-decomp/src/Final.lean).
- In this Mathlib `eLpNorm u p m` is defined to be infinity when u is not a.e.-strongly measurable (`eLpNorm_of_not_aestronglyMeasurable`), so the identity `eLpNorm u 2 m ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂m` needs the measurability hypothesis: `eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hu` followed by `simpa [ENNReal.rpow_two]`; the root form follows with `ENNReal.rpow_natCast`, `ENNReal.rpow_mul`, `norm_num`.
- Minkowski is `eLpNorm_add_le one_le_two` (in this version it takes only the exponent hypothesis); rewrite `eLpNorm a_0 2 mu = eLpNorm ((a_0 - a j) + a j) 2 mu` by `simp`.
- Step 2: `ENNReal.rpow_ne_top_of_nonneg`; step 3: `ENNReal.rpow_le_rpow` with exponent 1/2 (no ENNReal `pow_le_pow_iff_left` is available: ENNReal lacks `PosMulStrictMono`).
- Steps 8-9: `(ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h`, `simpa [Function.comp_def, ENNReal.zero_rpow_of_pos]`, `Tendsto.congr`, `lintegral_congr` with `enorm_sub_rev`, `Tendsto.add`, `ENNReal.Tendsto.const_mul _ (Or.inr hgamma_ne_top)`, `ge_of_tendsto'`, and `mul_le_mul_right` (in this Mathlib: `b <= c -> a * b <= a * c`).

## Key steps

1. Work with N_m(u) = eLpNorm u 2 m, whose square is int^- ||u||_e^2 dm for a.e.-strongly measurable u
2. Minkowski: N(a_0) <= N(a_0 - a_j) + N(a_j) and N(b_j) <= N(b_j - b_0) + N(b_0); the hypothesis gives N(a_j) <= c^(1/2) N(b_j) by monotonicity of square roots
3. N(a_0 - a_j) -> 0 and N(b_j - b_0) -> 0 by continuity of t |-> t^(1/2); since c^(1/2) < infinity the bound passes to the limit: N(a_0) <= c^(1/2) N(b_0); square

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

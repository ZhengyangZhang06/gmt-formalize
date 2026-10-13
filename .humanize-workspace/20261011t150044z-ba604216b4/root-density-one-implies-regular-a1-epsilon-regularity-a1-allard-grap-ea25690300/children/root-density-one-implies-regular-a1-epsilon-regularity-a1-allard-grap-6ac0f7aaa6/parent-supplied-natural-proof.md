# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 5 of the parent proof ("Definition and regularity of h"), stated abstractly for any family F with properties (i)–(iii). The parent applies it with F ε = W_ε. B̆_r(0) denotes the open ball of radius r about 0.

1. (Definition.) For x ∈ ℝⁿ put h(x) := F((R − |x|)/3)(x).

2. (Key claim.) If 0 < r < R and |x| < r, then F((R − r)/3)(x) = h(x).
Let ε := (R − r)/3 and δ := (R − |x|)/3. Then ε > 0 because r < R, and δ > 0 because |x| < r < R. Moreover
|x| + ε + δ = (2|x| + 2R − r)/3 < (2r + 2R − r)/3 = (2R + r)/3 < R,
using |x| < r and then r < R. By (iii), F ε x = F δ x = h(x).

3. (Smoothness.) Fix m ∈ ℕ. A function is C^m on a set s if every point of s has an open neighbourhood u such that it is C^m on s ∩ u (contDiffOn_of_locally_contDiffOn).
Fix x ∈ B̆_R(0) and set r := (|x| + R)/2, so 0 < r < R and |x| < r. Let u := B̆_r(0), an open set containing x, and ε₀ := (R − r)/3. Then 0 < ε₀ < R.
- By (i), F ε₀ is C^m on B̆_{R−ε₀}(0).
- B̆_R(0) ∩ u ⊆ B̆_r(0) ⊆ B̆_{R−ε₀}(0), because r < R − ε₀ = (2R + r)/3 is equivalent to r < R.
- So F ε₀ is C^m on B̆_R(0) ∩ u (ContDiffOn.mono).
- By step 2, h = F ε₀ on B̆_r(0) ⊇ B̆_R(0) ∩ u. Hence h is C^m on B̆_R(0) ∩ u (ContDiffOn.congr).
Therefore h is C^m on B̆_R(0), for every m.

4. (Harmonicity.) Fix y ∈ B̆_R(0) and let r := (|y| + R)/2 and ε₀ := (R − r)/3, as in step 3.
- B̆_r(0) is open and contains y, and h = F ε₀ on it by step 2. So h and F ε₀ agree on a neighbourhood of y.
- Functions that agree on a neighbourhood of y have the same iterated derivatives of every order at y (Filter.EventuallyEq.iteratedFDeriv, then Filter.EventuallyEq.eq_of_nhds). So iteratedFDeriv ℝ 2 h y = iteratedFDeriv ℝ 2 (F ε₀) y.
- Since 0 < ε₀ < R and |y| < r < R − ε₀, hypothesis (ii) gives
Σ_i iteratedFDeriv ℝ 2 h y ![e_i, e_i] = Σ_i iteratedFDeriv ℝ 2 (F ε₀) y ![e_i, e_i] = 0.

5. (Eventual agreement.) Fix x ∈ B̆_R(0) and put η := 2(R − |x|)/3 > 0. Let 0 < ε < η and δ := (R − |x|)/3 > 0. Then
|x| + ε + δ < |x| + 2(R − |x|)/3 + (R − |x|)/3 = R,
so (iii) gives F ε x = F δ x = h(x). The interval (0, η) belongs to the filter 𝓝[>] 0 (Ioo_mem_nhdsGT). Hence F ε x = h(x) for all ε eventually in 𝓝[>] 0.

6. (Conclusion.) Steps 3, 4 and 5 are the three required properties of the witness h from step 1. ∎

Formalization note (checked against the pinned Mathlib in about 40 lines): take `refine ⟨fun x => F ((R - ‖x‖) / 3) x, ?_, ?_, ?_⟩`. Prove the claim of step 2 once with `apply hcons` and three `linarith` goals. In step 4 rewrite with `(heq.iteratedFDeriv ℝ 2).eq_of_nhds`, where `heq : (fun x => F ((R - ‖x‖) / 3) x) =ᶠ[𝓝 y] F ((R - (‖y‖ + R) / 2) / 3)` comes from `isOpen_ball.mem_nhds`.

## Key steps

1. Define h(x) := F((R − |x|)/3)(x).
2. If 0 < r < R and |x| < r, then |x| + (R−r)/3 + (R−|x|)/3 < R, so (iii) gives h = F((R−r)/3) on B̆_r(0).
3. Near each x ∈ B̆_R(0), h equals F ε₀ (ε₀ = (R−r)/3, r = (|x|+R)/2) on the open ball B̆_r(0), where F ε₀ is C^m by (i). Hence h is C^m on B̆_R(0) (contDiffOn_of_locally_contDiffOn, ContDiffOn.congr).
4. Local equality gives equal second iterated derivatives at y (EventuallyEq.iteratedFDeriv), so Δh(y) = ΔF ε₀(y) = 0 by (ii).
5. For 0 < ε < 2(R − |x|)/3, (iii) gives F ε x = h(x); hence ∀ᶠ ε in 𝓝[>] 0, F ε x = h(x).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json  (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical); lake-manifest mathlib rev == git -C .lake/packages/mathlib rev-parse HEAD == 25730c7c`
- `grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean; sed -n 95,140p (ae_convolution_tendsto_right_of_locallyIntegrable proof)`
- `sed -n 820,860p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Average.lean  (tendsto_integral_smul_of_tendsto_average_norm_sub)`
- `grep -rn 'theorem\|lemma' Analysis/Calculus/ContDiff/Convolution.lean; grep -rn 'precompL_apply\|precompR_apply\|convolution_precompL\|convolution_precompR' Analysis/Convolution.lean Analysis/Calculus/ContDiff/Convolution.lean; sed -n 955,1000p Analysis/Convolution.lean; sed -n 55,135p Analysis/Calculus/ContDiff/Convolution.lean`
- `grep -rn 'theorem convolution_flip\|theorem convolution_comm\|convolution_symm\|theorem integral_convolution' Analysis/Convolution.lean`
- `grep -rn 'theorem iteratedFDeriv_comp_neg\|theorem iteratedFDeriv_neg_apply\|iteratedFDeriv_comp_sub\|iteratedFDeriv_comp_add_left' <snapshot>/mathlib/Mathlib; sed -n 978,1000p Analysis/Calculus/ContDiff/FTaylorSeries.lean; sed -n 280,300p Analysis/Calculus/ContDiff/Operations.lean`
- `grep -rn 'theorem Integrable.mul_prod\|theorem Integrable.prod_mul' <snapshot>/mathlib/Mathlib; sed -n 295,302p MeasureTheory/Integral/Prod.lean`
- `grep -n -A3 'theorem addHaar_real_closedBall \|theorem addHaar_real_closedBall.\|theorem addHaar_closedBall \|theorem addHaar_real_closedBall_center' MeasureTheory/Measure/Lebesgue/EqHaar.lean; grep -rn 'theorem ae_tendsto_average_norm_sub\|theorem tendsto_filterAt' MeasureTheory/Covering/*.lean`
- `python3 -I scan of every lean_name in dag.json and nodes/*/*.json (2790 files, 566 names) for dorag_ha_weyl_{radial_mollifier,conv_laplacian,mollify_harmonic,conv_swap,glue,ae_tendsto} (none reserved); regex scan of DAG lean_statements for 'smoothTransition|convolution|Besicovitch|⨍|𝓝\[>\]|iteratedFDeriv ℝ 2|indicator'`
- `grep -n 'weyl\|mollif' GMT/Ch07/Submission.lean (no match); grep -il 'weyl\|mollif\|smoothTransition\|convolution\|Besicovitch.vitaliFamily\|ae_tendsto_average' .humanize/math-wiki/*.md (only unrelated reference notes)`
- `#check batches /tmp/weyl-decomp/Names.lean, Names2.lean, Names3.lean for every cited lemma and for instances IsAddHaarMeasure/IsNegInvariant/IsAddLeftInvariant/SFinite (volume on Euclid n), HasBesicovitchCovering, SecondCountableTopology`
- `lean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = workspace .lake builds) on /tmp/weyl-decomp/{Children,Assembly,A,B1,B2,C,D,E,Full}.lean and on ChallengeCheck.lean/SolutionCheck.lean generated with gmt-compare.py contract_scope/child_modules; #print axioms on every child and on GMT.Ch07.Submission.dorag_ha_weyl_lemma`
- `python3 -I lean_contract.validate_lean_statement on the six child lean_statements (all OK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-ea25690300/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-ea25690300/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/weyl-decomp/Children.lean`
- `/tmp/weyl-decomp/Assembly.lean`
- `/tmp/weyl-decomp/Full.lean`
- `/tmp/weyl-decomp/ChallengeCheck.lean`
- `/tmp/weyl-decomp/SolutionCheck.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. GMT/Ch07/Contract.lean is byte-identical in the snapshot and the workspace and equals Submission.lean, and the workspace Mathlib checkout is the same revision. So the type checks below are in comparator scope.

Nothing is reusable. The project, the approved math-wiki and the DAG (regex scan of every lean_statement) contain no Weyl lemma, mollifier family, convolution-Laplacian, Fubini-symmetry or patching declaration, and pinned Mathlib has no ℝⁿ Weyl lemma. The six proposed names are unreserved among 566 lean_names.

Pinned Mathlib supplies every child's tools; all were verified by #check and by compiled proofs:
- Convolution calculus: convolution_def, HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right (ContDiff/Convolution.lean:61), convolution_precompR_apply (Convolution.lean:970), HasCompactSupport.convolutionExists_right, iteratedFDeriv_two_apply, iteratedFDeriv_comp_sub (FTaylorSeries.lean:978), ContinuousLinearMap.iteratedFDeriv_comp_right. There is no multivariate iteratedFDeriv_comp_neg, only a 𝕜→F version, so the reflection is done with −id via iteratedFDeriv_comp_right.
- Lebesgue differentiation: VitaliFamily.ae_tendsto_average_norm_sub (Differentiation.lean:837), Besicovitch.tendsto_filterAt (Besicovitch.lean:1060), tendsto_integral_smul_of_tendsto_average_norm_sub (Average.lean:835), Measure.addHaar_real_closedBall' (EqHaar.lean:479). ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable is the template, but ContDiffBump is not provably radial, which the mean value sibling needs, so the mollifier is built from Real.smoothTransition with contDiff_norm_sq, Measure.integral_comp_smul and finrank_euclideanSpace_fin.
- Fubini: integral_integral_swap, Integrable.mul_prod (Prod.lean:297), AEStronglyMeasurable.comp_snd, integral_sub_left_eq_self.
- Patching: contDiffOn_of_locally_contDiffOn, Filter.EventuallyEq.iteratedFDeriv, Ioo_mem_nhdsGT.

Lean results:
- All six child types elaborate in the exact comparator scope and pass validate_lean_statement.
- Every child is fully proved, and each NodeSolution `exact Submission.X` uses only [propext, Classical.choice, Quot.sound].
- The exact frozen dorag_ha_weyl_lemma type compiles from the six children plus the stubbed sibling dorag_ha_mean_value. The only extra axiom is sorryAx, coming from that stub.

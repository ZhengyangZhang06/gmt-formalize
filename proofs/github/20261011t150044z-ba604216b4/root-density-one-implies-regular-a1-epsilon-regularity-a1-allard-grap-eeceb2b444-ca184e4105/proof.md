# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.radial_mollifier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is step 0 of the parent proof (the radial mollifier ρ_ε(y) = ĝ_ε(|y|²) built from Real.smoothTransition; cf. the standard mollifier in Evans, PDE, Appendix C). Simon's own text (Ch. 5, proof of Lemma 3.1, chapter-05.txt l. 639, "Thus w is harmonic in B") uses Weyl's lemma without proof, so there is no printed argument to copy. The construction below is the parent's, with the ε-scaling written out.

1. (The profile.) Let θ := Real.smoothTransition : ℝ → ℝ.
- θ is C^∞ (Real.smoothTransition.contDiff), in particular continuous.
- 0 ≤ θ ≤ 1 (Real.smoothTransition.nonneg, Real.smoothTransition.le_one).
- θ(s) = 0 for s ≤ 0 (Real.smoothTransition.zero_of_nonpos).
- θ(s) = 1 for s ≥ 1 (Real.smoothTransition.one_of_one_le).

2. (The unscaled bump.) Define k : ℝⁿ → ℝ by k(y) := θ(1 − |y|²).
- k is continuous, as a composition of continuous maps.
- k ≥ 0 by step 1.
- k(0) = θ(1) = 1 ≠ 0.
- If |y| > 1 then 1 − |y|² < 0, so k(y) = 0. Hence k vanishes outside the compact set closedBall(0, 1), so k has compact support (HasCompactSupport.intro with isCompact_closedBall).

3. (Its integral is positive.) Put c := ∫_{ℝⁿ} k dLⁿ. Since k is continuous with compact support, it is integrable.
- k is continuous and k(0) = 1, so there is r > 0 with k(y) > 1/2 for |y| < r.
- k ≥ 0 everywhere, so c ≥ (1/2)·Lⁿ(B̆_r(0)) > 0, because a nonempty open ball has positive Lebesgue measure.
(In Lean: Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero applied to k, its compact support, 0 ≤ k and k 0 ≠ 0.)

4. (Definition of C and g.) Set C := c⁻¹. For all ε, t ∈ ℝ set g ε t := θ(1 − t/ε²)/(c·εⁿ). For the rest of the proof fix ε > 0. Then εⁿ > 0 and c·εⁿ > 0.

5. (a) Continuity. t ↦ 1 − t/ε² is continuous and θ is continuous. Dividing by the constant c·εⁿ preserves continuity. So t ↦ g ε t is continuous.

6. (b) Vanishing. Let t ≥ ε². Since ε² > 0, t/ε² ≥ 1, so 1 − t/ε² ≤ 0. By step 1, θ(1 − t/ε²) = 0, hence g ε t = 0.

7. (c) Sup bound. By step 1, 0 ≤ θ(1 − t/ε²) ≤ 1. Since c·εⁿ > 0,
0 ≤ g ε t ≤ 1/(c·εⁿ) = c⁻¹/εⁿ = C/εⁿ.
Therefore |g ε t| = g ε t ≤ C/εⁿ for every t.

8. (d) Smoothness.
- On the inner product space ℝⁿ the map y ↦ |y|² is C^∞ (contDiff_norm_sq ℝ).
- Hence y ↦ 1 − |y|²/ε² is C^∞, and so is its composition with the C^∞ function θ (ContDiff.comp).
- Dividing by the constant c·εⁿ keeps it C^∞ (ContDiff.div_const).
- Since g ε (|y|²) = θ(1 − |y|²/ε²)/(c·εⁿ), the function y ↦ g ε (|y|²) is C^m for every m ∈ ℕ.

9. (e) Normalization.
- For y ∈ ℝⁿ, |ε⁻¹·y| = ε⁻¹|y| because ε > 0. Hence k(ε⁻¹·y) = θ(1 − ε⁻²|y|²) = θ(1 − |y|²/ε²).
- Lⁿ is an additive Haar measure on ℝⁿ, and Module.finrank ℝ (Euclid n) = n (finrank_euclideanSpace_fin).
- The linear change of variables formula (Measure.integral_comp_smul with scalar ε⁻¹) gives ∫ k(ε⁻¹·y) dy = |((ε⁻¹)ⁿ)⁻¹|·∫ k = εⁿ·c.
- So ∫ θ(1 − |y|²/ε²) dy = εⁿ·c.
- Pulling the constant denominator out of the integral (integral_div): ∫ g ε (|y|²) dy = (εⁿ·c)/(c·εⁿ) = 1.

10. (Conclusion.) Steps 5–9 establish (a)–(e) for every ε > 0, with C = c⁻¹ and g as in step 4. ∎

Formalization note (checked against the pinned Lean/Mathlib in about 50 lines):
- After `set c := ∫ y, k y` and proving `0 < c`, use `clear_value c`.
- Supply positivity of `c * ε ^ n` as `mul_pos hcpos hεn`. Calling `positivity` on goals that still contain the integral times out in `whnf`.
- For (e), rewrite `MeasureTheory.Measure.integral_comp_smul volume k ε⁻¹` with `finrank_euclideanSpace_fin`, `inv_pow`, `inv_inv` and `abs_of_pos`.

## Key steps

1. θ := Real.smoothTransition is C^∞, 0 ≤ θ ≤ 1, θ = 0 on (−∞, 0] and θ(1) = 1.
2. k(y) := θ(1 − |y|²) is continuous, nonnegative, vanishes off closedBall(0,1) and has k(0) = 1, so c := ∫k ∈ (0, ∞).
3. Define C := c⁻¹ and g ε t := θ(1 − t/ε²)/(c·εⁿ).
4. For ε > 0, g ε is continuous, vanishes for t ≥ ε², satisfies 0 ≤ g ε t ≤ C/εⁿ, and y ↦ g ε(|y|²) is C^∞ (contDiff_norm_sq and composition).
5. The change of variables y = εu gives ∫θ(1 − |y|²/ε²)dy = εⁿc, hence ∫ g ε(|y|²) dy = 1.

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

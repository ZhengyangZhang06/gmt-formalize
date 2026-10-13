# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.conv_swap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 4 of the parent proof ("Symmetry in ε, δ"): Fubini applies, the inner integral is a convolution of the two kernels, and convolution of kernels is commutative. Here it is stated for any f ∈ L¹ and any continuous compactly supported kernels. The parent applies it with f = W̃, φ = ρ_ε, ψ = ρ_δ. All integrals are over ℝⁿ. Lebesgue measure is invariant under z ↦ w − z: ∫ H(w − z) dz = ∫ H(z) dz (integral_sub_left_eq_self).

1. (A general identity.) Let a, b : ℝⁿ → ℝ be continuous with compact support. We prove
(★) ∫_z (∫_y f(y)·a(x − z − y) dy)·b(z) dz = ∫_y f(y)·(∫_z a(z)·b(x − y − z) dz) dy.

1a. A continuous function with compact support is bounded (HasCompactSupport.exists_bound_of_continuous), so |a| ≤ M on ℝⁿ for some M. Also b is integrable (Continuous.integrable_of_hasCompactSupport).

1b. Let K(z, y) := f(y)·a(x − z − y)·b(z) on ℝⁿ × ℝⁿ with the product measure Lⁿ ⊗ Lⁿ.
- K is a.e.-strongly measurable: (z, y) ↦ f(y) is a.e.-strongly measurable for the product measure (AEStronglyMeasurable.comp_snd), and (z, y) ↦ a(x − z − y) and (z, y) ↦ b(z) are continuous.
- |K(z, y)| ≤ M·|b(z)|·|f(y)|.
- The right-hand side is integrable for the product measure: |b(z)|·|f(y)| is a product of integrable functions of separate variables (Integrable.mul_prod), times a constant.
Hence K is integrable on ℝⁿ × ℝⁿ (Integrable.mono').

1c. For each z, (∫_y f(y)·a(x − z − y) dy)·b(z) = ∫_y K(z, y) dy (integral_mul_const).

1d. By Fubini for the integrable K (integral_integral_swap): ∫_z ∫_y K(z, y) dy dz = ∫_y ∫_z K(z, y) dz dy.

1e. For each y, x − z − y = x − y − z, and f(y) is constant in z (integral_const_mul). So ∫_z K(z, y) dz = f(y)·∫_z a(x − y − z)·b(z) dz.

1f. For each y, put w := x − y and H(z) := a(z)·b(w − z). Then H(w − z) = a(w − z)·b(w − (w − z)) = a(x − y − z)·b(z). By invariance of Lⁿ under z ↦ w − z, ∫ H(w − z) dz = ∫ H(z) dz. That is, ∫_z a(x − y − z)·b(z) dz = ∫_z a(z)·b(x − y − z) dz.

Chaining 1c, 1d, 1e and 1f proves (★).

2. Apply (★) with (a, b) := (φ, ψ): LHS = ∫_y f(y)·(∫_z φ(z)·ψ(x − y − z) dz) dy.

3. Apply (★) with (a, b) := (ψ, φ): RHS = ∫_y f(y)·(∫_z ψ(z)·φ(x − y − z) dz) dy.

4. For each y, put w := x − y and substitute z ↦ w − z as in 1f:
∫_z φ(z)·ψ(w − z) dz = ∫_z φ(w − z)·ψ(w − (w − z)) dz = ∫_z φ(w − z)·ψ(z) dz = ∫_z ψ(z)·φ(w − z) dz,
using commutativity of multiplication in the last step. So the inner integrals in steps 2 and 3 agree for every y.

5. Hence LHS = RHS. ∎

Formalization note (checked against the pinned Mathlib in about 40 lines): prove (★) as a local `have gen` for arbitrary a, b, then `rw [gen φ ψ …, gen ψ φ …]`. Close the remaining inner-integral equality with `integral_sub_left_eq_self (fun z => φ z * ψ (x - y - z)) volume (x - y)` and `simp [mul_comm]`.

## Key steps

1. For continuous compactly supported a, b, the map (z, y) ↦ f(y)a(x−z−y)b(z) is integrable on ℝⁿ×ℝⁿ, being dominated by sup|a|·|b(z)|·|f(y)| (Integrable.mul_prod, Integrable.mono').
2. Fubini (integral_integral_swap) and the substitution z ↦ (x−y) − z give ∫_z(∫_y f(y)a(x−z−y)dy)b(z)dz = ∫_y f(y)(∫_z a(z)b(x−y−z)dz)dy.
3. Apply this with (a,b) = (φ,ψ) and with (ψ,φ). The inner kernel integrals ∫φ(z)ψ(w−z)dz and ∫ψ(z)φ(w−z)dz agree by the substitution z ↦ w − z, so the two sides are equal.

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

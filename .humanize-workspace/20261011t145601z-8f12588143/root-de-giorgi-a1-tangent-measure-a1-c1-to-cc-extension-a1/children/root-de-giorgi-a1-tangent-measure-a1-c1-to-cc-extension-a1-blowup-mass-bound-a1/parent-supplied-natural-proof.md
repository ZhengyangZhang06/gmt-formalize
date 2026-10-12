# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Child DAG node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.blowup_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 3 ('Mass bound for the blow-ups') of the supplied proof of deGiorgiTM_blowUp_tendsto_of_contDiff. It is the estimate '|(rⁿ)⁻¹ ∫ (f − φ)(η_r(y)) dμ(y)| ≤ δ(rⁿ)⁻¹μ(B_{rR}(x)) ≤ δCRⁿ' of Part 4(iii) of the grandparent proof, stated for a general bounded h.

The hypothesis μ(B_{rR}(x)) ≤ ofReal(C(rR)ⁿ) is the instance ρ = rR of the mass bound (6′) (Simon Ch. 3, proof of Theorem 4.3, (6), erratum E3). As in the supplied proof, C is replaced by C⁺ := max(C, 0) because C may be negative.

The only external input is the sibling lemma ball_integral_bound (Lean: deGiorgiTM_integral_bound_of_ball). It states: if ν(B_ρ(a)) < ∞, g is continuous, |g| ≤ M, and g(y) ≠ 0 ⇒ y ∈ B_ρ(a), then g is ν-integrable and |∫ g dν| ≤ M · ν.real(B_ρ(a)).

1. Put g(y) := h(η_{x,r}(y)) = h(r⁻¹(y − x)). The map η_{x,r} is affine, hence continuous, so g is continuous. Also |g(y)| ≤ M for every y, since |h| ≤ M everywhere.

2. Support. Let g(y) ≠ 0. Then |η_{x,r}(y)| < R by the hypothesis on h. Since r > 0, |η_{x,r}(y)| = |r⁻¹|·|y − x| = r⁻¹|y − x|. So r⁻¹|y − x| < R, i.e. |y − x| < rR. Thus g(y) ≠ 0 implies y ∈ B_{rR}(x).

3. Finiteness. μ(B_{rR}(x)) ≤ ENNReal.ofReal(C(rR)ⁿ) < ∞.

4. Apply ball_integral_bound with ν = μ, a = x, ρ = rR, the constant M and the function g. Its hypotheses are steps 1-3. It gives two facts:
 - g is μ-integrable, which is the first claim;
 - |∫ g dμ| ≤ M · μ.real(B_{rR}(x)).

5. Real value of the mass. ENNReal.ofReal(C(rR)ⁿ) ≠ ∞, and toReal is monotone on finite extended reals (ENNReal.toReal_mono). So μ.real(B_{rR}(x)) = (μ(B_{rR}(x))).toReal ≤ (ENNReal.ofReal(C(rR)ⁿ)).toReal = max(C(rR)ⁿ, 0) (ENNReal.toReal_ofReal').
 Let t := (rR)ⁿ ≥ 0.
 - If C ≥ 0, then max(Ct, 0) = Ct = max(C, 0)·t.
 - If C < 0, then Ct ≤ 0, so max(Ct, 0) = 0 = max(C, 0)·t.
 Hence μ.real(B_{rR}(x)) ≤ max(C, 0)·(rR)ⁿ.

6. M ≥ |h(0)| ≥ 0. So steps 4 and 5 give |∫ g dμ| ≤ M · max(C, 0) · (rR)ⁿ = M · max(C, 0) · rⁿ · Rⁿ.

7. Since r > 0, rⁿ > 0 and (rⁿ)⁻¹ > 0; this includes n = 0, where rⁿ = 1. Therefore |(rⁿ)⁻¹ ∫ g dμ| = (rⁿ)⁻¹·|∫ g dμ| ≤ (rⁿ)⁻¹ · M · max(C, 0) · rⁿ · Rⁿ = M · max(C, 0) · Rⁿ. Since ∫ g dμ = ∫ h(η_{x,r}(y)) dμ(y), this is the second claim. ∎

## Key steps

1. g = h ∘ η_{x,r} is continuous (η_{x,r} is affine) and bounded by M.
2. g(y) ≠ 0 ⇒ r⁻¹|y − x| < R ⇒ y ∈ B_{rR}(x). Also μ(B_{rR}(x)) ≤ ofReal(C(rR)ⁿ) < ∞.
3. The sibling ball_integral_bound (ν = μ, a = x, ρ = rR) gives that g is μ-integrable and |∫ g dμ| ≤ M · μ.real(B_{rR}(x)).
4. μ.real(B_{rR}(x)) ≤ max(C(rR)ⁿ, 0) ≤ max(C, 0)·(rR)ⁿ (ENNReal.toReal_mono, ENNReal.toReal_ofReal', case split on the sign of C).
5. With M ≥ 0 and rⁿ > 0, |(rⁿ)⁻¹∫ g dμ| ≤ M · max(C, 0) · Rⁿ.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean; git show 04be0f6611c8d054d3d52fc7c1ee131652c23087:GMT/Ch03/Submission.lean | cmp - GMT/Ch03/Submission.lean; cmp GMT/Ch03/Submission.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem exists_contDiff_tsupport_subset|theorem dist_convolution_le|theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero|theorem norm_setIntegral_le_of_norm_le_const\b|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem integrableOn_iff_integrable_of_support_subset|theorem toReal_ofReal'|theorem toReal_mono\b|theorem support_eq|theorem one_of_mem_closedBall|theorem UniformContinuous.exists_contDiff_dist_le|theorem dist_normed_convolution_le" <snapshot>/mathlib/Mathlib`
- `rg -n "contDiff_convolution_left|theorem _root_.HasCompactSupport.convolution|uniformContinuous_of_continuous|bounded_above_of_compact_support" <snapshot>/mathlib/Mathlib`
- `rg -n "integrableOn_of_bounded|Ioo_mem_nhdsGT\b" <snapshot>/mathlib/Mathlib`
- `sed -n 88,96p Topology/UniformSpace/HeineCantor.lean; sed -n 810,822p Analysis/Convolution.lean; sed -n 425,432p Analysis/Calculus/ContDiff/Convolution.lean; sed -n 43,50p Analysis/Calculus/BumpFunction/FiniteDimension.lean (snapshot)`
- `grep -n 'def blowUpMap' -A 6 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; grep -n 'Rn\b' GMT/Ch03/Contract.lean`
- `python3 -I /tmp/c1cc-decomp-a3/scripts/mkchallenges.py <verifier> GMT/Ch03/Contract.lean /tmp/c1cc-decomp-a3/challenges children.json dag.json (gmt-compare layout+child_modules contract mode, lean_contract.validate_lean_statement, parent type == dag.json)`
- `lake env lean /tmp/c1cc-decomp-a3/challenges/Challenge_{smooth_approx,ball_integral_bound,blowup_mass_bound,parent_c1_to_cc_extension}.lean`
- `lake env lean /tmp/c1cc-decomp-a3/lean/Avail.lean (#check of every cited lemma; #synth MeasurableSpace (Rn 0), BorelSpace (Rn 3), IsAddHaarMeasure volume on Rn 0)`
- `lake env lean /tmp/c1cc-decomp-a3/lean/Inst.lean (EuclideanSpace.norm_eq, ball/norm compatibility, blowUpMap = r⁻¹ • (y - x) by rfl, BorelSpace (Rn N))`
- `lake env lean /tmp/c1cc-decomp-a3/lean/Full.lean (three child proofs + parent assembly + exact-type comparator targets + #print axioms)`
- `python3 -I lean_name and identical-lean_statement scan over dag.json (210 nodes)`
- `git log --no-walk --format=%T --stdin over 2420 refs (1516 unique trees) | xargs -n 100 git grep -l -w -e deGiorgiTM_cc_contDiff_approx -e deGiorgiTM_integral_bound_of_ball -e deGiorgiTM_blowUp_integral_bound -- 'GMT/*.lean' (positive control: deGiorgiTM_halfSpace_integral_fderiv found)`
- `grep -rlw <three names> .lake/packages/simongmt GMT <snapshot>/project; rg -l -w <three names> <snapshot>/mathlib`
- `python3 -I: dag.json record, issue-workers.json, run.json, decomposition-v1/v2.json, decomposition-audit/review-receipt-v1/v2.json for this node`
- `sed -n 728,748p book/chapter-03.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/c1cc-decomp-a3/scripts/children.json`
- `/tmp/c1cc-decomp-a3/scripts/mkchallenges.py`
- `/tmp/c1cc-decomp-a3/challenges/Challenge_smooth_approx.lean`
- `/tmp/c1cc-decomp-a3/challenges/Challenge_ball_integral_bound.lean`
- `/tmp/c1cc-decomp-a3/challenges/Challenge_blowup_mass_bound.lean`
- `/tmp/c1cc-decomp-a3/challenges/Challenge_parent_c1_to_cc_extension.lean`
- `/tmp/c1cc-decomp-a3/lean/Avail.lean`
- `/tmp/c1cc-decomp-a3/lean/Inst.lean`
- `/tmp/c1cc-decomp-a3/lean/Full.lean`

The snapshot Contract.lean is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). The handoff-commit Submission.lean equals both the workspace Submission and the contract, so the child import closure is the contract's.

The snapshot Mathlib provides every tool the child proofs use:
- exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45)
- ContDiffBump.support_eq and one_of_mem_closedBall (BumpFunction/Basic.lean:151, 137)
- dist_convolution_le (Convolution.lean:814)
- HasCompactSupport.convolution (Convolution.lean:568)
- HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427)
- Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Bochner/Set.lean:1031)
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486)
- norm_setIntegral_le_of_norm_le_const (Bochner/Set.lean:613)
- integrableOn_iff_integrable_of_support_subset (IntegrableOn.lean:462)
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716)
- HasCompactSupport.uniformContinuous_of_continuous (to_additive of HeineCantor.lean:91)
- Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153)
- ENNReal.toReal_ofReal' (ENNReal/Basic.lean:255)
- ENNReal.toReal_mono (ENNReal/Real.lean:67)
All of these resolve by #check after `import GMT.Ch03.Submission`.

UniformContinuous.exists_contDiff_dist_le (SmoothApprox.lean:48) and ContDiffBump.dist_normed_convolution_le (BumpFunction/Convolution.lean:71) exist in the snapshot but are not in the closure (unknown constant). So the smoothing child must hand-build the mollifier. SimonGMT supplies only blowUpMap x r y = r⁻¹ • (y − x) (Rectifiable.lean:96), and Rn N is an abbrev for EuclideanSpace ℝ (Fin N) (Contract.lean:56). No snapshot, project or SimonGMT declaration provides the three child statements.

All three child types:
- pass validate_lean_statement;
- elaborate in the generated comparator scope with WithLp.measurableSpace, PiLp.borelSpace and Haar volume;
- use the Euclidean norm, consistent with Metric.ball.
The full child proofs and the parent assembly compile with axioms [propext, Classical.choice, Quot.sound] only.

No name collision was found:
- 210 DAG nodes: no match;
- 1516 unique trees from 2420 refs: no match, while the positive control matched;
- SimonGMT, GMT and the snapshot project and Mathlib: no match.
No identical accepted type exists to reuse.

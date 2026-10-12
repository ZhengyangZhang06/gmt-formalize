# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Child DAG node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is Step 2 ('Smoothing') of the supplied proof of deGiorgiTM_blowUp_tendsto_of_contDiff. That step writes out the mollification in Part 4(iii) of the grandparent proof: 'mollifying f with radius < 1 gives φ ∈ C^∞_c with tsupport φ ⊆ B_R(0) and sup|f − φ| ≤ δ'. This fills in the approximation detail left implicit at the end of Simon Ch. 3, proof of Theorem 4.3 (chapter-03.txt lines 739-746).

Here f is an arbitrary continuous, compactly supported function and the support condition is given pointwise. In the parent, f(z) ≠ 0 ⇒ |z| < R − 1 comes from tsupport f ⊆ B_{R−1}(0). The argument is the parent's, with mollification radius ε ≤ 1/2.

Conventions. B_s(p) is the open ball. L^N = volume is Lebesgue (additive Haar) measure on ℝ^N. It is finite on compact sets, positive on nonempty open sets, and invariant under translations and under t ↦ −t. This holds for every N ≥ 0; for N = 0, ℝ^0 is a point and L^0 is the unit point mass.

1. Uniform continuity. f is continuous with compact support, hence uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous; metric form: Metric.uniformContinuous_iff). Choose ε₀ > 0 such that |z − z'| < ε₀ implies |f(z) − f(z')| < δ. Put ε := min(ε₀, 1/2). Then 0 < ε ≤ ε₀ and ε ≤ 1/2.

2. Normalized bump. Take a C¹ function ψ : ℝ^N → ℝ with compact support, ψ ≥ 0, support ψ ⊆ B_ε(0) and ψ(0) = 1. Either of the following works.
 - exists_contDiff_tsupport_subset, applied to the neighbourhood B_ε(0) of 0 with smoothness order 1, gives ψ with tsupport ψ ⊆ B_ε(0), compact support, values in [0, 1] and ψ(0) = 1.
 - The ContDiffBump centred at 0 with radii ε/2 < ε. It is smooth and nonnegative, has compact support, and its support is exactly B_ε(0) (ContDiffBump.support_eq). It equals 1 on the closed ball of radius ε/2 (ContDiffBump.one_of_mem_closedBall), in particular at 0.
 ψ is continuous, compactly supported, nonnegative and ψ(0) ≠ 0. L^N is finite on compact sets and positive on nonempty open sets. Hence c := ∫ψ dL^N > 0 (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero).
 Put κ := c⁻¹ψ. Then:
 - κ is C¹ (a constant times a C¹ function);
 - κ has compact support (support κ ⊆ support ψ);
 - κ ≥ 0;
 - ∫κ dL^N = c⁻¹c = 1;
 - κ(t) ≠ 0 implies ψ(t) ≠ 0, hence |t| < ε; that is, support κ ⊆ B_ε(0).

3. Mollification. Let φ := κ ⋆ f, that is φ(z) = ∫κ(t) f(z − t) dL^N(t). This is Mathlib's convolution with the bilinear map lsmul ℝ ℝ and the measure L^N.
 - κ is C¹ with compact support, and f is continuous, hence locally integrable. So φ is C¹ (HasCompactSupport.contDiff_convolution_left, which uses the translation and reflection invariance of L^N).
 - κ and f both have compact support, so φ has compact support (HasCompactSupport.convolution).

4. Averaging estimate. Let z ∈ ℝ^N, w ∈ ℝ and η ≥ 0, and assume |f(z') − w| ≤ η for every z' ∈ B_ε(z). Then |φ(z) − w| ≤ η.
 Proof: since ∫κ = 1, φ(z) − w = ∫κ(t)(f(z − t) − w) dt. If κ(t) ≠ 0 then |t| < ε, so z − t ∈ B_ε(z) and |f(z − t) − w| ≤ η. As κ ≥ 0, |φ(z) − w| ≤ ∫κ(t)·η dt = η.
 In Mathlib this is dist_convolution_le. Its hypotheses are:
 - η ≥ 0;
 - support κ ⊆ B_ε(0);
 - κ ≥ 0 and ∫κ = 1;
 - f is a.e.-strongly measurable (f is continuous);
 - dist(f(z'), w) ≤ η for z' ∈ B_ε(z).

5. Uniform approximation. Fix z. Every z' ∈ B_ε(z) satisfies |z' − z| < ε ≤ ε₀, so |f(z') − f(z)| < δ by step 1. Step 4 with w = f(z) and η = δ gives |φ(z) − f(z)| ≤ δ.

6. Support. Let |z| ≥ R and let z' ∈ B_ε(z). Then |z'| ≥ |z| − |z − z'| > R − ε ≥ R − 1/2 > R − 1. Hence f(z') = 0, since otherwise the hypothesis would give |z'| < R − 1. Step 4 with w = 0 and η = 0 gives |φ(z)| ≤ 0, so φ(z) = 0. Contrapositively, φ(z) ≠ 0 implies |z| < R.

7. Conclusion. By steps 3, 5 and 6, φ is C¹ and has compact support. It satisfies |φ(z) − f(z)| ≤ δ for every z, and φ(z) ≠ 0 implies |z| < R. ∎

## Key steps

1. f is uniformly continuous (continuous with compact support). Choose ε₀ for δ and set ε = min(ε₀, 1/2).
2. Build a normalized C¹ bump κ = c⁻¹ψ with κ ≥ 0, ∫κ = 1, compact support and support κ ⊆ B_ε(0). Take ψ from exists_contDiff_tsupport_subset or a ContDiffBump with radii ε/2 < ε; c = ∫ψ > 0 by Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero.
3. φ = κ ⋆ f (lsmul ℝ ℝ, Lebesgue measure) is C¹ by HasCompactSupport.contDiff_convolution_left and has compact support by HasCompactSupport.convolution.
4. Averaging bound (dist_convolution_le): if |f − w| ≤ η on B_ε(z), then |φ(z) − w| ≤ η.
5. With w = f(z) and η = δ, |φ − f| ≤ δ everywhere.
6. For |z| ≥ R, f vanishes on B_ε(z), because there |z'| > R − 1/2 > R − 1. With w = 0 and η = 0 this gives φ(z) = 0, so φ(z) ≠ 0 ⇒ |z| < R.

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

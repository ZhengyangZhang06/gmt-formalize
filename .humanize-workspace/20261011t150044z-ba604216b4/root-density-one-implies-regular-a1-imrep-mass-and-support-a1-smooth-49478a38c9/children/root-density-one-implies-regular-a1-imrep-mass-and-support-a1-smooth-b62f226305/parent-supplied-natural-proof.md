# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.smooth_unit_approximation-a1.mollify_unit_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (mollification), applied to an arbitrary compactly supported continuous field g with |g| ≤ 1 and tsupport g ⊆ V. Two changes from the parent: the support margin r is chosen from tsupport g, and the constant in (N5) is the operator norm of the coefficient map. Any finite constant works there.
1. (Norm facts.) By the sibling coeff_norm_rep, fix a continuous linear map A : Λ → EuclideanSpace ℝ (Fin n → Fin P) with |α| = ‖A α‖ for all α ∈ Λ. Let C₀ := ‖A‖ ≥ 0 be its operator norm. Then
   (N5) |α| = ‖A α‖ ≤ C₀‖α‖ for all α.
2. (Support margin.) tsupport g is compact (g has compact support) and contained in the open set V. So there is r > 0 with cthickening(r, tsupport g) ⊆ V (IsCompact.exists_cthickening_subset_open).
3. (Uniform continuity.) A continuous function with compact support is uniformly continuous (HasCompactSupport.uniformContinuous_of_continuous). So there is s₀ > 0 such that ‖g(y) − g(x)‖ < ε/(C₀ + 1) whenever dist(y, x) < s₀. Put s := min(s₀, r) > 0.
4. (Kernel.) Let φ be the smooth bump function ContDiffBump (0 : ℝ^P) with rIn = s/2 and rOut = s. Let ψ := φ.normed volume be its normalization for Lebesgue measure. Then:
   - ψ is C^∞, ψ ≥ 0 and ∫ ψ = 1;
   - support ψ = B(0, s), the open ball;
   - tsupport ψ is the closed ball, so ψ has compact support;
   - ψ is continuous and integrable.
   (ContDiffBump.contDiff_normed, nonneg_normed, integral_normed, support_normed_eq, hasCompactSupport_normed, continuous_normed, integrable_normed.)
5. (Definition.) Let ω := ψ ⋆ g, that is ω(x) = ∫ ψ(t)·g(x − t) dt. In Mathlib this is convolution ψ g (lsmul ℝ ℝ) volume, a Bochner integral in the complete space Λ. For each x, the integrand t ↦ ψ(t)·g(x − t) is continuous and vanishes outside the compact set tsupport ψ, hence integrable (HasCompactSupport.convolutionExists_left, ConvolutionExistsAt.integrable).
6. (Smoothness.) ψ is C^∞ with compact support, and g is continuous, hence locally integrable. So ω is C^∞ (HasCompactSupport.contDiff_convolution_left, with smoothness order ⊤).
7. (Support.)
   - ψ and g both have compact support, so ω has compact support (HasCompactSupport.convolution).
   - support ω ⊆ support ψ + support g (support_convolution_subset).
   - If y = t + z with ‖t‖ < s and z ∈ support g ⊆ tsupport g, then dist(y, z) = ‖t‖ < s, so y ∈ thickening(s, tsupport g). Thus support ω ⊆ thickening(s, tsupport g).
   - Hence tsupport ω ⊆ closure(thickening(s, tsupport g)) ⊆ cthickening(s, tsupport g) ⊆ cthickening(r, tsupport g) ⊆ V, using s ≤ r and step 2.
   Together with step 6, ω is C^∞ with compact support (IsTestForm ω) and tsupport ω ⊆ V.
8. (Bound |ω| ≤ 1; this is (N4) of the parent.) Fix x. A is continuous linear and the integrand of step 5 is integrable, so A commutes with the integral (ContinuousLinearMap.integral_comp_comm) and with scalar multiplication: A(ω(x)) = ∫ ψ(t)·A(g(x − t)) dt. Hence
   |ω(x)| = ‖A(ω(x))‖ ≤ ∫ ‖ψ(t)·A(g(x − t))‖ dt = ∫ ψ(t)·|g(x − t)| dt ≤ ∫ ψ(t) dt = 1.
   This uses norm_integral_le_integral_norm, ψ ≥ 0, |g| ≤ 1, monotonicity of the integral (integral_mono_of_nonneg; ψ is integrable) and ∫ ψ = 1.
9. (Approximation.) Fix x.
   - For every y ∈ B(x, s), dist(y, x) < s ≤ s₀, so ‖g(y) − g(x)‖ ≤ ε/(C₀ + 1) by step 3.
   - Since ∫ ψ = 1, ω(x) − g(x) = ∫ ψ(t)·(g(x − t) − g(x)) dt. Because ψ ≥ 0 and support ψ ⊆ B(0, s), only t with ‖t‖ < s contribute, i.e. those with x − t ∈ B(x, s). So ‖ω(x) − g(x)‖ ≤ ε/(C₀ + 1). This is ContDiffBump.dist_normed_convolution_le; g is a.e.-strongly measurable because it is continuous.
   - By (N5), |ω(x) − g(x)| ≤ C₀‖ω(x) − g(x)‖ ≤ C₀·ε/(C₀ + 1) ≤ ε.
10. Steps 6–9 show that ω is C^∞ with compact support, tsupport ω ⊆ V, |ω| ≤ 1 everywhere, and |ω − g| ≤ ε everywhere.

## Key steps

1. Fix A with |α| = ‖Aα‖; then |α| ≤ ‖A‖·‖α‖.
2. Choose r > 0 with cthickening(r, tsupport g) ⊆ V. By uniform continuity, choose 0 < s ≤ r with ‖g(y) − g(x)‖ < ε/(‖A‖+1) whenever dist(y,x) < s.
3. Convolve g with a normalized smooth bump ψ of radius s. Then ω = ψ ⋆ g is C^∞ with compact support and tsupport ω ⊆ cthickening(s, tsupport g) ⊆ V.
4. A commutes with the integral, so |ω(x)| ≤ ∫ ψ(t)|g(x−t)| dt ≤ 1.
5. dist_normed_convolution_le gives ‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1), hence |ω(x) − g(x)| ≤ ε.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/{parent-child-handoff.json,parent-supplied-natural-proof.md,parent-supplied-plan.md}`
- `python3 scan of dag.json nodes for lean_name/lean_statement containing smooth|testForm_approx|covectorEuclideanNorm|finiteDimensional (statuses and reserved names)`
- `grep -n covectorEuclideanNorm lake-packages-25730c7c/simongmt/Poincare/SimonGMT (Chapter06/Mass.lean, FormSupNorm.lean); grep -n 'Covector|DifferentialForm|IsTestForm' Chapter06/Forms.lean`
- `grep -n '^namespace|^open|^end|^noncomputable section|^variable|^theorem' GMT/Ch07/Contract.lean; sed -n 545,612p verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/sua-decomp/Probe1.lean: FiniteDimensional ℝ (Covector (Euclid P) n) fails to synthesize; TietzeExtension, ContinuousMap.exists_restrict_eq and ContDiffBump.dist_normed_convolution_le are not imported by the contract`
- `rg -n 'dist_normed_convolution_le|normed_convolution_eq_right|nonneg_normed|contDiff_normed|integral_normed|support_normed_eq|hasCompactSupport_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/*.lean; cat BumpFunction/SmoothApprox.lean`
- `rg -n 'ContinuousMap.exists_restrict_eq|instTietzeExtensionTVS|TietzeExtension.of_tvs|instance.*TietzeExtension' Topology/TietzeExtension.lean Analysis/Complex/Tietze.lean`
- `rg -n 'ext_multilinear|ext_alternating' LinearAlgebra/; grep 'theorem of_injective' LinearAlgebra/FiniteDimensional/Defs.lean; grep 'instance' LinearAlgebra/Multilinear/FiniteDimensional.lean; grep 'toAlternatingMap_injective|def apply' Topology/Algebra/Module/Alternating/{Basic,Topology}.lean`
- `grep -n 'dist_convolution_le|convolutionExists|convolution_def' Analysis/Convolution.lean; grep -n 'uniformContinuous_of_continuous' Topology/UniformSpace/HeineCantor.lean; grep -n 'mem_thickening_iff|mem_thickening_iff_infDist_lt|closure_thickening_subset_cthickening|cthickening_mono' Topology/MetricSpace/Thickening.lean; grep EuclideanSpace.equiv|EuclideanSpace.norm_eq Analysis/InnerProductSpace/PiL2.lean`
- `grep -rl dor_ims_sua over the run directory and GMT/; git grep for dor_ims_sua and the four proposed names over all 541 refs (no match)`
- `lake env lean /tmp/sua-decomp/Children.lean; /tmp/sua-decomp/final/Challenges.lean; /tmp/sua-decomp/final/FinalProofs.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-smooth-49478a38c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/Basis.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/tmp/sua-decomp/Probe1.lean`
- `/tmp/sua-decomp/Children.lean`
- `/tmp/sua-decomp/final/statements.json`
- `/tmp/sua-decomp/final/Challenges.lean`
- `/tmp/sua-decomp/final/FinalProofs.lean`

Snapshot: project b4d606d, mathlib 25730c7c. SimonGMT Chapter06 provides covectorEuclideanNorm, defined as √(∑_I [StrictMono I] α(e_I)²), together with covectorEuclideanNorm_zero, _nonneg and _neg. Chapter06/Forms.lean provides Covector, DifferentialForm and IsTestForm (= ContDiff ℝ ∞ ∧ HasCompactSupport).

Missing locally:
- No FiniteDimensional instance for Covector (Euclid P) n (synthesis fails).
- No continuity, homogeneity or integral lemmas for covectorEuclideanNorm.
- No smooth unit approximation lemma.
Therefore finite-dimensionality and the coefficient-map representation become children.

Available in Mathlib and used by the child proofs:
- Tietze: ContinuousMap.exists_restrict_eq with RCLike.instTietzeExtensionTVS (Analysis/Complex/Tietze.lean, needs FiniteDimensional).
- Linear algebra: Module.Basis.ext_alternating, ContinuousAlternatingMap.toAlternatingMap_injective, FiniteDimensional.of_injective, ContinuousAlternatingMap.apply, ContinuousLinearMap.pi, EuclideanSpace.equiv and EuclideanSpace.norm_eq.
- Thickenings: IsCompact.exists_cthickening_subset_open, mem_thickening_iff(_infDist_lt), closure_thickening_subset_cthickening, cthickening_mono and IsCompact.cthickening.
- Bump functions: ContDiffBump.normed with nonneg_normed, integral_normed, support_normed_eq, hasCompactSupport_normed, contDiff_normed, continuous_normed, integrable_normed and dist_normed_convolution_le.
- Convolution and integration: HasCompactSupport.contDiff_convolution_left, HasCompactSupport.convolution, support_convolution_subset, HasCompactSupport.convolutionExists_left, convolution_def, ContinuousLinearMap.integral_comp_comm and HasCompactSupport.uniformContinuous_of_continuous.
These live in modules that the contract does not import, so child proofs must import them in Submission.lean. The statements need only the contract imports.

Names: no dor_ims_sua* name occurs in dag.json, the run directory, GMT/ or any of the 541 git refs. No accepted declaration has an identical type, so nothing is reused.

Lean checks:
- The four exact child types elaborate after `import GMT.Ch07.Submission` in the replayed contract scope.
- Full proofs of all four children, and of the frozen parent from children 3 and 4, compile.
- #print axioms shows only propext, Classical.choice and Quot.sound.

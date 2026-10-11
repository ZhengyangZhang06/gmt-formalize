# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.tangent_measure-a1`
- Child DAG node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the supplied parent proof, Step 4 (parent Part 4(iii)): 'choose R > 1 with tsupport f ⊆ B_{R−1}(0). Given δ > 0, mollifying f with radius < 1 gives φ ∈ C^∞_c with tsupport φ ⊆ B_R(0) and sup|f − φ| ≤ δ ... |(rⁿ)⁻¹ ∫ (f − φ)(η_r(y)) dμ(y)| ≤ δ(rⁿ)⁻¹μ(B_{rR}(x)) ≤ δCRⁿ, and |∫_P f dHⁿ − ∫_P φ dHⁿ| ≤ δHⁿ(P ∩ B_R(0)) ... limsup ≤ δ(C + ω_n)Rⁿ'. It writes out the last sentence of Simon Ch. 3, proof of Theorem 4.3, chapter-03.txt lines 739-746, together with the mass bound (6') (erratum E3). Three changes from the supplied text: the limit measure σ is arbitrary (σ = Hⁿ⌞P in the parent), with σ(B_R(0)) < ∞ replacing Hⁿ(P ∩ B_R(0)) = ω_nRⁿ; C is replaced by C⁺ := max(C, 0), because the hypothesis allows C < 0; and the mollification radius is at most 1/2.

Notation. η_r := η_{x,r}, so η_r(y) = r⁻¹(y − x). For h : ℝ^N → ℝ, L_r(h) := (rⁿ)⁻¹∫h(η_r(y))dμ(y) and L(h) := ∫h dσ.

1. Choice of R. tsupport f is compact, hence contained in some B_{R₀}(0). Put R := max(R₀, 0) + 1. Then R ≥ 1 and tsupport f ⊆ B_{R−1}(0); in particular f(z) ≠ 0 implies |z| < R. Put C⁺ := max(C, 0) ≥ 0, and let S ≥ 0 be the real value of σ(B_R(0)), which is finite by hypothesis.

2. Smoothing. Claim: for every δ > 0 there is a C¹ function φ : ℝ^N → ℝ with compact support such that |φ(z) − f(z)| ≤ δ for all z, and φ(z) ≠ 0 implies |z| < R.
 (a) f is uniformly continuous, being continuous with compact support (HasCompactSupport.uniformContinuous_of_continuous). Choose ε₀ > 0 with |z − z'| < ε₀ ⇒ |f(z) − f(z')| < δ, and put ε := min(ε₀, 1/2) > 0.
 (b) Choose ψ ∈ C^∞(ℝ^N) with compact support, tsupport ψ ⊆ B_ε(0), values in [0, 1] and ψ(0) = 1 (exists_contDiff_tsupport_subset). Then c := ∫ψ dL^N > 0 (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero). Put κ := c⁻¹ψ. It is C^∞ (hence C¹), κ ≥ 0, it has compact support, ∫κ = 1, and {κ ≠ 0} ⊆ B_ε(0).
 (c) Let φ := κ ⋆ f, i.e. φ(z) = ∫κ(t) f(z − t) dt (Mathlib convolution with the bilinear map lsmul ℝ ℝ and Lebesgue measure). φ is C¹ by HasCompactSupport.contDiff_convolution_left: κ is C¹ with compact support, and f is continuous, hence locally integrable. φ has compact support by HasCompactSupport.convolution.
 (d) Averaging bound (dist_convolution_le, using κ ≥ 0, ∫κ = 1 and {κ ≠ 0} ⊆ B_ε(0)): for every z and η ≥ 0, if |f(z') − f(z)| ≤ η for all z' ∈ B_ε(z), then |φ(z) − f(z)| ≤ η. By (a) and ε ≤ ε₀ this applies with η = δ at every z, so |φ − f| ≤ δ everywhere.
 (e) Support. Let |z| ≥ R. Every z' with |z'| ≥ R − 1/2 lies outside B_{R−1}(0) ⊇ tsupport f, so f(z') = 0. For z' ∈ B_ε(z) we have |z'| > |z| − ε ≥ R − 1/2. Hence f(z') = 0 = f(z) on B_ε(z), and (d) with η = 0 gives φ(z) = f(z) = 0. So φ(z) ≠ 0 implies |z| < R.

3. Mass bound for the blow-ups. Let r ∈ (0, ρ₁/R). Then 0 < rR < ρ₁, so μ(B_{rR}(x)) ≤ ofReal(C(rR)ⁿ) < ∞, and its real value is at most max(C(rR)ⁿ, 0) ≤ C⁺(rR)ⁿ. Now let h be continuous with |h| ≤ M′, and such that h(z) ≠ 0 implies |z| < R.
 - If h(η_r(y)) ≠ 0 then |y − x| = r|η_r(y)| < rR.
 - So y ↦ h(η_r(y)) is continuous (η_r is affine), bounded by M′, and vanishes outside B_{rR}(x).
 - Hence it is μ-integrable (Measure.integrableOn_of_bounded, integrableOn_iff_integrable_of_support_subset), and, by setIntegral_eq_integral_of_forall_compl_eq_zero and norm_setIntegral_le_of_norm_le_const,
 |L_r(h)| ≤ (rⁿ)⁻¹ M′ μ(B_{rR}(x)) ≤ (rⁿ)⁻¹ M′ C⁺ (rR)ⁿ = M′C⁺Rⁿ.

4. Mass bound for σ. In the same way, if h is continuous, |h| ≤ M′, and h(z) ≠ 0 implies |z| < R, then h is σ-integrable (since σ(B_R(0)) < ∞) and |L(h)| ≤ M′S.

5. ε-argument. Let ε > 0.
 - Put K := C⁺Rⁿ + S + 1 > 0 and δ := ε/(2K) > 0. Take φ from step 2 for this δ, and set d := f − φ. Then d is continuous, |d| ≤ δ, and d(z) ≠ 0 implies |z| < R, since f and φ both vanish where |z| ≥ R.
 - φ is continuous with compact support, so |φ| ≤ M_φ for some M_φ.
 - By hypothesis (φ is C¹ with compact support), |L_r(φ) − L(φ)| < ε/2 for all r in some set belonging to 𝓝[>]0. Intersect it with (0, ρ₁/R) ∈ 𝓝[>]0 (Ioo_mem_nhdsGT) and fix r in the intersection.
 - Steps 3-4 (with M′ = δ for d and M′ = M_φ for φ) show that d∘η_r and φ∘η_r are μ-integrable and that d and φ are σ-integrable. By linearity (integral_add), L_r(f) = L_r(d) + L_r(φ) and L(f) = L(d) + L(φ).
 - Therefore |L_r(f) − L(f)| ≤ |L_r(d)| + |L_r(φ) − L(φ)| + |L(d)| < δC⁺Rⁿ + ε/2 + δS ≤ δK + ε/2 = ε.
 So for every ε > 0, eventually along 𝓝[>]0, |L_r(f) − L(f)| < ε. That is, (rⁿ)⁻¹∫f(η_r(y))dμ(y) → ∫f dσ as r ↓ 0 (Metric.tendsto_nhds). ∎

## Key steps

1. Choose R ≥ 1 with tsupport f ⊆ B_{R−1}(0). Set C⁺ = max(C, 0) and S = σ(B_R(0)) < ∞.
2. Mollify f with a normalized C^∞ bump of radius ε = min(ε₀, 1/2) (exists_contDiff_tsupport_subset, dist_convolution_le). This gives φ ∈ C¹_c with |φ − f| ≤ δ and φ = 0 off B_R(0).
3. For r ∈ (0, ρ₁/R) and continuous h with |h| ≤ M′ that vanishes off B_R(0): |(rⁿ)⁻¹∫h∘η_{x,r}dμ| ≤ M′C⁺Rⁿ and |∫h dσ| ≤ M′S.
4. Take δ = ε/(2(C⁺Rⁿ + S + 1)). The hypothesis for φ and the triangle inequality give |L_r(f) − L(f)| < ε eventually as r ↓ 0.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n '^def HasApproxTangentPlaneWithMultiplicity|^def IsGaussGreenPair|^def reducedBoundary|^noncomputable def reducedNormal|^noncomputable def normalAverage' <snapshot>/project/GMT/Ch03/Contract.lean`
- `rg -n 'theorem Submodule.measurePreserving_measurableEquivProd|theorem Isometry.map_euclideanHausdorffMeasure|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_preimage' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'def toSpanUnitSingleton' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_Ioi_of_hasDerivAt_of_tendsto' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `rg -n 'theorem exists_contDiff_tsupport_subset' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem dist_convolution_le' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem integral_prod_symm|theorem finrank_orthogonal_span_singleton' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem' -A 6 <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `sed -n 55,120p <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `sed -n 1,70p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `sed -n 1,340p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'euclideanDivergence' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean; grep -n 'def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `lake env lean /tmp/tm-decomp/Check1.lean ... Check6.lean (#check availability inside the import closure of GMT.Ch03.Submission)`
- `python3 -I /tmp/tm-decomp/mkchallenges.py (importlib of verifier/gmt-compare.py: child_modules + contract_scope for GMT.Ch03.main_theorem); lake env lean /tmp/tm-decomp/challenges/Challenge_*.lean`
- `lake env lean /tmp/tm-decomp/Assembly.lean; lake env lean /tmp/tm-decomp/Full.lean (#print axioms)`
- `lake env lean /tmp/tm-decomp/C1.lean C2.lean C3.lean C4.lean C5.lean (scratch child proofs)`
- `python3 -I lean_name collision check against dag.json (141 nodes); git grep 'deGiorgiTM_' over all 437 refs -- 'GMT/*.lean'; grep -rn over .lake/packages/simongmt/Poincare`
- `python3 -I: read lean_statement of nodes/root-de-giorgi-a1-{blowup-identity,density-estimates,blowup-halfspace}-a1/parent-child-handoff.json`
- `sed -n 570,760p book/chapter-03.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/Span.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tm-decomp/challenges/Challenge_halfspace_flux.lean`
- `/tmp/tm-decomp/challenges/Challenge_set_convergence_integral.lean`
- `/tmp/tm-decomp/challenges/Challenge_excess_defect.lean`
- `/tmp/tm-decomp/challenges/Challenge_c1_to_cc_extension.lean`
- `/tmp/tm-decomp/Assembly.lean`
- `/tmp/tm-decomp/Full.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). HasApproxTangentPlaneWithMultiplicity (line 113), IsGaussGreenPair (153), normalAverage (161), reducedBoundary (168) and reducedNormal (173) were read there. Neither the snapshot Mathlib nor the pinned SimonGMT contains the half-space flux identity, the set-convergence integral lemma, the excess-defect estimate or the C¹→C_c extension. SimonGMT only provides euclideanDivergence (BV.lean) and blowUpMap (Rectifiable.lean). The snapshot Mathlib provides every tool the four child proofs use, inside the import closure of GMT.Ch03.Submission (checked with #check): Submodule.measurableEquivProd and measurePreserving_measurableEquivProd, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_preimage, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LinearIsometryEquiv.toSpanUnitSingleton, LinearIsometryEquiv.measurePreserving, integral_prod_symm, integral_Ioi_of_hasDerivAt_of_tendsto, exists_contDiff_tsupport_subset, dist_convolution_le, HasCompactSupport.contDiff_convolution_left, HasCompactSupport.convolution, Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero and Submodule.finrank_orthogonal_span_singleton. Some packaged lemmas are not in the closure: SmoothApprox.lean (UniformContinuous.exists_contDiff_dist_le), ContDiffBump.dist_normed_convolution_le and MeasureTheory.AEStronglyMeasurable.inner. So the c1_to_cc_extension proof builds the mollifier from exists_contDiff_tsupport_subset and dist_convolution_le, and excess_defect obtains measurability of ⟨e, ν⟩ as (continuous_const.inner continuous_id).comp_aestronglyMeasurable. The finiteness of Hⁿ on P ∩ B_R(0) is a 10-line inline argument, so the accepted cross-branch bf_plane_closedBall_measure_eq is not reused. All four child types elaborate in the exact comparator scope. The parent assembly and the full child proofs compile with only standard axioms plus the uncle stubs. No lean_name collides with dag.json or any ref.

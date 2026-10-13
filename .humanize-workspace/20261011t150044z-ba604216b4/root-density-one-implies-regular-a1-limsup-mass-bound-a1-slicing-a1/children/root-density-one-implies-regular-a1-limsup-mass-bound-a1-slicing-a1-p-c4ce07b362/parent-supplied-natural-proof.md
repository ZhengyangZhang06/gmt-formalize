# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.pointwise_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5(g) and 6 of the parent proof, i.e. the end of Simon's proof of Ch. 6, 4.5(2) (chapter-06.txt lines 1316–1322: "Finally we let ε ↓ 0 and we use 4.2 … by considering a countable dense set of ω ∈ 𝒟ⁿ(U) one can of course show that 4.2 is applicable … except for a set F of t having L¹-measure zero, with F independent of ω"), with Remark 4.2 (Lebesgue differentiation).

Notation: Hᵏ = μHE[k]; for a k-covector α, ‖α‖ is its operator norm; μ_R := R.measure for an integer multiplicity triple R. For ω ∈ 𝒟ⁿ(U) and t ∈ ℝ put
 J(t, ω) := ∫_{M∩{f<t}} θ⟨dω, ξ⟩ dH^{n+1} − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩ dHⁿ.

1. Bounds for integer multiplicity triples. Let R = (N, φ, ζ) be an integer multiplicity triple in U of dimension k. Let β : ℝ^P → Λ^k be continuous with tsupport β ⊆ K, K ⊆ U compact, and put ‖β‖_∞ := sup‖β‖.
 - By the field `orients`, for H^k-a.e. x ∈ N, ζ(x) is a unit orientation of some k-dimensional subspace: ζ(x)(α) = ±α(τ₁,…,τ_k) with τ orthonormal. Hence |ζ(x)(α)| ≤ ‖α‖·|τ₁|⋯|τ_k| = ‖α‖.
 - The function x ↦ φ(x)ζ(x)(β(x)) is a.e. strongly measurable for H^k⌞N: ζ is a.e. strongly measurable, β is continuous, evaluation (ζ, α) ↦ ζ(α) is continuous bilinear, and φ is measurable.
 - We have |φζ(β)| ≤ ‖β‖_∞·φ·1_K H^k-a.e. on N, and μ_R(K) = ∫_{N∩K} φ dH^k < ∞ (field locallyIntegrable_mult). So the function is integrable on N.
 - For every measurable E ⊆ ℝ^P: |∫_{N∩E} φζ(β) dH^k| ≤ ‖β‖_∞·μ_R(K). The integral is linear in β.
 We apply this with (R, β) = (RT, dω), (RB, ω) and (R_s, ω), for ω ∈ 𝒟ⁿ(U). Here dω is continuous and tsupport dω ⊆ tsupport ω, a compact subset of U.

2. Limit of the cut-off integrals. Fix ω ∈ 𝒟ⁿ(U) and t ∈ ℝ. For ε > 0 let γ_ε := γ_{t−ε,t}, i.e. γ_ε(s) = min{1, max{0, (t − s)/ε}}, and put
 A_ε := ∫_M θγ_ε(f)⟨dω, ξ⟩ dH^{n+1} − ∫_{M'} θ'γ_ε(f)⟨ω, ξ'⟩ dHⁿ.
 - Pointwise limit. For every x: if f(x) < t, then γ_ε(f(x)) = 1 as soon as ε ≤ t − f(x); if f(x) ≥ t, then γ_ε(f(x)) = 0 for every ε > 0. So γ_ε(f(x)) → 1_{f(x)<t} as ε ↓ 0, and 0 ≤ γ_ε ≤ 1.
 - Dominated convergence. The integrands are measurable (f is measurable). They are dominated by θ|⟨dω, ξ⟩| on M and θ'|⟨ω, ξ'⟩| on M', which are integrable by step 1. The filter ε ↓ 0 (𝓝[>] 0) is countably generated. So A_ε → ∫_M θ1_{f<t}⟨dω, ξ⟩ − ∫_{M'} θ'1_{f<t}⟨ω, ξ'⟩ = J(t, ω), because {f < t} is measurable.

3. Lebesgue differentiation. Fix ω ∈ 𝒟ⁿ(U) and let F_ω(s) := τ(R_s)(ω), which is locally integrable by (i).
 - By the Lebesgue differentiation theorem on ℝ (Mathlib: LocallyIntegrable.ae_hasDerivAt_integral, in Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm, which must be added to the imports since GMT.Ch07.Submission does not import it), for a.e. t the function x ↦ ∫_0^x F_ω has derivative F_ω(t) at t.
 - In particular the left difference quotients converge: ε⁻¹∫_{t−ε}^{t} F_ω(s) ds → F_ω(t) as ε ↓ 0. This uses ∫_0^t − ∫_0^{t−ε} = ∫_{t−ε}^t and HasDerivAt.tendsto_slope_zero_left, or the left half of hasDerivAt_iff_tendsto_slope_left_right.
 - By (ii) with a = t − ε and b = t (so b − a = ε > 0), ε⁻¹∫_{t−ε}^t F_ω(s) ds = A_ε for every ε > 0.
 - By step 2 and uniqueness of limits, F_ω(t) = J(t, ω).
 Hence there is an L¹-null set N_ω ⊆ ℝ with τ(R_t)(ω) = J(t, ω) for every t ∉ N_ω.

4. A null set independent of ω. Let D ⊆ 𝒟ⁿ(U) be the countable set given by the sibling testform_dense (U is open). Then N := ⋃_{η∈D} N_η is L¹-null, as a countable union of null sets. Fix t ∉ N; then τ(R_t)(η) = J(t, η) for every η ∈ D.

5. Extension to all test forms. Let ω ∈ 𝒟ⁿ(U). By testform_dense choose a compact K ⊆ U and ω_k ∈ D such that tsupport ω ⊆ K, tsupport ω_k ⊆ K, ω_k → ω uniformly and dω_k → dω uniformly. Apply step 1 to β = ω_k − ω and β = dω_k − dω, whose tsupports lie in K. All integrals involved are integrals of integrable functions and hence linear. We get:
 - |τ(R_t)(ω_k) − τ(R_t)(ω)| ≤ ‖ω_k − ω‖_∞·μ_{R_t}(K) → 0, with μ_{R_t}(K) < ∞ since R_t is an integer multiplicity triple in U;
 - |∫_{M∩{f<t}} θ⟨dω_k, ξ⟩ − ∫_{M∩{f<t}} θ⟨dω, ξ⟩| ≤ ‖dω_k − dω‖_∞·μ_{RT}(K) → 0;
 - |∫_{M'∩{f<t}} θ'⟨ω_k, ξ'⟩ − ∫_{M'∩{f<t}} θ'⟨ω, ξ'⟩| ≤ ‖ω_k − ω‖_∞·μ_{RB}(K) → 0.
 Hence τ(R_t)(ω_k) → τ(R_t)(ω) and J(t, ω_k) → J(t, ω). Since τ(R_t)(ω_k) = J(t, ω_k) for all k, we get τ(R_t)(ω) = J(t, ω).

6. Conclusion. The null set N does not depend on ω. So for every t ∉ N, i.e. for L¹-a.e. t, τ(R_t)(ω) = J(t, ω) holds simultaneously for all ω ∈ 𝒟ⁿ(U). This is the claim. ∎

## Key steps

1. Integer multiplicity triples give integrable pairings with |∫ θ_R ζ(β)| ≤ sup‖β‖·μ_R(K), because unit orientations have norm at most 1.
2. Dominated convergence: the integrals with the cut-off γ_{t−ε,t} tend to the {f<t} integrals J(t, ω) as ε ↓ 0.
3. Lebesgue differentiation and hypothesis (ii) with (a, b) = (t−ε, t) give τ(R_t)(ω) = J(t, ω) off a null set N_ω.
4. Take the union of the N_η over the countable family D from testform_dense.
5. Extend from D to all ω using uniform convergence of ω_k and dω_k with common compact support, together with the bound of step 1.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn -i 'slice|coarea|co-area|countable dense|SeparableSpace' local-references/123e8435b4a2469b/project/GMT --include=*.lean`
- `grep -n 'def |theorem |abbrev ' simongmt Chapter03/{Differential,Rectifiable}.lean, Chapter02/{Lipschitz,WhitneyExtension,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean, Chapter06/{Forms,Currents,Mass}.lean`
- `grep -rn 'ae_hasDerivAt_integral|ae_tendsto_average' snapshot mathlib Mathlib/MeasureTheory`
- `grep -rn 'SecondCountableTopology C(|SeparableSpace C(' snapshot mathlib Mathlib`
- `grep -rn 'exists_measurable_superset_of_null|integral_lineDeriv_mul_eq|tendsto_slope_zero_left|hasDerivAt_iff_tendsto_slope_left_right|tendsto_integral_filter_of_dominated_convergence' snapshot mathlib Mathlib`
- `dag.json scans: lean_name collision check for dor_lmbs_* (679 nodes, none); regex 'countable dense|separab|TendstoUniformly' and 'co-?area|Lebesgue point|mollif|tangential gradient|approxTangentPlane|Rademacher' over node statements; children of root.compactness_of_minimizing_currents-a1.slicing-a1`
- `git grep dor_lmbs_ over all local branches (no match); git show <accepted branches>:GMT/Ch07/Submission.lean | grep -c '^import' (extra Mathlib imports are used by accepted nodes)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the three statements; lake env lean on the three generated challenge files`
- `lake env lean /tmp/dor-slicing-decomp/Assembly.lean (#print axioms parent_from_children)`
- `lake env lean /tmp/dor-slicing-decomp/Inst.lean (TendstoUniformly on Covector = norm-uniform; default volume; intervalIntegral = Ioc integral; empty IMRep exists)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v6.json`
- `/tmp/dor-slicing-decomp/Assembly.lean`
- `/tmp/dor-slicing-decomp/Inst.lean`
- `/tmp/dor-slicing-decomp/challenges/slice_family_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/testform_dense_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/pointwise_identity_Challenge.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No current slicing, rectifiable co-area formula or countable dense family of test forms exists as a proved declaration:
- The snapshot's GMT/Ch02 and GMT/Ch06 contracts state CoareaFormula, C1Sard, IsSlice and SlicingTheorem, but only as unproven specs under sorry.
- SimonGMT has only linear and projection co-area, Rademacher, Whitney C¹ extension, and CountablyRectifiable/HasApproximateTangentSpaceAt.
- SimonGMT's tangentialGradient uses the ambient fderiv, so it is unusable for Lipschitz f on lower-dimensional sets. This is why no child statement mentions a tangential gradient.
- The compactness-branch slicing node cmc_slice_mass_bounds is about measure-represented currents without integer-multiplicity slices, and its children are not accepted, so none is reused.

Mathlib supplies these lemmas for the child proofs:
- LocallyIntegrable.ae_hasDerivAt_integral (needs an extra import);
- ContinuousMap.instSeparableSpace (needs an extra import);
- LipschitzWith.integral_lineDeriv_mul_eq;
- exists_measurable_superset_of_null;
- HasDerivAt.tendsto_slope_zero_left;
- tendsto_integral_filter_of_dominated_convergence.
Accepted nodes already add Mathlib imports to Submission.lean.

Lean checks:
- All three child types pass validate_lean_statement and elaborate in the exact comparator scope.
- A conditional assembly of the exact frozen parent type from the children, tangent_locality, borel_restriction and (C1) compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- TendstoUniformly on Covector is norm-uniform convergence, and the empty IMRep exists.
- No proposed name collides with any DAG node or branch.

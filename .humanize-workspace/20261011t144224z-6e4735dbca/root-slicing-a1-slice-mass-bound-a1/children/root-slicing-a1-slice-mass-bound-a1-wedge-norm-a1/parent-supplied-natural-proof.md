# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3(iv) (R5): “if α ≠ 0 choose an orthonormal basis ε₁,…,ε_P with α = |α|ε₁*; the Euclidean coefficient norm is the norm of the inner product induced on covectors, so it may be computed in this basis; writing γ = Σ_β c_β ε^β, α∧γ = |α| Σ_{β∌1} c_β ε^1∧ε^β with pairwise distinct multi-indices, so |α∧γ|² = |α|² Σ_{β∌1} c_β² ≤ |α|²|γ|².” Steps 1–3 below prove the basis independence used there; steps 4–8 carry out the computation in the adapted basis.

Notation. [P] := {0, …, P−1}; e_0, …, e_{P−1} is the standard basis of ℝ^P (e_i = EuclideanSpace.basisFun i); ⟨·,·⟩ and |·| are the Euclidean inner product and norm. A k-covector φ is a continuous alternating k-linear map (ℝ^P)^k → ℝ. For a family u = (u_0, …, u_{P−1}) of vectors and I : {0,…,k−1} → [P] put φ(u_I) := φ(u_{I(0)}, …, u_{I(k−1)}), and define
 N_u(φ) := Σ_{all I : {0..k−1} → [P]} φ(u_I)²,  Σ^<_u(φ) := Σ_{I strictly increasing} φ(u_I)².
By definition, covectorEuclideanNorm(φ) = (Σ^<_e(φ))^{1/2}. The wedge is α∧γ := alternatizeUncurryFin(α.smulRight γ); by `ContinuousAlternatingMap.alternatizeUncurryFin_apply`, for w = (w_0, …, w_m):
 (α∧γ)(w) = Σ_{i=0}^{m} (−1)^i α(w_i) γ(w_0, …, ŵ_i, …, w_m)  (ŵ_i omitted).
‖α‖ is the operator norm of α.

1. (Counting lemma.) For every k-covector φ and every family u: N_u(φ) = k!·Σ^<_u(φ). Proof. If I is not injective, the tuple (u_{I(0)}, …, u_{I(k−1)}) has two equal entries, so φ(u_I) = 0 because φ is alternating. If I is injective, let β be the strictly increasing enumeration of the k-element set I({0,…,k−1}) and σ := β⁻¹ ∘ I, a permutation of {0,…,k−1}; then I = β ∘ σ, and this representation is unique (β is determined by the image of I, then σ by I = β∘σ and injectivity of β). Conversely, for every strictly increasing β and every permutation σ, β∘σ is injective. Since φ is alternating, φ(u_{β∘σ}) = sign(σ)·φ(u_β), hence φ(u_{β∘σ})² = φ(u_β)². Therefore N_u(φ) = Σ_{β strictly increasing} Σ_{σ} φ(u_β)² = k!·Σ^<_u(φ).

2. (Basis independence of N.) If u is an orthonormal basis of ℝ^P, then N_u(φ) = N_e(φ). Proof. Every linear functional ℓ on ℝ^P is ℓ = ⟨a, ·⟩ for some a ∈ ℝ^P, and by Parseval for the orthonormal bases u and e: Σ_{i∈[P]} ℓ(u_i)² = Σ_i ⟨a, u_i⟩² = |a|² = Σ_i ⟨a, e_i⟩² = Σ_i ℓ(e_i)². For r = 0, 1, …, k define M_r := Σ_{all I} φ(w^{r,I})², where w^{r,I} is the k-tuple with entries w^{r,I}_j := e_{I(j)} for j < r and w^{r,I}_j := u_{I(j)} for j ≥ r. Then M_0 = N_u(φ) and M_k = N_e(φ). Let r < k. Fix the values I(j) for j ≠ r; then z ↦ φ(w_0, …, w_{r−1}, z, w_{r+1}, …, w_{k−1}) (the other entries being those of w^{r,I}, which do not depend on I(r)) is a linear functional ℓ, and the r-th entry of w^{r,I} is u_{I(r)} while that of w^{r+1,I} is e_{I(r)}; all other entries of w^{r,I} and w^{r+1,I} agree. Summing over I(r) ∈ [P] and using Σ_{i} ℓ(u_i)² = Σ_i ℓ(e_i)², then summing over the remaining indices, gives M_r = M_{r+1}. Hence N_u(φ) = M_0 = M_k = N_e(φ).

3. (The coefficient norm may be computed in any orthonormal basis.) For every orthonormal basis u and every k-covector φ: by steps 1 (for u and for e) and 2, k!·Σ^<_u(φ) = N_u(φ) = N_e(φ) = k!·Σ^<_e(φ); dividing by k! ≥ 1 gives covectorEuclideanNorm(φ)² = Σ^<_u(φ).

4. (Trivial case.) If α = 0, then α.smulRight γ = 0, so α∧γ = alternatizeUncurryFin 0 = 0 and covectorEuclideanNorm(α∧γ) = 0 = ‖α‖·covectorEuclideanNorm(γ). From now on α ≠ 0; in particular P ≥ 1.

5. (Adapted orthonormal basis.) By the Riesz representation on ℝ^P there is a ∈ ℝ^P with α(z) = ⟨a, z⟩ for all z, and ‖α‖ = |a| (|α(z)| ≤ |a||z| by Cauchy–Schwarz, with equality for z = a); a ≠ 0. Extend the unit vector u_0 := a/|a| to an orthonormal basis u_0, u_1, …, u_{P−1} of ℝ^P (Gram–Schmidt; e.g. `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`). Then α(u_0) = ⟨a, a⟩/|a| = |a| = ‖α‖ and, for j ≥ 1, α(u_j) = |a|·⟨u_0, u_j⟩ = 0.

6. (Values of α∧γ on the adapted basis.) Let β : {0,…,m} → [P] be strictly increasing and w := (u_{β(0)}, …, u_{β(m)}). By the formula for α∧γ, (α∧γ)(w) = Σ_{i=0}^{m} (−1)^i α(u_{β(i)}) γ(w_0, …, ŵ_i, …, w_m). For i ≥ 1 we have β(i) ≥ β(0) + i ≥ 1, so α(u_{β(i)}) = 0 and the i-th term vanishes. The i = 0 term is α(u_{β(0)})·γ(u_{β(1)}, …, u_{β(m)}), which equals ‖α‖·γ(u_{β(1)}, …, u_{β(m)}) if β(0) = 0 and equals 0 if β(0) ≥ 1. Hence
 (α∧γ)(u_β) = ‖α‖·γ(u_{β∘succ}) if β(0) = 0, and (α∧γ)(u_β) = 0 otherwise,
where β∘succ := (β(1), …, β(m)) is strictly increasing from {0,…,m−1} to [P].

7. (Estimate.) By step 3 (with k = m+1, φ = α∧γ) and step 6,
 covectorEuclideanNorm(α∧γ)² = Σ_{β strictly increasing, β(0) = 0} ‖α‖²·γ(u_{β∘succ})².
The map β ↦ β∘succ is injective on {β strictly increasing : β(0) = 0} (β is recovered by prepending the value 0) and takes values in the set of strictly increasing maps τ : {0,…,m−1} → [P]. All terms are nonnegative, hence the sum is at most ‖α‖²·Σ_{τ strictly increasing} γ(u_τ)² = ‖α‖²·covectorEuclideanNorm(γ)², by step 3 with k = m, φ = γ. (If m + 1 > P there is no strictly increasing β and the left side is 0.)

8. (Conclusion.) Both covectorEuclideanNorm(α∧γ) and ‖α‖·covectorEuclideanNorm(γ) are ≥ 0, so taking square roots in step 7 gives covectorEuclideanNorm(alternatizeUncurryFin(α.smulRight γ)) ≤ ‖α‖·covectorEuclideanNorm(γ). ∎

## Key steps

1. Counting: Σ over all index maps I of φ(u_I)² equals k!·Σ over strictly increasing I (non-injective tuples vanish; injective I = β∘σ uniquely with φ(u_{β∘σ})² = φ(u_β)²).
2. Parseval slot by slot: the full sum is the same for every orthonormal basis u, so covectorEuclideanNorm(φ)² = Σ_{β incr} φ(u_β)² in every orthonormal basis.
3. Adapted basis u_0 = a/|a| for α = ⟨a,·⟩: α(u_0) = ‖α‖ and α(u_j) = 0 for j ≠ 0.
4. (α∧γ)(u_β) = ‖α‖·γ(u_{β(1)},…,u_{β(m)}) if β(0) = 0 and 0 otherwise; injectivity of β ↦ (β(1),…,β(m)) gives |α∧γ|² ≤ ‖α‖²|γ|².

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'slicing_mb_' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem norm_deriv_le_of_lipschitz|theorem LipschitzOnWith.extend_real|theorem LipschitzWith.ae_differentiableAt|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem liminf_const_mul_of_ne_top|theorem hasDerivAt_integral_of_dominated_loc_of_lip|HasCompactSupport.contDiff_convolution_left|theorem alternatizeUncurryFin_apply|theorem tendsto_measure_biInter_gt|theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq|theorem fderiv_fun_smul|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_integral_filter_of_dominated_convergence' local-references/197bdd4b88278494/mathlib/Mathlib/{Analysis,Order,MeasureTheory,Topology,LinearAlgebra}`
- `grep -n 'covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms,Currents,FormsDuality}.lean`
- `python3 scan of dag.json (200 nodes): lean_name uniqueness of the seven proposed names; search of titles/statements/lean_statements for alternatizeUncurryFin, smulRight, liminf, Monotone, cut-off, mollif, wedge, Dini, McShane, Rademacher (no identical type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/{parent-child-handoff.json, decomposition-v3.json, decomposition-audit-v1..v4.json, decomposition-review-receipt-v1..v4.json}`
- `python3 read of .humanize/swarm-configs/*.json for github_selected_issue 676: 97b6c024c2834d99b1a86982198ed548.json max_nodes=1000 max_depth=6 (older 9bd566bbce374e36839dbfed5b2a4b01.json max_nodes=200)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope)`
- `lake env printenv LEAN_PATH; lean -o /tmp/smb_split_v5_bWB45t/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/smb_split_v5_bWB45t/check/Stmts.lean (7 child types + parent in the comparator child scope: 0 errors)`
- `lean /tmp/smb_split_v5_bWB45t/check/Instances.lean (wedge degree m+1, operator norms by rfl, C^∞ index)`
- `lean /tmp/smb_split_v5_bWB45t/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smb_split_v5_bWB45t/check/Plumbing.lean (dependency instantiations type-check)`
- `lean /tmp/smb_split_v5_bWB45t/check/Names.lean (#check of every lemma cited in the child proofs)`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/97b6c024c2834d99b1a86982198ed548.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smb_split_v5_bWB45t/check/Stmts.lean`
- `/tmp/smb_split_v5_bWB45t/check/Instances.lean`
- `/tmp/smb_split_v5_bWB45t/check/Assembly.lean`
- `/tmp/smb_split_v5_bWB45t/check/Plumbing.lean`
- `/tmp/smb_split_v5_bWB45t/check/Names.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies GeometricCurrentOn with boundary ∂T(ω) = T(dω), massOn via covectorEuclideanNorm, TestFormOn, exteriorDerivative (Mathlib's extDeriv, i.e. alternatizeUncurryFin ∘ fderiv) and tsupport_exteriorDerivative_subset. Mathlib supplies McShane extension (LipschitzOnWith.extend_real), Rademacher's theorem (LipschitzWith.ae_differentiableAt), convolution smoothness, differentiation under the integral, Lebesgue's theorem for monotone functions with the integral bound for their derivative, liminf algebra in ℝ≥0∞, dominated convergence along countably generated filters and continuity from above. Every cited name exists at the pinned revision. Neither library contains the sharp cut-off, the wedge coefficient-norm bound, the smooth approximation with an a.e. gradient bound, the slice estimates or the Dini-derivative majorant; these become the seven children. In a scratch compile of the frozen Submission, all seven child types and the parent type elaborate in the comparator's child scope. The exact parent follows from slicing_mass_representation, slicing_representation_unique, slicing_mb_pointwise and slicing_mb_density_majorant with axioms [propext, Classical.choice, Quot.sound], and the dependency instantiations type-check. No proposed name occurs in the snapshot project or among the 200 DAG nodes. The active issue-676 configuration allows 1000 nodes at depth ≤ 6. The printed Simon text (4.9–4.11) matches the supplied proof.

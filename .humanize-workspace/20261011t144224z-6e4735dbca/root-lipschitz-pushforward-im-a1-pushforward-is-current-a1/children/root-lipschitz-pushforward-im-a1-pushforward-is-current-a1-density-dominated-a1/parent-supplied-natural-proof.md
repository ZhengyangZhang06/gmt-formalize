# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_dominated-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^P = EuclideanSpace ℝ (Fin P) with norm |·|, and Hⁿ = μHE[n].
- An n-covector α is a continuous alternating n-linear map with the operator norm ‖α‖, the least C with |α(u_1, …, u_n)| ≤ C Π|u_i|.
- Λ_n = NVector denotes continuous linear functionals on n-covectors, with the operator norm.
- simpleNVector v is the n-vector α ↦ α(v_1, …, v_n). It is defined via mkContinuous with the bound Π‖v_i‖.
- For a linear A, A^#β := β(A·, …, A·) (covectorPullback n A = compContinuousLinearMapCLM A) and A_#v := nVectorPushforward n A v = v ∘ A^#.
- The used fields of IsRectifiableTriple U n M θ ξ are: nullMeasurableSet (M is Hⁿ-null-measurable), pos (θ > 0 on M), integrableOn (θ is Hⁿ-integrable on M ∩ K′′ for every compact K′′ ⊆ U), and orients.
- Write K′ := f⁻¹(K) ∩ Z and fix C ∈ ℝ with ‖L(x)‖ ≤ C for all x ∈ M ∩ K′.

1. (Push-forward bound.) For every linear A : ℝ^P → ℝ^Q and v ∈ Λ_n(ℝ^P), ‖A_#v‖ ≤ ‖A‖ⁿ‖v‖. Indeed, for an n-covector β on ℝ^Q and u_1, …, u_n ∈ ℝ^P, |(A^#β)(u_1, …, u_n)| = |β(Au_1, …, Au_n)| ≤ ‖β‖ Π|Au_i| ≤ ‖β‖‖A‖ⁿ Π|u_i|. So ‖A^#β‖ ≤ ‖A‖ⁿ‖β‖, i.e. ‖A^#‖ ≤ ‖A‖ⁿ. (Mathlib: ContinuousAlternatingMap.norm_compContinuousLinearMap_le with Fintype.card (Fin n) = n, then ContinuousLinearMap.opNorm_le_bound.) Since A_#v = v ∘ A^#, ‖A_#v‖ ≤ ‖v‖‖A^#‖ ≤ ‖A‖ⁿ‖v‖ (ContinuousLinearMap.opNorm_comp_le).

2. (‖ξ‖ ≤ 1 almost everywhere.) By orients, for Hⁿ⌞M-a.e. x there is an orthonormal τ : Fin n → ℝ^P with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. For every n-covector α, |simpleNVector τ (α)| = |α(τ_1, …, τ_n)| ≤ ‖α‖ Π|τ_i| = ‖α‖, because |τ_i| = 1. So ‖simpleNVector τ‖ ≤ Π|τ_i| = 1 (LinearMap.mkContinuous_norm_le, the bound Π‖τ_i‖ being ≥ 0). Since ‖−v‖ = ‖v‖, ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x.

3. (Almost every point lies in M ∩ Z.) M is Hⁿ-null-measurable, so Hⁿ⌞M-a.e. x lies in M (ae_restrict_mem₀). Moreover (Hⁿ⌞M)(E) = Hⁿ(E ∩ M) for every set E ⊆ ℝ^P (Measure.restrict_apply₀'). With E = ℝ^P ∖ Z this gives (Hⁿ⌞M)(ℝ^P ∖ Z) = Hⁿ(M ∖ Z) = 0 by hypothesis. Hence Hⁿ⌞M-a.e. x lies in Z.

4. (Definition and integrability of h.) Define h := 1_{K′}·Cⁿθ, i.e. h(x) = Cⁿθ(x) for x ∈ K′ and h(x) = 0 otherwise.
 - K′ is compact, hence closed, hence Borel measurable.
 - K′ ⊆ Z ⊆ U is compact, so by integrableOn θ is Hⁿ-integrable on M ∩ K′.
 - Since K′ is measurable, (Hⁿ⌞M)⌞K′ = Hⁿ⌞(K′ ∩ M) (Measure.restrict_restrict). So Cⁿθ is integrable on K′ for Hⁿ⌞M.
 - Hence its extension by zero h is Hⁿ⌞M-integrable (IntegrableOn.integrable_indicator).

5. (The bound.) Let x lie in the Hⁿ⌞M-full set where steps 2 and 3 hold (x ∈ M, x ∈ Z, ‖ξ(x)‖ ≤ 1), and suppose f(x) ∈ K. Then x ∈ f⁻¹(K) ∩ Z = K′, so x ∈ M ∩ K′ and 0 ≤ ‖L(x)‖ ≤ C. In particular C ≥ 0 and ‖L(x)‖ⁿ ≤ Cⁿ. Also θ(x) > 0 by pos. Using step 1:
 ‖θ(x)·L(x)_#ξ(x)‖ = |θ(x)| ‖L(x)_#ξ(x)‖ = θ(x) ‖L(x)_#ξ(x)‖ ≤ θ(x) ‖L(x)‖ⁿ ‖ξ(x)‖ ≤ θ(x)·Cⁿ·1 = h(x).
 The last equality holds because x ∈ K′. This proves the claim. ∎

Formalization remark, verified in the child scope: instance search does not find NormSMulClass ℝ (NVector (Eucl Q) n). Obtain ‖θ(x)·v‖ = |θ(x)|‖v‖ as (NormedSpace.toNormSMulClass).norm_smul (θ x) (nVectorPushforward n (L x) (ξ x)), with the arguments given explicitly. Likewise write norm_neg (simpleNVector τ) with an explicit argument.

## Key steps

1. ‖A_#v‖ ≤ ‖A‖ⁿ‖v‖, from ‖A^#β‖ ≤ ‖A‖ⁿ‖β‖ and A_#v = v ∘ A^#.
2. ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x, since ξ = ±simpleNVector τ with τ orthonormal.
3. Hⁿ⌞M-a.e. x lies in M ∩ Z, because M is null-measurable and Hⁿ(M ∖ Z) = 0.
4. h := 1_{K′}Cⁿθ is Hⁿ⌞M-integrable, since θ is integrable on M ∩ K′ (K′ compact ⊆ U).
5. For such x with f(x) ∈ K: x ∈ M ∩ K′, so ‖θ(x)L(x)_#ξ(x)‖ ≤ θ(x)‖L(x)‖ⁿ‖ξ(x)‖ ≤ Cⁿθ(x) = h(x).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean and project/GMT/Ch06/Submission.lean against workspace GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean (both identical)`
- `python3 listing of lean_name fields in dag.json; grep lean_name in nodes/*/decomposition-v*.json filtered on lpf (no lpf_pic_* reserved; sibling convention lpf_lli_*)`
- `grep -rl 'lpf_current_of_dominated_density|lpf_pushforward_density_aestronglyMeasurable|lpf_pushforward_density_dominated' in the run directory (no match)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and child_modules(..., 'contract') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the 3 child statements (all OK)`
- `rg -n 'theorem continuous_compContinuousLinearMapCLM|theorem norm_compContinuousLinearMap_le' mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean (lines 432, 437)`
- `rg -n 'theorem LocallyIntegrableOn.aestronglyMeasurable' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean (line 178)`
- `rg -n 'theorem ContinuousOn.aemeasurable ' mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean (line 754)`
- `rg -n 'theorem Continuous.clm_comp|theorem isBoundedBilinearMap_apply' mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean (lines 391, 448)`
- `rg -n 'theorem norm_iteratedFDeriv_zero' mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean (line 823)`
- `rg -n 'theorem restrict_apply₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean (lines 136, 637)`
- `rg -n 'theorem mkContinuous_norm_le ' mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean (line 490)`
- `grep -n 'toCurrent :=|: GeometricCurrentOn' simongmt/Poincare/SimonGMT/Chapter06/*.lean; sed -n 1,60p Chapter06/Representation.lean`
- `cat simongmt Chapter06/Currents.lean Forms.lean FormsDuality.lean CurrentLocalEquality.lean FormSupNorm.lean (TestFormOn, TestFormOnConverges, GeometricCurrentOn.continuous', support = U minus zeroRegion, support_subset_domain, nVectorPushforward = w.comp (covectorPullback n L), simpleNVector via mkContinuous)`
- `lean in scratch (LEAN_PATH from lake env plus a /tmp olean of GMT.Ch06.Submission): ChildA.lean, ChildF.lean, ChildG.lean fully proved; Full.lean parent assembly with #print axioms; 3 comparator NodeChallenge files elaborate`
- `#synth NormSMulClass ℝ (NVector (Eucl Q) n) (fails; explicit (NormedSpace.toNormSMulClass).norm_smul with explicit arguments works)`
- `grep -n '3.6|3.9|push-forward' book/chapter-06.txt; sed -n 770,880p book/chapter-06.txt; line 271 for (2.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-is-current-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/pic_scratch_lpfpic/test/Full.lean`
- `/tmp/pic_scratch_lpfpic/test/ChildA.lean`
- `/tmp/pic_scratch_lpfpic/test/ChildF.lean`
- `/tmp/pic_scratch_lpfpic/test/ChildG.lean`
- `/tmp/pic_scratch_lpfpic/test/Assembly.lean`
- `/tmp/pic_scratch_lpfpic/cmp/lpf_pic_current_of_dominated_density_Challenge.lean`
- `/tmp/pic_scratch_lpfpic/cmp/lpf_pic_density_aestronglyMeasurable_Challenge.lean`
- `/tmp/pic_scratch_lpfpic/cmp/lpf_pic_density_dominated_Challenge.lean`

Snapshot and workspace agree: snapshot project d8d46c95 (Mathlib 25730c7c) contains the frozen Ch06 Contract and Submission, byte-identical to the workspace copies.

The child scope (import GMT.Ch06.Submission plus the replayed namespace and opens) provides everything the three child statements need: Eucl, IsRectifiableTriple, NVector, nVectorPushforward, simpleNVector, TestFormOn, DifferentialForm, GeometricCurrentOn and μHE[n].

Mathlib provides the needed tools:
- ContinuousAlternatingMap.norm_compContinuousLinearMap_le and continuous_compContinuousLinearMapCLM (covectorPullback n A is compContinuousLinearMapCLM A);
- Continuous.clm_comp and isBoundedBilinearMap_apply;
- LocallyIntegrableOn.aestronglyMeasurable and ContinuousOn.aemeasurable;
- norm_iteratedFDeriv_zero, Measure.restrict_apply₀', ae_restrict_mem₀ and LinearMap.mkContinuous_norm_le.

SimonGMT gap: there is no lemma building a domain GeometricCurrentOn from a dominated integral. Representation.lean only gives algebraic whole-space Currents from assumed MassRepresentation data, so the generic child fills a real gap.

Lean quirk: NormSMulClass ℝ (NVector (Eucl Q) n) is not found by instance search. The explicit (NormedSpace.toNormSMulClass).norm_smul with explicit arguments, and norm_neg (simpleNVector τ), work.

Verification:
- No lpf_pic_* names are reserved in the DAG.
- All three child statements pass the lexical validator and elaborate in the comparator NodeChallenge scope.
- All three were fully proved in scratch Lean with only propext, Classical.choice and Quot.sound.
- The parent assembly from these three children plus the frozen lpf_rectifiable_support_null statement kernel-checks.

Book: f_#T is defined on p. 147 (chapter-06.txt lines 770-880) without a separate continuity proof; (2.7) is on p. 136.

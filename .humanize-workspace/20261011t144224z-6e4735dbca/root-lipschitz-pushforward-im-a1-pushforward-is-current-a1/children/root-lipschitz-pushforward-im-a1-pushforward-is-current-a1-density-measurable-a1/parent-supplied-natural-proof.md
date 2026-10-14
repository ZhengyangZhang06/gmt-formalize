# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.density_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^P = EuclideanSpace ℝ (Fin P) and Hⁿ = μHE[n].
- n-covectors are continuous alternating n-linear maps with the operator norm. Λ_n = NVector denotes continuous linear functionals on n-covectors, with the operator norm.
- For a linear A : ℝ^P → ℝ^Q, A^#β := β(A·, …, A·). This is covectorPullback n A, which by definition is ContinuousAlternatingMap.compContinuousLinearMapCLM A.
- A_#v := nVectorPushforward n A v = v ∘ A^#.
- The used fields of IsRectifiableTriple U n M θ ξ are: subset (M ⊆ U), integrableOn (θ is Hⁿ-integrable on M ∩ K for every compact K ⊆ U), and aestronglyMeasurable (ξ is Hⁿ⌞M-a.e. strongly measurable).

1. (θ is Hⁿ⌞M-a.e. strongly measurable.)
 (a) θ is locally Hⁿ-integrable on M. Let x ∈ M. Since M ⊆ U and U is open, there is a compact neighbourhood B_x of x with B_x ⊆ U, e.g. a closed ball B̄(x, r_x) ⊆ U (compact by Heine–Borel). By integrableOn, θ is Hⁿ-integrable on M ∩ B_x, and M ∩ B_x is a neighbourhood of x relative to M.
 (b) Since ℝ^P is second countable, countably many of these relative neighbourhoods M ∩ B_{x_m} (m ∈ ℕ) cover M (Lindelöf).
 (c) On each M ∩ B_{x_m}, θ is integrable, hence a.e. strongly measurable for Hⁿ⌞(M ∩ B_{x_m}).
 (d) A function that is a.e. strongly measurable for the restrictions of a measure to each member of a countable family is a.e. strongly measurable for the restriction to their union, here Hⁿ⌞M.
 (In Mathlib: prove LocallyIntegrableOn θ M Hⁿ using exists_compact_subset hU and inter_mem_nhdsWithin, then apply LocallyIntegrableOn.aestronglyMeasurable. Equivalently, as in the parent proof, exhaust U by compact sets K_m and write M = ⋃_m (M ∩ K_m).)

2. (Continuity of the push-forward.) Define Φ : L(ℝ^P, ℝ^Q) × Λ_n(ℝ^P) → Λ_n(ℝ^Q) by Φ(A, v) := A_#v = v ∘ A^#.
 (a) A ↦ A^# ∈ L(Λⁿ(ℝ^Q), Λⁿ(ℝ^P)) is continuous for the operator norms. For n = 0, A^# is the identity on 0-covectors and does not depend on A. For n ≥ 1, take A, A′, an n-covector β on ℝ^Q and u_1, …, u_n ∈ ℝ^P. Telescoping gives β(Au_1, …, Au_n) − β(A′u_1, …, A′u_n) = Σ_{i=1}^n β(A′u_1, …, A′u_{i−1}, (A − A′)u_i, Au_{i+1}, …, Au_n). With multilinearity this gives |(A^#β − A′^#β)(u)| ≤ n‖β‖ max(‖A‖, ‖A′‖)^{n−1} ‖A − A′‖ Π|u_i|. Hence ‖A^# − A′^#‖ ≤ n max(‖A‖, ‖A′‖)^{n−1} ‖A − A′‖ → 0 as A′ → A. (Mathlib: ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.)
 (b) Composition (v, Ψ) ↦ v ∘ Ψ of bounded linear maps is continuous, since ‖v∘Ψ − v′∘Ψ′‖ ≤ ‖v − v′‖‖Ψ‖ + ‖v′‖‖Ψ − Ψ′‖ (Mathlib: Continuous.clm_comp).
 Hence Φ(A, v) = v ∘ A^# is continuous on the product space.

3. (Measurability of L_#ξ.) L is Hⁿ⌞M-a.e. strongly measurable (hypothesis) and so is ξ (field aestronglyMeasurable). So x ↦ (L(x), ξ(x)) is Hⁿ⌞M-a.e. strongly measurable into the product (AEStronglyMeasurable.prodMk). Composing with the continuous Φ of step 2, x ↦ L(x)_#ξ(x) = nVectorPushforward n (L x) (ξ x) is Hⁿ⌞M-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable).

4. (Conclusion.) Scalar multiplication ℝ × Λ_n(ℝ^Q) → Λ_n(ℝ^Q) is continuous. So x ↦ θ(x)·L(x)_#ξ(x), the product of the a.e. strongly measurable functions from steps 1 and 3, is Hⁿ⌞M-a.e. strongly measurable (AEStronglyMeasurable.smul). ∎

## Key steps

1. θ is locally Hⁿ-integrable on M (compact neighbourhoods inside the open U and the field integrableOn), hence Hⁿ⌞M-a.e. strongly measurable by second countability.
2. (A, v) ↦ A_#v = v ∘ A^# is continuous: A ↦ A^# is continuous (telescoping estimate; Mathlib continuous_compContinuousLinearMapCLM) and composition is continuous bilinear.
3. Since L and ξ are a.e. strongly measurable, x ↦ L(x)_#ξ(x) is a.e. strongly measurable; multiplying by θ preserves this.

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

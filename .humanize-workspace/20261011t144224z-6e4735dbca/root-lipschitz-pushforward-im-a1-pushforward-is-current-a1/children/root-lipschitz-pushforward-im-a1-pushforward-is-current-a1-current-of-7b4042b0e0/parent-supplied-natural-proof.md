# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_is_current-a1.current_of_dominated_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^Q = EuclideanSpace ℝ (Fin Q) with norm |·|.
- An n-covector β is a continuous alternating n-linear map (ℝ^Q)ⁿ → ℝ with the operator norm ‖β‖. Λⁿ(ℝ^Q) denotes the space of n-covectors.
- An n-vector φ ∈ Λ_n(ℝ^Q) = NVector (Eucl Q) n is a continuous linear functional on n-covectors with the operator norm, so |φ(β)| ≤ ‖φ‖‖β‖.
- A test form ω ∈ Dⁿ(V) = TestFormOn V n is identified with its underlying map ω : ℝ^Q → Λⁿ(ℝ^Q). By definition ω is C^∞ (hence continuous), has compact support, and tsupport ω ⊆ V. Sums and scalar multiples of test forms are computed pointwise.
- 'TestFormOnConverges (ω_j) 0' means: there is a compact K ⊆ V with tsupport ω_j ⊆ K for all j (and tsupport 0 ⊆ K) such that for every k ∈ ℕ, iteratedFDeriv ℝ k ω_j → iteratedFDeriv ℝ k 0 uniformly on K.
- An element of GeometricCurrentOn V n is a linear map S : TestFormOn V n → ℝ such that S(ω_j) → 0 whenever TestFormOnConverges (ω_j) 0.
- For ω ∈ Dⁿ(V) put F_ω(x) := w(x)(ω(g(x))).

1. (Measurability of the integrands.) g is μ-a.e. measurable with values in the second-countable metrizable space ℝ^Q, hence μ-a.e. strongly measurable. Let η : ℝ^Q → Λⁿ(ℝ^Q) be continuous; then η∘g is μ-a.e. strongly measurable. The evaluation map Λ_n(ℝ^Q) × Λⁿ(ℝ^Q) → ℝ, (φ, β) ↦ φ(β), is bounded bilinear, hence continuous (Mathlib isBoundedBilinearMap_apply). Since w and η∘g are μ-a.e. strongly measurable, so is x ↦ w(x)(η(g(x))) (Continuous.comp_aestronglyMeasurable₂).

2. (Key estimate.) Let η be continuous as in step 1, and let K ⊆ ℝ^Q with tsupport η ⊆ K. Let h : ℝ^P → ℝ be μ-integrable with ‖w(x)‖ ≤ h(x) for μ-a.e. x with g(x) ∈ K. Let B ≥ 0 with ‖η(y)‖ ≤ B for all y ∈ ℝ^Q. Claim: x ↦ w(x)(η(g(x))) is μ-integrable and |∫ w(x)(η(g(x))) dμ(x)| ≤ B ∫ |h| dμ.
 Fix x in the μ-full set on which the implication [g(x) ∈ K ⇒ ‖w(x)‖ ≤ h(x)] holds.
 - If g(x) ∈ K, then |w(x)(η(g(x)))| ≤ ‖w(x)‖ ‖η(g(x))‖ ≤ |h(x)|·B.
 - If g(x) ∉ K, then g(x) ∉ tsupport η, so η(g(x)) = 0 and w(x)(η(g(x))) = w(x)(0) = 0 ≤ B|h(x)|.
 Hence |w(x)(η(g(x)))| ≤ B|h(x)| for μ-a.e. x. The function B|h| is μ-integrable. By step 1 and domination, x ↦ w(x)(η(g(x))) is μ-integrable, and |∫ w(x)(η(g(x))) dμ| ≤ ∫ B|h| dμ = B ∫ |h| dμ.

3. (S(ω) is well defined.) Let ω ∈ Dⁿ(V). K_ω := tsupport ω is compact (ω has compact support) and K_ω ⊆ V. By hypothesis choose a μ-integrable h_ω with ‖w(x)‖ ≤ h_ω(x) for μ-a.e. x with g(x) ∈ K_ω. ω is continuous with compact support, hence bounded: there is B_ω with ‖ω(y)‖ ≤ B_ω for all y, and B_ω ≥ ‖ω(0)‖ ≥ 0. Step 2 with η = ω, K = K_ω, h = h_ω, B = B_ω shows that F_ω is μ-integrable. Put S(ω) := ∫ F_ω dμ.

4. (Linearity.) Let ω₁, ω₂ ∈ Dⁿ(V) and c ∈ ℝ. Then (ω₁ + ω₂)(y) = ω₁(y) + ω₂(y) and (cω₁)(y) = c ω₁(y). Since each w(x) is linear, F_{ω₁+ω₂} = F_{ω₁} + F_{ω₂} and F_{cω₁} = c F_{ω₁} pointwise. By step 3, F_{ω₁} and F_{ω₂} are integrable, so S(ω₁ + ω₂) = ∫ F_{ω₁} dμ + ∫ F_{ω₂} dμ = S(ω₁) + S(ω₂). Also S(cω₁) = ∫ c F_{ω₁} dμ = c S(ω₁). Thus S : TestFormOn V n → ℝ is linear.

5. (Sequential continuity at 0.) Let (ω_j) satisfy TestFormOnConverges (ω_j) 0, with the compact K ⊆ V from the definition. By hypothesis choose a μ-integrable h with ‖w(x)‖ ≤ h(x) for μ-a.e. x with g(x) ∈ K, and put I := ∫ |h| dμ ≥ 0.
 Use the case k = 0. iteratedFDeriv ℝ 0 0 vanishes identically, and ‖iteratedFDeriv ℝ 0 ω_j (y)‖ = ‖ω_j(y)‖ (Mathlib norm_iteratedFDeriv_zero). So uniform convergence on K gives: for every δ > 0 there is j₀ with ‖ω_j(y)‖ < δ for all j ≥ j₀ and all y ∈ K. For y ∉ K we have y ∉ tsupport ω_j, so ω_j(y) = 0. Hence for j ≥ j₀, ‖ω_j(y)‖ ≤ δ for every y ∈ ℝ^Q.
 Given ε > 0, take δ := ε/(I + 1) > 0 and the corresponding j₀. For j ≥ j₀, ω_j is continuous with tsupport ω_j ⊆ K, so step 2 (η = ω_j, the above h, B = δ) gives |S(ω_j)| ≤ δ I = εI/(I + 1) < ε. Therefore S(ω_j) → 0.

6. (Conclusion.) By steps 4 and 5, the linear map S with this sequential continuity is an element of GeometricCurrentOn V n. By construction S(ω) = ∫ w(x)(ω(g(x))) dμ(x) for every ω ∈ TestFormOn V n. The argument uses neither openness of V nor any finiteness property of μ. ∎

## Key steps

1. For continuous η, x ↦ w(x)(η(g(x))) is μ-a.e. strongly measurable: g is a.e. measurable into ℝ^Q and the evaluation (φ, β) ↦ φ(β) is continuous bilinear.
2. If tsupport η ⊆ K and ‖η‖ ≤ B, then |w(x)(η(g x))| ≤ B|h_K(x)| μ-a.e., since the integrand vanishes when g x ∉ K. So the integrand is integrable and |∫| ≤ B∫|h_K|.
3. Each test form is bounded with compact tsupport ⊆ V, so S(ω) := ∫ w(ω∘g) dμ is defined. Linearity follows from integrability and linearity of w(x).
4. If ω_j → 0 in TestFormOnConverges with common compact K, uniform convergence of the k = 0 derivatives gives sup_y ‖ω_j(y)‖ → 0. Hence |S(ω_j)| ≤ sup‖ω_j‖·∫|h_K| → 0, and S ∈ GeometricCurrentOn V n.

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

# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1.riesz_borel-a1.pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P = EuclideanSpace ℝ (Fin P) with its Borel σ-algebra; H := EuclideanSpace ℝ (Fin N); Y := ↥U is U with the subspace topology and the subspace σ-algebra (the comap of the Borel σ-algebra of ℝ^P under ι := Subtype.val : Y → ℝ^P; it is the Borel σ-algebra of Y); CF_N(U) := {f : ℝ^P → H : f continuous, HasCompactSupport f, tsupport f ⊆ U}. Hypotheses: m is a measure on Y with m(K) < ∞ for every compact K ⊆ Y, and ν₁ : Y → H is measurable with ‖ν₁(y)‖ ≤ 1 for all y and ‖ν₁(y)‖ = 1 for m-a.e. y. This is step 1 (measurable embedding) and steps 8–9 of the parent proof of smr_riesz_borel_euclidean, written out in full.

1. (ι is a measurable embedding.) ι is injective; it is measurable because the σ-algebra of Y is the comap σ-algebra; and it maps measurable sets to measurable sets: a measurable set of Y has the form ι⁻¹(S) with S Borel, and ι(ι⁻¹(S)) = S ∩ U is Borel because U is open, hence Borel (MeasurableEmbedding.subtype_coe hU.measurableSet). For a measurable embedding ι and μ := m.map ι the following hold: μ(A) = m(ι⁻¹(A)) for every A ⊆ ℝ^P (MeasurableEmbedding.map_apply); ∫ F dμ = ∫_Y F(ι y) dm(y) for every F : ℝ^P → ℝ (MeasurableEmbedding.integral_map); and a property Q holds μ-a.e. iff Q ∘ ι holds m-a.e. (MeasurableEmbedding.ae_map_iff).

2. (Definitions.) Let μ := m.map ι, a measure on the Borel σ-algebra of ℝ^P, and let ν be the extension of ν₁ by zero: ν(x) := ν₁(⟨x, hx⟩) if hx : x ∈ U, and ν(x) := 0 if x ∉ U (in Lean ν = Function.extend Subtype.val ν₁ 0). Then ν(ι y) = ν₁(y) for every y ∈ Y (ι is injective), and ν(x) = 0 for every x ∉ U (such x is not of the form ι y).

3. (ν is Borel.) For a Borel set S ⊆ H we have ν⁻¹(S) = ι(ν₁⁻¹(S)) ∪ E_S, where E_S := ℝ^P ∖ U if 0 ∈ S and E_S := ∅ otherwise. The set ι(ν₁⁻¹(S)) is Borel because ν₁⁻¹(S) is measurable in Y and ι maps measurable sets to measurable sets (step 1), and ℝ^P ∖ U is closed. Hence ν is measurable (MeasurableEmbedding.measurable_extend, with the measurable extension value 0).

4. (‖ν‖ ≤ 1 everywhere.) For x ∈ U, ‖ν(x)‖ = ‖ν₁(⟨x, hx⟩)‖ ≤ 1 by hypothesis; for x ∉ U, ‖ν(x)‖ = ‖0‖ = 0 ≤ 1.

5. (μ lives on U.) μ(ℝ^P ∖ U) = m(ι⁻¹(ℝ^P ∖ U)) = m(∅) = 0, because every ι y lies in U.

6. (Local finiteness.) Let K ⊆ U be compact. Since K ⊆ U = range ι and ι is a topological embedding (inducing), ι⁻¹(K) is compact in Y (Topology.IsInducing.isCompact_preimage_iff). Hence μ(K) = m(ι⁻¹(K)) < ∞ by the hypothesis on m.

7. (‖ν‖ = 1 μ-a.e.) By step 1 this is equivalent to ‖ν(ι y)‖ = 1 for m-a.e. y; since ν(ι y) = ν₁(y) (step 2), this is exactly the hypothesis ‖ν₁(y)‖ = 1 for m-a.e. y.

8. (Integrability.) Let f ∈ CF_N(U) and F(x) := ⟨f(x), ν(x)⟩. F is Borel measurable: x ↦ (f(x), ν(x)) is measurable (f is continuous, ν is Borel by step 3) and the inner product H × H → ℝ is continuous, hence measurable for the product σ-algebra, which equals the Borel σ-algebra of H × H because H is second countable; in particular F is a.e. strongly measurable. F vanishes outside T := tsupport f: if x ∉ T then f(x) = 0 and hence F(x) = 0, so support F ⊆ T. The set T is compact (f has compact support), so the continuous function f is bounded on T: there is C ∈ ℝ with ‖f(x)‖ ≤ C for x ∈ T. For x ∈ T, |F(x)| ≤ ‖f(x)‖ ‖ν(x)‖ ≤ ‖f(x)‖ ≤ C, by the Cauchy–Schwarz inequality and step 4. Since T ⊆ U is compact, μ(T) < ∞ by step 6. A measurable function bounded by C almost everywhere on a set of finite measure is integrable on that set (Measure.integrableOn_of_bounded), so F is μ-integrable on T; as support F ⊆ T, F is μ-integrable on ℝ^P (integrableOn_iff_integrable_of_support_subset).

9. (Integral identity.) By step 1 (MeasurableEmbedding.integral_map) and step 2,
∫ ⟨f(x), ν(x)⟩ dμ(x) = ∫_Y ⟨f(ι y), ν(ι y)⟩ dm(y) = ∫_Y ⟨f(ι y), ν₁(y)⟩ dm(y).

10. (Conclusion.) The pair (μ, ν) satisfies: ν is measurable (step 3); μ(ℝ^P ∖ U) = 0 (step 5); μ(K) < ∞ for every compact K ⊆ U (step 6); ‖ν(x)‖ ≤ 1 for all x (step 4); ‖ν(x)‖ = 1 for μ-a.e. x (step 7); and for every f ∈ CF_N(U), x ↦ ⟨f(x), ν(x)⟩ is μ-integrable (step 8) with ∫ ⟨f(x), ν(x)⟩ dμ(x) = ∫_Y ⟨f(ι y), ν₁(y)⟩ dm(y) (step 9). ∎

Formalization note (not part of the argument): the statement and the proof only need names visible after import GMT.Ch06.Submission. Useful API: MeasurableEmbedding.subtype_coe hU.measurableSet; Subtype.val_injective.extend_apply; Function.extend_apply'; MeasurableEmbedding.measurable_extend; MeasurableEmbedding.map_apply; MeasurableEmbedding.ae_map_iff; MeasurableEmbedding.integral_map; Topology.IsInducing.subtypeVal.isCompact_preimage_iff; IsCompact.exists_bound_of_continuousOn; Measure.integrableOn_of_bounded; ae_restrict_mem; integrableOn_iff_integrable_of_support_subset; norm_inner_le_norm; measurability of x ↦ inner ℝ (f x) (ν x) as continuous_inner.measurable.comp (hf.measurable.prodMk hν). A scratch Lean proof following exactly these steps was kernel-checked against the frozen submission (axioms: propext, Classical.choice, Quot.sound).

## Key steps

1. ι = Subtype.val : ↥U → ℝ^P is a measurable embedding (U open), so μ := m.map ι satisfies μ(A) = m(ι⁻¹A), ∫ F dμ = ∫ F ∘ ι dm and μ-a.e. ⟺ m-a.e. after composing with ι.
2. ν := Function.extend Subtype.val ν₁ 0 is Borel (MeasurableEmbedding.measurable_extend), ν ∘ ι = ν₁, ν = 0 off U, and ‖ν‖ ≤ 1.
3. μ(Uᶜ) = m(∅) = 0; for compact K ⊆ U, ι⁻¹K is compact, so μ(K) = m(ι⁻¹K) < ∞; ‖ν‖ = 1 μ-a.e. by ae_map_iff and ν ∘ ι = ν₁.
4. For f ∈ CF_N(U), ⟨f, ν⟩ is Borel, bounded by sup‖f‖ on the compact T = tsupport f ⊆ U of finite μ-measure and zero off T, hence μ-integrable.
5. ∫⟨f, ν⟩ dμ = ∫⟨f ∘ ι, ν ∘ ι⟩ dm = ∫⟨f ↑y, ν₁ y⟩ dm(y) by MeasurableEmbedding.integral_map.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp / sha256sum local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean (identical, sha256 ea3ee0dd…)`
- `rg -n "CompactlySupportedContinuousMap|rieszMeasure|simon_theorem_4_14|IsLocallyBoundedCcFunctional|extend Subtype.val|Function.extend" project/GMT (only README tool lists: Ch06/README.md:84,94; Ch01/README.md:40-41)`
- `rg -n "extend_one\b|extend_zero\b|continuous_extend_one|tsupport_extend|mulSupport_extend_one" mathlib/Mathlib --include=*.lean; sed -n 310,352p mathlib/Mathlib/Topology/Algebra/Support.lean`
- `rg -n "theorem integral_trim|MeasurableEmbedding.integral_map" mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `rg -n "NullMeasurable.aemeasurable" mathlib/Mathlib/MeasureTheory`
- `rg -n "theorem measurable_extend|theorem ae_map_iff|theorem map_apply" mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `rg -n "sigmaCompactSpace_of_locallyCompact_secondCountable|IsOpen.locallyCompactSpace|instance Subtype.borelSpace" mathlib/Mathlib`
- `rg -n "theorem Measurable.inner" mathlib/Mathlib (only MeasureTheory/Function/SpecialFunctions/Inner.lean, not imported by the frozen submission)`
- `rg -n "setIntegral_eq_integral_of_forall_compl_eq_zero|integrableOn_iff_integrable_of_support_subset" mathlib/Mathlib/MeasureTheory`
- `grep -n simon_theorem_4_14 and full read of simongmt Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean; grep -n declarations in VectorFunctionalEnvelope.lean, RadonCaratheodoryIntegral.lean, RadonOuterMeasure.lean, RegularityCompletion.lean, Basic.lean (pinned simongmt 2b3663083f3f in lake-packages-25730c7c)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; validate_lean_statement from verifier/lean_contract.py on the three child statements`
- `python3 listing of dag.json lean_name for all 211 nodes; grep -rn smr_rb_ dag.json nodes/ and simongmt (no matches)`
- `lake build GMT.Ch06.Submission in scratch /tmp/rb-split-Sjkh67 (frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Avail.lean (name availability under import GMT.Ch06.Submission); Scratch/Inst.lean (#synth MeasurableSpace/BorelSpace/CountablyGenerated on EuclideanSpace, Module on CompactlySupportedContinuousMap, subtype instances)`
- `lake env lean Scratch/Challenge_smr_rb_*.lean (three child types in comparator child scope, 0 errors); Scratch/Assembly.lean (parent from sorry'd children); Scratch/Proofs.lean (#print axioms of all three children and the parent)`
- `git show --stat of accepted leaf commits cb89cc7f, 8c000d1f, 3ccbe082, ca04907a, eefd7c3e, 6c6b4b27, 26d9d850, e4a2285e (24–89 inserted lines each; granularity calibration)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Notation/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonCaratheodoryIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RegularityCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-riesz-borel-a1/parent-child-handoff.json`
- `/tmp/rb-split-Sjkh67/Scratch/Avail.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Inst.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Challenge_smr_rb_transfer_functional.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Challenge_smr_rb_borel_riesz_sigma_compact.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Challenge_smr_rb_pushforward_subtype.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Assembly.lean`
- `/tmp/rb-split-Sjkh67/Scratch/Proofs.lean`

Snapshot: project d8d46c95 and Mathlib 25730c7c. Its frozen Ch06 Contract is byte-identical to the workspace Contract and Submission (sha256 ea3ee0dd…). The project declares nothing about Riesz, C_c or zero extension; the rg hits are only README tool lists that cite simon_theorem_4_14.

Available after import GMT.Ch06.Submission alone:
- CompactlySupportedContinuousMap;
- HasCompactSupport.continuous_extend_zero, extend_zero and tsupport_extend_zero_subset;
- MeasurableEmbedding.subtype_coe, measurable_extend, map_apply, ae_map_iff and integral_map;
- integral_trim and NullMeasurable.aemeasurable;
- IsOpen.locallyCompactSpace, the instance sigmaCompactSpace_of_locallyCompact_secondCountable, and Subtype.borelSpace.

Not available after that import:
- IsLocallyBoundedCcFunctional, simon_theorem_4_14, IsRadonOuterMeasure and radonCaratheodoryMeasure (pinned SimonGMT Chapter01). They are needed only inside child 2's proof, via two extra imports that compile with the frozen submission.
- Measurable.inner, which sits in an unimported Mathlib file.

So the child statements inline the local-boundedness hypothesis and use only frozen-scope names. No existing declaration states the Borel form of the Riesz theorem, the C_c(↥U) transfer or the push-forward. The smr_rb_* names are unused in the DAG, nodes/ and SimonGMT.

All three child types elaborate in the comparator child scope and pass the lexical validator. The parent's frozen type kernel-checks from them, and all three children were proved in scratch with axioms [propext, Classical.choice, Quot.sound].

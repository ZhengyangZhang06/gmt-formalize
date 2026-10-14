# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.local_finite_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is the finiteness estimate of Step 4(b) of the parent proof, using the Jacobian bound of Step 2.

1. Let K ⊆ V be compact and K′ := f⁻¹(K) ∩ spt T. By hypothesis K′ is compact. Moreover K′ ⊆ spt T ⊆ U, since the support of a current in U lies in U (`GeometricCurrentOn.support_subset_domain`; spt T = U ∖ zeroRegion).
2. The sibling lemma lpf_pi_jacobian_local_bound applies to (U, M, θ, ξ, f, L) and the compact K′ ⊆ U. It gives C ∈ ℝ with ‖L(x)_#ξ(x)‖ ≤ C for Hⁿ⌞M-a.e. x with x ∈ K′. Put C₊ := max(C, 0).
3. By (RSN) applied to T and (M, θ, ξ), Hⁿ(M ∖ spt T) = 0.
4. Write F(x) := ofReal(θ(x))·‖L(x)_#ξ(x)‖ₑ. Since M ∩ f⁻¹(K) ⊆ (M ∩ K′) ∪ (M ∖ spt T), monotonicity of the set lintegral and `lintegral_union_le` give ∫⁻_{M∩f⁻¹K} F ≤ ∫⁻_{M∩K′} F + ∫⁻_{M∖spt T} F. The second term is 0, because the restriction of Hⁿ to the Hⁿ-null set M ∖ spt T is the zero measure.
5. M ∩ K′ ⊆ M, and M ∩ K′ is null-measurable (M null-measurable, K′ closed). So the a.e. bound of Step 2 holds Hⁿ⌞(M ∩ K′)-a.e. with x ∈ K′, giving F ≤ ofReal(θ)·ofReal(C₊) Hⁿ⌞(M ∩ K′)-a.e. Hence ∫⁻_{M∩K′} F ≤ ofReal(C₊)·∫⁻_{M∩K′} ofReal(θ) dHⁿ (`lintegral_mono_ae`, `lintegral_const_mul'`).
6. K′ is compact and K′ ⊆ U, so by the field `integrableOn` of the triple θ is Hⁿ-integrable on M ∩ K′. Since ofReal(θ) ≤ ‖θ‖ₑ, ∫⁻_{M∩K′} ofReal(θ) ≤ ∫⁻_{M∩K′} ‖θ‖ₑ < ∞.
7. Steps 4–6 give ∫⁻_{M∩f⁻¹K} F ≤ ofReal(C₊)·∫⁻_{M∩K′} ofReal(θ) < ∞. ∎

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_local_finite_weight : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared sibling `Submission.lpf_pi_jacobian_local_bound`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro hRSN P Q n U V T M θ ξ f L hU htri hT hf hprop hderiv K hK hKV
  have hK'c : IsCompact (f ⁻¹' K ∩ T.support) := hprop K hK hKV
  have hK'U : f ⁻¹' K ∩ T.support ⊆ U := fun x hx => T.support_subset_domain hx.2
  obtain ⟨C, hC⟩ :=
    Submission.lpf_pi_jacobian_local_bound P Q n U M θ ξ f L hU htri hf hderiv _ hK'c hK'U
  have hnull : (μHE[n] : Measure (Eucl P)) (M \ T.support) = 0 := hRSN P n U T M θ ξ htri hT
  have hK'meas : MeasurableSet (f ⁻¹' K ∩ T.support) := hK'c.isClosed.measurableSet
  have hsub : M ∩ f ⁻¹' K ⊆ (M ∩ (f ⁻¹' K ∩ T.support)) ∪ (M \ T.support) := by
    intro x hx
    by_cases hxT : x ∈ T.support
    · exact Or.inl ⟨hx.1, hx.2, hxT⟩
    · exact Or.inr ⟨hx.1, hxT⟩
  have hint : IntegrableOn θ (M ∩ (f ⁻¹' K ∩ T.support)) (μHE[n] : Measure (Eucl P)) :=
    htri.integrableOn _ hK'c hK'U
  have hθfin : ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x)
      ∂(μHE[n] : Measure (Eucl P)) < ∞ :=
    hint.setLIntegral_lt_top
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
      ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ ≤
        ENNReal.ofReal (θ x) * ENNReal.ofReal (max C 0) := by
    have h1 : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
        x ∈ f ⁻¹' K ∩ T.support → ‖nVectorPushforward n (L x) (ξ x)‖ ≤ C :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hC
    have h2 : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ (f ⁻¹' K ∩ T.support))),
        x ∈ M ∩ (f ⁻¹' K ∩ T.support) :=
      ae_restrict_mem₀ (htri.nullMeasurableSet.inter hK'meas.nullMeasurableSet)
    filter_upwards [h1, h2] with x hx1 hx2
    have h3 : ‖nVectorPushforward n (L x) (ξ x)‖ₑ ≤ ENNReal.ofReal (max C 0) := by
      rw [← ofReal_norm (nVectorPushforward n (L x) (ξ x))]
      exact ENNReal.ofReal_le_ofReal ((hx1 hx2.2).trans (le_max_left _ _))
    exact mul_le_mul' le_rfl h3
  calc ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
        ∂(μHE[n] : Measure (Eucl P))
      ≤ ∫⁻ x in (M ∩ (f ⁻¹' K ∩ T.support)) ∪ (M \ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_set hsub
    _ ≤ ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) +
        ∫⁻ x in M \ T.support, ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_union_le _ _ _
    _ = ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support),
          ENNReal.ofReal (θ x) * ‖nVectorPushforward n (L x) (ξ x)‖ₑ
          ∂(μHE[n] : Measure (Eucl P)) := by
        rw [setLIntegral_measure_zero _ _ hnull, add_zero]
    _ ≤ ∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x) * ENNReal.ofReal (max C 0)
          ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hbound
    _ = (∫⁻ x in M ∩ (f ⁻¹' K ∩ T.support), ENNReal.ofReal (θ x)
          ∂(μHE[n] : Measure (Eucl P))) * ENNReal.ofReal (max C 0) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top hθfin ENNReal.ofReal_lt_top
```

## Key steps

1. K′ := f⁻¹K ∩ spt T is compact and contained in U
2. Jacobian bound on K′ (sibling) and Hⁿ(M ∖ spt T) = 0 (RSN)
3. Split M ∩ f⁻¹K ⊆ (M ∩ K′) ∪ (M ∖ spt T); the null part contributes 0
4. ∫⁻_{M∩K′} θ‖L_#ξ‖ ≤ C ∫_{M∩K′} θ < ∞ by local integrability of θ

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical)`
- `python3 over dag.json: frozen lean_statement/status of the 8 uncle nodes; all lean_name fields (226 unique); grep -c 'lpf_pi_' dag.json (0 matches)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lean_contract.validate_lean_statement on all 11 child statements`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def covectorPullback|def nVectorPushforward|def simpleNVector|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; 'abbrev TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; 'def GeometricCurrentOn.support|theorem GeometricCurrentOn.support_subset_domain' Chapter06/CurrentLocalEquality.lean`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (line 216)`
- `grep -n 'LocallyLipschitzOn.comp|protected lemma comp' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean (only LocallyLipschitz.comp exists)`
- `lake build GMT.Ch06.Submission in /tmp/lpi3_scratch (scratch copy, .lake/packages linked to the pinned package tree)`
- `lake env lean Scratch/Stmts.lean (11 statements in comparator scope, only sorry warnings)`
- `lake env lean Scratch/Names.lean (#check of ~90 cited Mathlib/SimonGMT names; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm, ENorm via SeminormedAddGroup.toContinuousENorm, MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace, Norm (Covector ..) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm)`
- `lake env lean Scratch/Inst.lean (#synth ContinuousAdd / PseudoMetrizableSpace / ContinuousENorm (NVector (Eucl 3) 2) fail; documented workarounds compile)`
- `lake env lean Scratch/Assembly.lean (parent from 19 stubs; #print axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Scratch/AllChildren.lean and Scratch/E2E.lean (all 11 children proved in dependency order + parent assembly; per-child #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpi3_scratch/Scratch/Stmts.lean`
- `/tmp/lpi3_scratch/Scratch/Names.lean`
- `/tmp/lpi3_scratch/Scratch/Inst.lean`
- `/tmp/lpi3_scratch/Scratch/Assembly.lean`
- `/tmp/lpi3_scratch/Scratch/AllChildren.lean`
- `/tmp/lpi3_scratch/Scratch/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace Contract and Submission. The child scope is import GMT.Ch06.Submission plus the replayed namespace and opens. It provides the contract notions (IsRectifiableTriple, tauAction, IsIntegerMultiplicity) and SimonGMT Ch03 Rectifiable (CountablyRectifiable with mono/range/iUnion, HasWeightedApproximateTangentSpaceAt, .unique for θ x ≠ 0). It also provides Ch06 n-vectors (NVector = Covector →L[ℝ] ℝ with the operator norm, simpleNVector, nVectorPushforward_simple), test forms, currents and support_subset_domain, plus Ch02 euclideanHausdorffMeasure_image_le_of_lipschitzOn.

It does not provide:
- SimonGMT SubmanifoldCover (countablyRectifiable_image_contDiffOn_open) or Mathlib's Multilinear.FiniteDimensional; both facts are therefore separate import-free leaves.
- LocallyLipschitzOn.comp.
- Instance search on NVector for ContinuousAdd, PseudoMetrizableSpace, ContinuousENorm and NormSMulClass; the verified workarounds are recorded in the child texts.

No lpf_pi_* name is reserved in dag.json, and leaf plans forbid helper declarations, so every child script is a single theorem. All 11 frozen statements validate and elaborate in the comparator scope. All 11 children are fully proved in Lean with only propext, Classical.choice and Quot.sound, using only their declared siblings. The frozen parent type follows from them and the eight uncles by the stated assembly; its only sorryAx comes from the uncle stubs.

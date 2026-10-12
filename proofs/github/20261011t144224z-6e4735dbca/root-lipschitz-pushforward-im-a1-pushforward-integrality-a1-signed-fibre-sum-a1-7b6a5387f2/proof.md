# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.signed_fibre_sum-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: ofReal : ℝ → [0, ∞] is ENNReal.ofReal, and N^h(y) := Σ'_{x ∈ A, f(x) = y} h(x) for h : X → [0, ∞]. This is the passage from the nonnegative area formula to the signed integral in Step 9 of the parent proof, where it is applied to h⁺ and h⁻.

1. Put h⁺(x) := ofReal(g(x)) and h⁻(x) := ofReal(−g(x)). Both are μ⌞A-a.e. measurable (g is). Pointwise h⁺ + h⁻ = ‖g‖ₑ (ofReal(a) + ofReal(−a) = |a| for a ∈ ℝ), and g = (h⁺).toReal − (h⁻).toReal.
2. By the area identity, N⁺ := N^{h⁺} and N⁻ := N^{h⁻} are ν-a.e. measurable and ∫⁻ N^± dν = ∫⁻_A h^± J dμ. Each is ≤ ∫⁻_A ‖g‖ₑ J dμ < ∞, because h^± ≤ ‖g‖ₑ. An a.e. measurable [0, ∞]-valued function with finite lintegral is a.e. finite (`ae_lt_top'`), so N⁺ < ∞ and N⁻ < ∞ ν-a.e.
3. Fix y with N⁺(y) < ∞ and N⁻(y) < ∞. The fibre sum of ‖g‖ₑ equals N⁺(y) + N⁻(y) < ∞ (`ENNReal.tsum_add`). So the nonnegative real family ‖g(x)‖ is summable (`ENNReal.tsum_coe_ne_top_iff_summable` for ‖g‖₊), and therefore (g(x))_x is summable in the complete space ℝ (`Summable.of_norm`). This proves (i). The families max(g, 0) = (h⁺).toReal and max(−g, 0) = (h⁻).toReal are dominated by ‖g‖, hence also summable, with sums N⁺(y).toReal and N⁻(y).toReal (`ENNReal.tsum_toReal_eq` with finiteness). Since g = (h⁺).toReal − (h⁻).toReal termwise, Σ'_x g(x) = N⁺(y).toReal − N⁻(y).toReal.
4. The functions y ↦ N^±(y).toReal are ν-a.e. measurable and nonnegative with ∫⁻ ofReal(N^±.toReal) ≤ ∫⁻ N^± < ∞, so they are ν-integrable. By `integral_toReal` (using N^± < ∞ a.e.), ∫ N^±(y).toReal dν = (∫⁻ N^± dν).toReal. By Step 3, y ↦ Σ'_x g(x) agrees ν-a.e. with N⁺.toReal − N⁻.toReal. Hence it is ν-integrable (proving (ii)) and ∫ Σ' g dν = (∫⁻_A h⁺ J dμ).toReal − (∫⁻_A h⁻ J dμ).toReal.
5. On the source side, ∫⁻_A ‖g‖ₑ J < ∞ forces ‖g‖ₑ J < ∞ μ⌞A-a.e. Hence g(x) = 0 for μ⌞A-a.e. x with J(x) = ∞. Consequently, μ⌞A-a.e., ofReal(g·J.toReal) = h⁺·J and ofReal(−g·J.toReal) = h⁻·J. Where J < ∞ this is ofReal(ab) = ofReal(a)·ofReal(b) for b = J.toReal ≥ 0, with ofReal(J.toReal) = J; where J = ∞ both sides are 0 because g = 0.
6. The real function g·J.toReal is μ⌞A-a.e. strongly measurable (g a.e. strongly measurable, J a.e. measurable). Its lintegral of absolute values satisfies ∫⁻_A ‖g·J.toReal‖ₑ ≤ ∫⁻_A ‖g‖ₑ J < ∞, so it is μ⌞A-integrable. By the positive/negative-part formula for the Bochner integral (`integral_eq_lintegral_pos_part_sub_lintegral_neg_part`) and Step 5, ∫_A g·J.toReal dμ = (∫⁻_A h⁺ J).toReal − (∫⁻_A h⁻ J).toReal.
7. Steps 4 and 6 have the same right-hand side, which gives (iii). ∎

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_signed_fibre_sum : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses no sibling lemma. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro X Y _ _ μ ν f A J hJ harea g hg hfin
  have hp_meas : AEMeasurable (fun x => ENNReal.ofReal (g x)) (μ.restrict A) :=
    hg.aemeasurable.ennreal_ofReal
  have hm_meas : AEMeasurable (fun x => ENNReal.ofReal (-g x)) (μ.restrict A) :=
    hg.aemeasurable.neg.ennreal_ofReal
  obtain ⟨hNp_meas, hNp_eq⟩ := harea _ hp_meas
  obtain ⟨hNm_meas, hNm_eq⟩ := harea _ hm_meas
  have hp_le : ∀ x, ENNReal.ofReal (g x) ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hm_le : ∀ x, ENNReal.ofReal (-g x) ≤ ‖g x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have hIp_lt : ∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul' (hp_le x) le_rfl) hfin
  have hIm_lt : ∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul' (hm_le x) le_rfl) hfin
  have hNp_fin : ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) ∂ν ≠ ∞ := by
    rw [← hNp_eq]; exact hIp_lt.ne
  have hNm_fin : ∫⁻ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) ∂ν ≠ ∞ := by
    rw [← hNm_eq]; exact hIm_lt.ne
  have hNp_ae : ∀ᵐ y ∂ν, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) < ∞ :=
    ae_lt_top' hNp_meas hNp_fin
  have hNm_ae : ∀ᵐ y ∂ν, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) < ∞ :=
    ae_lt_top' hNm_meas hNm_fin
  have hg_eq : ∀ x, g x = (ENNReal.ofReal (g x)).toReal - (ENNReal.ofReal (-g x)).toReal :=
    fun x => by
      rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
      exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
  have hfib : ∀ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x) < ∞ →
      ∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x) < ∞ →
      Summable (fun x : {x : X // x ∈ A ∧ f x = y} => g x) ∧
      ∑' x : {x : X // x ∈ A ∧ f x = y}, g x =
        (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal -
          (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal := by
    intro y hy1 hy2
    have hs1 : Summable (fun x : {x : X // x ∈ A ∧ f x = y} => (ENNReal.ofReal (g x)).toReal) :=
      ENNReal.summable_toReal hy1.ne
    have hs2 : Summable
        (fun x : {x : X // x ∈ A ∧ f x = y} => (ENNReal.ofReal (-g x)).toReal) :=
      ENNReal.summable_toReal hy2.ne
    refine ⟨(hs1.sub hs2).congr (fun x => (hg_eq x).symm), ?_⟩
    rw [tsum_congr (fun x : {x : X // x ∈ A ∧ f x = y} => hg_eq x), hs1.tsum_sub hs2,
      ENNReal.tsum_toReal_eq (f := fun x : {x : X // x ∈ A ∧ f x = y} => ENNReal.ofReal (g x))
        (fun _ => ENNReal.ofReal_ne_top),
      ENNReal.tsum_toReal_eq (f := fun x : {x : X // x ∈ A ∧ f x = y} => ENNReal.ofReal (-g x))
        (fun _ => ENNReal.ofReal_ne_top)]
  have hae_eq : (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) =ᵐ[ν]
      fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal -
        (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal := by
    filter_upwards [hNp_ae, hNm_ae] with y hy1 hy2
    exact (hfib y hy1 hy2).2
  have hintp : Integrable
      (fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (g x)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hNp_meas hNp_fin
  have hintm : Integrable
      (fun y => (∑' x : {x : X // x ∈ A ∧ f x = y}, ENNReal.ofReal (-g x)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top hNm_meas hNm_fin
  have hint : Integrable (fun y => ∑' x : {x : X // x ∈ A ∧ f x = y}, g x) ν :=
    (hintp.sub' hintm).congr hae_eq.symm
  refine ⟨?_, hint, ?_⟩
  · filter_upwards [hNp_ae, hNm_ae] with y hy1 hy2
    exact (hfib y hy1 hy2).1
  have htarget : ∫ y, ∑' x : {x : X // x ∈ A ∧ f x = y}, g x ∂ν =
      (∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ).toReal -
        (∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ).toReal := by
    rw [integral_congr_ae hae_eq, integral_sub hintp hintm, integral_toReal hNp_meas hNp_ae,
      integral_toReal hNm_meas hNm_ae, ← hNp_eq, ← hNm_eq]
  have hgJ_meas : AEMeasurable (fun x => ‖g x‖ₑ * J x) (μ.restrict A) := hg.enorm.mul hJ
  have hgJ_fin : ∀ᵐ x ∂(μ.restrict A), ‖g x‖ₑ * J x < ∞ := ae_lt_top' hgJ_meas hfin.ne
  have hG_int : Integrable (fun x => g x * (J x).toReal) (μ.restrict A) := by
    refine ⟨hg.mul hJ.ennreal_toReal.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖g x * (J x).toReal‖ₑ ∂(μ.restrict A) < ∞
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
    rw [enorm_mul, Real.enorm_eq_ofReal_abs ((J x).toReal), abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
  have hg0 : ∀ᵐ x ∂(μ.restrict A), J x = ∞ → g x = 0 := by
    filter_upwards [hgJ_fin] with x hx hJx
    by_contra hne
    have h1 : ‖g x‖ₑ ≠ 0 := enorm_ne_zero.mpr hne
    rw [hJx, ENNReal.mul_top h1] at hx
    exact lt_irrefl _ hx
  have hpos : ∀ᵐ x ∂(μ.restrict A),
      ENNReal.ofReal (g x * (J x).toReal) = ENNReal.ofReal (g x) * J x := by
    filter_upwards [hg0] with x hx
    by_cases hJx : J x = ∞
    · simp [hx hJx]
    · rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hJx]
  have hneg : ∀ᵐ x ∂(μ.restrict A),
      ENNReal.ofReal (-(g x * (J x).toReal)) = ENNReal.ofReal (-g x) * J x := by
    filter_upwards [hg0] with x hx
    by_cases hJx : J x = ∞
    · simp [hx hJx]
    · rw [← neg_mul, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hJx]
  have hsource : ∫ x in A, g x * (J x).toReal ∂μ =
      (∫⁻ x in A, ENNReal.ofReal (g x) * J x ∂μ).toReal -
        (∫⁻ x in A, ENNReal.ofReal (-g x) * J x ∂μ).toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hG_int, lintegral_congr_ae hpos,
      lintegral_congr_ae hneg]
  rw [hsource, htarget]
```

## Key steps

1. Split g into h⁺ = ofReal g and h⁻ = ofReal(−g); apply the area identity to each
2. Finite lintegrals ⇒ fibre sums N^± finite ν-a.e. ⇒ fibre families summable, Σ' g = N⁺ − N⁻ a.e.
3. Integrability and ∫ Σ' g = (∫⁻_A h⁺J).toReal − (∫⁻_A h⁻J).toReal via integral_toReal
4. g = 0 a.e. where J = ∞; positive/negative parts give ∫_A g·J.toReal equal to the same difference

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

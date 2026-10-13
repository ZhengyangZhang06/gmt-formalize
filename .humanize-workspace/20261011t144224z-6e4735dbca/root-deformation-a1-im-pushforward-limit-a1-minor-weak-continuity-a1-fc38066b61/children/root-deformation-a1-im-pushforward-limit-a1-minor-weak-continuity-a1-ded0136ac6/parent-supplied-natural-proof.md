# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.minor_weak_continuity-a1.test_density-a1.scalar_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1, the density lemma, of the supplied proof of deformation_ipl_mwc_test_density. This is parent step (3.0): “choose φ ∈ C_c^∞(Ω) with ∫_Ω|η − φ| < ε (C_c^∞(Ω) is dense in L¹(Ω))”. This child is exactly the claim of Step 1.
The supplied sub-steps 1(a)–(c) (exhaustion, truncation, mollification with the kernels of ae_mollifier) are replaced by the comparator-accepted vector-valued density theorem Submission.slicing_im_ll_gws_smooth_dense (sibling smooth_dense). That theorem is itself proved through a compact exhaustion of Ω, and it was accepted after the parent's decomposition was written. Only a coordinate embedding is added here.

Notation.
- ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k); λ = Lebesgue measure (volume) on ℝ^k; ∫_Ω is the integral with respect to λ restricted to Ω.
- For v ∈ ℝ^k and i ∈ Fin k, v_i is the i-th coordinate of v (Lean: v i), and ‖v‖ = (Σ_i v_i²)^{1/2} is the Euclidean norm.
- tsupport is the closure of the support; C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞).

Fix k ∈ ℕ, an open set Ω ⊆ ℝ^k, a function η : ℝ^k → ℝ that is λ-integrable on Ω, and ε > 0.

1. (Case k = 0: the space is a point.) Fin 0 is empty, so ℝ⁰ has exactly one element. Hence:
- any two points of ℝ⁰ are equal, and every function on ℝ⁰ is constant;
- every subset of ℝ⁰ is compact;
- Ω = ∅ or Ω = ℝ⁰.
 (a) If Ω = ∅, put φ := 0. It is C^∞ (a constant) and has compact support (its support is empty). Also tsupport φ = ∅ ⊆ Ω, and ∫_Ω |η − φ| dλ = 0 < ε because λ restricted to ∅ is the zero measure.
 (b) If Ω ≠ ∅, pick x ∈ Ω. Every y ∈ ℝ⁰ equals x, so Ω = ℝ⁰. Put φ := η.
- φ is C^∞, because η = (w ↦ η(0)) is constant.
- tsupport φ is a closed subset of the compact set ℝ⁰, hence compact. So φ has compact support, and tsupport φ ⊆ ℝ⁰ = Ω.
- ∫_Ω |η − φ| dλ = ∫_Ω 0 dλ = 0 < ε.
 This proves the claim when k = 0.

2. (Case k ≥ 1: a vector field carrying η.) Let i₀ := 0 ∈ Fin k and e := EuclideanSpace.single i₀ 1 ∈ ℝ^k, the first standard basis vector, so e_{i₀} = 1. Define c : ℝ^k → ℝ^k by c(w) := η(w)·e. Since η is λ-integrable on Ω and e is a fixed vector, c is λ-integrable on Ω (Integrable.smul_const).

3. (Vector approximation.) Apply the sibling smooth_dense with n := k, the open set Ω, the field c and δ := ε > 0. It yields b : ℝ^k → ℝ^k with:
- b is C^∞ and has compact support;
- tsupport b ⊆ Ω;
- ∫_Ω ‖c(w) − b(w)‖ dλ(w) < ε.

4. (Scalar approximant.) Let p := EuclideanSpace.proj i₀ : ℝ^k → ℝ, p(v) = v_{i₀}; it is a continuous linear map with p(0) = 0. Put φ := p ∘ b, i.e. φ(w) = b(w)_{i₀}.
 (a) φ is C^∞: a continuous linear map is C^∞, and a composite of C^∞ maps is C^∞ (ContinuousLinearMap.contDiff, ContDiff.comp).
 (b) If b(w) = 0 then φ(w) = p(0) = 0. So support φ ⊆ support b, whence tsupport φ ⊆ tsupport b ⊆ Ω (tsupport_comp_subset). Being a closed subset of the compact set tsupport b, tsupport φ is compact, i.e. φ has compact support (HasCompactSupport.comp_left).

5. (Pointwise estimate.) Let w ∈ ℝ^k.
- Taking a coordinate is linear, so (c(w) − b(w))_{i₀} = η(w)·e_{i₀} − b(w)_{i₀} = η(w) − φ(w).
- A coordinate is bounded by the Euclidean norm: |v_{i₀}| ≤ ‖v‖, because ‖v‖² = Σ_i v_i² ≥ v_{i₀}² (PiLp.norm_apply_le).
Hence |η(w) − φ(w)| ≤ ‖c(w) − b(w)‖ for every w ∈ ℝ^k.

6. (Integrability.)
- b is continuous with compact support, hence λ-integrable on ℝ^k and so on Ω. Thus c − b is integrable on Ω, and so is w ↦ ‖c(w) − b(w)‖.
- Likewise φ is continuous with compact support (step 4), hence integrable. So η − φ is integrable on Ω, and so is w ↦ |η(w) − φ(w)|.

7. (Conclusion.) By steps 5 and 6 and the monotonicity of the integral over Ω (setIntegral_mono), ∫_Ω |η(w) − φ(w)| dλ(w) ≤ ∫_Ω ‖c(w) − b(w)‖ dλ(w). By step 3 this is < ε. With step 4, φ is C^∞, has compact support, satisfies tsupport φ ⊆ Ω and has ∫_Ω |η − φ| dλ < ε. This proves the claim when k ≥ 1, and together with step 1 for every k. ∎

Formalization notes (no new mathematics). Every name below is available under the frozen `import GMT.Ch06.Submission`; do not add any import.
- Case split: Nat.eq_zero_or_pos.
- k = 0: Subsingleton.elim (Eucl 0 has a Subsingleton instance), HasCompactSupport.zero, Set.subsingleton_of_subsingleton.isCompact, IsCompact.of_isClosed_subset, isClosed_tsupport.
- Embedding: EuclideanSpace.single, EuclideanSpace.proj, Integrable.smul_const.
- Smoothness and support: ContinuousLinearMap.contDiff, ContDiff.comp, HasCompactSupport.comp_left, tsupport_comp_subset.
- Estimates: Continuous.integrable_of_hasCompactSupport, setIntegral_mono, PiLp.norm_apply_le, Real.norm_eq_abs.
The single-theorem proof below, of exactly this frozen type, was compiled under import GMT.Ch06.Submission in the exact comparator scope, placed after the verbatim accepted proof of Submission.slicing_im_ll_gws_smooth_dense. It produced no warning, and #print axioms gives propext, Classical.choice, Quot.sound. It is a reference implementation; the prose proof above governs.

theorem Submission.deformation_ipl_mwc_td_scalar_smooth_dense : <frozen type> := by
  intro k Ω η hΩ hη ε hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- k = 0: `Eucl 0` is a single point, so `Ω = ∅` or `Ω = univ`.
    by_cases hΩe : Ω = ∅
    · subst hΩe
      exact ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by simpa using hε⟩
    · have hΩu : Ω = univ := by
        obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hΩe
        exact eq_univ_of_forall fun y => (Subsingleton.elim x y) ▸ hx
      have hconst : η = fun _ => η 0 := funext fun x => congrArg η (Subsingleton.elim x 0)
      refine ⟨η, ?_, ?_, by simp [hΩu], by simpa using hε⟩
      · rw [hconst]; exact contDiff_const
      · exact IsCompact.of_isClosed_subset (Set.subsingleton_of_subsingleton.isCompact)
          (isClosed_tsupport _) (subset_univ _)
  · -- k ≥ 1: embed `η` as the first coordinate of a vector field and project back.
    let i₀ : Fin k := ⟨0, hk⟩
    let e : Eucl k := EuclideanSpace.single i₀ (1 : ℝ)
    have he : e i₀ = 1 := by simp [e]
    have hc : IntegrableOn (fun w => η w • e) Ω := hη.smul_const e
    obtain ⟨b, hb, hbc, hbΩ, hbε⟩ := Submission.slicing_im_ll_gws_smooth_dense k Ω (fun w => η w • e) hΩ hc ε hε
    let p : Eucl k →L[ℝ] ℝ := EuclideanSpace.proj i₀
    have hp : ∀ v : Eucl k, p v = v i₀ := fun v => rfl
    have hp0 : p 0 = 0 := map_zero p
    refine ⟨p ∘ b, p.contDiff.comp hb, hbc.comp_left hp0, (tsupport_comp_subset hp0 b).trans hbΩ, ?_⟩
    have hbi : Integrable b := hb.continuous.integrable_of_hasCompactSupport hbc
    have hφi : Integrable (p ∘ b) := (p.contDiff.comp hb).continuous.integrable_of_hasCompactSupport (hbc.comp_left hp0)
    have hR : IntegrableOn (fun w => ‖η w • e - b w‖) Ω := (hc.sub hbi.integrableOn).norm
    have hL : IntegrableOn (fun w => |η w - (p ∘ b) w|) Ω := (hη.sub hφi.integrableOn).abs
    calc ∫ w in Ω, |η w - (p ∘ b) w| ≤ ∫ w in Ω, ‖η w • e - b w‖ := by
          refine setIntegral_mono hL hR fun w => ?_
          have h1 : (η w • e - b w) i₀ = η w - (p ∘ b) w := by
            simp [Function.comp, hp, he]
          calc |η w - (p ∘ b) w| = ‖(η w • e - b w) i₀‖ := by rw [h1, Real.norm_eq_abs]
            _ ≤ ‖η w • e - b w‖ := PiLp.norm_apply_le _ _
      _ < ε := hbε

## Key steps

1. k = 0: ℝ⁰ is a single point, so Ω = ∅ (take φ = 0) or Ω = ℝ⁰ (take φ = η, which is constant and compactly supported); the error is 0 < ε.
2. k ≥ 1: put c(w) := η(w)·e with e = EuclideanSpace.single 0 1; c is integrable on Ω.
3. Apply the reused sibling smooth_dense to c and δ = ε: b is C^∞ with compact support, tsupport b ⊆ Ω and ∫_Ω ‖c − b‖ < ε.
4. φ := EuclideanSpace.proj 0 ∘ b is C^∞ with compact support and tsupport φ ⊆ tsupport b ⊆ Ω.
5. |η − φ| = |(c − b)_0| ≤ ‖c − b‖ pointwise; both sides are integrable on Ω, so ∫_Ω |η − φ| ≤ ∫_Ω ‖c − b‖ < ε.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD (= project_commit)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both identical)`
- `cmp snapshot mathlib vs .lake/packages/mathlib for Analysis/Normed/Lp/PiLp.lean, Analysis/InnerProductSpace/PiL2.lean, Topology/Algebra/Support.lean, MeasureTheory/Function/L1Space/Integrable.lean, MeasureTheory/Integral/Bochner/Set.lean, MeasureTheory/Integral/Bochner/Basic.lean, MeasureTheory/Measure/Restrict.lean (all identical)`
- `python3 -I regex over dag.json titles/lean_names: dens|mollif|C_c|L¹|L1|truncat|exhaust|smooth approx|smooth_dense|approx (found accepted slicing_im_ll_gws_smooth_dense, imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le, fiw_tb_te_l1d_compact_sign_approx, fiw_tb_te_l1d_smooth_sign_sep, fiw_tb_te_l1_le_of_smooth_dual, polyhedral_approx_integrable_smooth_ext, slicing_ru_smooth_to_continuous, slicing_mb_sa_mollifier_exists)`
- `python3 -I over dag.json: full record of root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.gradient_weak_star-a1.smooth_dense-a1 and of its parent gradient_weak_star-a1 and siblings (status, candidate_commit, title, statement, lean_statement)`
- `cat comparator-v1.log, isolated-comparator-result.json, accepted-candidate.json, parent-child-handoff.json, parent-supplied-natural-proof.md in nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584`
- `git show c278f023:GMT/Ch06/Submission.lean | head (frozen import header); git diff 21dd6b41 c278f023 --stat (1 file, 154 insertions)`
- `python3 -I over nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/decomposition-v1.json (format of reused children, key/lean_name mapping)`
- `rg -n 'CoeFun|theorem norm_apply_le' snapshot mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; rg -n 'EuclideanSpace.proj|EuclideanSpace.single|single_apply|norm_single' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem Integrable.mul_bdd|theorem norm_integral_le_of_norm_le|theorem setIntegral_mono |theorem Integrable.smul_const|theorem ae_restrict_of_forall_mem|theorem comp_left' snapshot mathlib/Mathlib`
- `grep deformation_ipl_mwc_td over dag.json, DAG.md, dag.mmd, issue-workers.json, nodes/, GMT/, snapshot project, simongmt (no match)`
- `lake env lean /tmp/td_decomp/lean/Avail.lean (#check availability under import GMT.Ch06.Submission; Integrable.bdd_mul' unknown, all others present)`
- `python3 -I /tmp/td_decomp/scripts/gen.py (verifier lean_contract.validate_lean_statement + gmt-compare child_modules, contract mode) and lake env lean on /tmp/td_decomp/build/{scalar_dense,smooth_dense,parent}_challenge.lean (exit 0, sorry warnings only)`
- `lake env lean /tmp/td_decomp/lean/LinkScalar.lean, LinkParent.lean, EndToEnd.lean (#print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-fc38066b61/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1-fc38066b61/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-minor-weak-continuity-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-gr-8d8546a584/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/td_decomp/build/scalar_dense_challenge.lean`
- `/tmp/td_decomp/build/smooth_dense_challenge.lean`
- `/tmp/td_decomp/build/parent_challenge.lean`
- `/tmp/td_decomp/lean/Avail.lean`
- `/tmp/td_decomp/lean/LinkScalar.lean`
- `/tmp/td_decomp/lean/LinkParent.lean`
- `/tmp/td_decomp/lean/EndToEnd.lean`

Pinned revisions confirmed:
- The manifest records mode local-project, project d8d46c95 (= git HEAD) and Mathlib 25730c7c.
- Contract.lean, Submission.lean and the snapshot Contract.lean are byte-identical.
- Every cited snapshot Mathlib file is identical to the workspace package copy.

No usable library lemma: Mathlib's L¹-density results (MemLp.exist_eLpNorm_sub_le, Integrable.exists_hasCompactSupport_integral_sub_le) lie outside the frozen import closure, and SimonGMT has no such statement.

The DAG does contain the needed fact: Submission.slicing_im_ll_gws_smooth_dense, the vector-valued density of C_c^∞(Ω) in L¹(Ω; ℝⁿ).
- Status: accepted at 07:07Z. That is after the parent's decomposition (06:27/06:39Z), so the parent handoff still called it “not accepted”.
- Comparator: passed.
- Candidate c278f023: a pure 154-line insertion with the frozen imports; recompiled here, its axioms are propext, Classical.choice, Quot.sound only.

Other accepted density nodes fit worse:
- imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le gives only continuous approximants, needs a finite measure and has no support-in-Ω condition.
- fiw_tb_te_l1d_*, slicing_ru_smooth_to_continuous and polyhedral_approx_integrable_smooth_ext are equality or duality statements, not approximation results.

Decision: smooth_dense is reused with a byte-identical type. The one new name, deformation_ipl_mwc_td_scalar_smooth_dense, matches nothing anywhere searched.

Snapshot Mathlib supplies everything the new proofs need:
- PiLp.lean: PiLp.norm_apply_le (‖x i‖ ≤ ‖x‖) and the PiLp CoeFun;
- PiL2.lean: EuclideanSpace.single and EuclideanSpace.proj;
- L1Space/Integrable.lean: Integrable.smul_const and Integrable.mul_bdd;
- Bochner/Set.lean: setIntegral_mono;
- Bochner/Basic.lean: norm_integral_le_of_norm_le;
- Measure/Restrict.lean: ae_restrict_of_forall_mem;
- Topology/Algebra/Support.lean: HasCompactSupport.comp_left and tsupport_comp_subset (via to_additive).

Lean checks:
- All three types elaborate in comparator scope.
- The links scalar_dense ⇐ smooth_dense and parent ⇐ scalar_dense compile.
- The end-to-end file compiles with only standard axioms.

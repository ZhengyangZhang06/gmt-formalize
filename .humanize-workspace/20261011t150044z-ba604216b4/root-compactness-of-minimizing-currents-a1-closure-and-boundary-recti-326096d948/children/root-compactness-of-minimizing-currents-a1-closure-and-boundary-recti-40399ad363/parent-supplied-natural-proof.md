# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.isp_of_im-a1.ae_mass_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of cbr_cc_slice_property_of_im, isolated for an arbitrary family Z of currents with the liminf mass bound. The parent applies it with U := ℝ^P, q := d, Z_t := ∂A_t − B_t and the bound supplied by (SL); f is continuous because it is Lipschitz.
Notation: M_W(T) := T.massOn W; B_k := ball(0, k) (open) and B̄_k := closedBall(0, k) for k ∈ ℕ; volume is Lebesgue measure on ℝ.
1. (Setup.) Fix k, m ∈ ℕ and put G := B_k, a := −m, b := m. Since G ∩ {a < f < b} ⊆ B_k ⊆ B̄_k and B̄_k is compact (isCompact_closedBall; ℝ^P is proper), μ(G ∩ {a < f < b}) ≤ μ(B̄_k) < ∞ (measure_mono and the hypothesis on μ).
2. (Applying (MM).) Apply (MM) with P, the constant sequence μ_j := μ (j ∈ ℕ), f, G, a, b, L and the constant sequence Z_j(t) := M_{B_k}(Z_t) (j ∈ ℕ, t ∈ ℝ). Its hypotheses hold: f is continuous; μ_j(G ∩ {a < f < b}) < ∞ for every j by step 1; and for every j and every t ∈ (a, b), Z_j(t) = M_{B_k}(Z_t) ≤ L·liminf_{h→0+} h⁻¹·μ(B_k ∩ {t − h < f < t}) by the hypothesis on Z applied to the open set W := B_k (isOpen_ball). (MM) yields a measurable g : ℝ → [0, ∞] with (i) liminf_j Z_j(t) ≤ g(t) for a.e. t such that t ∈ (a, b), and (ii) ∫_{(a,b)} g dt ≤ L·liminf_j μ(G ∩ {a < f < b}).
3. (Constant sequences.) The filter atTop on ℕ is nontrivial, so the liminf of a constant sequence equals its value (Filter.liminf_const). Thus (i) says: for a.e. t, t ∈ (−m, m) implies M_{B_k}(Z_t) ≤ g(t); and (ii) says ∫_{(−m,m)} g dt ≤ L·μ(B_k ∩ {−m < f < m}), which is < ∞ because (L : [0, ∞]) < ∞ and by step 1 (ENNReal.mul_lt_top).
4. (Finiteness of g.) g is measurable and its integral with respect to volume⌞(−m, m) is finite, so g(t) < ∞ for volume⌞(−m, m)-a.e. t (ae_lt_top). Since (−m, m) is measurable, this means: for a.e. t, t ∈ (−m, m) implies g(t) < ∞ (ae_restrict_iff'). Intersecting with step 3: for a.e. t, t ∈ (−m, m) implies M_{B_k}(Z_t) ≤ g(t) < ∞.
5. (Countable intersection.) ℕ is countable, so by ae_all_iff, applied over k and then over m, there is one Lebesgue-null set N such that for every t ∉ N and all k, m ∈ ℕ: t ∈ (−m, m) implies M_{B_k}(Z_t) < ∞.
6. (Conclusion.) Let t ∉ N and let W ⊆ ℝ^P be bounded. Then W ⊆ ball(0, r) for some r ∈ ℝ (Bornology.IsBounded.subset_ball). Choose k ∈ ℕ with r < k (exists_nat_gt), so W ⊆ B_k (ball_subset_ball). Choose m ∈ ℕ with |t| < m, so −m < t < m. By monotonicity of the local mass in the region (GeometricCurrentOn.massOn_mono) and step 5, M_W(Z_t) ≤ M_{B_k}(Z_t) < ∞. Since N is null, for L¹-a.e. t this holds for every bounded W. ∎
Appendix (verified Lean). This tactic proof of exactly the frozen statement compiled after import GMT.Ch07.Submission inside namespace GMT.Ch07 with the contract's opens. #print axioms: propext, Classical.choice, Quot.sound.
  intro hMM P q U Z μ f L hf hμ hZ
  have key : ∀ k m : ℕ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (-(m : ℝ)) m →
      (Z t).massOn (ball (0 : Euclid P) k) < ∞ := by
    intro k m
    have hfinG : μ (ball (0 : Euclid P) k ∩ {x | -(m : ℝ) < f x ∧ f x < m}) < ∞ :=
      (measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
        (hμ _ (isCompact_closedBall _ _))
    obtain ⟨g, hg, hle, hint⟩ := hMM P (fun _ => μ) f (ball (0 : Euclid P) k) (-(m : ℝ)) m L
      (fun _ t => (Z t).massOn (ball (0 : Euclid P) k)) hf (fun _ => hfinG)
      (fun _ t _ => hZ _ t isOpen_ball)
    simp only [liminf_const] at hle hint
    have hint' : ∫⁻ t in Ioo (-(m : ℝ)) m, g t ≠ ∞ :=
      (hint.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hfinG)).ne
    have hgfin : ∀ᵐ t ∂(volume.restrict (Ioo (-(m : ℝ)) m)), g t < ∞ := ae_lt_top hg hint'
    rw [ae_restrict_iff' measurableSet_Ioo] at hgfin
    filter_upwards [hle, hgfin] with t h1 h2 ht
    exact (h1 ht).trans_lt (h2 ht)
  have key2 : ∀ᵐ t ∂(volume : Measure ℝ), ∀ k m : ℕ, t ∈ Ioo (-(m : ℝ)) m →
      (Z t).massOn (ball (0 : Euclid P) k) < ∞ := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; exact key k
  filter_upwards [key2] with t ht W hW
  obtain ⟨r, hr⟩ := hW.subset_ball (0 : Euclid P)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  obtain ⟨m, hm⟩ := exists_nat_gt |t|
  have htm : t ∈ Ioo (-(m : ℝ)) m := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  exact ((Z t).massOn_mono (hr.trans (ball_subset_ball hk.le))).trans_lt (ht k m htm)

## Key steps

1. For k, m ∈ ℕ, apply (MM) on (−m, m) to the constant sequences μ_j := μ and Z_j(t) := M_{B_k(0)}(Z_t), with G := B_k(0); here μ(B_k(0) ∩ {−m < f < m}) ≤ μ(B̄_k(0)) < ∞.
2. Since the sequences are constant, M_{B_k(0)}(Z_t) ≤ g(t) a.e. on (−m, m) and ∫_{(−m,m)} g < ∞; so g, and hence M_{B_k(0)}(Z_t), is finite a.e. on (−m, m) (ae_lt_top, ae_restrict_iff').
3. Intersect over the countably many k, m (ae_all_iff). Every bounded W lies in some B_k(0) and every t in some (−m, m), so M_W(Z_t) ≤ M_{B_k(0)}(Z_t) < ∞ (massOn_mono).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp of snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (all identical)`
- `python3 -I over dag.json: frozen type of the selected node (split into IMC(a-d), SL, MM, RU) and of the sibling cbr_cc_current_algebra; accepted declarations whose type mentions IMRep and .measure (cmc_fcl_imrep_integral_data, cmc_fcl_imrep_restrict_formula, cmc_fcl_massOn_le_measure_inter, cmc_fcl_massOn_le_add, cbr_imRep_measure_basic, lcmp_imRep_measure_restrict, dor_lmb_imrep_restrict_current, rsd_imrep_compact_measure_ne_top, cmc_massOn_eq_imRep_measure); status/candidate_commit of the three reused nodes (all accepted; candidate commits cc7e5b19, 7868c22b and 1041782e); lean_name collision check for cbr_ccisp_restrict_isIntegerMultiplicity and cbr_ccisp_ae_massOn_lt_top (absent among 1310 DAG names)`
- `rg -n 'cbr_ccisp|cmc_fcl_|cbr_cc_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project --glob '*.lean' (no match)`
- `rg -n -F in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib: 'theorem ae_lt_top ', "theorem ae_restrict_iff' ", 'theorem ae_all_iff ', 'theorem _root_.Bornology.IsBounded.subset_ball', 'isCompact_closedBall' (ProperSpace export), 'theorem ball_subset_closedBall', 'theorem mul_lt_top ', 'theorem integral_zero_measure', 'theorem aestronglyMeasurable_const', 'theorem measurableSet_lt ', 'theorem exists_nat_gt', 'theorem limsup_const' (liminf_const via to_dual), 'theorem integral_withDensity_eq_integral_smul', 'theorem restrict_withDensity ', 'theorem enorm_integral_le_lintegral_enorm', 'theorem withDensity_absolutelyContinuous', 'theorem lintegral_indicator_one '`
- `grep -n in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Mass,Currents}.lean: massAdmissibleOn, GeometricCurrentOn.massOn, GeometricCurrentOn.massOn_mono, GeometricCurrentOn.le_massOn, GeometricCurrentOn.ext, GeometricCurrentOn.boundary_apply`
- `sed -n on /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, existing_by_name child-id mapping) and store.py ensure (existing nodes are returned unchanged)`
- `git show cc7e5b19a93e9f857a433ce9746013fcfc7ba856:GMT/Ch07/Submission.lean (accepted declarations are written theorem Submission.X inside namespace GMT.Ch07)`
- `lake env lean /tmp/isp-im-decomp/lean/{Types,Assembly,Restrict,AeFinite,Full,Final}.lean with #print axioms (all compile; axioms propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-326096d948/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b218e818f5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-2bdc65f87f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-a5cfc87778/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-be968f7b5a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/ProperSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/tmp/isp-im-decomp/lean/Full.lean`
- `/tmp/isp-im-decomp/lean/Final.lean`

Findings:
- The snapshot (project b4d606d, Mathlib 25730c7c) has a Contract.lean byte-identical to the workspace Contract.lean and Submission.lean.
- Neither the snapshot project nor SimonGMT contains the restriction-IM or a.e.-finite-slice-mass lemmas: rg finds no cbr_ccisp_/cmc_fcl_/cbr_cc_ match, and SimonGMT Chapter06 supplies only massOn, massOn_mono, le_massOn and GeometricCurrentOn.ext. Two new children are therefore needed.
- Three accepted DAG declarations match steps 3 and 6(i) of the supplied proof exactly: cmc_fcl_imrep_integral_data, cmc_fcl_imrep_restrict_formula and cmc_fcl_massOn_le_measure_inter. Each has status accepted with a candidate commit. They are reused by Lean name with types copied byte-for-byte, which runtime.py _existing_lean_name_problem permits.
- The new names cbr_ccisp_restrict_isIntegerMultiplicity and cbr_ccisp_ae_massOn_lt_top collide with nothing.
- Every Mathlib lemma used by the new proofs is in the pinned snapshot: ae_lt_top, ae_restrict_iff', ae_all_iff, Bornology.IsBounded.subset_ball, isCompact_closedBall, liminf_const, ENNReal.mul_lt_top, integral_zero_measure, aestronglyMeasurable_const, measurableSet_lt and exists_nat_gt.
Lean checks (lake env lean in the workspace):
- All five child types elaborate in the replayed contract scope.
- The exact frozen node type compiles from the children plus cbr_cc_current_algebra.
- Both new children compile, and the reused proofs recompile verbatim.
- Axioms are only propext, Classical.choice and Quot.sound.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1.cube_exhaust-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the supplied proof of dimred_mbl_dt_cbm_bv_trace ("Limit δ ↓ 0. Let δ_j := 1/(j + 4) ∈ (0, 1/4], δ_j ↓ 0; every point of Q₁ lies in Q_{δ_j} for all large j. The functions 1_{Q_{δ_j}}w div G converge pointwise on Q₁ to w div G and are dominated by M|w|, which is integrable on Q₁. By dominated convergence, ∫_{Q_{δ_j}} w div G → ∫_{Q₁} w div G"), stated for an arbitrary f integrable on Q₁ (dominated by |f|; for f = w div G one has |f| ≤ M|w| on Q₁) and along the filter δ → 0⁺ (𝓝[>] 0), of which the parent's sequence δ_j = 1/(j + 4) → 0⁺ is a special case. The parent applies it with k = m + 1 and f = w · div G.

Notation. Euclid k = EuclideanSpace ℝ (Fin k) with Lebesgue measure `volume`; y_i is the i-th coordinate of y (in Lean `y i`, i.e. `WithLp.ofLp y i`). Q₁ := {y : 0 < y_i < 1 for all i}. For δ ∈ ℝ, Q_δ := {z : δ < z_i < 1 − δ for all i}; 1_E is the indicator function of E.

1. Openness and measurability. For a, b ∈ ℝ, {z : a < z_i < b for all i} = ⋂_{i ∈ Fin k} ({z : a < z_i} ∩ {z : z_i < b}). Each coordinate map z ↦ z_i is continuous (the continuous map WithLp.ofLp, `PiLp.continuous_ofLp`, followed by evaluation at i, `continuous_apply`), so each set {z : a < z_i} and {z : z_i < b} is open (`isOpen_lt`), and a finite intersection of open sets is open (`isOpen_iInter_of_finite`). Hence Q₁ (a = 0, b = 1) and every Q_δ (a = δ, b = 1 − δ) are open, in particular Borel measurable (`IsOpen.measurableSet`).

2. Inclusion. If δ ≥ 0 then Q_δ ⊆ Q₁: from δ < z_i < 1 − δ we get 0 ≤ δ < z_i and z_i < 1 − δ ≤ 1.

3. Reduction to the fixed measure μ := volume⌞Q₁. Put F_δ := 1_{Q_δ} f. For δ > 0, since Q_δ is measurable (step 1) and Q₁ ∩ Q_δ = Q_δ (step 2), ∫_{Q₁} F_δ = ∫_{Q₁ ∩ Q_δ} f = ∫_{Q_δ} f (`setIntegral_indicator`). The set (0, ∞) belongs to 𝓝[>] 0 (`self_mem_nhdsWithin`), so δ ↦ ∫_{Q₁} F_δ and δ ↦ ∫_{Q_δ} f agree eventually along 𝓝[>] 0, and it suffices (`Tendsto.congr'`) to prove ∫_{Q₁} F_δ → ∫_{Q₁} f as δ → 0⁺.

4. Dominated convergence. The filter 𝓝[>] 0 on ℝ is countably generated (ℝ is first countable), so the dominated convergence theorem for countably generated filters (`tendsto_integral_filter_of_dominated_convergence`) applies to μ, the functions F_δ, the limit f and the bound |f|:
 (a) every F_δ is a.e.-strongly measurable for μ, because f is (it is integrable on Q₁) and Q_δ is measurable (step 1);
 (b) |F_δ(y)| ≤ |f(y)| for every y and every δ (`norm_indicator_le_norm_self`);
 (c) |f| is μ-integrable, because f is integrable on Q₁;
 (d) for μ-a.e. y — it suffices to treat every y ∈ Q₁, because Q₁ is measurable (`ae_restrict_mem`) — F_δ(y) → f(y) as δ → 0⁺. Indeed, fix y ∈ Q₁ and i ∈ Fin k. Since 0 < y_i and 0 < 1 − y_i, every δ in a neighbourhood of 0 satisfies δ < y_i and δ < 1 − y_i (`eventually_lt_nhds`), i.e. δ < y_i < 1 − δ. Fin k is finite, so these finitely many eventualities hold simultaneously (`Filter.eventually_all`): y ∈ Q_δ for all δ near 0, hence eventually along 𝓝[>] 0 ≤ 𝓝 0 (`nhdsWithin_le_nhds`). For such δ, F_δ(y) = f(y) (`Set.indicator_of_mem`), so δ ↦ F_δ(y) is eventually equal to the constant f(y) and converges to f(y).
Dominated convergence gives ∫_{Q₁} F_δ → ∫_{Q₁} f as δ → 0⁺, and by step 3, ∫_{Q_δ} f → ∫_{Q₁} f as δ → 0⁺. ∎ (Degenerate cases: for k = 0 the index type Fin 0 is empty, so Q_δ = Q₁ = Euclid 0 for every δ and the argument applies verbatim, `Filter.eventually_all` over an empty index being trivially true; for δ ≥ 1/2 the set Q_δ is empty when k ≥ 1, which is harmless because only δ → 0⁺ matters.)

Appendix (formalization aid only; the numbered argument above is the proof). The following Lean proof of the exact frozen type was compiled with `lake env lean` at the pinned revisions (project b4d606db, Mathlib 25730c7c, Lean v4.35.0-rc3) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology` and the contract's other opens, with no additional imports; `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_dt_cbm_bvt_cube_exhaust : ∀ (k : ℕ) (f : Euclid k → ℝ), IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} → Tendsto (fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y) (𝓝[>] 0) (𝓝 (∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, f y)) := by
  intro k f hf
  have hcoord : ∀ i : Fin k, Continuous fun z : Euclid k => z i := fun i =>
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))
  have hopen : ∀ a b : ℝ, IsOpen {z : Euclid k | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    have : {z : Euclid k | ∀ i, a < z i ∧ z i < b} =
        ⋂ i, ({z : Euclid k | a < z i} ∩ {z : Euclid k | z i < b}) := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (hcoord i)).inter (isOpen_lt (hcoord i) continuous_const)
  set Q₁ : Set (Euclid k) := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  have hQ₁m : MeasurableSet Q₁ := (hopen 0 1).measurableSet
  have hQm : ∀ δ : ℝ, MeasurableSet {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} :=
    fun δ => (hopen δ (1 - δ)).measurableSet
  have hsub : ∀ δ : ℝ, 0 ≤ δ → {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆ Q₁ :=
    fun δ hδ z hz i => ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  have hF : Tendsto (fun δ : ℝ => ∫ y in Q₁, {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}.indicator f y)
      (𝓝[>] 0) (𝓝 (∫ y in Q₁, f y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
      (Eventually.of_forall fun δ => hf.aestronglyMeasurable.indicator (hQm δ))
      (Eventually.of_forall fun δ => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _)
      hf.norm ?_
    filter_upwards [ae_restrict_mem hQ₁m] with y hy
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), y ∈ {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} := by
      have h0 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ i, δ < y i ∧ y i < 1 - δ := by
        rw [Filter.eventually_all]
        intro i
        have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < y i := eventually_lt_nhds (hy i).1
        have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 1 - y i := eventually_lt_nhds (by linarith [(hy i).2])
        filter_upwards [h1, h2] with δ hδ1 hδ2
        exact ⟨hδ1, by linarith⟩
      exact h0.filter_mono nhdsWithin_le_nhds
    exact tendsto_const_nhds.congr' (hev.mono fun δ hδ => (indicator_of_mem hδ f).symm)
  refine hF.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [setIntegral_indicator (hQm δ), Set.inter_eq_right.2 (hsub δ (le_of_lt hδ))]
```

## Key steps

1. Every set {z : a < z_i < b ∀ i} is a finite intersection of open coordinate half-spaces, so Q₁ and every Q_δ are open and measurable.
2. For δ ≥ 0, Q_δ ⊆ Q₁, so for δ > 0, ∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f, and these agree eventually along 𝓝[>] 0.
3. Every y ∈ Q₁ lies in Q_δ for all sufficiently small δ (finitely many coordinates; Filter.eventually_all), so 1_{Q_δ} f → f pointwise on Q₁.
4. Dominated convergence along the countably generated filter 𝓝[>] 0 with integrable bound |f| gives ∫_{Q_δ} f → ∫_{Q₁} f.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c…); git rev-parse HEAD (b4d606db…); cmp GMT/Ch07/Submission.lean SNAPSHOT/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean SNAPSHOT/project/GMT/Ch07/Contract.lean (both identical)`
- `rg -n 'dimred_mbl_dt_cbm_bvt|cube_cont_bound|cube_exhaust|l1_limit' SNAPSHOT/project SNAPSHOT/mathlib/Mathlib lake-packages-25730c7c/simongmt GMT -g '*.lean' (no match)`
- `python3 -I scans of RUN/dag.json (2092 nodes): selected node depth 5, status decomposing, children []; substring 'dimred_mbl_dt_cbm_bvt' occurs 0 times; no accepted node has any proposed child type; twin root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1 has a byte-identical frozen type, and its children cmcdt_cbm_bvt_{cube_cont_bound,l1_limit,cube_exhaust} have byte-identical types but status decomposing (unaccepted)`
- `rg -n over SNAPSHOT/mathlib/Mathlib for the declarations ContinuousOn.integrableOn_compact, isCompact_univ_pi, Integrable.mul_bdd, tendsto_integral_filter_of_dominated_convergence, norm_indicator_le_norm_self, setIntegral_indicator, setIntegral_mono_set, abs_integral_le_integral_abs, integral_mono_ae, ContDiff.continuous_fderiv, LinearMap.continuous_of_finiteDimensional, le_of_tendsto, isOpen_iInter_of_finite, PiLp.continuous_ofLp, Filter.eventually_all, IsCompact.exists_bound_of_continuousOn', tendsto_setIntegral_of_monotone, IntegrableOn.mul_continuousOn (found)`
- `lake env lean /tmp/dmbvt-decomp/lean/Where.lean (custom #where command using Environment.getModuleIdxFor? on 39 cited constants: all resolve inside the import closure of GMT.Ch07.Submission, e.g. IsCompact.exists_bound_of_continuousOn -> Mathlib.Analysis.Normed.Group.Bounded, PiLp.homeomorph -> Mathlib.Analysis.Normed.Lp.PiLp, Ioo_mem_nhdsGT / ge_of_tendsto' / eventually_lt_nhds -> Mathlib.Topology.Order.OrderClosed, Integrable.mul_bdd -> Mathlib.MeasureTheory.Function.L1Space.Integrable)`
- `python3 -I loading verifier/gmt-compare.py: contract_scope(GMT/Ch07/Contract.lean, 'GMT.Ch07.main_theorem') -> [open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end]; lake env lean /tmp/dmbvt-decomp/lean/Challenge_{cube_cont_bound,l1_limit,cube_exhaust,parent}.lean (only 'declaration uses sorry')`
- `lake env lean /tmp/dmbvt-decomp/lean/Check.lean, CheckAxioms.lean and FromJson.lean (generated from the final JSON strings): children fully proved with axioms [propext, Classical.choice, Quot.sound]; exact parent type proved from the three child types and the exact frozen types of dimred_mbl_dt_cbm_smooth_approx / dimred_mbl_dt_cbm_smooth_trace declared as axioms; the parent's only extra axioms are those two stand-ins`
- `validate_lean_statement from verifier/lean_contract.py and /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py on the three child types (accepted, unchanged)`
- `sed -n 1380,1440p and grep -n 'def _existing_lean_name_problem' -A60 /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (depth gate node.depth >= max_depth; an unaccepted node under another parent cannot share a name)`
- `python3 -I dump of RUN/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-59622a92c9/decomposition-v1.json; diff of its parent-supplied-natural-proof.md with RUN/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-cdacf20fe4/parent-supplied-natural-proof.md (same steps 0–3, wording only)`
- `git show 64f176020a955d00c93754cd060d8de53ac5e331:GMT/Ch07/Submission.lean | grep -n 'namespace\|^theorem' (accepted declarations are `theorem Submission.X` inside namespace GMT.Ch07 after the section end)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-cdacf20fe4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-cdacf20fe4/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-59622a92c9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-59622a92c9/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-59622a92c9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/dmbvt-decomp/lean/FromJson.lean`
- `/tmp/dmbvt-decomp/lean/CheckAxioms.lean`
- `/tmp/dmbvt-decomp/lean/Challenge_cube_cont_bound.lean`
- `/tmp/dmbvt-decomp/lean/Challenge_l1_limit.lean`
- `/tmp/dmbvt-decomp/lean/Challenge_cube_exhaust.lean`
- `/tmp/dmbvt-decomp/lean/Challenge_parent.lean`
- `/tmp/dmbvt-decomp/lean/Where.lean`

The pins match (project b4d606db, Mathlib 25730c7c), and Submission.lean is byte-identical to the frozen contract. Neither the snapshot project, Mathlib nor SimonGMT contains these three lemmas under any name (no rg match), and no accepted DAG node has their types. The only identical types are the twin's unaccepted cmcdt_cbm_bvt_* children, owned by another parent, so fresh names dimred_mbl_dt_cbm_bvt_* are required; they occur nowhere. Every Mathlib lemma the proofs use exists at the pinned revision inside the bare import closure of GMT.Ch07.Submission, so no extra imports are needed. The three child types elaborate in the exact comparator challenge form and pass both statement validators. Complete Lean proofs of all three children compile using only propext, Classical.choice and Quot.sound. The exact frozen parent type compiles from the three child types plus the exact frozen sibling types (smooth_approx, smooth_trace), with no other axioms.

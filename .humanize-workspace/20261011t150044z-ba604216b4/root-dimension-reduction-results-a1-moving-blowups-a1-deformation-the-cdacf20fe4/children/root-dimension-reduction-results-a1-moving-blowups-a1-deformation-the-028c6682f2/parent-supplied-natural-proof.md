# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.bv_trace-a1.l1_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of dimred_mbl_dt_cbm_bv_trace ("Limit k → ∞. |∫_{Q_δ} v_k div G − ∫_{Q_δ} w div G| ≤ ∫_{Q_δ}|v_k − w||div G| ≤ Mε_k → 0, and |∫_{Q_δ}|v_k| − ∫_{Q_δ}|w|| ≤ ε_k → 0. Passing to the limit in the inequality of step 1"), stated for an arbitrary measure space (α, μ) with α : Type, a measurable set S, a multiplier h and constants A, B ≥ 0, M. The parent applies it with α = Euclid (m + 1), μ = volume, S = Q_δ (open, hence measurable), h = div G, A = (2(m + 1) + 1)V, B = 4(m + 1) and the bound M of its step 0.

Notation. ∫_S F means ∫ x in S, F x ∂μ, the Bochner integral for the restricted measure μ⌞S. Put ε_k := ∫_S |v_k − w|.

1. A.e. bound and integrability of the products. S is measurable, so μ⌞S-almost every x lies in S (`ae_restrict_mem`); hence ‖h(x)‖ = |h(x)| ≤ M for μ⌞S-a.e. x. Since h is a.e.-strongly measurable for μ⌞S and essentially bounded by M there, while w and every v_k are μ⌞S-integrable, the products w·h and v_k·h are μ⌞S-integrable (`Integrable.mul_bdd`: integrable times essentially bounded a.e.-strongly measurable is integrable). Also v_k − w, |v_k − w|, |v_k| and |w| are μ⌞S-integrable.

2. Difference estimate. Fix k. By linearity (step 1), ∫_S w h − ∫_S v_k h = ∫_S (w h − v_k h), hence |∫_S w h − ∫_S v_k h| ≤ ∫_S |w h − v_k h| (`abs_integral_le_integral_abs`). For every x ∈ S, hence for μ⌞S-a.e. x, |w(x)h(x) − v_k(x)h(x)| = |v_k(x) − w(x)|·|h(x)| ≤ |v_k(x) − w(x)|·M = M|v_k(x) − w(x)|, using |h(x)| ≤ M and |v_k(x) − w(x)| ≥ 0 (no sign condition on M is needed). Both sides are μ⌞S-integrable, so monotonicity of the integral (`integral_mono_ae`) and `integral_const_mul` give |∫_S w h − ∫_S v_k h| ≤ ∫_S M|v_k − w| = M ε_k.

3. Comparison of ∫|v_k| with ∫|w|. For every x, |v_k(x)| = |w(x) + (v_k(x) − w(x))| ≤ |w(x)| + |v_k(x) − w(x)|. The three functions are μ⌞S-integrable, so `integral_mono` and `integral_add` give ∫_S |v_k| ≤ ∫_S |w| + ε_k.

4. Estimate for fixed k. By |a| ≤ |b| + |a − b| (from `abs_sub_abs_le_abs_sub`), the hypothesis for v_k, step 2, and step 3 multiplied by B ≥ 0:
|∫_S w h| ≤ |∫_S v_k h| + |∫_S w h − ∫_S v_k h| ≤ (A + B∫_S |v_k|) + M ε_k ≤ A + B(∫_S |w| + ε_k) + M ε_k = A + B∫_S |w| + (B + M) ε_k.

5. Limit. Since ε_k → 0, the sequence A + B∫_S |w| + (B + M) ε_k tends to A + B∫_S |w| + (B + M)·0 = A + B∫_S |w| (`tendsto_const_nhds.add (Tendsto.const_mul …)`). By step 4 the constant |∫_S w h| is ≤ every term of this sequence, so it is ≤ its limit (`ge_of_tendsto'`): |∫_S w h| ≤ A + B∫_S |w|. ∎ (Degenerate cases need no separate treatment: if S is empty or μ-null, every integral over S vanishes, the hypothesis for any k reads 0 ≤ A, and steps 1–5 still apply verbatim; likewise nothing above uses the sign of M.)

Appendix (formalization aid only; the numbered argument above is the proof). The following Lean proof of the exact frozen type was compiled with `lake env lean` at the pinned revisions (project b4d606db, Mathlib 25730c7c, Lean v4.35.0-rc3) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the frozen contract's `open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology` and the contract's other opens, with no additional imports; `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.dimred_mbl_dt_cbm_bvt_l1_limit : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (v : ℕ → α → ℝ) (w h : α → ℝ) (A B M : ℝ), MeasurableSet S → 0 ≤ B → (∀ k, IntegrableOn (v k) S μ) → IntegrableOn w S μ → AEStronglyMeasurable h (μ.restrict S) → (∀ x ∈ S, |h x| ≤ M) → Tendsto (fun k => ∫ x in S, |v k x - w x| ∂μ) atTop (𝓝 0) → (∀ k, |∫ x in S, v k x * h x ∂μ| ≤ A + B * ∫ x in S, |v k x| ∂μ) → |∫ x in S, w x * h x ∂μ| ≤ A + B * ∫ x in S, |w x| ∂μ := by
  intro α _ μ S v w h A B M hS hB hv hw hh hM hlim hbound
  have hae : ∀ᵐ x ∂(μ.restrict S), ‖h x‖ ≤ M := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simpa [Real.norm_eq_abs] using hM x hx
  have hwh : Integrable (fun x => w x * h x) (μ.restrict S) := Integrable.mul_bdd hw hh hae
  have hvh : ∀ k, Integrable (fun x => v k x * h x) (μ.restrict S) :=
    fun k => Integrable.mul_bdd (hv k) hh hae
  have key : ∀ k, |∫ x in S, w x * h x ∂μ| ≤
      A + B * ∫ x in S, |w x| ∂μ + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by
    intro k
    have hdiff : Integrable (fun x => |v k x - w x|) (μ.restrict S) := ((hv k).sub hw).abs
    have h1 : |∫ x in S, w x * h x ∂μ - ∫ x in S, v k x * h x ∂μ| ≤
        M * ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_sub hwh (hvh k), ← integral_const_mul]
      refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hwh.sub (hvh k)).abs
        (hdiff.const_mul M) ?_)
      filter_upwards [ae_restrict_mem hS] with x hx
      have hx' : |h x| ≤ M := hM x hx
      calc |w x * h x - v k x * h x| = |v k x - w x| * |h x| := by
            rw [← sub_mul, abs_mul, abs_sub_comm]
        _ ≤ |v k x - w x| * M := mul_le_mul_of_nonneg_left hx' (abs_nonneg _)
        _ = M * |v k x - w x| := mul_comm _ _
    have h2 : ∫ x in S, |v k x| ∂μ ≤ ∫ x in S, |w x| ∂μ + ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_add hw.abs hdiff]
      refine integral_mono (hv k).abs (hw.abs.add hdiff) fun x => ?_
      have := abs_add_le (w x) (v k x - w x)
      simp only [add_sub_cancel] at this
      exact this
    have h3 := hbound k
    calc |∫ x in S, w x * h x ∂μ|
        ≤ |∫ x in S, v k x * h x ∂μ| + |∫ x in S, w x * h x ∂μ - ∫ x in S, v k x * h x ∂μ| := by
          linarith [abs_sub_abs_le_abs_sub (∫ x in S, w x * h x ∂μ) (∫ x in S, v k x * h x ∂μ)]
      _ ≤ (A + B * ∫ x in S, |v k x| ∂μ) + M * ∫ x in S, |v k x - w x| ∂μ := add_le_add h3 h1
      _ ≤ (A + B * (∫ x in S, |w x| ∂μ + ∫ x in S, |v k x - w x| ∂μ)) +
            M * ∫ x in S, |v k x - w x| ∂μ := by gcongr
      _ = A + B * ∫ x in S, |w x| ∂μ + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by ring
  have hlim' : Tendsto (fun k => A + B * ∫ x in S, |w x| ∂μ + (B + M) * ∫ x in S, |v k x - w x| ∂μ)
      atTop (𝓝 (A + B * ∫ x in S, |w x| ∂μ + (B + M) * 0)) :=
    tendsto_const_nhds.add (hlim.const_mul _)
  simpa using ge_of_tendsto' hlim' key
```

## Key steps

1. |h| ≤ M on the measurable set S gives an a.e. bound for μ⌞S, so w·h and every v_k·h are integrable on S (Integrable.mul_bdd).
2. |∫_S w h − ∫_S v_k h| ≤ ∫_S |v_k − w||h| ≤ M ε_k with ε_k := ∫_S |v_k − w|.
3. ∫_S |v_k| ≤ ∫_S |w| + ε_k.
4. Hence |∫_S w h| ≤ A + B∫_S |w| + (B + M) ε_k for every k (B ≥ 0).
5. Let k → ∞ (ε_k → 0) and conclude with ge_of_tendsto'.

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

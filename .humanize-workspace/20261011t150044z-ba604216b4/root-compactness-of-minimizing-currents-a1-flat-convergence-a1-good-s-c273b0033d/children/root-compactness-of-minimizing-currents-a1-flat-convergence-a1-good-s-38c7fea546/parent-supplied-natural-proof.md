# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1.window_lintegral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent-supplied proof of cmc_fc_gs_ae_quotient_finite (Tonelli on the open set E_h). Here it is stated for an arbitrary s-finite measure ν and an arbitrary real h. Notation: Leb is Lebesgue measure on ℝ (Mathlib volume), ∫⁻ is the [0, ∞]-valued Lebesgue integral, and Leb ⊗ ν is the product measure on ℝ × ℝ (Mathlib volume.prod ν).

1. (The set E is measurable.) Let E := {(t, x) ∈ ℝ × ℝ : t − h < x and x < t}. Then E = A ∩ B with A := {p : p.1 − h < p.2} and B := {p : p.2 < p.1}. Each of A and B is the set where one measurable (indeed continuous) real function on ℝ × ℝ is strictly smaller than another. These functions are built from the projections p ↦ p.1 and p ↦ p.2 and subtraction of the constant h. So A and B are measurable (Mathlib measurableSet_lt), and hence so is E = A ∩ B.

2. (Sections of E.) Fix t ∈ ℝ. Then {x : (t, x) ∈ E} = {x : t − h < x < t} = (t − h, t), directly from the definition. Now fix x ∈ ℝ. Then {t : (t, x) ∈ E} = (x, x + h). Indeed t − h < x ⟺ t < x + h, so (t − h < x and x < t) ⟺ (x < t and t < x + h). Both directions are linear arithmetic.

3. (Measurability.) Since ν is s-finite and E is measurable, the function t ↦ ν({x : (t, x) ∈ E}) is measurable (Mathlib measurable_measure_prodMk_left, which needs only s-finiteness of ν). By step 2 this function is t ↦ ν((t − h, t)), which proves the first claim.

4. (Tonelli, integrating over t.) Since ν is s-finite and E is measurable, Mathlib Measure.prod_apply gives (Leb ⊗ ν)(E) = ∫⁻ ν({x : (t, x) ∈ E}) dt. By step 2 this equals ∫⁻ ν((t − h, t)) dt.

5. (Tonelli, integrating over x.) Leb is σ-finite, hence s-finite, and ν is s-finite. So Mathlib Measure.prod_apply_symm gives (Leb ⊗ ν)(E) = ∫⁻ Leb({t : (t, x) ∈ E}) dν(x). By step 2 this equals ∫⁻ Leb((x, x + h)) dν(x).

6. (Lebesgue measure of the sections.) For every x ∈ ℝ, Leb((x, x + h)) = ENNReal.ofReal((x + h) − x) = ENNReal.ofReal(h). This is Mathlib Real.volume_Ioo, valid for all real endpoints; when h ≤ 0 the interval is empty and both sides are 0. So the integrand in step 5 is the constant ENNReal.ofReal(h), and ∫⁻ ENNReal.ofReal(h) dν = ENNReal.ofReal(h)·ν(ℝ) (Mathlib lintegral_const).

7. (Conclusion.) Steps 4, 5 and 6 give ∫⁻ ν((t − h, t)) dt = (Leb ⊗ ν)(E) = ENNReal.ofReal(h)·ν(ℝ). This is the second claim; together with step 3 it proves the theorem. ∎

## Key steps

1. E := {(t, x) : t − h < x < t} is the intersection of two strict-inequality sets of measurable functions, so it is measurable (measurableSet_lt).
2. Sections: for fixed t, {x : (t, x) ∈ E} = (t − h, t); for fixed x, {t : (t, x) ∈ E} = (x, x + h).
3. Since ν is s-finite, t ↦ ν((t − h, t)) is measurable (measurable_measure_prodMk_left).
4. Tonelli in both orders (Measure.prod_apply, Measure.prod_apply_symm): ∫⁻ ν((t − h, t)) dt = (Leb ⊗ ν)(E) = ∫⁻ Leb((x, x + h)) dν(x).
5. Leb((x, x + h)) = ofReal(h) (Real.volume_Ioo), so the right side is ofReal(h)·ν(ℝ) (lintegral_const).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `rg -n "theorem measurable_measure_prodMk_left |theorem prod_apply |theorem prod_apply_symm|theorem lintegral_liminf_le |theorem ae_lt_top |theorem Measurable.liminf |liminf_le_liminf_comp|theorem liminf_congr|theorem liminf_le_liminf |theorem tendsto_one_div_add_atTop_nhds_zero_nat|theorem lintegral_const_mul |theorem lintegral_const |theorem volume_Ioo|theorem restrict_apply_univ|theorem restrict_apply |theorem liminf_const " mathlib/Mathlib --glob '*.lean'`
- `rg -n -B2 "theorem limsup_le_limsup \{|theorem limsup_congr \{|theorem limsup_const |lemma limsup_const " mathlib/Mathlib/Order --glob '*.lean' (to_dual sources of liminf_le_liminf, liminf_congr, liminf_const)`
- `rg -n "theorem ofReal_inv_of_pos|theorem mul_inv_cancel|theorem ofReal_natCast|theorem ofReal_add " mathlib/Mathlib/Basic/ENNReal; rg -n "theorem tendsto_nhdsWithin_iff" mathlib/Mathlib; rg -n "theorem measurableSet_lt " mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean; rg -n "lemma ofReal_natCast|theorem ne_top_of_le_ne_top|theorem tendsto_order " mathlib/Mathlib`
- `rg -n "Ioo \(t - h\) t|Ioo \(x - h\) x|Ioo \(t - r\) t" mathlib/Mathlib project --glob '*.lean' (no match)`
- `rg -n "lintegral_measure_Ioo|measure_Ioo_sub|lintegral_measure_Ioc_sub|∫⁻ [a-z], [a-zμν]+ \((Ioo|Ioc|Ico|Icc) \([a-z] - " mathlib/Mathlib project --glob '*.lean' (no match)`
- `rg -n "cmc_fc_gs|aqf_" project --glob '*.lean' (no match); rg -n "liminf .*𝓝\[>\] 0" project --glob '*.lean' (no match)`
- `python3 scan of dag.json: lean_name membership of cmc_fc_gs_aqf_window_lintegral / cmc_fc_gs_aqf_ae_seq_liminf_finite / cmc_fc_gs_aqf_liminf_le_seq (all absent); lean_statement patterns 'Ioo (t - h) t', 'ofReal h *', 'SFinite', 'liminf (fun n : ℕ', '∫⁻ t, ', 'h⁻¹ *', 'liminf (fun h'; node status and children of the selected node`
- `sed -n 560,613p verifier/gmt-compare.py (contract_scope, child_modules); sed -n 2790,2840p and 6532,6575p runtime.py (_install_speculative_assumptions, _existing_lean_name_problem); sed -n 16,96p lean_contract.py (validate_lean_statement)`
- `python3 -I /tmp/aqf2-dec-b7c1/gen.py (imports verifier/gmt-compare.py child_modules in 'contract' mode and lean_contract.validate_lean_statement; writes exact NodeChallenge/NodeSolution files)`
- `lake env lean /tmp/aqf2-dec-b7c1/gen/{parent,window_lintegral,ae_seq_liminf_finite,liminf_le_seq}_NodeChallenge.lean`
- `lake env lean /tmp/aqf2-dec-b7c1/proofs/{Full,FullSolution,Stub,InstancesFull}.lean (complete child proofs, exact-type assembly, comparator resolution, speculative-stub scope, rfl instance checks, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/BoundedOrder/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-c273b0033d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-c273b0033d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-c273b0033d/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/lean_contract.py`
- `/tmp/aqf2-dec-b7c1/gen/parent_NodeChallenge.lean`
- `/tmp/aqf2-dec-b7c1/gen/window_lintegral_NodeChallenge.lean`
- `/tmp/aqf2-dec-b7c1/gen/ae_seq_liminf_finite_NodeChallenge.lean`
- `/tmp/aqf2-dec-b7c1/gen/liminf_le_seq_NodeChallenge.lean`
- `/tmp/aqf2-dec-b7c1/proofs/Full.lean`
- `/tmp/aqf2-dec-b7c1/proofs/FullSolution.lean`
- `/tmp/aqf2-dec-b7c1/proofs/Stub.lean`
- `/tmp/aqf2-dec-b7c1/proofs/InstancesFull.lean`

Snapshot revisions: project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are identical.

Neither the snapshot project nor the pinned Mathlib states any of the three child obligations. The sliding-window and window-lintegral searches and the project searches for cmc_fc_gs/aqf_ and for 𝓝[>] 0 liminfs all returned no match. So each child is a new obligation.

Every tool the child proofs use exists in the snapshot:
- measurable_measure_prodMk_left: Measure/Prod.lean:97, needs only [SFinite ν]
- Measure.prod_apply: Prod.lean:223
- Measure.prod_apply_symm: Prod.lean:706
- measurableSet_lt: BorelSpace/Order.lean:245
- Real.volume_Ioo: Lebesgue/Basic.lean:96
- lintegral_const: Integral/Lebesgue/Basic.lean:110
- lintegral_const_mul: Add.lean:381
- lintegral_liminf_le (Fatou): Add.lean:233
- Measurable.liminf: BorelSpace/Order.lean:1058
- ae_lt_top: Markov.lean:159
- Filter.Tendsto.liminf_le_liminf_comp: LiminfLimsup.lean:181 via to_dual, form Tendsto v f g → liminf u g ≤ liminf (u ∘ v) f
- liminf_le_liminf, liminf_congr, liminf_const: to_dual of LiminfLimsup.lean:159/201/213
- tendsto_one_div_add_atTop_nhds_zero_nat: SpecificLimits/Basic.lean:70
- tendsto_nhdsWithin_iff: NhdsWithin.lean:474
- tendsto_order: Topology/Order/Basic.lean:139
- ENNReal.ofReal_inv_of_pos: Inv.lean:945
- ENNReal.mul_inv_cancel: Inv.lean:103
- ENNReal.ofReal_add: Real.lean:52
- ENNReal.ofReal_natCast: Basic.lean:510
- Measure.restrict_apply and restrict_apply_univ: Restrict.lean:75/168
- ne_top_of_le_ne_top: BoundedOrder/Basic.lean:206

The three bare names are absent from dag.json, and the selected node has no children. No accepted node has an identical type. The nearest node, cmcs_smi_lintegral_left_density_le (different parent, speculative-ready), has a different type and is not reused.

With the pinned toolchain, all the following compile:
- the verifier-generated contract-mode challenges for the parent and all three children;
- complete scratch proofs of the three children;
- the exact-type parent assembly;
- comparator-style exact Submission.X solutions;
- the assembly against the runtime's speculative-stub axioms;
- rfl instance checks.
Every #print axioms report lists only propext, Classical.choice and Quot.sound, except the stub run, which also lists the two child stub axioms the assembly uses.

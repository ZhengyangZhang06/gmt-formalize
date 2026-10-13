# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.box_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (F3) of the parent proof of `cmcdt_cbm_smooth_trace`: continuous functions are bounded on the closed cube, which has finite measure, so all integrals over Q_δ are finite. Here it is isolated as a lemma about an arbitrary open box. The parent uses it for the integrands ∂_i(vG_i), Dv(G) and ‖Dv‖, and the sibling `cmcdt_cbm_st_coord_bound` uses it for F, H, |v| and ‖Dv‖.

Notation. n ∈ ℕ. ℝⁿ is `Euclid n` = EuclideanSpace ℝ (Fin n) with Lebesgue measure (volume), and z_j := z.ofLp j is the j-th coordinate (j ∈ Fin n). Let a, b ∈ ℝ be arbitrary; no order between them is assumed. Put B := {z ∈ ℝⁿ : a < z_j < b for all j}. Let h : ℝⁿ → ℝ be continuous. Claim: h is integrable on B (IntegrableOn h B).

1. Closed box. Let I := {w ∈ Fin n → ℝ : a ≤ w_j ≤ b for all j}. This is the order interval Icc (fun _ => a) (fun _ => b) for the product order. Let K := toLp(I) ⊆ ℝⁿ be its image under the canonical map toLp 2 : (Fin n → ℝ) → Euclid n. (If a > b and n ≥ 1, then I = K = ∅. If n = 0, then I and K are single points. Neither case needs separate treatment.)
2. B ⊆ K. Let z ∈ B and w := z.ofLp. Then a < w_j < b, hence a ≤ w_j ≤ b, for every j. So w ∈ I and z = toLp w ∈ K.
3. K is compact. I is compact because closed order intervals of the finite product Fin n → ℝ are compact (Mathlib `isCompact_Icc`). The map toLp 2 is continuous (`PiLp.continuous_toLp`), and the continuous image of a compact set is compact.
4. h is integrable on K. h is continuous, so it is continuous on K. Lebesgue measure on ℝⁿ is finite on compact sets, so a function continuous on a compact set is integrable on it (`ContinuousOn.integrableOn_compact`).
5. Since B ⊆ K (step 2), integrability restricts from K to B (`IntegrableOn.mono_set`). Hence h is integrable on B. ∎

Formalization notes. A scratch build checked the Lean proof below against exactly this frozen type. It used Lean v4.35.0-rc3 and Mathlib 25730c7c, with the declaration inserted into a copy of `GMT/Ch07/Submission.lean` after the contract's `noncomputable section … end` and before `main_theorem`, in namespace `GMT.Ch07` with the contract's `open`s. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.cmcdt_cbm_st_box_integrableOn : ∀ (n : ℕ) (h : Euclid n → ℝ) (a b : ℝ), Continuous h → IntegrableOn h {z : Euclid n | ∀ j, a < z j ∧ z j < b} := by
  intro n h a b hh
  have hsub : {z : Euclid n | ∀ j, a < z j ∧ z j < b} ⊆
      (WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hz j).1.le, fun j => (hz j).2.le⟩, rfl⟩
  have hKc : IsCompact ((WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  exact (hh.continuousOn.integrableOn_compact hKc).mono_set hsub
```

## Key steps

1. B ⊆ K := toLp '' Icc (fun _ => a) (fun _ => b), the closed box.
2. K is compact: the order interval Icc in Fin n → ℝ is compact and toLp 2 is continuous.
3. A continuous h is integrable on the compact set K (ContinuousOn.integrableOn_compact).
4. Restrict from K to B ⊆ K (IntegrableOn.mono_set).

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C <snapshot>/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest)`
- `rg -c 'cmcdt_cbm_st_' <snapshot> -g '*.lean' (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name/theorems fields for the five proposed names (no collision)`
- `rg -n 'theorem volume_preserving_piFinSuccAbove|theorem PiLp.volume_preserving_toLp|theorem integral_prod_symm|theorem MeasurePreserving.setIntegral_preimage_emb|theorem MeasurePreserving.integrableOn_comp_preimage|lemma trace_eq_sum_inner|theorem EuclideanSpace.inner_single_left|theorem norm_apply_le|theorem contDiff_piLp_apply|theorem integral_deriv_eq_sub|theorem integral_mono_interval|theorem norm_integral_le_abs_integral_norm|theorem Integrable.integral_prod_right|theorem forall_iff_succAbove|theorem basisFun_apply' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `grep -n 'def piFinSuccAbove' <snapshot>/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `rg -n 'piFinSuccAbove|insertNth|trace_eq_sum_inner|integral_divergence|integral_prod_symm|volume_preserving_toLp' <snapshot>/project -g '*.lean' (no match) and lake-packages-25730c7c/simongmt -g '*.lean' (only proof-internal uses; euclideanDivergence_eq_sum_inner in Chapter02/BV.lean is a wrapper of LinearMap.trace_eq_sum_inner)`
- `lake env lean /tmp/st-decomp-ch07/final/FromProofs.lean (copy of GMT/Ch07/Submission.lean + the five children + the parent; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/st-decomp-ch07/final/CompareSim.lean (comparator-style challenges via gmt-compare.py contract_scope); python3 -I verifier/lean_contract.py validate_lean_statement on all six types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/st-decomp-ch07/final/FromProofs.lean`
- `/tmp/st-decomp-ch07/final/CompareSim.lean`

Nothing in the snapshot can be reused for this node.
- The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace, and Submission.lean is byte-identical to Contract.lean.
- The project has no slicing, Fubini, trace or divergence lemma.
- SimonGMT only wraps LinearMap.trace_eq_sum_inner (euclideanDivergence_eq_sum_inner).

Mathlib 25730c7c supplies every tool used, all within the import closure of GMT.Ch07.Submission:
- volume_preserving_piFinSuccAbove and MeasurableEquiv.piFinSuccAbove;
- PiLp.volume_preserving_toLp;
- MeasurePreserving.setIntegral_preimage_emb and integrableOn_comp_preimage;
- Measure.prod_restrict, integral_prod_symm and Integrable.integral_prod_right;
- intervalIntegral.integral_deriv_eq_sub, integral_mono_interval and norm_integral_le_abs_integral_norm;
- LinearMap.trace_eq_sum_inner, EuclideanSpace.inner_single_left, PiLp.norm_apply_le and contDiff_piLp_apply;
- Fin.forall_iff_succAbove and Fin.succAboveCases.

The five child proofs and the parent assembly compile in a copy of Submission.lean with no extra imports, and #print axioms gives propext, Classical.choice and Quot.sound only. The proposed names cmcdt_cbm_st_* collide with nothing in the snapshot or the DAG.

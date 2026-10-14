# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_volume-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.isodiametric_bound-a1.steiner_volume-a1.steiner_slice_length-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3, 4 and 5 of the parent proof of cbr_ci_iso_steiner_volume_eq, written for the line through an arbitrary point y ∈ ℝ^d instead of the fibre over z (Simon Ch. 1, proof of 2.10: S_j(A) meets each line ℓ_j(ξ) that meets A in the closed segment {|t| ≤ ½ L¹(A ∩ ℓ_j(ξ))}). Notation: x[j↦s] := WithLp.toLp 2 (Function.update x.ofLp j s), A^j_x := {s ∈ ℝ : x[j↦s] ∈ A}, x_j := x.ofLp j. Fix y ∈ ℝ^d and put B := A^j_y, ℓ := (L¹(B)).toReal ≥ 0 and F := {t ∈ ℝ : y[j↦t] ∈ S_j(A)}. We must show L¹(F) = L¹(B).
1. Coordinate identities. For t ∈ ℝ, (y[j↦t]).ofLp = Function.update y.ofLp j t (WithLp.ofLp_toLp), so (y[j↦t])_j = Function.update y.ofLp j t j = t (Function.update_self). For t, s ∈ ℝ, Function.update (Function.update y.ofLp j t) j s = Function.update y.ofLp j s (Function.update_idem), so (y[j↦t])[j↦s] = y[j↦s]. Consequently A^j_{y[j↦t]} = {s : y[j↦s] ∈ A} = B for every t ∈ ℝ.
2. Description of F. By the definition of S_j(A), t ∈ F iff A^j_{y[j↦t]} ≠ ∅ and |(y[j↦t])_j| ≤ (L¹(A^j_{y[j↦t]})).toReal/2. By step 1 this condition reads: B ≠ ∅ and |t| ≤ ℓ/2. So F = {t ∈ ℝ : B ≠ ∅ ∧ |t| ≤ ℓ/2}.
3. L¹(B) < ∞. The coordinate map π : ℝ^d → ℝ, π(x) := x_j, is continuous, so π(A) is compact (IsCompact.image) and L¹(π(A)) < ∞ (IsCompact.measure_lt_top). If t ∈ B, then x := y[j↦t] ∈ A and π(x) = t by step 1. Thus B ⊆ π(A), and L¹(B) < ∞ by measure_lt_top_of_subset.
4. Case B = ∅. No t satisfies the condition of step 2, so F = ∅ and L¹(F) = 0 = L¹(∅) = L¹(B).
5. Case B ≠ ∅. Then F = {t : |t| ≤ ℓ/2} = [−ℓ/2, ℓ/2] (abs_le). By Real.volume_Icc, L¹(F) = ofReal(ℓ/2 − (−ℓ/2)) = ofReal(ℓ) = ofReal((L¹(B)).toReal). This equals L¹(B) by ENNReal.ofReal_toReal, which applies because L¹(B) ≠ ∞ by step 3. (When ℓ = 0, F = {0} and both sides are 0.)
6. In both cases L¹({t : y[j↦t] ∈ S_j(A)}) = L¹(F) = L¹(B) = L¹(A^j_y). Since y ∈ ℝ^d was arbitrary, the claim holds for every y. ∎

## Key steps

1. (y[j↦t])_j = t and (y[j↦t])[j↦s] = y[j↦s] (WithLp.ofLp_toLp, Function.update_self, Function.update_idem), so A^j_{y[j↦t]} = A^j_y =: B for every t.
2. Hence {t : y[j↦t] ∈ S_j(A)} = {t : B ≠ ∅ ∧ |t| ≤ (L¹ B).toReal / 2}.
3. B is contained in the compact image π_j(A), so L¹(B) < ∞.
4. If B = ∅ both measures are 0. Otherwise the set is Icc (−ℓ/2) (ℓ/2), whose measure is ofReal ℓ = L¹(B) (Real.volume_Icc, ENNReal.ofReal_toReal).

## Reference use

### local-project

Queries:
- `cat manifest.json in the snapshot (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean with workspace GMT/Ch07/Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `rg -il 'cavalieri|steiner' project mathlib/Mathlib → only mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean and Analysis/SpecialFunctions/Pow/Integral.lean (layer-cake formula ∫ f = ∫ μ{f > t} dt, not coordinate slicing); rg -il 'isodiametric|steiner|cavalieri' project → only project/GMT/Ch01/{Contract.lean,Submission.lean,README.md}, outside the Ch07 import closure; rg -n cbr_ci_iso_svol project → no match`
- `rg -n in snapshot mathlib: volume_preserving_piFinSuccAbove (MeasureTheory/Constructions/Pi.lean:818), MeasurableEquiv.piFinSuccAbove (MeasureTheory/MeasurableSpace/Embedding.lean:566), Measure.prod_apply_symm (MeasureTheory/Measure/Prod.lean:706), PiLp.volume_preserving_toLp (MeasureTheory/Measure/Haar/InnerProductSpace.lean:139), MeasurePreserving.measure_preimage (Dynamics/Ergodic/MeasurePreserving.lean:142), Fin.update_insertNth (Data/Fin/Tuple/Basic.lean:1050), Fin.insertNth_apply_same (Data/Fin/Tuple/Basic.lean:855), Function.update_idem (Logic/Function/Basic.lean:792), Function.update_self (Logic/Function/Basic.lean:648), WithLp.ofLp_toLp (Analysis/Normed/Lp/WithLp.lean:96), Real.volume_Icc (MeasureTheory/Measure/Lebesgue/Basic.lean:86), ENNReal.ofReal_toReal (Basic/ENNReal/Basic.lean:248), measure_lt_top_of_subset (MeasureTheory/Measure/MeasureSpaceDef.lean:265), IsCompact.measure_lt_top (MeasureTheory/Measure/Typeclasses/Finite.lean:346), IsCompact.measurableSet (MeasureTheory/Constructions/BorelSpace/Basic.lean:262), lintegral_congr (MeasureTheory/Integral/Lebesgue/Basic.lean:278)`
- `lake env lean /tmp/svol-decomp/Reach.lean (import GMT.Ch07.Submission): Poincare.SimonGMT.Chapter01.volume_simonCenteredSlice, volume_le_volume_simonSteinerSymmetrization, simonSteinerSymmetrization are unknown identifiers (outside the import closure); Measure.prod_apply_symm, volume_preserving_piFinSuccAbove, Fin.update_insertNth are reachable`
- `read lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/{SteinerVolume,SteinerSliceBounds,SteinerDiameter}.lean (same Mathlib pin): template for φ = toLp ∘ (piFinSuccAbove).symm, the prod_apply_symm chain and the centred-slice length computation`
- `lake env lean /tmp/svol-decomp/Scratch.lean: Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq and Submission.cbr_ci_iso_svol_steiner_slice_volume_eq proved, and the frozen parent type derived from them; #print axioms: propext, Classical.choice, Quot.sound`
- `python3 -I with verifier/gmt-compare.py child_modules(mode contract) → /tmp/svol-decomp/cmp/*_{Challenge,Solution}.lean for both children and the frozen parent type; lake env lean on all six files: challenges elaborate (only the sorry warning), solutions close by exact Submission.X with axioms propext, Classical.choice, Quot.sound`
- `validate_lean_statement from /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py and verifier/lean_contract.py on both child statements: pass, unchanged`
- `python3 -I scan of dag.json lean_name values (1523 nodes; cbr_ci_iso_* = the 9 parent-level names only) and grep -rl cbr_ci_iso_svol over runs/.../nodes and dag.json: no reservation`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Logic/Function/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b1e99d8ae2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b1e99d8ae2/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerVolume.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerSliceBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/SteinerDiameter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/svol-decomp/Scratch.lean`
- `/tmp/svol-decomp/Reach.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_svol_volume_eq_of_slice_volume_eq_Challenge.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_svol_volume_eq_of_slice_volume_eq_Solution.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_svol_steiner_slice_volume_eq_Challenge.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_svol_steiner_slice_volume_eq_Solution.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_steiner_volume_eq_test_Challenge.lean`
- `/tmp/svol-decomp/cmp/cbr_ci_iso_steiner_volume_eq_test_Solution.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Mathlib has no coordinate-slice Cavalieri theorem (its 'Cavalieri' is the layer-cake formula) and no Steiner symmetrization. The SimonGMT Chapter01 Steiner lemmas (volume_simonCenteredSlice, volume_le_volume_simonSteinerSymmetrization) compile against the same Mathlib but are outside the import closure of GMT.Ch07.Submission. They serve only as templates, so both children must be proved from Mathlib. Every lemma cited in the child proofs exists at the listed snapshot location and is reachable. Both child types elaborate in the frozen contract scope and pass validate_lean_statement. Complete Lean proofs of both children compile with axioms propext, Classical.choice, Quot.sound, and the byte-identical frozen parent type is derived from them in one `exact`. The names cbr_ci_iso_svol_* are fresh.

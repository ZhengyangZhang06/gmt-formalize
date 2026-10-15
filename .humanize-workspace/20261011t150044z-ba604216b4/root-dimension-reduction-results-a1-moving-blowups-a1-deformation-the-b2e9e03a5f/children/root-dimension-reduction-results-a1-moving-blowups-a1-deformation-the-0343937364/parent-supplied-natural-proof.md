# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.face_regroup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 ("Regrouping") of the parent proof, with the strict-monotonicity remark of its step 1. The statement quantifies over an arbitrary I, so one (s', β') serves every test form; the parent applies it with I(q) := ∫_{Q^m} γ(Φ_q y)(E_q) dy. Purely finite bookkeeping: no analysis and no sibling is used.

Notation. For p = (ι, b) and i ∈ Fin (m+1): front(p, i) := (ι ∘ Fin.succAbove i, b + Pi.single (ι i) 1) and back(p, i) := (ι ∘ Fin.succAbove i, b). These are the parent's q(p, i, 1) and q(p, i, 0). [P] denotes 1 if P holds and 0 otherwise.

1. Choice of s'. Let s' := ⋃_{p ∈ s} ⋃_{i ∈ Fin (m+1)} {front(p, i), back(p, i)} (Finset.biUnion over s and Finset.univ). This is the image of the finite index set 𝒜 = s × Fin (m+1) × {0, 1} under κ(p, i, ε) = q(p, i, ε), as in the parent proof. In particular front(p, i) ∈ s' and back(p, i) ∈ s' for all p ∈ s and all i (Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton).

2. Choice of β'. Let β'(q) := Σ_{p ∈ s} Σ_{i} β_p (−1)^i ([front(p, i) = q] − [back(p, i) = q]) ∈ ℤ. This is the parent's fibre sum Σ_{a ∈ 𝒜, κ a = q} c(a) with c(p, i, ε) = β_p (−1)^i (2ε − 1), written with indicators.

3. Strict monotonicity. Let q ∈ s'. Then q = front(p, i) or q = back(p, i) for some p ∈ s and i, so q.1 = p.1 ∘ Fin.succAbove i. p.1 is strictly increasing by hypothesis and Fin.succAbove i is strictly increasing (Fin.strictMono_succAbove), so q.1 is strictly increasing (StrictMono.comp).

4. Each term picks out its two faces. Fix I, p ∈ s and i. Expanding the indicator difference (mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_sub_distrib), and using Σ_{q ∈ s'} [x = q] f(q) = f(x) for x ∈ s' (Finset.sum_ite_eq) together with step 1, we get Σ_{q ∈ s'} β_p (−1)^i ([front(p, i) = q] − [back(p, i) = q]) I(q) = β_p ((−1)^i (I(front(p, i)) − I(back(p, i)))).

5. Exchange of sums. By Finset.mul_sum and step 4, the left-hand side of the claim equals Σ_{p ∈ s} Σ_i Σ_{q ∈ s'} β_p (−1)^i ([front(p, i) = q] − [back(p, i) = q]) I(q). Exchanging the order of summation (Finset.sum_comm, twice) gives Σ_{q ∈ s'} Σ_{p ∈ s} Σ_i β_p (−1)^i ([front(p, i) = q] − [back(p, i) = q]) I(q). For each q, this inner double sum equals (β'(q) : ℝ) · I(q): the integer cast commutes with sums, products, powers and differences (push_cast, with ((−1 : ℤ)^i : ℝ) = (−1 : ℝ)^i and the cast of an indicator being the real indicator), and I(q) factors out (Finset.sum_mul). Hence Σ_{p ∈ s} β_p Σ_i (−1)^i (I(front(p, i)) − I(back(p, i))) = Σ_{q ∈ s'} β'(q) I(q).

6. Steps 1–5 give s' and β' with the required properties, and neither depends on I. For m = 0 nothing changes: each ι ∘ Fin.succAbove i is the unique map Fin 0 → Fin P, strict monotonicity is vacuous, and all sums are finite. ∎

## Key steps

1. front(p,i) = (ι∘succAbove i, b + 𝟙_{ι(i)}), back(p,i) = (ι∘succAbove i, b); s' := ⋃_{p,i} {front(p,i), back(p,i)}.
2. β'(q) := Σ_{p,i} β_p(−1)^i([front(p,i) = q] − [back(p,i) = q]), the parent's fibre sum.
3. q.1 = ι∘succAbove i is StrictMono (hypothesis, Fin.strictMono_succAbove).
4. For each (p, i) the q-sum over s' picks out its two faces (Finset.sum_ite_eq); exchange sums (Finset.sum_comm) and push the cast through to get Σ_{q∈s'} β'_q I(q).

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD and git -C SNAPSHOT/project rev-parse HEAD (both match the manifest); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'dimred_mbl_dtfrcb' SNAPSHOT/project SNAPSHOT/mathlib/Mathlib lake-packages-25730c7c/simongmt GMT -g '*.lean' (no match, exit 1)`
- `python3 -I scan of RUN/dag.json lean_name fields (2235 nodes, updated 2026-10-14T03:00:34Z): dimred_mbl_dtfrcb_cube_partial_ftc, dimred_mbl_dtfrcb_cube_stokes and dimred_mbl_dtfrcb_face_regroup each occur 0 times. The only *dtfrcb* names are the twin's cmcdtfrcb_cube_partial_ftc (accepted), cmcdtfrcb_cube_stokes (speculative-ready), cmcdtfrcb_face_regroup (accepted at 02:06:25Z, after v1's rejection) and cmcdtfrcb_pullback_divergence. The face_divergence frozen type was read from its node.`
- `rg -n on SNAPSHOT/mathlib/Mathlib: 'theorem volume_preserving_piFinSuccAbove' (MeasureTheory/Constructions/Pi.lean:818), 'theorem integral_eq_sub_of_hasDerivAt ' (MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148), 'theorem integral_prod_symm' (MeasureTheory/Integral/Prod.lean:463), 'theorem MeasurePreserving.setIntegral_preimage_emb' (MeasureTheory/Integral/Bochner/Set.lean:571), 'theorem integral_Ioc_eq_integral_Ioo' (MeasureTheory/Integral/Bochner/Set.lean:709), 'volume_preserving_toLp' (MeasureTheory/Measure/Haar/InnerProductSpace.lean:139), 'trace_eq_sum_inner' (Analysis/InnerProductSpace/Trace.lean:25), 'theorem prod_restrict' (MeasureTheory/Measure/Prod.lean:778), 'theorem Continuous.finInsertNth' (Topology/Constructions.lean:1037), 'forall_iff_succAbove|eq_self_or_eq_succAbove|insertNthEquiv' (Data/Fin/Tuple/Basic.lean:827/841/1065), 'strictMono_succAbove' (Order/Fin/Basic.lean:191)`
- `rg -n "theorem integral_divergence_of_hasFDerivAt_off_countable'" SNAPSHOT/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean (line 296; this module is not imported by the frozen contract)`
- `rg -n 'boundary_apply|exteriorDerivativeTestOn|GeometricCurrentOn|TestFormOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (TestFormOn :123, GeometricCurrentOn :145, exteriorDerivativeTestOn :193, GeometricCurrentOn.boundary_apply :333)`
- `grep/sed of /runtime/flows/gmt-claude-5675b49b7aec/_recursive_lean/runtime.py (_decompose depth gate :1397, _existing_lean_name_problem :6812, _accepted_checkpoint :2414, _reference_use_problem :900) and speculation.py (resolve_accepted_duplicates, keyed by declaration name); swarm-project.json (max_depth 6); verifier/gmt-compare.py (contract_scope, child_modules)`
- `lake env lean /tmp/cbdec-dimred-v2/lean/{Types,Full2,HB50k,SubmissionSim,Names}.lean (run from the project root)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b2e9e03a5f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b2e9e03a5f/decomposition-v1.json`
- `/runtime/flows/gmt-claude-5675b49b7aec/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cbdec-dimred-v2/lean/Types.lean`
- `/tmp/cbdec-dimred-v2/lean/Full2.lean`
- `/tmp/cbdec-dimred-v2/lean/HB50k.lean`
- `/tmp/cbdec-dimred-v2/lean/SubmissionSim.lean`
- `/tmp/cbdec-dimred-v2/lean/Names.lean`

Pins match: snapshot project b4d606db and Mathlib 25730c7c, and Submission.lean is byte-identical to the frozen contract.
No lattice-face current, cubical Stokes or face-regrouping lemma exists under the frozen imports, in the snapshot project, Mathlib or SimonGMT. Mathlib's box divergence theorem (integral_divergence_of_hasFDerivAt_off_countable', DivergenceTheorem.lean:296) lives in a module the contract does not import. So the cube identity is proved from Fubini and the one-variable FTC. The Fubini side uses integral_prod_symm, Measure.prod_restrict, volume_preserving_piFinSuccAbove, PiLp.volume_preserving_toLp and MeasurePreserving.setIntegral_preimage_emb; the FTC side uses intervalIntegral.integral_eq_sub_of_hasDerivAt. All are present in the pinned snapshot.
The twin branch's cmcdtfrcb_cube_partial_ftc and cmcdtfrcb_face_regroup have byte-identical types, but per the correction nothing is reused. The three children get the fresh names dimred_mbl_dtfrcb_cube_partial_ftc, dimred_mbl_dtfrcb_cube_stokes and dimred_mbl_dtfrcb_face_regroup, which occur nowhere in dag.json, the snapshot, Mathlib, SimonGMT or GMT/.
Every cited Mathlib and SimonGMT name resolves under import GMT.Ch07.Submission.
In the comparator scope, the three child types and the selected type elaborate. Each child is proved as a single theorem using only [propext, Classical.choice, Quot.sound], within 50k heartbeats. The parent's exact frozen type follows from the children plus face_divergence's frozen type; its only sorryAx is the face_divergence stand-in. This also holds when everything is inserted in place into a copy of Submission.lean.

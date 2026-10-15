# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.skeleton_deformation-a1.good_radius-a1.slice_liminf-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the supplied proof of the selected node dimred_mbl_dtsd_good_radius, for one finite measure. The argument never uses the structure of ℝ^P, so it is stated for an arbitrary measurable space α; the parent applies it with α = ℝ^P (Euclid P), once to μ and once to μ'. The book source is Simon, Introduction to GMT, Ch. 6. The remark after 4.9 (book/chapter-06.txt lines 1361–1375) says that t ↦ M_W(T⌞{f < t}) is increasing, hence differentiable for L¹-a.e. t, and 4.9 controls slice masses by liminf_{h↓0} h⁻¹·M_W(T⌞{t − h < f < t}). The proof of 5.1, (8)–(10) (lines 1725–1734) uses this to choose the slicing radius. Throughout, ofReal := ENNReal.ofReal, A_s := {x ∈ α : f(x) < s} for s ∈ ℝ, and F(s) := (μ(A_s)).toReal. So F is exactly the function fun s : ℝ => (μ {x | f x < s}).toReal of the statement, and the hypothesis says F is differentiable at t.

1. (Finite values of the distribution function.) For each s ∈ ℝ the set A_s is measurable, because f and the constant s are measurable (measurableSet_lt hf measurable_const). Since μ is a finite measure, μ(A_s) ≠ ∞ (measure_ne_top). Hence μ(A_s) = ofReal(F(s)) (ENNReal.ofReal_toReal) and F(s) ≥ 0 (ENNReal.toReal_nonneg).

2. (Slice bound.) Fix h > 0. If f(x) < t − h then f(x) < t, so A_{t−h} ⊆ A_t. If t − h < f(x) < t, then x ∈ A_t and x ∉ A_{t−h}, because f(x) < t − h would contradict t − h < f(x). Hence {x : t − h < f(x) < t} ⊆ A_t \ A_{t−h}. Apply monotonicity of μ (measure_mono) and measure_sdiff. The latter applies because A_{t−h} ⊆ A_t, A_{t−h} is measurable (hence null-measurable), and μ(A_{t−h}) ≠ ∞. This gives
   μ({t − h < f < t}) ≤ μ(A_t \ A_{t−h}) = μ(A_t) − μ(A_{t−h}) = ofReal(F(t)) − ofReal(F(t − h)) = ofReal(F(t) − F(t − h)).
   The last two equalities use step 1 and ENNReal.ofReal_sub, which is valid because F(t − h) ≥ 0. Multiplying both sides by ofReal(h⁻¹) preserves the inequality in [0, ∞] (monotonicity of multiplication, e.g. gcongr). So for every h > 0,
   ofReal(h⁻¹)·μ({t − h < f < t}) ≤ ofReal(h⁻¹)·ofReal(F(t) − F(t − h)).

3. (Comparison of the liminfs.) The set (0, ∞) belongs to the filter 𝓝[>] 0 (self_mem_nhdsWithin), so the inequality of step 2 holds eventually along 𝓝[>] 0. In the complete lattice [0, ∞], liminf is monotone under eventual inequality, with no boundedness side conditions (Filter.liminf_le_liminf; its boundedness arguments are discharged automatically in a complete lattice). Hence
   liminf_{h→0+} ofReal(h⁻¹)·μ({t − h < f < t}) ≤ liminf_{h→0+} ofReal(h⁻¹)·ofReal(F(t) − F(t − h)).

4. (Left slopes at a point of differentiability.) F is differentiable at t by hypothesis. The sibling cbr_smm_liminf_left_slope_le_deriv (key left_slope), applied to F and t, gives
   liminf_{h→0+} ofReal(h⁻¹)·ofReal(F(t) − F(t − h)) ≤ ofReal(deriv F t).
   This is step 3 of the selected node's supplied proof. The left quotients h⁻¹(F(t) − F(t − h)) tend to F′(t) as h ↓ 0, and for h > 0 the product equals ofReal(h⁻¹(F(t) − F(t − h))), which tends to ofReal(F′(t)).

5. (Conclusion.) Chaining steps 3 and 4 gives liminf_{h→0+} ofReal(h⁻¹)·μ({x : t − h < f(x) < t}) ≤ ofReal(deriv F t). This is the claim, because F is literally fun s : ℝ => (μ {x | f x < s}).toReal. ∎

## Key steps

1. A_s := {f < s} is measurable and μ(A_s) = ofReal(F(s)) with F(s) = (μ A_s).toReal ≥ 0 (finite measure).
2. For h > 0: {t − h < f < t} ⊆ A_t \ A_{t−h}, so μ({t − h < f < t}) ≤ μ(A_t) − μ(A_{t−h}) = ofReal(F(t) − F(t − h)) (measure_sdiff, ENNReal.ofReal_sub); multiply by ofReal(h⁻¹).
3. The bound holds eventually along 𝓝[>] 0, so the liminfs compare (Filter.liminf_le_liminf in [0, ∞]).
4. The sibling cbr_smm_liminf_left_slope_le_deriv bounds liminf ofReal(h⁻¹)·ofReal(F(t) − F(t − h)) by ofReal(deriv F t).

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (mode local-project; project_commit b4d606db1, mathlib_commit 25730c7c); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d); git log -1 and git status of the workspace (HEAD b4d606db1, clean)`
- `python3 -I comparison of this node's parent-child-handoff.json with the handoff of the twin node cmcsd_good_radius (nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940): key, title, statement, lean_statement, depends_on, natural_proof and proof_key_steps byte-identical (only lean_name differs)`
- `python3 -I scans of RUN/dag.json (2130 nodes at 01:21Z, re-run on 2194 nodes at 2026-10-14T01:55Z): exactly two nodes carry the selected frozen type (this node and the twin cmcsd_good_radius, status waiting-children); the twin's children cmcsd_gr_liminf_slice_le_deriv and cmcsd_gr_exists_deriv_le_off_null are both rlcr-lean, not accepted checkpoints, so their names cannot be shared; the two reused declarations (keys lebesgue_deriv and left_slope) are status accepted with candidate commits 6efe397f and 9e4623f7, and their DAG lean_statements are byte-identical to the child types given here`
- `sed of the twin's decomposition-v1.json and decomposition-audit-v1.json (split passed, no required changes) and of its children's no-split decisions (nodes/...-ske-8c04a2bb5d and nodes/...-ske-c45cc6258b, decomposition-v1.json)`
- `python3 -I scan of RUN/dag.json lean_name and theorems fields for the prefix dimred_mbl_dtsd_gr_ (no match); rg -n -l dimred_mbl_dtsd_gr_ over SNAPSHOT/project, SNAPSHOT/mathlib/Mathlib, lake-packages-25730c7c/simongmt/Poincare and GMT/Ch07 (no match)`
- `rg -n over SNAPSHOT/mathlib/Mathlib: theorem measure_sdiff, measure_sdiff_null, measure_union_null, measure_mono_null, measurableSet_lt, ENNReal ofReal_sub, ofReal_toReal, ofReal_lt_top, mul_top, le_inv_iff_mul_le, ofReal_inv_of_pos, ofReal_le_ofReal_iff, Real volume_Ioo, measurable_deriv, Measurable.ennreal_ofReal, lintegral_eq_zero_iff, mul_meas_ge_le_lintegral₀, restrict_apply', nonempty_of_measure_ne_zero, Monotone.ae_differentiableAt, HasDerivAt.tendsto_slope_zero_left, Filter.Tendsto.liminf_eq, limsup_le_limsup with @[to_dual] (generating Filter.liminf_le_liminf), exists_notMem_null_le_laverage (all found)`
- `git show 6efe397f182ee5f93e5be9c4b09eb298c3f56ad8:GMT/Ch07/Submission.lean and git show 9e4623f7949b6e8a31421369c9b6bcbc190d2c41:GMT/Ch07/Submission.lean; git diff --stat b4d606db1 against each (each adds only its one declaration, header unchanged); python3 -I extraction of both declarations verbatim into SCRATCH/FullCheck.lean`
- `grep/sed of /runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean: runtime.py (_decompose, _existing_lean_name_problem, _accepted_checkpoint, child activation by lean_name, _install_parent_supplied_child_handoff, _render_parent_supplied_natural, _install_speculative_assumptions, _inherited_prerequisites), inherited.py (cited, cited_inherited), leaf_verification.py (check_source_delta: a leaf may append only its own declaration), prompts.py (DECOMPOSE); verifier/gmt-compare.py (child_contract, contract_scope, child_modules)`
- `lean (toolchain v4.35.0-rc3, pinned LEAN_PATH of env.sh) on SCRATCH/Types.lean, AssemblyAx.lean, FullCheck.lean, SpecStub.lean, InstCheck.lean, ComparatorStyle.lean and chal/Challenge_*.lean (all exit 0; only sorry warnings in Types and the challenges)`
- `python3 -I validate_lean_statement of verifier/lean_contract.py and of the runtime _recursive_lean/lean_contract.py on the four child types and the selected type (accepted unchanged); python3 -I emulation of the runtime's _existing_lean_name_problem, _dependency_problem and inherited.cited_inherited on this output (no collision, acyclic, no ancestor prerequisite cited by a new child's rendered proof file)`
- `grep -n and sed -n 1355,1380p and 1718,1740p of book/chapter-06.txt (Simon 4.9, remark before 4.10, 4.10; proof of 5.1 displays (8)–(10))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-725bd6e6ba/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8ab327b940/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-8c04a2bb5d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-c45cc6258b/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_good_radius_decomposition/FullCheck.lean`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/inherited.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-6c9908f72f7f/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/FullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/SpecStub.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/InstCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/ComparatorStyle.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/chal/Challenge_dimred_mbl_dtsd_gr_liminf_slice_le_deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/dimred_mbl_dtsd_good_radius_decomposition/chal/Challenge_dimred_mbl_dtsd_gr_exists_deriv_le_off_null.lean`

Pins match (project b4d606db1, Mathlib 25730c7c), and the workspace is clean at the frozen commit. The selected node's supplied proof, statement and frozen type are byte-identical to those of the twin node cmcsd_good_radius. That twin's split into slice_liminf and markov_point, plus two reused accepted declarations, passed its independent audit with no required changes, and both of its new children were later judged atomic. Those twin children are not yet accepted, so this split mirrors them with byte-identical frozen types under the fresh, collision-free names dimred_mbl_dtsd_gr_liminf_slice_le_deriv and dimred_mbl_dtsd_gr_exists_deriv_le_off_null. It reuses the two accepted declarations (keys lebesgue_deriv and left_slope) with types identical to their DAG nodes. Mathlib at the pinned snapshot supplies every lemma the child proofs cite; the snapshot project has no other relevant declaration. Compilation evidence (all exit 0): every type elaborates after import GMT.Ch07.Submission in the contract scope and in the comparator's generated challenge form. The new types also elaborate in the runtime's speculative stub layout outside namespace GMT.Ch07. The selected frozen type is proved from the two new children with axioms propext, Classical.choice and Quot.sound plus the two stubs. Complete proofs of all four children and of the selected type use only propext, Classical.choice and Quot.sound. The pp.explicit check shows volume = Real.measureSpace Lebesgue measure, real ⁻¹ and /, and the synthesized MeasurableSpace instance at α = Euclid P. No new child's rendered proof file cites an ancestor dependency by Lean name.

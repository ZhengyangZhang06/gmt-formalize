# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.support_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the support facts listed in the notation paragraph of the parent's supplied proof ("spt(A − B) ⊆ spt A ∪ spt B; spt ∂A ⊆ spt A; spt 0 = ∅; a current that vanishes on every test form whose support is disjoint from a closed set E has support in E (every x ∉ E has a ball with compact closure disjoint from E)"), proved directly from Simon's definition 6.2.11 (no use of the partition-of-unity fact (VO) is needed).

Notation: for X ∈ 𝒟_n(ℝ^P), x ∉ spt X ⟺ x ∈ X.zeroRegion ⟺ there is W with x ∈ W, W open, closure W compact, closure W ⊆ univ, and X.VanishesOn W (∀ ω, tsupport ω ⊆ W → X(ω) = 0); call such W a zero neighbourhood of x for X. Since ℝ^P is a proper metric space, for every x and ε > 0 the ball W = ball x ε is open with closure W ⊆ closedBall x ε (closure_ball_subset_closedBall), a compact set (isCompact_closedBall), so closure W is compact (IsCompact.of_isClosed_subset with isClosed_closure); trivially closure W ⊆ univ.

1. (i) Let E be closed and X vanish on all test forms whose tsupport is disjoint from E. Let x ∈ spt X and suppose x ∉ E. As Eᶜ is open, there is ε > 0 with ball x ε ⊆ Eᶜ (Metric.isOpen_iff). Put W := ball x ε. It is open with compact closure (notation paragraph). If tsupport ω ⊆ W then tsupport ω ⊆ Eᶜ, i.e. Disjoint (tsupport ω) E, so X(ω) = 0 by hypothesis. Hence W is a zero neighbourhood of x and x ∈ X.zeroRegion, contradicting x ∈ spt X. Therefore x ∈ E, i.e. spt X ⊆ E.
2. (ii) spt X = univ \ X.zeroRegion = (X.zeroRegion)ᶜ and X.zeroRegion is open, being a union of open sets (GeometricCurrentOn.isOpen_zeroRegion). Hence spt X is closed (IsOpen.isClosed_compl).
3. (iii) Let x ∉ spt A ∪ spt B, with zero neighbourhoods W_A of x for A and W_B of x for B. Put W := W_A ∩ W_B: it is open and contains x; closure W ⊆ closure W_A (closure_mono), so closure W is a closed subset of a compact set, hence compact; closure W ⊆ univ. If tsupport ω ⊆ W, then tsupport ω ⊆ W_A and tsupport ω ⊆ W_B, so A(ω) = 0 and B(ω) = 0, and (A − B)(ω) = A(ω) − B(ω) = 0. So W is a zero neighbourhood of x for A − B, and x ∉ spt(A − B). Contrapositively spt(A − B) ⊆ spt A ∪ spt B.
4. (iv) For every x, W := ball x 1 is open with compact closure, and the zero current vanishes on every test form (GeometricCurrentOn.zero_apply), in particular on W. So every x lies in the zero region of 0, and spt 0 = ∅.
5. (v) Let A ∈ 𝒟_{n+1}(ℝ^P) and x ∉ spt A, with a zero neighbourhood W of x for A. Let η ∈ 𝒟ⁿ(ℝ^P) with tsupport η ⊆ W. Then ∂A(η) = A(dη) (GeometricCurrentOn.boundary_apply), where the form underlying dη is exteriorDerivative η and tsupport (exteriorDerivative η) ⊆ tsupport η ⊆ W (tsupport_exteriorDerivative_subset). Hence A(dη) = 0, i.e. ∂A vanishes on W, W is a zero neighbourhood of x for ∂A, and x ∉ spt ∂A. So spt ∂A ⊆ spt A. ∎

## Key steps

1. Points off spt X are exactly the points with an open neighbourhood of compact closure on which X vanishes; small balls are such neighbourhoods in the proper space ℝ^P.
2. (i) For x ∉ E (closed), a ball around x inside Eᶜ is a zero neighbourhood, so spt X ⊆ E; (ii) spt X is the complement of the open zero region.
3. (iii) Intersect zero neighbourhoods of A and B; (iv) every ball is a zero neighbourhood of 0; (v) tsupport dη ⊆ tsupport η, so zero neighbourhoods of A are zero neighbourhoods of ∂A.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n -i 'deformation|skeleton|telescop' project/GMT -g '*.lean'`
- `rg -n 'theorem LipschitzOnWith.extend_real|theorem LipschitzOnWith.extend_pi' mathlib/Mathlib`
- `rg -n 'theorem Monotone.ae_differentiableAt|theorem measurable_deriv|theorem hasDerivAt_iff_tendsto_slope_zero|theorem HasDerivAt.tendsto_slope_zero_left|theorem mul_meas_ge_le_lintegral₀|theorem enorm_integral_le_lintegral_enorm|theorem ENNReal.tsum_geometric|theorem isClosedEmbedding_coe_real|theorem lipschitz_infDist_pt|theorem isClosed_cthickening' mathlib/Mathlib`
- `rg -n 'cmcsd_' over the snapshot project, mathlib and lake-packages-25730c7c/simongmt (no match)`
- `rg -n 'theorem countablyRectifiable_of_measure_zero|theorem GeometricCurrentOn.isOpen_zeroRegion|theorem tsupport_exteriorDerivative_subset' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json (961 nodes): frozen types of the selected node and of siblings RET/GC/PF/IMS, accepted reusable declarations (support, mass, IMRep, Lebesgue-derivative lemmas), name collisions for the cmcsd_ prefix (none)`
- `git show ae810e9b / 7a706164 / ea5c1199 / 6efe397f (accepted proofs of lcmp_imRep_measure_restrict, cmr_abs_apply_le_massOn, cmc_fc_cs_massOn_sub_le, cmcs_smi_lintegral_ofReal_deriv_le)`
- `lean Types.lean (16 stub types elaborate); lean InstCheck.lean (coercions, rfl checks); lean AssemblyAx.lean (selected type from stubs; axioms propext, Classical.choice, Quot.sound + named stubs); lean ReusedCheck.lean (reused proofs, standard axioms); lean Probe3/Probe4.lean (lemma names: measure_sdiff, setIntegral_sdiff, image_eq_zero_of_notMem_tsupport)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-9a64d46574/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/Types.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/AssemblyAx.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcsd_skeleton_deformation_decomposition/ReusedCheck.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace Contract.lean and Submission.lean. Its only deformation-theorem material is the separate, unsolved Ch06 specification (project/GMT/Ch06/Contract.lean, DeformationTheorem with IsLatticeChain/Eucl). Those types are incompatible with Ch07, so nothing there is reusable. Mathlib supplies every tool the child proofs cite: LipschitzOnWith.extend_real/extend_pi (McShane), Monotone.ae_differentiableAt, measurable_deriv, HasDerivAt.tendsto_slope_zero_left, Markov (mul_meas_ge_le_lintegral₀), enorm_integral_le_lintegral_enorm, ENNReal.tsum_geometric, lipschitz_infDist_pt, isClosed_cthickening and Int.isClosedEmbedding_coe_real. SimonGMT supplies countablyRectifiable_of_measure_zero, isOpen_zeroRegion and tsupport_exteriorDerivative_subset. The DAG yields four accepted, reusable declarations with identical types: cmcs_smi_lintegral_ofReal_deriv_le, cmc_fc_cs_massOn_sub_le, cmr_abs_apply_le_massOn and lcmp_imRep_measure_restrict. Their proofs recompile with standard axioms. The prefix cmcsd_ has no match anywhere. All child types elaborate, and the assembly of the selected frozen type from the sibling and child types compiles with only propext, Classical.choice and Quot.sound beyond the named stubs.

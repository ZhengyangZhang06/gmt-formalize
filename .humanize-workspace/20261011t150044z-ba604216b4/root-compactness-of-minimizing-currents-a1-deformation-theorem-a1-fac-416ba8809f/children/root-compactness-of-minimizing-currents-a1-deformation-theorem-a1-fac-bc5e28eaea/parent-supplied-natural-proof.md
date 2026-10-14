# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.cube_partial_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof (“Divergence theorem on the unit cube … Equivalently: for each i, Fubini in the other m coordinates and the fundamental theorem of calculus in the i-th coordinate”), specialised to a single coordinate i and a single C¹ function G. Mathlib's box divergence theorem is in Mathlib.MeasureTheory.Integral.DivergenceTheorem, which the frozen Ch07 contract does NOT import, and a leaf may not add imports. So the parent's parenthetical Fubini + FTC route is the one written out here. Every tool below is reachable from the frozen imports.

Notation. For d ∈ ℕ, Q^d := {y ∈ Euclid d | ∀ j, 0 < y j ∧ y j < 1}, and B^d := Set.pi univ (fun _ => Ioo 0 1) ⊆ (Fin d → ℝ) is the open box. e_i := EuclideanSpace.single i 1. For c ∈ ℝ and z : Fin k → ℝ, insertNth i c z : Fin (k+1) → ℝ has i-th coordinate c and (succAbove i l)-th coordinate z l. toLp = WithLp.toLp 2 and ofLp = WithLp.ofLp are mutually inverse, and (toLp x) j = x j.

1. Regularity. G is C¹, so G is differentiable everywhere (ContDiff.differentiable, 1 ≠ 0) and y ↦ fderiv ℝ G y is continuous (ContDiff.continuous_fderiv). Hence g(y) := fderiv ℝ G y e_i is continuous on Euclid (k+1).
2. Integrability (first conjunct). Q^{k+1} ⊆ toLp '' Icc 0 1, because y = toLp (ofLp y) and 0 ≤ y j ≤ 1. toLp '' Icc 0 1 is compact: it is the image of the compact box Icc 0 1 under the continuous map toLp. A continuous function is integrable on a compact set (ContinuousOn.integrableOn_compact), hence on the subset Q^{k+1} (IntegrableOn.mono_set).
3. Transport to coordinates. For every n and every f : Euclid n → ℝ, ∫_{Q^n} f = ∫_{B^n} f(toLp x) dx. Indeed toLp : (Fin n → ℝ) → Euclid n is a measure-preserving (PiLp.volume_preserving_toLp) measurable embedding (MeasurableEquiv.toLp), and toLp ⁻¹' Q^n = B^n, so MeasurePreserving.setIntegral_preimage_emb applies. Apply this to the three integrals of the claim. Using ofLp (toLp z) = z, the claim becomes
   ∫_{B^{k+1}} g(toLp x) dx = ∫_{B^k} G(toLp(insertNth i 1 z)) dz − ∫_{B^k} G(toLp(insertNth i 0 z)) dz.
4. Splitting off coordinate i. Let e := MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i : (Fin (k+1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ). Its inverse is (t, z) ↦ insertNth i t z (piFinSuccAbove_symm_apply, Fin.insertNthEquiv), and e.symm is measure-preserving (volume_preserving_piFinSuccAbove, .symm). Moreover e.symm ⁻¹' B^{k+1} = Ioo 0 1 ×ˢ B^k: insertNth i t z lies in the box iff t ∈ (0,1) and every z l ∈ (0,1) (Fin.forall_iff_succAbove). So ∫_{B^{k+1}} g(toLp x) dx = ∫_{Ioo 0 1 ×ˢ B^k} h, where h(t, z) := g(toLp(insertNth i t z)) and the measure is volume = volume.prod volume.
5. Fubini. h is continuous on ℝ × (Fin k → ℝ) (Continuous.finInsertNth, continuity of toLp and of g). Hence h is integrable on the compact set Icc 0 1 ×ˢ Icc 0 1, and therefore on Ioo 0 1 ×ˢ B^k. By Measure.prod_restrict, (volume.prod volume).restrict (Ioo 0 1 ×ˢ B^k) = (volume.restrict (Ioo 0 1)).prod (volume.restrict B^k), so h is integrable for this product measure. Fubini with the second factor outside (integral_prod_symm) gives ∫_{Ioo 0 1 ×ˢ B^k} h = ∫_{z ∈ B^k} (∫_{t ∈ Ioo 0 1} h(t, z) dt) dz.
6. FTC in the i-th coordinate. Fix z and put φ(t) := G(toLp(insertNth i t z)). Then toLp(insertNth i t z) = toLp(insertNth i 0 z) + t • e_i. Check coordinates: at i both sides equal t; at succAbove i l both equal z l, since e_i vanishes there (Fin.succAbove_ne). So t ↦ toLp(insertNth i t z) has derivative e_i, and by the chain rule φ'(t) = fderiv ℝ G (toLp(insertNth i t z)) e_i = h(t, z). This is continuous in t, hence interval integrable, and intervalIntegral.integral_eq_sub_of_hasDerivAt gives ∫_0^1 h(t, z) dt = φ(1) − φ(0). Since 0 ≤ 1, the interval integral is the integral over Ioc 0 1 (intervalIntegral.integral_of_le). That equals the integral over Ioo 0 1 (integral_Ioc_eq_integral_Ioo; singletons are null). So ∫_{t ∈ Ioo 0 1} h(t, z) dt = G(toLp(insertNth i 1 z)) − G(toLp(insertNth i 0 z)).
7. Conclusion. For c ∈ {0, 1}, z ↦ G(toLp(insertNth i c z)) is continuous, hence integrable on Icc 0 1 ⊇ B^k. By integral_sub, ∫_{B^k} G(toLp(insertNth i 1 z)) dz − ∫_{B^k} G(toLp(insertNth i 0 z)) dz = ∫_{B^k} (G(toLp(insertNth i 1 z)) − G(toLp(insertNth i 0 z))) dz. By step 6 and setIntegral_congr_fun (B^k is measurable), this equals ∫_{z ∈ B^k} ∫_{t ∈ Ioo 0 1} h(t, z) dt dz. By steps 3–5, that is the transported left-hand side. This proves the second conjunct.
   For k = 0, Fin 0 → ℝ is a single point and B^0 is all of it, so every step applies verbatim. ∎

## Key steps

1. G ∈ C¹, so g = DG(·)e_i is continuous. Q^{k+1} lies in the compact set toLp '' [0,1]^{k+1}, so g is integrable on Q^{k+1}.
2. Transport the three cube integrals to open boxes in Fin d → ℝ with the measure-preserving embedding toLp (PiLp.volume_preserving_toLp).
3. Split off coordinate i with the measure-preserving map (t, z) ↦ insertNth i t z (volume_preserving_piFinSuccAbove). The box pulls back to Ioo 0 1 ×ˢ B^k.
4. Fubini (Measure.prod_restrict, integral_prod_symm) for the continuous integrand, with the integral over t inside.
5. FTC in t: toLp(insertNth i t z) = toLp(insertNth i 0 z) + t e_i, so d/dt G(…) = DG(…)e_i and ∫_{(0,1)} = G(…1…) − G(…0…).
6. Recombine with integral_sub (continuous integrands on the compact closure) to get the face difference.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); manifest.json project_commit b4d606db1…, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d`
- `rg -n 'cmcdtfrcb' project mathlib/Mathlib -g '*.lean' (exit 1, no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name for cmcdtfrcb|cube_divergence|cube_stokes|face_regroup|regroup|cubical (0 hits); 'divergence'/'stokes' hits inspected (cmr_coordinate_divergence_form, codim1_rdo_dg_vdl_integral_divergence_eq_zero, cbr_cipi_plane_halfspace_stokes, …): none has an identical type`
- `rg -n -i 'IsLatticeChain|latticeFace|LatticeFaceIndex' project/GMT -g '*.lean' (only Ch06/Submission.lean, separate module); rg -n -i 'cube|stokes|divergence' project/GMT -g '*.lean' (only tangentialDivergence defs); rg -n -i 'integral_divergence|divergence theorem|insertNth|unit cube|cube' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (no cube Stokes/divergence lemma)`
- `grep -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean (lines 266, 296, 313); lake env lean probe under import GMT.Ch07.Submission: Unknown identifier integral_divergence_of_hasFDerivAt_off_countable' and BoxIntegral.Box (module outside the frozen import closure)`
- `grep -rn 'volume_preserving_ofLp|volume_preserving_toLp|univ_pi_Ioo_ae_eq_Icc|strictMono_succAbove|prod_fiberwise_of_maps_to|continuousAlternatingMap_apply|def removeNth|def insertNthEquiv|setIntegral_preimage_emb' mathlib/Mathlib`
- `lake env lean Avail.lean/Avail2.lean probes: intervalIntegral.integral_eq_sub_of_hasDerivAt, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo, integral_prod_symm, Measure.prod_restrict, volume_preserving_piFinSuccAbove, MeasurableEquiv.piFinSuccAbove_symm_apply, Continuous.finInsertNth, HasFDerivAt.continuousAlternatingMap_apply_const, ContinuousAlternatingMap.apply, Finset.sum_fiberwise_of_maps_to, Fin.sum_univ_succAbove all available; Fin.insertNthEquiv_apply is pointwise (rfl used instead)`
- `git show 14cdd14d8 / fa0865963 (leaf gate: 'leaf proof must preserve the complete frozen base byte-for-byte', no imports/helpers); git show 84d5ca9d5:GMT/Ch07/Submission.lean (proof base = contract imports only, 457 lines); python3 scan of .humanize/swarm-configs (max_nodes 5000, max_depth 6)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') → replayed scope; lake env lean /tmp/cbsplit-k7q2/lean/Node{A1,B1,B,C,Parent}.lean (all four child types and the parent type elaborate)`
- `lake env lean /tmp/cbsplit-k7q2/lean/Assembly.lean (frozen cube_stokes + face_regroup types ⇒ selected frozen type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cbsplit-k7q2/lean/Combined.lean (each child proved as ONE theorem under base imports; parent assembled; exact Submission.X comparator-style checks; no errors; standard axioms only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-416ba8809f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/tmp/cbsplit-k7q2/lean/Combined.lean`
- `/tmp/cbsplit-k7q2/lean/Assembly.lean`
- `/tmp/cbsplit-k7q2/lean/ValidA1.lean`
- `/tmp/cbsplit-k7q2/lean/ValidB1.lean`
- `/tmp/cbsplit-k7q2/lean/ValidB.lean`
- `/tmp/cbsplit-k7q2/lean/ValidC.lean`
- `/tmp/cbsplit-k7q2/lean/Avail.lean`
- `/tmp/cbsplit-k7q2/lean/Avail2.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. No local declaration gives cubical Stokes, a cube divergence identity, or face regrouping. The Ch06 lattice-chain definitions live in a separate module and come with no proofs. No accepted DAG node has an identical type to reuse. Mathlib's box divergence theorem (DivergenceTheorem.lean, lines 266–313) exists in the snapshot but is NOT reachable from the frozen Ch07 imports, and leaves may not add imports. So the cube identity is split per coordinate and proved with reachable tools: PiLp.volume_preserving_toLp, volume_preserving_piFinSuccAbove, Measure.prod_restrict, integral_prod_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt, ContinuousAlternatingMap.apply and SimonGMT exteriorDerivative_apply. Lean checks under `import GMT.Ch07.Submission` alone pass: all four children are proved as single theorems, and the parent is assembled from cube_stokes and face_regroup, using only standard axioms. The prefix cmcdtfrcb_ collides with nothing.

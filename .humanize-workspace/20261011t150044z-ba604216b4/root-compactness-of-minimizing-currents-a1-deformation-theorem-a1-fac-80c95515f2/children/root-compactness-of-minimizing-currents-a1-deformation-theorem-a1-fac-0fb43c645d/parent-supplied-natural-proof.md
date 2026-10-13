# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.face_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 8, 10, 11 and 12 of the parent proof restricted to one face (Simon Ch. 6, proof of 5.1, display (33): Q⌞F̆ is an integer density on the face F̆), with the face orientation of step 9 supplied by the sibling child coordinate_plane_orientation_sign.

Notation: Hⁿ := μHE[n]; Φ := Φ_p; e_i = EuclideanSpace.single i 1; c := WithLp.toLp 2 (fun i => (b i : ℝ)); vol := Lebesgue measure (volume) on Euclid n.

1. (Measurability.) Q₁ = ⋂_i ({y : 0 < y_i} ∩ {y : y_i < 1}) is Borel, the coordinate maps y ↦ y_i being continuous (EuclideanSpace.proj). Φ is an isometry, hence a closed embedding (Isometry.isClosedEmbedding) and therefore a measurable embedding (IsClosedEmbedding.measurableEmbedding). So F̆ = Φ(Q₁) is Borel (MeasurableEmbedding.measurableSet_image'), and so is M ∩ F̆.
2. (F̆ lies in a coordinate plane.) For a = Φ(y) and an index i with ι(j) ≠ i for all j, a_i = b_i + Σ_j y_j·(e_{ι(j)})_i = b_i + 0 = c_i (Pi.single_apply).
3. (Orientation sign.) Apply the sibling child coordinate_plane_orientation_sign (the antecedents (IMC-b) and (PO) are those of this statement) to P, n, U := univ (open), R, ι, c, E := F̆, using ι strictly increasing, F̆ Borel (step 1) and step 2. It gives a Borel σ : ℝ^P → ℤ with |σ| ≤ 1 such that for Hⁿ⌞(M ∩ F̆)-a.e. x: ξ(x)(α) = σ(x)·α(E_p) for every α.
4. (Change of variables.) Hⁿ = vol on Euclid n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and Φ is an isometry, so map Φ vol = Hⁿ⌞(range Φ) (Isometry.map_euclideanHausdorffMeasure). Since F̆ ⊆ range Φ and Φ⁻¹(F̆) = Q₁ (Φ injective):
   Hⁿ⌞F̆ = (Hⁿ⌞range Φ)⌞F̆ = (map Φ vol)⌞F̆ = map Φ (vol⌞Q₁)
   (Measure.restrict_restrict_of_subset, MeasurableEmbedding.restrict_map, Function.Injective.preimage_image). Hence for every f : ℝ^P → ℝ, ∫_{F̆} f dHⁿ = ∫_{Q₁} f(Φ(y)) dy (MeasurableEmbedding.integral_map), and for every f : ℝ^P → [0, ∞], ∫⁻_{F̆} f dHⁿ = ∫⁻_{Q₁} f(Φ(y)) dy (MeasurableEmbedding.lintegral_map). Neither identity needs measurability or integrability of f.
5. (The density.) Let g := M.indicator (x ↦ θ(x)·σ(x)), h := M.indicator (x ↦ θ(x)) (real valued) and u(y) := g(Φ(y)).
   (a) g is Borel: θ is measurable, every map out of ℕ or ℤ is measurable (so the casts to ℝ are measurable), σ is Borel and M is Borel (Measurable.indicator). Φ is continuous, so u is Borel.
   (b) u(y) ∈ ℤ for every y: u(y) = θ(Φ(y))·σ(Φ(y)) ∈ ℤ if Φ(y) ∈ M, and u(y) = 0 otherwise.
   (c) |g(x)| ≤ h(x) for every x: for x ∈ M, |θ(x)σ(x)| = θ(x)|σ(x)| ≤ θ(x) since θ ≥ 0 and |σ| ≤ 1; for x ∉ M both sides are 0.
6. (Face mass.) ofReal ∘ h = M.indicator (x ↦ (θ(x) : [0,∞])). Hence ∫⁻_{F̆} ofReal(h) dHⁿ = ∫⁻_{M ∩ F̆} θ dHⁿ = ((Hⁿ⌞M).withDensity θ)(F̆) = R.measure(F̆) (lintegral_indicator, Measure.restrict_restrict, withDensity_apply with F̆ Borel, IMRep.measure).
7. (Finiteness.) C := WithLp.toLp 2 '' (∏_i [0,1]) is compact (isCompact_univ_pi, isCompact_Icc, continuity of WithLp.toLp), K := Φ(C) is compact (Φ continuous) and Borel, and F̆ ⊆ K (y = WithLp.toLp 2 (WithLp.ofLp y) with WithLp.ofLp y ∈ ∏_i [0,1]). So R.measure(F̆) ≤ R.measure(K) = ∫⁻_{M ∩ K} θ dHⁿ ≠ ∞ by R.locallyIntegrable_mult K (K compact, K ⊆ univ).
8. (Integrability and the mass bound.) ‖u(y)‖ₑ = ofReal|u(y)| ≤ ofReal(h(Φ(y))) by 5(c), so ∫⁻_{Q₁} ‖u‖ₑ ≤ ∫⁻_{Q₁} ofReal(h ∘ Φ) = ∫⁻_{F̆} ofReal(h) dHⁿ = R.measure(F̆) < ∞ (steps 4, 6, 7). With 5(a), u is integrable on Q₁. Then |u| is integrable on Q₁ and nonnegative, so ofReal(∫_{Q₁} |u|) = ∫⁻_{Q₁} ofReal|u| (ofReal_integral_eq_lintegral_ofReal) ≤ ∫⁻_{Q₁} ofReal(h ∘ Φ) = R.measure(F̆).
9. (The integral identity.) Fix a test form ω and write ω_p(x) := ω(x)(E_p).
   (a) By step 3 and ae_restrict_iff' (M ∩ F̆ Borel), for Hⁿ-a.e. x with x ∈ M ∩ F̆: θ(x)·ξ(x)(ω(x)) = θ(x)·σ(x)·ω_p(x) = g(x)·ω_p(x), using g(x) = θ(x)σ(x) for x ∈ M. Hence ∫_{M ∩ F̆} θ ξ(ω) dHⁿ = ∫_{M ∩ F̆} g·ω_p dHⁿ (setIntegral_congr_ae).
   (b) g·ω_p vanishes on F̆ ∖ (M ∩ F̆) since g = 0 off M; as F̆ is Borel and M ∩ F̆ ⊆ F̆, ∫_{M ∩ F̆} g·ω_p dHⁿ = ∫_{F̆} g·ω_p dHⁿ (setIntegral_eq_of_subset_of_forall_diff_eq_zero).
   (c) By step 4, ∫_{F̆} g·ω_p dHⁿ = ∫_{Q₁} g(Φ(y))·ω(Φ(y))(E_p) dy = ∫_{Q₁} u(y)·ω(Φ(y))(E_p) dy.
   Steps 5(b), 8 and 9 give all four conclusions for this u. ∎

## Key steps

1. F̆ = Φ_p(Q₁) is Borel (isometry ⇒ measurable embedding) and lies in the coordinate plane through b, so the orientation-sign child gives a Borel σ ∈ {−1,0,1} with ξ = σ e_p a.e. on M ∩ F̆.
2. Isometry invariance of μHE and μHE = volume on ℝⁿ give Hⁿ⌞F̆ = Φ_p#(vol⌞Q₁), hence ∫_{F̆} f dHⁿ = ∫_{Q₁} f∘Φ_p for all f.
3. u := (1_M θ σ)∘Φ_p is Borel and integer-valued with |u| ≤ (1_M θ)∘Φ_p; ∫⁻_{Q₁}(1_M θ)∘Φ_p = R.measure(F̆) < ∞ (compact face, local integrability), giving integrability and ofReal ∫|u| ≤ R.measure(F̆).
4. a.e. on M ∩ F̆, θξ(ω) = 1_Mθσ ω(E_p); extend to F̆ (vanishes off M) and change variables to get ∫_{Q₁} u ω(Φ_p y)(E_p) dy.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n 'cmcdtfrsd_' project mathlib/Mathlib -g '*.lean' (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json (1585 nodes): lean_name/lean_statement/status/candidate_commit/proof_base_commit; no cmcdtfrsd_* name; imrep_carrier_sdiff_support_null (accepted, candidate d15b5cf, base c36d11c) and regcomp_rim_action_integrable (accepted, candidate f1339f9, base e5f36a3) have byte-identical frozen types; sibling frozen types of cmcdtfr_face_geometry, cmcdtfr_skeleton_null, cmcdtfr_plane_orientation extracted`
- `git show d15b5cf:GMT/Ch07/Submission.lean | grep -n '^theorem'; git show f1339f9:GMT/Ch07/Submission.lean | grep -n '^theorem' (accepted declarations present with identical types, no sorry except the root placeholder)`
- `rg -n 'theorem (Isometry\.map_euclideanHausdorffMeasure|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume)' mathlib/Mathlib`
- `rg -n 'theorem (orderEmbOfFin_mem|range_orderEmbOfFin)' mathlib/Mathlib/Data/Finset/Sort.lean`
- `rg -n 'measurableSet_eq_fun' mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean; rg -n 'instIsCountablyGeneratedUniformity' mathlib/Mathlib/Topology/EMetricSpace/Defs.lean; rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'theorem norm_apply_le' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; rg -n 'theorem (floor_add_fract|fract_lt_one)' mathlib/Mathlib/Algebra/Order/Floor/Ring.lean`
- `rg -n 'theorem (setIntegral_congr_ae|setIntegral_congr_set|integral_biUnion_finset)' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean; rg -n 'theorem _root_.MeasurableEmbedding.(integral_map|lintegral_map)' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean; rg -n 'theorem restrict_map' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean; rg -n 'theorem ofReal_integral_eq_lintegral_ofReal' mathlib/Mathlib; rg -n 'theorem isClosedEmbedding' mathlib/Mathlib/Topology/MetricSpace/Isometry.lean; rg -n 'IsClosedEmbedding.measurableEmbedding' mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `sed/grep of lake-packages-25730c7c/simongmt Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, mass), Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, support), Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn), Chapter06/Forms.lean (Covector, DifferentialForm), Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt)`
- `grep of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_existing_lean_name_problem, retained_children, _accepted_checkpoint, _overlay_accepted_children) and github_runtime.py (_handoff_published_children): an accepted declaration with identical type is reused by mapping to the existing node, and its candidate commit is overlaid when the parent is formalized`
- `lake env lean /tmp/sdecomp-k3/lean/Types.lean (all six child types elaborate in the replayed contract scope)`
- `lake env lean /tmp/sdecomp-k3/lean/Probe4.lean and Probe5.lean (TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) is not found by instance search; an explicit ⟨⟨m.toUniformSpace, rfl, EMetric.instIsCountablyGeneratedUniformity⟩⟩ works and makes StronglyMeasurable.measurableSet_eq_fun usable)`
- `lake env lean /tmp/sdecomp-k3/lean/Full.lean (N1Check and N2Check proved; N3Check from (IMC-b) and (PO); N4Check from N3Check; AssemblyCheck.parent and FullCheck.parent: reused types + the three sibling frozen types imply the selected frozen type; #print axioms gives propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Floor/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-80c95515f2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-restriction-integer-multipl-1450eb50b9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/github_runtime.py`
- `/tmp/sdecomp-k3/lean/Types.lean`
- `/tmp/sdecomp-k3/lean/Full.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) matches the workspace, and Submission.lean equals the contract. Neither the snapshot nor simongmt has lattice-face, skeleton or face-density lemmas, and no cmcdtfrsd_ name exists anywhere, so four children are new. Two obligations already exist as comparator-accepted DAG declarations with byte-identical frozen types, imrep_carrier_sdiff_support_null and regcomp_rim_action_integrable, and are reused under the controller's reuse rule. Mathlib supplies every tool the child proofs cite: Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.isClosedEmbedding with IsClosedEmbedding.measurableEmbedding, MeasurableEmbedding.restrict_map/integral_map/lintegral_map, Finset.orderEmbOfFin with orderEmbOfFin_mem and range_orderEmbOfFin, Int.fract_pos and Int.floor_add_fract, PiLp.norm_apply_le, Set.Finite.pi, StronglyMeasurable.measurableSet_eq_fun, ContinuousAlternatingMap.apply, setIntegral_congr_ae, setIntegral_eq_of_subset_of_forall_diff_eq_zero, integral_biUnion_finset, measure_biUnion_finset and ofReal_integral_eq_lintegral_ofReal. One instance gap needs a workaround: PseudoMetrizableSpace (MultiVector P n) is not found by instance search and must be given explicitly. All six child types elaborate. The four new children and the assembly to the selected frozen type compile using only propext, Classical.choice and Quot.sound.

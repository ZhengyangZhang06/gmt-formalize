# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1.piece_orientation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (tangent planes, B2) and the measurability part of step 5 of the supplied proof, for one piece (G, A) of an arbitrary oriented Borel set M. The supplied proof applies it with M := M₀ ∩ spt X, ξ the orientation, G := G_i and A := A_i.

Hypothesis as named in the statement: (IMC a) for every P, n, every open U and all Borel M₁ ⊆ M₂ ⊆ U with Hⁿ(M₂ ∩ K) < ∞ for every compact K ⊆ U: for Hⁿ⌞M₁-a.e. x and every subspace Q, HasApproximateTangentSpaceAt n M₁ x Q ⟺ HasApproximateTangentSpaceAt n M₂ x Q.

Notation: Hⁿ := μHE[n] on ℝ^N; λ := volume on ℝⁿ; e_a := EuclideanSpace.single a 1 (a ∈ Fin n); DG(u) := fderiv ℝ G u.

1. (Pulling back a.e. statements.) By the accepted sibling ae_pullback (Submission.ptd_piece_image_measurable_ae_pullback with P := N, F := G, B := A and the given L, m): (a) G(A) is Borel; (b) every property that holds Hⁿ⌞G(A)-a.e. holds at G(u) for λ⌞A-a.e. u. Moreover, since G(A) ⊆ M, every property that holds Hⁿ⌞M-a.e. holds Hⁿ⌞G(A)-a.e. (ae_restrict_of_ae_restrict_of_subset).
2. (Tangent planes of the piece.) By the accepted theorem ptd_piece_image_approxTangent_ae (with P := N, F := G, B := A and the given L, m; its hypotheses are exactly ours), for λ⌞A-a.e. u: HasApproximateTangentSpaceAt n (G(A)) (G(u)) (range DG(u)).
3. (Locality.) Apply (IMC a) with U := ℝ^N (open), M₁ := G(A) (Borel by 1(a)) and M₂ := M (Borel). Here G(A) ⊆ M ⊆ ℝ^N, and Hⁿ(M ∩ K) < ∞ for every compact K by hypothesis. So for Hⁿ⌞G(A)-a.e. x and every Q: HasApproximateTangentSpaceAt n (G(A)) x Q ⟺ HasApproximateTangentSpaceAt n M x Q. By 1(b), this holds at x = G(u) for λ⌞A-a.e. u.
4. (Orientation.) By hypothesis, for Hⁿ⌞M-a.e. x there is Q with HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ(x)) Q. By step 1, for λ⌞A-a.e. u there is Q_u with HasApproximateTangentSpaceAt n M (G(u)) Q_u and IsUnitOrientationOf (ξ(G(u))) Q_u.
5. (Identification of the plane.) Let u lie in the intersection of the three full-measure sets of steps 2, 3 and 4 (a finite intersection of λ⌞A-conull sets is conull). By step 2 and the direction ⟹ of step 3 with Q := range DG(u), M has approximate tangent space range DG(u) at G(u). By step 4, M also has approximate tangent space Q_u at G(u). Approximate tangent spaces are unique (SimonGMT HasApproximateTangentSpaceAt.unique), so Q_u = range DG(u). Further, range DG(u) = DG(u)(ℝⁿ) = DG(u)(span{e_a}) = span{DG(u)e_a : a ∈ Fin n}, because the e_a form a basis of ℝⁿ (EuclideanSpace.basisFun, whose a-th vector is e_a; LinearMap.range_eq_map, Basis.span_eq, Submodule.map_span, Set.range_comp). Hence ξ(G(u)) is a unit orientation of span{DG(u)e_a : a}. This is the second conclusion.
6. (Measurability.) Since ξ is AE strongly measurable for Hⁿ⌞M, there is a strongly measurable ξ' : ℝ^N → Λ_n(ℝ^N) with ξ = ξ' Hⁿ⌞M-a.e. (AEStronglyMeasurable.mk and ae_eq_mk). By step 1, ξ(G(u)) = ξ'(G(u)) for λ⌞A-a.e. u. The map u ↦ ξ'(G(u)) is strongly measurable (StronglyMeasurable.comp_measurable; G is Lipschitz, hence continuous, hence measurable). So u ↦ ξ(G(u)) is AE strongly measurable for λ⌞A, which is the first conclusion. ∎

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) in a scratch file that imports GMT.Ch07.Submission and uses the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `namespace GMT.Ch07`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`). The prerequisites it applies (Submission.ptd_piece_image_measurable_ae_pullback, Submission.ptd_piece_image_approxTangent_ae) were declared before it with their exact frozen types and `sorry` bodies; `#print axioms` reports propext, Classical.choice and Quot.sound, plus sorryAx coming only from those stubs. It follows the numbered proof above step by step.

```lean
theorem Submission.cmcdt_lpi_pr_piece_orientation_ae : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (N n : ℕ) (M : Set (Euclid N)) (ξ : Euclid N → MultiVector N n) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), MeasurableSet M → (∀ K : Set (Euclid N), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → AEStronglyMeasurable ξ (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid N), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ξ x) Q) → LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ M → AEStronglyMeasurable (fun u => ξ (G u)) (volume.restrict A) ∧ ∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ξ (G u)) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))) := by
  intro hIMCa N n M ξ G A L m hM hloc hξ hor hL hA hm hlow hdiff hGAsub
  obtain ⟨hGAm, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback N n G A L m hL hA hm hlow
  -- (a) the piece has tangent plane `range DG(u)`
  have htan := Submission.ptd_piece_image_approxTangent_ae N n G A L m hL hA hm hlow hdiff
  -- (b) locality of approximate tangent planes, pulled back
  have hlocal := hIMCa N n univ (G '' A) M isOpen_univ hGAm hM hGAsub (subset_univ _)
    (fun K hK _ => hloc K hK)
  have hlocal' := hpull _ hlocal
  -- (c) the orientation property, pulled back
  have hor' := hpull _ (ae_restrict_of_ae_restrict_of_subset hGAsub hor)
  -- (d) a strongly measurable version of `ξ`, pulled back
  have hξ' := hpull _ (ae_restrict_of_ae_restrict_of_subset hGAsub hξ.ae_eq_mk)
  refine ⟨⟨fun u => hξ.mk ξ (G u),
    hξ.stronglyMeasurable_mk.comp_measurable hL.continuous.measurable, ?_⟩, ?_⟩
  · filter_upwards [hξ'] with u hu using hu
  · filter_upwards [htan, hlocal', hor'] with u h1 h2 h3
    obtain ⟨Q, hQ, hQor⟩ := h3
    have hQeq := hQ.unique ((h2 _).mp h1)
    have hrange : LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N) =
        Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))) := by
      rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq,
        Submodule.map_span, ← Set.range_comp]
      congr 2
      funext a
      simp
    rw [← hrange, ← hQeq]
    exact hQor
```

## Key steps

1. ae_pullback (ptd_piece_image_measurable_ae_pullback): G(A) is Borel, and Hⁿ⌞G(A)-a.e. (hence Hⁿ⌞M-a.e.) properties hold at G(u) for λ⌞A-a.e. u.
2. ptd_piece_image_approxTangent_ae: G(A) has approximate tangent space range DG(u) at G(u) for a.e. u ∈ A.
3. (IMC a) with U := ℝ^N, M₁ := G(A), M₂ := M: the approximate tangent spaces of G(A) and M agree a.e. on G(A).
4. The orientation property of ξ on M, pulled back, gives Q_u with HasApproximateTangentSpaceAt n M (G u) Q_u and ξ(G u) a unit orientation of Q_u.
5. Uniqueness of approximate tangent spaces gives Q_u = range DG(u) = span{DG(u)e_a}.
6. A strongly measurable version ξ' of ξ, pulled back, gives AE strong measurability of ξ∘G for λ⌞A.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); sed -n 1,200p GMT/Ch07/Submission.lean (IMRep, IMRep.action, IMRep.Represents, IMRep.measure, IsIntegerMultiplicity, MultiVector, IsUnitOrientationOf)`
- `rg -n 'carrier ⊆|IMRep|massOn' local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json: the selected node (depth 5, max_depth 6, so new children are leaves), its parent integrality-a1 and siblings, the statuses and frozen types of the selected node's five resolved dependencies, the dependencies of every ancestor (two of them, besides this node's own not-yet-accepted span dependency, are not yet accepted), accepted theorems overlapping the supplied steps (dimred_rpd_bilipschitz_image_measure, ptd_piece_image_measurable_ae_pullback, imrep_carrier_sdiff_support_null; frozen types copied verbatim), and lean_name collisions for cmcdt_lpi_pr_imrep_in_support, cmcdt_lpi_pr_lintegral_pullback, cmcdt_lpi_pr_piece_orientation_ae, cmcdt_lpi_pr_orientation_sign, cmcdt_lpi_pr_oriented_piece_area (no node)`
- `grep -rln 'cmcdt_lpi_pr_' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib --include=*.lean (no match)`
- `grep -n in simongmt Chapter06/Mass.lean (covectorEuclideanNorm, covectorEuclideanNorm_zero, massAdmissibleOn, GeometricCurrentOn.massOn, GeometricCurrentOn.mass), Chapter06/CurrentLocalEquality.lean (VanishesOn, zeroRegion, GeometricCurrentOn.support, isOpen_zeroRegion), Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn), Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm), Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `rg -n 'theorem hasSum_integral_iUnion|theorem measurableSet_eq_fun|theorem ae_restrict_of_ae_restrict_of_subset|theorem le_restrict_apply|theorem restrict_apply.|theorem setIntegral_congr_set|theorem lintegral_iUnion|theorem measurable_of_countable|theorem lintegral_map|theorem lintegral_smul_measure|theorem ae_eq_mk|theorem ae_eq_set' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'enorm_natCast|theorem isBoundedBilinearMap_apply|comp_aestronglyMeasurable₂|bounded_above_of_compact_support|theorem basisFun_apply|theorem LinearIndependent.map.' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n 'continuous_eval_const|def apply|apply_apply' Mathlib/Topology/Algebra/Module/Alternating/Topology.lean; rg -n 'norm_image_sub_le' Mathlib/Analysis/Normed/Module/Alternating/Basic.lean; rg -n 'measurable_fderiv_apply_const' Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `rg -n 'MetrizableSpace|toMetrizableSpace|pseudoMetrizableSpace' Mathlib/Topology/Metrizable/Basic.lean; rg -n 'toPseudoMetricSpace|toSeminormedAddCommGroup|toNormedAddCommGroup' Mathlib/Analysis/Normed/Operator/Basic.lean Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `lake env lean /tmp/prsplit/Inst.lean, Inst2.lean, Inst3.lean (#synth: Covector (Euclid 3) 2 is normed via ContinuousAlternatingMap.instNormedAddCommGroup; MultiVector 3 2 is normed via ContinuousLinearMap.toNormedAddCommGroup and its topology is ContinuousLinearMap.topologicalSpace, defeq (rfl) to the norm topology; MetrizableSpace (MultiVector N n) is not synthesized but is built from a local MetricSpace; z ↦ ev_z is continuous)`
- `sed -n 1,200p nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-supplied-natural-proof.md (accepted proof of the reused child); python3 of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json (parent decomposition and its reuse convention); sections of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-natural-proof.md`
- `grep -n of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_decompose and max_depth, _existing_lean_name_problem, _overlay_accepted_children, _inherited_prerequisites) and inherited.py (cited_inherited scans the whole frozen proof file, including Key steps and Reference use)`
- `git show <candidate>:GMT/Ch07/Submission.lean for the three reused theorems (d15b5cf486 imrep_carrier_sdiff_support_null, bed5b8494a ptd_piece_image_measurable_ae_pullback, 0501e07ced dimred_rpd_bilipschitz_image_measure) with #print axioms appended; lake env lean /tmp/prsplit/review/ax_*.lean (each: propext, Classical.choice, Quot.sound); sed of their accepted parent-supplied-natural-proof.md files`
- `lake env lean /tmp/prsplit/v2/ASSEMBLY.lean (the selected theorem from the eight child types and the selected node's five dependencies, all stubbed by their exact frozen types; no other sorry); /tmp/prsplit/v2/ALL.lean (five new children proven plus the assembly; no errors; only the eight stub sorry warnings; #print axioms propext, Classical.choice, Quot.sound plus sorryAx from the stubs only); /tmp/prsplit/v2/ROUNDTRIP.lean (every Lean text of this decomposition extracted verbatim from the JSON; same result); /tmp/prsplit/review/FullParent.lean (merge of the seven accepted prerequisite commits as the runtime overlays them, with only this node's not-yet-accepted span dependency stubbed; exit 0; the new children other than orientation_sign use only propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-655ccd9eaf/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-bilipsch-1804d7035f/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/tmp/prsplit/Stmts.lean`
- `/tmp/prsplit/Assembly.lean`
- `/tmp/prsplit/Inst.lean`
- `/tmp/prsplit/Inst2.lean`
- `/tmp/prsplit/Inst3.lean`
- `/tmp/prsplit/kids/K1.lean`
- `/tmp/prsplit/kids/K25.lean`
- `/tmp/prsplit/kids/K3.lean`
- `/tmp/prsplit/kids/K4.lean`
- `/tmp/prsplit/kids/ALL.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/tmp/prsplit/review/ax_imrep_carrier_sdiff_support_null.lean`
- `/tmp/prsplit/review/ax_ptd_piece_image_measurable_ae_pullback.lean`
- `/tmp/prsplit/review/ax_dimred.lean`
- `/tmp/prsplit/v2/ALL.lean`
- `/tmp/prsplit/v2/ASSEMBLY.lean`
- `/tmp/prsplit/v2/ROUNDTRIP.lean`
- `/tmp/prsplit/review/FullParent.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) carries the same Ch07 contract as the workspace. It contains no lemma giving a support-carried representation, a pulled-back integral bound for bi-Lipschitz pieces, an orientation sign for Lipschitz pieces or an oriented piece area formula. None of the five new cmcdt_lpi_pr_ names occurs in the snapshot or the DAG. Three accepted DAG theorems prove supplied steps exactly and are reused as children with their frozen types copied verbatim:
- imrep_carrier_sdiff_support_null: the null set of step 1;
- ptd_piece_image_measurable_ae_pullback: the a.e. pull-back of step 3 and Borel images;
- dimred_rpd_bilipschitz_image_measure: the measure bound of steps 3 and 10.
Each compiles at its candidate commit with only propext, Classical.choice and Quot.sound.
Library support. SimonGMT provides the current support as U ∖ zeroRegion with zeroRegion open, test forms, and HasApproximateTangentSpaceAt.unique. Mathlib provides every other tool the child proofs cite: ae_eq_set, setIntegral_congr_set, Measure.restrict_apply', Measure.map_apply, Measure.le_iff, lintegral_map, lintegral_smul_measure, ae_restrict_of_ae_restrict_of_subset, AEStronglyMeasurable.mk, StronglyMeasurable.measurableSet_eq_fun, measurable_fderiv_apply_const, ContinuousAlternatingMap.apply and norm_image_sub_le, ContinuousLinearMap.opNorm_le_bound, LinearIndependent.map', EuclideanSpace.basisFun, hasSum_integral_iUnion, lintegral_iUnion, isBoundedBilinearMap_apply and Continuous.bounded_above_of_compact_support.
Instance quirk. MultiVector N n has the CLM topology, which is defeq but not reducibly defeq to its norm topology, so MetrizableSpace must be supplied by hand. The orientation_sign proof records how.
Lean evidence. All eight child types elaborate. The selected statement compiles from the children and the selected node's dependencies. Each of the five new children has a complete Lean proof. The bundle compiles with only standard axioms plus sorryAx from the stubbed prerequisites. It also compiles on the merged real commits of the seven accepted prerequisites, where only this node's not-yet-accepted span dependency remains stubbed.
Prerequisite hygiene. No child proof file names an ancestor dependency it does not apply, so the two unaccepted ancestor dependencies of integrality-a1 and deformation_theorem-a1 never become inherited prerequisites.

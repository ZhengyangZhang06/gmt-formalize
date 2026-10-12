# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.riesz_positive-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `RieszPositive` (Simon, Ch. 1, Lemmas 4.1–4.5, 4.8, Remarks 4.13 and Theorem 4.12; printed proofs, transcribed and completed).

Statement. Let X be a locally compact Hausdorff space (Lean: `T2Space X`, `LocallyCompactSpace X`; for Hausdorff spaces this is equivalent to Simon's definition that every point has a neighbourhood with compact closure). Let K₊ := C_c(X, [0, ∞)) be the cone of continuous f ≥ 0 with compact support spt f, and Λ : K₊ → [0, ∞) additive and positively homogeneous (Lean: an ℝ≥0-linear map C_c(X, ℝ≥0) → ℝ≥0). Then there is a Radon outer measure μ on X (Def. 4.6: (R1) μ is Borel regular and μ(K) < ∞ for compact K; (R2) μ(A) = inf{μ(U) : U ⊇ A open} for all A; (R3) μ(U) = sup{μ(K) : K ⊆ U compact} for open U) such that Λ(f) = ∫_X f dμ for all f ∈ K₊ (integral with respect to μ on the σ-algebra of μ-measurable sets; Lean `caratheodoryMeasure μ`).

Standard facts: compact subsets of a Hausdorff space are closed; a closed subset of a compact set is compact; Urysohn's lemma for normal spaces; Carathéodory's Lemma 1.6 (μ-measurable sets form a σ-algebra on which μ is countably additive) and Remark 1.3 (A is μ-measurable iff μ(Y) ≥ μ(Y ∖ A) + μ(Y ∩ A) whenever μ(Y) < ∞).

TOPOLOGICAL LEMMAS.
T1 (4.1, 4.2). If K₁, …, K_N ⊆ X are pairwise disjoint compact sets, there are pairwise disjoint open U_j ⊇ K_j. [Printed: for x ∉ K compact, for each y ∈ K pick disjoint open U_y ∋ x, V_y ∋ y; finitely many V_{y_i} cover K and ⋂U_{y_i}, ⋃V_{y_i} separate x and K. For L compact disjoint from K, repeat for x ∈ L and use compactness of L to get disjoint open sets containing L and K. For N sets: for i ≠ j choose disjoint open O_{ij} ⊇ K_i, O_{ji} ⊇ K_j and put U_i := ⋂_{j≠i} O_{ij}; then U_i ∩ U_j ⊆ O_{ij} ∩ O_{ji} = ∅.] In particular a compact Hausdorff space is normal (4.2).
T2 (4.3). If V is a neighbourhood of x, there is an open U_x ∋ x with closure Ū_x compact and Ū_x ⊆ V. [Printed: WLOG V open; take an open W₀ ∋ x with W̄₀ compact and W := W₀ ∩ V. W̄ is compact, hence normal (T1); W̄ ∖ W and {x} are disjoint closed subsets of W̄, so there are open U₁ ∋ x, U₂ ⊇ W̄ ∖ W in X with U₁ ∩ U₂ ∩ W̄ = ∅. Put U_x := U₁ ∩ W. Then U_x ⊆ W̄ ∖ U₂, a closed set contained in W ⊆ V; hence Ū_x ⊆ W̄ ∖ U₂ ⊆ V, and Ū_x is compact as a closed subset of W̄.]
T3 (4.4, Urysohn). If K ⊆ V with K compact and V open, there are an open U ⊇ K with Ū compact, Ū ⊆ V, and a continuous f : X → [0, 1] with f ≡ 1 on a neighbourhood of K and f ≡ 0 on X ∖ U; in particular f ∈ K₊ and spt f ⊆ Ū ⊆ V. [Printed: by T2 and compactness, K ⊆ U := U_{x_1} ∪ ⋯ ∪ U_{x_N} with Ū = ⋃Ū_{x_i} compact ⊆ V. Ū is normal (T1), so Urysohn's lemma gives continuous f₀ : Ū → [0, 1] with f₀ = 1 on K and f₀ = 0 on Ū ∖ U. Let f₁ := f₀ on Ū and 0 on X ∖ U; this is well defined (f₀ = 0 on Ū ∖ U) and continuous by the pasting lemma for the finite closed cover X = Ū ∪ (X ∖ U). Finally f := 2 min{f₁, 1/2} equals 1 on the open set {f₁ > 1/2} ⊇ K and vanishes off U.]
T4 (4.5, partition of unity). If K is compact and U₁, …, U_N are open with K ⊆ ⋃U_j, there are φ_j ∈ K₊, 0 ≤ φ_j ≤ 1, with spt φ_j a compact subset of U_j, Σ_jφ_j ≤ 1 on X and Σ_jφ_j ≡ 1 on a neighbourhood of K. [Printed: by T2 each x ∈ K has an open U_x with Ū_x compact ⊆ some U_j; finitely many U_{x_1}, …, U_{x_M} cover K; let V_j be the union of those U_{x_i} with Ū_{x_i} ⊆ U_j, so V̄_j is compact ⊆ U_j and the V_j cover K. By T3 choose ψ_j : X → [0, 1] continuous with ψ_j ≡ 1 on V̄_j and ψ_j ≡ 0 off an open W_j with W̄_j compact ⊆ U_j; and choose f₀ : X → [0, 1] with f₀ ≡ 1 on a neighbourhood of ⋃_jV̄_j and f₀ ≡ 0 on the closed set {Σ_jψ_j = 0}, whose complement is an open neighbourhood of the compact set ⋃_jV̄_j. Put ψ₀ := 1 − f₀. Then Σ_{i=0}^Nψ_i > 0 everywhere (where Σ_{j≥1}ψ_j = 0 we have ψ₀ = 1), and φ_j := ψ_j/Σ_{i=0}^Nψ_i (j = 1, …, N) are continuous, spt φ_j ⊆ W̄_j ⊆ U_j, Σ_{j≥1}φ_j ≤ 1, and Σ_{j≥1}φ_j = 1 where f₀ = 1, a neighbourhood of K.]

REMARKS 4.13. (1) If f, g ∈ K₊ and f ≤ g then g − f ∈ K₊ and Λ(g) = Λ(f) + Λ(g − f) ≥ Λ(f). (2) If spt f ⊆ K and g ∈ K₊ with g ≥ 1 on K, then f ≤ (sup f)g, so Λ(f) ≤ (sup f)Λ(g).

CONSTRUCTION. For open U let μ(U) := sup{Λ(f) : f ∈ K₊, f ≤ 1, spt f ⊆ U} (1), and for arbitrary A let μ(A) := inf{μ(U) : U ⊇ A open} (2). The definitions agree on open sets because (1) is monotone in U.

P1 (finiteness on compacts; formula (3)). For compact K:
  (3) μ(K) = inf{Λ(g) : g ∈ K₊, g ≤ 1, g ≡ 1 on a neighbourhood of K} < ∞.
 “≤”: if g ≡ 1 on an open O ⊇ K and g ≤ 1, then every f ∈ K₊ with f ≤ 1 and spt f ⊆ O satisfies f ≤ g (f ≤ 1 = g on O, f = 0 off O), so μ(K) ≤ μ(O) ≤ Λ(g) by Remark 4.13(1). “≥”: for every open U ⊇ K, T3 gives g ∈ K₊ with g ≤ 1, g ≡ 1 near K and spt g ⊆ U, so Λ(g) ≤ μ(U); take the infimum over U. Finiteness: T3 gives such a g at all, so μ(K) ≤ Λ(g) < ∞.

P2 (μ is an outer measure). μ(∅) = 0 (only f = 0 has spt f ⊆ ∅) and μ is monotone. Let U = ⋃_jU_j with U_j open, and f ∈ K₊, f ≤ 1, spt f ⊆ U. By compactness spt f ⊆ U₁ ∪ ⋯ ∪ U_N for some N; T4 gives φ₁, …, φ_N with spt φ_j ⊆ U_j compact and Σφ_j ≡ 1 near spt f. Then f = Σ_jφ_jf with φ_jf ∈ K₊, φ_jf ≤ 1, spt(φ_jf) ⊆ U_j, so Λ(f) = Σ_jΛ(φ_jf) ≤ Σ_jμ(U_j). Taking the supremum over f, μ(U) ≤ Σ_jμ(U_j). For arbitrary A_j and ε > 0 choose open U_j ⊇ A_j with μ(U_j) ≤ μ(A_j) + 2^{−j}ε; then μ(⋃A_j) ≤ μ(⋃U_j) ≤ Σ_jμ(A_j) + ε.

P3 ((R2), (R3)). (R2) holds by definition (2). (R3): if U is open, f ∈ K₊, f ≤ 1, spt f ⊆ U, then by (3) Λ(f) ≤ μ(spt f) (every g ≤ 1 with g ≡ 1 near spt f satisfies f ≤ g); so μ(U) ≤ sup{μ(K) : K ⊆ U compact} ≤ μ(U).

P4 (additivity on disjoint compacts; printed). Let K₁, K₂ be disjoint compact sets and ε > 0. By (3) choose g ∈ K₊, g ≤ 1, g ≡ 1 on a neighbourhood of K₁ ∪ K₂, with Λ(g) ≤ μ(K₁ ∪ K₂) + ε. By T1 choose disjoint open U₁ ⊇ K₁, U₂ ⊇ K₂, and by T3 f_i ∈ K₊ with f_i ≤ 1, f_i ≡ 1 near K_i, spt f_i ⊆ U_i. Then f_ig ∈ K₊, f_ig ≤ 1, f_ig ≡ 1 near K_i, so μ(K_i) ≤ Λ(f_ig) by (3); and f₁ + f₂ ≤ 1 (disjoint supports), so (f₁ + f₂)g ≤ g. Hence μ(K₁) + μ(K₂) ≤ Λ(f₁g) + Λ(f₂g) = Λ((f₁ + f₂)g) ≤ Λ(g) ≤ μ(K₁ ∪ K₂) + ε. With subadditivity, μ(K₁ ∪ K₂) = μ(K₁) + μ(K₂) < ∞.

P5 (Lemma 4.8: μ is a Radon measure). Borel hulls: given A with μ(A) < ∞, (R2) gives open U_k ⊇ A with μ(U_k) < μ(A) + 1/k, so G := ⋂_kU_k is Borel, G ⊇ A, μ(G) = μ(A); if μ(A) = ∞ take G := X. Open sets are μ-measurable (printed): let U be open, Y ⊆ X with μ(Y) < ∞, ε > 0. By (R2) choose open V ⊇ Y with μ(V) < μ(Y) + ε; by (R3) a compact K₁ ⊆ V ∩ U with μ(V ∩ U) ≤ μ(K₁) + ε; and, V ∖ K₁ being open (K₁ is closed), a compact K₂ ⊆ V ∖ K₁ with μ(V ∖ K₁) ≤ μ(K₂) + ε. Since V ∖ U ⊆ V ∖ K₁, using P4 and monotonicity,
  μ(V ∖ U) + μ(V ∩ U) ≤ μ(V ∖ K₁) + μ(K₁) + ε ≤ μ(K₂) + μ(K₁) + 2ε = μ(K₁ ∪ K₂) + 2ε ≤ μ(V) + 2ε ≤ μ(Y) + 3ε,
and μ(Y ∖ U) + μ(Y ∩ U) ≤ μ(V ∖ U) + μ(V ∩ U). As ε is arbitrary, Remark 1.3 shows U is μ-measurable. The μ-measurable sets form a σ-algebra (Lemma 1.6) containing the open sets, hence all Borel sets. With the Borel hulls and P1, (R1) holds; with P3, μ is a Radon measure.

P6 (representation; printed, with the level sets f^{−1}{t_j} accounted for).
 (4) Λ(h) ≤ μ({h > 0})·sup h for h ∈ K₊. Proof: for compact K ⊇ spt h and g ∈ K₊ with g ≤ 1, g ≡ 1 near K, Remark 4.13(2) gives Λ(h) ≤ (sup h)Λ(g); by (3), Λ(h) ≤ (sup h)μ(K). For η > 0 let h_η := max{h − η, 0} ∈ K₊; spt h_η ⊆ {h ≥ η}, a compact subset of {h > 0}, so Λ(h_η) ≤ (sup h)μ({h > 0}). Also 0 ≤ h − h_η = min{h, η} ≤ ηg' for a fixed g' ∈ K₊ with g' ≡ 1 on spt h (T3), so Λ(h) − Λ(h_η) = Λ(h − h_η) ≤ ηΛ(g') → 0 (η ↓ 0).
 Now let f ∈ K₊, K := spt f, ε > 0; if f ≡ 0 both sides vanish. The sets f^{−1}{t}, t > 0, are pairwise disjoint μ-measurable subsets of K and μ(K) < ∞, so μ(f^{−1}{t}) > 0 for at most countably many t. Choose 0 = t₀ < t₁ < ⋯ < t_N with t_{N−1} < sup f < t_N, t_j − t_{j−1} < ε and μ(f^{−1}{t_j}) = 0 for j = 1, …, N. Let U_j := f^{−1}((t_{j−1}, t_j)): open, pairwise disjoint, contained in K.
 By (1) choose g_j ∈ K₊, g_j ≤ 1, spt g_j ⊆ U_j, with Λ(g_j) ≥ μ(U_j) − ε/N. By (R3) and the measurability of compact sets choose a compact K_j ⊆ U_j with μ(U_j ∖ K_j) < ε/N (μ(U_j) < ∞). By T3 choose h_j ∈ K₊, h_j ≤ 1, h_j ≡ 1 near the compact set K_j ∪ spt g_j, spt h_j ⊆ U_j. Then g_j ≤ h_j and
  (5) μ(U_j) − ε/N ≤ Λ(g_j) ≤ Λ(h_j) ≤ μ(U_j).
 The supports of the h_j are disjoint, so Σ_jh_j ≤ 1 and f − fΣ_jh_j ∈ K₊. If f(x)(1 − Σh_j(x)) > 0, then f(x) > 0, and either f(x) = t_j for some 1 ≤ j < N, or x ∈ U_j for the j with f(x) ∈ (t_{j−1}, t_j) and then x ∉ K_j (as h_j = 1 on K_j). So {f − fΣh_j > 0} ⊆ ⋃_j(U_j ∖ K_j) ∪ ⋃_jf^{−1}{t_j}, and (4) gives
  (6) Λ(f − fΣ_jh_j) ≤ (Σ_jμ(U_j ∖ K_j) + 0)·sup f ≤ ε sup f.
 On spt h_j ⊆ U_j we have t_{j−1}h_j ≤ fh_j ≤ t_jh_j, so by linearity, (5) and t_{j−1} ≤ sup f:
  Σ_jt_{j−1}μ(U_j) − ε sup f ≤ Σ_jt_{j−1}Λ(h_j) ≤ Λ(fΣh_j) ≤ Σ_jt_jΛ(h_j) ≤ Σ_jt_jμ(U_j),
 and adding (6): Σ_jt_{j−1}μ(U_j) − ε sup f ≤ Λ(f) ≤ Σ_jt_jμ(U_j) + ε sup f. On the other hand f vanishes off ⋃_jU_j ∪ ⋃_jf^{−1}{t_j}, the latter set being μ-null, and t_{j−1} ≤ f ≤ t_j on U_j, so Σ_jt_{j−1}μ(U_j) ≤ ∫_Xf dμ ≤ Σ_jt_jμ(U_j). Both Λ(f) and ∫_Xf dμ therefore lie in an interval of length Σ_j(t_j − t_{j−1})μ(U_j) + 2ε sup f ≤ ε(μ(K) + 2 sup f). As ε > 0 is arbitrary, Λ(f) = ∫_Xf dμ.

Conclusion. μ is a Radon outer measure (P5) and Λ(f) = ∫_X f dμ for all f ∈ K₊ (P6); the integral of the bounded continuous compactly supported real function f against the measure μ (finite on spt f) is the Lean integral ∫ (f x : ℝ) ∂(caratheodoryMeasure μ). ∎

Formalization note (non-binding): Mathlib's Riesz–Markov–Kakutani theorem (`MeasureTheory.NNRealRMK.integral_rieszMeasure` and the instance `rieszMeasure_regular`, Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean, after equipping X with `borel X`) gives a regular measure ν with ∫ f dν = Λ f; SimonGMT `isRadonOuterMeasure_toOuterMeasure` (Chapter01/RadonOuterMeasure.lean) shows ν.toOuterMeasure satisfies (R1)–(R3), and `integral_radonCaratheodoryMeasure` (Chapter01/RadonCaratheodoryIntegral.lean) or `integral_trim` (the Carathéodory measure trims to ν on Borel sets) identifies the integrals.

## Key steps

1. Topological lemmas 4.1–4.5: separation of disjoint compacts, relatively compact neighbourhoods, Urysohn's lemma, partitions of unity.
2. Define μ(U) := sup{Λ(f) : f ≤ 1, spt f ⊆ U} for open U and μ(A) := inf{μ(U) : U ⊇ A open}.
3. Formula (3) for compact sets; μ is an outer measure via partitions of unity; (R2) and (R3) hold.
4. Additivity on disjoint compacts; Lemma 4.8 then makes open sets measurable and gives Borel hulls, so μ is a Radon measure.
5. Λ(h) ≤ μ({h > 0})·sup h; a level-set partition with μ-null levels t_j puts Λ(f) and ∫f dμ in one interval of length ≤ ε(μ(spt f) + 2 sup f).

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def (CaratheodoryCriterion|BorelRegularApproximation|LusinTheorem|LebesgueEqHausdorff|IsodiametricInequality|UpperDensityComparison|UpperDensityTheorem|BesicovitchCovering|GeneralDensityTheorem|LebesgueDifferentiation|RadonNikodymTheorem|HausdorffDensityBounds|RieszPositive|RieszVector|RadonCompactness)|^theorem main_theorem|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n -c Poincare.SimonGMT project mathlib/Mathlib`
- `rg -n 'theorem simon_theorem' . (no match: SimonGMT is not in the snapshot)`
- `rg -n 'theorem borel_le_caratheodory|def IsMetric' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n '^theorem exist_disjoint_covering_families|^theorem isEmpty_satelliteConfig_multiplicity|def multiplicity' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n 'theorem integral_rieszMeasure|instance rieszMeasure_regular|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem volume_ball|theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'def IsCaratheodory|def caratheodory |theorem isCaratheodory_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `rg -n 'theorem toMeasure_apply|theorem le_toMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem setLIntegral_trim_ae|theorem lintegral_trim_ae' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; rg -n 'theorem integral_trim_ae|theorem integral_trim ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem restrict_trim' mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n '^instance|^theorem' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'metrizableSpace_of_t3_secondCountable' mathlib/Mathlib/Topology/Metrizable/Urysohn.lean; rg -n 'theorem exists_compact_superset' mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact' mathlib/Mathlib/Topology/UrysohnsLemma.lean; rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'theorem tendsto_iff_forall_integral_tendsto' mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean; rg -n -F 'CompactSpace (ProbabilityMeasure' mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean; rg -n 'theorem measure_iUnion_le|theorem measure_mono_null' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `test -f on every cited snapshot file (all present); cmp of cited Mathlib files against lake-packages-25730c7c/mathlib (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Urysohn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`

The manifest pins project ec1c322 and Mathlib 25730c7c. In the snapshot, project/GMT/Ch01/Contract.lean is byte-identical to Submission.lean. It defines exactly the fifteen Props CaratheodoryCriterion … RadonCompactness (lines 88–303), with main_theorem at line 313, inside namespace GMT.Ch01 with `universe u v` (line 69) and the opens at lines 63–65. Each child lean_statement is one of these Props or a conjunction of two of them; the two merged children with universe parameters share the declared universe u, which the comparator replays from that scope. README.md maps the conjuncts to SimonGMT theorems and documents the 4.16 erratum (second countability). That erratum is applied in radon_compactness. The snapshot contains no SimonGMT declarations: rg finds 'Poincare.SimonGMT' only as imports and opens in the project files, and 'theorem simon_theorem' has no match. The package is pinned in project/lake-manifest.json and lives outside the snapshot, so the children cite it only in non-binding formalization notes. The snapshot's Mathlib contains the facts those notes rely on:
- OuterMeasure.IsMetric and borel_le_caratheodory: Measure/Hausdorff.lean:137,161.
- Besicovitch.exist_disjoint_covering_families (Covering/Besicovitch.lean:455), multiplicity and isEmpty_satelliteConfig_multiplicity (BesicovitchVectorSpace.lean:98,488).
- NNRealRMK.integral_rieszMeasure and rieszMeasure_regular (RieszMarkovKakutani/NNReal.lean:47,66); the real RMK (Real.lean:345,357).
- EuclideanSpace.volume_ball and volume_closedBall: Lebesgue/VolumeOfBalls.lean:307,324.
- IsCaratheodory and the caratheodory σ-algebra: OuterMeasure/Caratheodory.lean:55,176,181.
- toMeasure_apply and le_toMeasure_apply (Measure/OuterMeasure.lean:46,50); ae_iff (OuterMeasure/AE.lean:134).
- setLIntegral_trim_ae (Integral/Lebesgue/Add.lean:490); integral_trim and integral_trim_ae (Bochner/Basic.lean:1301,1332); restrict_trim (Measure/Trim.lean:108).
- σ-compactness and compact exhaustions: SigmaCompact.lean:187,376,418.
- Urysohn's lemma: UrysohnsLemma.lean:404.
- Separability of C(X,Y): ContinuousMap/SecondCountableSpace.lean:108. Metrizability: Metrizable/Urysohn.lean:127.
- Compact supersets: LocallyCompact.lean:58. IsCompact.tendsto_subseq: Sequences.lean:298.
- Weak convergence and Prokhorov: FiniteMeasure.lean:727; Prokhorov.lean:176.
The cited Mathlib files are byte-identical to the packages used by the build. The mathematical arguments of the children are the printed proofs of the source and do not depend on these declarations.

# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1`
- Child DAG node: `root.density_one_regularity-a1.translate_varifold-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is the translation step 'after applying the appropriate translation' of Simon's proof of 7.1 (p. 127) and fact (Inv) of the parent proof, proved in detail from the contract definitions. Notation: H^n = muHE[n]; mu = V.weight = (H^n restricted to M) with density ofReal(theta); tau(x) = x - xi with inverse tau^{-1}(x) = x + xi; for a set A, tau(A) = {a - xi : a in A} = (tau^{-1})^{-1}(A).
1. tau is a bijective isometry of R^(n+l), hence a homeomorphism and a measurable equivalence (Borel sets to Borel sets, both ways). Hausdorff measures, and hence H^n = muHE[n], are invariant under isometries: H^n(tau(A)) = H^n(A) for every A, tau_# H^n = H^n and (tau^{-1})_# H^n = H^n (tau is measure preserving for H^n).
2. Construction of V'. Put M' := tau(M) and theta'(x) := theta(x + xi). The structure fields hold: (a) M' is contained in tau(U) since M is contained in U. (b) M' = (tau^{-1})^{-1}(M) is H^n-null-measurable, because M is and preimages of null-measurable sets under the measure-preserving map tau^{-1} are null-measurable. (c) M' is countably n-rectifiable: if M is contained in M_0 union U_j F_j(R^n) with H^n(M_0) = 0 and F_j Lipschitz, then M' is contained in tau(M_0) union U_j (tau o F_j)(R^n), H^n(tau(M_0)) = H^n(M_0) = 0, and tau o F_j is Lipschitz with the same constant. (d) If x is in M' then x + xi is in M, so theta'(x) = theta(x + xi) > 0. (e) H^n restricted to M' equals tau_#(H^n restricted to M) (for Borel A: tau_#(H^n|M)(A) = H^n(tau^{-1}(A) cap M) = H^n(tau(tau^{-1}(A) cap M)) = H^n(A cap M')), and theta' o tau = theta; since a function f is a.e.-measurable for tau_# nu iff f o tau is a.e.-measurable for nu (tau a measurable equivalence), theta' is a.e.-measurable for H^n restricted to M'. (f) If K is compact and contained in tau(U), then K' := tau^{-1}(K) = K + xi is compact and contained in U, M' cap K = tau(M cap K'), and integrability (a.e. strong measurability together with finiteness of the integral) transfers as a whole under the measure-preserving equivalence tau: theta' is H^n-integrable on tau(M cap K') iff theta' o tau = theta is H^n-integrable on M cap K', which holds by hypothesis. So V' := v(M', theta') is a rectifiable n-varifold in tau(U), with carrier tau(M) and multiplicity theta(. + xi) by construction.
3. Weight. For Borel A: (tau_# mu)(A) = mu(tau^{-1}(A)) = int_{tau^{-1}(A)} ofReal(theta) d(H^n|M) = int_A ofReal(theta o tau^{-1}) d(tau_#(H^n|M)) = int_A ofReal(theta') d(H^n|M') = mu_{V'}(A), using the change of variables for the pushforward under the measurable equivalence tau and step 2(e). Hence mu_{V'} = tau_# mu.
4. Support. For a homeomorphism tau, spt(tau_# mu) = tau(spt mu): x is in spt(tau_# mu) iff every neighbourhood N of x has mu(tau^{-1}(N)) > 0 iff every neighbourhood of tau^{-1}(x) has positive mu-measure (tau^{-1} maps the neighbourhoods of x onto those of tau^{-1}(x)) iff tau^{-1}(x) is in spt mu. Therefore spt V' = tau(U) cap spt(mu_{V'}) = tau(U) cap tau(spt mu) = tau(U cap spt mu) = tau(spt V) (tau injective).
5. Tangent planes. For every x and every linear subspace P: P is an approximate tangent space of M' with respect to theta' at x (Simon Ch. 3, 1.7, i.e. HasWeightedApproximateTangentSpaceAt n M' theta' x P) iff P is one of M with respect to theta at x + xi. Indeed, with eta_{x,r}(y) = r^{-1}(y - x): eta_{x,r}(M') = {r^{-1}(m - xi - x) : m in M} = eta_{x+xi,r}(M); for y in this set theta'(x + r y) = theta((x + xi) + r y); and theta'(x) = theta(x + xi). Hence for every f in C_c and every r the integrals int_{eta_{x,r}(M')} f(y) theta'(x + r y) dH^n(y) and int_{eta_{x+xi,r}(M)} f(y) theta(x + xi + r y) dH^n(y) coincide, the limits theta'(x) int_P f dH^n and theta(x + xi) int_P f dH^n coincide, and the dimension condition is the same. Since tangentProj is defined from this predicate alone (orthogonal projection onto a chosen approximate tangent space when one exists, 0 otherwise), and the two predicates are equal as functions of P, we get tangentProj_{V'}(x) = tangentProj_V(x + xi) for all x: either no approximate tangent space exists for either side (both values are 0), or both existence statements hold and the two chosen subspaces are choices (Classical.choose) from the same predicate, hence equal. (In Lean, rewriting the predicate inside the dependent if-then-else can fail because of the auxiliary orthogonal-projection instance proof in its body; case-split on the existence statement and prove equality of the two chosen subspaces by substituting the equal predicates.)
6. Divergence. For X in C^1 put Y := X o tau, i.e. Y(y) = X(y - xi). Then DY(y) = DX(tau y), so by step 5 div_M Y(y) = trace(DX(tau y) o tangentProj_V(y)) = trace(DX(tau y) o tangentProj_{V'}(tau y)) = div_{M'} X(tau y).
7. Proof of (i). Assume V has generalized mean curvature H in U. (a) Local integrability: let x be in tau(U), x = tau(y) with y in U. By hypothesis there is N, a neighbourhood of y within U, with int_N |H| dmu < infinity. Then tau(N) is a neighbourhood of x within tau(U) (tau homeomorphism) and, integrability transferring as a whole under the measurable equivalence tau, H' is (tau_# mu)-integrable on tau(N) iff H' o tau = H is mu-integrable on N, since H'(tau(y)) = H(y - xi + xi) = H(y). So H' is locally integrable on tau(U) for mu_{V'} = tau_# mu. (b) Let X be C^1 with compact support and tsupport X contained in tau(U). Then Y = X o tau is C^1, has compact support, and tsupport Y = tau^{-1}(tsupport X) is contained in U. The identity for V gives int div_M Y dmu = - int <Y, H> dmu. By the change of variables for pushforwards under the measurable equivalence tau (valid for Bochner integrals of arbitrary functions, integrable or not): int div_{M'} X dmu_{V'} = int (div_{M'} X) o tau dmu = int div_M Y dmu (step 6), and int <X, H'> dmu_{V'} = int <X(tau y), H'(tau y)> dmu(y) = int <Y, H> dmu. Hence int div_{M'} X dmu_{V'} = - int <X, H'> dmu_{V'}, i.e. V' has generalized mean curvature H' in tau(U).
8. Proof of (ii). Under the stated assumptions we check the seven parts of AllardHypotheses H' p delta r for V'. (a) 0 < r is assumed. (b) V' has generalized mean curvature H' in tau(U) by step 7. (c) theta' >= 1 mu_{V'}-a.e.: for the measurable equivalence tau, a property holds (tau_# mu)-a.e. iff its composition with tau holds mu-a.e.; and 1 <= theta'(tau y) = theta(y) holds for mu-a.e. y. (d) 0 = tau(xi) is in tau(spt V) = spt V' (step 4). (e) B_r(0) is contained in tau(U): if |z| <= r then z + xi is in B_r(xi), which is contained in U, and z = tau(z + xi). (f) mu_{V'}(B_r(0)) = mu(tau^{-1}(B_r(0))) = mu(B_r(xi)) <= (1 + delta) omega_n r^n, since tau^{-1}(B_r(0)) = {y : |y - xi| <= r} (closed balls are Borel). (g) int_{B_r(0)} |H'|^p dmu_{V'} = int_{tau^{-1}(B_r(0))} |H' o tau|^p dmu = int_{B_r(xi)} |H|^p dmu (change of variables for [0, infinity]-valued functions under a measurable equivalence; no measurability of H is needed), so (r^(p-n) int_{B_r(0)} |H'|^p dmu_{V'})^(1/p) = (r^(p-n) int_{B_r(xi)} |H|^p dmu)^(1/p) <= delta. Hence V'.AllardHypotheses H' p delta r. Steps 2-8 give all asserted properties of V'.

## Key steps

1. tau(x) = x - xi is an isometric measurable equivalence preserving H^n
2. Define V' = v(tau(M), theta(. + xi)) and verify the structure fields
3. Weight of V' is the pushforward of mu; support of V' is tau(spt V)
4. Weighted approximate tangent spaces and hence tangentProj are translation equivariant; div_{M'} X o tau = div_M (X o tau)
5. Change of variables transfers the first-variation identity and local integrability
6. Check the seven parts of AllardHypotheses at the origin by change of variables

## Reference use

### local-project

Queries:
- `sed -n 1280,1400p book/chapter-05.txt (Theorem 7.1 and its printed proof)`
- `sed -n 215,575p book/chapter-04.txt (3.1-3.17, 4.1-4.11); sed -n 1,200p and 270,340p book/chapter-03.txt (1.1-1.9); sed -n 560,720p book/chapter-01.txt (3.1-3.7); grep -n 'Approximation Theorem' book/chapter-02.txt`
- `grep -n '^def \|^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn 'ae_hasWeightedApproximateTangent\|ae_hasApproximateTangent\|Theorem 1.9\|1\.9' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Densities,DensityComparison,LowerDensityComparison,HausdorffDensityBounds,RelativeDensityComparison,GeneralDensity,EuclideanNormalization,Hausdorff}.lean`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{LpLowerDensity,MultiplicityBridge}.lean; sed -n 1,227p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `grep -n '^theorem \|^lemma \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,WhitneyExtension}.lean .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{SubmanifoldCover,Differential}.lean; grep -n 'injective_area_formula_lipschitz_simon' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `grep -rn 'μHE\[' <snapshot>/mathlib/Mathlib --include=*.lean; sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n image_symmDiff <snapshot>/mathlib/Mathlib/Data/Set/Image.lean; rg -n 'inf_symmDiff_distrib_right|symmDiff_inf_distrib|inter_symmDiff_distrib' <snapshot>/mathlib/Mathlib/Order/SymmDiff.lean <snapshot>/mathlib/Mathlib/Data/Set/*.lean`
- `grep -n 'divRight\|mulRight\|to_additive' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `rg -n 'theorem fderivWithin_of_mem_nhds|theorem ball_subset_interior_closedBall|theorem closedBall_mem_nhds ' <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean <snapshot>/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `rg -n 'isometry_sub_const|isometry_add_const|IsometryEquiv.subRight|def subRight|def addRight' <snapshot>/mathlib/Mathlib/Topology <snapshot>/mathlib/Mathlib/Analysis/Normed`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/README.md GMT/Ch05/README.md`
- `grep -rl '<the seven proposed lean_names>' .humanize GMT; python3 scan of dag.json nodes for reserved children/theorems`
- `lake env lean /tmp/dor-a1-check/Check2.lean (contract lines 1-460, namespace Submission with allard_regularity_theorem and the 7 children as sorry placeholders, full proof of density_one_regularity : DensityOneRegularity, sanity example transferring tangentProj measurability to V.weight)`
- `lake env lean /tmp/dor-a1-check/verify/FormalAll.lean (reviewer's sorry-free proofs of four children with the frozen types; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Data/Set/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/IsometricSMul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpLowerDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/MultiplicityBridge.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/tmp/dor-a1-check/Check2.lean`
- `/tmp/dor-a1-check/verify/FormalAll.lean`

Snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's Contract.lean and README.md are byte-identical to the workspace copies (cmp).

No prior work: there is no existing proof of DensityOneRegularity or of any proposed child. The seven proposed names occur nowhere in .humanize or GMT, and dag.json reserves no child names yet.

SimonGMT, Chapter03/Rectifiable.lean: defines HasWeightedApproximateTangentSpaceAt (l.330) and proves uniqueness (l.345), but the grep finds no a.e.-existence result (Ch. 3, 1.9 is not formalized) and nothing on measurability of the tangent field. Hence child tangent_ae.

SimonGMT Chapter04 L^p density results (LpLowerDensity.lean: one_le_stationaryDensityReal_of_mem_support_lp) are stated for Chapter04.RectifiableVarifold. That structure stores a tangent field, a measurable carrier and a globally locally finite weight (Chapter04/Basic.lean), so they do not apply to the contract varifold. Hence child density_ge_one, proved from the contract's first variation following Simon 4.1-4.10(1).

SimonGMT Chapter01/DensityComparison.lean has the Upper Density Theorem (simon_theorem_3_6) and the comparison theorem (simon_theorem_3_3, mul_simonHausdorff_le_of_le_dimensionalUpperDensity). Both are stated for simonHausdorffOuterMeasureReal, a positive multiple of μH[n] (Hausdorff.lean: simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure). Since μHE[n] is also a nonzero multiple of μH[n] (Mathlib Geometry/Euclidean/Volume/Measure.lean), null sets agree; this is used by carrier_support_null.

SimonGMT also provides, for tangent_ae: Lusin (Chapter01/Lusin.lean, simon_theorem_1_17), the injective Lipschitz area formula (Chapter02/AreaLipschitz.lean:126) and Whitney C^1 extension (Chapter02/WhitneyExtension.lean).

Mathlib items used by the parent assembly:
- Isometry.euclideanHausdorffMeasure_image and IsometryEquiv.measurePreserving_euclideanHausdorffMeasure (Measure.lean)
- Set.image_symmDiff (Data/Set/Image.lean:388)
- Set.inter_symmDiff_distrib_right (Data/Set/SymmDiff.lean:46)
- IsometryEquiv.subRight, via to_additive of divRight (IsometricSMul.lean:166-172)
- fderivWithin_of_mem_nhds (FDeriv/Basic.lean:522)
- ball_subset_interior_closedBall (Pseudo/Defs.lean:1216) and closedBall_mem_nhds (Pseudo/Defs.lean:842)
The names isometry_sub_const / isometry_add_const / def subRight have no match in Topology or Analysis/Normed.

Lean checks:
- All 7 child types elaborate in the contract scope.
- density_one_regularity : DensityOneRegularity compiles from the children plus the sibling AllardRegularityTheorem. The only warnings are the 8 sorry warnings on the placeholders; an independent reviewer reproduced this.
- The reviewer's sorry-free Lean proofs of allard_scale, translate_varifold, open_graph_domain and holder_class use exactly the frozen types and recompile with axioms propext, Classical.choice, Quot.sound.

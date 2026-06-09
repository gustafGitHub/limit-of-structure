/-
================================================================================
  Where Structure Ends — Lean 4 formalization (first draft)
  Companion to: G. Ullman, "Where Structure Ends" (Zenodo 2026).
  Concept DOI: 10.5281/zenodo.17159948   Version DOI: 10.5281/zenodo.18773650
================================================================================

  WHAT THIS FILE FORMALIZES
  -------------------------
  The paper's formal core is a single engine — *fiber-blindness of descent* —
  applied in four registers:

    1.  The Quotient Test (Criterion 1) as a genuine factorization theorem:
        a quantity is invariant under admissible transformations IFF it
        descends to the structural quotient, and the descent is UNIQUE.
    2.  The sharpened dilemma (§9.1): a quantity that separates two
        perspectives in a common fiber cannot be invariant, hence cannot be
        an objective observable.
    3.  Degeneration in the S_min regime (§7) and the time-degeneration
        corollary (Remark 1).
    4.  "Limit of structure ≠ limit of actuality" (§6.3): as soon as the
        projection forgets mode of givenness, there are facts about
        perspectives that do not descend to the quotient, hence survive any
        collapse of structure.

  WHAT IS *NOT* A THEOREM (and must not be coded as one)
  ------------------------------------------------------
  Primitivism about phenomenality and the Ontological Closure Principle are
  the paper's METAPHYSICAL PREMISES (the paper itself says "a metaphysical
  stance, not a theorem"). They live in `namespace OE.Metaphysics` as explicit
  hypotheses / definitions, NEVER as global `axiom`s. The verified core above
  therefore stays free of extra-logical commitments; expect
  `#print axioms` on the core theorems to return only
  `[propext, Classical.choice, Quot.sound]` (Classical only for the `by_cases`
  dichotomy; the rest are constructive modulo `Quot.sound`).

  STATUS: first draft, NOT yet `lake build`-verified in a Mathlib project.
  See CLAUDE_CODE_INSTRUCTIONS.md for the build steps and the "VERIFY" list of
  Mathlib lemma names that may need adjustment.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Basic
-- Fallback if a lemma is not found: `import Mathlib`

set_option autoImplicit false

namespace OE

/-! ## 1. Schematic descent layer (§2)

`Obs` is the type of observer-perspectives. The admissible transformations are
modelled, at this schematic level, by an equivalence relation: a `Setoid Obs`
whose quotient is the structural codomain `Str`. This matches the paper's
hedging that descent is "a quotient/descent construction along the relevant
action/groupoid, not necessarily a set-theoretic quotient." The genuine
group-action case is recovered in §2'. -/

section Schematic

variable {Obs : Type*} [s : Setoid Obs] {X : Type*}

/-- The structural quotient `S ≃ O/G` (Eq. 1).

The base type `Obs` is an explicit argument so that the quotient (and hence its
`Setoid` instance) is always pinned at use sites; otherwise an occurrence of
`Str` with no constraining `proj` would leave the `Setoid Obs` instance stuck on
a metavariable. -/
abbrev Str (Obs : Type*) [inst : Setoid Obs] : Type _ := Quotient inst

/-- The projection `π : O → S` that forgets mode of givenness (Eq. 1, §2). -/
def proj : Obs → Str Obs := Quotient.mk s

/-- A candidate quantity is **invariant** if it is constant on
equivalence classes of admissible transformations (the hypothesis of
Criterion 1(i): `Q(o) = Q(g · o)`). -/
def Invariant (Q : Obs → X) : Prop := ∀ a b : Obs, a ≈ b → Q a = Q b

/-- A candidate quantity is **constant on fibers** if any two perspectives
with the same structural image receive the same value. -/
def ConstantOnFibers (Q : Obs → X) : Prop := ∀ a b : Obs, proj a = proj b → Q a = Q b

/-- A candidate quantity **descends** to the structural quotient if it
factors through `π` (Criterion 1(i): existence of `Q̃` with `Q = Q̃ ∘ π`). -/
def Descends (Q : Obs → X) : Prop := ∃ Q' : Str Obs → X, Q = Q' ∘ proj

/-- A candidate quantity **separates a fiber** if it distinguishes two
perspectives with the same structural image (the would-be "phenomenal
discriminator" of §9.1). -/
def SeparatesAFiber (Q : Obs → X) : Prop := ∃ a b : Obs, proj a = proj b ∧ Q a ≠ Q b

/-- Invariance and constancy-on-fibers are the same condition, since
`π a = π b ↔ a ≈ b`. -/
theorem invariant_iff_constantOnFibers (Q : Obs → X) :
    Invariant Q ↔ ConstantOnFibers Q := by
  constructor
  · intro h a b hab
    exact h a b (Quotient.exact hab)
  · intro h a b hab
    exact h a b (Quotient.sound hab)

/-- The descent of an invariant quantity to the structural quotient
(the map `Q̃` of Criterion 1(i)). -/
def descend (Q : Obs → X) (h : Invariant Q) : Str Obs → X :=
  Quotient.lift Q fun _ _ hab => h _ _ hab

@[simp] theorem descend_proj (Q : Obs → X) (h : Invariant Q) (o : Obs) :
    descend Q h (proj o) = Q o := rfl

/-- **Quotient Test, Criterion 1(i) (existence).**
A quantity is invariant under admissible transformations iff it descends to
the structural quotient. -/
theorem quotientTest (Q : Obs → X) : Invariant Q ↔ Descends Q := by
  constructor
  · intro h
    refine ⟨descend Q h, ?_⟩
    funext o
    rfl
  · rintro ⟨Q', rfl⟩
    intro a b hab
    exact congrArg Q' (Quotient.sound hab)

/-- Two maps out of the quotient that agree after precomposition with `π`
are equal (`π` is surjective). The uniqueness half of Criterion 1(i). -/
theorem descend_unique {Q'₁ Q'₂ : Str Obs → X}
    (h : ∀ o : Obs, Q'₁ (proj o) = Q'₂ (proj o)) : Q'₁ = Q'₂ :=
  funext (Quotient.ind h)

/-- **Quotient Test, Criterion 1(i) (existence + uniqueness).**
An invariant quantity descends to a *unique* map on the structural quotient. -/
theorem quotientTest_unique (Q : Obs → X) (h : Invariant Q) :
    ∃! Q' : Str Obs → X, Q = Q' ∘ proj := by
  refine ⟨descend Q h, ?_, ?_⟩
  · funext o; rfl
  · intro Q'' hQ''
    apply descend_unique
    intro o
    exact (congrFun hQ'' o).symm

/-- **Dilemma horn (a), §9.1.** If a quantity descends to the structural
quotient, it is *blind to the fiber*: it cannot distinguish two perspectives
once their structural image is fixed. -/
theorem fiber_blind {Q : Obs → X} (h : Descends Q) {a b : Obs}
    (hab : proj a = proj b) : Q a = Q b := by
  obtain ⟨Q', rfl⟩ := h
  exact congrArg Q' hab

/-- Contrapositive of `fiber_blind`: a quantity that separates two perspectives
in a common fiber cannot descend. -/
theorem not_descends_of_separates {Q : Obs → X} {a b : Obs}
    (hab : proj a = proj b) (hne : Q a ≠ Q b) : ¬ Descends Q :=
  fun h => hne (fiber_blind h hab)

/-- **A structural observable is necessarily fiber-blind (§9.1).** No quantity
can both descend to the structural quotient and separate a fiber. This is the
most article-ready form of horn (a). -/
theorem no_objective_fiber_sensitive_quantity {Q : Obs → X} :
    Descends Q → ¬ SeparatesAFiber Q := by
  intro hdesc hsep
  obtain ⟨a, b, hab, hne⟩ := hsep
  exact hne (fiber_blind hdesc hab)

/-- **No structural factorization of a fiber-sensitive quantity (§9.1 no-go).**
If `Q` separates a fiber, then `Q` is not of the form `Q' ∘ π` for any structural
`Q' : Str → X`: a fiber-sensitive quantity has no structural representative. -/
theorem no_factor_of_separates {Q : Obs → X} (h : SeparatesAFiber Q) :
    ∀ Q' : Str Obs → X, Q ≠ Q' ∘ proj := by
  intro Q' hQ
  obtain ⟨a, b, hab, hne⟩ := h
  exact hne (fiber_blind ⟨Q', hQ⟩ hab)

/-- **Dilemma horn (b), §9.1 + Criterion 1(ii).** A quantity that tracks a
fiber-local difference (a "what-it-is-like" not visible in the public
structure) is not invariant — so it fails to define an objective observable. -/
theorem not_invariant_of_separatesAFiber {Q : Obs → X}
    (h : SeparatesAFiber Q) : ¬ Invariant Q := by
  intro hinv
  obtain ⟨a, b, hab, hne⟩ := h
  exact not_descends_of_separates hab hne ((quotientTest Q).mp hinv)

/-- The Quotient Test as a clean dichotomy (Criterion 1, both clauses):
every candidate quantity either descends to the structural quotient (and is
then fiber-blind) or fails to be invariant. -/
theorem quotient_dichotomy (Q : Obs → X) : Descends Q ∨ ¬ Invariant Q := by
  by_cases h : Invariant Q
  · exact Or.inl ((quotientTest Q).mp h)
  · exact Or.inr h

/-- Classical converse of `not_invariant_of_separatesAFiber`: if a quantity is
not invariant, then it separates some fiber. Classical because the witness is
extracted from the negation of a universal statement. -/
theorem separatesAFiber_of_not_invariant {Q : Obs → X}
    (h : ¬ Invariant Q) : SeparatesAFiber Q := by
  classical
  by_contra hsep
  apply h
  intro a b hab
  by_contra hne
  exact hsep ⟨a, b, Quotient.sound hab, hne⟩

/-- **Strong Quotient Test dichotomy.** A candidate quantity either descends to
the structural quotient or it separates a fiber. This is sharper than
`quotient_dichotomy`: it names the actual obstruction (fiber sensitivity)
instead of mere non-invariance. -/
theorem quotient_dichotomy_strong (Q : Obs → X) :
    Descends Q ∨ SeparatesAFiber Q := by
  classical
  by_cases h : Invariant Q
  · exact Or.inl ((quotientTest Q).mp h)
  · exact Or.inr (separatesAFiber_of_not_invariant h)

/-- A quantity descends exactly when it does not separate any fiber: the
descent obstruction is fiber sensitivity, and nothing else. -/
theorem descends_iff_not_separatesAFiber (Q : Obs → X) :
    Descends Q ↔ ¬ SeparatesAFiber Q := by
  classical
  constructor
  · exact no_objective_fiber_sensitive_quantity
  · intro hno
    refine (quotientTest Q).mp ?_
    intro a b hab
    by_contra hne
    exact hno ⟨a, b, Quotient.sound hab, hne⟩

end Schematic

/-! ## 2'. Group-action realization (§2, "G a symmetry group")

The schematic Setoid is realized by a genuine group action: the orbit relation
of `G ⟳ Obs`. Here "invariant" is the literal `Q (g • o) = Q o`, and the
Quotient Test transfers verbatim to the orbit space `Obs / G`. -/

section GroupAction

open MulAction

variable {G : Type*} [Group G] {Obs : Type*} [MulAction G Obs] {X : Type*}

-- The orbit relation as the operative `Setoid` (admissible transformations =
-- the group action). Made a local instance so the schematic results above
-- specialize to it. The `synthInstance.checkSynthOrder` guard is needed only
-- because `G` is recovered from the ambient `MulAction G Obs` rather than from
-- the target `Setoid Obs`; within this section that action is unique, so
-- resolution is unambiguous.
set_option synthInstance.checkSynthOrder false in
local instance instOrbitSetoid : Setoid Obs := orbitRel G Obs

/-- Invariance under the group of admissible transformations (Criterion 1's
"`Q(o) = Q(g · o)` for all `g ∈ G`"). -/
def GInvariant (Q : Obs → X) : Prop := ∀ (g : G) (o : Obs), Q (g • o) = Q o

/-- Group-invariance coincides with invariance under the orbit relation. -/
theorem ginvariant_iff_invariant (Q : Obs → X) :
    GInvariant (G := G) Q ↔ Invariant Q := by
  constructor
  · intro h a b hab
    -- `hab : a ≈ b` is, definitionally, `a ∈ orbit G b` (`orbitRel_apply` is `Iff.rfl`).
    have hmem : a ∈ orbit G b := hab
    obtain ⟨g, hg⟩ := hmem
    rw [← hg]
    exact h g b
  · intro h g o
    have hmem : g • o ∈ orbit G o := mem_orbit o g
    exact h _ _ hmem

/-- **Quotient Test for genuine symmetry groups.** A quantity is invariant
under the admissible group action iff it descends to the orbit space
`Obs / G`. -/
theorem quotientTest_group (Q : Obs → X) :
    GInvariant (G := G) Q ↔ Descends Q :=
  (ginvariant_iff_invariant Q).trans (quotientTest Q)

end GroupAction

/-! ## 3. Degeneration of the projection in the limit (§7, Remark 1)

`I` is the OE-relevant invariant signature read off the structural quotient
(`I` of §6.1: symmetry data, orbit-type complexity, `dim Aut(S)`, ...). The
`S_min` regime of "maximal symmetry / no remaining OE-relevant distinctions"
is modelled, in this first draft, by `I` being globally constant. (See
CLAUDE_CODE_INSTRUCTIONS.md TODO for the order-theoretic `S_min` refinement.) -/

section Degeneration

variable {Obs : Type*} [s : Setoid Obs] {Inv : Type*}

/-- The invariant signature **collapses** when it cannot distinguish any two
structural classes (the `S_min` regime: `Aut(S)` is `I`-maximal, the remaining
distinctions are quotiented out). -/
def Collapses (I : Str Obs → Inv) : Prop := ∀ x y : Str Obs, I x = I y

/-- Under collapse, admissible base change in `Obs` induces no variation in the
invariant signature of the structural image (the displayed equation after
§7.2: `I(π o)` ceases to vary). -/
theorem collapse_const (I : Str Obs → Inv) (h : Collapses I) (a b : Obs) :
    I (proj a) = I (proj b) := h _ _

/-- Under collapse, every quantity assembled from the invariant signature is
non-discriminating: invariance constraints become vacuous. -/
theorem collapse_no_discrimination {X : Type*} (I : Str Obs → Inv) (h : Collapses I)
    (f : Inv → X) (a b : Obs) :
    (f ∘ I ∘ proj) a = (f ∘ I ∘ proj) b :=
  congrArg f (collapse_const I h a b)

/-- OE-linked time as *registered* structural change (Remark 1): a base change
`a ⤳ b` registers iff it alters the invariant signature of the structural
image. -/
def Registers (I : Str Obs → Inv) (a b : Obs) : Prop := I (proj a) ≠ I (proj b)

/-- **Time-degeneration corollary (Remark 1).** In the collapsed regime no base
change registers, so the OE notion of time becomes vacuous. -/
theorem time_degenerates (I : Str Obs → Inv) (h : Collapses I) (a b : Obs) :
    ¬ Registers I a b :=
  fun hreg => hreg (collapse_const I h a b)

end Degeneration

/-! ## 4. Limit of structure ≠ limit of actuality (§6.3) — structural core

The forgetfulness constraint (F1) says `π` is non-injective on objects. We show
its precise consequence: as soon as `π` is forgetful, there are facts about
perspectives — paradigmatically *which* perspective one occupies — that do
**not** descend to the structural quotient. Such facts are invisible to every
structural quantity and therefore survive any collapse of structure. This is
the formal skeleton onto which the metaphysical reading of §6.3 is laid (next
section). -/

section Forgetfulness

variable {Obs : Type*} [s : Setoid Obs]

/-- Forgetfulness constraint (F1), §2.2: distinct perspectives can share a
structural image. -/
def Forgetful : Prop := ∃ o₁ o₂ : Obs, o₁ ≠ o₂ ∧ proj o₁ = proj o₂

/-- **Non-structural facts exist under forgetfulness.** If `π` is forgetful,
some predicate on perspectives does not descend to the structural quotient:
no structural predicate `P'` on `Str` satisfies `P = P' ∘ π`. -/
theorem exists_nonstructural_of_forgetful (h : Forgetful (Obs := Obs)) :
    ∃ P : Obs → Prop, ∀ P' : Str Obs → Prop, P ≠ P' ∘ proj := by
  obtain ⟨o₁, o₂, hne, hpr⟩ := h
  refine ⟨fun o => o = o₁, fun P' hP => hne ?_⟩
  have e₁ : (o₁ = o₁) = P' (proj o₁) := congrFun hP o₁
  have e₂ : (o₂ = o₁) = P' (proj o₂) := congrFun hP o₂
  have hmid : P' (proj o₁) = P' (proj o₂) := congrArg P' hpr
  have hchain : (o₁ = o₁) = (o₂ = o₁) := e₁.trans (hmid.trans e₂.symm)
  have hcast : o₂ = o₁ := cast hchain rfl
  exact hcast.symm

end Forgetfulness

/-! ## 5. Metaphysical layer — ASSUMPTIONS, NOT THEOREMS (§3, §6)

Everything below depends on the paper's metaphysical premises. They are
recorded as explicit hypotheses/definitions so that the *conditional* shape of
the argument is machine-checked, while the verified core (§§1–4) stays clean.
**No global `axiom` is introduced here.** -/

namespace Metaphysics

section
variable {Obs : Type*} [s : Setoid Obs]

-- `Phenomenal o`: there is something it is like for actuality to obtain at
-- perspective `o` (§3.1). An opaque, ontologically primitive predicate — in
-- particular it is *not assumed* to descend to the structural quotient.
variable (Phenomenal : Obs → Prop)

/-- **Primitivism, OE-operative reading (premise, §3.1 + §6.3).**
Phenomenality can differ between two perspectives that share a structural
image — i.e. givenness can live in a fiber that `π` forgets. This is the
formal counterpart of "phenomenality is not defined away in structural terms";
the Ontological Closure Principle (§3.3) is what licenses reading primitivism
this way and blocks re-identifying the fiber-local remainder with a structural
rearrangement. -/
def PhenomenalIsFiberLocal : Prop :=
  ∃ o₁ o₂ : Obs, proj o₁ = proj o₂ ∧ (Phenomenal o₁ ↔ ¬ Phenomenal o₂)

/-- The fiber-locality premise makes `Phenomenal` a fiber-separating quantity:
it supplies two fiber-mates `o₁, o₂` whose phenomenal verdicts are forced to
differ. This is the *only* place the metaphysical premise does work; the no-go
conclusion is then read off the general core lemma. -/
theorem separates_of_phenomenalIsFiberLocal
    (h : PhenomenalIsFiberLocal Phenomenal) :
    SeparatesAFiber Phenomenal := by
  obtain ⟨o₁, o₂, hpr, hiff⟩ := h
  refine ⟨o₁, o₂, hpr, ?_⟩
  intro heq
  rw [heq] at hiff
  exact iff_not_self hiff

/-- **Limit of structure ≠ limit of actuality (conditional, §6.3).**
GIVEN that phenomenality is fiber-local, the predicate `Phenomenal` does not
descend to the structural quotient: no structural property captures it. Hence a
collapse of the *structural* invariants (`Collapses`) leaves the phenomenal
facts untouched — the structural limit is not a limit of actuality.

The proof is now a one-line specialization of the core no-go lemma
`no_factor_of_separates`: the metaphysical layer supplies the fiber separation,
the verified core supplies the fiber-blindness engine of §1. -/
theorem phenomenal_not_structural (h : PhenomenalIsFiberLocal Phenomenal) :
    ∀ P' : Str Obs → Prop, Phenomenal ≠ P' ∘ proj :=
  no_factor_of_separates
    (Q := Phenomenal)
    (separates_of_phenomenalIsFiberLocal (Phenomenal := Phenomenal) h)

end

end Metaphysics

/-! ## Axiom audit (run in your Mathlib environment)

Verified results of this audit (Lean 4.30.0, Mathlib `v4.30.0`):

§8.1 Core quotient/descent theorems — constructive modulo `Quot.sound`:
  `quotientTest`, `quotientTest_unique`, `not_invariant_of_separatesAFiber`
                                       →  `[Quot.sound]`
  `fiber_blind`, `no_factor_of_separates`,
  `no_objective_fiber_sensitive_quantity`,
  `exists_nonstructural_of_forgetful`, `time_degenerates`
                                       →  no axioms at all.

§8.2 Classical corollaries — `Classical.choice` enters via `by_cases`/`by_contra`:
  `quotient_dichotomy`, `quotient_dichotomy_strong`,
  `separatesAFiber_of_not_invariant`, `descends_iff_not_separatesAFiber`,
  `quotientTest_group` (also pulls classical group-theory machinery)
                                       →  `[propext, Classical.choice, Quot.sound]`

§8.3 Metaphysical conditional layer — kept constructive via `iff_not_self`:
  `separates_of_phenomenalIsFiberLocal`, `phenomenal_not_structural`
                                       →  no axioms at all. -/

-- §8.1 core
-- #print axioms OE.quotientTest
-- #print axioms OE.quotientTest_unique
-- #print axioms OE.fiber_blind
-- #print axioms OE.not_invariant_of_separatesAFiber
-- #print axioms OE.no_factor_of_separates
-- #print axioms OE.no_objective_fiber_sensitive_quantity
-- #print axioms OE.exists_nonstructural_of_forgetful
-- #print axioms OE.time_degenerates
-- §8.2 classical corollaries
-- #print axioms OE.separatesAFiber_of_not_invariant
-- #print axioms OE.quotient_dichotomy
-- #print axioms OE.quotient_dichotomy_strong
-- #print axioms OE.descends_iff_not_separatesAFiber
-- #print axioms OE.quotientTest_group
-- §8.3 metaphysical conditional layer
-- #print axioms OE.Metaphysics.separates_of_phenomenalIsFiberLocal
-- #print axioms OE.Metaphysics.phenomenal_not_structural

end OE

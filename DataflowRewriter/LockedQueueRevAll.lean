import DataflowRewriter.StateTransition
import Mathlib.Tactic

namespace DataflowRewriter

inductive Method where
  | enq (n : Nat)
  | unenq (n : Nat)
  | deq (n : Nat)
  | undeq (n : Nat)
  | unlock

structure ImpState where
  lock : Bool
  queue : Queue
  deriving Inhabited, Repr

inductive imp_step : ImpState → List Method → ImpState → Prop where
  | enq : ∀ s n,
    s.lock = false →
    imp_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | unenq : ∀ s n rst,
    s.lock = false →
    s.queue = rst ++ [n] →
    imp_step s [Method.unenq n] { s with queue := rst }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step s [Method.deq n] { s with queue := rst }
  | undeq : ∀ s n,
    imp_step s [Method.undeq n] { s with queue := n :: s.queue }
  | unlock : ∀ s,
    s.lock = true →
    imp_step s [Method.unlock] { s with lock := false }
  | lock : ∀ s,
    imp_step s [] { s with lock := true }
  | unlock_natural : ∀ s,
    s.queue = [] →
    imp_step s [] { s with lock := false }

instance ImpStateTransition : StateTransition Method ImpState where
  init := default
  step := imp_step

structure SpecState where
  queue : Queue
  deriving Inhabited, Repr

inductive spec_step : SpecState → List Method → SpecState → Prop where
  | enq : ∀ s n,
    spec_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | unenq : ∀ s n rst,
    s.queue = rst ++ [n] →
    spec_step s [Method.unenq n] { s with queue := rst }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step s [Method.deq n] { s with queue := rst }
  | undeq : ∀ s n,
    spec_step s [Method.undeq n] { s with queue := n :: s.queue }
  | unlock : ∀ s,
    spec_step s [Method.unlock] s

instance SpecStateTransition : StateTransition Method SpecState where
  init := default
  step := spec_step

infix:60 " ≺ " => @indistinguishable Method

inductive Method₂ where
  | enq (n : Nat)
  | deq (n : Nat)

inductive imp_step₂ : ImpState → List Method₂ → ImpState → Prop where
  | enq : ∀ s n,
    s.lock = false →
    imp_step₂ s [Method₂.enq n] { s with queue := s.queue ++ [n] }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step₂ s [Method₂.deq n] { s with queue := rst }
  | lock : ∀ s,
    imp_step₂ s [] { s with lock := true }
  | unlock_natural : ∀ s,
    s.queue = [] →
    imp_step₂ s [] { s with lock := false }

instance ImpStateTransition₂ : StateTransition Method₂ ImpState where
  init := default
  step := imp_step₂

inductive spec_step₂ : SpecState → List Method₂ → SpecState → Prop where
  | enq : ∀ s n,
    spec_step₂ s [Method₂.enq n] { s with queue := s.queue ++ [n] }
  | deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step₂ s [Method₂.deq n] { s with queue := rst }

instance SpecStateTransition₂ : StateTransition Method₂ SpecState where
  init := default
  step := spec_step₂

infix:60 " ≺₂ " => @indistinguishable Method₂

/--
Implementation of have with holes, which uses let first to create the definition
and then assigns it using `have` to remove the body, followed by clearing the
hypothesis.
-/
syntax (name := haveByLet) "have_hole " haveDecl : tactic

macro_rules
  | `(tactic| have_hole $id:haveId $bs* : $type := $proof) =>
    `(tactic| (let h $bs* : $type := $proof; have $id:haveId := h; clear h))

theorem spec_single_signal (s1 s2 : SpecState) (e1 : List Method)
  : s1 -[ e1 ]-> s2 → ∃ (e2 : Method), e1 = [e2] := by
  intro H; have H₂ := H; cases H <;> tauto

inductive match_methods : Method → Method₂ → Prop where
  | enq : ∀ n, match_methods (Method.enq n) (Method₂.enq n)
  | deq : ∀ n, match_methods (Method.deq n) (Method₂.deq n)

theorem spec_steps (s s' : SpecState) (e : List Method) (e' : List Method₂)
  : s -[ e ]-> s' → List.Forall₂ match_methods e e' → s -[ e' ]-> s' := by
  intro HF; have Heq := spec_single_signal _ _ _ HF; rcases Heq with ⟨ m, Heq ⟩; subst e
  intro HM; cases HM; rename_i m₂ l₂ Hm HF'; cases HF'; cases Hm <;> (cases HF; constructor; try assumption)

theorem spec_star_steps (s s' : SpecState) (e : List Method) (e' : List Method₂)
  : s -[ e ]*> s' → List.Forall₂ match_methods e e' → s -[ e' ]*> s' := by
  intro H; induction H generalizing e' with
  | refl s2 =>
    intro HF; cases HF; constructor
  | step s1 s2 s3 e1 e2 Hs1 _ IH =>
    intro HF; have Hs1' := Hs1; apply spec_single_signal at Hs1; rcases Hs1 with ⟨ e1', Hs1 ⟩; subst e1
    cases HF; rename_i m ml Hm HF; dsimp at *
    apply IH at HF
    have : m :: ml = [m] ++ ml := by dsimp
    rw [this]; constructor
    apply spec_steps; assumption
    repeat' first | assumption | constructor

theorem indis_less_methods (i : ImpState) (s : SpecState) :
  i ≺ s → i ≺₂ s := by
  unfold indistinguishable; intro H
  intro e i' Histep
  have Histep' := Histep
  cases Histep with
  | enq n a =>
    have_hole H₂ : i -[[Method.enq n]]-> _ := by tauto
    apply H at H₂
    rcases H₂ with ⟨ s', Hsstep ⟩
    exists s'; apply spec_star_steps <;> tauto
  | deq n rst a =>
    have_hole H₂ : i -[[Method.deq n]]-> _ := by
      constructor; assumption
    apply H at H₂
    rcases H₂ with ⟨ s', Hsstep ⟩
    exists s'; apply spec_star_steps <;> tauto
  | lock | unlock_natural _ => tauto

/--
We define phi with a few necessary extensions.  For example, we use
quantification for the `enq` case, so that we can handle any inputs and still
commute.  In addition to that, we have indistinguishability inside of the φ.
This is because it makes it easier to prove the `enq` case, because one knows
one just has indistinguishability.
-/
inductive φ : ImpState → SpecState → Prop where
  | base :
    φ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.enq n] i' →
    spec_step s [Method.enq n] s' →
    φ i s
  | unenq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.unenq n] i' →
    spec_step s [Method.unenq n] s' →
    φ i s
  | deq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.deq n] i' →
    spec_step s [Method.deq n] s' →
    φ i s
  | undeq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.undeq n] i' →
    spec_step s [Method.undeq n] s' →
    φ i s
  | unlock : ∀ i i' s s',
    i ≺ s →
    φ i' s' →
    imp_step i [Method.unlock] i' →
    spec_step s [Method.unlock] s' →
    φ i s
  | internal : ∀ i i' s,
    i ≺ s →
    φ i' s →
    imp_step i [] i' →
    φ i s

inductive φ₂ : ImpState → SpecState → Prop where
  | base :
    φ₂ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step₂ i [Method₂.enq n] i' →
    spec_step₂ s [Method₂.enq n] s' →
    φ₂ i s
  | deq : ∀ i i' s s' n,
    φ₂ i' s' →
    imp_step₂ i [Method₂.deq n] i' →
    spec_step₂ s [Method₂.deq n] s' →
    φ₂ i s
  | internal : ∀ i i' s,
    φ₂ i' s →
    imp_step₂ i [] i' →
    φ₂ i s

macro "solve_indistinguishable" t:tactic : tactic =>
  `(tactic| (unfold indistinguishable; intros _ _ a; have Hindimpstep := a; cases a
             <;> (try ((repeat' first | (apply star.refl; done) | apply star.plus_one | constructor | $t:tactic) <;> done))))

theorem φ₂_equal_queues i s : φ₂ i s → i.queue = s.queue := by
  intro H; induction H with
  | base => simp
  | enq i i' s s' n Hphi Histep Hsstep iH
  | deq i i' s s' n Hphi Histep Hsstep iH =>
    cases Histep; cases Hsstep; simp [*] at *; assumption
  | internal i i' s Hphi Histep iH =>
    cases Histep <;> (simp [*] at *; assumption)

theorem φ₂_indist i s :
  φ₂ i s → i ≺₂ s := by
  intro Hphi;
  have Heq := φ₂_equal_queues _ _ Hphi
  solve_indistinguishable fail
  case deq n rst a _Hstep =>
    constructor; apply star.plus_one; constructor
    rw [←Heq]; assumption

theorem empty_indistinguishable :
  (default : ImpState) ≺ (default : SpecState) := by
  unfold indistinguishable; intros e i' Himp
  cases Himp with
  | enq n a | undeq n | unlock => constructor; apply star.plus_one; constructor
  | deq n rst a | unenq n rst _ a => reduce at a; simp at a
  | lock | unlock_natural => constructor; apply star.refl

theorem φ_indistinguishable i s :
  φ i s → i ≺ s := by
  intros H; cases H with
  | base => apply empty_indistinguishable
  | _ => assumption

theorem invert_single_spec_step (s1 s2 : SpecState) (e : Method):
  s1 -[[e]]*> s2 → s1 -[[e]]-> s2 := by
  generalize Hthis : [e] = e'; intros Hs
  cases Hs with
  | refl => simp at Hthis
  | step s1' s2' s3' e1 e2 Hstep Hstar =>
    have Hthis' : e1 = [e] ∧ e2 = [] := by
      cases Hstep <;> (simp at *; tauto)
    cases Hthis'; subst e1; subst e2
    generalize Hother : [] = e' at Hstar
    cases Hstar with
   | step s1'' s2'' s3'' e1' e2' Hstep' Hstar' =>
      symm at Hother; rw [List.append_eq_nil] at Hother; cases Hother
      subst e1'; subst e2'; cases Hstep'
   | refl => assumption

theorem invert_single_spec_step₂ (s1 s2 : SpecState) (e : Method₂):
  s1 -[[e]]*> s2 → s1 -[[e]]-> s2 := by
  generalize Hthis : [e] = e'; intros Hs
  cases Hs with
  | refl => simp at Hthis
  | step s1' s2' s3' e1 e2 Hstep Hstar =>
    have Hthis' : e1 = [e] ∧ e2 = [] := by
      cases Hstep <;> (simp at *; tauto)
    cases Hthis'; subst e1; subst e2
    generalize Hother : [] = e' at Hstar
    cases Hstar with
   | step s1'' s2'' s3'' e1' e2' Hstep' Hstar' =>
      symm at Hother; rw [List.append_eq_nil] at Hother; cases Hother
      subst e1'; subst e2'; cases Hstep'
   | refl => assumption

open Lean Elab Meta Tactic

/--
Tactic to specialize all the hypotheses in the context that contain an binding
of that term in the first position.
-/
syntax (name := specializeAll) "specializeAll " term : tactic

@[tactic specializeAll] def specializeAllTactic : Tactic -- Syntax -> TacticM Unit
  | `(tactic| specializeAll $t:term) => withMainContext do
    let t ← elabTerm t none
    let termType ← inferType t
    let lctx ← getLCtx
    lctx.forM fun decl : LocalDecl => do
      -- First we check if the current hypothesis contains a binding of the same
      -- type as the input term in the first position.
      if (← forallTelescopeReducing decl.type fun vars _ => do
        if h : vars.size > 0 then
          isDefEq (← inferType vars[0]) termType
        else
          return false)
        -- We don't want to instantiate arrow types (only dependent types).
        && decl.type.arrow?.isNone
      then
        let e ← mkAppM' decl.toExpr #[t]
        -- We create a new assertion in the current goal and also infer the type
        -- of `e` again.  Instead we could generate the correct type as well.
        let mvarId ← (← getMainGoal).assert decl.userName (← inferType e).headBeta e
        let (_, mvarId) ← mvarId.intro1P
        let mvarId ← mvarId.tryClear decl.fvarId
        replaceMainGoal [mvarId]
      else
        return ()
  | _ => throwUnsupportedSyntax

def kAbstractMatches (expr t : Expr) : MetaM Bool := do
  try
    -- `==` does not work here because sometimes the term can be reduced I
    -- believe, in which case they won't 100% match.
    let abstr ← withAssignableSyntheticOpaque <| kabstract expr t
    not <$> (withAssignableSyntheticOpaque <| isDefEq abstr expr)
  -- isDefEq will error with unbound bvars, which is expected and means
  -- that the abstraction worked.
  catch _e =>
    return true

def findIndHyp : TacticM (FVarId × FVarId) := do
    -- First: Figure out which hypothesis is the top step and which is the
    -- inductive hypothesis.  This will be made with the assumption that the
    -- inductive hypothesis will contain the implementation step, implying a
    -- series of specification steps and the phi.
    let lctx ← getLCtx

    -- log m!"{repr (∃ s', s -[ e ]*> s' ∧ φ i' s')}"

    let mut ret := none

    for decl in lctx do
      -- Otherwise the theorem itself shows up in the declarations.
      if decl.isImplementationDetail then continue

      trace[debug] m!"(DECL) {decl.userName}: {decl.type}"

      -- This will match different step functions, which can then be used to
      -- find the inductive hypothesis.
      let (x, ind_hyp') ← withNewMCtxDepth do
        let (_, _, expr) ← forallMetaTelescopeReducing decl.type
        let t ← elabTermWithHoles (← `(imp_step₂ ?a ?b ?c)) none `createInductivePhi
        let s ← elabTerm (← `(imp_step₂ ?c ?d ?e)) none
        -- trace[debug] m!"T':: {t.fst}"
        -- trace[debug] m!"(DECL2): {expr}"
        -- trace[debug] m!"(DECL3): {repr expr}"
        trace[debug] m!"(MAGIC): {(← withAssignableSyntheticOpaque <| kabstract expr t.fst)}"
        if ← kAbstractMatches expr t.fst then
          let mut declId := false
          let mut ind_hyp : Array FVarId := #[]
          for decl' in lctx do
            if decl'.isImplementationDetail then continue

            -- Using `forallMetaTelescopeReducing` here is necessary because
            -- otherwise a new context is created that is not a `subPrefixOf`
            -- the previous context.  This means that meta variables cannot be
            -- instantiated in that context.
            let (lst, _, expr') ← forallMetaTelescopeReducing decl'.type
            match ← whnf expr' with
            | .app (.app (.const ``Exists _) _) _ =>

              trace[debug] m!"(LIST): {← sequence <| List.map (inferType ·) (lst.toList)}"
              for hyp in lst do
                trace[debug] m!"(MAGIC2): {(← withAssignableSyntheticOpaque <| kabstract (← inferType hyp) s)}"
                if ← kAbstractMatches (← inferType hyp) s then
                  declId := true
                  ind_hyp := ind_hyp.push decl'.fvarId
                trace[debug] m!"TYPE: {(← inferType hyp)} ::: {s}"
                trace[debug] m!"DECLUSERNAME: {decl'.userName}: {← inferType hyp}"
            | _ => pure ()
          return (declId, ind_hyp)
        else return (false, #[])
      if h : x ∧ ind_hyp'.size > 0 then
        ret := some (decl.fvarId, ind_hyp'[0])

    let some someret := ret
        | throwError "Could not find hypothesis"
    return someret

def findCurrentEvent : TacticM Expr := do
  let (.app (.app (.const ``Exists _) _) goalType) := (← getMainTarget).consumeMData
    | throwError "Not the right goal type"
  trace[debug] m!"goal: {goalType}"
  withNewMCtxDepth <| lambdaTelescope goalType fun _ars newGoalType => do
    let (t, ars) ← elabTermWithHoles (← `(@star SpecState Method _ ?a ?b ?c)) none `findCurrentEvent
    if ← kAbstractMatches newGoalType t then
      instantiateMVars (Expr.mvar ars[1]!)
    else throwError "Could not find event type in goal"

/--
Creates
-/
syntax (name := createInductivePhi) "create_ind_phi" : tactic

@[tactic createInductivePhi] def createInductivePhiTactic : Tactic
  | `(tactic| create_ind_phi) => withMainContext do
    let lctx ← getLCtx
    let (imp, ind) ← findIndHyp
    trace[debug] m!"Found : {(lctx.get! imp).userName} and {(lctx.get! ind).userName}"
    let e ← findCurrentEvent
    trace[debug] m!"FOUND: {e}"
    liftMetaTactic fun mvarId => do
      let ind_decl := lctx.get! ind
      let (ars, _, t) ← forallMetaTelescopeReducing ind_decl.type
      for x in ars do
        if ← isDefEq (← inferType x) (← inferType e) then
          x.mvarId!.assign e
      let e_t ← mkAppM' ind_decl.toExpr ars
      let mvarIdNew ← mvarId.assert ind_decl.userName t e_t
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      let mvarIdNew ← mvarIdNew.tryClear ind
      -- log m!"LOG: {repr ((← (sequence <| (mvarIdNew :: (ars.map (·.mvarId!)).toList.reverse).map (·.getKind))))}"
      let newMVars := (ars.map (·.mvarId!)).toList.reverse
      return mvarIdNew :: newMVars
  | _ => throwUnsupportedSyntax

elab "remImp " h:ident : tactic =>
  withMainContext do
    let some decl := (← getLCtx).findFromUserName? h.getId
      | throwErrorAt h "Not found"
    liftMetaTactic fun mvarId => do
      let (arrs, _, e) ← forallMetaTelescopeReducing decl.type
      let e_t ← mkAppM' decl.toExpr arrs
      let mvarIdNew ← mvarId.assert decl.userName e e_t
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      let mvarIdNew ← mvarIdNew.tryClear decl.fvarId
      return mvarIdNew :: (arrs.map (·.mvarId!)).toList

elab "cases_transitions" : tactic =>
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      let (arr, _, expr) ← forallMetaTelescopeReducing decl.type
      let sig1 ← elabTerm (← `(imp_step₂ _ _ _)) none
      let sig2 ← elabTerm (← `(spec_step₂ _ _ _)) none
      let sig3 ← elabTerm (← `(@StateTransition.step Method₂ SpecState _ _ [_] _)) none
      if (arr.size == 0 && ((← kAbstractMatches expr sig1) ||
                            (← kAbstractMatches expr sig2) ||
                            (← kAbstractMatches expr sig3))) then
        trace[debug] m!"Found: {arr}, {expr}"
        evalTactic (← `(tactic| cases $(mkIdent <| decl.userName):term))

elab "propagate_eq" : tactic =>
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      let (_, _, expr) ← forallMetaTelescopeReducing decl.type
      let sig ← elabTerm (← `(_ = _)) none
      if (← kAbstractMatches expr sig) then
        evalTactic (← `(tactic| try subst $(mkIdent <| decl.userName):term))
        trace[debug] m!"Found: {expr}"

elab "findDownEvent" : tactic =>
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      -- find the base i_ne through φ
      let (_, _, expr) ← forallMetaTelescopeReducing decl.type
      let sig ← elabTerm (← `(φ₂ _ _)) none
      if (← kAbstractMatches expr sig) then
        match expr with
        | .app (.app _ i) _ =>
          for decl' in lctx do
            if decl'.isImplementationDetail then continue
            let (lst, _, expr') ← forallMetaTelescopeReducing decl'.type
            match ← whnf expr' with
            | .app (.app (.const ``Exists _) _) _ =>
              let mut matched := false
              let s ← elabTermWithHoles (← `(imp_step₂ _ _ _)) none `findDownEvent true
              s.snd.head!.assign i
              for arg in lst do
                if ← kAbstractMatches (← inferType arg) s.fst then
                  matched := true
              if matched then
                for decl' in lctx do
                  if decl'.isImplementationDetail then continue
                  let s ← elabTerm (← `(imp_step₂ _ _ _)) none
                  -- get the down left event
                  if (← kAbstractMatches decl'.type s) then
                    match decl'.type with
                    | .app (.app (.app _ _) m) i' =>
                      if !(← kAbstractMatches i i') then
                        let t ← elabTermWithHoles (← `(imp_step₂ _ _ _)) none `findDownEvent true
                        t.snd[0]!.assign i
                        t.snd[1]!.assign m
                        t.snd[2]!.setKind .natural
                        let v ← mkFreshExprMVar (some t.fst)
                        liftMetaTactic fun mvarId => do
                          let mvarIdNew ← mvarId.assert (Name.mkSimple "c1") t.fst v
                          let (_, mvarIdNew) ← mvarIdNew.intro1P
                          --let mvarIdNew ← mvarIdNew.tryClear decl.fvarId
                          logInfo m!"ISSYNTHETIC: {MetavarKind.isSyntheticOpaque <| ← t.snd[0]!.getKind}"
                          return [v.mvarId!] ++ [mvarIdNew]
                    | _ => pure ()
            | _ => pure ()
        | _ => throwUnsupportedSyntax

-- syntax (name := remImp) "remImp " ident : tactic

-- @[tactic remImp] def remImpTactic : Tactic
--   | `(tactic| remImp $h:ident) => withMainContext do
--     let some decl := (← getLCtx).findFromUserName? h.getId
--       | throwErrorAt h "Not found"
--     liftMetaTactic fun mvarId => do
--       let (arrs, _, e) ← forallMetaTelescopeReducing decl.type
--       let e_t ← mkAppM' decl.toExpr arrs
--       let mvarIdNew ← mvarId.assert decl.userName e e_t
--       let (_, mvarIdNew) ← mvarIdNew.intro1P
--       let mvarIdNew ← mvarIdNew.tryClear decl.fvarId
--       return mvarIdNew :: (arrs.map (·.mvarId!)).toList
--   | _ => throwUnsupportedSyntax

theorem enough :
  ∀ i s, φ i s →
    ∀ e i', imp_step i e i' →
      ∃ s', star s e s' ∧ φ i' s' := by
  intro i s h;
  induction h with
  | base =>
    intro e i' Himp
    cases Himp with
    | enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.unenq
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | unenq n rst a b => simp at b
    | deq n rst a => simp at a
    | undeq n =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.deq
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.unlock
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp
        · constructor
    | unlock a =>
      simp at a
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.base
  | enq i i_ne s s_ne n Hindist Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ.unenq
      · solve_indistinguishable fail
        · sorry
        · sorry
      · apply φ.enq <;> assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | unenq n' rst Hl Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst ileft; subst iright
      apply φ.enq
      · solve_indistinguishable fail
        · sorry
        · sorry
      · apply φ.enq <;> assumption
      · generalize Hi : ({ lock := false, queue := rst } : ImpState) = i'';
        have : false = i''.lock := by subst i''; rfl
        rw [this]
        have : rst = i''.queue := by subst i''; rfl
        rw [this]
        constructor; symm; assumption
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
  | _ => sorry

-- theorem l_empty (l : List Nat) : [] = l → True := by
--   generalize H : ([] : List Nat) = l' at *

theorem empty_spec (s s' : SpecState) :
  s -[ ([] : List Method) ]*> s' → s = s' := by
  intro H; generalize Hempty : ([] : List Method) = l at H
  induction H; rfl
  rename_i s1 s2 s3 e1 e2 Hs1 Hs2 He
  rw [List.nil_eq_append] at Hempty
  cases Hempty; subst e1; subst e2
  cases Hs1

theorem empty_spec₂ (s s' : SpecState) :
  s -[ ([] : List Method₂) ]*> s' → s = s' := by
  intro H; generalize Hempty : ([] : List Method₂) = l at H
  induction H; rfl
  rename_i s1 s2 s3 e1 e2 Hs1 Hs2 He
  rw [List.nil_eq_append] at Hempty
  cases Hempty; subst e1; subst e2
  cases Hs1

theorem enough₂ :
  ∀ i s, φ₂ i s →
    ∀ e i', imp_step₂ i e i' →
      ∃ s', star s e s' ∧ φ₂ i' s' := by
  intro i s h;
  induction h with
  | base =>
    intro e i' Himp
    cases Himp with
    | enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ₂.deq
        · apply φ₂.base
        · constructor; simp; rfl
        · constructor; simp
    | deq n rst a => simp at a
    | lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ₂.internal
        · apply φ₂.base
        · constructor; simp
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ₂.base
  | enq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    sorry
    -- intro e i_sw HimpDown
    -- have HspecDown := HimpDown
    -- have Hphi_base : φ₂ i s := by
    --   apply φ₂.enq <;> assumption
    -- have Hindist := φ₂_indist _ _ Hphi_base
    -- apply Hindist at HspecDown
    -- cases HspecDown; rename_i s' HspecDown
    -- exists s'; and_intros; assumption
    -- have HimpDown' := HimpDown
    -- cases HimpDown' with
    -- | enq n' lock =>
    --   apply φ₂.deq (n := n')
    --   · apply φ₂.enq (n := n)
    --     · exact Hphi
    --     · assumption
    --     · assumption
    --   · constructor <;> simp [*]
    --   · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    -- | deq n' rst a =>
    --   rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
    --   apply φ₂.undeq
    --   · assumption
    --   · constructor
    --   · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    -- | lock =>
    --   rcases i with ⟨ ileft, iright ⟩; simp at *
    --   apply empty_spec at HspecDown; subst s
    --   cases ileft
    --   · apply φ₂.unlock
    --     · assumption
    --     · constructor; simp
    --     · constructor
    --   · assumption
    -- | unlock_natural Hq =>
    --   rcases i with ⟨ ileft, iright ⟩; simp at *
    --   apply empty_spec at HspecDown; subst s
    --   cases ileft <;> try assumption
    --   apply φ₂.internal
    --   · assumption
    --   · constructor
  | deq i i_ne s s_ne n Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.deq <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n' lock =>
      set_option trace.debug true in
      findDownEvent
      · apply imp_step₂.enq
        · apply i_ne.lock
        · apply (i_ne.queue ++ [n'])

      let H' : imp_step₂ i_ne [Method₂.enq n'] _ := by
        constructor; cases_transitions; simp [*]

      specialize iH [Method₂.enq n'] { lock := i_ne.lock, queue := i_ne.queue ++ [n'] }
      remImp iH
      rcases iH with ⟨ s_se, H, phi ⟩
      · apply φ₂.deq
        · exact phi
        · cases_transitions; simp [*] at *
          constructor; rfl
        · apply invert_single_spec_step₂ at H
          apply invert_single_spec_step₂ at HspecDown
          cases_transitions
          constructor; simp [*] at *
      · cases_transitions; constructor; simp [*]
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      cases HimpRight
      rename_i rst H
      simp [*] at *
      cases H
      rename_i right left; subst right left
      cases HspecRight
      rename_i rst_s H
      apply invert_single_spec_step₂ at HspecDown
      cases HspecDown
      rename_i right left
      simp [*] at *
      subst left
      assumption
    | lock =>
      set_option trace.debug true in
      have Htest : ∃ i, imp_step₂ i_ne [] i := by
        constructor
        apply imp_step₂.lock
      create_ind_phi
      rcases i with ⟨ lock, queue ⟩; simp at *
      apply empty_spec₂ at HspecDown; subst s
      cases Htest
      rename_i i_se H
      specialize iH [] i_se
      remImp iH
      cases_transitions
      propagate_eq
      cases lock
      · rcases iH with ⟨ s_se, H, phi ⟩
        apply empty_spec₂ at H; subst s_se
        apply φ₂.deq
        · exact phi
        · constructor; simp; rfl
        · assumption
      · assumption
      · admit
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec₂ at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor
  | internal i i_ne s Hphi HimpRight iH =>
    intro e i_sw HimpDown
    have HspecDown := HimpDown
    have Hphi_base : φ₂ i s := by
      apply φ₂.internal <;> assumption
    have Hindist := φ₂_indist _ _ Hphi_base
    apply Hindist at HspecDown
    cases HspecDown; rename_i s' HspecDown
    exists s'; and_intros; assumption
    have HimpDown' := HimpDown
    cases HimpDown' with
    | enq n lock =>
      apply φ₂.unenq
      · assumption
      · constructor <;> [simp [*]; rfl]
      · apply invert_single_spec_step at HspecDown; cases HspecDown; constructor; simp
    | deq n' rst a =>
      rcases i with ⟨ ileft, iright ⟩; simp at *; subst iright
      apply φ₂.undeq
      · assumption
      · constructor
      · apply invert_single_spec_step at HspecDown; cases HspecDown; cases s; rename_i Ha; simp at Ha; rw [Ha]; constructor
    | lock =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft
      · apply φ₂.unlock
        · assumption
        · constructor; simp
        · constructor
      · assumption
    | unlock_natural Hq =>
      rcases i with ⟨ ileft, iright ⟩; simp at *
      apply empty_spec at HspecDown; subst s
      cases ileft <;> try assumption
      apply φ₂.internal
      · assumption
      · constructor

theorem φ₂_empty : φ₂ default default := by constructor

theorem enough₂_star (i i': ImpState) (s : SpecState) (e : List Method):
  φ₂ i s → star i e i' →
  ∃ s', star s e s' ∧ φ₂ i' s' := by
  intro Hphi Hstar; induction Hstar generalizing s with
  | refl => exists s; and_intros; constructor; assumption
  | step s1 s2 s3 e1 e2 Hs1 Hs2 iH =>
    apply enough₂ at Hs1 <;> try assumption
    rcases Hs1 with ⟨ a, b, c ⟩
    apply iH at c
    rcases c with ⟨ c, d, e ⟩
    exists c; and_intros; apply star.trans_star <;> assumption
    assumption

-- theorem refinement (i : ImpState) (e : List Method₂) :
--   default -[ e ]*> i →
--   ∃ s : SpecState, default -[ e ]*> s ∧ i ≺₂ s := by
--   intro H
--   have H' := enough₂_star _ _ _ _ φ₂_empty H

end DataflowRewriter

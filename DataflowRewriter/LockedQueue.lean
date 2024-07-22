import DataflowRewriter.StateTransition
import Mathlib.Tactic

namespace DataflowRewriter

inductive Method where
  | enq (n : Nat)
  | deq (n : Nat)
  | lock
  | unlock

structure ImpState where
  lock : Bool
  queue : Queue
  deriving Inhabited, Repr

inductive imp_step : ImpState → List Method → ImpState → Prop where
  | handle_enq : ∀ s n,
    s.lock = false →
    imp_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | handle_deq : ∀ s n rst,
    s.queue = n :: rst →
    imp_step s [Method.deq n] { s with queue := rst }
  | handle_lock : ∀ s,
    imp_step s [Method.lock] { s with lock := true }
  | handle_unlock : ∀ s,
    imp_step s [Method.unlock] { s with lock := false }
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
  | handle_enq : ∀ s n,
    spec_step s [Method.enq n] { s with queue := s.queue ++ [n] }
  | handle_deq : ∀ s n rst,
    s.queue = n :: rst →
    spec_step s [Method.deq n] { s with queue := rst }
  | handle_lock : ∀ s,
    spec_step s [Method.lock] s
  | handle_unlock : ∀ s,
    spec_step s [Method.unlock] s

instance SpecStateTransition : StateTransition Method SpecState where
  init := default
  step := spec_step

infix:60 " ≺ " => @indistinguishable Method

/-- 
We define phi with a few necessary extensions.  For example, we use
quantification for the `enq` case, so that we can handle any inputs and still
commute.  In addition to that, we have indistinguishability inside of the φ.
This is because
-/
inductive φ : ImpState → SpecState → Prop where
  | base :
    φ ⟨false, []⟩ ⟨[]⟩
  | enq : ∀ i (i' : Nat → ImpState) s (s' : Nat → SpecState),
    (∀ n, i' n = { i with queue := i.queue ++ [n] }) →
    (∀ n, s' n = { s with queue := s.queue ++ [n] }) →
    i ≺ s → 
    (∀ n, φ (i' n) (s' n)) →
    (∀ n, imp_step i [Method.enq n] (i' n)) →
    (∀ n, spec_step s [Method.enq n] (s' n)) →
    φ i s
  | deq : ∀ i i' s s' n,
    i ≺ s →
    φ i' s' →
    imp_step i [Method.deq n] i' →
    spec_step s [Method.deq n] s' →
    φ i s
  | unlock : ∀ i i' s s',
    i ≺ s →
    φ i' s' →
    imp_step i [Method.unlock] i' →
    spec_step s [Method.unlock] s' →
    φ i s
  | lock : ∀ i i' s s',
    i ≺ s →
    φ i' s' →
    imp_step i [Method.lock] i' →
    spec_step s [Method.lock] s' →
    φ i s
  | internal : ∀ i i' s,
    i ≺ s →
    φ i' s →
    imp_step i [] i' →
    φ i s

theorem empty_indistinguishable :
  (default : ImpState) ≺ (default : SpecState) := by
  unfold indistinguishable; intros e i' Himp
  cases Himp with
  | handle_enq n a | handle_lock | handle_unlock => constructor; apply star.plus_one; constructor
  | handle_deq n rst a => simp at a
  | unlock_natural => constructor; apply star.refl

theorem φ_indistinguishable i s :
  φ i s → i ≺ s := by
  intros H; induction H with
  | base => apply empty_indistinguishable
  | _ => assumption

theorem φ_length i s :
  φ i s → i.queue.length = s.queue.length := by
  intros H; induction H with
  | base => simp
  | enq i i_ne s s_ne i_wf s_wf _ _ _ _ Hlist =>
    specialize Hlist 0
    specialize i_wf 0
    specialize s_wf 0
    rw [i_wf,s_wf] at Hlist
    simp at Hlist; assumption
  | deq i i' s s' n _ Hphi Himp Hspec Hlist
  | unlock i i' s s' _ Hphi Himp Hspec Hlist
  | lock i i' s s' _ Hphi Himp Hspec Hlist =>
    cases Himp; cases Hspec; simp [*]
  | internal i i' s _ Hphi Himp Hlist =>
    cases Himp; assumption

macro "solve_indistinguishable" t:tactic : tactic => 
  `(tactic| (unfold indistinguishable; intros _ _ a; have Hindimpstep := a; cases a 
             <;> (try ((repeat' first | (apply star.refl; done) | apply star.plus_one | constructor | $t:tactic) <;> done))))

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

open Lean Elab Meta Tactic

/--
Tactic to specialize all the hypotheses in the context that contain an binding
of that term in the first position.
-/
syntax (name := specializeAll) "specializeAll " term : tactic

@[tactic specializeAll] def specializeAllTactic : Tactic
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
    let _ ← withAssignableSyntheticOpaque <| kabstract expr t
    if not (← withAssignableSyntheticOpaque <| isDefEq (← kabstract expr t) expr) then
      return true
    else
      return false
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
        let t ← elabTermWithHoles (← `(imp_step ?a ?b ?c)) none `createInductivePhi
        let s ← elabTerm (← `(imp_step ?c ?d ?e)) none
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
      let mvarIdNew ← mvarId.define ind_decl.userName t e_t
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      sequence <| (mvarIdNew :: (ars.map (·.mvarId!)).toList.reverse).map (·.tryClear ind)
  | _ => throwUnsupportedSyntax

/--
Implementation of have with holes, which uses let first to create the definition
and then assigns it using `have` to remove the body, followed by clearing the
hypothesis.
-/
syntax (name := haveByLet) "have_hole " haveDecl : tactic

macro_rules
  | `(tactic| have_hole $id:haveId $bs* : $type := $proof) => 
    `(tactic| (let h $bs* : $type := $proof; have $id:haveId := h; clear h))
set_option pp.all true
theorem enough :
  ∀ i s, φ i s→ 
    ∀ e i', imp_step i e i' → 
      ∃ s', star s e s' ∧ φ i' s' := by
  intro i s h;
  induction h with
  | base =>
    intro e i' Himp
    cases Himp with
    | handle_enq n a =>
      simp; exists ⟨[n]⟩; and_intros
      · apply step_one; constructor
      · apply φ.deq
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor; simp; rfl
        · constructor; simp
    | handle_deq n rst a => simp at a
    | handle_lock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.plus_one; constructor
      · apply φ.unlock
        · solve_indistinguishable (simp [*] at *)
        · apply φ.base
        · constructor
        · constructor
    | handle_unlock =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.plus_one; constructor
      · apply φ.base
    | unlock_natural a =>
      simp; exists ⟨[]⟩; and_intros
      · apply star.refl
      · apply φ.base
  | enq i i_ne s s_ne i_wf s_wf Hindist Hphi HimpRight HspecRight iH =>
    intro e i_sw HimpDown
    have HimpDown' := HimpDown
    cases HimpDown with
    | handle_enq n' Hlock =>
      exists { s with queue := s.queue ++ [n'] }; 
      have Hphi' : φ { lock := i.lock, queue := i.queue ++ [n'] } { queue := s.queue ++ [n'] } := by rw [←i_wf,←s_wf]; apply Hphi
      and_intros
      · apply star.plus_one; constructor
      · assumption
    | handle_deq n' rst Hqueue =>
      create_ind_phi; rotate_left
      specializeAll ?n
      apply imp_step.handle_deq
      run_tac do
        withAssignableSyntheticOpaque <| evalTactic (← `(tactic| apply imp_step.handle_deq))
      
      rw [i_wf, Hqueue]; constructor; simp; rfl
      have_hole Himp2 : ∀ n, imp_step (i_ne n) [Method.deq n'] _ := by
        
      simp at *
      -- have_hole iH' : ∀ n, ∃ s', s_ne n -[ [Method.deq n'] ]*> s' ∧ φ { lock := i.lock, queue := rst ++ [n] } s' := by
      --   intro n''; apply iH
      --   apply Himp2
      have HimpDown'' := HimpDown'
      apply Hindist at HimpDown'
      rcases HimpDown' with ⟨ s_sw, HspecDown' ⟩
      exists s_sw; and_intros <;> try assumption
      have_hole HimpDownR : ∀ n, imp_step (i_ne n) [Method.deq n'] _ := by
        intro n
        constructor
        rw [i_wf]; simp; rw [Hqueue]; rfl
      have hfinalphi: ∀ n, φ { lock := i.lock, queue := rst ++ [n] } { queue := s_sw.queue ++ [n] } := by
        intro n
        specializeAll n
        --specializeAll 0
        apply iH at HimpDownR
        rcases HimpDownR with ⟨ s_se, HspecRightD, Hphi_se ⟩
        rw [s_wf] at *; rw [i_wf] at *
        clear i_wf; clear s_wf
        simp at Hphi_se
        apply invert_single_spec_step at HspecDown'
        rcases HspecDown' with _ | ⟨ _, rst', Ha ⟩
        apply invert_single_spec_step at HspecRightD
        rcases HspecRightD with _ | ⟨ _, rst'', Ha' ⟩
        simp only [*] at *
        have : rst' ++ [n] = rst'' := by cases Ha'; dsimp
        subst rst''; assumption
      apply φ.enq
      · intros; rfl
      · intros; rfl
      · solve_indistinguishable fail
        specialize hfinalphi 0
        apply φ_indistinguishable at hfinalphi
        unfold indistinguishable at *
        rename_i n rst' a Hindimpstep
        have_hole : ({ lock := i.lock, queue := rst ++ [0] } : ImpState) -[ [Method.deq n] ]-> _ := by
          constructor; simp only at a; rw [a]; rfl
        apply hfinalphi at this
        rcases this with ⟨ hns, H ⟩
        apply invert_single_spec_step at H
        rcases H with _ | ⟨ _, rst''', Ha'' ⟩ | _
        simp at *
        generalize Hgen : s_sw.queue = e at *
        cases e
        . simp at *; cases Ha''; subst n; subst rst'''
          have : φ i s := φ.enq i i_ne s s_ne i_wf s_wf Hindist Hphi HimpRight HspecRight
          apply φ_length at this
          rcases HimpDown'' with _ | ⟨ _, _, c ⟩
          subst rst
          apply invert_single_spec_step at HspecDown'
          cases HspecDown'; simp at *
          rename_i rst'''' a''''
          subst rst''''; rw [a''''] at this
          rw [Hqueue] at this; simp at this
        · simp at *; cases Ha''; subst n; subst rst'''
          (repeat' first | apply star.plus_one | rw [← Hgen] | constructor)
      · assumption
      · intros; constructor; specialize HimpRight 0; 
        generalize Hother : i_ne 0 = i' at *; cases HimpRight; simp [*]
      . intros; constructor
    | handle_lock => sorry
    | handle_unlock => sorry
    | unlock_natural => sorry
  | _ => sorry

end DataflowRewriter

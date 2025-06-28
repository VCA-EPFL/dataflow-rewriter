/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Module
import Graphiti.Simp
import Graphiti.ExprHigh
import Graphiti.AssocList.Basic
import Graphiti.TypeExpr
import Graphiti.Environment

open Batteries (AssocList)

namespace Graphiti.CombModule

abbrev Val := Nat
abbrev Reg := Nat

structure Context where
  memory : AssocList Reg Val
  deriving Inhabited

def update_loc (loc: Reg) (val: Val) (c: Context) : Context :=
  ⟨c.memory.cons loc val⟩

inductive Aexp where
  | lit : Val → Aexp
  | var : Reg → Aexp
  | add : Aexp → Aexp → Aexp

inductive Bexp where
  | true : Bexp
  | false : Bexp
  | eq : Aexp → Aexp → Bexp
  | lt : Aexp → Aexp → Bexp
  | and : Bexp → Bexp → Bexp
  | or : Bexp → Bexp → Bexp
  | not : Bexp → Bexp

inductive Com where
  | skip : Com
  | assign : Reg → Aexp → Com
  | seq : Com → Com → Com
  | cond : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  | assert : Bexp → Com

namespace Semantics

inductive Aexp.sem : Context → Aexp → Val → Prop where
  | lit {c n} : Aexp.sem c (Aexp.lit n) n
  | var {c y r} : c.memory.find? r = some y → Aexp.sem c (Aexp.var r) y
  | add {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Aexp.sem c (Aexp.add a b) (v + v')

inductive Bexp.sem : Context → Bexp → Bool → Prop where
  | true {c} : Bexp.sem c Bexp.true Bool.true
  | false {c} : Bexp.sem c Bexp.false Bool.false
  | eq {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Bexp.sem c (Bexp.eq a b) (v = v')
  | lt {c a v b v'} : Aexp.sem c a v → Aexp.sem c b v' → Bexp.sem c (Bexp.lt a b) (v < v')
  | and {c a v b v'} : Bexp.sem c a v → Bexp.sem c b v' → Bexp.sem c (Bexp.and a b) (v && v')
  | or {c a v b v'} : Bexp.sem c a v → Bexp.sem c b v' → Bexp.sem c (Bexp.or a b) (v || v')
  | not {c a v} : Bexp.sem c a v → Bexp.sem c (Bexp.not a) (¬ v)

structure State where
  context : Context
  command : Com

inductive Com.sem : Context → Com → Context → Prop where
  | skip {c} : Com.sem c Com.skip c
  | assign {c e v r} : Aexp.sem c e v → Com.sem c (Com.assign r e) (update_loc r v c)
  | seq {c s1 c' s2 c''} : Com.sem c s1 c' → Com.sem c' s2 c'' → Com.sem c (Com.seq s1 s2) c''
  | cond_true {c b t c' f} : Bexp.sem c b True → Com.sem c t c' → Com.sem c (Com.cond b t f) c'
  | cond_false {c b t c' f} : Bexp.sem c b False → Com.sem c f c' → Com.sem c (Com.cond b t f) c'
  | while_false {c b a} : Bexp.sem c b False → Com.sem c (Com.while b a) c
  | while_true {c b a c'} : Bexp.sem c b True → Com.sem c (Com.seq a (Com.while b a)) c' → Com.sem c (Com.while b a) c'
  | assert_true {c b} : Bexp.sem c b True → Com.sem c (Com.assert b) c

end Semantics

namespace Denotation

def moduleGen (f : Context → Option Context) : StringModule (Option Context) :=
  NatModule.stringify {
    inputs := [(0, ⟨ Context, fun
      | .none, s, .some c' => f s = .some c'
      | _, _, _ => False ⟩)].toAssocList,
    outputs := [(0, ⟨ Context, fun
      | .some c, s, .none => s = c
      | _, _, _ => False ⟩)].toAssocList,
    init_state := λ s => s = default
  }

-- def Com.toGraph : Com → ExprLow String
-- | skip c => .base ⟨[(0, 0)].toAssocList, [(0, 0)].toAssocList⟩ "Skip"
-- | assign r a => .base ⟨[(0, 0)].toAssocList, [(0, 0)].toAssocList⟩ "Assign"
-- | seq s1 s2 =>
-- | cond_true {c b t c' f} : Bexp.sem c b True → Com.sem c t c' → Com.sem c (Com.cond b t f) c'
-- | cond_false {c b t c' f} : Bexp.sem c b False → Com.sem c f c' → Com.sem c (Com.cond b t f) c'
-- | while_false {c b a} : Bexp.sem c b False → Com.sem c (Com.while b a) c
-- | while_true {c b a c'} : Bexp.sem c b True → Com.sem c (Com.seq a (Com.while b a)) c' → Com.sem c (Com.while b a) c'
-- | assert b => .base ⟨[(0, 0)].toAssocList, [(0, 0)].toAssocList⟩ "Assert"

end Denotation

end Graphiti.CombModule

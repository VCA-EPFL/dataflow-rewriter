/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.ModuleReduction
import DataflowRewriter.ExprLow
import DataflowRewriter.ExprLowLemmas

namespace DataflowRewriter.Examples.Noc

class NocParam where
  Data  : Type    -- Type of data transmitted over the Noc
  DataS : String  -- String representation of Data
  netsz : Nat     -- Network Size (Total number of router)
  len   : Nat
  HLen  : netsz = len * len

variable [P : NocParam]

@[simp] abbrev RouterID := Nat -- TODO: Should this be a Fin P.netsz ?

structure FlitHeader : Type :=
  dst : RouterID

def FlitHeaderS : String :=
  s!"FlitHeader {P.netsz}"

@[simp] abbrev Flit := P.Data × FlitHeader

@[simp] abbrev Dir      := Nat
@[simp] abbrev DirLocal := 0
@[simp] abbrev DirWest  := 1
@[simp] abbrev DirEast  := 2
@[simp] abbrev DirNorth := 3
@[simp] abbrev DirSouth := 4

@[simp] abbrev Arbiter := (src dst : RouterID) → Option Dir

def get_x (rId : RouterID) : Nat := rId.mod P.len

def get_y (rId : RouterID) : Nat := rId.div P.len

theorem get_xy_correct {a b : RouterID} (Hx : get_x a = get_x b) (Hy : get_y a = get_y b) :
   a = b := by
    dsimp [get_x] at Hx
    dsimp [get_y] at Hy
    sorry -- Annoying

def rid_of_xy (x y : Nat) : RouterID :=
  y * P.len + x

theorem rid_of_xy_corret {a : RouterID} :
  rid_of_xy (get_x a) (get_y a) = a := by
    sorry

def arbiter_xy : Arbiter := λ src dst =>
  let src_x := get_x src
  let src_y := get_y src
  let dst_x := get_x dst
  let dst_y := get_y dst
  if src_x == dst_x && src_y == dst_y then .some DirLocal
  else if src_x < dst_x then .some DirWest
  else if dst_x < src_x then .some DirEast
  else if src_y < dst_y then .some DirNorth
  else if dst_y < src_y then .some DirSouth
  else .none

theorem arbiter_xy_correct {rId dst : RouterID} :
  arbiter_xy rId dst = DirLocal → rId = dst := by
    dsimp [arbiter_xy]
    intros H
    cases Heq : (get_x rId == get_x dst && get_y rId == get_y dst)
    <;> rw [Heq] at H <;> dsimp at H
    · aesop
    · simp only [Bool.and_eq_true, beq_iff_eq] at Heq
      obtain ⟨HeqX, HeqY⟩ := Heq
      apply get_xy_correct HeqX HeqY

end DataflowRewriter.Examples.Noc

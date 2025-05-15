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
  netsz : Nat     -- Network Size (Number of router)

variable [P : NocParam]

@[simp] abbrev RouterID := Nat -- TODO: Should this be a Fin P.netsz ?

structure FlitHeader : Type :=
  dst : RouterID

def FlitHeaderS : String :=
  s!"FlitHeader {P.netsz}"

@[simp] abbrev Flit := P.Data × FlitHeader

-- Mesh ------------------------------------------------------------------------

class MeshParam where
  len   : Nat
  Hlen  : len * len = P.netsz   -- We only consider square network for now

variable [MP : MeshParam]

@[simp] abbrev Dir      := Nat  -- TODO: Should this be a Fin ?
@[simp] abbrev DirLocal := 0
@[simp] abbrev DirWest  := 1
@[simp] abbrev DirEast  := 2
@[simp] abbrev DirNorth := 3
@[simp] abbrev DirSouth := 4

-- If a packet is in router `src` and want to go to `dst`, which direction
-- should it go to?
-- NOTE: The `Dir` is actually dependent of the mesh topology
@[simp] abbrev Arbiter := (src dst : RouterID) → Option Dir

def MeshGetX (rId : RouterID) : Nat := rId.mod MP.len

def MeshGetY (rId : RouterID) : Nat := rId.div MP.len

theorem MeshGetXY_correct {a b : RouterID} (Hx : MeshGetX a = MeshGetX b) (Hy : MeshGetY a = MeshGetY b) :
   a = b := by sorry

def MeshRIdOfXY (X Y : Nat) :=
  Y * MP.len + X

theorem MeshRIdOfXY_correct {a : RouterID} :
  MeshRIdOfXY (MeshGetX a) (MeshGetY a) = a := by
    sorry

-- TODO: We want a theorem saying that for any rId < P.netsz, then
-- MeshRIdOfXY (MeshGetX i) (MeshGetY i) = i

def arbiterXY : Arbiter := λ src dst =>
  let src_x := MeshGetX src
  let src_y := MeshGetY src
  let dst_x := MeshGetX dst
  let dst_y := MeshGetY dst
  if src_x == dst_x && src_y == dst_y then .some DirLocal
  else if src_x < dst_x then .some DirWest
  else if dst_x < src_x then .some DirEast
  else if src_y < dst_y then .some DirNorth
  else if dst_y < src_y then .some DirSouth
  else .none

theorem arbiterXY_correct {rId dst : RouterID} :
  arbiterXY rId dst = DirLocal → rId = dst := by
    dsimp [arbiterXY]
    intros H
    cases Heq : (MeshGetX rId == MeshGetX dst && MeshGetY rId == MeshGetY dst)
    · rw [Heq] at H; dsimp at H
      sorry -- Contradiction, a bit annoying but true (Can prove with aesop)
    · rw [Heq] at H; dsimp at H
      simp only [Bool.and_eq_true, beq_iff_eq] at Heq
      obtain ⟨HeqX, HeqY⟩ := Heq
      apply MeshGetXY_correct HeqX HeqY

end DataflowRewriter.Examples.Noc

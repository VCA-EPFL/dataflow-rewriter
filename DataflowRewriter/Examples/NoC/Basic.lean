/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

namespace DataflowRewriter.Examples.NoC

class NocParam where
  Data  : Type     -- Type of data transmitted over the NoC
  DataS : String  -- String representation of Data
  netsz : Nat     -- Network Size (Number of router)

variable [P : NocParam]

@[simp] abbrev RouterID := Nat

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

-- If a packet is in router `src` and want to go to `dst`, which direction
-- should it go to?
def Arbiter := (src : RouterID) → (dst : RouterID) → Option Dir

end DataflowRewriter.Examples.NoC

/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

namespace DataflowRewriter.NoC

-- TODO: Maybe a comment here to explain Yann's hack would be great since this
-- is also an Example file
class NocParam where
  Data : Type     -- Type of data transmitted over the NoC
  DataS : String  -- String representation of Data
  netsz : Nat     -- Network Size (Number of router)

variable [P: NocParam]

-- TODO: Unsure why this needs to be an abbrev, but it does not work when this
-- is def
abbrev RouterID :=
  -- FIXME: This could be a Fin T.netsz, should it ?
  -- What is the expected behavior of a NoC in which the target is invalid?
  -- Making this a Fin T.netsz makes the below design harder, since we cannot
  -- range over Fin
  Nat

structure FlitHeader : Type :=
  dest : RouterID

def FlitHeaderS : String :=
  s!"FlitHeader {P.netsz}"

end DataflowRewriter.NoC

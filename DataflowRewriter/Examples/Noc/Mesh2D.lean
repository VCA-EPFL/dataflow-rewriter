/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Examples.Noc.Lang

namespace DataflowRewriter.Noc.Mesh2D

structure Mesh2D where
  sizeX : Nat
  sizeY : Nat

-- TODO: Harder than Torus because topology is less regular (edges)

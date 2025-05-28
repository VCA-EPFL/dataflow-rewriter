/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz, Gurvan Debaussart
-/

import DataflowRewriter.Module
import DataflowRewriter.Component
import DataflowRewriter.Examples.Noc.Utils
import DataflowRewriter.Examples.Noc.Lang

set_option autoImplicit false
set_option linter.all false

namespace DataflowRewriter.Noc

  -- TODO
  -- Choose wether it should be ExprLow or ExprHigh

  variable {Data : Type} [BEq Data] [LawfulBEq Data]

  @[drcomponents]
  def Noc.build_expr (n : Noc Data) : ExprLow Nat :=
    .base { input := .nil, output := .nil } 0

end DataflowRewriter.Noc

/-
Copyright (c) 2025 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import Graphiti.Module
import Graphiti.ExprHigh

namespace Graphiti.VerilogExport

structure VerilogInterface where
  input : PortMap String String
  output : PortMap String String
deriving Inhabited

structure VerilogTemplate where
  module : PortMapping String → Option String
  instantiation : String → PortMapping String → Option String
  declaration : String
deriving Inhabited

def format_ident : InternalPort String → String
| ⟨.top, i⟩ => s!"{i}"
| ⟨.internal n, i⟩ => s!"{n}_{i}"

def find_ident (inst : PortMap String (InternalPort String)) (port : String) :=
  format_ident <$> inst.find? ⟨.top, port⟩

def toPortList (inst : PortMap String (InternalPort String)) : List String :=
  inst.toList.map (λ (a, b) => s!".{format_ident a}({format_ident b})")

def allToPortList (inst : PortMapping String) : String :=
  let s := toPortList inst.input
  let s' := toPortList inst.output
  ", ".intercalate (s ++ s')

def format_instantiation (typ : String) (name : String) (inst : PortMapping String) :=
  s!"{typ} {name}({allToPortList inst});"

def format_declaration (inst : List (String × InternalPort String)) :=
  inst.map (λ (s, i) => s!"{s} {format_ident i};")

def format_declarations (inst : PortMapping String) :=
  "\n".intercalate (format_declaration ((inst.input.mapVal (λ | _, ⟨.top, b⟩ => ("input wire [0:0]", ⟨.top, b⟩)
                                                              | _, b => ("wire [0:0]", b))).toList.map Prod.snd)
                   ++ format_declaration ((inst.output.mapVal (λ | _, ⟨.top, b⟩ => ("output wire [0:0]", ⟨.top, b⟩)
                                                                 | _, b => ("wire [0:0]", b))).toList.map Prod.snd))

def format_declarations_with_interface (v : VerilogInterface) :=
  let inps := v.input.toList.map (λ (a, b) => (b, a))
  let outs := v.output.toList.map (λ (a, b) => (b, a))
  "\n".intercalate <| format_declaration inps ++ format_declaration outs

def simple_interface (inps outs : List String): VerilogInterface :=
  ⟨inps.map (λ x => (⟨.top, x⟩, "input wire [0:0]")) |>.toAssocList,
   outs.map (λ x => (⟨.top, x⟩, "output wire [0:0]")) |>.toAssocList⟩

def format_local_decls (inst : PortMapping String) :=
  "\n".intercalate (format_declaration ((inst.input.mapVal (λ b _ => ("input wire [0:0]", b))).toList.map Prod.snd)
                    ++ format_declaration ((inst.output.mapVal (λ b _ => ("output wire [0:0]", b))).toList.map Prod.snd))

def build_local_module (typ : String) (inst : PortMapping String) (body : String) :=
  let v := ", ".intercalate (inst.input.toList.map
    (λ (x, _) => format_ident x) ++ inst.output.toList.map (λ (x, _) => format_ident x))
  s!"module {typ}({v});\n"
  ++ s!"{format_local_decls inst}\n"
  ++ s!"{body}\n"
  ++ s!"endmodule"

def build_verilog_instances (env : IdentMap String VerilogTemplate) (e : ExprHigh String): Option String := do
  let s ← e.modules.toList.mapM (λ x => env.find? x.2.2 >>= (VerilogTemplate.instantiation · x.1 x.2.1))
  return "\n".intercalate s

def build_verilog_decls' (env : IdentMap String VerilogTemplate) (e : ExprHigh String): Option String := do
  let s ← e.modules.toList.mapM (λ x => env.find? x.2.2 >>= (VerilogTemplate.declaration · x.1 x.2.1))
  return "\n".intercalate s

def build_verilog_decls (env : IdentMap String VerilogTemplate) : Option String := do
  let s := env.toList.map (λ (name, template) => template.declaration)
  return "\n".intercalate s

def build_verilog_mods (env : IdentMap String VerilogTemplate) (e : ExprHigh String): Option String := do
  let (s, _) ← e.modules.toList.foldrM
    (λ x acc =>
      if x.2.2 ∈ acc.2 then acc else
        env.find? x.2.2 >>= (VerilogTemplate.module · x.2.1) >>= λ v => .some (s!"{v}\n\n{acc.1}", x.2.2 :: acc.2))
    ("", [])
  return s

def build_verilog_conns (e : ExprHigh String): String :=
  "\n".intercalate <| e.connections.map (λ ⟨o, i⟩ => s!"assign {format_ident i} = {format_ident o};")

def build_verilog_body (env : IdentMap String VerilogTemplate) (e : ExprHigh String) := do
  return s!"{← build_verilog_instances env e}\n\n{build_verilog_conns e}"

def build_verilog_module (modName : String) (env : IdentMap String VerilogTemplate) (e : ExprHigh String) : Option String := do
  let decls ← build_verilog_decls env e
  let mods ← build_verilog_mods env e
  let body ← build_verilog_body env e
  let args := ", ".intercalate ((e.inputPorts ++ e.outputPorts).map (InternalPort.mk .top ·) |>.map format_ident)
  s!"{mods}\n\nmodule {modName}({args});\n{decls}\n\n{body}\nendmodule\n"

end Graphiti.VerilogExport

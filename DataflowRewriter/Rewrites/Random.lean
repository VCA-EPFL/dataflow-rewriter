import DataflowRewriter.Rewriter
import DataflowRewriter.Rewrites.CombineMux
import DataflowRewriter.Rewrites.CombineBranch

open DataflowRewriter
open CombineMux

def h : ExprHigh String :=
{ modules := Batteries.AssocList.cons
               "cst_7"
               ({ input := Batteries.AssocList.cons
                             { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                             { inst := DataflowRewriter.InstIdent.internal "cst_7", name := "in1" }
                             (Batteries.AssocList.nil),
                  output := Batteries.AssocList.cons
                              { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                              { inst := DataflowRewriter.InstIdent.internal "cst_7", name := "out1" }
                              (Batteries.AssocList.nil) },
                "ConstantC")
               (Batteries.AssocList.cons
                 "cst_6"
                 ({ input := Batteries.AssocList.cons
                               { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                               { inst := DataflowRewriter.InstIdent.internal "cst_6", name := "in1" }
                               (Batteries.AssocList.nil),
                    output := Batteries.AssocList.cons
                                { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                { inst := DataflowRewriter.InstIdent.internal "cst_6", name := "out1" }
                                (Batteries.AssocList.nil) },
                  "ConstantC")
                 (Batteries.AssocList.cons
                   "branch_0"
                   ({ input := Batteries.AssocList.cons
                                 { inst := DataflowRewriter.InstIdent.top, name := "in2" }
                                 { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "in2" }
                                 (Batteries.AssocList.cons
                                   { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                   { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "in1" }
                                   (Batteries.AssocList.nil)),
                      output := Batteries.AssocList.cons
                                  { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                  { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "out2" }
                                  (Batteries.AssocList.cons
                                    { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                    { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "out1" }
                                    (Batteries.AssocList.nil)) },
                    "branch T")
                   (Batteries.AssocList.cons
                     "sink_1"
                     ({ input := Batteries.AssocList.cons
                                   { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                   { inst := DataflowRewriter.InstIdent.internal "sink_1", name := "in1" }
                                   (Batteries.AssocList.nil),
                        output := Batteries.AssocList.nil },
                      "Sink")
                     (Batteries.AssocList.cons
                       "store_0"
                       ({ input := Batteries.AssocList.cons
                                     { inst := DataflowRewriter.InstIdent.top, name := "in2" }
                                     { inst := DataflowRewriter.InstIdent.internal "store_0", name := "in2" }
                                     (Batteries.AssocList.cons
                                       { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                       { inst := DataflowRewriter.InstIdent.internal "store_0", name := "in1" }
                                       (Batteries.AssocList.nil)),
                          output := Batteries.AssocList.cons
                                      { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                      { inst := DataflowRewriter.InstIdent.internal "store_0", name := "out1" }
                                      (Batteries.AssocList.cons
                                        { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                        { inst := DataflowRewriter.InstIdent.internal "store_0", name := "out2" }
                                        (Batteries.AssocList.nil)) },
                        "Add")
                       (Batteries.AssocList.cons
                         "cst_4"
                         ({ input := Batteries.AssocList.cons
                                       { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                       { inst := DataflowRewriter.InstIdent.internal "cst_4", name := "in1" }
                                       (Batteries.AssocList.nil),
                            output := Batteries.AssocList.cons
                                        { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                        { inst := DataflowRewriter.InstIdent.internal "cst_4", name := "out1" }
                                        (Batteries.AssocList.nil) },
                          "ConstantC")
                         (Batteries.AssocList.cons
                           "add_19"
                           ({ input := Batteries.AssocList.cons
                                         { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                         { inst := DataflowRewriter.InstIdent.internal "add_19", name := "in1" }
                                         (Batteries.AssocList.cons
                                           { inst := DataflowRewriter.InstIdent.top, name := "in2" }
                                           { inst := DataflowRewriter.InstIdent.internal "add_19", name := "in2" }
                                           (Batteries.AssocList.nil)),
                              output := Batteries.AssocList.cons
                                          { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                          { inst := DataflowRewriter.InstIdent.internal "add_19", name := "out1" }
                                          (Batteries.AssocList.nil) },
                            "Add")
                           (Batteries.AssocList.cons
                             "fork_2"
                             ({ input := Batteries.AssocList.cons
                                           { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                           { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "in1" }
                                           (Batteries.AssocList.nil),
                                output := Batteries.AssocList.cons
                                            { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                            { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "out2" }
                                            (Batteries.AssocList.cons
                                              { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                              { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "out1" }
                                              (Batteries.AssocList.nil)) },
                              "fork Bool 2")
                             (Batteries.AssocList.cons
                               "ret_0"
                               ({ input := Batteries.AssocList.cons
                                             { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                             { inst := DataflowRewriter.InstIdent.internal "ret_0", name := "in1" }
                                             (Batteries.AssocList.nil),
                                  output := Batteries.AssocList.cons
                                              { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                              { inst := DataflowRewriter.InstIdent.internal "ret_0", name := "out1" }
                                              (Batteries.AssocList.nil) },
                                "Add")
                               (Batteries.AssocList.cons
                                 "fork_3_4"
                                 ({ input := Batteries.AssocList.cons
                                               { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                               { inst := DataflowRewriter.InstIdent.internal "fork_3_4",
                                                 name := "in1" }
                                               (Batteries.AssocList.nil),
                                    output := Batteries.AssocList.cons
                                                { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                                { inst := DataflowRewriter.InstIdent.internal "fork_3_4",
                                                  name := "out2" }
                                                (Batteries.AssocList.cons
                                                  { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                  { inst := DataflowRewriter.InstIdent.internal "fork_3_4",
                                                    name := "out1" }
                                                  (Batteries.AssocList.nil)) },
                                  "fork Bool 2")
                                 (Batteries.AssocList.cons
                                   "fork_11_1"
                                   ({ input := Batteries.AssocList.cons
                                                 { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                 { inst := DataflowRewriter.InstIdent.internal "fork_11_1",
                                                   name := "in1" }
                                                 (Batteries.AssocList.nil),
                                      output := Batteries.AssocList.cons
                                                  { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                  { inst := DataflowRewriter.InstIdent.internal "fork_11_1",
                                                    name := "out1" }
                                                  (Batteries.AssocList.cons
                                                    { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                                    { inst := DataflowRewriter.InstIdent.internal "fork_11_1",
                                                      name := "out2" }
                                                    (Batteries.AssocList.nil)) },
                                    "fork Bool 2")
                                   (Batteries.AssocList.cons
                                     "MC_V"
                                     ({ input := Batteries.AssocList.cons
                                                   { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                   { inst := DataflowRewriter.InstIdent.internal "MC_V",
                                                     name := "in1" }
                                                   (Batteries.AssocList.nil),
                                        output := Batteries.AssocList.cons
                                                    { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                                    { inst := DataflowRewriter.InstIdent.internal "MC_V",
                                                      name := "out2" }
                                                    (Batteries.AssocList.cons
                                                      { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                      { inst := DataflowRewriter.InstIdent.internal "MC_V",
                                                        name := "out1" }
                                                      (Batteries.AssocList.nil)) },
                                      "MC")
                                     (Batteries.AssocList.cons
                                       "fork_3_2"
                                       ({ input := Batteries.AssocList.cons
                                                     { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                     { inst := DataflowRewriter.InstIdent.internal "fork_3_2",
                                                       name := "in1" }
                                                     (Batteries.AssocList.nil),
                                          output := Batteries.AssocList.cons
                                                      { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                                      { inst := DataflowRewriter.InstIdent.internal "fork_3_2",
                                                        name := "out2" }
                                                      (Batteries.AssocList.cons
                                                        { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                        { inst := DataflowRewriter.InstIdent.internal "fork_3_2",
                                                          name := "out1" }
                                                        (Batteries.AssocList.nil)) },
                                        "fork Bool 2")
                                       (Batteries.AssocList.cons
                                         "add_14"
                                         ({ input := Batteries.AssocList.cons
                                                       { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                       { inst := DataflowRewriter.InstIdent.internal "add_14",
                                                         name := "in1" }
                                                       (Batteries.AssocList.cons
                                                         { inst := DataflowRewriter.InstIdent.top, name := "in2" }
                                                         { inst := DataflowRewriter.InstIdent.internal "add_14",
                                                           name := "in2" }
                                                         (Batteries.AssocList.nil)),
                                            output := Batteries.AssocList.cons
                                                        { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                        { inst := DataflowRewriter.InstIdent.internal "add_14",
                                                          name := "out1" }
                                                        (Batteries.AssocList.nil) },
                                          "Add")
                                         (Batteries.AssocList.cons
                                           "fork_11_3"
                                           ({ input := Batteries.AssocList.cons
                                                         { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                         { inst := DataflowRewriter.InstIdent.internal "fork_11_3",
                                                           name := "in1" }
                                                         (Batteries.AssocList.nil),
                                              output := Batteries.AssocList.cons
                                                          { inst := DataflowRewriter.InstIdent.top, name := "out2" }
                                                          { inst := DataflowRewriter.InstIdent.internal "fork_11_3",
                                                            name := "out2" }
                                                          (Batteries.AssocList.cons
                                                            { inst := DataflowRewriter.InstIdent.top, name := "out1" }
                                                            { inst := DataflowRewriter.InstIdent.internal "fork_11_3",
                                                              name := "out1" }
                                                            (Batteries.AssocList.nil)) },
                                            "fork Bool 2")
                                           (Batteries.AssocList.cons
                                             "cst_10"
                                             ({ input := Batteries.AssocList.cons
                                                           { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                           { inst := DataflowRewriter.InstIdent.internal "cst_10",
                                                             name := "in1" }
                                                           (Batteries.AssocList.nil),
                                                output := Batteries.AssocList.nil },
                                              "ConstantA")
                                             (Batteries.AssocList.cons
                                               "sink_2"
                                               ({ input := Batteries.AssocList.cons
                                                             { inst := DataflowRewriter.InstIdent.top, name := "in1" }
                                                             { inst := DataflowRewriter.InstIdent.internal "sink_2",
                                                               name := "in1" }
                                                             (Batteries.AssocList.nil),
                                                  output := Batteries.AssocList.nil },
                                                "Sink")
                                               (Batteries.AssocList.cons
                                                 "fork_7"
                                                 ({ input := Batteries.AssocList.cons
                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                 name := "in1" }
                                                               { inst := DataflowRewriter.InstIdent.internal "fork_7",
                                                                 name := "in1" }
                                                               (Batteries.AssocList.nil),
                                                    output := Batteries.AssocList.cons
                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                  name := "out2" }
                                                                { inst := DataflowRewriter.InstIdent.internal "fork_7",
                                                                  name := "out2" }
                                                                (Batteries.AssocList.cons
                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                    name := "out1" }
                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                              "fork_7",
                                                                    name := "out1" }
                                                                  (Batteries.AssocList.nil)) },
                                                  "fork Bool 2")
                                                 (Batteries.AssocList.cons
                                                   "phi_4"
                                                   ({ input := Batteries.AssocList.cons
                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                   name := "in1" }
                                                                 { inst := DataflowRewriter.InstIdent.internal "phi_4",
                                                                   name := "in1" }
                                                                 (Batteries.AssocList.cons
                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                     name := "in3" }
                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                               "phi_4",
                                                                     name := "in3" }
                                                                   (Batteries.AssocList.cons
                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                       name := "in2" }
                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                 "phi_4",
                                                                       name := "in2" }
                                                                     (Batteries.AssocList.nil))),
                                                      output := Batteries.AssocList.cons
                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                    name := "out1" }
                                                                  { inst := DataflowRewriter.InstIdent.internal "phi_4",
                                                                    name := "out1" }
                                                                  (Batteries.AssocList.nil) },
                                                    "mux T")
                                                   (Batteries.AssocList.cons
                                                     "fork_0"
                                                     ({ input := Batteries.AssocList.cons
                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                     name := "in1" }
                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                               "fork_0",
                                                                     name := "in1" }
                                                                   (Batteries.AssocList.nil),
                                                        output := Batteries.AssocList.cons
                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                      name := "out3" }
                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                "fork_0",
                                                                      name := "out3" }
                                                                    (Batteries.AssocList.cons
                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                        name := "out2" }
                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                  "fork_0",
                                                                        name := "out2" }
                                                                      (Batteries.AssocList.cons
                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                          name := "out1" }
                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                    "fork_0",
                                                                          name := "out1" }
                                                                        (Batteries.AssocList.nil))) },
                                                      "fork Bool 2")
                                                     (Batteries.AssocList.cons
                                                       "branch_1"
                                                       ({ input := Batteries.AssocList.cons
                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                       name := "in2" }
                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                 "branch_1",
                                                                       name := "in2" }
                                                                     (Batteries.AssocList.cons
                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                         name := "in1" }
                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                   "branch_1",
                                                                         name := "in1" }
                                                                       (Batteries.AssocList.nil)),
                                                          output := Batteries.AssocList.cons
                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                        name := "out2" }
                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                  "branch_1",
                                                                        name := "out2" }
                                                                      (Batteries.AssocList.cons
                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                          name := "out1" }
                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                    "branch_1",
                                                                          name := "out1" }
                                                                        (Batteries.AssocList.nil)) },
                                                        "branch T")
                                                       (Batteries.AssocList.cons
                                                         "load_7"
                                                         ({ input := Batteries.AssocList.cons
                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                         name := "in2" }
                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                   "load_7",
                                                                         name := "in2" }
                                                                       (Batteries.AssocList.cons
                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                           name := "in1" }
                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                     "load_7",
                                                                           name := "in1" }
                                                                         (Batteries.AssocList.nil)),
                                                            output := Batteries.AssocList.cons
                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                          name := "out1" }
                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                    "load_7",
                                                                          name := "out1" }
                                                                        (Batteries.AssocList.cons
                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                            name := "out2" }
                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                      "load_7",
                                                                            name := "out2" }
                                                                          (Batteries.AssocList.nil)) },
                                                          "Add")
                                                         (Batteries.AssocList.cons
                                                           "forkC_9"
                                                           ({ input := Batteries.AssocList.cons
                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                           name := "in1" }
                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                     "forkC_9",
                                                                           name := "in1" }
                                                                         (Batteries.AssocList.nil),
                                                              output := Batteries.AssocList.cons
                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                            name := "out4" }
                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                      "forkC_9",
                                                                            name := "out4" }
                                                                          (Batteries.AssocList.cons
                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                              name := "out3" }
                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                        "forkC_9",
                                                                              name := "out3" }
                                                                            (Batteries.AssocList.cons
                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                name := "out2" }
                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                          "forkC_9",
                                                                                name := "out2" }
                                                                              (Batteries.AssocList.cons
                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                  name := "out1" }
                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                            "forkC_9",
                                                                                  name := "out1" }
                                                                                (Batteries.AssocList.nil)))) },
                                                            "fork Bool 2")
                                                           (Batteries.AssocList.cons
                                                             "branch_2"
                                                             ({ input := Batteries.AssocList.cons
                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                             name := "in2" }
                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                       "branch_2",
                                                                             name := "in2" }
                                                                           (Batteries.AssocList.cons
                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                               name := "in1" }
                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                         "branch_2",
                                                                               name := "in1" }
                                                                             (Batteries.AssocList.nil)),
                                                                output := Batteries.AssocList.cons
                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                              name := "out2" }
                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                        "branch_2",
                                                                              name := "out2" }
                                                                            (Batteries.AssocList.cons
                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                name := "out1" }
                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                          "branch_2",
                                                                                name := "out1" }
                                                                              (Batteries.AssocList.nil)) },
                                                              "branch T")
                                                             (Batteries.AssocList.cons
                                                               "init"
                                                               ({ input := Batteries.AssocList.cons
                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                               name := "in1" }
                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                         "init",
                                                                               name := "in1" }
                                                                             (Batteries.AssocList.nil),
                                                                  output := Batteries.AssocList.cons
                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                name := "out1" }
                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                          "init",
                                                                                name := "out1" }
                                                                              (Batteries.AssocList.nil) },
                                                                "init Bool false")
                                                               (Batteries.AssocList.cons
                                                                 "cst_9"
                                                                 ({ input := Batteries.AssocList.cons
                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                 name := "in1" }
                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                           "cst_9",
                                                                                 name := "in1" }
                                                                               (Batteries.AssocList.nil),
                                                                    output := Batteries.AssocList.cons
                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                  name := "out1" }
                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                            "cst_9",
                                                                                  name := "out1" }
                                                                                (Batteries.AssocList.nil) },
                                                                  "ConstantA")
                                                                 (Batteries.AssocList.cons
                                                                   "zext_9"
                                                                   ({ input := Batteries.AssocList.cons
                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                   name := "in1" }
                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                             "zext_9",
                                                                                   name := "in1" }
                                                                                 (Batteries.AssocList.nil),
                                                                      output := Batteries.AssocList.cons
                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                    name := "out1" }
                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                              "zext_9",
                                                                                    name := "out1" }
                                                                                  (Batteries.AssocList.nil) },
                                                                    "Add")
                                                                   (Batteries.AssocList.cons
                                                                     "branch_5"
                                                                     ({ input := Batteries.AssocList.cons
                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                     name := "in1" }
                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                               "branch_5",
                                                                                     name := "in1" }
                                                                                   (Batteries.AssocList.cons
                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                       name := "in2" }
                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                 "branch_5",
                                                                                       name := "in2" }
                                                                                     (Batteries.AssocList.nil)),
                                                                        output := Batteries.AssocList.cons
                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                      name := "out2" }
                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                "branch_5",
                                                                                      name := "out2" }
                                                                                    (Batteries.AssocList.cons
                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                        name := "out1" }
                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                  "branch_5",
                                                                                        name := "out1" }
                                                                                      (Batteries.AssocList.nil)) },
                                                                      "branch T")
                                                                     (Batteries.AssocList.cons
                                                                       "MC_Out"
                                                                       ({ input := Batteries.AssocList.cons
                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                       name := "in1" }
                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                 "MC_Out",
                                                                                       name := "in1" }
                                                                                     (Batteries.AssocList.cons
                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                         name := "in3" }
                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                   "MC_Out",
                                                                                         name := "in3" }
                                                                                       (Batteries.AssocList.cons
                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                           name := "in2" }
                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                     "MC_Out",
                                                                                           name := "in2" }
                                                                                         (Batteries.AssocList.nil))),
                                                                          output := Batteries.AssocList.cons
                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                        name := "out1" }
                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                  "MC_Out",
                                                                                        name := "out1" }
                                                                                      (Batteries.AssocList.nil) },
                                                                        "MC")
                                                                       (Batteries.AssocList.cons
                                                                         "phiC_1"
                                                                         ({ input := Batteries.AssocList.cons
                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                         name := "in1" }
                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                   "phiC_1",
                                                                                         name := "in1" }
                                                                                       (Batteries.AssocList.cons
                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                           name := "in2" }
                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                     "phiC_1",
                                                                                           name := "in2" }
                                                                                         (Batteries.AssocList.cons
                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                             name := "in3" }
                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                       "phiC_1",
                                                                                             name := "in3" }
                                                                                           (Batteries.AssocList.nil))),
                                                                            output := Batteries.AssocList.cons
                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                          name := "out1" }
                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                    "phiC_1",
                                                                                          name := "out1" }
                                                                                        (Batteries.AssocList.nil) },
                                                                          "mux T")
                                                                         (Batteries.AssocList.cons
                                                                           "fork_3_3"
                                                                           ({ input := Batteries.AssocList.cons
                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                           name := "in1" }
                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                     "fork_3_3",
                                                                                           name := "in1" }
                                                                                         (Batteries.AssocList.nil),
                                                                              output := Batteries.AssocList.cons
                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                            name := "out2" }
                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                      "fork_3_3",
                                                                                            name := "out2" }
                                                                                          (Batteries.AssocList.cons
                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                              name := "out1" }
                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                        "fork_3_3",
                                                                                              name := "out1" }
                                                                                            (Batteries.AssocList.nil)) },
                                                                            "fork Bool 2")
                                                                           (Batteries.AssocList.cons
                                                                             "start_0"
                                                                             ({ input := Batteries.AssocList.nil,
                                                                                output := Batteries.AssocList.cons
                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                              name := "out1" }
                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                        "start_0",
                                                                                              name := "out1" }
                                                                                            (Batteries.AssocList.nil) },
                                                                              "Entry")
                                                                             (Batteries.AssocList.cons
                                                                               "phi_1"
                                                                               ({ input := Batteries.AssocList.cons
                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                               name := "in1" }
                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                         "phi_1",
                                                                                               name := "in1" }
                                                                                             (Batteries.AssocList.cons
                                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                                 name := "in3" }
                                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                                           "phi_1",
                                                                                                 name := "in3" }
                                                                                               (Batteries.AssocList.cons
                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                   name := "in2" }
                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                             "phi_1",
                                                                                                   name := "in2" }
                                                                                                 (Batteries.AssocList.nil))),
                                                                                  output := Batteries.AssocList.cons
                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                name := "out1" }
                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                          "phi_1",
                                                                                                name := "out1" }
                                                                                              (Batteries.AssocList.nil) },
                                                                                "mux T")
                                                                               (Batteries.AssocList.cons
                                                                                 "getelementptr_10"
                                                                                 ({ input := Batteries.AssocList.cons
                                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                                 name := "in3" }
                                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                                           "getelementptr_10",
                                                                                                 name := "in3" }
                                                                                               (Batteries.AssocList.cons
                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                   name := "in2" }
                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                             "getelementptr_10",
                                                                                                   name := "in2" }
                                                                                                 (Batteries.AssocList.cons
                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                     name := "in1" }
                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                               "getelementptr_10",
                                                                                                     name := "in1" }
                                                                                                   (Batteries.AssocList.nil))),
                                                                                    output := Batteries.AssocList.cons
                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                  name := "out1" }
                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                            "getelementptr_10",
                                                                                                  name := "out1" }
                                                                                                (Batteries.AssocList.nil) },
                                                                                  "Add")
                                                                                 (Batteries.AssocList.cons
                                                                                   "branchC_6"
                                                                                   ({ input := Batteries.AssocList.cons
                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                   name := "in1" }
                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                             "branchC_6",
                                                                                                   name := "in1" }
                                                                                                 (Batteries.AssocList.cons
                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                     name := "in2" }
                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                               "branchC_6",
                                                                                                     name := "in2" }
                                                                                                   (Batteries.AssocList.nil)),
                                                                                      output := Batteries.AssocList.cons
                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                    name := "out2" }
                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                              "branchC_6",
                                                                                                    name := "out2" }
                                                                                                  (Batteries.AssocList.cons
                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                      name := "out1" }
                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                "branchC_6",
                                                                                                      name := "out1" }
                                                                                                    (Batteries.AssocList.nil)) },
                                                                                    "branch T")
                                                                                   (Batteries.AssocList.cons
                                                                                     "cst_3"
                                                                                     ({ input := Batteries.AssocList.cons
                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                     name := "in1" }
                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                               "cst_3",
                                                                                                     name := "in1" }
                                                                                                   (Batteries.AssocList.nil),
                                                                                        output := Batteries.AssocList.cons
                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                      name := "out1" }
                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                "cst_3",
                                                                                                      name := "out1" }
                                                                                                    (Batteries.AssocList.nil) },
                                                                                      "ConstantB")
                                                                                     (Batteries.AssocList.cons
                                                                                       "cst_2"
                                                                                       ({ input := Batteries.AssocList.cons
                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                       name := "in1" }
                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                 "cst_2",
                                                                                                       name := "in1" }
                                                                                                     (Batteries.AssocList.nil),
                                                                                          output := Batteries.AssocList.cons
                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                        name := "out1" }
                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                  "cst_2",
                                                                                                        name := "out1" }
                                                                                                      (Batteries.AssocList.nil) },
                                                                                        "ConstantA")
                                                                                       (Batteries.AssocList.cons
                                                                                         "cst_1"
                                                                                         ({ input := Batteries.AssocList.cons
                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                         name := "in1" }
                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                   "cst_1",
                                                                                                         name := "in1" }
                                                                                                       (Batteries.AssocList.nil),
                                                                                            output := Batteries.AssocList.cons
                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                          name := "out1" }
                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                    "cst_1",
                                                                                                          name := "out1" }
                                                                                                        (Batteries.AssocList.nil) },
                                                                                          "ConstantA")
                                                                                         (Batteries.AssocList.cons
                                                                                           "load_11"
                                                                                           ({ input := Batteries.AssocList.cons
                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                           name := "in2" }
                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                     "load_11",
                                                                                                           name := "in2" }
                                                                                                         (Batteries.AssocList.cons
                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                             name := "in1" }
                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                       "load_11",
                                                                                                             name := "in1" }
                                                                                                           (Batteries.AssocList.nil)),
                                                                                              output := Batteries.AssocList.cons
                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                            name := "out1" }
                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                      "load_11",
                                                                                                            name := "out1" }
                                                                                                          (Batteries.AssocList.cons
                                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                                              name := "out2" }
                                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                                        "load_11",
                                                                                                              name := "out2" }
                                                                                                            (Batteries.AssocList.nil)) },
                                                                                            "Add")
                                                                                           (Batteries.AssocList.cons
                                                                                             "forkC_8"
                                                                                             ({ input := Batteries.AssocList.cons
                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                             name := "in1" }
                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                       "forkC_8",
                                                                                                             name := "in1" }
                                                                                                           (Batteries.AssocList.nil),
                                                                                                output := Batteries.AssocList.cons
                                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                                              name := "out9" }
                                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                                        "forkC_8",
                                                                                                              name := "out9" }
                                                                                                            (Batteries.AssocList.cons
                                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                                name := "out8" }
                                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                                          "forkC_8",
                                                                                                                name := "out8" }
                                                                                                              (Batteries.AssocList.cons
                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                  name := "out7" }
                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                            "forkC_8",
                                                                                                                  name := "out7" }
                                                                                                                (Batteries.AssocList.cons
                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                    name := "out6" }
                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                              "forkC_8",
                                                                                                                    name := "out6" }
                                                                                                                  (Batteries.AssocList.cons
                                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                                      name := "out4" }
                                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                "forkC_8",
                                                                                                                      name := "out4" }
                                                                                                                    (Batteries.AssocList.cons
                                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                                        name := "out3" }
                                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                  "forkC_8",
                                                                                                                        name := "out3" }
                                                                                                                      (Batteries.AssocList.cons
                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                          name := "out2" }
                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                    "forkC_8",
                                                                                                                          name := "out2" }
                                                                                                                        (Batteries.AssocList.cons
                                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                                            name := "out1" }
                                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                      "forkC_8",
                                                                                                                            name := "out1" }
                                                                                                                          (Batteries.AssocList.nil)))))))) },
                                                                                              "fork Bool 2")
                                                                                             (Batteries.AssocList.cons
                                                                                               "fork_1"
                                                                                               ({ input := Batteries.AssocList.cons
                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                               name := "in1" }
                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                         "fork_1",
                                                                                                               name := "in1" }
                                                                                                             (Batteries.AssocList.nil),
                                                                                                  output := Batteries.AssocList.cons
                                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                                name := "out3" }
                                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                                          "fork_1",
                                                                                                                name := "out3" }
                                                                                                              (Batteries.AssocList.cons
                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                  name := "out2" }
                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                            "fork_1",
                                                                                                                  name := "out2" }
                                                                                                                (Batteries.AssocList.cons
                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                    name := "out1" }
                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                              "fork_1",
                                                                                                                    name := "out1" }
                                                                                                                  (Batteries.AssocList.nil))) },
                                                                                                "fork Bool 2")
                                                                                               (Batteries.AssocList.cons
                                                                                                 "zext_8"
                                                                                                 ({ input := Batteries.AssocList.cons
                                                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                                                 name := "in1" }
                                                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                                                           "zext_8",
                                                                                                                 name := "in1" }
                                                                                                               (Batteries.AssocList.nil),
                                                                                                    output := Batteries.AssocList.cons
                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                  name := "out1" }
                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                            "zext_8",
                                                                                                                  name := "out1" }
                                                                                                                (Batteries.AssocList.nil) },
                                                                                                  "Add")
                                                                                                 (Batteries.AssocList.cons
                                                                                                   "fork_11_2"
                                                                                                   ({ input := Batteries.AssocList.cons
                                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                                   name := "in1" }
                                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                                             "fork_11_2",
                                                                                                                   name := "in1" }
                                                                                                                 (Batteries.AssocList.nil),
                                                                                                      output := Batteries.AssocList.cons
                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                    name := "out1" }
                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                              "fork_11_2",
                                                                                                                    name := "out1" }
                                                                                                                  (Batteries.AssocList.cons
                                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                                      name := "out2" }
                                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                "fork_11_2",
                                                                                                                      name := "out2" }
                                                                                                                    (Batteries.AssocList.nil)) },
                                                                                                    "fork Bool 2")
                                                                                                   (Batteries.AssocList.cons
                                                                                                     "phiC_3"
                                                                                                     ({ input := Batteries.AssocList.cons
                                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                                     name := "in1" }
                                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                                               "phiC_3",
                                                                                                                     name := "in1" }
                                                                                                                   (Batteries.AssocList.cons
                                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                                       name := "in2" }
                                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                 "phiC_3",
                                                                                                                       name := "in2" }
                                                                                                                     (Batteries.AssocList.cons
                                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                                         name := "in3" }
                                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                   "phiC_3",
                                                                                                                         name := "in3" }
                                                                                                                       (Batteries.AssocList.nil))),
                                                                                                        output := Batteries.AssocList.cons
                                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                                      name := "out1" }
                                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                "phiC_3",
                                                                                                                      name := "out1" }
                                                                                                                    (Batteries.AssocList.nil) },
                                                                                                      "mux T")
                                                                                                     (Batteries.AssocList.cons
                                                                                                       "fork_10"
                                                                                                       ({ input := Batteries.AssocList.cons
                                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                                       name := "in1" }
                                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                 "fork_10",
                                                                                                                       name := "in1" }
                                                                                                                     (Batteries.AssocList.nil),
                                                                                                          output := Batteries.AssocList.cons
                                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                                        name := "out2" }
                                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                  "fork_10",
                                                                                                                        name := "out2" }
                                                                                                                      (Batteries.AssocList.cons
                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                          name := "out1" }
                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                    "fork_10",
                                                                                                                          name := "out1" }
                                                                                                                        (Batteries.AssocList.nil)) },
                                                                                                        "fork Bool 2")
                                                                                                       (Batteries.AssocList.cons
                                                                                                         "fork_4"
                                                                                                         ({ input := Batteries.AssocList.cons
                                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                                         name := "in1" }
                                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                   "fork_4",
                                                                                                                         name := "in1" }
                                                                                                                       (Batteries.AssocList.nil),
                                                                                                            output := Batteries.AssocList.cons
                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                          name := "out2" }
                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                    "fork_4",
                                                                                                                          name := "out2" }
                                                                                                                        (Batteries.AssocList.cons
                                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                                            name := "out1" }
                                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                      "fork_4",
                                                                                                                            name := "out1" }
                                                                                                                          (Batteries.AssocList.nil)) },
                                                                                                          "fork Bool 2")
                                                                                                         (Batteries.AssocList.cons
                                                                                                           "phi_3"
                                                                                                           ({ input := Batteries.AssocList.cons
                                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                                           name := "in1" }
                                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                     "phi_3",
                                                                                                                           name := "in1" }
                                                                                                                         (Batteries.AssocList.cons
                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                             name := "in3" }
                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                       "phi_3",
                                                                                                                             name := "in3" }
                                                                                                                           (Batteries.AssocList.cons
                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                               name := "in2" }
                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                         "phi_3",
                                                                                                                               name := "in2" }
                                                                                                                             (Batteries.AssocList.nil))),
                                                                                                              output := Batteries.AssocList.cons
                                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                                            name := "out1" }
                                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                      "phi_3",
                                                                                                                            name := "out1" }
                                                                                                                          (Batteries.AssocList.nil) },
                                                                                                            "mux T")
                                                                                                           (Batteries.AssocList.cons
                                                                                                             "fork_5"
                                                                                                             ({ input := Batteries.AssocList.cons
                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                             name := "in1" }
                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                       "fork_5",
                                                                                                                             name := "in1" }
                                                                                                                           (Batteries.AssocList.nil),
                                                                                                                output := Batteries.AssocList.cons
                                                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                                                              name := "out3" }
                                                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                        "fork_5",
                                                                                                                              name := "out3" }
                                                                                                                            (Batteries.AssocList.cons
                                                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                name := "out2" }
                                                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                          "fork_5",
                                                                                                                                name := "out2" }
                                                                                                                              (Batteries.AssocList.cons
                                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                  name := "out1" }
                                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                            "fork_5",
                                                                                                                                  name := "out1" }
                                                                                                                                (Batteries.AssocList.nil))) },
                                                                                                              "fork Bool 2")
                                                                                                             (Batteries.AssocList.cons
                                                                                                               "cst_0"
                                                                                                               ({ input := Batteries.AssocList.cons
                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                               name := "in1" }
                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                         "cst_0",
                                                                                                                               name := "in1" }
                                                                                                                             (Batteries.AssocList.nil),
                                                                                                                  output := Batteries.AssocList.cons
                                                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                name := "out1" }
                                                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                          "cst_0",
                                                                                                                                name := "out1" }
                                                                                                                              (Batteries.AssocList.nil) },
                                                                                                                "ConstantA")
                                                                                                               (Batteries.AssocList.cons
                                                                                                                 "sink_3"
                                                                                                                 ({ input := Batteries.AssocList.cons
                                                                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                 name := "in1" }
                                                                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                           "sink_3",
                                                                                                                                 name := "in1" }
                                                                                                                               (Batteries.AssocList.nil),
                                                                                                                    output := Batteries.AssocList.nil },
                                                                                                                  "Sink")
                                                                                                                 (Batteries.AssocList.cons
                                                                                                                   "cst_5"
                                                                                                                   ({ input := Batteries.AssocList.cons
                                                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                   name := "in1" }
                                                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                             "cst_5",
                                                                                                                                   name := "in1" }
                                                                                                                                 (Batteries.AssocList.nil),
                                                                                                                      output := Batteries.AssocList.cons
                                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                    name := "out1" }
                                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                              "cst_5",
                                                                                                                                    name := "out1" }
                                                                                                                                  (Batteries.AssocList.nil) },
                                                                                                                    "ConstantB")
                                                                                                                   (Batteries.AssocList.cons
                                                                                                                     "fadd_13"
                                                                                                                     ({ input := Batteries.AssocList.cons
                                                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                     name := "in2" }
                                                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                               "fadd_13",
                                                                                                                                     name := "in2" }
                                                                                                                                   (Batteries.AssocList.cons
                                                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                       name := "in1" }
                                                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                 "fadd_13",
                                                                                                                                       name := "in1" }
                                                                                                                                     (Batteries.AssocList.nil)),
                                                                                                                        output := Batteries.AssocList.cons
                                                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                      name := "out1" }
                                                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                "fadd_13",
                                                                                                                                      name := "out1" }
                                                                                                                                    (Batteries.AssocList.nil) },
                                                                                                                      "Add")
                                                                                                                     (Batteries.AssocList.cons
                                                                                                                       "cst_8"
                                                                                                                       ({ input := Batteries.AssocList.cons
                                                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                       name := "in1" }
                                                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                 "cst_8",
                                                                                                                                       name := "in1" }
                                                                                                                                     (Batteries.AssocList.nil),
                                                                                                                          output := Batteries.AssocList.cons
                                                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                        name := "out1" }
                                                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                  "cst_8",
                                                                                                                                        name := "out1" }
                                                                                                                                      (Batteries.AssocList.nil) },
                                                                                                                        "ConstantB")
                                                                                                                       (Batteries.AssocList.cons
                                                                                                                         "end_0"
                                                                                                                         ({ input := Batteries.AssocList.cons
                                                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                         name := "in4" }
                                                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                   "end_0",
                                                                                                                                         name := "in4" }
                                                                                                                                       (Batteries.AssocList.cons
                                                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                           name := "in3" }
                                                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                     "end_0",
                                                                                                                                           name := "in3" }
                                                                                                                                         (Batteries.AssocList.cons
                                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                             name := "in2" }
                                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                       "end_0",
                                                                                                                                             name := "in2" }
                                                                                                                                           (Batteries.AssocList.cons
                                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                               name := "in1" }
                                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                         "end_0",
                                                                                                                                               name := "in1" }
                                                                                                                                             (Batteries.AssocList.nil)))),
                                                                                                                            output := Batteries.AssocList.nil },
                                                                                                                          "Exit")
                                                                                                                         (Batteries.AssocList.cons
                                                                                                                           "phi_n0"
                                                                                                                           ({ input := Batteries.AssocList.cons
                                                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                           name := "in1" }
                                                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                     "phi_n0",
                                                                                                                                           name := "in1" }
                                                                                                                                         (Batteries.AssocList.cons
                                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                             name := "in2" }
                                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                       "phi_n0",
                                                                                                                                             name := "in2" }
                                                                                                                                           (Batteries.AssocList.cons
                                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                               name := "in3" }
                                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                         "phi_n0",
                                                                                                                                               name := "in3" }
                                                                                                                                             (Batteries.AssocList.nil))),
                                                                                                                              output := Batteries.AssocList.cons
                                                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                            name := "out1" }
                                                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                      "phi_n0",
                                                                                                                                            name := "out1" }
                                                                                                                                          (Batteries.AssocList.nil) },
                                                                                                                            "mux T")
                                                                                                                           (Batteries.AssocList.cons
                                                                                                                             "icmp_20"
                                                                                                                             ({ input := Batteries.AssocList.cons
                                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                             name := "in1" }
                                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                       "icmp_20",
                                                                                                                                             name := "in1" }
                                                                                                                                           (Batteries.AssocList.cons
                                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                               name := "in2" }
                                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                         "icmp_20",
                                                                                                                                               name := "in2" }
                                                                                                                                             (Batteries.AssocList.nil)),
                                                                                                                                output := Batteries.AssocList.cons
                                                                                                                                            { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                              name := "out1" }
                                                                                                                                            { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                        "icmp_20",
                                                                                                                                              name := "out1" }
                                                                                                                                            (Batteries.AssocList.nil) },
                                                                                                                              "Add")
                                                                                                                             (Batteries.AssocList.cons
                                                                                                                               "MC_M"
                                                                                                                               ({ input := Batteries.AssocList.cons
                                                                                                                                             { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                               name := "in1" }
                                                                                                                                             { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                         "MC_M",
                                                                                                                                               name := "in1" }
                                                                                                                                             (Batteries.AssocList.nil),
                                                                                                                                  output := Batteries.AssocList.cons
                                                                                                                                              { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                name := "out2" }
                                                                                                                                              { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                          "MC_M",
                                                                                                                                                name := "out2" }
                                                                                                                                              (Batteries.AssocList.cons
                                                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                  name := "out1" }
                                                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                            "MC_M",
                                                                                                                                                  name := "out1" }
                                                                                                                                                (Batteries.AssocList.nil)) },
                                                                                                                                "MC")
                                                                                                                               (Batteries.AssocList.cons
                                                                                                                                 "fork_3_1"
                                                                                                                                 ({ input := Batteries.AssocList.cons
                                                                                                                                               { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                 name := "in1" }
                                                                                                                                               { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                           "fork_3_1",
                                                                                                                                                 name := "in1" }
                                                                                                                                               (Batteries.AssocList.nil),
                                                                                                                                    output := Batteries.AssocList.cons
                                                                                                                                                { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                  name := "out2" }
                                                                                                                                                { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                            "fork_3_1",
                                                                                                                                                  name := "out2" }
                                                                                                                                                (Batteries.AssocList.cons
                                                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                    name := "out1" }
                                                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                              "fork_3_1",
                                                                                                                                                    name := "out1" }
                                                                                                                                                  (Batteries.AssocList.nil)) },
                                                                                                                                  "fork Bool 2")
                                                                                                                                 (Batteries.AssocList.cons
                                                                                                                                   "phi_n12"
                                                                                                                                   ({ input := Batteries.AssocList.cons
                                                                                                                                                 { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                   name := "in2" }
                                                                                                                                                 { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                             "phi_n12",
                                                                                                                                                   name := "in2" }
                                                                                                                                                 (Batteries.AssocList.cons
                                                                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                     name := "in1" }
                                                                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                               "phi_n12",
                                                                                                                                                     name := "in1" }
                                                                                                                                                   (Batteries.AssocList.nil)),
                                                                                                                                      output := Batteries.AssocList.cons
                                                                                                                                                  { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                    name := "out1" }
                                                                                                                                                  { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                              "phi_n12",
                                                                                                                                                    name := "out1" }
                                                                                                                                                  (Batteries.AssocList.nil) },
                                                                                                                                    "Merge")
                                                                                                                                   (Batteries.AssocList.cons
                                                                                                                                     "forkC_6"
                                                                                                                                     ({ input := Batteries.AssocList.cons
                                                                                                                                                   { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                     name := "in1" }
                                                                                                                                                   { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                               "forkC_6",
                                                                                                                                                     name := "in1" }
                                                                                                                                                   (Batteries.AssocList.nil),
                                                                                                                                        output := Batteries.AssocList.cons
                                                                                                                                                    { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                      name := "out3" }
                                                                                                                                                    { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                "forkC_6",
                                                                                                                                                      name := "out3" }
                                                                                                                                                    (Batteries.AssocList.cons
                                                                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                        name := "out2" }
                                                                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                  "forkC_6",
                                                                                                                                                        name := "out2" }
                                                                                                                                                      (Batteries.AssocList.cons
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                          name := "out1" }
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                    "forkC_6",
                                                                                                                                                          name := "out1" }
                                                                                                                                                        (Batteries.AssocList.nil))) },
                                                                                                                                      "fork Bool 2")
                                                                                                                                     (Batteries.AssocList.cons
                                                                                                                                       "branchC_7"
                                                                                                                                       ({ input := Batteries.AssocList.cons
                                                                                                                                                     { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                       name := "in1" }
                                                                                                                                                     { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                 "branchC_7",
                                                                                                                                                       name := "in1" }
                                                                                                                                                     (Batteries.AssocList.cons
                                                                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                         name := "in2" }
                                                                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                   "branchC_7",
                                                                                                                                                         name := "in2" }
                                                                                                                                                       (Batteries.AssocList.nil)),
                                                                                                                                          output := Batteries.AssocList.cons
                                                                                                                                                      { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                        name := "out2" }
                                                                                                                                                      { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                  "branchC_7",
                                                                                                                                                        name := "out2" }
                                                                                                                                                      (Batteries.AssocList.cons
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                          name := "out1" }
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                    "branchC_7",
                                                                                                                                                          name := "out1" }
                                                                                                                                                        (Batteries.AssocList.nil)) },
                                                                                                                                        "branch T")
                                                                                                                                       (Batteries.AssocList.cons
                                                                                                                                         "icmp_15"
                                                                                                                                         ({ input := Batteries.AssocList.cons
                                                                                                                                                       { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                         name := "in1" }
                                                                                                                                                       { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                   "icmp_15",
                                                                                                                                                         name := "in1" }
                                                                                                                                                       (Batteries.AssocList.cons
                                                                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                           name := "in2" }
                                                                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                     "icmp_15",
                                                                                                                                                           name := "in2" }
                                                                                                                                                         (Batteries.AssocList.nil)),
                                                                                                                                            output := Batteries.AssocList.cons
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                          name := "out1" }
                                                                                                                                                        { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                    "icmp_15",
                                                                                                                                                          name := "out1" }
                                                                                                                                                        (Batteries.AssocList.nil) },
                                                                                                                                          "Add")
                                                                                                                                         (Batteries.AssocList.cons
                                                                                                                                           "fmul_12"
                                                                                                                                           ({ input := Batteries.AssocList.cons
                                                                                                                                                         { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                           name := "in2" }
                                                                                                                                                         { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                     "fmul_12",
                                                                                                                                                           name := "in2" }
                                                                                                                                                         (Batteries.AssocList.cons
                                                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                             name := "in1" }
                                                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                       "fmul_12",
                                                                                                                                                             name := "in1" }
                                                                                                                                                           (Batteries.AssocList.nil)),
                                                                                                                                              output := Batteries.AssocList.cons
                                                                                                                                                          { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                            name := "out1" }
                                                                                                                                                          { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                      "fmul_12",
                                                                                                                                                            name := "out1" }
                                                                                                                                                          (Batteries.AssocList.nil) },
                                                                                                                                            "Add")
                                                                                                                                           (Batteries.AssocList.cons
                                                                                                                                             "sink_0"
                                                                                                                                             ({ input := Batteries.AssocList.cons
                                                                                                                                                           { inst := DataflowRewriter.InstIdent.top,
                                                                                                                                                             name := "in1" }
                                                                                                                                                           { inst := DataflowRewriter.InstIdent.internal
                                                                                                                                                                       "sink_0",
                                                                                                                                                             name := "in1" }
                                                                                                                                                           (Batteries.AssocList.nil),
                                                                                                                                                output := Batteries.AssocList.nil },
                                                                                                                                              "Sink")
                                                                                                                                             (Batteries.AssocList.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  connections := [{ output := { inst := DataflowRewriter.InstIdent.internal "fork_11_3", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_11_3", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_n0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_11_2", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_4", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_11_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_10", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_10", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_9", name := "out4" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_7", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_9", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_4", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_9", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branchC_7", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_9", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out9" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_10", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out8" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_8", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out7" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_6", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out6" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_5", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out4" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_3", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branchC_6", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_7", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_5", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_7", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "zext_8", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_6", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_9", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_6", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_1", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "forkC_6", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "cst_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_5", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branchC_6", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_5", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_n12", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_5", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_4", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_4", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "icmp_20", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_4", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branchC_7", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_4", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_5", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_3", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_3_4", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_3", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_2", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_2", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_3_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_2", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_1", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_1", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "init", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_3_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_3_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "icmp_15", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_1", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "load_7", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_1", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "add_14", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "zext_9", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_0", name := "out3" },
                    input := { inst := DataflowRewriter.InstIdent.internal "store_0", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_0", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "add_19", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_n0", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branchC_7", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_3", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branchC_7", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "sink_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branchC_6", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phiC_1", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branchC_6", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "sink_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_5", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_n0", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_5", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "sink_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_2", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_4", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_2", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "sink_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_11_2", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_11_3", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fork_11_1", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_11_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "init", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_11_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_1", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_3", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "store_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_9", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_n12", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phi_n12", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_10", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_1", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "branch_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "ret_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phiC_3", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "forkC_9", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phiC_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "forkC_8", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phi_n0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_7", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "start_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "forkC_6", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_7", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "getelementptr_10", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "ret_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "end_0", name := "in4" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "icmp_20", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_5", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_6", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "icmp_20", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "add_19", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_4", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_5", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "add_19", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "icmp_15", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_3_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_4", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "icmp_15", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "add_14", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_2", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_3", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "add_14", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fadd_13", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "branch_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "fmul_12", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fadd_13", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "load_11", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fmul_12", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "getelementptr_10", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "load_11", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "zext_9", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "getelementptr_10", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "zext_8", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "getelementptr_10", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "load_7", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fmul_12", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phi_4", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_1", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_2", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_4", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phi_3", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fadd_13", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_3", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "phi_1", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "fork_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "phi_1", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "MC_Out", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "end_0", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "cst_8", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "MC_Out", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "MC_M", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "end_0", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "MC_V", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "end_0", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "store_0", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "MC_Out", name := "in3" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "store_0", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "MC_Out", name := "in2" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "MC_M", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "load_11", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "load_11", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "MC_M", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "MC_V", name := "out1" },
                    input := { inst := DataflowRewriter.InstIdent.internal "load_7", name := "in1" } },
                  { output := { inst := DataflowRewriter.InstIdent.internal "load_7", name := "out2" },
                    input := { inst := DataflowRewriter.InstIdent.internal "MC_V", name := "in1" } }] }

#check String.contains
#eval IO.print h

#eval IO.print <| (rewrite "T" "T").run "rw0_" h

#eval IO.print <| do
        let rw0 ← (rewrite "T" "T").run "rw0_" h
        let rw1 ← (rewrite "T" "(T × T)").run "rw1_" rw0
        let rw2 ← (rewrite "T" "(T × (T × T))").run "rw2_" rw1
        let rw3 ← (CombineBranch.rewrite "T" "T").run "rw3_" rw2
        let rw4 ← (CombineBranch.rewrite "T" "(T × T)").run "rw4_" rw3
        let rw5 ← (CombineBranch.rewrite "T" "(T × (T × T))").run "rw4_" rw4
        pure rw5

-- #eval IO.print <| (rewrite "T" "(T × (T × T))").run "rw2_" random

/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewrites.BagModule
import DataflowRewriter.Rewrites.BranchMuxToMerge
import DataflowRewriter.Rewrites.CombineBranch
import DataflowRewriter.Rewrites.CombineMux
import DataflowRewriter.Rewrites.ForkRewrite
import DataflowRewriter.Rewrites.FusionParallelTaggers
import DataflowRewriter.Rewrites.FusionTaggerTagger
import DataflowRewriter.Rewrites.JoinRewriteCorrect
import DataflowRewriter.Rewrites.JoinRewrite
import DataflowRewriter.Rewrites.LoopRewrite
import DataflowRewriter.Rewrites.MergeRewriteCorrect
import DataflowRewriter.Rewrites.MergeRewrite
import DataflowRewriter.Rewrites.MuxTaggedRewriteCorrect
import DataflowRewriter.Rewrites.MuxTaggedRewrite
import DataflowRewriter.Rewrites.MuxToTaggedMux
import DataflowRewriter.Rewrites.OoOAdd
import DataflowRewriter.Rewrites.PushTaggerOutsideBranch

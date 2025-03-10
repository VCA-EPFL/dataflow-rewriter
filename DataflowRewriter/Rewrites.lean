/-
Copyright (c) 2024 VCA Lab, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Herklotz
-/

import DataflowRewriter.Rewrites.LoopRewrite
import DataflowRewriter.Rewrites.LoopRewrite2
import DataflowRewriter.Rewrites.CombineBranch
import DataflowRewriter.Rewrites.CombineMux
import DataflowRewriter.Rewrites.JoinSplitLoopCond
import DataflowRewriter.Rewrites.ReduceSplitJoin
import DataflowRewriter.Rewrites.PureRewrites
import DataflowRewriter.Rewrites.LoadRewrite
import DataflowRewriter.Rewrites.JoinQueueLeftRewrite
import DataflowRewriter.Rewrites.JoinQueueRightRewrite
import DataflowRewriter.Rewrites.MuxQueueRightRewrite
import DataflowRewriter.Rewrites.PureSink
import DataflowRewriter.Rewrites.SplitSinkLeft
import DataflowRewriter.Rewrites.SplitSinkRight
import DataflowRewriter.Rewrites.PureSeqComp
import DataflowRewriter.Rewrites.PureJoinLeft
import DataflowRewriter.Rewrites.PureJoinRight
import DataflowRewriter.Rewrites.PureSplitRight
import DataflowRewriter.Rewrites.PureSplitLeft
import DataflowRewriter.Rewrites.JoinPureUnit
import DataflowRewriter.Rewrites.JoinSplitElim
import DataflowRewriter.Rewrites.JoinAssocL
import DataflowRewriter.Rewrites.JoinAssocR
import DataflowRewriter.Rewrites.JoinComm
import DataflowRewriter.Rewrites.ForkPure
import DataflowRewriter.Rewrites.ForkJoin
import DataflowRewriter.Rewrites.JoinRewrite
import DataflowRewriter.Rewrites.JoinRewriteCorrect

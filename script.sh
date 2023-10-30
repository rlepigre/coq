#!/bin/bash

# Reset to the version tag, to allow re-running the script.
mv script.sh script.sh.backup
git reset --hard V8.18.0
mv script.sh.backup script.sh

# Picking a merge commit from master.
pick () {
  git cherry-pick -m 1 ${1}
}

# Merge PR #17702: Produce profiles in google trace format.
pick a99e6ec32433c0893432c334f633af33e04c3830
# Merge PR #17744: Add instruction counting support.
pick 4f1fda3fe3135fd76f2c55eff323fa5c00aac634
# Merge PR #18105: Rename perf/perf.c into perf/coq_perf.
pick e6a957898fb184825043af45bf541e9e505bc1ac

# Merge PR #17789: Fix Typeclasses Unique Instances option.
pick 577b1330623b6bae1cdee8143dd276ad0cf9a39b

# Merge PR #17946: Use CWarnings in coqdep
pick d52a29a3cdf9a83b38dc25cc925d2af420fdf812

# Merge PR #17777: Expose [Evarconv.unify] as an Ltac2 primitive.
pick afaecfdae4b5573d72f4f5ccf95be83903def9b3
# Merge PR #17788: Correctly handle opaque primitive projections in Evarconv
pick 96dd2317ee2aa78d22ddd4b4f0103661cf85c49a

# Merge PR #17638: Guard many unguarded try..with expressions
pick f53426c0760e5ce5515c878b1824a18ab16fd7f6
# Merge PR #13071: resolve_tc c solves typeclasses appearing in c
pick 1f9e1ec638b2e0b57c8246c7898c608b1cac5cbf
# Merge PR #17878: Declaration of Ltac2 primitives using a GADT-based mechanism
pick 6ff90d83d4b026982a2d53b2929bb7528a5b967b
# Fixing conflict.
patch plugins/ltac2/tac2stdlib.ml <<EOF
478,486d477
< <<<<<<< HEAD
< let () = define_prim1 "tac_revert" (list ident) begin fun ids ->
<   Tactics.revert ids
< end
< ||||||| parent of 6ff90d83d4 (Merge PR #17878: Declaration of Ltac2 primitives using a GADT-based mechanism)
< let () = define_prim1 "tac_revert" (list ident) begin fun ids ->
<   Generalize.revert ids
< end
< =======
489d479
< >>>>>>> 6ff90d83d4 (Merge PR #17878: Declaration of Ltac2 primitives using a GADT-based mechanism)
492c482
<   define "tac_revert" (list ident @-> tac unit) Generalize.revert
---
>   define "tac_revert" (list ident @-> tac unit) Tactics.revert
EOF
git add plugins/ltac2/tac2stdlib.ml
git cherry-pick --continue --no-edit

# Merge PR #18095: Extensions to the Ltac2 standard library
pick 49fce3a967a93200f569a51b28085c9e74bb1378
# Fixing bad automatic conflict resolution.
patch plugins/ltac2/tac2core.ml <<EOF
697c697
<     return (Value.of_ext val_constructor ((ind, i), (k + 1)))
---
>     return (Tac2ffi.of_ext val_constructor ((ind, i), (k + 1)))
EOF
git add plugins/ltac2/tac2core.ml
git commit -m "Fixup badly resolved conflict when cherry-picking #18095."

# Merge PR #18152: Restrict zify saturation to work on hypotheses of the initial goal
pick be8726c0a5d49673132a687b815fb3f68a243127

# Make Coq_Micromega.witness_list tail recursive.
git cherry-pick db826e12753a03446421d51569dedae8691f2632

# [coqdep] normalize more paths.
git cherry-pick 69ca0e9b3168943376ee8b434ce1f3a647da4043

# Merge PR #18166: Don't emit deprecated warnings in name generation
pick 5d0ded0ce135b9b4a1071c995515fcf427af875f

# Merge PR #17883: Delayed substitution in VM normalization of telescopes.
# Required for #18023 to apply more cleanly.
pick c1b18fe6ae23316398659d8fb2c237814630f857

# Merge PR #17792: Stop relying on opaque proof accessors in funind.
# Required for #18023 to apply more cleanly.
pick c0e7d0c9789b46245e8478e2793a1c20d049fd3d

# Adding folding and equality on pairs.
# Required for #18023 to apply more cleanly.
git cherry-pick 2928cbbfd521e56976ca8d1a6148ee2b8a156ea7

# Merge PR #18023: Some cleanup around CClosure
pick b187b85016b4d7076548da2c6f2cb781de899eb0
# Fixing conflict.
patch pretyping/tacred.ml <<EOF
1369d1368
< <<<<<<< HEAD
1371c1370
<              (special_red_case betadeltazeta env sigma (ci,u,pms,p,iv,c,lf),
---
>              (special_red_case RedFlags.betadeltazeta env sigma (ci,u,pms,p,iv,c,lf),
1374,1384d1372
< ||||||| parent of b187b85016 (Merge PR #18023: Some cleanup around CClosure)
<         begin match special_red_case betadeltazeta env sigma (ci,u,pms,p,iv,c,lf) with
<         | Reduced c -> (c, stack)
<         | NotReducible -> raise NotStepReducible
<         end
< =======
<         begin match special_red_case RedFlags.betadeltazeta env sigma (ci,u,pms,p,iv,c,lf) with
<         | Reduced c -> (c, stack)
<         | NotReducible -> raise NotStepReducible
<         end
< >>>>>>> b187b85016 (Merge PR #18023: Some cleanup around CClosure)
1386,1387c1374
< <<<<<<< HEAD
<           (try match reduce_fix betadeltazeta env sigma fix stack with
---
>           (try match reduce_fix RedFlags.betadeltazeta env sigma fix stack with
1391,1401d1377
< ||||||| parent of b187b85016 (Merge PR #18023: Some cleanup around CClosure)
<         begin match reduce_fix betadeltazeta env sigma None fix stack with
<         | Reduced s' -> s'
<         | NotReducible -> raise NotStepReducible
<         end
< =======
<         begin match reduce_fix RedFlags.betadeltazeta env sigma None fix stack with
<         | Reduced s' -> s'
<         | NotReducible -> raise NotStepReducible
<         end
< >>>>>>> b187b85016 (Merge PR #18023: Some cleanup around CClosure)
1404d1379
< <<<<<<< HEAD
1406c1381
<              fst (red_elim_const betadeltazeta env sigma ref u stack)
---
>              fst (red_elim_const RedFlags.betadeltazeta env sigma ref u stack)
1408,1416d1382
< ||||||| parent of b187b85016 (Merge PR #18023: Some cleanup around CClosure)
<           begin match red_elim_const betadeltazeta env sigma ref u stack with
<           | Reduced (c, _) -> c
<           | NotReducible ->
< =======
<           begin match red_elim_const RedFlags.betadeltazeta env sigma ref u stack with
<           | Reduced (c, _) -> c
<           | NotReducible ->
< >>>>>>> b187b85016 (Merge PR #18023: Some cleanup around CClosure)
EOF
git add pretyping/tacred.ml
git cherry-pick --continue --no-edit

# Add compatibility layer with the [RedFlags] move.
cat >> kernel/cClosure.mli <<EOF

val all : RedFlags.reds
val allnolet : RedFlags.reds
val beta : RedFlags.reds
val betadeltazeta : RedFlags.reds
val betaiota : RedFlags.reds
val betaiotazeta : RedFlags.reds
val betazeta : RedFlags.reds
val delta : RedFlags.reds
val zeta : RedFlags.reds
val nored : RedFlags.reds

module RedFlags : sig
  include module type of RedFlags
end with type reds = RedFlags.reds and type red_kind = RedFlags.red_kind
EOF
cat >> kernel/cClosure.ml <<EOF

let all = RedFlags.all
let allnolet = RedFlags.allnolet
let beta = RedFlags.beta
let betadeltazeta = RedFlags.betadeltazeta
let betaiota = RedFlags.betaiota
let betaiotazeta = RedFlags.betaiotazeta
let betazeta = RedFlags.betazeta
let delta = RedFlags.delta
let zeta = RedFlags.zeta
let nored = RedFlags.nored

module RedFlags = RedFlags
EOF
git add kernel/cClosure.ml kernel/cClosure.mli
git commit -m "Compatibility layer for RedFlags (related to #18023)."

# Use Cpred for simpl_never, more efficient Tacred.make_simpl_reds #18187
git cherry-pick e38280a25744836d983cbdb4805cd98619570241
git cherry-pick 7f993a3aaa135052ee650dec2768fee809c2bea8
patch pretyping/tacred.ml <<EOF
793,794c793
< <<<<<<< HEAD
<              (match unf, get (GlobRef.ConstRef (Projection.constant p)) with
---
>              (match unf, ReductionBehaviour.get (Projection.constant p) with
796,802d794
< ||||||| parent of 7f993a3aaa (ReductionBehaviour is on constants, not any globref)
<              match unf, get (GlobRef.ConstRef (Projection.constant p)) with
<               | false, Some NeverUnfold -> NotReducible
< =======
<              match unf, ReductionBehaviour.get (Projection.constant p) with
<               | false, Some NeverUnfold -> NotReducible
< >>>>>>> 7f993a3aaa (ReductionBehaviour is on constants, not any globref)
EOF
git add pretyping/tacred.ml
git cherry-pick --continue --no-edit
git cherry-pick 08ae9a45eb6132e03e3b92049e8defbb536de914

# Revert "Stop catching anomalies from conversion"
git cherry-pick 0f1d10dc4afab04a8ec679320105c64d0f33cfb3

# Don't nf_univ_variables in prepare_hint
# Seems not useful and may result in a speedup
# cf https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs-.26-plugin-devs\
#    /topic/Universe.20normalization.20in.20.60make_local_hint_db.60
git cherry-pick 908cecc9390361800c5ff3191046e92fa3c4b2fe

# Recording the script.
git add script.sh
git commit \
  -m "Cherry-picking script used to create this branch." \
  --author "Rodolphe Lepigre <rodolphe@bedrocksystems.com>"

# Tagging and pushing.
git tag -f V8.18.0+bedrock
git push --force-with-lease
git push -f --tags

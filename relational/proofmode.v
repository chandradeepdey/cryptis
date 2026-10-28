(** Entry point of the relational proof toolkit: the ghost state updates of
  [proofmode/updates.v], the tactics of [proofmode/tactics.v], and the
  tactics that run the programs through the primitives.  These find the
  one-sided specs through the instances of [proofmode/classes.v]; importing
  the spec files here puts the instances of every primitive in scope.

  - [rel_prims_l] takes the left program as far as it can go on its own: pure
    steps, the primitives on terms, the list and AVL operations, and list
    literals.  It stops at the first step that needs the relation, such as a
    send or a receive.  [rel_prims_r] does the same on the right and
    [rel_prims] does both.
  - Each step walks the program once to its next redex and applies the spec
    that the [rel_prims] database gives for it ([rel_prim_l], [rel_prim_r]);
    the cost of a step does not depend on how many primitives there are.  A
    new primitive needs only a [RelPrimL] and a [RelPrimR] instance. *)

From iris.proofmode Require Import environments.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper.primitives Require Import pre_term_spec simple_spec comp_spec with_cryptis_spec.
From cryptis.hyper.proofmode Require Export classes updates tactics.

Tactic Notation "rel_apply_at_l" constr(K) open_constr(lem) :=
  iPoseProofCore lem as false (fun H => rel_bind_ctx_l K; iApplyHyp H);
  try rel_finish.

Tactic Notation "rel_apply_at_r" constr(K) open_constr(lem) :=
  iPoseProofCore lem as false (fun H => rel_bind_ctx_r K; iApplyHyp H);
  try lazymatch goal with |- _ ⊆ _ => solve_ndisj end;
  try rel_finish.

Ltac rel_prim_l :=
  lazymatch goal with |- @envs_entails (iPropI ?Σ) _ _ =>
  rel_reshape_cont_l ltac:(fun K e =>
    let H := constr:(ltac:(typeclasses eauto with rel_prims) : RelPrimL Σ e _) in
    rel_apply_at_l K (rel_prim_l_spec H))
  end.

Ltac rel_prim_r :=
  lazymatch goal with |- @envs_entails (iPropI ?Σ) _ _ =>
  rel_reshape_cont_r ltac:(fun K e =>
    let H := constr:(ltac:(typeclasses eauto with rel_prims) : RelPrimR Σ e _) in
    rel_apply_at_r K (rel_prim_r_spec H))
  end.

Ltac rel_prims_l :=
  repeat (rel_later; rel_pures_l; rel_prim_l);
  rel_later; rel_pures_l.
Ltac rel_prims_r :=
  repeat (rel_later; rel_pures_r; rel_prim_r);
  rel_later; rel_pures_r.

Ltac rel_prims := rel_prims_l; rel_prims_r.

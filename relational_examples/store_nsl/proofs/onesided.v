(** One-sided steps of the server of the NSL store case study.  [handle_model]
    says what [store_handle] computes: the reply to a request and the
    database after it.  The specs run [store_handle] on one side only, so they
    hold whatever the request is. *)

From mathcomp Require Import ssreflect.
From reloc Require Import reloc.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.lib Require Import avl_spec list_match_spec.
From cryptis.hyper.primitives Require Import simple_spec.
From cryptis.hyper.examples.store_nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition handle_store_model (db : AVL.tree) (req : term) :
  option (term * AVL.tree) :=
  match Spec.to_list req with
  | Some [k; v] =>
    match Spec.to_int k, Spec.to_int v with
    | Some k, Some v => Some (TInt 0, AVL.insert k v db)
    | _, _ => None
    end
  | _ => None
  end.

Definition handle_load_model (db : AVL.tree) (k : term) :
  option (term * AVL.tree) :=
  match Spec.to_int k with
  | Some k => Some (TInt (default 0%Z (AVL.lookup k db)), db)
  | None => None
  end.

Definition handle_model (db : AVL.tree) (m : term) : option (term * AVL.tree) :=
  match Spec.untag (Tag (storeN.@"store")) m with
  | Some req => handle_store_model db req
  | None =>
    match Spec.untag (Tag (storeN.@"load")) m with
    | Some k => handle_load_model db k
    | None => None
    end
  end.

Definition handle_val (r : option (term * AVL.tree)) : val :=
  match r with
  | Some (t, db) => SOMEV (t : val, repr db)%V
  | None => NONEV
  end.

Section OneSided.

Context `{!relocG Σ}.

Lemma rel_store_handle_l K e db m Ψ :
  (REL fill K (handle_val (handle_model db m) : expr) << e : Ψ) -∗
  REL fill K (store_handle (repr db) m) << e : Ψ.
Proof.
iIntros "post". rewrite /store_handle /handle_model. rel_pures_l.
rel_apply_l rel_untag_l.
case: (Spec.untag _ m) => [req|] /=; rel_pures_l.
- rewrite /store_handle_store /handle_store_model. rel_pures_l.
  rel_apply_l rel_list_of_term_l.
  case: (Spec.to_list req) => [ts|] /=; rel_pures_l; last by iApply "post".
  rewrite ?subst_list_match /=. rel_apply_l (rel_list_match_l (A:=term)).
  case: decide => len.
  + destruct ts as [|k [|v [|? ?]]] => //=. rel_pures_l.
    rel_apply_l rel_to_int_l.
    case: (Spec.to_int k) => [k'|] /=; rel_pures_l; last by iApply "post".
    rel_apply_l rel_to_int_l.
    case: (Spec.to_int v) => [v'|] /=; rel_pures_l; last by iApply "post".
    rel_apply_l rel_avl_insert_l. rel_pures_l. by iApply "post".
  + destruct ts as [|k [|v [|? ?]]] => //=; rel_pures_l; by iApply "post".
- rel_apply_l rel_untag_l.
  case: (Spec.untag _ m) => [k|] /=; rel_pures_l; last by iApply "post".
  rewrite /store_handle_load /handle_load_model. rel_pures_l.
  rel_apply_l rel_to_int_l.
  case: (Spec.to_int k) => [k'|] /=; rel_pures_l; last by iApply "post".
  rel_apply_l rel_avl_lookup_l.
  case: (AVL.lookup k' db) => [v|] /=; rel_pures_l;
    rel_apply_l rel_tint_l; rel_pures_l; by iApply "post".
Qed.

Lemma rel_store_handle_r K e db m Ψ :
  (REL e << fill K (handle_val (handle_model db m) : expr) : Ψ) -∗
  REL e << fill K (store_handle (repr db) m) : Ψ.
Proof.
iIntros "post". rewrite /store_handle /handle_model. rel_pures_r.
rel_apply_r rel_untag_r.
case: (Spec.untag _ m) => [req|] /=; rel_pures_r.
- rewrite /store_handle_store /handle_store_model. rel_pures_r.
  rel_apply_r rel_list_of_term_r.
  case: (Spec.to_list req) => [ts|] /=; rel_pures_r; last by iApply "post".
  rewrite ?subst_list_match /=. rel_apply_r (rel_list_match_r (A:=term)).
  case: decide => len.
  + destruct ts as [|k [|v [|? ?]]] => //=. rel_pures_r.
    rel_apply_r rel_to_int_r.
    case: (Spec.to_int k) => [k'|] /=; rel_pures_r; last by iApply "post".
    rel_apply_r rel_to_int_r.
    case: (Spec.to_int v) => [v'|] /=; rel_pures_r; last by iApply "post".
    rel_apply_r rel_avl_insert_r. rel_pures_r. by iApply "post".
  + destruct ts as [|k [|v [|? ?]]] => //=; rel_pures_r; by iApply "post".
- rel_apply_r rel_untag_r.
  case: (Spec.untag _ m) => [k|] /=; rel_pures_r; last by iApply "post".
  rewrite /store_handle_load /handle_load_model. rel_pures_r.
  rel_apply_r rel_to_int_r.
  case: (Spec.to_int k) => [k'|] /=; rel_pures_r; last by iApply "post".
  rel_apply_r rel_avl_lookup_r.
  case: (AVL.lookup k' db) => [v|] /=; rel_pures_r;
    rel_apply_r rel_tint_r; rel_pures_r; by iApply "post".
Qed.

End OneSided.

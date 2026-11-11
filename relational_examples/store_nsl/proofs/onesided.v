(** One-sided steps of the server of the NSL store case study.  [handle_model]
    says what [store_handle] computes: the reply to a request and the
    database after it.  The specs run [store_handle] on one side only, so they
    hold whatever the request is. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From cryptis.hyper Require Import lib.
From cryptis.hyper.lib Require Import avl list_match.
From cryptis.hyper.primitives Require Import simple.
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

Definition handle_db (db : AVL.tree) (m : term) : AVL.tree :=
  from_option snd db (handle_model db m).

Definition handle_val (st : val) (r : option (term * AVL.tree)) : val :=
  match r with
  | Some (t, _) => SOMEV (t : val, st)%V
  | None => NONEV
  end.

Section OneSided.

Context `{!relocG Σ}.

Lemma refines_store_handle_l K e st db m Ψ :
  is_avl st db -∗
  (is_avl st (handle_db db m) -∗
   REL fill K (handle_val st (handle_model db m) : expr) << e : Ψ) -∗
  REL fill K (store_handle st m) << e : Ψ.
Proof.
iIntros "Hdb post". rewrite /store_handle /handle_db /handle_model. rel_pures_l.
rel_apply_l refines_untag_l.
case: (Spec.untag _ m) => [req|] /=; rel_pures_l.
- rewrite /store_handle_store /handle_store_model. rel_pures_l.
  rel_apply_l refines_list_of_term_l.
  case: (Spec.to_list req) => [ts|] /=; rel_pures_l; last by iApply ("post" with "Hdb").
  rewrite ?subst_list_match /=. rel_apply_l (refines_list_match_l (A:=term)).
  case: decide => len.
  + destruct ts as [|k [|v [|? ?]]] => //=. rel_pures_l.
    rel_apply_l refines_to_int_l.
    case: (Spec.to_int k) => [k'|] /=; rel_pures_l; last by iApply ("post" with "Hdb").
    rel_apply_l refines_to_int_l.
    case: (Spec.to_int v) => [v'|] /=; rel_pures_l; last by iApply ("post" with "Hdb").
    rel_apply_l (refines_avl_insert_l with "Hdb"). iIntros "Hdb". rel_pures_l.
    by iApply ("post" with "Hdb").
  + destruct ts as [|k [|v [|? ?]]] => //=; rel_pures_l; by iApply ("post" with "Hdb").
- rel_apply_l refines_untag_l.
  case: (Spec.untag _ m) => [k|] /=; rel_pures_l; last by iApply ("post" with "Hdb").
  rewrite /store_handle_load /handle_load_model. rel_pures_l.
  rel_apply_l refines_to_int_l.
  case: (Spec.to_int k) => [k'|] /=; rel_pures_l; last by iApply ("post" with "Hdb").
  rel_apply_l (refines_avl_lookup_l with "Hdb"). iIntros "Hdb".
  case: (AVL.lookup k' db) => [v|] /=; rel_pures_l;
    rel_apply_l refines_tint_l; rel_pures_l; by iApply ("post" with "Hdb").
Qed.

Lemma refines_store_handle_r K e st db m Ψ :
  is_avl_spec st db -∗
  (is_avl_spec st (handle_db db m) -∗
   REL e << fill K (handle_val st (handle_model db m) : expr) : Ψ) -∗
  REL e << fill K (store_handle st m) : Ψ.
Proof.
iIntros "Hdb post". rewrite /store_handle /handle_db /handle_model. rel_pures_r.
rel_apply_r refines_untag_r.
case: (Spec.untag _ m) => [req|] /=; rel_pures_r.
- rewrite /store_handle_store /handle_store_model. rel_pures_r.
  rel_apply_r refines_list_of_term_r.
  case: (Spec.to_list req) => [ts|] /=; rel_pures_r; last by iApply ("post" with "Hdb").
  rewrite ?subst_list_match /=. rel_apply_r (refines_list_match_r (A:=term)).
  case: decide => len.
  + destruct ts as [|k [|v [|? ?]]] => //=. rel_pures_r.
    rel_apply_r refines_to_int_r.
    case: (Spec.to_int k) => [k'|] /=; rel_pures_r; last by iApply ("post" with "Hdb").
    rel_apply_r refines_to_int_r.
    case: (Spec.to_int v) => [v'|] /=; rel_pures_r; last by iApply ("post" with "Hdb").
    rel_apply_r (refines_avl_insert_r with "Hdb"). iIntros "Hdb". rel_pures_r.
    by iApply ("post" with "Hdb").
  + destruct ts as [|k [|v [|? ?]]] => //=; rel_pures_r; by iApply ("post" with "Hdb").
- rel_apply_r refines_untag_r.
  case: (Spec.untag _ m) => [k|] /=; rel_pures_r; last by iApply ("post" with "Hdb").
  rewrite /store_handle_load /handle_load_model. rel_pures_r.
  rel_apply_r refines_to_int_r.
  case: (Spec.to_int k) => [k'|] /=; rel_pures_r; last by iApply ("post" with "Hdb").
  rel_apply_r (refines_avl_lookup_r with "Hdb"). iIntros "Hdb".
  case: (AVL.lookup k' db) => [v|] /=; rel_pures_r;
    rel_apply_r refines_tint_r; rel_pures_r; by iApply ("post" with "Hdb").
Qed.

End OneSided.

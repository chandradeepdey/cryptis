(** Entry point of the relational proof toolkit: the ghost state updates of
  [proofmode/updates.v], the tactics of [proofmode/tactics.v], and the
  tactics that run the programs through the primitives, which need every
  primitive's one-sided spec and therefore live here, above them.

  - [rel_prims_l] takes the left program as far as it can go on its own: pure
    steps, the primitives on terms, the list and AVL operations, and list
    literals.  It stops at the first step that needs the relation, such as a
    send or a receive.  [rel_prims_r] does the same on the right and
    [rel_prims] does both. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis primitives.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper.primitives Require Import pre_term_spec simple_spec comp_spec with_cryptis_spec.
From cryptis.hyper.proofmode Require Export updates tactics.

Ltac rel_prim_l :=
  first
  [ rel_apply_l rel_tint_l | rel_apply_l rel_to_int_l
  | rel_apply_l rel_tuple_l | rel_apply_l rel_untuple_l
  | rel_apply_l rel_term_of_list_l | rel_apply_l rel_list_of_term_l
  | rel_apply_l rel_tag_l | rel_apply_l rel_untag_l
  | rel_apply_l rel_key_l | rel_apply_l rel_seal_l | rel_apply_l rel_hash_l
  | rel_apply_l rel_derive_aenc_key_l | rel_apply_l rel_derive_senc_key_l
  | rel_apply_l rel_derive_sign_key_l
  | rel_apply_l rel_to_key_l | rel_apply_l rel_open_key_l | rel_apply_l rel_open_l
  | rel_apply_l rel_enc_l | rel_apply_l rel_dec_l
  | rel_apply_l rel_aenc'_l | rel_apply_l rel_senc'_l | rel_apply_l rel_sign'_l
  | rel_apply_l rel_pkey_l | rel_apply_l rel_is_key_l
  | rel_apply_l rel_has_key_type_l
  | rel_apply_l rel_eq_term_l | rel_apply_l rel_texp_l | rel_apply_l rel_tmul_l
  | rel_apply_l rel_tinv_l | rel_apply_l rel_tone_l
  | rel_apply_l rel_tgmul_l | rel_apply_l rel_tginv_l | rel_apply_l rel_tgone_l
  | rel_apply_l rel_avl_insert_l | rel_apply_l rel_avl_lookup_l
  | rel_apply_l rel_avl_to_list_l | rel_apply_l rel_random_adec_l ].

Ltac rel_prim_r :=
  first
  [ rel_apply_r rel_tint_r | rel_apply_r rel_to_int_r
  | rel_apply_r rel_tuple_r | rel_apply_r rel_untuple_r
  | rel_apply_r rel_term_of_list_r | rel_apply_r rel_list_of_term_r
  | rel_apply_r rel_tag_r | rel_apply_r rel_untag_r
  | rel_apply_r rel_key_r | rel_apply_r rel_seal_r | rel_apply_r rel_hash_r
  | rel_apply_r rel_derive_aenc_key_r | rel_apply_r rel_derive_senc_key_r
  | rel_apply_r rel_derive_sign_key_r
  | rel_apply_r rel_to_key_r | rel_apply_r rel_open_key_r | rel_apply_r rel_open_r
  | rel_apply_r rel_enc_r | rel_apply_r rel_dec_r
  | rel_apply_r rel_aenc'_r | rel_apply_r rel_senc'_r | rel_apply_r rel_sign'_r
  | rel_apply_r rel_pkey_r | rel_apply_r rel_is_key_r
  | rel_apply_r rel_has_key_type_r
  | rel_apply_r rel_eq_term_r | rel_apply_r rel_texp_r | rel_apply_r rel_tmul_r
  | rel_apply_r rel_tinv_r | rel_apply_r rel_tone_r
  | rel_apply_r rel_tgmul_r | rel_apply_r rel_tginv_r | rel_apply_r rel_tgone_r
  | rel_apply_r rel_avl_insert_r | rel_apply_r rel_avl_lookup_r
  | rel_apply_r rel_avl_to_list_r | rel_apply_r rel_random_adec_r ].

Ltac rel_list_l :=
  rel_apply_l (rel_nil_l (A:=term)); repeat rel_apply_l rel_cons_l;
  rel_apply_l rel_term_of_list_l.
Ltac rel_list_r :=
  rel_apply_r (rel_nil_r (A:=term)); repeat rel_apply_r rel_cons_r;
  rel_apply_r rel_term_of_list_r.

Ltac rel_prims_l :=
  repeat (rel_later; rel_pures_l; first [rel_prim_l | rel_list_l]);
  rel_later; rel_pures_l.
Ltac rel_prims_r :=
  repeat (rel_later; rel_pures_r; first [rel_prim_r | rel_list_r]);
  rel_later; rel_pures_r.

Ltac rel_prims := rel_prims_l; rel_prims_r.

(** Entry point of the relational proof toolkit: the ghost state updates of
  [proofmode/updates.v], the tactics of [proofmode/tactics.v], and the
  tactics that run the programs through the primitives, which need every
  primitive's one-sided spec and therefore live here, above them.

  - [rel_prims_l] takes the left program as far as it can go on its own: pure
    steps, the primitives on terms, the list and AVL operations, and list
    literals.  It stops at the first step that needs the relation, such as a
    send or a receive.  [rel_prims_r] does the same on the right and
    [rel_prims] does both.
  - Each step walks the program once to its next redex, an application whose
    arguments are all values, and applies the spec of the primitive at its
    head ([rel_prim_l], [rel_prim_r]); the cost of a step does not depend on
    how many primitives there are. *)

From reloc Require Import reloc.
From cryptis Require Import lib cryptis primitives.
From cryptis.lib Require Import avl.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.lib Require Import avl_spec.
From cryptis.hyper.primitives Require Import pre_term_spec simple_spec comp_spec with_cryptis_spec.
From cryptis.hyper.proofmode Require Export updates tactics.

(** The function at the head of an application whose arguments are all
    values. *)
Ltac rel_redex_head e :=
  lazymatch e with
  | App ?f (Val _) =>
    lazymatch f with
    | Val ?v => v
    | _ => rel_redex_head f
    end
  end.

Tactic Notation "rel_apply_at_l" constr(K) open_constr(lem) :=
  iPoseProofCore lem as false (fun H => rel_bind_ctx_l K; iApplyHyp H);
  try rel_finish.

Tactic Notation "rel_apply_at_r" constr(K) open_constr(lem) :=
  iPoseProofCore lem as false (fun H => rel_bind_ctx_r K; iApplyHyp H);
  try lazymatch goal with |- _ ⊆ _ => solve_ndisj end;
  try rel_finish.

Ltac rel_prim_at_l K f :=
  lazymatch f with
  | tint => rel_apply_at_l K rel_tint_l
  | to_int => rel_apply_at_l K rel_to_int_l
  | tuple => rel_apply_at_l K rel_tuple_l
  | untuple => rel_apply_at_l K rel_untuple_l
  | term_of_list => rel_apply_at_l K rel_term_of_list_l
  | list_of_term => rel_apply_at_l K rel_list_of_term_l
  | tag => rel_apply_at_l K rel_tag_l
  | untag => rel_apply_at_l K rel_untag_l
  | key => rel_apply_at_l K rel_key_l
  | seal => rel_apply_at_l K rel_seal_l
  | hash => rel_apply_at_l K rel_hash_l
  | derive_aenc_key => rel_apply_at_l K rel_derive_aenc_key_l
  | derive_senc_key => rel_apply_at_l K rel_derive_senc_key_l
  | derive_sign_key => rel_apply_at_l K rel_derive_sign_key_l
  | to_key => rel_apply_at_l K rel_to_key_l
  | open_key => rel_apply_at_l K rel_open_key_l
  | open => rel_apply_at_l K rel_open_l
  | enc => rel_apply_at_l K rel_enc_l
  | dec => rel_apply_at_l K rel_dec_l
  | aenc => rel_apply_at_l K rel_aenc'_l
  | senc => rel_apply_at_l K rel_senc'_l
  | sign => rel_apply_at_l K rel_sign'_l
  | pkey => rel_apply_at_l K rel_pkey_l
  | is_key => rel_apply_at_l K rel_is_key_l
  | has_key_type => rel_apply_at_l K rel_has_key_type_l
  | eq_term => rel_apply_at_l K rel_eq_term_l
  | texp => rel_apply_at_l K rel_texp_l
  | tmul => rel_apply_at_l K rel_tmul_l
  | tinv => rel_apply_at_l K rel_tinv_l
  | tone => rel_apply_at_l K rel_tone_l
  | tgmul => rel_apply_at_l K rel_tgmul_l
  | tginv => rel_apply_at_l K rel_tginv_l
  | tgone => rel_apply_at_l K rel_tgone_l
  | avl_insert => rel_apply_at_l K rel_avl_insert_l
  | avl_lookup => rel_apply_at_l K rel_avl_lookup_l
  | avl_to_list => rel_apply_at_l K rel_avl_to_list_l
  | random_adec => rel_apply_at_l K rel_random_adec_l
  | CONS => first [ rel_apply_at_l K rel_cons_l
              | rel_apply_at_l K (rel_cons_nil_l (A:=term)) ]
  end.

Ltac rel_prim_at_r K f :=
  lazymatch f with
  | tint => rel_apply_at_r K rel_tint_r
  | to_int => rel_apply_at_r K rel_to_int_r
  | tuple => rel_apply_at_r K rel_tuple_r
  | untuple => rel_apply_at_r K rel_untuple_r
  | term_of_list => rel_apply_at_r K rel_term_of_list_r
  | list_of_term => rel_apply_at_r K rel_list_of_term_r
  | tag => rel_apply_at_r K rel_tag_r
  | untag => rel_apply_at_r K rel_untag_r
  | key => rel_apply_at_r K rel_key_r
  | seal => rel_apply_at_r K rel_seal_r
  | hash => rel_apply_at_r K rel_hash_r
  | derive_aenc_key => rel_apply_at_r K rel_derive_aenc_key_r
  | derive_senc_key => rel_apply_at_r K rel_derive_senc_key_r
  | derive_sign_key => rel_apply_at_r K rel_derive_sign_key_r
  | to_key => rel_apply_at_r K rel_to_key_r
  | open_key => rel_apply_at_r K rel_open_key_r
  | open => rel_apply_at_r K rel_open_r
  | enc => rel_apply_at_r K rel_enc_r
  | dec => rel_apply_at_r K rel_dec_r
  | aenc => rel_apply_at_r K rel_aenc'_r
  | senc => rel_apply_at_r K rel_senc'_r
  | sign => rel_apply_at_r K rel_sign'_r
  | pkey => rel_apply_at_r K rel_pkey_r
  | is_key => rel_apply_at_r K rel_is_key_r
  | has_key_type => rel_apply_at_r K rel_has_key_type_r
  | eq_term => rel_apply_at_r K rel_eq_term_r
  | texp => rel_apply_at_r K rel_texp_r
  | tmul => rel_apply_at_r K rel_tmul_r
  | tinv => rel_apply_at_r K rel_tinv_r
  | tone => rel_apply_at_r K rel_tone_r
  | tgmul => rel_apply_at_r K rel_tgmul_r
  | tginv => rel_apply_at_r K rel_tginv_r
  | tgone => rel_apply_at_r K rel_tgone_r
  | avl_insert => rel_apply_at_r K rel_avl_insert_r
  | avl_lookup => rel_apply_at_r K rel_avl_lookup_r
  | avl_to_list => rel_apply_at_r K rel_avl_to_list_r
  | random_adec => rel_apply_at_r K rel_random_adec_r
  | CONS => first [ rel_apply_at_r K rel_cons_r
              | rel_apply_at_r K (rel_cons_nil_r (A:=term)) ]
  end.

Ltac rel_prim_l :=
  rel_reshape_cont_l ltac:(fun K e =>
    let f := rel_redex_head e in rel_prim_at_l K f).

Ltac rel_prim_r :=
  rel_reshape_cont_r ltac:(fun K e =>
    let f := rel_redex_head e in rel_prim_at_r K f).

Ltac rel_prims_l :=
  repeat (rel_later; rel_pures_l; rel_prim_l);
  rel_later; rel_pures_l.
Ltac rel_prims_r :=
  repeat (rel_later; rel_pures_r; rel_prim_r);
  rel_later; rel_pures_r.

Ltac rel_prims := rel_prims_l; rel_prims_r.

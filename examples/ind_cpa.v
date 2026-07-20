From stdpp Require Import base gmap.
From mathcomp Require Import ssreflect.
From iris.algebra Require Import agree auth csum gset gmap excl frac.
From iris.algebra Require Import reservation_map.
From iris.heap_lang Require Import notation proofmode adequacy.
From iris.heap_lang.lib Require Import par nondet_bool.
From cryptis Require Import lib term cryptis primitives tactics.
From cryptis Require Import role.
From cryptis.primitives Require Import attacker.

From reloc Require Import reloc.
From cryptis.core Require Import minted_spec term_meta_spec rel.
From cryptis.primitives Require Import simple_spec with_cryptis_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPA.

Context `{!relocG Σ, !public_relGS Σ}.
Notation iProp := (iProp Σ).

Implicit Types (t nonce : term).
Implicit Types (skA : aenc_key).

Variable N : namespace.

(*

* --> A: msg_0
* --> A: msg_1
A --> *: if b then {nonce, msg_0}@pkA else {nonce, msg_1}@pkA

*)
Definition alice : val := λ: "c",
  let: "skA" := mk_aenc_key #() in
  let: "pkA" := pkey "skA" in
  send "c" "pkA";;
  let: "nonce" := mk_nonce #() in
  bind: "msg_0" := recv "c" in
  bind: "msg_1" := recv "c" in
  let: "b" := nondet_bool #() in
  let: "msg" := if: "b" then "msg_0" else "msg_1" in
  send "c" (aenc "pkA" (Tag $ N.@"m") (term_of_list ["nonce"; "msg"]));;
  bind: "b'" := recv "c" in
  let: "b'" := eq_term (TInt 1) "b'" in
  ("b", "b'").

Lemma rel_alice c c' (b: bool) :
  cryptis_rel_ctx -∗
  channel_rel c c' -∗
  REL alice c << alice c' : λ p1 p2,
    ⌜∃ b1 b'1 b2 b'2 : bool,
    p1 = (#b1, #b'1)%V ∧ p2 = (#b2, #b'2)%V ∧
    (b = b1 → b ≠ b2 ∧ b'1 = b'2)⌝.
Proof.
iIntros "#Hctx #Hc". rewrite /alice.
rel_pures_l. rel_pures_r.
rel_apply_l (rel_mk_aenc_key_l with "[//]").
iIntros (skA) "#mint token".
rel_apply_r (rel_mk_aenc_key_r with "[//]").
iIntros "%skA' #mint_spec token_spec".
rel_pures_l. rel_pures_r.
rel_apply_l rel_pkey_l. rel_apply_r rel_pkey_r.
rel_pures_l. rel_pures_r.
rel_bind_l (send _ _). rel_bind_r (send _ _).
iAssert (|={⊤}=> publicly_related (Spec.pkey skA) (Spec.pkey skA'))%I with "[token token_spec]" as ">#Hpub".
{ iApply publicly_related_aenc_key_pkey. iLeft.
  iApply publicly_related_aenc_key_seed. admit. }
iApply (refines_bind _ _ _ lrel_unit);
first by iApply (rel_send with "[] []") => //=.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.

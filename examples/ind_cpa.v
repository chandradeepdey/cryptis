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
From cryptis Require Import lib_spec.
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
  let: "msg_0" := recv "c" in
  let: "msg_1" := recv "c" in
  let: "b" := nondet_bool #() in
  let: "msg" := if: "b" then "msg_0" else "msg_1" in
  send "c" (aenc "pkA" (Tag $ N.@"m") (term_of_list ["nonce"; "msg"]));;
  let: "b'" := recv "c" in
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
iIntros (skA) "#mint_skA token_skA".
rel_apply_r (rel_mk_aenc_key_r with "[//]").
iIntros "%skA' #mint_spec_skA' token_spec_skA'".
rel_pures_l. rel_pures_r.
rel_apply_l rel_pkey_l. rel_apply_r rel_pkey_r.
rel_pures_l. rel_pures_r.
iAssert (|={⊤}=> publicly_related (Spec.pkey skA) (Spec.pkey skA'))%I
          with "[token_skA token_spec_skA']" as ">#Hpub".
{ iApply publicly_related_aenc_key_pkey. iLeft.
  iApply publicly_related_aenc_key_seed. admit. }
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply (refines_bind _ _ _ lrel_unit); first by iApply rel_send.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.
rel_apply_l (rel_mk_nonce_l _ _ (λ _, ∅) with "[//]").
{ iIntros "%t". by iApply big_sepS_empty. }
iIntros (nonce) "%Hnonce #mint_nonce _".
rel_apply_r (rel_mk_nonce_r _ _ (λ _, ∅) with "[//]").
{ iIntros "%t". by iApply big_sepS_empty. }
iIntros (nonce') "%Hnonce' #mint_spec_nonce' _".
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply (refines_bind _ _ _ (λ v v', ∃ t t', ⌜v = t ∧ v' = t'⌝ ∧ publicly_related t t')%I);
  first by iApply (rel_recv with "[//]"); eauto.
iIntros (? ?) "(%msg_0 & %msg_0' & [-> ->] & #Hmsg_0)"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply (refines_bind _ _ _ (λ v v', ∃ t t', ⌜v = t ∧ v' = t'⌝ ∧ publicly_related t t')%I);
  first by iApply (rel_recv with "[//]"); eauto.
iIntros (? ?) "(%msg_1 & %msg_1' & [-> ->] & #Hmsg_1)"=> /=.
rel_pures_l. rel_pures_r.
rel_apply_l rel_nondet_bool_l. iIntros ([]).
- rel_apply_r (rel_nondet_bool_r _ _ false).
  rel_pures_l. rel_pures_r.
  set K := [AppRCtx (send c);
  AppRCtx
  (λ: <>,
  let: "b'" := recv c in
  let: "b'" := eq_term (TInt 1) "b'" in (#true, "b'"))].
  set e := (send c'
  (aenc (Spec.pkey skA') (Tag (N.@"m"))
  (term_of_list (nonce' :: msg_1' :: InjLV #())));;
  let: "b'" := recv c' in let: "b'" := eq_term (TInt 1) "b'" in
  (#false, "b'"))%E.
  set Ψ := (λ p1 p2 : val,
  ⌜∃ b1 b'1 b2 b'2 : bool,
  p1 = (#b1, #b'1)%V ∧ p2 = (#b2, #b'2)%V ∧ (b = b1
  → b ≠ b2 ∧ b'1 = b'2)⌝)%I.
  set t := (term_of_list (nonce :: msg_0 :: InjLV #())%E).
  (* rel_apply_l rel_term_of_list_l. ?? *)
  rel_apply_l (rel_aenc_l ⊤ K e skA (N.@"m") _ Ψ).
  admit.
- rel_apply_r (rel_nondet_bool_r _ _ true).
  rel_pures_l. rel_pures_r.
  admit.
Admitted.

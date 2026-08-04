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
From cryptis.primitives Require Import simple_spec comp_spec with_cryptis_spec.

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

Definition aenc' : val := λ: "pk" "m",
  let: "nonce" := mk_nonce #() in
  aenc "pk" (Tag $ N.@"m") (term_of_list ["nonce"; "m"]).

Definition alice : val := λ: "c",
  let: "skA" := mk_aenc_key #() in
  let: "pkA" := pkey "skA" in
  send "c" "pkA";;
  let: "msg_0" := recv "c" in
  let: "msg_1" := recv "c" in
  let: "b" := nondet_bool #() in
  let: "msg" := if: "b" then "msg_0" else "msg_1" in
  send "c" (aenc' "pkA" "msg");;
  let: "guess" := recv "c" in
  let: "guess" := eq_term (TInt 1) "guess" in
  ("b", "guess").

Lemma rel_aenc' (sk sk' : aenc_key) (m m' : term) (Ψ : val → val → iProp) :
  cryptis_rel_ctx -∗
  minted (Spec.pkey sk) -∗ minted_spec (Spec.pkey sk') -∗
  minted m -∗ minted_spec m' -∗
  (∀ c c', publicly_related c c' -∗ Ψ c c') -∗
  REL aenc' (Spec.pkey sk) m << aenc' (Spec.pkey sk') m' : Ψ.
Proof.
iIntros "#Hctx #mintsk #mint_specsk' #mintm #mint_specm' post". rewrite /aenc'.
rel_pures_l. rel_pures_r.
rel_apply_l (rel_mk_nonce_l _ _ (λ _, ∅) with "[//]").
{ iIntros "%t". by iApply big_sepS_empty. }
iIntros (nonce) "%Hnonce #mint_nonce _".
rel_apply_r (rel_mk_nonce_r _ _ (λ _, ∅) with "[//]").
{ iIntros "%t". by iApply big_sepS_empty. }
iIntros (nonce') "%Hnonce' #mint_spec_nonce' _".
rel_pures_l. rel_pures_r.
rel_apply_l rel_nil_l.
repeat rel_apply_l rel_cons_l. rel_apply_l rel_term_of_list_l.
rel_apply_r rel_nil_r.
repeat rel_apply_r rel_cons_r. rel_apply_r rel_term_of_list_r.
rel_apply_l rel_aenc'_l. iModIntro.
rel_apply_r rel_aenc'_r.
rel_values. iApply "post".
rewrite publicly_related_aenc.
iRight.
rewrite minted_of_list minted_spec_of_list=> /=.
iFrame "#".
Admitted.

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
{ iApply publicly_related_aenc_key_pkey. iRight.
  iFrame "#".
  admit. }
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind; first by iApply rel_send.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (msg_0 msg_0') "#Hmsg_0"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (msg_1 msg_1') "#Hmsg_1"=> /=.
rel_pures_l. rel_pures_r.
rel_apply_l rel_nondet_bool_l. iIntros (choice); rel_pures_l.
rel_apply_r (rel_nondet_bool_r _ _ (negb choice)); rel_pures_r.
rel_bind_l (if: _ then _ else _)%E.
rel_bind_r (if: _ then _ else _)%E.
iApply (refines_bind _ _ _ (λ v v', ∃ m m' : term, ⌜v = m⌝ ∧ ⌜v' = m'⌝ ∧ minted m ∧ minted_spec m')%I).
{ rewrite (publicly_related_minted msg_0) (publicly_related_minted msg_1).
  iDestruct "Hmsg_0" as "[? ?]".
  iDestruct "Hmsg_1" as "[? ?]".
  case: choice; rel_pures_l; rel_pures_r; rel_values.
  iExists msg_0, msg_1'; iFrame "#"; eauto.
  iExists msg_1, msg_0'; iFrame "#"; eauto. }
iIntros (? ?) "(%msg & %msg' & -> & -> & #mint_msg & #mint_spec_msg')"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (aenc' _ _). rel_bind_r (aenc' _ _).
iApply refines_bind'. iApply rel_aenc'=> //=.
by rewrite minted_pkey. by rewrite minted_spec_pkey.
rewrite (publicly_related_minted msg_0).
iIntros (c_msg c_msg') "#Hcmsg".
rel_bind_l (send _ _). rel_bind_r (send _ _).
iApply refines_bind; first by iApply rel_send.
iIntros (? ?) "[-> ->]"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (recv _). rel_bind_r (recv _).
iApply refines_bind'. iApply rel_recv=> //.
iIntros (guess guess') "#Hguess"=> /=.
rel_pures_l. rel_pures_r.
rel_bind_l (eq_term _ _). rel_bind_r (eq_term _ _).
iApply refines_bind'. iApply rel_eq_term=> /=.
rel_pures_l. rel_pures_r.
rel_values.
iAssert (▷ ⌜TInt 1 = guess ↔ TInt 1 = guess'⌝)%I as ">%H".
{ iApply publicly_related_part_bij'=> //.
  by rewrite publicly_related_TInt. }
iPureIntro.
eexists _, _, _, _. repeat split; eauto.
destruct choice=> /=; congruence.
by apply bool_decide_ext.
Admitted.

End CPA.

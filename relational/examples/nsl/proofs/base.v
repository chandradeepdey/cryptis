(** * Ghost state of the NSL case study

- [Messages]: the plaintexts of the three messages, the session key, the
  record that an encryption under an honest key adds to the key's seal set,
  and how related lists decode.
- [KeysAndNonces]: the long-term keys of I and R, and the nonces of honest
  sessions.
- [SealSets]: the seal set of an honest key, which holds a fact about each
  honest ciphertext under the key, and how encrypting and decrypting with
  the key use it.
- [KeyGeneration]: creating an honest key.
- [Protocol]: what each honest ciphertext of NSL tells its receiver.  R's
  honest reply also holds the tokens of the session key, which the test
  claims, and what I needs to send the third message. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib_spec.
From cryptis.hyper.core Require Import minted_spec term_meta_spec rel rel_inv_updates.
From cryptis.hyper.primitives Require Import simple_spec comp_spec with_cryptis_spec attacker_spec.
From cryptis.hyper Require Import proofmode.
From cryptis.hyper.examples.nsl Require Import impl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Abbreviation m1N := (nslN.@"m1").
Abbreviation m2N := (nslN.@"m2").
Abbreviation m3N := (nslN.@"m3").
Abbreviation initN := (nslN.@"init").
Abbreviation respN := (nslN.@"resp").
Abbreviation claimN := (nslN.@"claim").
Abbreviation m3claimN := (nslN.@"m3_claim").
Abbreviation sealsIN := (nslN.@"seals_I").
Abbreviation sealsRN := (nslN.@"seals_R").

Section Base.

Context `{!relocG Σ, !public_relGS Σ}.
Abbreviation iProp := (iProp Σ).

Implicit Types (t u m n nI nR pk s : term) (sk : aenc_key).
Implicit Types (e : wf_seal_data * wf_seal_data).

Section Messages.

Definition m1_pl nI pkI : term := Spec.of_list [nI; pkI].
Definition m2_pl nI nR pkR : term := Spec.of_list [nI; nR; pkR].
Definition sess_seed pkI pkR nI nR : term := Spec.of_list [pkI; pkR; nI; nR].
Definition sess_key s : term := SEncKey (THash s).

Lemma m1N_m3N : m1N ≠ m3N.
Proof.
move=> e. have Hd : (↑m1N : coPset) ## ↑m3N by solve_ndisj.
rewrite e in Hd. have := nclose_non_empty m3N. set_solver.
Qed.

Definition aenc_seal sk sk' (N : namespace) m m' : wf_seal_data * wf_seal_data :=
  (Some (sk : term, Spec.tag (Tag N) m), Some (sk' : term, Spec.tag (Tag N) m')).

Lemma aenc_seal_inj sk sk' N m1 m1' m2 m2' :
  aenc_seal sk sk' N m1 m1' = aenc_seal sk sk' N m2 m2' →
  m1 = m2 ∧ m1' = m2'.
Proof.
rewrite /aenc_seal.
by move=> [= /Spec.tag_inj [_ ->] /Spec.tag_inj [_ ->]].
Qed.

Definition aenc_shape sk sk' e : Prop :=
  ∃ u u', e = (Some (sk : term, u), Some (sk' : term, u')).

Lemma pub_list k m m' :
  PUB⟨m, m'⟩ ⊢
  ⌜Spec.to_list m = None ∧ Spec.to_list m' = None⌝ ∨
  ∃ ts ts', ⌜Spec.to_list m = Some ts ∧ Spec.to_list m' = Some ts'⌝ ∗
    (⌜length ts ≠ k ∧ length ts' ≠ k⌝ ∨
     ⌜length ts = k⌝ ∗ [∗ list] t; t' ∈ ts; ts', PUB⟨t, t'⟩).
Proof.
iIntros "#Hm". iPoseProof (publicly_related_to_list with "Hm") as "Hl".
destruct (Spec.to_list m) as [ts|], (Spec.to_list m') as [ts'|]; try done.
- iDestruct (big_sepL2_length with "Hl") as %Hlen.
  iRight. iExists ts, ts'. iSplit; first done.
  case: (decide (length ts = k)) => Hk.
  + iRight. by iSplit.
  + iLeft. iPureIntro. lia.
- by iLeft.
Qed.

End Messages.

Section KeysAndNonces.

Definition honest_key sk sk' : iProp :=
  ⌜is_nonce (seed_of_aenc_key sk)⌝ ∗ ⌜is_nonce (seed_of_aenc_key sk')⌝ ∗
  minted sk ∗ minted_spec sk' ∗
  PUB⟨Spec.pkey sk, Spec.pkey sk'⟩ ∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') ∗
  secret_in_l (seed_of_aenc_key sk) ∗ secret_in_r (seed_of_aenc_key sk').

#[global] Instance honest_key_persistent sk sk' : Persistent (honest_key sk sk').
Proof. apply _. Qed.

(** A nonce made by an honest party for a session with an honest peer.  It
    is secret, and tagged with its partner in the other run. *)
Definition nonce_meta (N : namespace) n n' : iProp :=
  ⌜is_nonce n⌝ ∗ ⌜is_nonce n'⌝ ∗
  term_meta n N n' ∗ term_meta_spec n' N n ∗
  secret_in_l n ∗ secret_in_r n'.

#[global] Instance nonce_meta_persistent N n n' : Persistent (nonce_meta N n n').
Proof. apply _. Qed.

Definition init_nonce := nonce_meta initN.
Definition resp_nonce := nonce_meta respN.

(** A nonce received in a message: the attacker's, and then related to its
    partner, or an honest one. *)
Definition nonce_info N n n' : iProp := PUB⟨n, n'⟩ ∨ nonce_meta N n n'.

#[global] Instance nonce_info_persistent N n n' : Persistent (nonce_info N n n').
Proof. apply _. Qed.

(** Two received nonces are equal in one run exactly when they are equal in
    the other. *)
Lemma nonce_info_eq E N a a' b b' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗ nonce_info N a a' -∗ nonce_info N b b' ={E}=∗
  ⌜a = b ↔ a' = b'⌝.
Proof.
iIntros (HE) "#Hctx #Ha #Hb".
have Hsec : ∀ x x' y y', is_nonce y → is_nonce y' →
  PUB⟨x, x'⟩ -∗ secret_in_l y -∗ secret_in_r y' -∗ ⌜x ≠ y ∧ x' ≠ y'⌝.
{ move=> x x' y y' Hy Hy'. iIntros "#Hx #sy #sy'". iSplit; iIntros (?); subst.
  - iDestruct (publicly_related_nonce_term _ Hy with "Hx") as "[Hl _]".
    by iApply (secret_in_l_publicly_linked_in_l with "sy Hl").
  - iDestruct (publicly_related_term_nonce _ Hy' with "Hx") as "[_ Hr]".
    by iApply (secret_in_r_publicly_linked_in_r with "sy' Hr"). }
iDestruct "Ha" as "[#Ha|(%Ha & %Ha' & #ma & #ma' & #sa & #sa')]";
iDestruct "Hb" as "[#Hb|(%Hb & %Hb' & #mb & #mb' & #sb & #sb')]".
- by iApply (publicly_related_part_bij' with "Hctx Ha Hb").
- iDestruct (Hsec _ _ _ _ Hb Hb' with "Ha sb sb'") as %[??]. iPureIntro. tauto.
- iDestruct (Hsec _ _ _ _ Ha Ha' with "Hb sa sa'") as %[??]. iPureIntro. naive_solver.
- iAssert (⌜a = b → a' = b'⌝)%I as %H1.
  { iIntros (->). by iDestruct (term_meta_agree with "ma mb") as %->. }
  iAssert (⌜a' = b' → a = b⌝)%I as %H2.
  { iIntros (->). by iDestruct (term_meta_spec_agree with "ma' mb'") as %->. }
  iPureIntro. tauto.
Qed.

End KeysAndNonces.

Section SealSets.

(** The seal set of an honest key, the same in both runs, with [P] holding
    for each of its seals. *)
Definition seals_inv sk sk' (P : wf_seal_data * wf_seal_data → iProp) : iProp :=
  ∃ S, seals_auth_l (seed_of_aenc_key sk) S ∗
       seals_auth_r (seed_of_aenc_key sk') S ∗
       ⌜set_Forall (aenc_shape sk sk') S⌝ ∗
       [∗ set] e ∈ S, P e.

(** Decrypting a message with an honest key: both runs fail, or both
    plaintexts are related, or the message is in the key's seal set. *)
Lemma seals_inv_open E N sk sk' P t t' :
  ↑cryptisN ⊆ E → ↑N ⊆ E →
  cryptis_rel_ctx -∗
  honest_key sk sk' -∗
  inv N (seals_inv sk sk' P) -∗
  PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.open sk t = None ∧ Spec.open sk' t' = None⌝ ∨
  ∃ u u', ⌜Spec.open sk t = Some u ∧ Spec.open sk' t' = Some u'⌝ ∗
    (PUB⟨u, u'⟩ ∨ seals_l (seed_of_aenc_key sk) (Some (sk : term, u), Some (sk' : term, u'))).
Proof.
iIntros (HE HN) "#Hctx (_ & _ & _ & _ & #Hpk & #Hlink & _) #Hinv #Ht".
iMod (publicly_related_open_aenc_fupd with "Hctx Hpk Hlink Ht") as "#Ho"; first done.
case eL: (Spec.open sk t) => [u|]; case eR: (Spec.open sk' t') => [u'|]; iSimpl in "Ho".
- iModIntro. iRight. iExists u, u'. iSplit; first done.
  iDestruct "Ho" as "[?|[Hl _]]"; first by iLeft.
  iRight. by rewrite wf_seal_data_seals_aenc_l.
- iDestruct "Ho" as "[Hl _]". rewrite wf_seal_data_seals_aenc_l.
  iInv "Hinv" as "(%S & >seals & _ & >%Hshape & _)".
  iDestruct (seals_auth_l_elem_of with "seals Hl") as %Hin.
  by case: (Hshape _ Hin) => ? [? [=]].
- iDestruct "Ho" as "[_ Hr]". rewrite wf_seal_data_seals_aenc_r.
  iInv "Hinv" as "(%S & _ & >seals & >%Hshape & _)".
  iDestruct (seals_auth_r_elem_of with "seals Hr") as %Hin.
  by case: (Hshape _ Hin) => ? [? [=]].
- iModIntro. by iLeft.
Qed.

(** Encrypting under an honest key a plaintext that one of its subterms
    protects.  The result is a step, to be run with the seal set open, that
    adds the seal to the set and relates the two ciphertexts. *)
Lemma aenc_link E sk sk' (N : namespace) m m' {tsub tsub'} :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  honest_key sk sk' -∗
  minted m -∗ minted_spec m' -∗
  protected_by_subterm_l (Spec.tag (Tag N) m) tsub -∗
  protected_by_subterm_r (Spec.tag (Tag N) m') tsub' -∗
  term_token (Spec.tag (Tag N) m) ⊤ -∗
  term_token_spec (Spec.tag (Tag N) m') ⊤ -∗
  term_token (Spec.enc (Spec.pkey sk) (Tag N) m) ⊤ -∗
  term_token_spec (Spec.enc (Spec.pkey sk') (Tag N) m') ⊤ ={E}=∗
  ∀ E' S S', ⌜↑cryptisN ⊆ E'⌝ -∗
    seals_auth_l (seed_of_aenc_key sk) S -∗
    seals_auth_r (seed_of_aenc_key sk') S' ={E'}=∗
    seals_auth_l (seed_of_aenc_key sk) (S ∪ {[aenc_seal sk sk' N m m']}) ∗
    seals_auth_r (seed_of_aenc_key sk') (S' ∪ {[aenc_seal sk sk' N m m']}) ∗
    PUB⟨Spec.enc (Spec.pkey sk) (Tag N) m, Spec.enc (Spec.pkey sk') (Tag N) m'⟩.
Proof.
iIntros (HE) "#Hctx (%Hnonce & _ & #mint_sk & #mint_sk' & _ & #elem_pk & #secret & _)".
iIntros "#mint_m #mint_m' protby protby' tt_tg tts_tg tt_c tts_c".
iAssert (minted (Spec.pkey sk)) as "#mint_pk"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey sk')) as "#mint_pk'";
  first by rewrite minted_spec_pkey.
iMod (public_rel_link HE with "Hctx protby protby' tt_tg tts_tg") as "#priv_tg".
iAssert (□ (PUB⟨sk, sk'⟩ → PUB⟨m, m'⟩))%I as "#Hbox".
{ iIntros "!> #Hsk". iExFalso.
  rewrite publicly_related_adec_key'.
  iDestruct (publicly_related_nonce_term _ Hnonce with "Hsk") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret Hl") as "[]". }
iModIntro. iIntros (E' S S' HE') "seals_l seals_r".
iMod (seals_auth_l_insert _ _ (aenc_seal sk sk' N m m') with "seals_l")
  as "[seals_l #Hin_l]".
iMod (seals_auth_r_insert _ _ (aenc_seal sk sk' N m m') with "seals_r")
  as "[seals_r #Hin_r]".
iMod (public_rel_publish HE' with "Hctx [] tt_c tts_c") as "[_ #Hpub_c]".
{ iIntros "!> #elem_c". rewrite publicly_related_aenc.
  iRight. do 5 (iSplit; first done).
  iSplit; first by iApply publicly_linked_linked.
  iSplit; first done. iSplit; first done.
  by iApply (wf_seal_rel_aenc_intro with "Hin_l Hin_r"). }
iModIntro. by iFrame "#∗".
Qed.

(** Runs the step of [aenc_link], given [P] for the new seal. *)
Lemma seals_inv_link E N sk sk' P e Q :
  ↑N ⊆ E → ↑cryptisN ⊆ E ∖ ↑N → aenc_shape sk sk' e →
  inv N (seals_inv sk sk' P) -∗
  P e -∗
  (∀ E' S S', ⌜↑cryptisN ⊆ E'⌝ -∗
     seals_auth_l (seed_of_aenc_key sk) S -∗
     seals_auth_r (seed_of_aenc_key sk') S' ={E'}=∗
     seals_auth_l (seed_of_aenc_key sk) (S ∪ {[e]}) ∗
     seals_auth_r (seed_of_aenc_key sk') (S' ∪ {[e]}) ∗ Q) ={E}=∗
  Q ∗ seals_l (seed_of_aenc_key sk) e.
Proof.
iIntros (HN HE Hshape) "#Hinv HP link".
iInv "Hinv" as "(%S & >seals & >seals' & >%HS & HPs)".
iMod ("link" with "[//] seals seals'") as "(seals & seals' & HQ)".
iMod (seals_auth_l_insert _ _ e with "seals") as "[seals #Hl]".
rewrite -assoc_L union_idemp_L.
iModIntro. iFrame "HQ Hl". iSplitL; last done.
iNext. iExists (S ∪ {[e]}). iFrame "seals seals'".
iSplit. { iPureIntro. by apply set_Forall_union; last apply set_Forall_singleton. }
by iApply (big_sepS_insert_2' with "HP HPs").
Qed.

End SealSets.

Section KeyGeneration.

Lemma rel_mk_honest_key K K' Ψ :
  cryptis_rel_ctx -∗
  (∀ sk sk', honest_key sk sk' -∗
     seals_auth_l (seed_of_aenc_key sk) ∅ -∗
     seals_auth_r (seed_of_aenc_key sk') ∅ -∗
     term_token (seed_of_aenc_key sk) (⊤ ∖ ↑cryptisN.@"public_rel") -∗
     REL fill K (sk : expr) << fill K' (sk' : expr) : Ψ) -∗
  REL fill K (mk_aenc_key #()) << fill K' (mk_aenc_key #()) : Ψ.
Proof.
iIntros "#Hctx post".
have Hdisj : ∀ sk : aenc_key,
    seed_of_aenc_key sk ∉ (∅ : gset term) ∧
    seed_of_aenc_key sk ∉ ({[Spec.pkey sk]} : gset term) ∧
    (∅ : gset term) ## ({[Spec.pkey sk]} : gset term).
{ move=> sk. rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
  have Hne : ∀ kt (t : term), t ≠ TKey kt t.
  { move=> kt t H. have := f_equal tsize H.
    rewrite (tsize_eq (TKey kt t)). lia. }
  set_solver. }
rel_apply_l (rel_mk_aenc_key_l _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (sk) "%Hnonce #mint_sk token_s _ token_pk".
rel_apply_r (rel_mk_aenc_key_r _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (sk') "%Hnonce' #mint_sk' token_s' _ token_pk'".
split_term_tokens.
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "(#secret_s & seals & _ & token_s)".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "(#secret_s' & seals' & _ & _)".
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj) with "Hctx [] token_pk token_pk'")
  as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
iApply ("post" with "[] seals seals' token_s").
do 2 (iSplit; first done). by iFrame "#".
Qed.

End KeyGeneration.

Section Protocol.

Variables skI skI' skR skR' : aenc_key.

(** The right to take the session key's tokens out of the seal set of I's
    key.  The test uses it once. *)
Definition claim : iProp := term_token (seed_of_aenc_key skI) (↑claimN).

Definition key_tokens s s' : iProp :=
  term_token (THash s) ⊤ ∗ term_token_spec (THash s') ⊤.

Definition seed_l nI nR := sess_seed (Spec.pkey skI) (Spec.pkey skR) nI nR.
Definition seed_r nI' nR' := sess_seed (Spec.pkey skI') (Spec.pkey skR') nI' nR'.

Definition m1_seal nI nI' :=
  aenc_seal skR skR' m1N (m1_pl nI (Spec.pkey skI)) (m1_pl nI' (Spec.pkey skI')).

Definition m3_seal nR nR' := aenc_seal skR skR' m3N nR nR'.

Definition m2_seal nI nI' nR nR' :=
  aenc_seal skI skI' m2N (m2_pl nI nR (Spec.pkey skR)) (m2_pl nI' nR' (Spec.pkey skR')).

Lemma m2_seal_inj nI1 nI1' nR1 nR1' nI2 nI2' nR2 nR2' :
  m2_seal nI1 nI1' nR1 nR1' = m2_seal nI2 nI2' nR2 nR2' →
  nI1 = nI2 ∧ nI1' = nI2' ∧ nR1 = nR2 ∧ nR1' = nR2'.
Proof.
case/aenc_seal_inj; rewrite /m2_pl.
by move=> /Spec.of_list_inj [-> ->] /Spec.of_list_inj [-> ->].
Qed.

(** The honest ciphertexts under R's key: I's first message and the third
    message. *)
Definition seals_R_info e : iProp :=
  (∃ nI nI', ⌜e = m1_seal nI nI'⌝ ∗ init_nonce nI nI') ∨
  (∃ nR nR', ⌜e = m3_seal nR nR'⌝ ∗ resp_nonce nR nR').

Definition m2_facts nI nI' nR nR' : iProp :=
  nonce_info initN nI nI' ∗ resp_nonce nR nR' ∗
  secret_in_l (seed_l nI nR) ∗ secret_in_r (seed_r nI' nR').

#[global] Instance m2_facts_persistent nI nI' nR nR' :
  Persistent (m2_facts nI nI' nR nR').
Proof. apply _. Qed.

(** What the initiator needs to encrypt the responder's nonce. *)
Definition m3_tokens nR nR' : iProp :=
  protected_by_subterm_l (Spec.tag (Tag m3N) nR) nR ∗
  protected_by_subterm_r (Spec.tag (Tag m3N) nR') nR' ∗
  term_token (Spec.tag (Tag m3N) nR) ⊤ ∗
  term_token_spec (Spec.tag (Tag m3N) nR') ⊤ ∗
  term_token (Spec.enc (Spec.pkey skR) (Tag m3N) nR) ⊤ ∗
  term_token_spec (Spec.enc (Spec.pkey skR') (Tag m3N) nR') ⊤.

(** The honest replies of R under I's key.  Each holds the tokens of its
    session key until the test claims them with [claim], and the tokens of
    the third message until I claims them with its nonce. *)
Definition seals_I_info e : iProp :=
  ∃ nI nI' nR nR', ⌜e = m2_seal nI nI' nR nR'⌝ ∗
    m2_facts nI nI' nR nR' ∗
    (key_tokens (seed_l nI nR) (seed_r nI' nR') ∨ claim) ∗
    (m3_tokens nR nR' ∨ term_token nI (↑m3claimN)).

Definition nsl_ctx : iProp :=
  honest_key skI skI' ∗ honest_key skR skR' ∗
  inv sealsIN (seals_inv skI skI' seals_I_info) ∗
  inv sealsRN (seals_inv skR skR' seals_R_info).

#[global] Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

(** The session secrets of an honest reply of R, which is in the seal set of
    I's key. *)
Definition session s s' : iProp :=
  ∃ nI nI' nR nR',
    ⌜s = seed_l nI nR⌝ ∗ ⌜s' = seed_r nI' nR'⌝ ∗
    seals_l (seed_of_aenc_key skI) (m2_seal nI nI' nR nR').

Lemma seals_R_lookup E e :
  ↑sealsRN ⊆ E →
  nsl_ctx -∗ seals_l (seed_of_aenc_key skR) e ={E}=∗ seals_R_info e.
Proof.
iIntros (HE) "(_ & _ & _ & #Hinv) #Hl".
iInv "Hinv" as "(%S & >seals & >seals' & >%HS & >#HP)".
iDestruct (seals_auth_l_elem_of with "seals Hl") as %Hin.
iDestruct (big_sepS_elem_of with "HP") as "#He"; first done.
iModIntro. iSplitL "seals seals'"; last by iModIntro.
iNext. iExists S. by iFrame "∗#".
Qed.

Lemma seals_I_lookup E e :
  ↑sealsIN ⊆ E →
  nsl_ctx -∗ seals_l (seed_of_aenc_key skI) e ={E}=∗
  ∃ nI nI' nR nR', ⌜e = m2_seal nI nI' nR nR'⌝ ∗ m2_facts nI nI' nR nR'.
Proof.
iIntros (HE) "(_ & _ & #Hinv & _) #Hl".
iInv "Hinv" as "(%S & >seals & >seals' & >%HS & >HP)".
iDestruct (seals_auth_l_elem_of with "seals Hl") as %Hin.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first done.
iDestruct "He" as (nI nI' nR nR' ->) "(#Hf & slot & slot3)".
iModIntro. iSplitL "seals seals' HP slot slot3".
2: { iModIntro. iExists nI, nI', nR, nR'. by iFrame "Hf". }
iNext. iExists S. iFrame. iSplit; first done. iApply "HP".
iExists nI, nI', nR, nR'. iSplit; first done. by iFrame "#∗".
Qed.

Lemma claim_key E s s' :
  ↑sealsIN ⊆ E →
  nsl_ctx -∗ session s s' -∗ claim ={E}=∗
  key_tokens s s' ∗ secret_in_l s ∗ secret_in_r s'.
Proof.
iIntros (HE) "(_ & _ & #Hinv & _) (%nI & %nI' & %nR & %nR' & -> & -> & #Hl) claim".
iInv "Hinv" as "(%S & >seals & >seals' & >%HS & >HP)".
iDestruct (seals_auth_l_elem_of with "seals Hl") as %Hin.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first done.
iDestruct "He" as (nI0 nI0' nR0 nR0' e) "(#Hf & slot & slot3)".
case/m2_seal_inj: (e) => [<- [<- [<- <-]]].
iDestruct "slot" as "[toks|claim']"; last first.
{ iDestruct (term_token_disj with "claim claim'") as %dis.
  pose proof (nclose_non_empty claimN). set_solver. }
iPoseProof "Hf" as "(_ & _ & #sec & #sec')".
iModIntro. iSplitL "seals seals' HP claim slot3"; last by iFrame "toks sec sec'".
iNext. iExists S. iFrame. iSplit; first done. iApply "HP".
iExists nI, nI', nR, nR'. iSplit; first done. iFrame "Hf slot3". by iRight.
Qed.

Lemma claim_m3 E nI nI' nR nR' :
  ↑sealsIN ⊆ E →
  nsl_ctx -∗
  seals_l (seed_of_aenc_key skI) (m2_seal nI nI' nR nR') -∗
  term_token nI (↑m3claimN) ={E}=∗
  m3_tokens nR nR'.
Proof.
iIntros (HE) "(_ & _ & #Hinv & _) #Hl claim".
iInv "Hinv" as "(%S & >seals & >seals' & >%HS & >HP)".
iDestruct (seals_auth_l_elem_of with "seals Hl") as %Hin.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first done.
iDestruct "He" as (nI0 nI0' nR0 nR0' e) "(#Hf & slot & slot3)".
case/m2_seal_inj: (e) => [<- [<- [<- <-]]].
iDestruct "slot3" as "[toks|claim']"; last first.
{ iDestruct (term_token_disj with "claim claim'") as %dis.
  pose proof (nclose_non_empty m3claimN). set_solver. }
iModIntro. iSplitL "seals seals' HP claim slot"; last by iFrame "toks".
iNext. iExists S. iFrame. iSplit; first done. iApply "HP".
iExists nI, nI', nR, nR'. iSplit; first done. iFrame "Hf slot". by iRight.
Qed.

End Protocol.

End Base.

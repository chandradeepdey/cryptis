(** * Ghost state of the NSL case study

- [Messages]: the plaintexts of the three messages, the session key, and
  what an encryption under an honest key seals.
- [KeysAndNonces]: the long-term keys of I and R, and the nonces of honest
  sessions.
- [SealSets]: the invariant of an honest key.  It knows every honest
  ciphertext under the key, with a fact about each, and how encrypting and
  decrypting with the key use it.
- [KeyGeneration]: creating an honest key.
- [Protocol]: what each honest ciphertext of NSL tells its receiver.  R's
  honest reply also holds what the honest session gives both roles
  ([sess]), and what I needs to send the third message. *)

From cryptis Require Import lib cryptis primitives.
From reloc Require Import reloc.
From cryptis.hyper Require Import lib.
From cryptis.hyper.core Require Import minted_spec term_meta_spec public.
From cryptis.hyper.primitives Require Import simple comp with_cryptis attacker.
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
Implicit Types (e : term * term).

Section Messages.

Definition m1_pl nI pkI : term := Spec.of_list [nI; pkI].
Definition m2_pl nI nR pkR : term := Spec.of_list [nI; nR; pkR].
Definition sess_seed pkI pkR nI nR : term := Spec.of_list [pkI; pkR; nI; nR].
Definition sess_key s : term := SEncKey s.

Lemma m1N_m3N : m1N ≠ m3N.
Proof.
move=> e. have Hd : (↑m1N : coPset) ## ↑m3N by solve_ndisj.
rewrite e in Hd. have := nclose_non_empty m3N. set_solver.
Qed.

Definition aenc_seal (N : namespace) m m' : term * term :=
  (Spec.tag (Tag N) m, Spec.tag (Tag N) m').

Lemma aenc_seal_inj N m1 m1' m2 m2' :
  aenc_seal N m1 m1' = aenc_seal N m2 m2' → m1 = m2 ∧ m1' = m2'.
Proof. rewrite /aenc_seal. by move=> [= /Spec.tag_inj [_ ->] /Spec.tag_inj [_ ->]]. Qed.

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

Abbreviation markN := (nslN.@"sealed").

Definition seal_mark sk sk' e : iProp :=
  term_meta (TSeal (Spec.pkey sk) e.1) markN () ∗
  term_meta_spec (TSeal (Spec.pkey sk') e.2) markN ().

#[global] Instance seal_mark_persistent sk sk' e : Persistent (seal_mark sk sk' e).
Proof. apply _. Qed.

(** The honest ciphertexts under an honest key, the same in both runs, with
    [P] holding for each.  The plaintexts not in [S] are still unsealed. *)
Definition seals_inv sk sk' (P : term * term → iProp) : iProp :=
  ∃ S E E',
    never_sealed_under (seed_of_aenc_key sk) (seed_of_aenc_key sk') E E' ∗
    ⌜∀ u, ↑seal_ns (Spec.pkey sk) u ⊆ E ∨ ∃ e, e ∈ S ∧ e.1 = u⌝ ∗
    ⌜∀ u', ↑seal_ns (Spec.pkey sk') u' ⊆ E' ∨ ∃ e, e ∈ S ∧ e.2 = u'⌝ ∗
    □ ([∗ set] e ∈ S, publicly_linked (TSeal (Spec.pkey sk) e.1) (TSeal (Spec.pkey sk') e.2) ∗
                      seal_mark sk sk' e) ∗
    [∗ set] e ∈ S, P e.

Lemma seals_elem_of_l E sk sk' S E0 u x :
  ↑cryptisN ⊆ E →
  (∀ u0, ↑seal_ns (Spec.pkey sk) u0 ⊆ E0 ∨ ∃ e, e ∈ S ∧ e.1 = u0) →
  cryptis_rel_ctx -∗
  term_token (seed_of_aenc_key sk) E0 -∗
  ([∗ set] e ∈ S, publicly_linked (TSeal (Spec.pkey sk) e.1) (TSeal (Spec.pkey sk') e.2) ∗
                  seal_mark sk sk' e) -∗
  publicly_linked (TSeal (Spec.pkey sk) u) x ={E}=∗
  ⌜∃ u', (u, u') ∈ S ∧ x = TSeal (Spec.pkey sk') u'⌝ ∗
  term_token (seed_of_aenc_key sk) E0.
Proof.
move=> HE HS. iIntros "#Hctx tok #Hrec #[Hl _]".
case: (HS u) => [sub|[[e1 e2] [He Heq]]]; last (simpl in Heq; subst e1).
{ rewrite Spec.aenc_key_pkey in sub *.
  iMod (linked_in_l_map_token_fupd _ _ HE with "Hctx [Hl] [tok]") as "[]".
  - by iApply publicly_linked_in_l_linked_in_l.
  - rewrite /map_token_l /=. iApply (term_token_drop with "tok").
    etrans; last exact: sub. solve_ndisj. }
iDestruct (big_sepS_elem_of with "Hrec") as "[[Hl' _] _]"; first exact: He.
iDestruct (publicly_linked_in_l_agree with "Hl Hl'") as %->.
iFrame. iPureIntro. by exists e2.
Qed.

Lemma seals_elem_of_r E sk sk' S E0' u' x :
  ↑cryptisN ⊆ E →
  (∀ u0', ↑seal_ns (Spec.pkey sk') u0' ⊆ E0' ∨ ∃ e, e ∈ S ∧ e.2 = u0') →
  cryptis_rel_ctx -∗
  term_token_spec (seed_of_aenc_key sk') E0' -∗
  ([∗ set] e ∈ S, publicly_linked (TSeal (Spec.pkey sk) e.1) (TSeal (Spec.pkey sk') e.2) ∗
                  seal_mark sk sk' e) -∗
  publicly_linked x (TSeal (Spec.pkey sk') u') ={E}=∗
  ⌜∃ u, (u, u') ∈ S ∧ x = TSeal (Spec.pkey sk) u⌝ ∗
  term_token_spec (seed_of_aenc_key sk') E0'.
Proof.
move=> HE HS. iIntros "#Hctx tok #Hrec #[_ Hr]".
case: (HS u') => [sub|[[e1 e2] [He Heq]]]; last (simpl in Heq; subst e2).
{ rewrite Spec.aenc_key_pkey in sub *.
  iMod (linked_in_r_map_token_fupd _ _ HE with "Hctx [Hr] [tok]") as "[]".
  - by iApply publicly_linked_in_r_linked_in_r.
  - rewrite /map_token_r /=. iApply (term_token_spec_drop with "tok").
    etrans; last exact: sub. solve_ndisj. }
iDestruct (big_sepS_elem_of with "Hrec") as "[[_ Hr'] _]"; first exact: He.
iDestruct (publicly_linked_in_r_agree with "Hr Hr'") as %->.
iFrame. iPureIntro. by exists e1.
Qed.

(** Decrypting a message with an honest key: both runs fail, or both
    plaintexts are related, or the message is an honest ciphertext. *)
Lemma seals_inv_open E N sk sk' P t t' :
  ↑N ⊆ E → ↑cryptisN ⊆ E ∖ ↑N →
  cryptis_rel_ctx -∗
  honest_key sk sk' -∗
  inv N (seals_inv sk sk' P) -∗
  PUB⟨t, t'⟩ ={E}=∗
  ⌜Spec.open sk t = None ∧ Spec.open sk' t' = None⌝ ∨
  ∃ u u', ⌜Spec.open sk t = Some u ∧ Spec.open sk' t' = Some u'⌝ ∗
    (PUB⟨u, u'⟩ ∨ publicly_linked (TSeal (Spec.pkey sk) u) (TSeal (Spec.pkey sk') u')).
Proof.
iIntros (HN HE) "#Hctx (_ & _ & _ & _ & #Hpk & #Hlink & _) #Hinv #Ht".
iMod (publicly_related_open_aenc_fupd with "Hctx Hpk Hlink Ht") as "#Ho";
  first set_solver.
case eL: (Spec.open sk t) => [u|]; case eR: (Spec.open sk' t') => [u'|]; iSimpl in "Ho".
- move/Spec.open_aenc_key_Some: (eL) => ->. move/Spec.open_aenc_key_Some: (eR) => ->.
  iModIntro. iRight. iExists u, u'. by iSplit.
- move/Spec.open_aenc_key_Some: (eL) => ?; subst t.
  iDestruct "Ho" as "[Hl _]".
  iInv "Hinv" as "(%S & %E1 & %E1' & >[tok _] & >%HS & _ & >#Hrec & _)".
  iMod (seals_elem_of_l _ _ _ HE HS with "Hctx tok Hrec Hl") as "[%Hu _]".
  case: Hu => u'' [_ ?]; subst t'.
  by rewrite (proj2 (Spec.open_aenc_key_Some _ _ _) eq_refl) in eR.
- move/Spec.open_aenc_key_Some: (eR) => ?; subst t'.
  iDestruct "Ho" as "[Hr _]".
  iInv "Hinv" as "(%S & %E1 & %E1' & >[_ tok'] & _ & >%HS' & >#Hrec & _)".
  iMod (seals_elem_of_r _ _ _ HE HS' with "Hctx tok' Hrec Hr") as "[%Hu _]".
  case: Hu => u'' [_ ?]; subst t.
  by rewrite (proj2 (Spec.open_aenc_key_Some _ _ _) eq_refl) in eL.
- iModIntro. by iLeft.
Qed.

Definition seal_step sk sk' e (Q : iProp) : iProp :=
  ∀ E Ek Ek',
    ⌜↑cryptisN ⊆ E⌝ -∗
    ⌜↑seal_ns (Spec.pkey sk) e.1 ⊆ Ek⌝ -∗ ⌜↑seal_ns (Spec.pkey sk') e.2 ⊆ Ek'⌝ -∗
    never_sealed_under (seed_of_aenc_key sk) (seed_of_aenc_key sk') Ek Ek' ={E}=∗
    never_sealed_under (seed_of_aenc_key sk) (seed_of_aenc_key sk')
      (Ek ∖ ↑seal_ns (Spec.pkey sk) e.1) (Ek' ∖ ↑seal_ns (Spec.pkey sk') e.2) ∗
    publicly_linked (TSeal (Spec.pkey sk) e.1) (TSeal (Spec.pkey sk') e.2) ∗ Q.

(** Encrypting under an honest key a plaintext that one of its subterms
    protects.  The result is a step, to be run with the key's invariant
    open, that relates the two ciphertexts, and the tokens of the
    ciphertexts that mark them as sealed. *)
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
  seal_step sk sk' (aenc_seal N m m')
    (PUB⟨Spec.enc (Spec.pkey sk) (Tag N) m, Spec.enc (Spec.pkey sk') (Tag N) m'⟩) ∗
  term_token (Spec.enc (Spec.pkey sk) (Tag N) m) (↑markN) ∗
  term_token_spec (Spec.enc (Spec.pkey sk') (Tag N) m') (↑markN).
Proof.
iIntros (HE) "#Hctx (%Hnonce & _ & #mint_sk & #mint_sk' & _ & #elem_pk & #secret & _)".
iIntros "#mint_m #mint_m' protby protby' tt_tg tts_tg tt_c tts_c".
iAssert (minted (Spec.pkey sk)) as "#mint_pk"; first by rewrite minted_pkey.
iAssert (minted_spec (Spec.pkey sk')) as "#mint_pk'";
  first by rewrite minted_spec_pkey.
iDestruct (term_token_rel_token_l with "tt_tg") as "(tt_tg & _ & _)"; first solve_not_TSeal.
iDestruct (term_token_rel_token_r with "tts_tg") as "(tts_tg & _ & _)"; first solve_not_TSeal.
iMod (public_rel_link HE with "Hctx protby protby' tt_tg tts_tg") as "#priv_tg".
iAssert (□ (PUB⟨seed_of_aenc_key sk, seed_of_aenc_key sk'⟩ →
            PUB⟨Spec.tag (Tag N) m, Spec.tag (Tag N) m'⟩))%I as "#Hbox".
{ iIntros "!> #Hs". iExFalso.
  iDestruct (publicly_related_nonce_term _ Hnonce with "Hs") as "[Hl _]".
  by iDestruct (secret_in_l_publicly_linked_in_l with "secret Hl") as "[]". }
iAssert (minted (Spec.tag (Tag N) m)) as "#mint_tg"; first by rewrite minted_tag.
iAssert (minted_spec (Spec.tag (Tag N) m')) as "#mint_tg'"; first by rewrite minted_spec_tag.
iModIntro. iSplitR "tt_c tts_c"; last first.
{ iSplitL "tt_c"; [iApply (term_token_drop with "tt_c") |
                   iApply (term_token_spec_drop with "tts_c")]; solve_ndisj. }
iIntros (E0 Ek Ek' HE0 sub sub') "ns".
rewrite /Spec.enc !Spec.aenc_key_pkey in sub sub' *.
iMod (public_rel_seal HE0 sub sub' with "Hctx [] ns") as "(#Hpl & #Hpub & $)";
  last by iFrame "#".
iIntros "!> #Hpl". rewrite publicly_related_TSeal. iRight.
rewrite minted_TSeal minted_spec_TSeal.
iSplit; first by iSplit. iSplit; first by iSplit. iSplit; first done.
iLeft. iSplit; first by iApply publicly_linked_linked. iModIntro.
iSplit; first done. by iRight.
Qed.

(** Runs the step of [aenc_link], given [P] for the new seal. *)
Lemma seals_inv_link E N {sk sk' P} {Nm : namespace} {m m' Q} :
  ↑N ⊆ E → ↑cryptisN ⊆ E ∖ ↑N →
  inv N (seals_inv sk sk' P) -∗
  P (aenc_seal Nm m m') -∗
  seal_step sk sk' (aenc_seal Nm m m') Q -∗
  term_token (Spec.enc (Spec.pkey sk) (Tag Nm) m) (↑markN) -∗
  term_token_spec (Spec.enc (Spec.pkey sk') (Tag Nm) m') (↑markN) ={E}=∗
  Q ∗ publicly_linked (TSeal (Spec.pkey sk) (aenc_seal Nm m m').1)
        (TSeal (Spec.pkey sk') (aenc_seal Nm m m').2).
Proof.
iIntros (HN HE) "#Hinv HP link mk mk'".
set e := aenc_seal Nm m m'.
iInv "Hinv" as "(%S & %E0 & %E0' & >ns & >%HS & >%HS' & >#Hrec & HPs)".
iAssert ⌜↑seal_ns (Spec.pkey sk) e.1 ⊆ E0⌝%I as %sub.
{ case: (HS e.1) => [|[e0 [He0 He01]]]; first done.
  iDestruct (big_sepS_elem_of _ _ _ He0 with "Hrec") as "[_ [Hm _]]".
  rewrite He01. by iDestruct (term_meta_token with "mk Hm") as "[]". }
iAssert ⌜↑seal_ns (Spec.pkey sk') e.2 ⊆ E0'⌝%I as %sub'.
{ case: (HS' e.2) => [|[e0 [He0 He02]]]; first done.
  iDestruct (big_sepS_elem_of _ _ _ He0 with "Hrec") as "[_ [_ Hm']]".
  rewrite He02. by iDestruct (term_meta_spec_token with "mk' Hm'") as "[]". }
iMod ("link" $! (E ∖ ↑N) E0 E0' with "[//] [//] [//] ns") as "(ns & #Hsu & HQ)".
iMod (term_meta_set markN () with "mk") as "#Hm"; first done.
iMod (term_meta_spec_set markN () with "mk'") as "#Hm'"; first done.
iModIntro. iFrame "HQ Hsu". iSplitL; last done. iNext.
iExists (S ∪ {[e]}), _, _. iFrame "ns". iSplit.
{ iPureIntro. move=> u. case: (decide (u = e.1)) => [He|ne].
  - right. exists e. split; last by symmetry.
    apply elem_of_union_r. exact: elem_of_singleton_2.
  - case: (HS u) => [sub0|[e0 [? ?]]].
    + left. apply subseteq_difference_r; last done.
      apply ndot_ne_disjoint. by case.
    + right. exists e0. split; last done. exact: elem_of_union_l. }
iSplit.
{ iPureIntro. move=> u'. case: (decide (u' = e.2)) => [He|ne].
  - right. exists e. split; last by symmetry.
    apply elem_of_union_r. exact: elem_of_singleton_2.
  - case: (HS' u') => [sub0|[e0 [? ?]]].
    + left. apply subseteq_difference_r; last done.
      apply ndot_ne_disjoint. by case.
    + right. exists e0. split; last done. exact: elem_of_union_l. }
iSplit; last by iApply (big_sepS_insert_2' with "HP HPs").
iModIntro. iApply (big_sepS_insert_2' with "[] Hrec").
iFrame "Hsu". by iFrame "Hm Hm'".
Qed.

End SealSets.

Section KeyGeneration.

Lemma mk_honest_key_refinement K K' Ψ :
  cryptis_rel_ctx -∗
  (∀ sk sk', honest_key sk sk' -∗
     never_sealed_under (seed_of_aenc_key sk) (seed_of_aenc_key sk')
       (↑sealN) (↑sealN) -∗
     term_token (seed_of_aenc_key sk) (⊤ ∖ ↑hypercryptisN) -∗
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
rel_apply_l (refines_mk_aenc_key_l _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (sk) "%Hnonce #mint_sk token_s _ token_pk".
rel_apply_r (refines_mk_aenc_key_r _ _ (λ _, ∅) (λ t, {[t]}) _ Hdisj with "[//]");
  [solve_minted_iff.. |].
iIntros (sk') "%Hnonce' #mint_sk' token_s' _ token_pk'".
split_term_tokens.
iMod (public_rel_secret_seals_l (E:=⊤) Hnonce ltac:(solve_ndisj) with "Hctx token_s")
  as "(#secret_s & seals & _ & token_s)".
iMod (public_rel_secret_seals_r (E:=⊤) Hnonce' ltac:(solve_ndisj) with "Hctx token_s'")
  as "(#secret_s' & seals' & _ & _)".
iDestruct (term_token_rel_token_l with "token_pk") as "(token_pk & _ & _)";
  first solve_not_TSeal.
iDestruct (term_token_rel_token_r with "token_pk'") as "(token_pk' & _ & _)";
  first solve_not_TSeal.
iMod (public_rel_publish (E:=⊤) ltac:(solve_ndisj)
        with "Hctx [] token_pk token_pk'") as "[#elem_pk #pub_pk]".
{ iIntros "!> #elem". rewrite publicly_related_aenc_key. iRight.
  do 3 (iSplit; first done).
  iSplit; [by iApply secret_in_l_linked_in_l | by iApply secret_in_r_linked_in_r]. }
iApply ("post" with "[] [$seals $seals'] token_s").
do 2 (iSplit; first done). by iFrame "#".
Qed.

End KeyGeneration.

Section Protocol.

Variables skI skI' skR skR' : aenc_key.

(** What an honest session gives both roles.  R makes it when it builds its
    reply, out of [key_tokens]. *)
Variable sess : term → term → iProp.
Context {sess_persistent : ∀ s s', Persistent (sess s s')}.
Context {sess_timeless : ∀ s s', Timeless (sess s s')}.

(** The tests derive their key from the hash of the session key. *)
Definition key_tokens s s' : iProp :=
  never_sealed_under s s' (↑sealN) (↑sealN) ∗
  term_token (sess_key s) ⊤ ∗ term_token_spec (sess_key s') ⊤ ∗
  term_token (THash (sess_key s)) ⊤ ∗ term_token_spec (THash (sess_key s')) ⊤.

Definition seed_l nI nR := sess_seed (Spec.pkey skI) (Spec.pkey skR) nI nR.
Definition seed_r nI' nR' := sess_seed (Spec.pkey skI') (Spec.pkey skR') nI' nR'.

Definition m1_seal nI nI' :=
  aenc_seal m1N (m1_pl nI (Spec.pkey skI)) (m1_pl nI' (Spec.pkey skI')).

Definition m3_seal nR nR' := aenc_seal m3N nR nR'.

Definition m2_seal nI nI' nR nR' :=
  aenc_seal m2N (m2_pl nI nR (Spec.pkey skR)) (m2_pl nI' nR' (Spec.pkey skR')).

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
  secret_in_l (seed_l nI nR) ∗ secret_in_r (seed_r nI' nR') ∗
  sess (seed_l nI nR) (seed_r nI' nR').

#[global] Instance m2_facts_persistent nI nI' nR nR' :
  Persistent (m2_facts nI nI' nR nR').
Proof. apply _. Qed.

Lemma seed_not_pub nI nI' nR nR' :
  resp_nonce nR nR' -∗
  □ (PUB⟨seed_l nI nR, seed_r nI' nR'⟩ → False).
Proof.
iIntros "#(%HnR & _ & _ & _ & #secR & _) !> #H".
iPoseProof (publicly_related_to_list with "H") as "H'".
rewrite /seed_l /seed_r /sess_seed !Spec.of_listK /=.
iDestruct "H'" as "(_ & _ & _ & HR & _)".
iDestruct (publicly_related_nonce_term _ HnR with "HR") as "[Hl _]".
by iApply (secret_in_l_publicly_linked_in_l with "secR Hl").
Qed.

(** What the initiator needs to encrypt the responder's nonce. *)
Definition m3_tokens nR nR' : iProp :=
  protected_by_subterm_l (Spec.tag (Tag m3N) nR) nR ∗
  protected_by_subterm_r (Spec.tag (Tag m3N) nR') nR' ∗
  term_token (Spec.tag (Tag m3N) nR) ⊤ ∗
  term_token_spec (Spec.tag (Tag m3N) nR') ⊤ ∗
  term_token (Spec.enc (Spec.pkey skR) (Tag m3N) nR) ⊤ ∗
  term_token_spec (Spec.enc (Spec.pkey skR') (Tag m3N) nR') ⊤.

(** The honest replies of R under I's key.  Each holds the tokens of the
    third message until I claims them with its nonce. *)
Definition seals_I_info e : iProp :=
  ∃ nI nI' nR nR', ⌜e = m2_seal nI nI' nR nR'⌝ ∗
    m2_facts nI nI' nR nR' ∗
    (m3_tokens nR nR' ∨ term_token nI (↑m3claimN)).

Definition nsl_ctx : iProp :=
  honest_key skI skI' ∗ honest_key skR skR' ∗
  inv sealsIN (seals_inv skI skI' seals_I_info) ∗
  inv sealsRN (seals_inv skR skR' seals_R_info).

#[global] Instance nsl_ctx_persistent : Persistent nsl_ctx.
Proof. apply _. Qed.

(** The session secrets of an honest reply of R, which is an honest ciphertext
    under I's key. *)
Definition session s s' : iProp :=
  ∃ nI nI' nR nR',
    ⌜s = seed_l nI nR⌝ ∗ ⌜s' = seed_r nI' nR'⌝ ∗
    publicly_linked (TSeal (Spec.pkey skI) (m2_seal nI nI' nR nR').1)
      (TSeal (Spec.pkey skI') (m2_seal nI nI' nR nR').2).

Lemma seals_R_lookup E u u' :
  ↑sealsRN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsRN →
  cryptis_rel_ctx -∗
  nsl_ctx -∗ publicly_linked (TSeal (Spec.pkey skR) u) (TSeal (Spec.pkey skR') u') ={E}=∗
  seals_R_info (u, u').
Proof.
iIntros (HN HE) "#Hctx (_ & _ & _ & #Hinv) #Hl".
iInv "Hinv" as "(%S & %E0 & %E0' & >[tok tok'] & >%HS & >%HS' & >#Hrec & >#HP)".
iMod (seals_elem_of_l _ _ _ HE HS with "Hctx tok Hrec Hl") as "[%Hu tok]".
case: Hu => u0' [Hin [= Hu0]]; subst u0'.
iDestruct (big_sepS_elem_of with "HP") as "#He"; first exact: Hin.
iModIntro. iSplitL "tok tok'"; last by iModIntro.
iNext. iExists S, E0, E0'. by iFrame "∗#".
Qed.

Lemma seals_I_lookup E u u' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN →
  cryptis_rel_ctx -∗
  nsl_ctx -∗ publicly_linked (TSeal (Spec.pkey skI) u) (TSeal (Spec.pkey skI') u') ={E}=∗
  ∃ nI nI' nR nR', ⌜(u, u') = m2_seal nI nI' nR nR'⌝ ∗
    m2_facts nI nI' nR nR'.
Proof.
iIntros (HN HE) "#Hctx (_ & _ & #Hinv & _) #Hl".
iInv "Hinv" as "(%S & %E0 & %E0' & >[tok tok'] & >%HS & >%HS' & >#Hrec & >HP)".
iMod (seals_elem_of_l _ _ _ HE HS with "Hctx tok Hrec Hl") as "[%Hu tok]".
case: Hu => u0' [Hin [= Hu0]]; subst u0'.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first exact: Hin.
iDestruct "He" as (nI nI' nR nR' e) "(#Hf & slot3)".
iModIntro. iSplitL "tok tok' HP slot3".
2: { iModIntro. iExists nI, nI', nR, nR'. by iFrame "Hf". }
iNext. iExists S, E0, E0'. iFrame "tok tok' Hrec". do 2 (iSplit; first done).
iApply "HP". iExists nI, nI', nR, nR'. iSplit; first done. by iFrame "#∗".
Qed.

Lemma session_sess E s s' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN →
  cryptis_rel_ctx -∗
  nsl_ctx -∗ session s s' ={E}=∗
  ∃ nI nI' nR nR', ⌜s = seed_l nI nR ∧ s' = seed_r nI' nR'⌝ ∗ m2_facts nI nI' nR nR'.
Proof.
iIntros (HN HE) "#Hctx (_ & _ & #Hinv & _) (%nI & %nI' & %nR & %nR' & -> & -> & #Hl)".
iInv "Hinv" as "(%S & %E0 & %E0' & >[tok tok'] & >%HS & >%HS' & >#Hrec & >HP)".
iMod (seals_elem_of_l _ _ _ HE HS with "Hctx tok Hrec Hl") as "[%Hu tok]".
case: Hu => u0' [Hin [= Hu0]]; subst u0'.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first exact: Hin.
iDestruct "He" as (nI0 nI0' nR0 nR0' e) "(#Hf & slot3)".
case/m2_seal_inj: (e) => [<- [<- [<- <-]]].
iModIntro. iSplitL "tok tok' HP slot3"; last by iExists nI, nI', nR, nR'; iFrame "Hf".
iNext. iExists S, E0, E0'. iFrame "tok tok' Hrec". do 2 (iSplit; first done).
iApply "HP". iExists nI, nI', nR, nR'. iSplit; first done. by iFrame "Hf slot3".
Qed.

Lemma claim_m3 E nI nI' nR nR' :
  ↑sealsIN ⊆ E → ↑cryptisN ⊆ E ∖ ↑sealsIN →
  cryptis_rel_ctx -∗
  nsl_ctx -∗
  publicly_linked (TSeal (Spec.pkey skI) (m2_seal nI nI' nR nR').1)
    (TSeal (Spec.pkey skI') (m2_seal nI nI' nR nR').2) -∗
  term_token nI (↑m3claimN) ={E}=∗
  m3_tokens nR nR'.
Proof.
iIntros (HN HE) "#Hctx (_ & _ & #Hinv & _) #Hl claim".
iInv "Hinv" as "(%S & %E0 & %E0' & >[tok tok'] & >%HS & >%HS' & >#Hrec & >HP)".
iMod (seals_elem_of_l _ _ _ HE HS with "Hctx tok Hrec Hl") as "[%Hu tok]".
case: Hu => u0' [Hin [= Hu0]]; subst u0'.
iDestruct (big_sepS_elem_of_acc with "HP") as "[He HP]"; first exact: Hin.
iDestruct "He" as (nI0 nI0' nR0 nR0' e) "(#Hf & slot3)".
case/m2_seal_inj: (e) => [<- [<- [<- <-]]].
iDestruct "slot3" as "[toks|claim']"; last first.
{ iDestruct (term_token_disj with "claim claim'") as %dis.
  pose proof (nclose_non_empty m3claimN). set_solver. }
iModIntro. iSplitL "tok tok' HP claim"; last by iFrame "toks".
iNext. iExists S, E0, E0'. iFrame "tok tok' Hrec". do 2 (iSplit; first done).
iApply "HP". iExists nI, nI', nR, nR'. iSplit; first done. iFrame "Hf". by iRight.
Qed.

End Protocol.

End Base.

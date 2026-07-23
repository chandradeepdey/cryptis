From elpi.apps Require Import locker.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MintedSpec.

Context `{!relocG Σ}.

Notation iProp := (iProp Σ).

Definition minted_spec_loc (a : loc) : iProp :=
  a ↦ₛ□ #().

#[global] Instance Persistent_minted_spec_loc a :
  Persistent (minted_spec_loc a).
Proof. apply _. Qed.

#[global] Instance Timeless_minted_spec_loc a :
  Timeless (minted_spec_loc a).
Proof. apply _. Qed.

lock Definition minted_spec t : iProp :=
  [∗ set] a ∈ nonces_of_term t, minted_spec_loc (nonce_loc a).

#[global] Instance Persistent_minted_spec t : Persistent (minted_spec t).
Proof. rewrite unlock; apply _. Qed.

#[global] Instance Timeless_minted_spec t : Timeless (minted_spec t).
Proof. rewrite unlock; apply _. Qed.

Lemma subterm_minted_spec t1 t2 :
  subterm t1 t2 → minted_spec t2 -∗ minted_spec t1.
Proof.
rewrite unlock !big_sepS_forall; iIntros "%sub m_t2 %t %t_t1".
move/subterm_nonces_of_term in sub.
iApply "m_t2". iPureIntro. set_solver.
Qed.

Lemma minted_spec_TInt n : minted_spec (TInt n) ⊣⊢ True.
Proof. by rewrite unlock nonces_of_term_unseal /= big_sepS_empty. Qed.

Lemma minted_spec_TPair t1 t2 : minted_spec (TPair t1 t2) ⊣⊢ minted_spec t1 ∧ minted_spec t2.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_spec_TNonce a : minted_spec (TNonce a) ⊣⊢ minted_spec_loc (nonce_loc a).
Proof.
by rewrite unlock nonces_of_term_unseal /= big_sepS_singleton.
Qed.

Lemma minted_spec_TKey kt t : minted_spec (TKey kt t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_spec_TSeal k t : minted_spec (TSeal k t) ⊣⊢ minted_spec k ∧ minted_spec t.
Proof.
by rewrite unlock nonces_of_term_unseal /= !big_sepS_union_pers.
Qed.

Lemma minted_spec_THash t : minted_spec (THash t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_term_unseal /=. Qed.

Lemma minted_TInv t : minted_spec (TInv t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_termE. Qed.

Lemma minted_spec_TExpN t ts :
  ~ is_exp t -> is_true (atomic ts) -> invs_canceled ts ->
  minted_spec (TExpN t ts) ⊣⊢ minted_spec t ∧ [∗ list] t' ∈ ts, minted_spec t'.
Proof.
move => /negb_True nx atom ic.
rewrite unlock (nonces_of_term_TExpN (proj2 (is_trueP _) nx) atom).
rewrite (cancel_invs_canceled atom ic) big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_spec_base_exps t :
  minted_spec t ⊣⊢ minted_spec (base t) ∧ [∗ list] t' ∈ exps t, minted_spec t'.
Proof.
rewrite -{1}[t]base_expsK minted_spec_TExpN //; last exact: invs_canceled_exps.
exact: atom_exps.
Qed.

Lemma all_minted_spec_TExpN t ts :
  minted_spec t ∧ ([∗ list] t' ∈ ts, minted_spec t') ⊢ minted_spec (TExpN t ts).
Proof.
rewrite unlock !big_sepS_forall.
iIntros "[Ht Hts]" (l) "%l_in".
have /elem_of_subseteq in_nonces := nonces_of_term_TExpN_subseteq t ts.
move: l_in => /(in_nonces l). rewrite elem_of_union elem_of_union_list.
case => [?|]; first by iApply "Ht".
case => _ [] /list_elem_of_fmap [] t' [] -> ??.
rewrite big_sepL_elem_of // big_sepS_forall.
by iApply "Hts".
Qed.

Lemma minted_spec_tfactors t :
  minted_spec t ⊣⊢ [∗ list] t' ∈ tfactors t, minted_spec t'.
Proof.
rewrite unlock (nonces_of_term_tfactors t).
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_spec_TExp t1 t2 :
  ~ is_exp t1 ->
  minted_spec (TExp t1 t2) ⊣⊢ minted_spec t1 ∧ minted_spec t2.
Proof.
move => nx.
have -> : TExp t1 t2 = TExpN t1 (tfactors t2) by rewrite /TExpN tfactorsK.
rewrite (minted_spec_TExpN nx (atom_tfactors t2)
           (proj1 (is_trueP _) (invs_canceled_tfactors t2))).
by rewrite -minted_spec_tfactors.
Qed.

Lemma all_minted_spec_TExp t1 t2 :
  minted_spec t1 ∧ minted_spec t2 ⊢ minted_spec (TExp t1 t2).
Proof.
have -> : TExp t1 t2 = TExpN t1 (tfactors t2) by rewrite /TExpN tfactorsK.
rewrite (minted_spec_tfactors t2).
exact: (all_minted_spec_TExpN t1 (tfactors t2)).
Qed.

Lemma minted_spec_nonces_of_term t :
  minted_spec t ⊣⊢ [∗ set] a ∈ nonces_of_term t, minted_spec (TNonce a).
Proof.
rewrite {1}unlock !big_sepS_forall; iSplit; iIntros "#H %a %a_t".
- by rewrite minted_spec_TNonce; iApply "H".
- by rewrite -minted_spec_TNonce; iApply "H".
Qed.

Lemma minted_spec_to_list t ts :
  Spec.to_list t = Some ts →
  minted_spec t -∗ [∗ list] t' ∈ ts, minted_spec t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite minted_spec_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma minted_spec_of_list ts :
  minted_spec (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, minted_spec t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite minted_spec_TInt.
by rewrite minted_spec_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma minted_spec_Tag N : ⊢ minted_spec (Tag N).
Proof. by rewrite Tag_unseal minted_spec_TInt. Qed.

Lemma minted_spec_tag N t : minted_spec (Spec.tag (Tag N) t) ⊣⊢ minted_spec t.
Proof.
rewrite Spec.tag_unseal minted_spec_TPair; iSplit.
- by iIntros "[_ ?]".
- iIntros "?"; iSplit => //. iApply minted_spec_Tag.
Qed.

Lemma minted_spec_pkey k : minted_spec (Spec.pkey k) ⊣⊢ minted_spec k.
Proof.
by case: k => // - [] //= ?; rewrite !minted_spec_TKey.
Qed.

Lemma minted_spec_aenc k : minted_spec (AEncKey k) ⊣⊢ minted_spec k.
Proof. by rewrite [term_of_aenc_key]unlock minted_spec_TKey. Qed.

Lemma minted_spec_senc k : minted_spec (SEncKey k) ⊣⊢ minted_spec k.
Proof. by rewrite [term_of_senc_key]unlock minted_spec_TKey. Qed.

Lemma minted_spec_sign k : minted_spec (SignKey k) ⊣⊢ minted_spec k.
Proof. by rewrite [term_of_sign_key]unlock minted_spec_TKey. Qed.

Definition mintable_spec t : iProp := ¬ minted_spec t ∧ |==> minted_spec t.

Lemma mintable_spec_alloc a : a ↦ₛ #() -∗ mintable_spec (TNonce (Nonce a)).
Proof.
rewrite /mintable_spec minted_spec_TNonce. iIntros "Ha"; iSplit.
- iIntros "contra". iCombine "Ha contra" gives %[contra _].
  by move/dfrac_valid_own_l: contra; auto.
- by iMod (pointstoS_persist with "Ha").
Qed.

Lemma mintable_spec_alloc_2 a t :
□ (minted_spec a ↔ minted_spec t) -∗
  mintable_spec a -∗ mintable_spec t.
Proof.
iIntros "#[H1 H2] H".
rewrite /mintable_spec.
iSplit.
- iDestruct "H" as "[H _]".
  iIntros "contra".
  iApply "H".
  by iApply "H2".
- iDestruct "H" as "[_ H]".
  iMod "H" as "H".
  iModIntro.
  by iApply "H1".
Qed.

End MintedSpec.

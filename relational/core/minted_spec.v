From elpi.apps Require Import locker.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MintedSpec.

Context `{!relocG Σ}.

Abbreviation iProp := (iProp Σ).

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
Proof. by rewrite unlock nonces_of_termE /= big_sepS_empty. Qed.

Lemma minted_spec_TPair t1 t2 : minted_spec (TPair t1 t2) ⊣⊢ minted_spec t1 ∧ minted_spec t2.
Proof.
by rewrite unlock nonces_of_termE /= !big_sepS_union_pers.
Qed.

Lemma minted_spec_TNonce a : minted_spec (TNonce a) ⊣⊢ minted_spec_loc (nonce_loc a).
Proof.
by rewrite unlock nonces_of_termE /= big_sepS_singleton.
Qed.

Lemma minted_spec_TKey kt t : minted_spec (TKey kt t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_termE /=. Qed.

Lemma minted_spec_TSeal k t : minted_spec (TSeal k t) ⊣⊢ minted_spec k ∧ minted_spec t.
Proof.
by rewrite unlock nonces_of_termE /= !big_sepS_union_pers.
Qed.

Lemma minted_spec_THash t : minted_spec (THash t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_termE /=. Qed.

Lemma minted_spec_TInv t : minted_spec (TInv t) ⊣⊢ minted_spec t.
Proof. by rewrite unlock nonces_of_termE. Qed.

(* Unconditional: [nonces_of_term_base_exps] holds for every [t], including a
   product, where [base t = t] and [exps t] is empty. *)
Lemma minted_spec_base_exps t :
  minted_spec t ⊣⊢
  minted_spec (base t) ∧ [∗ list] t' ∈ elements (exps t), minted_spec t'.
Proof.
rewrite unlock (nonces_of_term_base_exps t) big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_spec_factors t :
  minted_spec t ⊣⊢ [∗ list] t' ∈ elements (factors t), minted_spec t'.
Proof.
rewrite unlock (nonces_of_term_factors t).
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_spec_TExp t1 t2 :
  negb (is_exp t1) -> negb (is_gmul t1) ->
  minted_spec (TExp t1 t2) ⊣⊢ minted_spec t1 ∧ minted_spec t2.
Proof.
move => nx nm.
rewrite (minted_spec_factors t2) unlock (nonces_of_term_TExp _ nx nm).
by rewrite big_sepS_union_pers big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma all_minted_spec_TExp t1 t2 :
  minted_spec t1 ∧ minted_spec t2 ⊢ minted_spec (TExp t1 t2).
Proof.
rewrite unlock !big_sepS_forall.
iIntros "[H1 H2]" (l) "%l_in".
have sub : nonces_of_term (TExp t1 t2) ⊆
           nonces_of_term t1 ∪ nonces_of_term t2.
  rewrite ![nonces_of_term]unlock unfold_TExp.
  exact: nonces_of_pre_term_exp_sub.
by move: l_in => /sub /elem_of_union [?|?]; [iApply "H1"|iApply "H2"].
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
  by case=> // [] ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite minted_spec_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma minted_spec_of_list ts :
  minted_spec (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, minted_spec t.
Proof.
rewrite [Spec.of_list]unlock.
elim: ts => [|t ts IH]; first by rewrite minted_spec_TInt.
by rewrite minted_spec_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma minted_spec_Tag N : ⊢ minted_spec (Tag N).
Proof. by rewrite [Tag]unlock minted_spec_TInt. Qed.

Lemma minted_spec_tag N t : minted_spec (Spec.tag (Tag N) t) ⊣⊢ minted_spec t.
Proof.
rewrite [Spec.tag]unlock minted_spec_TPair; iSplit.
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

Lemma mintable_spec_alloc a : (nonce_loc a) ↦ₛ #() -∗ mintable_spec a.
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

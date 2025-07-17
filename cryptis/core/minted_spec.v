From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list reservation_map excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term.
From reloc Require Import reloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Minted.

Context `{!heapGS Σ, !cfgGS Σ, !minted_specGS Σ}.

Notation iProp := (iProp Σ).

Definition minted_spec_loc (a : loc) : iProp :=
  a ↦ₛ□ #().

Global Instance Persistent_minted_spec_loc a :
  Persistent (minted_spec_loc a).
Proof. apply _. Qed.

Global Instance Timeless_minted_spec_loc a :
  Timeless (minted_spec_loc a).
Proof. apply _. Qed.

Fact minted_spec_key : unit. Proof. exact: tt. Qed.

Definition minted_spec : term → iProp :=
  locked_with minted_spec_key (
    λ t, [∗ set] a ∈ nonces_of_term t,
      minted_spec_loc a
  )%I.

Canonical minted_spec_unlock := [unlockable of minted_spec].

Global Instance Persistent_minted_spec t : Persistent (minted_spec t).
Proof. rewrite unlock; apply _. Qed.

Global Instance Timeless_minted_spec t : Timeless (minted_spec t).
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

Lemma minted_spec_TNonce a : minted_spec (TNonce a) ⊣⊢ minted_spec_loc a.
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

Lemma minted_spec_TExpN t ts :
  minted_spec (TExpN t ts) ⊣⊢ minted_spec t ∧ [∗ list] t' ∈ ts, minted_spec t'.
Proof.
rewrite unlock nonces_of_term_TExpN big_sepS_union_pers.
by rewrite big_sepS_union_list_pers big_sepL_fmap.
Qed.

Lemma minted_spec_TExp t1 t2 :
  minted_spec (TExp t1 t2) ⊣⊢ minted_spec t1 ∧ minted_spec t2.
Proof.
rewrite unlock nonces_of_term_TExpN big_sepS_union_pers.
by rewrite /= union_empty_r_L.
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

Lemma minted_spec_pre_alloc a :
  a ↦ₛ #() -∗
  ¬ minted_spec (TNonce a) ∧ |==> minted_spec (TNonce a).
Proof.
rewrite minted_spec_TNonce. iIntros "Ha"; iSplit.
- iIntros "contra". iCombine "Ha contra" gives %[contra _].
  by move/dfrac_valid_own_l: contra; auto.
- by iMod (pointstoS_persist with "Ha").
Qed.

End Minted.

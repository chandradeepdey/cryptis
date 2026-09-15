From iris.algebra Require Import auth cmra ofe gmap gset local_updates.
From iris.base_logic.lib Require Import own.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import saved_prop.
From cryptis.core Require Import term minted.
From cryptis Require Import cryptis.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.
From cryptis.core Require Export rel_state rel_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section Constructors.

Lemma publicly_related_minted t t' :
  PUB⟨t, t'⟩ ⊢ minted t ∗ minted_spec t'.
Proof.
case: t => /= *; iIntros "(#? & #? & _)"; by iFrame "#".
Qed.

(* Constructor lemmas. *)

Lemma publicly_related_TInt n1 n2 :
  PUB⟨TInt n1, TInt n2⟩ ⊣⊢ ⌜n1 = n2⌝.
Proof.
rewrite /= minted_TInt minted_spec_TInt.
by rewrite !left_id.
Qed.

Lemma publicly_related_TInt_term n (t2 : term) :
  PUB⟨TInt n, t2⟩ -∗ ⌜t2 = TInt n⌝.
Proof.
case: t2 => /= *; try by iIntros "(_ & _ & [])".
by iIntros "(_ & _ & ->)".
Qed.

Lemma publicly_related_term_TInt (t1 : term) n :
  PUB⟨t1, TInt n⟩ -∗ ⌜t1 = TInt n⌝.
Proof.
case: t1 => /= *; try by iIntros "(_ & _ & [])".
by iIntros "(_ & _ & ->)".
Qed.

Lemma publicly_related_TPair t11 t12 t21 t22 :
  PUB⟨TPair t11 t12, TPair t21 t22⟩ ⊣⊢
  PUB⟨t11, t21⟩ ∧ PUB⟨t12, t22⟩.
Proof.
rewrite /= minted_TPair minted_spec_TPair. iSplit.
- by iIntros "(_ & _ & ?)".
- iIntros "#[H1 H2]".
  iPoseProof (publicly_related_minted with "H1") as "[? ?]".
  iPoseProof (publicly_related_minted with "H2") as "[? ?]".
  iSplit; first by iSplit. iSplit; first by iSplit. by iSplit.
Qed.

Lemma publicly_related_TPair_term t11 t12 (t2 : term) :
  PUB⟨TPair t11 t12, t2⟩ -∗
  ∃ t21 t22, ⌜t2 = TPair t21 t22⌝.
Proof.
case: t2 => /= *; try by iIntros "(_ & _ & [])".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_term_TPair (t1 : term) t21 t22 :
  PUB⟨t1, TPair t21 t22⟩ -∗
  ∃ t11 t12, ⌜t1 = TPair t11 t12⌝.
Proof.
case: t1 => /= *; try by iIntros "(_ & _ & [])".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_TNonce a1 a2 :
  PUB⟨TNonce a1, TNonce a2⟩ ⊣⊢
  minted (TNonce a1) ∧ minted_spec (TNonce a2) ∧
  public_rel_elem (TNonce a1) (TNonce a2).
Proof. done. Qed.

Lemma publicly_related_TKey kt1 kt2 t1 t2 :
  PUB⟨TKey kt1 t1, TKey kt2 t2⟩ ⊣⊢
  ⌜kt1 = kt2⌝ ∧
  match kt1 with
  | AEnc => PUB⟨t1, t2⟩ ∨
            (minted t1 ∧ minted_spec t2 ∧
             public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ private_rel_elem t1 t2)
  | ADec => PUB⟨t1, t2⟩
  | Sign => PUB⟨t1, t2⟩
  | Verify => PUB⟨t1, t2⟩ ∨
              (minted t1 ∧ minted_spec t2 ∧
               public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ private_rel_elem t1 t2)
  | SEnc => PUB⟨t1, t2⟩
  end.
Proof.
rewrite /= minted_TKey minted_spec_TKey. iSplit.
- iIntros "#(? & ? & -> & H)". iSplit; first done.
  case: kt2 => /=; try (by iExact "H");
    (iDestruct "H" as "[H|(? & ?)]"; [by iLeft | iRight; by do 3 (iSplit; first done)]).
- iIntros "#(-> & H)".
  case: kt2 => /=.
  1,4: iDestruct "H" as "[H|(? & ? & ? & ?)]";
       [ iPoseProof (publicly_related_minted with "H") as "[? ?]";
         do 3 (iSplit; first done); by iLeft
       | do 3 (iSplit; first done); iRight; by iSplit ].
  all: iPoseProof (publicly_related_minted with "H") as "[? ?]"; by do 3 (iSplit; first done).
Qed.

Lemma publicly_related_TSeal k1 k2 t1 t2 :
  PUB⟨TSeal k1 t1, TSeal k2 t2⟩ ⊣⊢
  (PUB⟨k1, k2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (minted (TSeal k1 t1) ∧ minted_spec (TSeal k2 t2) ∧
   public_rel_elem (TSeal k1 t1) (TSeal k2 t2) ∧
   private_rel_elem k1 k2 ∧ private_rel_elem t1 t2 ∧
   □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | ADec | Verify => False
        | Sign => PUB⟨t1, t2⟩
        | AEnc | SEnc => PUB⟨k1, k2⟩ → PUB⟨t1, t2⟩
        end
      | _, _ => False
      end)).
Proof.
rewrite /=. iSplit.
- iIntros "#(? & ? & [?|(? & ? & ? & ?)])"; [by iLeft | iRight; by do 5 (iSplit; first done)].
- iIntros "#[[H1 H2]|(? & ? & ? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; do 3 (iSplit; first done)).
  iPoseProof (publicly_related_minted with "H1") as "[? ?]".
  iPoseProof (publicly_related_minted with "H2") as "[? ?]".
  rewrite minted_TSeal minted_spec_TSeal.
  iSplit; first by iSplit. iSplit; first by iSplit. iLeft. by iSplit.
Qed.

Lemma publicly_related_THash t1 t2 :
  PUB⟨THash t1, THash t2⟩ ⊣⊢
  PUB⟨t1, t2⟩ ∨
  (minted t1 ∧ minted_spec t2 ∧
   public_rel_elem (THash t1) (THash t2) ∧ private_rel_elem t1 t2).
Proof.
rewrite /= minted_THash minted_spec_THash. iSplit.
- iIntros "#(? & ? & [?|(? & ?)])"; [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 2 (iSplit; first done); iRight; iSplit).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 2 (iSplit; first done). by iLeft.
Qed.

(* Opening sealed terms. *)

Lemma publicly_related_open k1 k2 t1 t2 t1' t2' :
  Spec.open k1 t1 = Some t1' →
  Spec.open k2 t2 = Some t2' →
  PUB⟨k1, k2⟩ -∗
  PUB⟨t1, t2⟩ -∗
  PUB⟨t1', t2'⟩.
Proof.
rewrite /Spec.open.
case: t1 => // k_t1 t1.
case: t2 => // k_t2 t2.
rewrite publicly_related_TSeal.
case: decide => // k_t_k1 [<-].
case: decide => // k_t_k2 [<-].
iIntros "#Hk #[[_ Ht]|(_ & _ & _ & _ & _ & #Hrest)]"; first done.
case: k_t1 k_t2 => // kt1 k1' [] // kt2 k2' in k_t_k1 k_t_k2 *.
iDestruct "Hrest" as "[<- Hrest]".
case: kt1 k_t_k1 k_t_k2 => // - [<-] [<-] //.
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
Qed.

(* Tags. *)

Lemma publicly_related_Tag N1 N2 : PUB⟨Tag N1, Tag N2⟩ ⊣⊢ ⌜N1 = N2⌝.
Proof.
rewrite Tag_unseal publicly_related_TInt. iSplit.
- iIntros "%H". injection H as H. by apply encode_inj in H.
- iIntros "->". done.
Qed.

Lemma publicly_related_Tag_term N1 (N2 : term) :
  PUB⟨Tag N1, N2⟩ -∗
  ⌜N2 = Tag N1⌝.
Proof.
iIntros "#H".
rewrite Tag_unseal /Tag_def.
by iPoseProof (publicly_related_TInt_term with "H") as "->".
Qed.

Lemma publicly_related_term_Tag (N1 : term) N2 :
  PUB⟨N1, Tag N2⟩ -∗
  ⌜N1 = Tag N2⌝.
Proof.
iIntros "#H".
rewrite Tag_unseal /Tag_def.
by iPoseProof (publicly_related_term_TInt with "H") as "->".
Qed.

Lemma publicly_related_tag N1 N2 t1 t2 :
  PUB⟨Spec.tag (Tag N1) t1, Spec.tag (Tag N2) t2⟩ ⊣⊢
  ⌜N1 = N2⌝ ∧ PUB⟨t1, t2⟩.
Proof.
by rewrite Spec.tag_unseal /Spec.tag_def publicly_related_TPair publicly_related_Tag.
Qed.

Lemma publicly_related_tag_term N t1 (t2 : term) :
  PUB⟨Spec.tag (Tag N) t1, t2⟩ -∗
  ∃ t2', ⌜t2 = Spec.tag (Tag N) t2'⌝.
Proof.
iIntros "#H".
rewrite Spec.tag_unseal /Spec.tag_def.
iPoseProof (publicly_related_TPair_term with "H") as "(%t21 & %t22 & ->)".
rewrite publicly_related_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (publicly_related_Tag_term with "H1") as "->".
by iExists t22.
Qed.

Lemma publicly_related_term_tag (t1 : term) N t2 :
  PUB⟨t1, Spec.tag (Tag N) t2⟩ -∗
  ∃ t1', ⌜t1 = Spec.tag (Tag N) t1'⌝.
Proof.
iIntros "#H".
rewrite Spec.tag_unseal /Spec.tag_def.
iPoseProof (publicly_related_term_TPair with "H") as "(%t11 & %t12 & ->)".
rewrite publicly_related_TPair.
iDestruct "H" as "[H1 H2]".
iPoseProof (publicly_related_term_Tag with "H1") as "->".
by iExists t12.
Qed.

(* Asymmetric keys. *)

Lemma publicly_related_adec_key' (k1 k2 : aenc_key) :
  PUB⟨k1, k2⟩ ⊣⊢
  PUB⟨seed_of_aenc_key k1, seed_of_aenc_key k2⟩.
Proof.
rewrite [term_of_aenc_key]unlock /= minted_TKey minted_spec_TKey.
iSplit; first by iIntros "(_ & _ & _ & ?)".
iIntros "#H". iPoseProof (publicly_related_minted with "H") as "[? ?]".
by do 3 (iSplit; first done).
Qed.

Lemma publicly_related_aenc_key_term (k1 : aenc_key) (k2 : term) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k2' : aenc_key), ⌜k2 = k2'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: k2 => /= [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & <- & _)". by iExists (AEncKey s2).
Qed.

Lemma publicly_related_term_aenc_key (k1 : term) (k2 : aenc_key) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k1' : aenc_key), ⌜k1 = k1'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: k1 => /= [n1|a1 b1|a1|kt1 s1|k1 b1|s1|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & -> & _)". by iExists (AEncKey s1).
Qed.

Lemma publicly_related_aenc_key (k1 k2 : aenc_key) :
  PUB⟨Spec.pkey k1, Spec.pkey k2⟩ ⊣⊢
  PUB⟨k1, k2⟩ ∨
  (minted k1 ∧ minted_spec k2 ∧
   public_rel_elem (Spec.pkey k1) (Spec.pkey k2) ∧
   private_rel_elem (seed_of_aenc_key k1) (seed_of_aenc_key k2)).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= !minted_TKey !minted_spec_TKey.
iSplit.
- iIntros "#(? & ? & _ & [?|(? & ?)])"; [by iLeft | iRight; by do 3 (iSplit; first done)].
- iIntros "#[H|(? & ? & ? & ?)]";
    last by (do 3 (iSplit; first done); iRight; iSplit).
  iPoseProof (publicly_related_minted with "H") as "[? ?]".
  do 3 (iSplit; first done). by iLeft.
Qed.

Lemma publicly_related_aenc_key_pkey_term (sk1 : aenc_key) (k2 : term) :
  PUB⟨Spec.pkey sk1, k2⟩ -∗
  ∃ (sk2' : aenc_key), ⌜k2 = Spec.pkey sk2'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: k2 => /= [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & <- & _)". by iExists (AEncKey s2).
Qed.

Lemma publicly_related_term_aenc_key_pkey (k1 : term) (sk2 : aenc_key) :
  PUB⟨k1, Spec.pkey sk2⟩ -∗
  ∃ (sk1' : aenc_key), ⌜k1 = Spec.pkey sk1'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: k1 => /= [n1|a1 b1|a1|kt1 s1|k1 b1|s1|pt wf nf]; try by iIntros "(_ & _ & [])".
iIntros "(_ & _ & -> & _)". by iExists (AEncKey s1).
Qed.

Lemma publicly_related_aenc (sk1 sk2 : aenc_key) N (t1 t2 : term) :
  PUB⟨Spec.enc (Spec.pkey sk1) (Tag N) t1,
      Spec.enc (Spec.pkey sk2) (Tag N) t2⟩ ⊣⊢
  (PUB⟨Spec.pkey sk1, Spec.pkey sk2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (minted (Spec.pkey sk1) ∧ minted t1 ∧
   minted_spec (Spec.pkey sk2) ∧ minted_spec t2 ∧
   public_rel_elem (Spec.enc (Spec.pkey sk1) (Tag N) t1)
                   (Spec.enc (Spec.pkey sk2) (Tag N) t2) ∧
   private_rel_elem (Spec.pkey sk1) (Spec.pkey sk2) ∧
   private_rel_elem (Spec.tag (Tag N) t1) (Spec.tag (Tag N) t2) ∧
   □ (PUB⟨sk1, sk2⟩ → PUB⟨t1, t2⟩)).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.enc publicly_related_TSeal.
rewrite minted_TSeal minted_spec_TSeal minted_tag minted_spec_tag.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= publicly_related_tag.
iSplit.
- iIntros "#[[Hk [_ Ht]]|([Hmk Hmt] & [Hmk' Hmt'] & Hel & Hpk & Hpt & #Hrest)]";
    first by iLeft; iSplit.
  iRight. do 7 (iSplit; first done).
  iIntros "!> #Hs". iDestruct "Hrest" as "[_ Hrest]".
  by iDestruct ("Hrest" with "Hs") as "[_ ?]".
- iIntros "#[[Hk Ht]|(Hmk & Hmt & Hmk' & Hmt' & Hel & Hpk & Hpt & #Hrest)]";
    first by iLeft; iSplit; last iSplit.
  iRight. iSplit; first by iSplit. iSplit; first by iSplit.
  do 3 (iSplit; first done).
  iIntros "!>". iSplit; first done.
  iIntros "#Hs". iSplit; first done. by iApply "Hrest".
Qed.

End Constructors.

Section PartBij.

(* Partial bijectivity. This is where the invariant is needed: a term that is
   registered as Private (or that protects a superterm) can never be publicly
   related to anything, which rules out mixed structural/ghost cases. *)

#[local] Lemma public_rel_map_l_locked_agree t t1 t2 :
  public_rel_map_l_locked t t1 -∗
  public_rel_map_l_locked t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro.
move: H. rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid.
have -> : Public t1 ⋅ Public t2 = state_op_instance (Public t1) (Public t2) by [].
rewrite /state_op_instance. case: bool_decide_reflect => // _ [].
Qed.

#[local] Lemma public_rel_map_r_locked_agree t' t1 t2 :
  public_rel_map_r_locked t1 t' -∗
  public_rel_map_r_locked t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro.
move: H. rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid.
have -> : Public t1 ⋅ Public t2 = state_op_instance (Public t1) (Public t2) by [].
rewrite /state_op_instance. case: bool_decide_reflect => // _ [].
Qed.

#[local] Lemma public_rel_elem_agree_l t t1 t2 :
  public_rel_elem t t1 -∗
  public_rel_elem t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[H1 _] [H2 _]".
by iApply (public_rel_map_l_locked_agree with "H1 H2").
Qed.

#[local] Lemma public_rel_elem_agree_r t1 t2 t' :
  public_rel_elem t1 t' -∗
  public_rel_elem t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[_ H1] [_ H2]".
by iApply (public_rel_map_r_locked_agree with "H1 H2").
Qed.

#[local] Lemma public_rel_map_l_locked_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  public_rel_map_l_locked t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_l !! t) as [st|] eqn:Heq.
- assert (◯ (Public t') ≼ ● st ⋅ ◯ st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_frag_included in H as [st' ->].
  specialize (Hval t).
  rewrite lookup_fmap Heq /= in Hval.
  apply auth_both_valid_discrete in Hval as [_ Hval].
  change (Public t' ⋅ st') with (state_op_instance (Public t') st') in Hval.
  change (Public t' ⋅ st') with (state_op_instance (Public t') st').
  f_equal. destruct st' as [?|?|]; simpl in *;
    repeat case_bool_decide; try done; try destruct Hval.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

#[local] Lemma public_rel_map_r_locked_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  public_rel_map_r_locked t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_r !! t') as [st|] eqn:Heq.
- assert (◯ (Public t) ≼ ● st ⋅ ◯ st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_frag_included in H as [st' ->].
  specialize (Hval t').
  rewrite lookup_fmap Heq /= in Hval.
  apply auth_both_valid_discrete in Hval as [_ Hval].
  change (Public t ⋅ st') with (state_op_instance (Public t) st') in Hval.
  change (Public t ⋅ st') with (state_op_instance (Public t) st').
  f_equal. destruct st' as [?|?|]; simpl in *;
    repeat case_bool_decide; try done; try destruct Hval.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

#[local] Lemma public_rel_map_l_lookup_elem pub_l t t' :
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  public_rel_map_l_elem t t' -∗
  ⌜(∃ ts, pub_l !! t = Some (Private ts) ∧ t' ∈ ts) ∨
   pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t). rewrite lookup_fmap in Hval.
destruct (pub_l !! t) as [st|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
destruct Hincl as [z Hz].
apply leibniz_equiv in Hz. subst st.
have Hop : Private {[ t' ]} ⋅ z = state_op_instance (Private {[ t' ]}) z by [].
rewrite Hop in Heq Hval *.
destruct z as [ts|t2|]; simpl in *; repeat case_bool_decide; simpl in *;
  try solve [ destruct Hval ].
- left. exists ({[ t' ]} ∪ ts). split; first done. set_solver.
- right. by have ->: t2 = t' by set_solver.
Qed.

#[local] Lemma public_rel_map_r_lookup_elem pub_r t t' :
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  public_rel_map_r_elem t t' -∗
  ⌜(∃ ts, pub_r !! t' = Some (Private ts) ∧ t ∈ ts) ∨
   pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t'). rewrite lookup_fmap in Hval.
destruct (pub_r !! t') as [st|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
destruct Hincl as [z Hz].
apply leibniz_equiv in Hz. subst st.
have Hop : Private {[ t ]} ⋅ z = state_op_instance (Private {[ t ]}) z by [].
rewrite Hop in Heq Hval *.
destruct z as [ts|t2|]; simpl in *; repeat case_bool_decide; simpl in *;
  try solve [ destruct Hval ].
- left. exists ({[ t ]} ∪ ts). split; first done. set_solver.
- right. by have ->: t2 = t by set_solver.
Qed.

(** The pure facts recorded by the invariant about one side ([pub], [flow]
    stand for either [pub_l], [flow_l] or [pub_r], [flow_r]). *)
Record public_rel_facts pub flow : Prop := {
  public_rel_facts_flow_sub : ∀ tsub ts,
    flow !! tsub = Some ts → set_Forall (is_immediate_subterm tsub) ts;
  public_rel_facts_flow_chain : ∀ tsub ts,
    flow !! tsub = Some ts → ts ≠ ∅ →
    (∃ a, tsub = TNonce a) ∨ (∃ tsub' ts', flow !! tsub' = Some ts' ∧ tsub ∈ ts');
  public_rel_facts_Private_protected : ∀ t ts,
    pub !! t = Some (Private ts) →
    (∃ a, t = TNonce a) ∨ (∃ tsub ts1, flow !! tsub = Some ts1 ∧ t ∈ ts1);
  public_rel_facts_flow_consistent : ∀ t ts,
    flow !! t = Some ts → ts ≠ ∅ →
    (pub !! t = None) ∨ (∃ ts1, pub !! t = Some (Private ts1));
}.

#[local] Lemma public_rel_flow_l_auth_facts flow_l :
  public_rel_flow_l_auth flow_l -∗
  ⌜∀ tsub ts, flow_l !! tsub = Some ts → set_Forall (is_immediate_subterm tsub) ts⌝ ∗
  ⌜∀ tsub ts, flow_l !! tsub = Some ts → ts ≠ ∅ →
     (∃ a, tsub = TNonce a) ∨ (∃ tsub' ts', flow_l !! tsub' = Some ts' ∧ tsub ∈ ts')⌝.
Proof.
iIntros "[_ H]". rewrite !big_sepM_sep.
iDestruct "H" as "(_ & H1 & H2)".
setoid_rewrite big_sepS_pure. rewrite !big_sepM_pure.
iDestruct "H1" as %H1. iDestruct "H2" as %H2.
iPureIntro. split.
- move=> tsub ts Hts. exact: (H1 tsub ts Hts).
- move=> tsub ts Hts. exact: (H2 tsub ts Hts).
Qed.

#[local] Lemma public_rel_flow_r_auth_facts flow_r :
  public_rel_flow_r_auth flow_r -∗
  ⌜∀ tsub ts, flow_r !! tsub = Some ts → set_Forall (is_immediate_subterm tsub) ts⌝ ∗
  ⌜∀ tsub ts, flow_r !! tsub = Some ts → ts ≠ ∅ →
     (∃ a, tsub = TNonce a) ∨ (∃ tsub' ts', flow_r !! tsub' = Some ts' ∧ tsub ∈ ts')⌝.
Proof.
iIntros "[_ H]". rewrite !big_sepM_sep.
iDestruct "H" as "(_ & H1 & H2)".
setoid_rewrite big_sepS_pure. rewrite !big_sepM_pure.
iDestruct "H1" as %H1. iDestruct "H2" as %H2.
iPureIntro. split.
- move=> tsub ts Hts. exact: (H1 tsub ts Hts).
- move=> tsub ts Hts. exact: (H2 tsub ts Hts).
Qed.

#[local] Lemma public_rel_inv_facts pub_l pub_r flow_l flow_r :
  public_rel_inv pub_l pub_r flow_l flow_r -∗
  ⌜public_rel_facts pub_l flow_l⌝ ∗ ⌜public_rel_facts pub_r flow_r⌝.
Proof.
iIntros "(_ & (Hflow_l & Hflow_r & _ & _) & _ & [%HPriv_l %HPriv_r] & [%Hcons_l %Hcons_r])".
iPoseProof (public_rel_flow_l_auth_facts with "Hflow_l") as "[%Hsub_l %Hchain_l]".
iPoseProof (public_rel_flow_r_auth_facts with "Hflow_r") as "[%Hsub_r %Hchain_r]".
iPureIntro. split; by constructor.
Qed.

(** A term that is registered as [Private], or that protects some superterm,
    is never registered as [Public], and is either a nonce or protected by
    one of its immediate subterms. *)
#[local] Lemma public_rel_protected_inv pub flow t :
  public_rel_facts pub flow →
  (∃ ts, pub !! t = Some (Private ts)) ∨ (∃ ts, flow !! t = Some ts ∧ ts ≠ ∅) →
  (∀ t', pub !! t ≠ Some (Public t')) ∧
  ((∃ a, t = TNonce a) ∨
   ∃ tsub ts, flow !! tsub = Some ts ∧ t ∈ ts ∧ is_immediate_subterm tsub t).
Proof.
move=> [Hsub Hchain HPriv Hcons] [[ts Hts]|[ts [Hts Hne]]].
- split; first by move=> t' Ht'; rewrite Hts in Ht'.
  case: (HPriv _ _ Hts) => [Ha|[tsub [ts1 [Hts1 Hin]]]]; first by left.
  right. exists tsub, ts1. do 2 (split=> //). exact: (Hsub _ _ Hts1).
- split.
  + move=> t' Ht'. case: (Hcons _ _ Hts Hne) => [H|[? H]]; rewrite H in Ht'; congruence.
  + case: (Hchain _ _ Hts Hne) => [Ha|[tsub [ts1 [Hts1 Hin]]]]; first by left.
    right. exists tsub, ts1. do 2 (split=> //). exact: (Hsub _ _ Hts1).
Qed.

(** A protected term is never publicly related to anything. *)
#[local] Lemma publicly_related_protected_l pub_l flow_l t :
  public_rel_facts pub_l flow_l →
  (∃ ts, pub_l !! t = Some (Private ts)) ∨ (∃ ts, flow_l !! t = Some ts ∧ ts ≠ ∅) →
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  ∀ t', PUB⟨t, t'⟩ -∗ False.
Proof.
move=> Hfacts.
elim/term_ind': t => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf] Hprot;
  iIntros "Hauth" (t') "#Hpub".
- case: (public_rel_protected_inv Hfacts Hprot) => _ [[a Ha]|[tsub [ts [_ [_ Hsub]]]]] //.
  by inversion Hsub.
- iDestruct (publicly_related_TPair_term with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: (public_rel_protected_inv Hfacts Hprot) => _ [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  + iApply (IHa (or_intror Hprot') with "Hauth Ha").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & Hel)".
  iDestruct (public_rel_map_l_lookup_locked with "Hauth Hel") as %Hlookup.
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub _.
  by case: (HnotPub _ Hlookup).
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & <- & Hpub)".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  destruct kt;
    try (by iApply (IH (or_intror Hprot') with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[Hel _]]";
     [ by iApply (IH (or_intror Hprot') with "Hauth Hpub")
     | iDestruct (public_rel_map_l_lookup_locked with "Hauth Hel") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  iDestruct "Hpub" as "(_ & _ & [[Hk Hb]|[Hel _]])"; last first.
  { iDestruct (public_rel_map_l_lookup_locked with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  inversion Hsub; subst.
  + iApply (IHk (or_intror Hprot') with "Hauth Hk").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t' => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  iDestruct "Hpub" as "(_ & _ & [Hpub|[Hel _]])";
    first by iApply (IH (or_intror Hprot') with "Hauth Hpub").
  iDestruct (public_rel_map_l_lookup_locked with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by iDestruct "Hpub" as "(_ & _ & [])".
Qed.

#[local] Lemma publicly_related_protected_r pub_r flow_r t' :
  public_rel_facts pub_r flow_r →
  (∃ ts, pub_r !! t' = Some (Private ts)) ∨ (∃ ts, flow_r !! t' = Some ts ∧ ts ≠ ∅) →
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  ∀ t, PUB⟨t, t'⟩ -∗ False.
Proof.
move=> Hfacts.
elim/term_ind': t' => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf] Hprot;
  iIntros "Hauth" (t) "#Hpub".
- case: (public_rel_protected_inv Hfacts Hprot) => _ [[a Ha]|[tsub [ts [_ [_ Hsub]]]]] //.
  by inversion Hsub.
- iDestruct (publicly_related_term_TPair with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: (public_rel_protected_inv Hfacts Hprot) => _ [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  + iApply (IHa (or_intror Hprot') with "Hauth Ha").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & Hel)".
  iDestruct (public_rel_map_r_lookup_locked with "Hauth Hel") as %Hlookup.
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub _.
  by case: (HnotPub _ Hlookup).
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  iDestruct "Hpub" as "(_ & _ & -> & Hpub)".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  destruct kt;
    try (by iApply (IH (or_intror Hprot') with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[Hel _]]";
     [ by iApply (IH (or_intror Hprot') with "Hauth Hpub")
     | iDestruct (public_rel_map_r_lookup_locked with "Hauth Hel") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  iDestruct "Hpub" as "(_ & _ & [[Hk Hb]|[Hel _]])"; last first.
  { iDestruct (public_rel_map_r_lookup_locked with "Hauth Hel") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  inversion Hsub; subst.
  + iApply (IHk (or_intror Hprot') with "Hauth Hk").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t => /= *; try by iDestruct "Hpub" as "(_ & _ & [])".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  inversion Hsub; subst.
  iDestruct "Hpub" as "(_ & _ & [Hpub|[Hel _]])";
    first by iApply (IH (or_intror Hprot') with "Hauth Hpub").
  iDestruct (public_rel_map_r_lookup_locked with "Hauth Hel") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by case: t => /= *; iDestruct "Hpub" as "(_ & _ & [])".
Qed.

(** If [t] is publicly related to [t2] and privately related to [t2'], then
    [t2 = t2'] (given injectivity for [t] itself). *)
#[local] Lemma publicly_related_private_rel_elem_l pub_l flow_l t :
  public_rel_facts pub_l flow_l →
  (own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
   □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
   ∀ t2 t2', PUB⟨t, t2⟩ -∗ PUB⟨t, t2'⟩ -∗ ⌜t2 = t2'⌝) →
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
  ∀ t2 t2', PUB⟨t, t2⟩ -∗ private_rel_elem_l t t2' -∗ ⌜t2 = t2'⌝.
Proof.
move=> Hfacts IH. iIntros "Hauth #Hrel" (t2 t2') "#H1 #[H2|H2]".
- iDestruct (public_rel_map_l_lookup_elem with "Hauth H2") as %[(ts & Hts & _)|Hpub].
  + by iPoseProof (publicly_related_protected_l Hfacts (or_introl (ex_intro _ ts Hts))
                    with "Hauth H1") as "[]".
  + iPoseProof ("Hrel" $! t t2' with "[//]") as "H2'".
    by iApply (IH with "Hauth Hrel H1 H2'").
- iDestruct (public_rel_map_l_locked_lookup with "Hauth H2") as %Hpub.
  iPoseProof ("Hrel" $! t t2' with "[//]") as "H2'".
  by iApply (IH with "Hauth Hrel H1 H2'").
Qed.

#[local] Lemma publicly_related_private_rel_elem_r pub_r flow_r t' :
  public_rel_facts pub_r flow_r →
  (own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
   □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
   ∀ t1 t1', PUB⟨t1, t'⟩ -∗ PUB⟨t1', t'⟩ -∗ ⌜t1 = t1'⌝) →
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
  ∀ t1 t1', PUB⟨t1, t'⟩ -∗ private_rel_elem_r t1' t' -∗ ⌜t1 = t1'⌝.
Proof.
move=> Hfacts IH. iIntros "Hauth #Hrel" (t1 t1') "#H1 #[H2|H2]".
- iDestruct (public_rel_map_r_lookup_elem with "Hauth H2") as %[(ts & Hts & _)|Hpub].
  + by iPoseProof (publicly_related_protected_r Hfacts (or_introl (ex_intro _ ts Hts))
                    with "Hauth H1") as "[]".
  + iPoseProof ("Hrel" $! t1' t' with "[//]") as "H2'".
    by iApply (IH with "Hauth Hrel H1 H2'").
- iDestruct (public_rel_map_r_locked_lookup with "Hauth H2") as %Hpub.
  iPoseProof ("Hrel" $! t1' t' with "[//]") as "H2'".
  by iApply (IH with "Hauth Hrel H1 H2'").
Qed.

#[local] Lemma publicly_related_part_bij_l pub_l flow_l t1 :
  public_rel_facts pub_l flow_l →
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
  ∀ t2 t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ⌜t2 = t2'⌝.
Proof.
move=> Hfacts.
elim/term_ind': t1 => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf];
  iIntros "Hauth #Hrel" (t2 t2') "#H1 #H2".
- iDestruct (publicly_related_TInt_term with "H1") as %->.
  by iDestruct (publicly_related_TInt_term with "H2") as %->.
- iDestruct (publicly_related_TPair_term with "H1") as %(a2 & b2 & ->).
  iDestruct (publicly_related_TPair_term with "H2") as %(a2' & b2' & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct (IHa with "Hauth Hrel Ha Ha'") as %->.
  by iDestruct (IHb with "Hauth Hrel Hb Hb'") as %->.
- case: t2 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & H1)". iDestruct "H2" as "(_ & _ & H2)".
  by iApply (public_rel_elem_agree_l with "H1 H2").
- have IH' := publicly_related_private_rel_elem_l Hfacts IH.
  case: t2 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & <- & H1)". iDestruct "H2" as "(_ & _ & <- & H2)".
  destruct kt;
    try (by iDestruct (IH with "Hauth Hrel H1 H2") as %->);
    iDestruct "H1" as "[H1|[Hel1 [Hpriv1 _]]]";
    iDestruct "H2" as "[H2|[Hel2 [Hpriv2 _]]]";
    first
      [ by iDestruct (IH with "Hauth Hrel H1 H2") as %->
      | by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->
      | by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->
      | by (iDestruct (public_rel_elem_agree_l with "Hel1 Hel2") as %Heq;
            injection Heq as ->) ].
- have IHk' := publicly_related_private_rel_elem_l Hfacts IHk.
  have IHb' := publicly_related_private_rel_elem_l Hfacts IHb.
  case: t2 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [[Hk1 Hb1]|(Hel1 & [Hpk1 _] & [Hpb1 _] & _)])";
  iDestruct "H2" as "(_ & _ & [[Hk2 Hb2]|(Hel2 & [Hpk2 _] & [Hpb2 _] & _)])".
  + iDestruct (IHk with "Hauth Hrel Hk1 Hk2") as %->.
    by iDestruct (IHb with "Hauth Hrel Hb1 Hb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk1 Hpk2") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb1 Hpb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk2 Hpk1") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb2 Hpb1") as %->.
  + iDestruct (public_rel_elem_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- have IH' := publicly_related_private_rel_elem_l Hfacts IH.
  case: t2 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t2' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [H1|[Hel1 [Hpriv1 _]]])";
  iDestruct "H2" as "(_ & _ & [H2|[Hel2 [Hpriv2 _]]])".
  + by iDestruct (IH with "Hauth Hrel H1 H2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->.
  + iDestruct (public_rel_elem_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by iDestruct "H1" as "(_ & _ & [])".
Qed.

#[local] Lemma publicly_related_part_bij_r pub_r flow_r t2 :
  public_rel_facts pub_r flow_r →
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
  ∀ t1 t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ⌜t1 = t1'⌝.
Proof.
move=> Hfacts.
elim/term_ind': t2 => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH|pt wf nf];
  iIntros "Hauth #Hrel" (t1 t1') "#H1 #H2".
- iDestruct (publicly_related_term_TInt with "H1") as %->.
  by iDestruct (publicly_related_term_TInt with "H2") as %->.
- iDestruct (publicly_related_term_TPair with "H1") as %(a1 & b1 & ->).
  iDestruct (publicly_related_term_TPair with "H2") as %(a1' & b1' & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct (IHa with "Hauth Hrel Ha Ha'") as %->.
  by iDestruct (IHb with "Hauth Hrel Hb Hb'") as %->.
- case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t1' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & H1)". iDestruct "H2" as "(_ & _ & H2)".
  by iApply (public_rel_elem_agree_r with "H1 H2").
- have IH' := publicly_related_private_rel_elem_r Hfacts IH.
  case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t1' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & -> & H1)". iDestruct "H2" as "(_ & _ & -> & H2)".
  destruct kt;
    try (by iDestruct (IH with "Hauth Hrel H1 H2") as %->);
    iDestruct "H1" as "[H1|[Hel1 [_ Hpriv1]]]";
    iDestruct "H2" as "[H2|[Hel2 [_ Hpriv2]]]";
    first
      [ by iDestruct (IH with "Hauth Hrel H1 H2") as %->
      | by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->
      | by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->
      | by (iDestruct (public_rel_elem_agree_r with "Hel1 Hel2") as %Heq;
            injection Heq as ->) ].
- have IHk' := publicly_related_private_rel_elem_r Hfacts IHk.
  have IHb' := publicly_related_private_rel_elem_r Hfacts IHb.
  case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t1' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [[Hk1 Hb1]|(Hel1 & [_ Hpk1] & [_ Hpb1] & _)])";
  iDestruct "H2" as "(_ & _ & [[Hk2 Hb2]|(Hel2 & [_ Hpk2] & [_ Hpb2] & _)])".
  + iDestruct (IHk with "Hauth Hrel Hk1 Hk2") as %->.
    by iDestruct (IHb with "Hauth Hrel Hb1 Hb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk1 Hpk2") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb1 Hpb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk2 Hpk1") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb2 Hpb1") as %->.
  + iDestruct (public_rel_elem_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- have IH' := publicly_related_private_rel_elem_r Hfacts IH.
  case: t1 => /= *; try by iDestruct "H1" as "(_ & _ & [])".
  case: t1' => /= *; try by iDestruct "H2" as "(_ & _ & [])".
  iDestruct "H1" as "(_ & _ & [H1|[Hel1 [_ Hpriv1]]])";
  iDestruct "H2" as "(_ & _ & [H2|[Hel2 [_ Hpriv2]]])".
  + by iDestruct (IH with "Hauth Hrel H1 H2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->.
  + iDestruct (public_rel_elem_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by case: t1 => /= *; iDestruct "H1" as "(_ & _ & [])".
Qed.

Lemma publicly_related_part_bij_1 E t1 t2 t2' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t2⟩ -∗
  PUB⟨t1, t2'⟩ -∗
  |={E}=> ⌜t2 = t2'⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hrel_inv)".
iPoseProof (public_rel_inv_facts with "Hrel_inv") as "[%Hfacts_l %Hfacts_r]".
iDestruct "Hrel_inv" as "(([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                          Hflow & [%Hpub_eq #Hpub_rel] & HPriv & Hcons)".
iDestruct (publicly_related_part_bij_l _ Hfacts_l with "Hmap_l Hpub_rel H1 H2") as %Heq.
iModIntro. iSplitL; last by iPureIntro.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame. iFrame "#". by iPureIntro.
Qed.

Lemma publicly_related_part_bij_2 E t1 t1' t2 :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t2⟩ -∗
  PUB⟨t1', t2⟩ -∗
  |={E}=> ⌜t1 = t1'⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #H1 #H2".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r & Hrel_inv)".
iPoseProof (public_rel_inv_facts with "Hrel_inv") as "[%Hfacts_l %Hfacts_r]".
iDestruct "Hrel_inv" as "((Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                          Hflow & [%Hpub_eq #Hpub_rel] & HPriv & Hcons)".
iAssert (□ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩))%I as "#Hpub_rel_r".
{ iIntros "!>" (t t') "%H". iApply "Hpub_rel". iPureIntro. by apply Hpub_eq. }
iDestruct (publicly_related_part_bij_r _ Hfacts_r with "Hmap_r Hpub_rel_r H1 H2") as %Heq.
iModIntro. iSplitL; last by iPureIntro.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame. iFrame "#". by iPureIntro.
Qed.

Lemma publicly_related_part_bij E t1 t2 :
  ↑cryptisN ⊆ E →
  (∀ t2', cryptis_rel_ctx -∗ PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ |={E}=> ⌜t2 = t2'⌝) ∧
  (∀ t1', cryptis_rel_ctx -∗ PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ |={E}=> ⌜t1 = t1'⌝).
Proof.
move=> HE. split.
- move=> t2'. exact: publicly_related_part_bij_1.
- move=> t1'. exact: publicly_related_part_bij_2.
Qed.

Lemma publicly_related_part_bij' E t1 t1' t2 t2' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t1, t1'⟩ -∗
  PUB⟨t2, t2'⟩ -∗
  |={E}=> ⌜t1 = t2 ↔ t1' = t2'⌝.
Proof.
iIntros (HE) "#Hctx #Ht1 #Ht2".
destruct (decide (t1 = t2)) as [->|Hne].
{ iMod (publicly_related_part_bij_1 with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
destruct (decide (t1' = t2')) as [->|Hne'].
{ iMod (publicly_related_part_bij_2 with "Hctx Ht1 Ht2") as %->; first done.
  by iPureIntro. }
iPureIntro. tauto.
Qed.

End PartBij.

End Rel.

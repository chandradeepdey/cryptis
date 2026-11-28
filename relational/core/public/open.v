(** * Decryption lemmas for [PUB]

- [AttackerDecryption]: decrypting related terms with related keys
  succeeds in both runs or in neither, with related results.
- [HonestDecryption]: what an honest party gets when it decrypts a public
  term with its own key.

Lemmas ending in [_fupd] open the invariant themselves. *)

From iris.algebra Require Import gmap gset.
From reloc Require Import reloc.
From cryptis Require Import cryptis.
From cryptis.hyper.core Require Import minted_spec term_meta_spec.
From cryptis.hyper.core.public Require Import state states base rules bijection.
Import State.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PublicOpen.

Context `{!relocG Σ, !publicGS Σ}.

Abbreviation iProp := (iProp Σ).
Abbreviation iPropO := (iPropO Σ).

Implicit Types t tsub tsup troot tprot t'sub t'sup t'root t'prot : term.
Implicit Types st : state.
Implicit Types states_l states_r : gmap term state.
Implicit Types P : term -> term -> iProp.

Section AttackerDecryption.

#[local] Lemma public_open_auth {states_l k k' t t' t1 t1'} :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
case: t' => // k_t' t'.
case: decide => // k_t_k [<-].
case: decide => // k_t_k' [<-].
iIntros "Hstates Hprot #Hk #Ht".
case: k_t k_t' => // kt k1 [] // kt' k1' in k_t_k k_t_k' *.
case: kt k_t_k => // - [<-]; case: kt' k_t_k' => // - [<-].
all: try (rewrite public_TKey; by iDestruct "Hk" as "[% _]").
all: iDestruct (public_TSeal with "Ht") as "[[_ Ht1]|(_ & _ & [Hl _] & [[_ #Hrest]|[Ho _]])]";
  first done.
all: try iSimpl in "Ho"; try iSimpl in "Hrest".
- by iApply (public_TSeal_l_open with "Hstates Hprot Hl Hk").
- iDestruct "Ho" as "[Ho _]".
  by iDestruct (secret_in_l_public with "Hstates Hprot Ho Hk") as "[]".
- by iDestruct "Hrest" as "[_ ?]".
- by iDestruct "Ho" as "[]".
- by iApply (public_TSeal_l_open with "Hstates Hprot Hl Hk").
- by iDestruct (secret_in_l_public with "Hstates Hprot Ho Hk") as "[]".
Qed.

#[local] Lemma public_open_inv {states_l states_r k k' t t' t1 t1'} :
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  public_inv states_l states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (Ho Ho') "(([Hstates_l _] & _) & [Hprot _] & _) #Hk #Ht".
by iApply (public_open_auth Ho Ho' with "Hstates_l Hprot Hk Ht").
Qed.

Lemma public_open E k k' t t' t1 t1' :
  ↑cryptisN ⊆ E →
  Spec.open k t = Some t1 →
  Spec.open k' t' = Some t1' →
  hypercryptis_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ ={E}=∗
  PUB⟨t1, t1'⟩.
Proof.
iIntros (HE Ho Ho') "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_open_inv Ho Ho' with "Hbody Hk Ht") as "#Ht1".
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

#[local] Lemma public_TSeal_key_l states_l {k b k' b' k1'} :
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_states_l_deposits states_l -∗
  public_PublicLink_l_consistent states_l -∗
  PUB⟨TSeal k b, TSeal k' b'⟩ -∗
  PUB⟨k, k1'⟩ -∗
  PUB⟨k, k'⟩ ∨ opaque_l (TSeal k b).
Proof.
iIntros "Hstates Hdeps #HPublicLink_consistent #Ht #Hk".
iDestruct (public_TSeal with "Ht") as "[[? _]|(_ & _ & _ & [[[Hlink _] _]|[? _]])]".
- by iLeft.
- iLeft.
  by iApply (public_linked_in_l with "Hstates Hdeps HPublicLink_consistent Hk Hlink").
- by iRight.
Qed.

#[local] Lemma public_TSeal_key_r states_r {k b k' b' k1} :
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_states_r_deposits states_r -∗
  public_PublicLink_r_consistent states_r -∗
  PUB⟨TSeal k b, TSeal k' b'⟩ -∗
  PUB⟨k1, k'⟩ -∗
  PUB⟨k, k'⟩ ∨ opaque_r (TSeal k' b').
Proof.
iIntros "Hstates Hdeps #HPublicLink_consistent #Ht #Hk".
iDestruct (public_TSeal with "Ht") as "[[? _]|(_ & _ & _ & [[[_ Hlink] _]|[_ ?]])]".
- by iLeft.
- iLeft.
  by iApply (public_linked_in_r with "Hstates Hdeps HPublicLink_consistent Hk Hlink").
- by iRight.
Qed.

#[local] Lemma public_open_l_auth {states_l k k' t t' t1} :
  Spec.open k t = Some t1 →
  own public_states_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_l)) -∗
  public_PublicLink_l_consistent states_l -∗
  public_states_l_deposits states_l -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k' t')⌝.
Proof.
rewrite {1}/Spec.open. case: t => // k_t b.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t => // kt s Hkey.
have Hdone : ∀ kt' s' b', Spec.open_key (TKey kt' s') = Some k' →
  is_Some (Spec.open k' (TSeal (TKey kt' s') b')).
{ move=> kt' s' b' Hk'. rewrite /Spec.open decide_True //. }
case: kt Hkey => // - [<-] {k}; iIntros "Hstates_l HPublicLink_consistent Hprot #Hk #Ht";
  iDestruct (public_TKey_term with "Hk") as %[s'' ->];
  iDestruct (public_TSeal_term with "Ht") as "[(%k_t' & %b' & ->)|(_ & Hsec & _)]".
- (* Asymmetric encryption, [t'] is a ciphertext. *)
  iAssert (PUB⟨TKey AEnc s, TKey AEnc s''⟩) as "#Hpk"; first by iApply (public_pkey with "Hk").
  iAssert (PUB⟨TKey AEnc s, k_t'⟩ ∨ opaque_l (TSeal (TKey AEnc s) b))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_l with "Hstates_l Hprot HPublicLink_consistent Ht Hpk"). }
  + iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hpk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iDestruct "Ho" as "[Ho _]". iExFalso.
    by iApply (secret_in_l_public with "Hstates_l Hprot Ho Hk").
- (* Asymmetric encryption, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_l_public with "Hstates_l Hprot Hsec Hk").
- (* Signature, [t'] is a ciphertext. *)
  iDestruct (public_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[_ Hbox]|[Ho _]])]".
  + iDestruct (public_TKey_term with "Hkk") as %[s' ->].
    iAssert (PUB⟨TKey Verify s, TKey Verify s'⟩) as "#Hv";
      first by iApply (public_pkey with "Hkk").
    iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + case: k_t' => [?|? ?|?|kt' s'|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt'; try by iDestruct "Hbox" as "[]".
    iDestruct "Hbox" as "[Hv _]".
    iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". by iDestruct "Ho" as "[]".
- (* Signature, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- (* Symmetric encryption, [t'] is a ciphertext. *)
  iAssert (PUB⟨TKey SEnc s, k_t'⟩ ∨ opaque_l (TSeal (TKey SEnc s) b))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_l with "Hstates_l Hprot HPublicLink_consistent Ht Hk"). }
  + iDestruct (public_part_bij_1_auth
                 with "Hstates_l HPublicLink_consistent Hprot Hk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iExFalso.
    by iApply (secret_in_l_public with "Hstates_l Hprot Ho Hk").
- (* Symmetric encryption, [t'] is not a ciphertext: impossible. *)
  iSimpl in "Hsec". iExFalso.
  by iApply (secret_in_l_public with "Hstates_l Hprot Hsec Hk").
Qed.

#[local] Lemma public_open_r_auth {states_r k k' t t' t1'} :
  Spec.open k' t' = Some t1' →
  own public_states_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> states_r)) -∗
  public_PublicLink_r_consistent states_r -∗
  public_states_r_deposits states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t)⌝.
Proof.
rewrite {1}/Spec.open. case: t' => // k_t' b'.
case: decide => // Hkey _.
move: Hkey; rewrite /Spec.open_key /Spec.to_key.
case: k_t' => // kt' s' Hkey.
have Hdone : ∀ kt s b, Spec.open_key (TKey kt s) = Some k →
  is_Some (Spec.open k (TSeal (TKey kt s) b)).
{ move=> kt s b Hk. rewrite /Spec.open decide_True //. }
case: kt' Hkey => // - [<-] {k'}; iIntros "Hstates_r HPublicLink_consistent Hprot #Hk #Ht";
  iDestruct (public_term_TKey with "Hk") as %[s'' ->];
  iDestruct (public_term_TSeal with "Ht") as "[(%k_t & %b & ->)|(_ & _ & Hsec)]".
- iAssert (PUB⟨TKey AEnc s'', TKey AEnc s'⟩) as "#Hpk"; first by iApply (public_pkey with "Hk").
  iAssert (PUB⟨k_t, TKey AEnc s'⟩ ∨ opaque_r (TSeal (TKey AEnc s') b'))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_r with "Hstates_r Hprot HPublicLink_consistent Ht Hpk"). }
  + iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hpk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iDestruct "Ho" as "[Ho _]". iExFalso.
    by iApply (secret_in_r_public with "Hstates_r Hprot Ho Hk").
- iSimpl in "Hsec". iDestruct "Hsec" as "[Hsec _]". iExFalso.
  by iApply (secret_in_r_public with "Hstates_r Hprot Hsec Hk").
- iDestruct (public_TSeal with "Ht") as "[[Hkk _]|(_ & _ & _ & [[_ Hbox]|[_ Ho]])]".
  + iDestruct (public_term_TKey with "Hkk") as %[s ->].
    iAssert (PUB⟨TKey Verify s, TKey Verify s'⟩) as "#Hv";
      first by iApply (public_pkey with "Hkk").
    iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + case: k_t => [?|? ?|?|kt s|? ?|?|? ? ?]; try by iDestruct "Hbox" as "[]".
    case: kt; try by iDestruct "Hbox" as "[]".
    iDestruct "Hbox" as "[Hv _]".
    iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hv Hk") as %[= <-].
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". by iDestruct "Ho" as "[]".
- iSimpl in "Hsec". by iDestruct "Hsec" as "[]".
- iAssert (PUB⟨k_t, TKey SEnc s'⟩ ∨ opaque_r (TSeal (TKey SEnc s') b'))%I as "#[Hkk|Ho]".
  { by iApply (public_TSeal_key_r with "Hstates_r Hprot HPublicLink_consistent Ht Hk"). }
  + iDestruct (public_part_bij_2_auth
                 with "Hstates_r HPublicLink_consistent Hprot Hk Hkk") as %<-.
    iPureIntro. by apply: Hdone.
  + iSimpl in "Ho". iExFalso.
    by iApply (secret_in_r_public with "Hstates_r Hprot Ho Hk").
- iSimpl in "Hsec". iExFalso.
  by iApply (secret_in_r_public with "Hstates_r Hprot Hsec Hk").
Qed.

#[local] Lemma public_open_open states_l states_r k k' t t' :
  public_inv states_l states_r -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros "(([Hstates_l _] & [Hstates_r _] & _) & [Hprot_l Hprot_r] &
          [HPublicLink_consistent HPublicLink_consistent_r]) #Hk #Ht".
iSplit.
- iIntros "%Hopen". case: Hopen => t1 Hopen.
  by iApply (public_open_l_auth Hopen with "Hstates_l HPublicLink_consistent Hprot_l Hk Ht").
- iIntros "%Hopen". case: Hopen => t1' Hopen.
  by iApply (public_open_r_auth Hopen with "Hstates_r HPublicLink_consistent_r Hprot_r Hk Ht").
Qed.

Lemma public_open_fupd E k k' t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨k, k'⟩ -∗
  PUB⟨t, t'⟩ -∗
  |={E}=> ⌜is_Some (Spec.open k t) ↔ is_Some (Spec.open k' t')⌝.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hk #Ht".
iInv "Hinv" as ">(%states_l & %states_r & Hbody)".
iDestruct (public_open_open with "Hbody Hk Ht") as %Hiff.
iModIntro. iSplitL; last done.
iModIntro. iExists states_l, states_r. iFrame.
Qed.

End AttackerDecryption.

Section HonestDecryption.

Lemma public_open_aenc_fupd E (sk sk' : aenc_key) t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  PUB⟨Spec.pkey sk, Spec.pkey sk'⟩ -∗
  publicly_linked (Spec.pkey sk) (Spec.pkey sk') -∗
  PUB⟨t, t'⟩ ={E}=∗
  match Spec.open sk t, Spec.open sk' t' with
  | Some u, Some u' => PUB⟨u, u'⟩ ∨ publicly_linked t t'
  | Some u, None =>
    publicly_linked t t' ∧ secret_in_l sk ∧ secret_in_l u
  | None, Some u' =>
    publicly_linked t t' ∧ secret_in_r sk' ∧ secret_in_r u'
  | None, None => True
  end.
Proof.
move=> HE. case: sk sk' => [sA] [sA'].
rewrite [term_of_aenc_key]unlock.
rewrite -[Spec.pkey (TKey ADec sA)]/(TKey AEnc sA).
rewrite -[Spec.pkey (TKey ADec sA')]/(TKey AEnc sA').
iIntros "#Hctx #Hpk #[Hlink_l Hlink_r] #Ht".
case eL: (Spec.open (TKey ADec sA) t) => [u|];
case eR: (Spec.open (TKey ADec sA') t') => [u'|]; iSimpl.
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (public_TSeal with "Ht") as "[[_ Hu]|(_ & _ & Hl & _)]";
    iModIntro; by [iLeft|iRight].
- move/Spec.open_aenc_Some: (eL) => ?; subst t.
  iDestruct (public_TSeal_term with "Ht") as "[(%k' & %u' & ->)|(Hl & Ho & _)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk' : k' ≠ TKey AEnc sA'.
  { move=> ?; subst k'.
    have := proj2 (Spec.open_aenc_Some sA' (TSeal (TKey AEnc sA') u') u') eq_refl.
    by rewrite eR. }
  iDestruct (public_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[Hkl _] _]|[Ho _]])]".
  + iMod (public_part_bij' with "Hctx Hpk Hk") as %Hiff; first done.
    by case: Hk'; symmetry; apply Hiff.
  + iDestruct (linked_in_l_publicly_linked_in_l with "Hkl Hlink_l") as %?.
    by case: Hk'; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- move/Spec.open_aenc_Some: (eR) => ?; subst t'.
  iDestruct (public_term_TSeal with "Ht") as "[(%k & %u & ->)|(Hl & _ & Ho)]";
    last by iModIntro; iSimpl in "Ho"; iFrame "#".
  have Hk : k ≠ TKey AEnc sA.
  { move=> ?; subst k.
    have := proj2 (Spec.open_aenc_Some sA (TSeal (TKey AEnc sA) u) u) eq_refl.
    by rewrite eL. }
  iDestruct (public_TSeal with "Ht") as "[[Hk _]|(_ & _ & Hl & [[[_ Hkr] _]|[_ Ho]])]".
  + iMod (public_part_bij' with "Hctx Hk Hpk") as %Hiff; first done.
    by case: Hk; apply Hiff.
  + iDestruct (linked_in_r_publicly_linked_in_r with "Hkr Hlink_r") as %?.
    by case: Hk; congruence.
  + iModIntro. iSimpl in "Ho". iFrame "#".
- by iModIntro.
Qed.

Lemma public_open_senc_fupd E (k k' : senc_key) t t' :
  ↑cryptisN ⊆ E →
  hypercryptis_ctx -∗
  secret_in_l k -∗
  secret_in_r k' -∗
  PUB⟨t, t'⟩ ={E}=∗
  ⌜is_Some (Spec.open k t) ∨ is_Some (Spec.open k' t')⌝ → publicly_linked t t'.
Proof.
move=> HE. case: k k' => [s] [s'].
rewrite [term_of_senc_key]unlock /=.
iIntros "#Hctx #Hs #Hs' #Ht".
iDestruct (public_cases with "Ht") as "[Hsh|[Hl _]]"; last by iModIntro; iIntros.
case eL: (Spec.open (TKey SEnc s) t) => [u|].
{ move/Spec.open_senc_Some: (eL) => ?; subst t.
  case: t' => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  by iMod (secret_in_l_public_fupd with "Hctx Hs Hk") as "[]". }
case eR: (Spec.open (TKey SEnc s') t') => [u'|].
{ move/Spec.open_senc_Some: (eR) => ?; subst t'. clear eL.
  case: t => [?|? ?|?|? ?|k1 u1|?|? ? ?]; iSimpl in "Hsh"; try by iDestruct "Hsh" as "[]".
  iDestruct "Hsh" as "[Hk _]".
  by iMod (secret_in_r_public_fupd with "Hctx Hs' Hk") as "[]". }
iModIntro. iIntros ([[? ?]|[? ?]]); congruence.
Qed.

End HonestDecryption.

End PublicOpen.

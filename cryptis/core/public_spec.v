From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib.
From cryptis.lib Require Import gmeta nown saved_prop.
From cryptis.core Require Import term minted.

From cryptis.core Require Import public.
From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Existing Instance publicGpreS_nonce.
Local Existing Instance publicGpreS_seal.
Local Existing Instance publicGpreS_meta.

Class public_specGS Σ := PublicSpecGS {
  public_spec_inG : publicGpreS Σ;
  public_spec_hash_name  : gname;
  public_spec_aenc_name  : gname;
  public_spec_sign_name  : gname;
  public_spec_senc_name  : gname;
}
.

Global Existing Instance public_spec_inG.

Definition public_specΣ : gFunctors :=
  #[savedPredΣ term;
    savedPredΣ (key_type * term);
    savedPredΣ (term * term);
    metaΣ].

Global Instance subG_publicGpreS Σ : subG public_specΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section PublicSpec.

Context `{!relocG Σ, !public_specGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition pnonce_spec a : iProp :=
  ∃ γ P, meta a (nroot.@"nonce_spec") γ ∧
         own γ (saved_pred DfracDiscarded P) ∧
         ▷ □ P (TNonce a).

Global Instance Persistent_pnonce_spec a : Persistent (pnonce_spec a).
Proof. apply _. Qed.

Definition dh_spec_pred (t t' : term) : iProp :=
  match t with
  | TNonce a =>
    ∃ γ φ, meta a (nroot.@"dh_spec") γ ∧
           own γ (saved_pred DfracDiscarded φ) ∧
           ▷ □ φ t'
  | _ => False
  end.

Global Instance Persistent_dh_spec_pred t t' : Persistent (dh_spec_pred t t').
Proof. case: t => *; apply _. Qed.

Definition name_of_functionality_spec F :=
  match F with
  | AENC => public_spec_aenc_name
  | SIGN => public_spec_sign_name
  | SENC => public_spec_senc_name
  end.

Definition seal_spec_pred F N Φ : iProp :=
  nown (name_of_functionality_spec F) N
    (saved_pred DfracDiscarded (fun '(k, t) => Φ k t)).

Definition aenc_spec_pred N (Φ : aenc_key → term → iProp) :=
  seal_spec_pred AENC N (λ k t, ∃ k' : aenc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition sign_spec_pred N (Φ : sign_key → term → iProp) :=
  seal_spec_pred SIGN N (λ k t, ∃ k' : sign_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition senc_spec_pred N (Φ : senc_key → term → iProp) :=
  seal_spec_pred SENC N (λ k t, ∃ k' : senc_key, ⌜k = k'⌝ ∗ Φ k' t)%I.

Definition seal_spec_pred_token F E :=
  gmeta_token (name_of_functionality_spec F) E.

Lemma seal_spec_pred_token_difference F E1 E2 :
  E1 ⊆ E2 →
  seal_spec_pred_token F E2 ⊣⊢ seal_spec_pred_token F E1 ∗ seal_spec_pred_token F (E2 ∖ E1).
Proof.
move=> sub; rewrite /seal_spec_pred_token; exact: gmeta_token_difference.
Qed.

Lemma seal_spec_pred_token_drop E1 E2 F :
  E1 ⊆ E2 →
  seal_spec_pred_token F E2 -∗
  seal_spec_pred_token F E1.
Proof.
iIntros (sub) "t".
rewrite seal_spec_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance seal_spec_pred_persistent F N Φ : Persistent (seal_spec_pred F N Φ).
Proof. apply _. Qed.

Lemma seal_spec_pred_agree k t F N Φ1 Φ2 :
  seal_spec_pred F N Φ1 -∗
  seal_spec_pred F N Φ2 -∗
  ▷ (Φ1 k t ≡ Φ2 k t).
Proof.
rewrite /seal_spec_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! (k, t)).
Qed.

Lemma seal_spec_pred_set F E (N : namespace) Φ :
  ↑N ⊆ E →
  seal_spec_pred_token F E ==∗
  seal_spec_pred F N Φ ∗
  seal_spec_pred_token F (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Lemma aenc_spec_pred_set E N Φ :
  ↑N ⊆ E →
  seal_spec_pred_token AENC E ==∗
  aenc_spec_pred N Φ ∗
  seal_spec_pred_token AENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_spec_pred_set. Qed.

Lemma sign_spec_pred_set E N Φ :
  ↑N ⊆ E →
  seal_spec_pred_token SIGN E ==∗
  sign_spec_pred N Φ ∗
  seal_spec_pred_token SIGN (E ∖ ↑N).
Proof. move=> ?. by iApply seal_spec_pred_set. Qed.

Lemma senc_spec_pred_set E N Φ :
  ↑N ⊆ E →
  seal_spec_pred_token SENC E ==∗
  senc_spec_pred N Φ ∗
  seal_spec_pred_token SENC (E ∖ ↑N).
Proof. move=> ?. by iApply seal_spec_pred_set. Qed.

Definition wf_seal_spec F k t : iProp :=
  ∃ N t' Φ, ⌜t = Spec.tag (Tag N) t'⌝ ∧ seal_spec_pred F N Φ ∧ □ ▷ Φ k t'.

Global Instance wf_seal_spec_persistent F k t : Persistent (wf_seal_spec F k t).
Proof. by apply _. Qed.

Lemma wf_seal_spec_elim F k N t Φ :
  wf_seal_spec F k (Spec.tag (Tag N) t) -∗
  seal_spec_pred F N Φ -∗
  □ ▷ Φ k t.
Proof.
iDestruct 1 as (N' t' Φ') "(%t_t' & #HΦ' & #inv)"; iIntros "#HΦ".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (seal_spec_pred_agree k t with "HΦ HΦ'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Definition hash_spec_pred N (P : term → iProp) : iProp :=
  nown public_spec_hash_name N (saved_pred DfracDiscarded P).

Definition hash_spec_pred_token E :=
  gmeta_token public_spec_hash_name E.

Lemma hash_spec_pred_token_difference E1 E2 :
  E1 ⊆ E2 →
  hash_spec_pred_token E2 ⊣⊢ hash_spec_pred_token E1 ∗ hash_spec_pred_token (E2 ∖ E1).
Proof.
move=> sub; rewrite /hash_spec_pred_token; exact: gmeta_token_difference.
Qed.

Lemma hash_spec_pred_token_drop E1 E2 :
  E1 ⊆ E2 →
  hash_spec_pred_token E2 -∗
  hash_spec_pred_token E1.
Proof.
iIntros (sub) "t".
rewrite hash_spec_pred_token_difference //.
by iDestruct "t" as "[t _]".
Qed.

Global Instance hash_spec_pred_persistent N P : Persistent (hash_spec_pred N P).
Proof. apply _. Qed.

Lemma hash_spec_pred_agree t N P₁ P₂ :
  hash_spec_pred N P₁ -∗
  hash_spec_pred N P₂ -∗
  ▷ (P₁ t ≡ P₂ t).
Proof.
rewrite /hash_spec_pred. iIntros "#own1 #own2".
iPoseProof (nown_valid_2 with "own1 own2") as "#valid".
iPoseProof (saved_pred_op_validI with "valid") as "[_ #agree]".
by iApply ("agree" $! t).
Qed.

Lemma hash_spec_pred_set E N P :
  ↑N ⊆ E →
  hash_spec_pred_token E ==∗
  hash_spec_pred N P ∗
  hash_spec_pred_token (E ∖ ↑N).
Proof. iIntros (?) "token". by iApply nown_alloc. Qed.

Definition wf_hash_spec t : iProp :=
  ∃ N t' P, ⌜t = Spec.tag (Tag N) t'⌝ ∧ hash_spec_pred N P ∧ □ ▷ P t'.

Global Instance wf_hash_spec_persistent t : Persistent (wf_hash_spec t).
Proof. by apply _. Qed.

Lemma wf_hash_spec_elim N t P :
  wf_hash_spec (Spec.tag (Tag N) t) -∗
  hash_spec_pred N P -∗
  □ ▷ P t.
Proof.
iDestruct 1 as (N' t' P') "(%t_t' & #HP' & #inv)"; iIntros "#HP".
case/Spec.tag_inj: t_t' => /Tag_inj <- <-.
iPoseProof (hash_spec_pred_agree t with "HP HP'") as "e".
by iIntros "!> !>"; iRewrite "e".
Qed.

Fixpoint public_spec_aux n t : iProp :=
  if n is S n then
    minted_spec t ∧ (
     (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_spec_aux n t')
     ∨ match t with
       | TNonce a => pnonce_spec a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash_spec t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal_spec F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public_spec_aux n k' → public_spec_aux n t)
               | None => True
               end
           | None => True
           end
       | TExpN' _ _ _ => [∗ list] t' ∈ exps t, dh_spec_pred t' t
       | _ => False
       end%I
    )
  else False.

Global Instance Persistent_public_spec_aux n t : Persistent (public_spec_aux n t).
Proof.
elim: n t => [|n IH] /=; first by apply _.
case; try by move=> *; apply _.
Qed.

(** [public_spec t] holds when the term [t] can be declared public_spec. *)

Definition public_spec : term → iProp :=
  locked_with public_key (λ t, public_spec_aux (tsize t) t).
Canonical public_spec_unlock := [unlockable of public_spec].

Global Instance Persistent_public_spec t : Persistent (public_spec t).
Proof. rewrite unlock; apply _. Qed.

Lemma public_spec_aux_eq n t : tsize t ≤ n → public_spec_aux n t ⊣⊢ public_spec t.
Proof.
rewrite unlock.
elim: n / (lt_wf n) t => - [|n] _ IH t t_n /=;
move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => H;
first lia.
case e_st: (tsize t) => [|m] /=; first lia.
apply: bi.and_proper => // {H}.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite (IH n) ?(IH m) //; lia.
- case: t t_n e_st => //= k t t_n e_st.
  case: func_of_term => // F.
  apply: bi.and_proper => //.
  apply: bi.and_proper => //.
  case e_k: Spec.open_key => [k'|] //.
  have ? := open_key_tsize e_k.
  have ?: tsize (TSeal k t) = S (tsize k + tsize t).
    by rewrite tsize_eq -ssrnat.plusE.
  rewrite !(IH n) ?(IH m) //; lia.
Qed.

(* TODO: Merge with public_spec_aux_eq *)
Lemma public_spec_eq t :
  public_spec t ⊣⊢
  minted_spec t ∧ (
      (∃ T, ⌜decompose T t⌝ ∧ [∗ set] t' ∈ T, public_spec t')
     ∨ match t with
       | TNonce a => pnonce_spec a
       | TKey kt t => ⌜Spec.public_key_type kt⌝
       | THash t => wf_hash_spec t
       | TSeal k t =>
           match func_of_term k with
           | Some F =>
               ⌜Spec.is_seal_key k⌝ ∧
               wf_seal_spec F (Spec.skey k) t ∧
               match Spec.open_key k with
               | Some k' => □ (public_spec k' → public_spec t)
               | None => True
               end
           | None => True
           end
       | TExpN' _ _ _ => [∗ list] t' ∈ exps t, dh_spec_pred t' t
       | _ => False
       end%I
  ).
Proof.
rewrite {1}[public_spec]unlock.
case e_st: (tsize t) => [|m] /=.
  move: (ssrbool.elimT ssrnat.ltP (tsize_gt0 t)) => H; lia.
apply: bi.and_proper => //.
apply: bi.or_proper.
- apply: bi.exist_proper => T.
  apply: and_proper_L => T_t.
  apply: big_sepS_proper => t' T_t'.
  move: (decompose_tsize T_t T_t') => ?.
  rewrite public_spec_aux_eq //; lia.
- case: t e_st => //= k t e_st.
  rewrite tsize_eq -ssrnat.plusE in e_st.
  case: func_of_term => // F.
  apply: bi.and_proper => //.
  apply: bi.and_proper => //.
  case e_k: Spec.open_key => [k'|] //=.
  have ? := open_key_tsize e_k.
  rewrite !public_spec_aux_eq //; lia.
Qed.

Lemma public_spec_minted_spec t : public_spec t ⊢ minted_spec t.
Proof. rewrite public_spec_eq; by iIntros "[??]". Qed.

Lemma public_spec_TInt n : public_spec (TInt n) ⊣⊢ True.
Proof.
apply: (anti_symm _); iIntros "_" => //.
rewrite public_spec_eq minted_spec_TInt; iSplit => //.
iLeft; iExists ∅; rewrite big_sepS_empty; iSplit => //.
by iPureIntro; econstructor.
Qed.

Lemma public_spec_TPair t1 t2 : public_spec (TPair t1 t2) ⊣⊢ public_spec t1 ∧ public_spec t2.
Proof.
apply: (anti_symm _); iIntros "#Ht" => //.
- rewrite public_spec_eq minted_spec_TPair.
  iDestruct "Ht" as "([Ht1 Ht2] & publ)".
  iDestruct "publ" as "[publ | publ]" => //=.
  iDestruct "publ" as (T) "[%dec publ]".
  case: dec => //= {}t1 {}t2 -> [-> ->].
  by rewrite big_sepS_union_pers !big_sepS_singleton.
- iDestruct "Ht" as "[Ht1 Ht2]".
  rewrite [public_spec (TPair t1 t2)]public_spec_eq minted_spec_TPair -!public_spec_minted_spec.
  iSplit; eauto.
  iLeft; iExists _; iSplit.
    iPureIntro; by econstructor.
  by rewrite big_sepS_union_pers !big_sepS_singleton; eauto.
Qed.

Lemma public_spec_TNonce a :
  public_spec (TNonce a) ⊣⊢ pnonce_spec a ∗ meta a (nroot.@"minted_spec") ().
Proof.
apply: (anti_symm _); iIntros "Ht".
- rewrite public_spec_eq; iDestruct "Ht" as "[? Ht]".
  rewrite minted_spec_TNonce. iFrame.
  iDestruct "Ht" as "[publ | ?]" => //.
  iDestruct "publ" as (T) "[%dec _]".
  by case: dec.
- rewrite public_spec_eq minted_spec_TNonce /pnonce_spec.
  iDestruct "Ht" as "[Ht ?]". iFrame.
Qed.

Lemma public_spec_TKey kt t :
  public_spec (TKey kt t) ⊣⊢ public_spec t ∨ minted_spec t ∧ ⌜Spec.public_key_type kt⌝.
Proof.
apply: (anti_symm _).
- rewrite public_spec_eq minted_spec_TKey; iDestruct 1 as "[Ht publ]".
  iDestruct "publ" as "[publ | publ]" => //.
  + iDestruct "publ" as (T) "[%dec publ]".
    case: dec => //= {}kt {}t -> [-> ->].
    by rewrite big_sepS_singleton; eauto.
  + by eauto.
- iDestruct 1 as "# [publ | [s_t publ]]".
    rewrite [public_spec (TKey _ _)]public_spec_eq minted_spec_TKey -public_spec_minted_spec.
    iSplit => //; iLeft.
    iExists {[t]}; iSplit; first by iPureIntro; econstructor.
    by rewrite big_sepS_singleton.
  rewrite public_spec_eq; iSplit; eauto.
  by rewrite minted_spec_TKey.
Qed.

Lemma public_spec_TSeal k t :
  public_spec (TSeal k t) ⊣⊢
  public_spec k ∧ public_spec t ∨
  minted_spec (TSeal k t) ∧
  match func_of_term k with
  | Some F =>
      ⌜Spec.is_seal_key k⌝ ∧
      wf_seal_spec F (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public_spec k' → public_spec t)
      | None => True
      end
  | None => True
  end.
Proof.
apply: (anti_symm _).
- rewrite public_spec_eq minted_spec_TSeal.
  iDestruct 1 as "[[Hk Ht] publ]".
  iDestruct "publ" as "[publ | publ]".
  + iDestruct "publ" as (T) "[%dec ?]".
    case: dec => // {}k {}t -> [-> ->].
    by rewrite big_sepS_union_pers !big_sepS_singleton; iLeft.
  + iRight. iSplit; first by eauto.
    by case: k => // kt k.
- iDestruct 1 as "[#[Hk Ht] | (#Ht & inv)]".
  { rewrite [public_spec (TSeal _ _)]public_spec_eq minted_spec_TSeal.
    rewrite -!public_spec_minted_spec.
    iSplit; eauto; iLeft.
    iExists {[k; t]}; rewrite big_sepS_union_pers !big_sepS_singleton.
    iSplit; eauto; iPureIntro; by econstructor. }
  rewrite [public_spec (TSeal _ _)]public_spec_eq; iSplit => //. by eauto.
Qed.

Lemma public_spec_open k t t' :
  Spec.open k t = Some t' →
  public_spec k -∗
  public_spec t -∗
  public_spec t'.
Proof.
rewrite /Spec.open.
case: t => // k_t t.
rewrite public_spec_TSeal.
case: decide => // k_t_k [<-]. rewrite k_t_k.
iIntros "p_k [[??]|(? & p_t)] //".
case e: func_of_term => [F|].
- iDestruct "p_t" as "(_ & _ & p_t)". by iApply "p_t".
- by case: k_t => // ?? in k_t_k e *.
Qed.

Lemma public_spec_THash t :
  public_spec (THash t) ⊣⊢ public_spec t ∨ minted_spec t ∧ wf_hash_spec t.
Proof.
apply: (anti_symm _).
- rewrite public_spec_eq minted_spec_THash.
  iDestruct 1 as "[Ht [publ | publ]]" => //; eauto.
  iDestruct "publ" as (T) "[%dec ?]".
  case: dec => //= {}t -> [->].
  by rewrite big_sepS_singleton; eauto.
- iDestruct 1 as "[Ht | [? publ]]".
    rewrite [public_spec (THash _)]public_spec_eq minted_spec_THash -public_spec_minted_spec.
    iSplit => //=; iLeft.
    iExists {[t]}; rewrite big_sepS_singleton; iSplit => //.
    iPureIntro; by econstructor.
  rewrite public_spec_eq; iSplit.
    by rewrite minted_spec_THash.
  by eauto.
Qed.

Lemma public_spec_TExpN t ts :
  ¬ is_exp t →
  ts ≠ [] →
  public_spec (TExpN t ts) ⊣⊢
  (∃ t' ts', ⌜ts ≡ₚ t' :: ts'⌝ ∧ public_spec (TExpN t ts') ∧ public_spec t') ∨
  minted_spec (TExpN t ts) ∧ [∗ list] t' ∈ ts, dh_spec_pred t' (TExpN t ts).
Proof.
move=> tNX tsN0.
have ttsX : is_exp (TExpN t ts).
  by rewrite is_exp_TExpN; case: (ts) tsN0.
have [? [] ? [] H etts] : ∃ t' ts' H, TExpN t ts = TExpN' t' ts' H.
  case: (TExpN t ts) ttsX => //=; eauto.
apply: (anti_symm _).
- rewrite public_spec_eq minted_spec_TExpN {2}etts {H etts}.
  iDestruct 1 as "[# [Ht Hts] [#publ | #publ]]".
  + iDestruct "publ" as (T) "[%dec publ]".
    move e: (TExpN t ts) => t' in dec ttsX *.
    case: dec ttsX; try by move=> * {e}; subst t'.
    rewrite -{}e {t'}.
    move=> t1 t2 -> _ e _.
    rewrite big_sepS_union_pers !big_sepS_singleton.
    iDestruct "publ" as "[publ1 publ2]".
    iLeft. iExists t2, (exps t1).
    have -> : TExpN t (exps t1) = t1.
      apply: base_exps_inj.
      * by move/(f_equal base): e; rewrite !base_TExpN.
      * by rewrite exps_TExpN exps_expN //=.
    do !iSplit => //. iPureIntro.
    have ->: ts ≡ₚ exps (TExpN t ts).
      by rewrite exps_TExpN exps_expN //; apply/is_trueP.
    by rewrite e exps_TExpN [_ ++ _]comm.
  + iRight; do 2?iSplit => //.
    by rewrite exps_TExpN exps_expN.
- iDestruct 1 as "# [publ | publ]".
  + iDestruct "publ" as (t' ts') "[%e [Ht1 Ht2]]".
    rewrite e in ttsX *.
    rewrite [public_spec (TExpN _ (_ :: _))]public_spec_eq minted_spec_TExpN /=.
    iSplit.
      rewrite !public_spec_minted_spec minted_spec_TExpN /=.
      by iDestruct "Ht1" as "[??]"; eauto.
    iLeft.
    iExists {[TExpN t ts'; t']}.
    rewrite big_sepS_union_pers !big_sepS_singleton.
    do !iSplit => //.
    iPureIntro.
    rewrite -TExp_TExpN; apply: DExp; eauto.
    by rewrite TExp_TExpN.
  + iDestruct "publ" as "[s p]"; rewrite public_spec_eq [minted_spec]unlock; iSplit=> //.
    rewrite {4}etts; iRight.
    by rewrite exps_TExpN exps_expN //.
Qed.

Lemma public_spec_TExp_iff t1 t2 :
  ¬ is_exp t1 →
  public_spec (TExp t1 t2) ⊣⊢
  public_spec t1 ∧ public_spec t2 ∨
  minted_spec t1 ∧ minted_spec t2 ∧ dh_spec_pred t2 (TExp t1 t2).
Proof.
move=> ?; rewrite public_spec_TExpN //=.
apply: (anti_symm _); iIntros "#pub".
- iDestruct "pub" as "[pub | pub]" => //.
    iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
    symmetry in e.
    case/Permutation_singleton_r: e => -> ->; eauto.
    rewrite TExp0; eauto.
  by rewrite minted_spec_TExp /=; iDestruct "pub" as "[[??] [??]]"; eauto.
- iDestruct "pub" as "[[p1 p2] | (s1 & s2 & pub)]".
    by iLeft; iExists t2, []; rewrite TExp0; eauto.
  by iRight; rewrite /= minted_spec_TExp; do !iSplit => //=.
Qed.

Lemma public_spec_TExp2_iff t1 t2 t3 :
  ¬ is_exp t1 →
  public_spec (TExpN t1 [t2; t3]) ⊣⊢
  public_spec (TExpN t1 [t2]) ∧ public_spec t3 ∨
  public_spec (TExpN t1 [t3]) ∧ public_spec t2 ∨
  minted_spec (TExpN t1 [t2; t3]) ∧
  dh_spec_pred t2 (TExpN t1 [t2; t3]) ∧
  dh_spec_pred t3 (TExpN t1 [t2; t3]).
Proof.
move=> t1NX. rewrite public_spec_TExpN //.
apply: (anti_symm _); iIntros "#pub".
- rewrite /=; iDestruct "pub" as "[pub | (? & ? & ? & _)]" => //; eauto.
  iDestruct "pub" as (??) "(%e & p_t1 & p_t2)".
  by case: (Permutation_length_2_inv e) => [[-> ->] | [-> ->]]; eauto.
- iDestruct "pub" as "[[? ?] | [[? ?] | (? & ? & ?)]]".
  + iLeft; iExists t3, [t2]; do !iSplit => //.
    iPureIntro; apply: perm_swap.
  + by iLeft; iExists t2, [t3]; do !iSplit => //.
  + iRight; do !iSplit => //=.
Qed.

Lemma public_spec_TExp t1 t2 :
  public_spec t1 -∗
  public_spec t2 -∗
  public_spec (TExp t1 t2).
Proof.
iIntros "#p1 #p2".
rewrite -{2}(base_expsK t1) TExp_TExpN public_spec_TExpN //.
by iLeft; iExists t2, (exps t1); rewrite base_expsK; eauto.
Qed.

Lemma public_spec_to_list t ts :
  Spec.to_list t = Some ts →
  public_spec t -∗ [∗ list] t' ∈ ts, public_spec t'.
Proof.
elim/term_ind': t ts => //=.
  by case=> // ts [<-] /=; iIntros "?".
move=> t _ tl IH ts.
case e: (Spec.to_list tl) => [ts'|] // [<-] /=.
rewrite public_spec_TPair /=; iIntros "[??]"; iFrame.
by iApply IH.
Qed.

Lemma public_spec_of_list ts :
  public_spec (Spec.of_list ts) ⊣⊢
  [∗ list] t ∈ ts, public_spec t.
Proof.
rewrite Spec.of_list_unseal.
elim: ts => [|t ts IH]; first by rewrite public_spec_TInt.
by rewrite public_spec_TPair /= IH bi.persistent_and_sep.
Qed.

Lemma public_spec_Tag N : public_spec (Tag N) ⊣⊢ True.
Proof. by rewrite Tag_unseal public_spec_TInt. Qed.

Lemma public_spec_tag N t : public_spec (Spec.tag (Tag N) t) ⊣⊢ public_spec t.
Proof.
by rewrite Spec.tag_unseal public_spec_TPair public_spec_Tag bi.emp_and.
Qed.

Lemma public_spec_TSeal_tag k N t :
  public_spec (TSeal k (Spec.tag (Tag N) t)) ⊣⊢
  public_spec k ∧ public_spec t ∨
  minted_spec k ∧ minted_spec t ∧
  match func_of_term k with
  | Some F => ∃ Φ,
      ⌜Spec.is_seal_key k⌝ ∧
      seal_spec_pred F N Φ ∧
      □ ▷ Φ (Spec.skey k) t ∧
      match Spec.open_key k with
      | Some k' => □ (public_spec k' → public_spec t)
      | None => True
      end
  | None => True
  end.
Proof.
rewrite public_spec_TSeal {1}public_spec_tag minted_spec_TSeal minted_spec_tag.
rewrite [(_ ∧ _ ∧ _)%I]assoc.
apply: bi.or_proper => //.
apply: bi.and_proper => //.
case: func_of_term => // F.
apply (anti_symm _).
- iIntros "(? & (%N' & %t' & %Φ & %e & ? & ?) & ?)".
  case/Spec.tag_inj: e => [/Tag_inj <- <-].
  iExists Φ. do !iSplit => //.
  case: Spec.open_key => // k'. by rewrite public_spec_tag.
- iIntros "(%Φ & ? & ? & ? & ?)".
  do !iSplit => //.
  + iExists N, t, Φ. by eauto.
  + case: Spec.open_key => // k'. by rewrite public_spec_tag.
Qed.

Lemma public_spec_TSealE N Φ k t F :
  public_spec (TSeal k (Spec.tag (Tag N) t)) -∗
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_spec_pred F N Φ -∗
  public_spec k ∧ public_spec t ∨
  □ ▷ Φ (Spec.skey k) t ∧
  match Spec.open_key k with
  | Some k' => □ (public_spec k' → public_spec t)
  | None => True
  end.
Proof.
iIntros "#Ht %kP #HΦ"; rewrite public_spec_TSeal; case: kP => [-> k_seal].
iDestruct "Ht" as "[[? Ht] | [_ Ht]]"; first by rewrite public_spec_tag; eauto.
iDestruct "Ht" as "(_ & inv & ?)".
iPoseProof (wf_seal_spec_elim with "inv HΦ") as "?".
iRight. iSplit => //. case: Spec.open_key => // ?.
by rewrite public_spec_tag.
Qed.

Lemma public_spec_TSealIS F N Φ k t :
  ⌜func_of_term k = Some F ∧ Spec.is_seal_key k⌝ -∗
  seal_spec_pred F N Φ -∗
  □ Φ (Spec.skey k) t -∗
  minted_spec k -∗
  minted_spec t -∗
  match Spec.open_key k with
  | Some k' => □ (public_spec k' → public_spec t)
  | None => True
  end -∗
  public_spec (TSeal k (Spec.tag (Tag N) t)).
Proof.
iIntros "[%k_F %kP] #HΦ #HΦt #m_k #m_t #Hopenl".
rewrite public_spec_TSeal k_F. iRight. rewrite minted_spec_TSeal minted_spec_tag.
iSplit; first by eauto. iSplit => //. iSplit; last first.
{ case: Spec.open_key => // ?. by rewrite public_spec_tag. }
iExists N, t, Φ. eauto.
Qed.

Lemma public_spec_TSealIP k t :
  public_spec k -∗
  public_spec t -∗
  public_spec (TSeal k t).
Proof. by iIntros "? ?"; rewrite public_spec_TSeal; eauto. Qed.

Lemma nonce_alloc_spec P Q a :
  meta_token a ⊤ -∗
  (minted_spec (TNonce a) -∗ False) ∧
  |==> minted_spec (TNonce a) ∗
    □ (public_spec (TNonce a) ↔ ▷ □ P (TNonce a)) ∗
    □ (∀ t, dh_spec_pred (TNonce a) t ↔ ▷ □ Q t).
Proof.
iIntros "token".
iSplit.
{ rewrite minted_spec_TNonce. iIntros "contra".
  by iDestruct (meta_meta_token with "token contra") as "[]". }
iMod (own_alloc (saved_pred DfracDiscarded P)) as (γP) "#own_P" => //.
iMod (own_alloc (saved_pred DfracDiscarded Q)) as (γQ) "#own_Q" => //.
rewrite (meta_token_difference a (↑nroot.@"nonce_spec")) //.
iDestruct "token" as "[nonce token]".
iMod (meta_set _ _ γP with "nonce") as "#nonce"; eauto.
rewrite (meta_token_difference a (↑nroot.@"dh_spec")); last solve_ndisj.
iDestruct "token" as "[dh token]".
iMod (meta_set _ _ γQ with "dh") as "#dh"; eauto.
rewrite (meta_token_difference a (↑nroot.@"minted_spec")); last solve_ndisj.
iDestruct "token" as "[minted token]".
iMod (meta_set _ _ () (nroot.@"minted_spec") with "minted") as "#minted" => //.
iSplitR.
  by rewrite minted_spec_TNonce.
iSplitR.
  rewrite public_spec_TNonce; do 2!iModIntro; iSplit.
  + iIntros "[#public _]".
    iDestruct "public" as (γP' P') "(#meta_γP' & #own_P' & ?)".
    iPoseProof (meta_agree with "nonce meta_γP'") as "->".
    iPoseProof (own_valid_2 with "own_P own_P'") as "valid".
    iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
    iSpecialize ("e" $! (TNonce a)). iModIntro. by iRewrite "e".
  + iIntros "#?". iSplit => //. iExists γP, P; eauto.
iIntros "!> !> %t"; iSplit.
- iDestruct 1 as (γQ' Q') "(#meta_γQ' & #own_Q' & ?)".
  iPoseProof (meta_agree with "dh meta_γQ'") as "->".
  iPoseProof (own_valid_2 with "own_Q own_Q'") as "valid".
  iPoseProof (saved_pred_op_validI with "valid") as "[_ #e]".
  iSpecialize ("e" $! t). iModIntro. by iRewrite "e".
- by iIntros "#?"; iExists _, _; eauto.
Qed.

Lemma public_spec_pkey k : public_spec k ⊢ public_spec (Spec.pkey k).
Proof.
iIntros "#p_k".
iPoseProof (public_spec_minted_spec with "p_k") as "m_k".
case: k => // - [] // t; iClear "p_k";
rewrite minted_spec_TKey public_spec_TKey /=; eauto.
Qed.

Lemma public_spec_senc_key k : public_spec (SEncKey k) ⊣⊢ public_spec k.
Proof.
rewrite [term_of_senc_key]unlock public_spec_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_spec_senc_key' (sk : senc_key) :
  public_spec sk ⊣⊢ public_spec (seed_of_senc_key sk).
Proof.
case: sk => seed. by rewrite public_spec_senc_key.
Qed.

Lemma public_spec_aenc_key (sk : aenc_key) : public_spec (Spec.pkey sk) ⊣⊢ minted_spec sk.
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => [seed] /=.
rewrite public_spec_TKey /= minted_spec_TKey. iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_spec_minted_spec.
Qed.

Lemma public_spec_adec_key k : public_spec (AEncKey k) ⊣⊢ public_spec k.
Proof.
rewrite [term_of_aenc_key]unlock public_spec_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_spec_adec_key' (sk : aenc_key) :
  public_spec sk ⊣⊢ public_spec (seed_of_aenc_key sk).
Proof. case: sk => seed. by rewrite public_spec_adec_key. Qed.

Lemma public_spec_verify_key (sk : sign_key) : public_spec (Spec.pkey sk) ⊣⊢ minted_spec sk.
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=. rewrite public_spec_TKey /= minted_spec_TKey.
iSplit; eauto.
iIntros "[#p_k|[? ?]]"; eauto.
by iApply public_spec_minted_spec.
Qed.

Lemma public_spec_sign_key k : public_spec (SignKey k) ⊣⊢ public_spec k.
Proof.
rewrite [term_of_sign_key]unlock public_spec_TKey /=.
iSplit; eauto.
by iIntros "[#p_k|[? []]]"; eauto.
Qed.

Lemma public_spec_sign_key' (sk : sign_key) :
  public_spec sk ⊣⊢ public_spec (seed_of_sign_key sk).
Proof.
case: sk => seed. by rewrite public_spec_sign_key.
Qed.

Definition pending_spec γ : iProp :=
  gmeta_token γ ⊤.

Definition shot_spec γ (x : positive) : iProp :=
  gmeta γ nroot x.

Global Instance persistent_shot_spec γ x : Persistent (shot_spec γ x).
Proof. apply _. Qed.

Global Instance timeless_shot_spec γ x : Timeless (shot_spec γ x).
Proof. apply _. Qed.

Lemma pending_spec_alloc : ⊢ |==> ∃ γ, pending_spec γ.
Proof. apply gmeta_token_alloc. Qed.

Lemma shot_spec_alloc γ x : pending_spec γ ==∗ shot_spec γ x.
Proof. by apply gmeta_set. Qed.

Lemma pending_spec_shot_spec γ x : pending_spec γ -∗ shot_spec γ x -∗ False.
Proof. by apply gmeta_gmeta_token. Qed.

Lemma shot_spec_agree γ x y : shot_spec γ x -∗ shot_spec γ y -∗ ⌜x = y⌝.
Proof. apply gmeta_agree. Qed.

Definition secret_spec t : iProp :=
  (|==> public_spec t) ∧
  (|==> □ (public_spec t ↔ ▷ False)) ∧
  (public_spec t -∗ ▷ False).

Lemma secret_spec_alloc t γ :
  □ (public_spec t ↔ ▷ shot_spec γ 1) -∗ pending_spec γ -∗ secret_spec t.
Proof.
iIntros "#s_t pending_spec"; do 2?iSplit.
- iMod (shot_spec_alloc with "pending_spec") as "#shot_spec".
  by iSpecialize ("s_t" with "shot_spec").
- iMod (shot_spec_alloc _ 2 with "pending_spec") as "#shot_spec".
  iIntros "!> !>". iSplit.
  + iIntros "#p_t".
    iPoseProof ("s_t" with "p_t") as ">#shot_spec'".
    by iPoseProof (shot_spec_agree with "shot_spec shot_spec'") as "%".
  + iIntros "#contra".
    iApply "s_t". by iDestruct "contra" as ">[]".
- iIntros "#p_t".
  iPoseProof ("s_t" with "p_t") as ">#shot_spec".
  by iPoseProof (pending_spec_shot_spec with "[$] [//]") as "[]".
Qed.

Lemma secret_spec_not_public_spec t : secret_spec t -∗ public_spec t -∗ ▷ False.
Proof. by iIntros "(_ & _ & contra)". Qed.

Lemma secret_spec_public_spec t : secret_spec t ==∗ public_spec t.
Proof. by iIntros "(? & _)". Qed.

Lemma freeze_secret_spec t : secret_spec t ==∗ □ (public_spec t ↔ ▷ False).
Proof. by iIntros "(_ & ? & _)". Qed.

Lemma public_spec_aencIS (sk : aenc_key) N Φ t :
  aenc_spec_pred N Φ -∗
  minted_spec sk -∗
  minted_spec t -∗
  □ Φ sk t -∗
  □ (public_spec sk → public_spec t) -∗
  public_spec (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_aenc_key]unlock; case: sk => seed /=.
rewrite minted_spec_TKey. iIntros "#? #m_k #m_t #inv #p_t".
iApply public_spec_TSealIS => //.
- iModIntro. iExists (AEncKey _). rewrite [term_of_aenc_key]unlock. by eauto.
- by rewrite minted_spec_TKey.
Qed.

Lemma public_spec_sencIS (k : senc_key) N Φ t :
  senc_spec_pred N Φ -∗
  minted_spec k -∗
  minted_spec t -∗
  □ Φ k t -∗
  □ (public_spec k → public_spec t) -∗
  public_spec (TSeal k (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_senc_key]unlock; case: k => seed /=.
iIntros "#? #m_k #m_t #inv #p_t".
iApply public_spec_TSealIS => //.
iModIntro. iExists (SEncKey _). rewrite [term_of_senc_key]unlock. by eauto.
Qed.

Lemma public_spec_signIS (sk : sign_key) N Φ t :
  sign_spec_pred N Φ -∗
  minted_spec sk -∗
  public_spec t -∗
  □ Φ sk t -∗
  public_spec (TSeal sk (Spec.tag (Tag N) t)).
Proof.
rewrite [term_of_sign_key]unlock; case: sk => seed /=.
rewrite minted_spec_TKey.
iIntros "#? #m_k #p_t #inv".
iApply public_spec_TSealIS => //.
- iModIntro. iExists (SignKey _). rewrite [term_of_sign_key]unlock; by eauto.
- by rewrite minted_spec_TKey.
- by iApply public_spec_minted_spec.
- by iIntros "!> _".
Qed.

Lemma public_spec_aencE (sk : aenc_key) N Φ t :
  public_spec (TSeal (Spec.pkey sk) (Spec.tag (Tag N) t)) -∗
  aenc_spec_pred N Φ -∗
  minted_spec t ∧ (public_spec t ∨ □ ▷ Φ sk t ∧ □ (public_spec sk → public_spec t)).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_spec_minted_spec with "p_t") as "#m_t".
  rewrite minted_spec_TSeal minted_spec_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_spec_TSealE with "p_t [//] [//]") as "[[_ comp]|inv]"; eauto.
rewrite /=. iDestruct "inv" as "[#inv #?]". iRight. iSplit => //.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e. by case: k' e => seed' // [<-].
Qed.

Lemma public_spec_signE (sk : sign_key) N Φ t :
  public_spec (TSeal sk (Spec.tag (Tag N) t)) -∗
  sign_spec_pred N Φ -∗
  public_spec t ∧ (public_spec sk ∨ □ ▷ Φ sk t).
Proof.
rewrite keysE; case: sk => seed /=.
iIntros "#p_t #?". iPoseProof (public_spec_minted_spec with "p_t") as "m_t".
rewrite minted_spec_TSeal minted_spec_TKey. iDestruct "m_t" as "[? _]".
iPoseProof (public_spec_TSealE with "p_t [//] [//]") as "[[??]|inv]"; eauto.
iDestruct "inv" as "{p_t} (#inv & #p_t)". iSplit => //.
- iApply "p_t". iApply public_spec_TKey. iRight. by iSplit => //.
- iRight. iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
  rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.

Lemma public_spec_sencE (k : senc_key) N Φ t :
  public_spec (TSeal k (Spec.tag (Tag N) t)) -∗
  senc_spec_pred N Φ -∗
  minted_spec t ∧ (public_spec k ∨ □ ▷ Φ k t) ∧ □ (public_spec k → public_spec t).
Proof.
rewrite keysE; case: k => seed /=.
iIntros "#p_t #?". iSplit => //.
{ iPoseProof (public_spec_minted_spec with "p_t") as "#m_t".
  rewrite minted_spec_TSeal minted_spec_tag. by iDestruct "m_t" as "[_ ?]". }
iPoseProof (public_spec_TSealE with "p_t [//] [//]") as "[[??]|[#inv #p_t']]";
eauto. iSplit => //. iRight.
iIntros "!> !>". iDestruct "inv" as "(%k' & %e & inv)".
rewrite keysE in e; by case: k' e => seed' // [<-].
Qed.

End PublicSpec.

Arguments public_spec_aenc_name {Σ _}.
Arguments public_spec_sign_name {Σ _}.
Arguments public_spec_senc_name {Σ _}.
Arguments seal_spec_pred {Σ _} F N Φ.
Arguments seal_spec_pred_set {Σ _} F {_} N Φ.
Arguments seal_spec_pred_token_difference {Σ _} F E1 E2.
Arguments public_spec_hash_name {Σ _}.
Arguments hash_spec_pred {Σ _} N P.
Arguments hash_spec_pred_set {Σ _ _} N P.
Arguments hash_spec_pred_token_difference {Σ _} E1 E2.

Lemma public_specGS_alloc `{!relocG Σ} E :
  publicGpreS Σ →
  ⊢ |={E}=> ∃ (H : public_specGS Σ),
             seal_spec_pred_token AENC ⊤ ∗
             seal_spec_pred_token SIGN ⊤ ∗
             seal_spec_pred_token SENC ⊤ ∗
             hash_spec_pred_token ⊤.
Proof.
move=> ?; iStartProof.
iMod gmeta_token_alloc as (γ_aenc) "own_aenc".
iMod gmeta_token_alloc as (γ_sign) "own_sign".
iMod gmeta_token_alloc as (γ_senc) "own_senc".
iMod gmeta_token_alloc as (γ_hash) "own_hash".
pose (H := PublicSpecGS _ γ_aenc γ_sign γ_senc γ_hash).
iExists H. by iFrame.
Qed.

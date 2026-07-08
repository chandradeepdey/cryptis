From iris.base_logic.lib Require Import gset_bij.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import saved_prop.
From cryptis.core Require Import term minted.
From cryptis Require Import cryptis.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_bij :: gset_bijG Σ term term;
  #[local] public_relGpreS_term_meta :: term_metaGpreS Σ;
  #[local] public_relGpreS_prop :: savedPropG Σ;
}.

Class public_relGS Σ := Public_relGS {
  #[global] public_relGS_bij :: gset_bijG Σ term term;
  #[global] public_rel_term_meta :: term_metaGS Σ;
  #[global] public_rel_term_meta_spec :: term_meta_specGS Σ;
  #[global] public_relGS_prop :: savedPropG Σ;
  public_rel_name  : gname;
}.

Definition public_relΣ : gFunctors :=
  #[gset_bijΣ term term;
    term_metaΣ;
    savedPropΣ].

#[global] Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation lrelO := (term -d> term -d> iPropO).

Implicit Types t : term.
Implicit Types pub : gset (term * term).
Implicit Types P : lrelO.

Definition public_rel_auth pub : iProp :=
  gset_bij_own_auth public_rel_name (DfracOwn 1) pub.

Definition public_rel_elem t1 t2 : iProp :=
  gset_bij_own_elem public_rel_name t1 t2.

Definition public_rel_inv pub : iProp :=
  public_rel_auth pub ∗
  ([∗ set] p ∈ pub,
    term_meta p.1 (cryptisN.@"public_rel") () ∗
    term_meta_spec p.2 (cryptisN.@"public_rel") ()).

Definition public_rel_ctx : iProp :=
  inv cryptisN (∃ pub, public_rel_inv pub).

Definition cryptis_rel_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_rel_ctx.

#[global] Instance cryptis_rel_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance cryptis_rel_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

Lemma public_rel_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel") -∗
  term_token_spec t' (↑cryptisN.@"public_rel") -∗
  |={E}=> public_rel_elem t t'.
Proof.
  iIntros (HE) "#(_ & _ & Hinv) Htt Htts".
  iInv "Hinv" as "(%pub & (>Hauth & Htoken))".
  iAssert (▷ ⌜∀ t', (t, t') ∉ pub⌝)%I as "#>%Htnpub".
  { iModIntro. iIntros (t'' Ht'').
    rewrite big_sepS_forall.
    iSpecialize ("Htoken" $! (t, t'') with "[//]").
    iDestruct "Htoken" as "[Htoken _]".
    iDestruct (term_meta_token with "Htt Htoken") as "[]"=> //. }
  iAssert (▷ ⌜∀ t, (t, t') ∉ pub⌝)%I as "#>%Ht'npub".
  { iModIntro. iIntros (t'' Ht'').
    rewrite big_sepS_forall.
    iSpecialize ("Htoken" $! (t'', t') with "[//]").
    iDestruct "Htoken" as "[_ Htokens]".
    iDestruct (term_meta_spec_token with "Htts Htokens") as "[]"=> //. }
  iMod (gset_bij_own_extend with "Hauth") as "[Hauth #Hfrag]"; eauto.
  iMod (term_meta_set (cryptisN.@"public_rel") () with "Htt") as "#Htt"=> //.
  iMod (term_meta_spec_set (cryptisN.@"public_rel") () with "Htts") as "#Htts"=> //.
  iModIntro.
  iFrame.
  rewrite big_sepS_union_pers big_sepS_singleton.
  iFrame.
  by iFrame "#".
Qed.

Definition pnonce_rel t1 t2 : iProp :=
  □ term_prop t1 (cryptisN.@"public_rel_pnonce") ∧
  □ term_prop_spec t2 (cryptisN.@"public_rel_pnonce").

#[global] Instance Persistent_pnonce_rel t1 t2 : Persistent (pnonce_rel t1 t2).
Proof. apply _. Qed.

Lemma pnonce_rel_alloc t1 t2 E (P : iProp) :
  ↑cryptisN.@"public_rel_pnonce" ⊆ E →
    term_token t1 E ∗ term_token_spec t2 E ==∗
  □ (pnonce_rel t1 t2 ↔ ▷ □ P) ∗
    term_token t1 (E ∖ ↑cryptisN.@"public_rel_pnonce") ∗
    term_token_spec t2 (E ∖ ↑cryptisN.@"public_rel_pnonce").
Proof.
  iIntros (?) "[token token_spec]".
  iMod (term_prop_alloc (nroot.@"cryptis".@"public_rel_pnonce") P with "token")
    as "[#H1 $]" => //.
  iMod (term_prop_spec_alloc (nroot.@"cryptis".@"public_rel_pnonce") P with "token_spec")
    as "[#H2 $]" => //.
  iIntros "!> !>"; iSplit; iIntros "#H3".
  - by iDestruct "H3" as "#[H3 _]"; iSpecialize ("H1" with "H3"); eauto.
  - rewrite /pnonce_rel; iSplit; iIntros "!>".
    + iApply "H1"; eauto.
    + iApply "H2"; eauto.
Qed.

Definition double_squiggle_pre P : lrelO := λ t1 t2,
  (□ (∀ t2', ▷ P t1 t2' -∗ ▷ ⌜t2 = t2'⌝) ∧
  □ (∀ t1', ▷ P t1' t2 -∗ ▷ ⌜t1 = t1'⌝))%I.

#[local] Instance double_squiggle_pre_persistent P t1 t2 : Persistent (double_squiggle_pre P t1 t2).
Proof. apply _. Qed.

Definition publicly_related_pre P : lrelO :=
  fix publicly_related_pre t1 t2 {struct t1} : iProp :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      publicly_related_pre t11 t21 ∧ publicly_related_pre t12 t22
  | TNonce l1, TNonce l2 => public_rel_elem t1 t2 ∧ ◇ pnonce_rel t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => publicly_related_pre t1' t2' ∨
              (public_rel_elem t1 t2 ∧ double_squiggle_pre P t1' t2')
    | ADec => publicly_related_pre t1' t2'
    | Sign => publicly_related_pre t1' t2'
    | Verify => publicly_related_pre t1' t2' ∨
                (public_rel_elem t1 t2 ∧ double_squiggle_pre P t1' t2')
    | SEnc => publicly_related_pre t1' t2'
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (publicly_related_pre k1 k2 ∧ publicly_related_pre t1' t2') ∨
    (public_rel_elem t1 t2 ∧ double_squiggle_pre P k1 k2 ∧ double_squiggle_pre P t1' t2' ∧
    □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | ADec | Verify => False
        | Sign => publicly_related_pre t1' t2'
        | AEnc | SEnc => publicly_related_pre k1 k2 → publicly_related_pre t1' t2'
        end
      | _, _ => False
      end))
  | THash t1', THash t2' =>
    publicly_related_pre t1' t2' ∨
    (public_rel_elem t1 t2 ∧ double_squiggle_pre P t1' t2')
  | TExpN' _ _ _, TExpN' _ _ _ =>
      False (* FIXME *)
  | _, _ =>
      False (* WIP *)
  end%I.

#[local] Instance publicly_related_pre_persistent P t1 t2 : Persistent (publicly_related_pre P t1 t2).
Proof.
elim/term_lt_ind: t1 t2 => // -[] //=.
- move=> ? ? [] *; apply _.
- move=> t11 t12 IH []; try apply _.
  move=> t21 t22.
  have IH1: Persistent (publicly_related_pre P t11 t21).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  have IH2: Persistent (publicly_related_pre P t12 t22).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  apply _.
- move=> ? ? [] *; apply _.
- move=> k1 t1' IH []; try apply _.
  move=> k2 t2'.
  have {}IH: Persistent (publicly_related_pre P t1' t2').
  { apply IH. rewrite /tsize /=. lia. }
  apply _.
- move=> k1 t1' IH []; try apply _.
  move=> k2 t2'.
  have IH1: Persistent (publicly_related_pre P k1 k2).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  have IH2: Persistent (publicly_related_pre P t1' t2').
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  apply _.
- move=> t1' IH []; try apply _.
  move=> t2'.
  have {}IH: Persistent (publicly_related_pre P t1' t2').
  { apply IH. rewrite /tsize /=. lia. }
  apply _.
all: apply _.
Qed.

#[local] Instance publicly_related_pre_contractive : Contractive publicly_related_pre.
Proof.
  move=> n P P' HP t1 t2.
  elim/term_lt_ind: t1 t2 => // -[] //=.
  - move=> t11 t12 IH [] //= t21 t22.
    rewrite /tsize in IH.
    f_equiv; apply: IH; rewrite /= ssrnat.addnE; lia.
  - move=> kt1 t1' IH [] //= kt2 t2'.
    rewrite /tsize in IH.
    f_equiv.
    have {}IH: ∀ t2, publicly_related_pre P t1' t2 ≡{n}≡ publicly_related_pre P' t1' t2.
    { apply: IH. simpl. lia. }
    case: kt1 => //=.
    + f_equiv; first done.
      f_equiv; solve_contractive.
    + f_equiv; first done.
      f_equiv; solve_contractive.
  - move=> k1 t1' IH [] //= k2 t2'.
    rewrite /tsize in IH; f_equiv.
    + f_equiv; apply: IH; rewrite /= ssrnat.addnE; lia.
    + f_equiv.
      f_equiv. solve_contractive.
      f_equiv. solve_contractive.
      f_equiv.
      case: k1 => //= kt1 k1 in IH*.
      case: k2 => //= kt2 k2.
      f_equiv.
      have IH1: publicly_related_pre P t1' t2' ≡{n}≡ publicly_related_pre P' t1' t2'.
      { apply: IH. rewrite /= ssrnat.addnE. lia. }
      have IH2: publicly_related_pre P k1 k2 ≡{n}≡ publicly_related_pre P' k1 k2.
      { apply: IH. rewrite /= ssrnat.addnE. lia. }
      case: kt1 => //=; by f_equiv.
  - move=> t1' IH [] //= t2'.
    rewrite /tsize in IH.
    have {}IH: publicly_related_pre P t1' t2' ≡{n}≡ publicly_related_pre P' t1' t2'.
    { apply IH. simpl. lia. }
    f_equiv. solve_contractive.
    f_equiv. solve_contractive.
Qed.

#[local] Definition publicly_related_def : lrelO :=
  fixpoint (publicly_related_pre).
#[local] Definition publicly_related_aux : seal publicly_related_def. Proof. by eexists. Qed.
Definition publicly_related := publicly_related_aux.(unseal).
#[local] Lemma publicly_related_unseal : publicly_related = publicly_related_def.
Proof. rewrite -publicly_related_aux.(seal_eq) //. Qed.

Definition double_squiggle := double_squiggle_pre publicly_related.

Infix "≈" := double_squiggle (at level 50, no associativity) : bi_scope.

Lemma publicly_related_unfold :
  ∀ t1 t2, publicly_related t1 t2 ⊣⊢
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      publicly_related t11 t21 ∧ publicly_related t12 t22
  | TNonce l1, TNonce l2 => public_rel_elem t1 t2 ∧ ◇ pnonce_rel t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => publicly_related t1' t2' ∨
              (public_rel_elem t1 t2 ∧ t1' ≈ t2')
    | ADec => publicly_related t1' t2'
    | Sign => publicly_related t1' t2'
    | Verify => publicly_related t1' t2' ∨
                (public_rel_elem t1 t2 ∧ t1' ≈ t2')
    | SEnc => publicly_related t1' t2'
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (publicly_related k1 k2 ∧ publicly_related t1' t2') ∨
    (public_rel_elem t1 t2 ∧ k1 ≈ k2 ∧ t1' ≈ t2' ∧
    □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | ADec | Verify => False
        | Sign => publicly_related t1' t2'
        | _ => publicly_related k1 k2 → publicly_related t1' t2'
        end
      | _, _ => False
      end))
  | THash t1', THash t2' =>
    publicly_related t1' t2' ∨
    (public_rel_elem t1 t2 ∧ t1' ≈ t2')
  | TExpN' _ _ _, TExpN' _ _ _ =>
      False (* FIXME *)
  | _, _ =>
      False (* WIP *)
  end.
Proof.
  rewrite /double_squiggle publicly_related_unseal /publicly_related_def => t1 t2.
  rewrite (fixpoint_unfold publicly_related_pre t1 t2).
  case: t1 => //= [t11 t12|kt1 t1'|k1 t1'|t1'].
  1: case: t2 => //= t21 t22.
  2: case: t2 => //= kt2 t2'.
  3: case: t2 => //= k2 t2'.
  4: case: t2 => //= t2'.
  all: repeat f_equiv.
  by rewrite (fixpoint_unfold publicly_related_pre t11 t21).
  by rewrite (fixpoint_unfold publicly_related_pre t12 t22).
  all: try by rewrite (fixpoint_unfold publicly_related_pre t1' t2').
  all: try by rewrite (fixpoint_unfold publicly_related_pre k1 k2).
Qed.

#[global] Instance publicly_related_persistent t1 t2 : Persistent (publicly_related t1 t2).
Proof.
  rewrite /double_squiggle publicly_related_unseal /publicly_related_def.
  rewrite (fixpoint_unfold publicly_related_pre t1 t2).
  apply _.
Qed.

Lemma publicly_related_TInt n1 n2 :
  publicly_related (TInt n1) (TInt n2) ⊣⊢ ⌜n1 = n2⌝.
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_TPair t11 t12 t21 t22 :
  publicly_related (TPair t11 t12) (TPair t21 t22) ⊣⊢
  (publicly_related t11 t21 ∧ publicly_related t12 t22).
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_TNonce l1 l2 :
  publicly_related (TNonce l1) (TNonce l2) ⊣⊢
  public_rel_elem (TNonce l1) (TNonce l2) ∧
    ◇ pnonce_rel (TNonce l1) (TNonce l2).
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_TKey kt1 kt2 t1 t2 :
  publicly_related (TKey kt1 t1) (TKey kt2 t2) ⊣⊢
  ⌜kt1 = kt2⌝ ∧
  match kt1 with
  | AEnc => publicly_related t1 t2 ∨
            (public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ t1 ≈ t2)
  | ADec => publicly_related t1 t2
  | Sign => publicly_related t1 t2
  | Verify => publicly_related t1 t2 ∨
              (public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ t1 ≈ t2)
  | SEnc => publicly_related t1 t2
  end.
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_TSeal k1 k2 t1 t2 :
  publicly_related (TSeal k1 t1) (TSeal k2 t2) ⊣⊢
  (publicly_related k1 k2 ∧ publicly_related t1 t2) ∨
  (public_rel_elem (TSeal k1 t1) (TSeal k2 t2) ∧
   k1 ≈ k2 ∧ t1 ≈ t2 ∧
   □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | ADec | Verify => False
        | Sign => publicly_related t1 t2
        | _ => publicly_related k1 k2 → publicly_related t1 t2
        end
      | _, _ => False
      end)).
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_THash t1 t2 :
  publicly_related (THash t1) (THash t2) ⊣⊢
  (publicly_related t1 t2) ∨ (public_rel_elem (THash t1) (THash t2) ∧ t1 ≈ t2).
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_open k1 k2 t1 t2 t1' t2' :
  Spec.open k1 t1 = Some t1' →
  Spec.open k2 t2 = Some t2' →
  publicly_related k1 k2 -∗
  publicly_related t1 t2 -∗
  publicly_related t1' t2'.
Proof.
rewrite /Spec.open.
case: t1 => // k_t1 t1.
case: t2 => // k_t2 t2.
rewrite publicly_related_TSeal.
case: decide => // k_t_k1 [<-].
case: decide => // k_t_k2 [<-].
iIntros "#Hk #[[_ Ht]|(Hfrag & ≈k & ≈t & #Hrest)]"; first done.
case: k_t1 k_t2 => // kt1 k1' [] // kt2 k2' in k_t_k1 k_t_k2 *.
iDestruct "Hrest" as "[<- Hrest]".
case: kt1 k_t_k1 k_t_k2 => // - [<-] [<-].
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
Qed.

#[local] Lemma publicly_related_part_bij_1 t1 t2 t2' :
  publicly_related t1 t2 -∗
  publicly_related t1 t2' -∗
  ▷ ⌜t2 = t2'⌝.
Proof.
elim/term_lt_ind: t1 t2 t2' => t1 IH t2 t2'.
rewrite !publicly_related_unfold.
case: t1 IH.
- move=> n1 IH.
  case: t2; auto.
  move=> n2.
  case: t2'; auto.
  move=> n2'.
  iIntros (H1 H2).
  iPureIntro.
  congruence.
- move=> t11 t12 IH.
  case: t2; auto.
  move=> t21 t22.
  case: t2'; auto.
  move=> t2'1 t2'2.
  iIntros "#[H21 H22] #[H2'1 H2'2]".
  iAssert (▷ ⌜t21 = t2'1⌝)%I as ">->".
  { iApply (IH t11). rewrite /tsize /= ssrnat.addnE.
    lia. all: auto. }
  iAssert (▷ ⌜t22 = t2'2⌝)%I as ">->".
  { iApply (IH t12). rewrite /tsize /= ssrnat.addnE.
    lia. all: auto. }
  auto.
- move=> l1 _.
  case: t2; auto.
  iIntros (l2) "#[H2 _]".
  case: t2'; auto.
  iIntros (l2') "#[H2' _]".
  iPoseProof (gset_bij_own_elem_agree with "H2 H2'") as "%H".
  iPureIntro. by apply H.
- move=> kt1 t1 IH.
  case: t2; auto.
  iIntros (kt2 t2) "[-> #Ht2]".
  case: t2'; auto.
  iIntros (kt2' t2') "[-> #Ht2']".
  have {}IH: (∀ t2 t2', publicly_related t1 t2 -∗
                        publicly_related t1 t2' -∗
                        ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  case: kt2'.
    iDestruct "Ht2" as "#[Ht2|[Hfrag ≈t]]";
    iDestruct "Ht2'" as "#[Ht2'|[Hfrag' ≈t']]".
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t'" as "#[#≈t' _]".
      by iApply "≈t'".
      done.
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t" as "#[#≈t _]".
      by iApply "≈t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iDestruct "Ht2" as "#[Ht2|[Hfrag ≈t]]";
    iDestruct "Ht2'" as "#[Ht2'|[Hfrag' ≈t']]".
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t'" as "#[#≈t' _]".
      by iApply "≈t'".
      done.
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t" as "#[#≈t _]".
      by iApply "≈t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
- move=> k1 t1 IH.
  case: t2; auto.
  iIntros (k2 t2) "#Ht2".
  case: t2'; auto.
  iIntros (k2' t2') "#Ht2'".
  have IH1: (∀ k2 k2', publicly_related k1 k2 -∗
                       publicly_related k1 k2' -∗
                       ▷ ⌜k2 = k2'⌝).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  have IH2: (∀ t2 t2', publicly_related t1 t2 -∗
                       publicly_related t1 t2' -∗
                       ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  clear IH.
  iDestruct "Ht2" as "#[[Hk2 Ht2]|[Hfrag (≈k & ≈t & #Hrest)]]";
  iDestruct "Ht2'" as "#[[Hk2' Ht2']|[Hfrag' (≈k' & ≈t' & #Hrest')]]".
  + iAssert (▷ ⌜k2 = k2'⌝)%I as "#Hk".
    { by iApply IH1. }
    iAssert (▷ ⌜t2 = t2'⌝)%I as "#Ht".
    { by iApply IH2. }
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k2' = k2⌝)%I as "#Hk".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈k'" as "#[#≈k' _]".
    by iApply "≈k'".
    iAssert (▷ ⌜t2' = t2⌝)%I as "#Ht".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t'" as "#[#≈t' _]".
    by iApply "≈t'".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k2 = k2'⌝)%I as "#Hk".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈k" as "#[#≈k _]".
    by iApply "≈k".
    iAssert (▷ ⌜t2 = t2'⌝)%I as "#Ht".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t" as "#[#≈t _]".
    by iApply "≈t".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- move=> t1 IH.
  case: t2; auto.
  iIntros (t2) "#Ht2".
  case: t2'; auto.
  iIntros (t2') "#Ht2'".
  have {}IH: (∀ t2 t2', publicly_related t1 t2 -∗
                        publicly_related t1 t2' -∗
                        ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  iDestruct "Ht2" as "#[Ht2|[Hfrag ≈t]]";
  iDestruct "Ht2'" as "#[Ht2'|[Hfrag' ≈t']]".
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t'" as "#[#≈t' _]".
    by iApply "≈t'".
    done.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t" as "#[#≈t _]".
    by iApply "≈t".
    done.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- auto.
- case: t2; auto.
Qed.

#[local] Lemma publicly_related_part_bij_2 t1 t1' t2 :
  publicly_related t1 t2 -∗
  publicly_related t1' t2 -∗
  ▷ ⌜t1 = t1'⌝.
Proof.
elim/term_lt_ind: t2 t1 t1' => t2 IH t1 t1'.
rewrite !publicly_related_unfold.
case: t2 IH.
- move=> n2 IH.
  case: t1; auto.
  move=> n1.
  case: t1'; auto.
  move=> n1'.
  iIntros (H1 H2).
  iPureIntro.
  congruence.
- move=> t21 t22 IH.
  case: t1; auto.
  move=> t11 t12.
  case: t1'; auto.
  move=> t1'1 t1'2.
  iIntros "#[H11 H12] #[H1'1 H1'2]".
  iAssert (▷ ⌜t11 = t1'1⌝)%I as ">->".
  { iApply (IH t21). rewrite /tsize /= ssrnat.addnE.
    lia. all: auto. }
  iAssert (▷ ⌜t12 = t1'2⌝)%I as ">->".
  { iApply (IH t22). rewrite /tsize /= ssrnat.addnE.
    lia. all: auto. }
  auto.
- move=> l2 _.
  case: t1; auto.
  iIntros (l1) "#[H1 _]".
  case: t1'; auto.
  iIntros (l1') "#[H1' _]".
  iPoseProof (gset_bij_own_elem_agree with "H1 H1'") as "%H".
  iPureIntro. by apply H.
- move=> kt2 t2 IH.
  case: t1; auto.
  iIntros (kt1 t1) "[-> #Ht1]".
  case: t1'; auto.
  iIntros (kt1' t1') "[-> #Ht1']".
  have {}IH: (∀ t1 t1', publicly_related t1 t2 -∗
                        publicly_related t1' t2 -∗
                        ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  case: kt2.
    iDestruct "Ht1" as "#[Ht2|[Hfrag ≈t]]";
    iDestruct "Ht1'" as "#[Ht2'|[Hfrag' ≈t']]".
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t'" as "#[_ #≈t']".
      by iApply "≈t'".
      done.
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t" as "#[_ #≈t]".
      by iApply "≈t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iDestruct "Ht1" as "#[Ht1|[Hfrag ≈t]]";
    iDestruct "Ht1'" as "#[Ht1'|[Hfrag' ≈t']]".
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t'" as "#[_ #≈t']".
      by iApply "≈t'".
      done.
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      rewrite /double_squiggle /double_squiggle_pre.
      iDestruct "≈t" as "#[_ #≈t]".
      by iApply "≈t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
- move=> k2 t2 IH.
  case: t1; auto.
  iIntros (k1 t1) "#Ht1".
  case: t1'; auto.
  iIntros (k1' t1') "#Ht1'".
  have IH1: (∀ k1 k1', publicly_related k1 k2 -∗
                       publicly_related k1' k2 -∗
                       ▷ ⌜k1 = k1'⌝).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  have IH2: (∀ t1 t1', publicly_related t1 t2 -∗
                       publicly_related t1' t2 -∗
                       ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /= ssrnat.addnE. lia. }
  clear IH.
  iDestruct "Ht1" as "#[[Hk1 Ht1]|[Hfrag (≈k & ≈t & #Hrest)]]";
  iDestruct "Ht1'" as "#[[Hk1' Ht1']|[Hfrag' (≈k' & ≈t' & #Hrest')]]".
  + iAssert (▷ ⌜k1 = k1'⌝)%I as "#Hk".
    { by iApply IH1. }
    iAssert (▷ ⌜t1 = t1'⌝)%I as "#Ht".
    { by iApply IH2. }
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k1' = k1⌝)%I as "#Hk".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈k'" as "#[_ #≈k']".
    by iApply "≈k'".
    iAssert (▷ ⌜t1' = t1⌝)%I as "#Ht".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t'" as "#[_ #≈t']".
    by iApply "≈t'".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k1 = k1'⌝)%I as "#Hk".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈k" as "#[_ #≈k]".
    by iApply "≈k".
    iAssert (▷ ⌜t1 = t1'⌝)%I as "#Ht".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t" as "#[_ #≈t]".
    by iApply "≈t".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- move=> t2 IH.
  case: t1; auto.
  iIntros (t1) "#Ht1".
  case: t1'; auto.
  iIntros (t1') "#Ht1'".
  have {}IH: (∀ t1 t1', publicly_related t1 t2 -∗
                        publicly_related t1' t2 -∗
                        ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  iDestruct "Ht1" as "#[Ht1|[Hfrag ≈t]]";
  iDestruct "Ht1'" as "#[Ht1'|[Hfrag' ≈t']]".
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t'" as "#[_ #≈t']".
    by iApply "≈t'".
    done.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    rewrite /double_squiggle /double_squiggle_pre.
    iDestruct "≈t" as "#[_ #≈t]".
    by iApply "≈t".
    done.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- case: t1; auto.
- case: t1; auto.
Qed.

Lemma publicly_related_part_bij t1 t2 :
  (∀ t2', publicly_related t1 t2 -∗ publicly_related t1 t2' -∗ ▷ ⌜t2 = t2'⌝) ∧
  (∀ t1', publicly_related t1 t2 -∗ publicly_related t1' t2 -∗ ▷ ⌜t1 = t1'⌝).
Proof.
split.
apply publicly_related_part_bij_1.
move=> t1'. apply publicly_related_part_bij_2.
Qed.

End Rel.

Lemma public_relGS_alloc `{!relocG Σ} E :
  public_relGpreS Σ →
  ⊢ |={E}=> ∃ (H : public_relGS Σ),
              public_rel_ctx.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod term_meta_specGS_alloc as "[% #?]".
iMod (gset_bij_own_alloc_empty (A:=term) (B:=term)) as "[%γ Hauth]".
pose (Hpub := Public_relGS _ _ _ _ γ).
iExists Hpub.
iMod (inv_alloc cryptisN _ (∃ pub, public_rel_inv pub)%I with "[Hauth]") as "#Hinv".
{ iFrame. by rewrite big_sepS_empty. }
by iFrame "#".
Qed.

From stdpp Require Import sets.
From iris.algebra Require Import auth cmra ofe gmap local_updates.
From iris.base_logic.lib Require Import own ghost_map.
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

Inductive state :=
  | Private (ts : gset term)
  | Public (t : term)
  | Invalid.

Section cmra.

  Context {SI : sidx}.

  Canonical Structure stateO := leibnizO state.

  #[global] Instance stateO_discrete : OfeDiscrete state.
  Proof. apply _. Qed.

  #[local] Instance state_op_instance : Op state := λ s1 s2,
    match s1, s2 with
    | Private ts1, Private ts2 => Private (ts1 ∪ ts2)
    | Private ts, Public t | Public t, Private ts =>
      if bool_decide (ts ⊆ {[ t ]}) then Public t else Invalid
    | Public t1, Public t2 =>
      if bool_decide (t1 = t2) then Public t1 else Invalid
    | _, _ => Invalid
    end.

  #[local] Instance state_pcore_instance : PCore state := Some.

  #[local] Instance state_valid_instance : Valid state := λ s,
    match s with
    | Invalid => False
    | _ => True
    end.

  #[local] Instance state_unit_instance : Unit state := Private ∅.

  Lemma state_ra_mixin : RAMixin state.
  Proof.
  split.
  - solve_proper.
  - naive_solver.
  - solve_proper.
  - intros [] [] [];
    rewrite /op /state_op_instance;
    repeat case_bool_decide;
    try (f_equiv; set_solver);
    try (exfalso; set_solver).
  - intros [] [];
    rewrite /op /state_op_instance;
    repeat case_bool_decide; simplify_eq;
    f_equiv; set_solver.
  - intros [] ? [= <-];
    rewrite /op /state_op_instance;
    repeat case_bool_decide; simplify_eq;
    f_equiv; set_solver.
  - by move=> [] [].
  - rewrite /pcore /state_pcore_instance.
    move=> ? ? ? ? H.
    apply Some_inj in H as ->; eauto.
  - by move=> [] [].
  Qed.

  Lemma state_ucmra_mixin : UcmraMixin state.
  Proof.
  split=> //.
  intros s.
  change (ε ⋅ s) with (state_op_instance ε s).
  case: s => [ts|t|] //=.
  + f_equiv; set_solver.
  + case_bool_decide=> //; set_solver.
  Qed.

  Canonical Structure stateR := discreteR state state_ra_mixin.
  Canonical Structure stateUR := Ucmra state state_ucmra_mixin.

  #[global] Instance stateR_discrete : CmraDiscrete stateR.
  Proof. by split; first apply _. Qed.

  #[global] Instance state_core_id (s : state) : CoreId s.
  Proof. by constructor. Qed.

End cmra.

Section lemmas.

  Context {SI : sidx}.

  Lemma state_local_update_grow ts t :
  (● Private ts ⋅ ◯ Private ts, ● Private ts ⋅ ◯ Private ts) ~l~>
  (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]}), ● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]})).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq=> [[ts1|t1|]|] //= Hval Heq.
  - change (Private ts ⋅ Private ts1) with (state_op_instance (Private ts) (Private ts1)) in Heq.
    change (Private (ts ∪ {[ t ]}) ⋅ Private ts1) with (state_op_instance (Private (ts ∪ {[ t ]})) (Private ts1)).
    simpl in *. f_equal. set_solver.
  - change (Private ts ⋅ Public t1) with (state_op_instance (Private ts) (Public t1)) in Heq.
    simpl in Heq.
    by case_bool_decide.
  Qed.

  Lemma state_local_update_lock t :
    (● Private {[ t ]} ⋅ ◯ Private {[ t ]}, ● Private {[ t ]} ⋅ ◯ Private {[ t ]}) ~l~>
    (● Public t ⋅ ◯ Public t, ● Public t ⋅ ◯ Public t).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq=> [[ts1|t1|]|] //= Hval Heq.
  - change (Private {[ t ]} ⋅ Private ts1) with (state_op_instance (Private {[ t ]}) (Private ts1)) in Heq.
    change (Public t ⋅ Private ts1) with (state_op_instance (Public t) (Private ts1)).
    simpl in *. injection Heq as Heq.
    case_bool_decide; set_solver.
  - change (Private {[ t ]} ⋅ Public t1) with (state_op_instance (Private {[ t ]}) (Public t1)) in Heq.
    simpl in Heq.
    by case_bool_decide.
  Qed.

  Lemma state_core_id_local_update (st : state) :
    (● st ⋅ ◯ st, ● st) ~l~>
    (● st ⋅ ◯ st, ● st ⋅ ◯ st).
  Proof.
  apply core_id_local_update; first apply _.
  by rewrite auth_frag_included.
  Qed.

End lemmas.

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_maps :: inG Σ (authUR (gmapUR term (authUR stateUR)));
  #[local] public_relGpreS_flow :: ghost_mapG Σ term (gset term);
  #[local] public_relGpreS_term_meta :: term_metaGpreS Σ;
  #[local] public_relGpreS_prop :: savedPropG Σ;
}.

Class public_relGS Σ := Public_relGS {
  #[global] maps_inG :: inG Σ (authUR (gmapUR term (authUR stateUR)));
  #[global] flow_inG :: ghost_mapG Σ term (gset term);
  #[global] term_meta_inG :: term_metaGS Σ;
  #[global] term_meta_spec_inG :: term_meta_specGS Σ;
  #[global] prop_inG :: savedPropG Σ;
  public_rel_map_l : gname;
  public_rel_map_r : gname;
  public_rel_flow_l : gname;
  public_rel_flow_r : gname;
}.

Definition public_relΣ : gFunctors :=
  #[GFunctor (authUR (gmapUR term (authUR stateUR)));
    ghost_mapΣ term (gset term);
    term_metaΣ;
    savedPropΣ].

#[global] Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Definition public_rel_map_l_auth pub_l : iProp :=
    own public_rel_map_l (● (@fmap (gmap term) _ _ _ (λ st, ● st ⋅ ◯ st) pub_l)) ∗
    [∗ map] t ↦ st ∈ pub_l, match st with
                              | Private _ => own public_rel_map_l (◯ {[ t := ●{#1/2} st ]})
                              | _ => emp
                              end.

Definition public_rel_map_r_auth pub_r : iProp :=
  own public_rel_map_r (● (@fmap (gmap term) _ _ _ (λ st, ● st ⋅ ◯ st) pub_r)) ∗
  [∗ map] t' ↦ st ∈ pub_r, match st with
                            | Private _ => own public_rel_map_r (◯ {[ t' := ●{#1/2} st ]})
                            | _ => emp
                            end.

Definition public_rel_map_l_elem t t': iProp :=
  own public_rel_map_l (◯ {[ t := ◯ (Private {[ t' ]}) ]}).

#[global] Instance public_rel_map_l_elem_persistent t t' : Persistent (public_rel_map_l_elem t t').
Proof. apply _. Qed.

Definition public_rel_map_l_locked t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ (Public t') ]}).

#[global] Instance public_rel_map_l_locked_persistent t t' : Persistent (public_rel_map_l_locked t t').
Proof. apply _. Qed.

Definition private_rel_elem_l t t' : iProp :=
  public_rel_map_l_elem t t' ∨ public_rel_map_l_locked t t'.

Definition public_rel_map_r_elem t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ (Private {[ t ]}) ]}).

#[global] Instance public_rel_map_r_elem_persistent t t' : Persistent (public_rel_map_r_elem t t').
Proof. apply _. Qed.

Definition public_rel_map_r_locked t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ (Public t) ]}).

#[global] Instance public_rel_map_r_locked_persistent t t' : Persistent (public_rel_map_r_locked t t').
Proof. apply _. Qed.

Definition private_rel_elem_r t t' : iProp :=
  public_rel_map_r_elem t t' ∨ public_rel_map_r_locked t t'.

Definition private_rel_elem t t' : iProp :=
  private_rel_elem_l t t' ∧ private_rel_elem_r t t'.

#[global] Instance private_rel_elem_persistent t t' : Persistent (private_rel_elem t t').
Proof. apply _. Qed.

Definition public_rel_elem t t' : iProp :=
  public_rel_map_l_locked t t' ∧ public_rel_map_r_locked t t'.

Lemma public_rel_elem_private_rel_elem t t' :
  public_rel_elem t t' -∗
  private_rel_elem t t'.
Proof.
iIntros "#[? ?]".
rewrite /private_rel_elem /private_rel_elem_l /private_rel_elem_r.
eauto.
Qed.

#[global] Instance public_rel_elem_persistent t t' : Persistent (public_rel_elem t t').
Proof. apply _. Qed.

Inductive is_immediate_subterm : term → term → Prop :=
  | SubtermPairL t1 t2 : is_immediate_subterm t1 (TPair t1 t2)
  | SubtermPairR t1 t2 : is_immediate_subterm t2 (TPair t1 t2)
  | SubtermKey kt t1 : is_immediate_subterm t1 (TKey kt t1)
  | SubtermSealKey k t1 : is_immediate_subterm k (TSeal k t1)
  | SubtermSealBody k t1 : is_immediate_subterm t1 (TSeal k t1)
  | SubtermHash t1 : is_immediate_subterm t1 (THash t1).

Definition public_rel_flow_l_auth flow_l : iProp :=
  ghost_map_auth public_rel_flow_l 1 flow_l ∗
  [∗ map] t ↦ ts ∈ flow_l,
    t ↪[public_rel_flow_l]{#1/2} ts ∗
    ([∗ set] t1 ∈ ts, ⌜is_immediate_subterm t t1⌝) ∗
    ⌜(∃ a, t = TNonce a) ∨ (∃ t1 ts1, flow_l !! t1 = Some ts1 ∧ t ∈ ts1)⌝.

Definition public_rel_flow_r_auth flow_r : iProp :=
  ghost_map_auth public_rel_flow_r 1 flow_r ∗
  [∗ map] t' ↦ ts ∈ flow_r,
    t' ↪[public_rel_flow_r]{#1/2} ts ∗
    ([∗ set] t1' ∈ ts, ⌜is_immediate_subterm t' t1'⌝) ∗
    ⌜ts ≠ ∅ → (∃ a', t' = TNonce a') ∨ (∃ t1' ts1, flow_r !! t1' = Some ts1 ∧ t' ∈ ts1)⌝.

Lemma public_rel_map_l_t_st pub_l t (st : state) :
  own public_rel_map_l (● ((λ st : state, ● st ⋅ ◯ st) <$> pub_l)) -∗
  own public_rel_map_l (◯ {[ t := ●{#1/2} st ]}) -∗
  ⌜pub_l !! t = Some st⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_l !! t) as [st'|] eqn:Heq.
- assert (●{#1 / 2} st ≼ ● st' ⋅ ◯ st') as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  by apply auth_auth_dfrac_included in H as [_ ->].
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Lemma public_rel_map_r_t'_st pub_r t' (st : state) :
  own public_rel_map_r (● ((λ st : state, ● st ⋅ ◯ st) <$> pub_r)) -∗
  own public_rel_map_r (◯ {[ t' := ●{#1/2} st ]}) -∗
  ⌜pub_r !! t' = Some st⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_r !! t') as [st'|] eqn:Heq.
- assert (●{#1 / 2} st ≼ ● st' ⋅ ◯ st') as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  by apply auth_auth_dfrac_included in H as [_ ->].
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Fixpoint publicly_related t t' : iProp :=
  match t, t' with
  | TInt n, TInt n' => ⌜n = n'⌝
  | TPair t1 t2, TPair t1' t2' =>
      publicly_related t1 t1' ∧ publicly_related t2 t2'
  | TNonce a, TNonce a' => public_rel_elem t t'
  | TKey kt t1, TKey kt' t1' => ⌜kt = kt'⌝ ∧
    match kt with
    | AEnc => publicly_related t1 t1' ∨
              (public_rel_elem t t' ∧ private_rel_elem t1 t1')
    | ADec => publicly_related t1 t1'
    | Sign => publicly_related t1 t1'
    | Verify => publicly_related t1 t1' ∨
                (public_rel_elem t t' ∧ private_rel_elem t1 t1')
    | SEnc => publicly_related t1 t1'
    end
  | TSeal k t1, TSeal k' t1' =>
    (publicly_related k k' ∧ publicly_related t1 t1') ∨
    (public_rel_elem t t' ∧ private_rel_elem k k' ∧ private_rel_elem t1 t1' ∧
    □ (match k, k' with
      | TKey kt k1, TKey kt' k1' => ⌜kt = kt'⌝ ∧
        match kt with
        | ADec | Verify => False
        | Sign => publicly_related t1 t1'
        | AEnc | SEnc => publicly_related k1 k1' → publicly_related t1 t1'
        end
      | _, _ => False
      end))
  | THash t1, THash t1' =>
    publicly_related t1 t1' ∨
    (public_rel_elem t t' ∧ private_rel_elem t1 t1')
  | _, _ =>
      False (* WIP *)
  end.

#[local] Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 20, no associativity, format "PUB⟨ a , b ⟩").

Definition public_rel_inv pub_l pub_r flow_l flow_r : iProp :=
  public_rel_map_l_auth pub_l ∗
  public_rel_map_r_auth pub_r ∗
  public_rel_flow_l_auth flow_l ∗
  public_rel_flow_r_auth flow_r ∗
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) ∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()) ∗
  ([∗ set] t ∈ dom flow_l, term_meta t (cryptisN.@"public_rel".@"flow") ()) ∗
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()) ∗
  ⌜∀ t t', pub_l !! t = Some (Public t') ↔ pub_r !! t' = Some (Public t)⌝ ∗
  (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → publicly_related t t') ∗
  ⌜∀ t ts, pub_l !! t = Some (Private ts) → (∃ a, t = TNonce a) ∨ (∃ t1 ts1, flow_l !! t1 = Some ts1 ∧ t ∈ ts1)⌝ ∗
  ⌜∀ t' ts, pub_r !! t' = Some (Private ts) → (∃ a', t' = TNonce a') ∨ (∃ t1' ts1, flow_r !! t1' = Some ts1 ∧ t' ∈ ts1)⌝ ∗
  ⌜∀ t ts, flow_l !! t = Some ts → (pub_l !! t = None) ∨ (∃ ts1, pub_l !! t = Some (Private ts1))⌝ ∗
  ⌜∀ t' ts, flow_r !! t' = Some ts → (pub_r !! t' = None) ∨ (∃ ts1, pub_r !! t' = Some (Private ts1))⌝.

Definition public_rel_ctx : iProp :=
  inv cryptisN (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r).

Definition cryptis_rel_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_rel_ctx.

#[global] Instance cryptis_rel_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance cryptis_rel_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

Lemma public_rel_map_l_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem_l t t' ∗
          own public_rel_map_l (◯ {[ t := ●{#1/2} (Private {[ t' ]}) ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & [Hauth_l Hauth_l_frag] & Hauth_r &
                  #Hmeta_l & #Hmeta_r & %Hlock)".
iAssert (⌜pub_l !! t = None⌝)%I as "%Hfresh".
{ destruct (pub_l !! t) eqn:Heq; last eauto.
  iDestruct (big_sepS_elem_of _ _ t with "Hmeta_l") as "Hmeta"; first by apply elem_of_dom.
  iDestruct (term_meta_token with "Htt Hmeta") as "[]"=> //. }
iMod (own_update with "Hauth_l") as "[Hauth_l Hfrag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (Private {[ t' ]}) ⋅ ◯ (Private {[ t' ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hfrag_t" as "[[Hauth_t_frag Hauth_t_frag'] Hfrag_t]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_t"=> //.
iModIntro. iSplitR "Hfrag_t Hauth_t_frag'"; last by iFrame. iModIntro.
iExists (<[t := Private {[ t' ]}]> pub_l), pub_r.
iFrame. iFrame "#".
iSplitL; last iSplit; last (iIntros (t1 t1'); iPureIntro; split).
- rewrite /public_rel_map_l_auth fmap_insert.
  rewrite big_sepM_insert=> //.
  iFrame.
- rewrite dom_insert_L.
  rewrite big_sepS_insert; last by apply not_elem_of_dom.
  iFrame "#".
- move=> Hlookup.
  apply lookup_insert_Some in Hlookup as [[-> ?] | [_ ?]]=> //.
  by apply Hlock.
- move=> Hlookup.
  apply Hlock in Hlookup.
  destruct (decide (t = t1)) as [-> | ?].
  - by rewrite Hfresh in Hlookup.
  - by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_map_r_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem_r t t' ∗
          own public_rel_map_r (◯ {[ t' := ●{#1/2} (Private {[ t ]}) ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & Hauth_l & [Hauth_r Hauth_r_frag] &
                  #Hmeta_l & #Hmeta_r & %Hlock)".
iAssert (⌜pub_r !! t' = None⌝)%I as "%Hfresh".
{ destruct (pub_r !! t') eqn:Heq; last eauto.
  iDestruct (big_sepS_elem_of _ _ t' with "Hmeta_r") as "Hmeta"; first by apply elem_of_dom.
  iDestruct (term_meta_spec_token with "Htts Hmeta") as "[]"=> //. }
iMod (own_update with "Hauth_r") as "[Hauth_r Hfrag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (Private {[ t ]}) ⋅ ◯ (Private {[ t ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hfrag_t'" as "[[Hauth_t'_frag Hauth_t'_frag'] Hfrag_t']".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_t'"=> //.
iModIntro. iSplitR "Hfrag_t' Hauth_t'_frag'"; last by iFrame. iModIntro.
iExists pub_l, (<[t' := Private {[ t ]}]> pub_r).
iFrame. iFrame "#".
iSplitL; last iSplit; last (iIntros (t1 t1'); iPureIntro; split).
- rewrite /public_rel_map_r_auth fmap_insert.
  rewrite big_sepM_insert=> //.
  iFrame.
- rewrite dom_insert_L.
  rewrite big_sepS_insert; last by apply not_elem_of_dom.
  iFrame "#".
- move=> Hlookup.
  apply Hlock in Hlookup.
  destruct (decide (t' = t1')) as [-> | ?].
  - by rewrite Hfresh in Hlookup.
  - by rewrite lookup_insert_ne.
- move=> Hlookup.
  apply lookup_insert_Some in Hlookup as [[-> ?] | [_ ?]]=> //.
  by apply Hlock.
Qed.

Lemma private_rel_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem t t' ∗
          own public_rel_map_l (◯ {[ t := ●{#1/2} (Private {[ t' ]}) ]}) ∗
          own public_rel_map_r (◯ {[ t' := ●{#1/2} (Private {[ t ]}) ]}).
Proof.
iIntros (HE) "#Hctx Htt Htts".
iPoseProof (public_rel_map_l_extend t t' with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_rel_map_r_extend t t' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /private_rel_elem.
by iFrame.
Qed.

Lemma public_rel_map_l_grow E t ts t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  own public_rel_map_l (◯ {[ t := ●{#1/2} (Private ts) ]}) -∗
  |={E}=> private_rel_elem_l t t' ∗
          own public_rel_map_l (◯ {[ t := ●{#1/2} (Private (ts ∪ {[ t' ]})) ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & [Hauth_l Hauth_l_frag] & Hauth_r & #Hmeta_l & #Hmeta_r & %Hlock)".
iPoseProof (public_rel_map_l_t_st with "Hauth_l Hl_frac") as "%Hltt'".
iDestruct (big_sepM_delete _ _ t _ Hltt' with "Hauth_l_frag") as "[Hl_frac2 Hauth_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hauth_l Hl") as "[Hauth_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Private (ts ∪ {[ t' ]}) ⋅ ◯ Private (ts ∪ {[ t' ]}))
    (● Private (ts ∪ {[ t' ]}) ⋅ ◯ Private (ts ∪ {[ t' ]})));
    first by rewrite lookup_fmap Hltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_grow. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] #Hl']".
iAssert (own public_rel_map_l (◯ {[ t := ◯ Private {[ t' ]} ]})) as "Hl".
{ assert (Private (ts ∪ {[t']}) = Private ts ⋅ Private {[t']}) as -> by done.
  by iDestruct "Hl'" as "[_ Hl']". }
iModIntro. iSplitR "Hl_frac2"; last by iFrame; iFrame "#".
iModIntro.
iExists (<[t := Private (ts ∪ {[ t' ]})]> pub_l), pub_r.
rewrite /public_rel_inv /public_rel_map_l_auth.
iAssert ([∗ map] k ↦ y ∈ {[ t := Private (ts ∪ {[ t' ]})]}, match y with
    | Private _ => own public_rel_map_l (◯ {[ k := ●{#1/2} y]})
    | _ => emp
    end)%I with "[Hl_frac]" as "Hl_frac".
{ by rewrite big_sepM_singleton. }
iCombine "Hauth_l_frag Hl_frac" as "Hauth_l_frag".
rewrite -big_sepM_union; last by apply map_disjoint_singleton_r, lookup_delete_eq.
rewrite -insert_union_singleton_r; last by apply lookup_delete_eq.
rewrite insert_delete_eq.
rewrite fmap_insert.
rewrite dom_insert_lookup_L=> //.
iFrame. iFrame "#".
iPureIntro.
intros t1 t1'.
destruct (decide (t = t1)) as [->|?];
  destruct (decide (t' = t1')) as [->|?];
  rewrite ?lookup_insert_eq ?lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_map_r_grow E t ts t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  own public_rel_map_r (◯ {[ t' := ●{#1/2} (Private ts) ]}) -∗
  |={E}=> private_rel_elem_r t t' ∗
          own public_rel_map_r (◯ {[ t' := ●{#1/2} (Private (ts ∪ {[ t ]})) ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & Hauth_l & [Hauth_r Hauth_r_frag] & #Hmeta_l & #Hmeta_r & %Hlock)".
iPoseProof (public_rel_map_r_t'_st with "Hauth_r Hr_frac") as "%Hrtt'".
iDestruct (big_sepM_delete _ _ t' _ Hrtt' with "Hauth_r_frag") as "[Hr_frac2 Hauth_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hauth_r Hr") as "[Hauth_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]}))
    (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]})));
    first by rewrite lookup_fmap Hrtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_grow. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] #Hr']".
iAssert (own public_rel_map_r (◯ {[ t' := ◯ Private {[ t ]} ]})) as "Hl".
{ assert (Private (ts ∪ {[t]}) = Private ts ⋅ Private {[t]}) as -> by done.
  by iDestruct "Hr'" as "[_ Hr']". }
iModIntro. iSplitR "Hr_frac2"; last by iFrame; iFrame "#".
iModIntro.
iExists pub_l, (<[t' := Private (ts ∪ {[ t ]})]> pub_r).
rewrite /public_rel_inv /public_rel_map_r_auth.
iAssert ([∗ map] k ↦ y ∈ {[ t' := Private (ts ∪ {[ t ]})]}, match y with
    | Private _ => own public_rel_map_r (◯ {[ k := ●{#1/2} y]})
    | _ => emp
    end)%I with "[Hr_frac]" as "Hr_frac".
{ by rewrite big_sepM_singleton. }
iCombine "Hauth_r_frag Hr_frac" as "Hauth_r_frag".
rewrite -big_sepM_union; last by apply map_disjoint_singleton_r, lookup_delete_eq.
rewrite -insert_union_singleton_r; last by apply lookup_delete_eq.
rewrite insert_delete_eq.
rewrite fmap_insert.
rewrite dom_insert_lookup_L=> //.
iFrame. iFrame "#".
iPureIntro.
intros t1 t1'.
destruct (decide (t = t1)) as [->|?];
  destruct (decide (t' = t1')) as [->|?];
  rewrite ?lookup_insert_eq ?lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  own public_rel_map_l (◯ {[ t := ●{#1/2} (Private {[ t' ]}) ]}) -∗
  own public_rel_map_r (◯ {[ t' := ●{#1/2} (Private {[ t ]}) ]}) -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & [Hauth_l Hauth_l_frag] & [Hauth_r Hauth_r_frag] & #Hmeta_l & #Hmeta_r & %Hlock)".
iPoseProof (public_rel_map_l_t_st with "Hauth_l Hl_frac") as "%Hltt'".
iPoseProof (public_rel_map_r_t'_st with "Hauth_r Hr_frac") as "%Hrtt'".
iDestruct (big_sepM_delete _ _ t _ Hltt' with "Hauth_l_frag") as "[Hl_frac2 Hauth_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hrtt' with "Hauth_r_frag") as "[Hr_frac2 Hauth_r_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hauth_l Hl") as "[Hauth_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t') ⋅ ◯ (Public t'))
    (● (Public t') ⋅ ◯ (Public t'))); first by rewrite lookup_fmap Hltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
iMod (own_update_2 with "Hauth_r Hr") as "[Hauth_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t) ⋅ ◯ (Public t))
    (● (Public t) ⋅ ◯ (Public t))); first by rewrite lookup_fmap Hrtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro.
iExists (<[t := Public t']> pub_l), (<[t' := Public t]> pub_r).
rewrite /public_rel_inv /public_rel_map_l_auth /public_rel_map_r_auth.
rewrite !fmap_insert !big_sepM_insert_delete.
rewrite !dom_insert_lookup_L=> //.
iFrame. iFrame "#".
iPureIntro.
intros t1 t1'.
destruct (decide (t = t1)) as [->|?];
  destruct (decide (t' = t1')) as [->|?];
  rewrite ?lookup_insert_eq ?lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_extend_2 E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#Hctx Htt Htts".
iPoseProof (private_rel_extend with "[] Htt Htts") as ">(_ & Hl & Hr)"=> //.
by iApply (public_rel_extend with "[] Hl Hr").
Qed.

Definition publicly_related_later_pre P : term -d> term -d> iProp := λ t1 t2,
  (□ (∀ t2', ▷ P t1 t2' -∗ ▷ ⌜t2 = t2'⌝) ∧
  □ (∀ t1', ▷ P t1' t2 -∗ ▷ ⌜t1 = t1'⌝))%I.

#[local] Instance publicly_related_later_pre_persistent P t1 t2 : Persistent (publicly_related_later_pre P t1 t2).
Proof. apply _. Qed.

Definition publicly_related_pre P : term -d> term -d> iProp :=
  fix publicly_related_pre t1 t2 {struct t1} : iProp :=
  (minted t1 ∧ minted_spec t2 ∧
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      publicly_related_pre t11 t21 ∧ publicly_related_pre t12 t22
  | TNonce l1, TNonce l2 => public_rel_elem t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => publicly_related_pre t1' t2' ∨
              (public_rel_elem t1 t2 ∧ publicly_related_later_pre P t1' t2')
    | ADec => publicly_related_pre t1' t2'
    | Sign => publicly_related_pre t1' t2'
    | Verify => publicly_related_pre t1' t2' ∨
                (public_rel_elem t1 t2 ∧ publicly_related_later_pre P t1' t2')
    | SEnc => publicly_related_pre t1' t2'
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (publicly_related_pre k1 k2 ∧ publicly_related_pre t1' t2') ∨
    (public_rel_elem t1 t2 ∧ publicly_related_later_pre P k1 k2 ∧ publicly_related_later_pre P t1' t2' ∧
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
    (public_rel_elem t1 t2 ∧ publicly_related_later_pre P t1' t2')
  | _, _ =>
      False (* WIP *)
  end)%I.

#[local] Instance publicly_related_pre_persistent P t1 t2 : Persistent (publicly_related_pre P t1 t2).
Proof.
elim/term_lt_ind: t1 t2 => // -[] //=.
- move=> ? ? [] *; apply _.
- move=> t11 t12 IH []; try apply _.
  move=> t21 t22.
  have IH1: Persistent (publicly_related_pre P t11 t21).
  { apply IH. rewrite /tsize /=. lia. }
  have IH2: Persistent (publicly_related_pre P t12 t22).
  { apply IH. rewrite /tsize /=. lia. }
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
  { apply IH. rewrite /tsize /=. lia. }
  have IH2: Persistent (publicly_related_pre P t1' t2').
  { apply IH. rewrite /tsize /=. lia. }
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
    f_equiv; f_equiv; f_equiv; apply: IH; rewrite /=; lia.
  - move=> kt1 t1' IH [] //= kt2 t2'.
    rewrite /tsize in IH.
    f_equiv; f_equiv; f_equiv.
    have {}IH: ∀ t2, publicly_related_pre P t1' t2 ≡{n}≡ publicly_related_pre P' t1' t2.
    { apply: IH. simpl. lia. }
    case: kt1 => //=.
    + f_equiv; first done.
      f_equiv; solve_contractive.
    + f_equiv; first done.
      f_equiv; solve_contractive.
  - move=> k1 t1' IH [] //= k2 t2'.
    rewrite /tsize in IH; f_equiv; f_equiv; f_equiv.
    + f_equiv; apply: IH; rewrite /=; lia.
    + f_equiv.
      f_equiv. solve_contractive.
      f_equiv. solve_contractive.
      f_equiv.
      case: k1 => //= kt1 k1 in IH*.
      case: k2 => //= kt2 k2.
      f_equiv.
      have IH1: publicly_related_pre P t1' t2' ≡{n}≡ publicly_related_pre P' t1' t2'.
      { apply: IH. rewrite /=. lia. }
      have IH2: publicly_related_pre P k1 k2 ≡{n}≡ publicly_related_pre P' k1 k2.
      { apply: IH. rewrite /=. lia. }
      case: kt1 => //=; by f_equiv.
  - move=> t1' IH [] //= t2'.
    rewrite /tsize in IH.
    have {}IH: publicly_related_pre P t1' t2' ≡{n}≡ publicly_related_pre P' t1' t2'.
    { apply IH. simpl. lia. }
    f_equiv; f_equiv; f_equiv. solve_contractive.
    f_equiv. solve_contractive.
Qed.

#[local] Definition publicly_related_def : lrelO :=
  fixpoint (publicly_related_pre).
#[local] Definition publicly_related_aux : seal publicly_related_def. Proof. by eexists. Qed.
Definition publicly_related := publicly_related_aux.(unseal).
#[local] Lemma publicly_related_unseal : publicly_related = publicly_related_def.
Proof. rewrite -publicly_related_aux.(seal_eq) //. Qed.

Definition publicly_related_later := publicly_related_later_pre publicly_related.

#[local] Notation "PUB▷⟨ a , b ⟩" := (publicly_related_later a b)
  (at level 70, no associativity, format "PUB▷⟨ a , b ⟩").
#[local] Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 70, no associativity, format "PUB⟨ a , b ⟩").

Lemma publicly_related_unfold :
  ∀ t1 t2, PUB⟨t1, t2⟩ ⊣⊢
  minted t1 ∧ minted_spec t2 ∧
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 => PUB⟨t11, t21⟩ ∧ PUB⟨t12, t22⟩
  | TNonce l1, TNonce l2 => public_rel_elem t1 t2 ∧ ◇ pnonce_rel t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => PUB⟨t1', t2'⟩ ∨ (public_rel_elem t1 t2 ∧ PUB▷⟨t1', t2'⟩)
    | ADec => PUB⟨t1', t2'⟩
    | Sign => PUB⟨t1', t2'⟩
    | Verify => PUB⟨t1', t2'⟩ ∨ (public_rel_elem t1 t2 ∧ PUB▷⟨t1', t2'⟩)
    | SEnc => PUB⟨t1', t2'⟩
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (PUB⟨k1, k2⟩ ∧ PUB⟨t1', t2'⟩) ∨
    (public_rel_elem t1 t2 ∧ PUB▷⟨k1, k2⟩ ∧ PUB▷⟨t1', t2'⟩ ∧
    □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | ADec | Verify => False
        | Sign => PUB⟨t1', t2'⟩
        | _ => PUB⟨k1, k2⟩ → PUB⟨t1', t2'⟩
        end
      | _, _ => False
      end))
  | THash t1', THash t2' => PUB⟨t1', t2'⟩ ∨ (public_rel_elem t1 t2 ∧ PUB▷⟨t1', t2'⟩)
  | _, _ => False (* WIP *)
  end.
Proof.
  rewrite /publicly_related_later publicly_related_unseal /publicly_related_def => t1 t2.
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

#[global] Instance publicly_related_persistent t1 t2 : Persistent (PUB⟨t1, t2⟩).
Proof.
  rewrite /publicly_related_later publicly_related_unseal /publicly_related_def.
  rewrite (fixpoint_unfold publicly_related_pre t1 t2).
  apply _.
Qed.

Lemma publicly_related_minted t t' :
  PUB⟨t, t'⟩ ⊢ minted t ∗ minted_spec t'.
Proof.
rewrite publicly_related_unfold.
iIntros "(? & ? & _)". eauto.
Qed.

Lemma publicly_related_TInt n1 n2 :
  PUB⟨TInt n1, TInt n2⟩ ⊣⊢ ⌜n1 = n2⌝.
Proof.
rewrite publicly_related_unfold minted_TInt minted_spec_TInt.
by rewrite !left_id.
Qed.

Lemma publicly_related_TInt_term n (t2 : term) :
  PUB⟨TInt n, t2⟩ -∗ ⌜t2 = TInt n⌝.
Proof.
rewrite publicly_related_unfold.
iIntros "(_ & _ & H)". case: t2; eauto.
iIntros (?). by iDestruct "H" as "->".
Qed.

Lemma publicly_related_term_TInt (t1 : term) n :
  PUB⟨t1, TInt n⟩ -∗ ⌜t1 = TInt n⌝.
Proof.
rewrite publicly_related_unfold.
iIntros "(_ & _ & H)". case: t1; eauto.
iIntros (?). by iDestruct "H" as "->".
Qed.

Lemma publicly_related_TPair t11 t12 t21 t22 :
  PUB⟨TPair t11 t12, TPair t21 t22⟩ ⊣⊢
  PUB⟨t11, t21⟩ ∧ PUB⟨t12, t22⟩.
Proof.
rewrite publicly_related_unfold. iSplit.
- iIntros "(_ & _ & ?)". eauto.
- iIntros "(#H1 & #H2)". iSplit; last iSplit; last eauto.
  + iPoseProof (publicly_related_minted with "H1") as "(? & _)".
    iPoseProof (publicly_related_minted with "H2") as "(? & _)".
    rewrite minted_TPair. eauto.
  + iPoseProof (publicly_related_minted with "H1") as "(_ & ?)".
    iPoseProof (publicly_related_minted with "H2") as "(_ & ?)".
    rewrite minted_spec_TPair. eauto.
Qed.

Lemma publicly_related_TPair_term t11 t12 (t2 : term) :
  PUB⟨TPair t11 t12, t2⟩ -∗
  ∃ t21 t22, ⌜t2 = TPair t21 t22⌝.
Proof.
rewrite publicly_related_unfold.
iIntros "(_ & _ & ?)". case: t2; eauto.
Qed.

Lemma publicly_related_term_TPair (t1 : term) t21 t22 :
  PUB⟨t1, TPair t21 t22⟩ -∗
  ∃ t11 t12, ⌜t1 = TPair t11 t12⌝.
Proof.
rewrite publicly_related_unfold.
iIntros "(_ & _ & ?)". case: t1; eauto.
Qed.

Lemma publicly_related_TNonce a1 a2 :
  PUB⟨TNonce a1, TNonce a2⟩ ⊣⊢
  minted a1 ∧ minted_spec a2 ∧
    public_rel_elem a1 a2 ∧ ◇ pnonce_rel a1 a2.
Proof. by rewrite publicly_related_unfold. Qed.

Lemma publicly_related_TKey kt1 kt2 t1 t2 :
  PUB⟨TKey kt1 t1, TKey kt2 t2⟩ ⊣⊢
  ⌜kt1 = kt2⌝ ∧
  match kt1 with
  | AEnc => PUB⟨t1, t2⟩ ∨
            (minted t1 ∧ minted_spec t2 ∧
              public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ PUB▷⟨t1, t2⟩)
  | ADec => PUB⟨t1, t2⟩
  | Sign => PUB⟨t1, t2⟩
  | Verify => PUB⟨t1, t2⟩ ∨
              (minted t1 ∧ minted_spec t2 ∧
                public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ PUB▷⟨t1, t2⟩)
  | SEnc => PUB⟨t1, t2⟩
  end.
Proof.
rewrite publicly_related_unfold. iSplit.
- iIntros "#(? & ? & -> & H)". iSplit=> //.
  rewrite minted_TKey. rewrite minted_spec_TKey.
  case: kt2=> //; iDestruct "H" as "[H | H]"; eauto.
- iIntros "#(-> & H)". iSplit; last iSplit; last eauto.
  + rewrite minted_TKey.
    case: kt2; rewrite publicly_related_minted;
    try (iDestruct "H" as "[H _]"; eauto);
    try (iDestruct "H" as "[[H _]|[H _]]"; eauto).
  + rewrite minted_spec_TKey.
    case: kt2; rewrite publicly_related_minted;
    try (iDestruct "H" as "[_ ?]"; eauto);
    try (iDestruct "H" as "[[_ ?]|[_ [? _]]]"; eauto).
  + iSplit=> //. case: kt2=> //;
    iDestruct "H" as "[?|(_ & _ & ?)]"; eauto.
Qed.

Lemma publicly_related_TSeal k1 k2 t1 t2 :
  PUB⟨TSeal k1 t1, TSeal k2 t2⟩ ⊣⊢
  (PUB⟨k1, k2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (minted (TSeal k1 t1) ∧ minted_spec (TSeal k2 t2) ∧
    public_rel_elem (TSeal k1 t1) (TSeal k2 t2) ∧
    PUB▷⟨k1, k2⟩ ∧ PUB▷⟨t1, t2⟩ ∧
    □ (match k1, k2 with
        | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
          match kt1 with
          | ADec | Verify => False
          | Sign => PUB⟨t1, t2⟩
          | _ => PUB⟨k1, k2⟩ → PUB⟨t1, t2⟩
          end
        | _, _ => False
        end)).
Proof.
rewrite publicly_related_unfold. iSplit.
- iIntros "#(? & ? & [?|?])"; eauto.
- iIntros "#[[H1 H2]|(? & ? & ?)]"; (iSplit; last iSplit); eauto.
  all: rewrite !publicly_related_minted ?minted_TSeal ?minted_spec_TSeal.
  + iDestruct "H1" as "[? _]". iDestruct "H2" as "[? _]". eauto.
  + iDestruct "H1" as "[_ ?]". iDestruct "H2" as "[_ ?]". eauto.
Qed.

Lemma publicly_related_THash t1 t2 :
  PUB⟨THash t1, THash t2⟩ ⊣⊢
  PUB⟨t1, t2⟩ ∨
  (minted t1 ∧ minted_spec t2 ∧
    public_rel_elem (THash t1) (THash t2) ∧ PUB▷⟨t1, t2⟩).
Proof.
rewrite publicly_related_unfold. iSplit.
- iIntros "#(? & ? & [?|?])"; eauto.
  rewrite minted_THash minted_spec_THash; eauto.
- iIntros "#[H|(? & ? & ?)]".
  + iAssert (minted (THash t1)) as "Hmint".
    { rewrite publicly_related_minted minted_THash.
      iDestruct "H" as "[? _]"; eauto. }
    iAssert (minted_spec (THash t2)) as "Hmint_spec".
    { rewrite publicly_related_minted minted_spec_THash.
      iDestruct "H" as "[_ ?]"; eauto. }
    eauto.
  + rewrite minted_THash minted_spec_THash. eauto.
Qed.

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
iIntros "#Hk #[[_ Ht]|(_ & _ & Hfrag & pub▷_k & pub▷_t & #Hrest)]"; first done.
case: k_t1 k_t2 => // kt1 k1' [] // kt2 k2' in k_t_k1 k_t_k2 *.
iDestruct "Hrest" as "[<- Hrest]".
case: kt1 k_t_k1 k_t_k2 => // - [<-] [<-].
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
- iApply "Hrest". rewrite publicly_related_TKey.
  by iDestruct "Hk" as "[??]".
Qed.

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
iSplit.
- iIntros "#H".
  rewrite Spec.tag_unseal /Spec.tag_def.
  rewrite publicly_related_TPair publicly_related_Tag.
  iDestruct "H" as "[-> H]".
  by iFrame "#".
- iIntros "[-> #H]".
  rewrite Spec.tag_unseal /Spec.tag_def.
  rewrite publicly_related_TPair publicly_related_Tag.
  by iFrame "#".
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

Lemma publicly_related_adec_key' (k1 k2 : aenc_key) :
  PUB⟨k1, k2⟩ ⊣⊢
  PUB⟨seed_of_aenc_key k1, seed_of_aenc_key k2⟩.
Proof.
  rewrite [term_of_aenc_key]unlock=> /=.
  rewrite publicly_related_TKey.
  iSplit.
  - iIntros "(_ & ?)". eauto.
  - eauto.
Qed.

Lemma publicly_related_aenc_key_term (k1 : aenc_key) (k2 : term) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k2' : aenc_key), ⌜k2 = k2'⌝.
Proof.
rewrite [term_of_aenc_key]unlock publicly_related_unfold /=.
iIntros "(_ & _ & H)".
case: k2; eauto=> kt2 k2.
iDestruct "H" as "(<- & _)".
by iExists (AEncKey k2).
Qed.

Lemma publicly_related_term_aenc_key (k1 : term) (k2 : aenc_key) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k1' : aenc_key), ⌜k1 = k1'⌝.
Proof.
rewrite [term_of_aenc_key]unlock publicly_related_unfold /=.
iIntros "(_ & _ & H)".
case: k1; eauto=> kt1 k1.
iDestruct "H" as "(-> & _)".
by iExists (AEncKey k1).
Qed.

Lemma publicly_related_later_adec_key' (k1 k2 : aenc_key) :
  PUB▷⟨k1, k2⟩ ⊣⊢
  PUB▷⟨seed_of_aenc_key k1, seed_of_aenc_key k2⟩.
Proof.
rewrite /publicly_related_later /publicly_related_later_pre.
f_equiv; f_equiv; iSplit.
- iIntros "H %k2' #Hpub".
  pose k2'' := AEncKey k2'.
  rewrite -[k2']/(seed_of_aenc_key k2'').
  rewrite -publicly_related_adec_key'.
  iMod ("H" with "Hpub") as "%H".
  apply term_of_aenc_key_inj in H.
  by rewrite H.
- iIntros "H %k2' #Hpub".
  iMod (publicly_related_aenc_key_term with "Hpub") as "(%k2'' & ->)".
  rewrite publicly_related_adec_key'.
  iMod ("H" with "Hpub") as "%H".
  by rewrite [term_of_aenc_key]unlock /term_of_aenc_key_def H.
- iIntros "H %k1' #Hpub".
  pose k1'' := AEncKey k1'.
  rewrite -[k1']/(seed_of_aenc_key k1'').
  rewrite -publicly_related_adec_key'.
  iMod ("H" with "Hpub") as "%H".
  apply term_of_aenc_key_inj in H.
  by rewrite H.
- iIntros "H %k1' #Hpub".
  iMod (publicly_related_term_aenc_key with "Hpub") as "(%k1'' & ->)".
  rewrite publicly_related_adec_key'.
  iMod ("H" with "Hpub") as "%H".
  by rewrite [term_of_aenc_key]unlock /term_of_aenc_key_def H.
Qed.

Lemma publicly_related_aenc_key (k1 k2 : aenc_key) :
  PUB⟨Spec.pkey k1, Spec.pkey k2⟩ ⊣⊢
  PUB⟨k1, k2⟩ ∨
  (minted k1 ∧ minted_spec k2 ∧
    public_rel_elem (Spec.pkey k1) (Spec.pkey k2) ∧ PUB▷⟨k1, k2⟩).
Proof.
rewrite [term_of_aenc_key]unlock /term_of_aenc_key_def=> /=.
iSplit.
- rewrite !publicly_related_TKey.
  iIntros "#(_ & [?|(? & ? & ? & ?)])"; first eauto.
  iRight.
  rewrite minted_TKey minted_spec_TKey.
  rewrite -publicly_related_later_adec_key'.
  rewrite [term_of_aenc_key]unlock /term_of_aenc_key_def.
  eauto.
- rewrite !publicly_related_TKey.
  iIntros "#[[_ ?]|(? & ? & ? & ?)]"; first eauto.
  iSplit=> //.
  iRight.
  rewrite minted_TKey minted_spec_TKey.
  rewrite -publicly_related_later_adec_key'.
  rewrite [term_of_aenc_key]unlock /term_of_aenc_key_def.
  eauto.
Qed.

Lemma publicly_related_aenc_key_pkey_term (sk1 : aenc_key) (k2 : term) :
  PUB⟨Spec.pkey sk1, k2⟩ -∗
  ∃ (sk2' : aenc_key), ⌜k2 = Spec.pkey sk2'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= publicly_related_unfold.
iIntros "(_ & _ & #H)".
case: k2; eauto=> kt2 k2.
iDestruct "H" as "(<- & _)".
by iExists (AEncKey k2).
Qed.

Lemma publicly_related_term_aenc_key_pkey (k1 : term) (sk2 : aenc_key) :
  PUB⟨k1, Spec.pkey sk2⟩ -∗
  ∃ (sk1' : aenc_key), ⌜k1 = Spec.pkey sk1'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /= publicly_related_unfold.
iIntros "(_ & _ & #H)".
case: k1; eauto=> kt1 k1.
iDestruct "H" as "(<- & _)".
by iExists (AEncKey k1).
Qed.

Lemma publicly_related_later_tag N t1 t2 :
  PUB▷⟨Spec.tag (Tag N) t1, Spec.tag (Tag N) t2⟩ ⊣⊢
  PUB▷⟨t1, t2⟩.
Proof.
rewrite /publicly_related_later /publicly_related_later_pre.
iSplit; iIntros "#[#H1 #H2]"; iSplit.
- iIntros (t2') "!> #Hpub".
  iAssert (▷ PUB⟨Spec.tag (Tag N) t1, Spec.tag (Tag N) t2'⟩)%I as "#H".
  { iApply publicly_related_tag. eauto. }
  iPoseProof ("H1" with "H") as ">%H".
  iPureIntro.
  by apply Spec.tag_inj in H as [_ H].
- iIntros (t1') "!> #Hpub".
  iAssert (▷ PUB⟨Spec.tag (Tag N) t1', Spec.tag (Tag N) t2⟩)%I as "#H".
  { iApply publicly_related_tag. eauto. }
  iPoseProof ("H2" with "H") as ">%H".
  iPureIntro.
  by apply Spec.tag_inj in H as [_ H].
- iIntros (t2') "!> #Hpub".
  iAssert (▷ ∃ t2'', ⌜t2' = Spec.tag (Tag N) t2''⌝)%I as "#>[%t2'' ->]".
  { iModIntro. by iApply publicly_related_tag_term. }
  rewrite publicly_related_tag.
  iDestruct "Hpub" as "[_ Hpub]".
  by iPoseProof ("H1" with "Hpub") as ">->".
- iIntros (t1') "!> #Hpub".
  iAssert (▷ ∃ t1'', ⌜t1' = Spec.tag (Tag N) t1''⌝)%I as "#>[%t1'' ->]".
  { iModIntro. by iApply publicly_related_term_tag. }
  rewrite publicly_related_tag.
  iDestruct "Hpub" as "[_ Hpub]".
  by iPoseProof ("H2" with "Hpub") as ">->".
Qed.

Lemma publicly_related_aenc (sk1 sk2 : aenc_key) N (t1 t2 : term) :
  PUB⟨Spec.enc (Spec.pkey sk1) (Tag N) t1,
                    Spec.enc (Spec.pkey sk2) (Tag N) t2⟩ ⊣⊢
  (PUB⟨Spec.pkey sk1, Spec.pkey sk2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (minted (Spec.pkey sk1) ∧ minted t1 ∧
    minted_spec (Spec.pkey sk2) ∧ minted_spec t2 ∧
    public_rel_elem (Spec.enc (Spec.pkey sk1) (Tag N) t1)
                      (Spec.enc (Spec.pkey sk2) (Tag N) t2) ∧
    PUB▷⟨Spec.pkey sk1, Spec.pkey sk2⟩ ∧ PUB▷⟨t1, t2⟩ ∧
    □ (PUB⟨sk1, sk2⟩ → PUB⟨t1, t2⟩)).
Proof.
iSplit.
- iIntros "#Hpub".
  rewrite /Spec.enc /Spec.pkey [term_of_aenc_key]unlock /term_of_aenc_key_def
          publicly_related_TSeal.
  iDestruct "Hpub" as "[[? H]|(Hmint & Hmint_spec & Hpub & pub▷_sk & pub▷_t & _ & #Hskt)]".
  + rewrite publicly_related_tag.
    iDestruct "H" as "[_ H]". eauto.
  + iRight.
    rewrite minted_TSeal minted_tag minted_spec_TSeal minted_spec_tag.
    iDestruct "Hmint" as "[Hmintsk Hmintt]".
    iDestruct "Hmint_spec" as "[Hmint_specsk Hmint_spect]".
    rewrite publicly_related_later_tag.
    do 7 iSplit=> //.
    iClear "Hmintsk Hmintt Hmint_specsk Hmint_spect Hpub pub▷_sk pub▷_t".
    rewrite publicly_related_TKey.
    iIntros "!> #[_ H]".
    iPoseProof ("Hskt" with "H") as "Hpub".
    rewrite publicly_related_tag.
    by iDestruct "Hpub" as "[_ Hpub]".
- iIntros "#[[? ?]|(Hmintsk & Hmintt & Hmint_specsk & Hmint_spect &
                        Hpub & pub▷_sk & pub▷_t & #Hskt)]".
  + rewrite /Spec.enc. rewrite publicly_related_TSeal. iLeft.
    rewrite publicly_related_tag; eauto.
  + rewrite publicly_related_TSeal. iRight.
    iAssert (minted (Spec.enc (Spec.pkey sk1) (Tag N) t1)) as "#Hmint".
    { rewrite /Spec.enc minted_TSeal minted_tag. eauto. }
    iAssert (minted_spec (Spec.enc (Spec.pkey sk2) (Tag N) t2)) as "#Hmint_spec".
    { rewrite /Spec.enc minted_spec_TSeal minted_spec_tag. eauto. }
    iClear "Hmintsk Hmintt Hmint_specsk Hmint_spect".
    do 4 iSplit=> //. iSplit; first by rewrite publicly_related_later_tag.
    iClear "Hpub pub▷_sk pub▷_t Hmint Hmint_spec".
    iModIntro.
    rewrite /Spec.pkey [term_of_aenc_key]unlock /term_of_aenc_key_def.
    iSplit; first done.
    iIntros "#Hpub".
    rewrite publicly_related_TKey.
    iPoseProof ("Hskt" with "[Hpub]") as "#Ht"; first eauto.
    rewrite publicly_related_tag; eauto.
Qed.

#[local] Lemma publicly_related_part_bij_1 t1 t2 t2' :
  PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ▷ ⌜t2 = t2'⌝.
Proof.
elim/term_lt_ind: t1 t2 t2' => t1 IH t2 t2'.
rewrite !publicly_related_unfold.
iIntros "(_ & _ & H) (_ & _ & H')".
iRevert "H H'".
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
  { iApply (IH t11). rewrite /tsize /=.
    lia. all: auto. }
  iAssert (▷ ⌜t22 = t2'2⌝)%I as ">->".
  { iApply (IH t12). rewrite /tsize /=.
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
  have {}IH: (∀ t2 t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  case: kt2'.
    iDestruct "Ht2" as "#[Ht2|[Hfrag pub▷_t]]";
    iDestruct "Ht2'" as "#[Ht2'|[Hfrag' pub▷_t']]".
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t'" as "#[#pub▷_t' _]".
      by iApply "pub▷_t'".
      done.
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t" as "#[#pub▷_t _]".
      by iApply "pub▷_t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iDestruct "Ht2" as "#[Ht2|[Hfrag pub▷_t]]";
    iDestruct "Ht2'" as "#[Ht2'|[Hfrag' pub▷_t']]".
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t'" as "#[#pub▷_t' _]".
      by iApply "pub▷_t'".
      done.
    * iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t" as "#[#pub▷_t _]".
      by iApply "pub▷_t".
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
  have IH1: (∀ k2 k2', PUB⟨k1, k2⟩ -∗ PUB⟨k1, k2'⟩ -∗ ▷ ⌜k2 = k2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  have IH2: (∀ t2 t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  clear IH.
  iDestruct "Ht2" as "#[[Hk2 Ht2]|[Hfrag (pub▷_k & pub▷_t & #Hrest)]]";
  iDestruct "Ht2'" as "#[[Hk2' Ht2']|[Hfrag' (pub▷_k' & pub▷_t' & #Hrest')]]".
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
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_k'" as "#[#pub▷_k' _]".
    by iApply "pub▷_k'".
    iAssert (▷ ⌜t2' = t2⌝)%I as "#Ht".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t'" as "#[#pub▷_t' _]".
    by iApply "pub▷_t'".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k2 = k2'⌝)%I as "#Hk".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_k" as "#[#pub▷_k _]".
    by iApply "pub▷_k".
    iAssert (▷ ⌜t2 = t2'⌝)%I as "#Ht".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t" as "#[#pub▷_t _]".
    by iApply "pub▷_t".
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
  have {}IH: (∀ t2 t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ▷ ⌜t2 = t2'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  iDestruct "Ht2" as "#[Ht2|[Hfrag pub▷_t]]";
  iDestruct "Ht2'" as "#[Ht2'|[Hfrag' pub▷_t']]".
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t2' = t2⌝)%I as ">->".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t'" as "#[#pub▷_t' _]".
    by iApply "pub▷_t'".
    done.
  + iAssert (▷ ⌜t2 = t2'⌝)%I as ">->".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t" as "#[#pub▷_t _]".
    by iApply "pub▷_t".
    done.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- auto.
Qed.

#[local] Lemma publicly_related_part_bij_2 t1 t1' t2 :
  PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ▷ ⌜t1 = t1'⌝.
Proof.
elim/term_lt_ind: t2 t1 t1' => t2 IH t1 t1'.
rewrite !publicly_related_unfold.
iIntros "(_ & _ & H) (_ & _ & H')".
iRevert "H H'".
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
  { iApply (IH t21). rewrite /tsize /=.
    lia. all: auto. }
  iAssert (▷ ⌜t12 = t1'2⌝)%I as ">->".
  { iApply (IH t22). rewrite /tsize /=.
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
  have {}IH: (∀ t1 t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  case: kt2.
    iDestruct "Ht1" as "#[Ht2|[Hfrag pub▷_t]]";
    iDestruct "Ht1'" as "#[Ht2'|[Hfrag' pub▷_t']]".
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t'" as "#[_ #pub▷_t']".
      by iApply "pub▷_t'".
      done.
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t" as "#[_ #pub▷_t]".
      by iApply "pub▷_t".
      done.
    * iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
      iPureIntro. by apply H.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iDestruct "Ht1" as "#[Ht1|[Hfrag pub▷_t]]";
    iDestruct "Ht1'" as "#[Ht1'|[Hfrag' pub▷_t']]".
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      { by iApply IH. }
      done.
    * iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t'" as "#[_ #pub▷_t']".
      by iApply "pub▷_t'".
      done.
    * iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
      rewrite /publicly_related_later /publicly_related_later_pre.
      iDestruct "pub▷_t" as "#[_ #pub▷_t]".
      by iApply "pub▷_t".
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
  have IH1: (∀ k1 k1', PUB⟨k1, k2⟩ -∗ PUB⟨k1', k2⟩ -∗ ▷ ⌜k1 = k1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  have IH2: (∀ t1 t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  clear IH.
  iDestruct "Ht1" as "#[[Hk1 Ht1]|[Hfrag (pub▷_k & pub▷_t & #Hrest)]]";
  iDestruct "Ht1'" as "#[[Hk1' Ht1']|[Hfrag' (pub▷_k' & pub▷_t' & #Hrest')]]".
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
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_k'" as "#[_ #pub▷_k']".
    by iApply "pub▷_k'".
    iAssert (▷ ⌜t1' = t1⌝)%I as "#Ht".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t'" as "#[_ #pub▷_t']".
    by iApply "pub▷_t'".
    iModIntro.
    iDestruct "Hk" as %Hk.
    iDestruct "Ht" as %Ht.
    iPureIntro.
    congruence.
  + iAssert (▷ ⌜k1 = k1'⌝)%I as "#Hk".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_k" as "#[_ #pub▷_k]".
    by iApply "pub▷_k".
    iAssert (▷ ⌜t1 = t1'⌝)%I as "#Ht".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t" as "#[_ #pub▷_t]".
    by iApply "pub▷_t".
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
  have {}IH: (∀ t1 t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ▷ ⌜t1 = t1'⌝).
  { apply IH. rewrite /tsize /=. lia. }
  iDestruct "Ht1" as "#[Ht1|[Hfrag pub▷_t]]";
  iDestruct "Ht1'" as "#[Ht1'|[Hfrag' pub▷_t']]".
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    { by iApply IH. }
    done.
  + iAssert (▷ ⌜t1' = t1⌝)%I as ">->".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t'" as "#[_ #pub▷_t']".
    by iApply "pub▷_t'".
    done.
  + iAssert (▷ ⌜t1 = t1'⌝)%I as ">->".
    rewrite /publicly_related_later /publicly_related_later_pre.
    iDestruct "pub▷_t" as "#[_ #pub▷_t]".
    by iApply "pub▷_t".
    done.
  + iPoseProof (gset_bij_own_elem_agree with "Hfrag Hfrag'") as "%H".
    iPureIntro. by apply H.
- case: t1; auto.
Qed.

Lemma publicly_related_part_bij t1 t2 :
  (∀ t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ▷ ⌜t2 = t2'⌝) ∧
  (∀ t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ▷ ⌜t1 = t1'⌝).
Proof.
split.
apply publicly_related_part_bij_1.
move=> t1'. apply publicly_related_part_bij_2.
Qed.

Lemma publicly_related_part_bij' t1 t1' t2 t2' :
  PUB⟨t1, t1'⟩ -∗ PUB⟨t2, t2'⟩ -∗ ▷ ⌜t1 = t2 ↔ t1' = t2'⌝.
Proof.
iIntros "#Ht1 #Ht2".
iSplit.
- iIntros "%H". rewrite H.
  iApply publicly_related_part_bij_1=> //.
- iIntros "%H". rewrite H.
  iApply publicly_related_part_bij_2=> //.
Qed.

End Rel.

Notation "PUB▷⟨ a , b ⟩" := (publicly_related_later a b)
  (at level 70, no associativity, format "PUB▷⟨ a , b ⟩").
Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 70, no associativity, format "PUB⟨ a , b ⟩").

Lemma public_relGS_alloc `{!relocG Σ} E :
  public_relGpreS Σ →
  ⊢ |={E}=> ∃ (H : public_relGS Σ),
              public_rel_ctx.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod term_meta_specGS_alloc as "[% #?]".
iMod (gset_bij_own_alloc_empty (A:=term) (B:=term)) as "[%public_rel_name public_rel_name_auth]".
iMod (ghost_map_alloc_empty) as "[%private_rel_l private_rel_l_auth]".
iMod (ghost_map_alloc_empty) as "[%private_rel_r private_rel_r_auth]".
pose (Hpub := Public_relGS _ _ _ _ _ public_rel_name private_rel_l private_rel_r).
iExists Hpub.
iMod (inv_alloc cryptisN _ (∃ pub, public_rel_inv pub)%I with "[public_rel_name_auth]") as "#Hinv".
{ iFrame. by rewrite big_sepS_empty. }
by iFrame "#".
Qed.

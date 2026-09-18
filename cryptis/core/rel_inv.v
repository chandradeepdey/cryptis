From iris.algebra Require Import auth cmra ofe gmap gset local_updates.
From iris.base_logic.lib Require Import own.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require Import saved_prop.
From cryptis.core Require Import term minted.
From cryptis Require Import cryptis.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.
From cryptis.core Require Import rel_state.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class public_relGpreS Σ := Public_relGpreS {
  #[local] public_relGpreS_maps :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[local] public_relGpreS_flow :: inG Σ (authUR (gmapUR term (authUR (gset_disjUR term))));
  #[local] public_relGpreS_term_meta :: term_metaGpreS Σ;
  #[local] public_relGpreS_prop :: savedPropG Σ;
}.

Class public_relGS Σ := Public_relGS {
  #[global] maps_inG :: inG Σ (authUR (gmapUR term (authUR (optionUR stateR))));
  #[global] flow_inG :: inG Σ (authUR (gmapUR term (authUR (gset_disjUR term))));
  #[global] term_meta_inG :: term_metaGS Σ;
  #[global] term_meta_spec_inG :: term_meta_specGS Σ;
  #[global] prop_inG :: savedPropG Σ;
  public_rel_map_l : gname;
  public_rel_map_r : gname;
  public_rel_flow_l : gname;
  public_rel_flow_r : gname;
}.

Definition public_relΣ : gFunctors :=
  #[GFunctor (authUR (gmapUR term (authUR (optionUR stateR))));
    GFunctor (authUR (gmapUR term (authUR (gset_disjUR term))));
    term_metaΣ;
    savedPropΣ].

#[global] Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Section PublicRel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Section Map.

Definition public_rel_map_l_auth pub_l : iProp :=
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) ∗
  [∗ map] t ↦ st ∈ pub_l, match st with
                            | Private _ => own public_rel_map_l (◯ {[ t := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_rel_map_r_auth pub_r : iProp :=
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) ∗
  [∗ map] t' ↦ st ∈ pub_r, match st with
                            | Private _ => own public_rel_map_r (◯ {[ t' := ●{#1/2} Some st ]})
                            | _ => emp
                            end.

Definition public_rel_map_inv pub_l pub_r : iProp :=
  public_rel_map_l_auth pub_l ∗
  public_rel_map_r_auth pub_r ∗
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) ∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()).

Definition pending_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ●{#1/2} Some (Private t') ]}).

Definition pending_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ●{#1/2} Some (Private t) ]}).

Definition linked_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some (Private t') ]}).

#[global] Instance linked_in_l_persistent t t' : Persistent (linked_in_l t t').
Proof. apply _. Qed.

Definition linked_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some (Private t) ]}).

#[global] Instance linked_in_r_persistent t t' : Persistent (linked_in_r t t').
Proof. apply _. Qed.

Definition linked t t' : iProp :=
  linked_in_l t t' ∧ linked_in_r t t'.

#[global] Instance linked_persistent t t' : Persistent (linked t t').
Proof. apply _. Qed.

Definition publicly_linked_in_l t t' : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some (Public t') ]}).

#[global] Instance publicly_linked_in_l_persistent t t' : Persistent (publicly_linked_in_l t t').
Proof. apply _. Qed.

Definition publicly_linked_in_r t t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some (Public t) ]}).

#[global] Instance publicly_linked_in_r_persistent t t' : Persistent (publicly_linked_in_r t t').
Proof. apply _. Qed.

Definition publicly_linked t t' : iProp :=
  publicly_linked_in_l t t' ∧ publicly_linked_in_r t t'.

#[global] Instance publicly_linked_persistent t t' : Persistent (publicly_linked t t').
Proof. apply _. Qed.

Definition secret_in_l t : iProp :=
  own public_rel_map_l (◯ {[ t := ◯ Some Secret ]}).

#[global] Instance secret_in_l_persistent t : Persistent (secret_in_l t).
Proof. apply _. Qed.

Definition secret_in_r t' : iProp :=
  own public_rel_map_r (◯ {[ t' := ◯ Some Secret ]}).

#[global] Instance secret_in_r_persistent t' : Persistent (secret_in_r t').
Proof. apply _. Qed.

Lemma publicly_linked_in_l_linked_in_l t t' :
  publicly_linked_in_l t t' -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Public.
Qed.

Lemma publicly_linked_in_r_linked_in_r t t' :
  publicly_linked_in_r t t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Public.
Qed.

Lemma secret_in_l_linked_in_l t t' :
  secret_in_l t -∗ linked_in_l t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Secret.
Qed.

Lemma secret_in_r_linked_in_r t t' :
  secret_in_r t' -∗ linked_in_r t t'.
Proof.
apply bi.entails_wand, own_mono, auth_frag_mono, singleton_included_mono, auth_frag_mono,
  Some_included_mono, Private_included_Secret.
Qed.

Lemma publicly_linked_linked t t' :
  publicly_linked t t' -∗ linked t t'.
Proof.
iIntros "#[H1 H2]". iSplit.
- by iApply publicly_linked_in_l_linked_in_l.
- by iApply publicly_linked_in_r_linked_in_r.
Qed.

Lemma public_rel_map_l_fresh pub_l t :
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  ⌜pub_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (pub_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_token with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_map_r_fresh pub_r t' :
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()) -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  ⌜pub_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (pub_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_spec_token with "Htts Hmeta_t") as "[]".
Qed.

Lemma public_rel_map_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  pending_in_l t t' -∗
  ⌜pub_l !! t = Some (Private t')⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_l !! t) as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Private t') ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Lemma public_rel_map_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  pending_in_r t t' -∗
  ⌜pub_r !! t' = Some (Private t)⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (pub_r !! t') as [st|] eqn:Heq.
- assert (●{#1 / 2} Some (Private t) ≼ ● Some st ⋅ ◯ Some st) as H.
  { by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
  apply auth_auth_dfrac_included in H as [_ Heq'].
  apply leibniz_equiv in Heq'. by simplify_eq.
- apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl.
Qed.

Lemma public_rel_map_l_lookup_frag pub_l t st :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  own public_rel_map_l (◯ {[ t := ◯ Some st ]}) -∗
  ⌜∃ st1, pub_l !! t = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t). rewrite lookup_fmap in Hval.
destruct (pub_l !! t) as [st1|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists st1. split; first done.
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
split; first by apply Some_valid.
exact: (proj1 (Some_included_total _ _) Hincl).
Qed.

Lemma public_rel_map_r_lookup_frag pub_r t' st :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  own public_rel_map_r (◯ {[ t' := ◯ Some st ]}) -∗
  ⌜∃ st1, pub_r !! t' = Some st1 ∧ ✓ st1 ∧ st ≼ st1⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl Hval].
apply singleton_included_l in Hincl as (? & <- & Hincl).
rewrite lookup_fmap in Hincl.
specialize (Hval t'). rewrite lookup_fmap in Hval.
destruct (pub_r !! t') as [st1|] eqn:Heq; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists st1. split; first done.
apply Some_included in Hincl as [Heq' | Hincl];
  first by inversion Heq' as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply auth_both_valid_discrete in Hval as [_ Hval].
split; first by apply Some_valid.
exact: (proj1 (Some_included_total _ _) Hincl).
Qed.

Lemma linked_in_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  linked_in_l t t' -∗
  ⌜pub_l !! t = Some (Private t') ∨
   pub_l !! t = Some Secret ∨
   pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Private_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma linked_in_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  linked_in_r t t' -∗
  ⌜pub_r !! t' = Some (Private t) ∨
   pub_r !! t' = Some Secret ∨
   pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by case: (Private_included Hval Hincl) => [->|[->|->]]; eauto.
Qed.

Lemma publicly_linked_in_l_lookup pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  publicly_linked_in_l t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Public_included Hval Hincl).
Qed.

Lemma publicly_linked_in_r_lookup pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  publicly_linked_in_r t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Public_included Hval Hincl).
Qed.

Lemma secret_in_l_lookup pub_l t :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  secret_in_l t -∗
  ⌜pub_l !! t = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_l_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma secret_in_r_lookup pub_r t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  secret_in_r t' -∗
  ⌜pub_r !! t' = Some Secret⌝.
Proof.
iIntros "H1 H2".
iDestruct (public_rel_map_r_lookup_frag with "H1 H2") as %(st & -> & Hval & Hincl).
iPureIntro. by rewrite (Secret_included Hval Hincl).
Qed.

Lemma publicly_linked_lookup_l pub_l t t' :
  own public_rel_map_l (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_l)) -∗
  publicly_linked t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
Proof.
iIntros "H1 [H2 _]".
by iApply (publicly_linked_in_l_lookup with "H1 H2").
Qed.

Lemma publicly_linked_lookup_r pub_r t t' :
  own public_rel_map_r (● ((λ st, ● Some st ⋅ ◯ Some st) <$> pub_r)) -∗
  publicly_linked t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
Proof.
iIntros "H1 [_ H2]".
by iApply (publicly_linked_in_r_lookup with "H1 H2").
Qed.

Lemma publicly_linked_in_l_agree t t1 t2 :
  publicly_linked_in_l t t1 -∗
  publicly_linked_in_l t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Public_Public_valid.
Qed.

Lemma publicly_linked_in_r_agree t' t1 t2 :
  publicly_linked_in_r t1 t' -∗
  publicly_linked_in_r t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Public_Public_valid.
Qed.

Lemma linked_in_l_publicly_linked_in_l t t1 t2 :
  linked_in_l t t1 -∗
  publicly_linked_in_l t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Private_Public_valid.
Qed.

Lemma linked_in_r_publicly_linked_in_r t' t1 t2 :
  linked_in_r t1 t' -∗
  publicly_linked_in_r t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Private_Public_valid.
Qed.

Lemma secret_in_l_publicly_linked_in_l t t' :
  secret_in_l t -∗
  publicly_linked_in_l t t' -∗
  False.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Secret_Public_valid.
Qed.

Lemma secret_in_r_publicly_linked_in_r t t' :
  secret_in_r t' -∗
  publicly_linked_in_r t t' -∗
  False.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H". iPureIntro. move: H.
rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid.
rewrite -auth_frag_op auth_frag_valid -Some_op Some_valid.
exact: Secret_Public_valid.
Qed.

Lemma publicly_linked_agree_l t t1 t2 :
  publicly_linked t t1 -∗
  publicly_linked t t2 -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[H1 _] [H2 _]".
by iApply (publicly_linked_in_l_agree with "H1 H2").
Qed.

Lemma publicly_linked_agree_r t1 t2 t' :
  publicly_linked t1 t' -∗
  publicly_linked t2 t' -∗
  ⌜t1 = t2⌝.
Proof.
iIntros "[_ H1] [_ H2]".
by iApply (publicly_linked_in_r_agree with "H1 H2").
Qed.

End Map.

Section Flow.

Inductive is_immediate_subterm : term → term → Prop :=
  | SubtermPairL t1 t2 : is_immediate_subterm t1 (TPair t1 t2)
  | SubtermPairR t1 t2 : is_immediate_subterm t2 (TPair t1 t2)
  | SubtermKey kt t1 : is_immediate_subterm t1 (TKey kt t1)
  | SubtermSealKey k t1 : is_immediate_subterm k (TSeal k t1)
  | SubtermSealBody k t1 : is_immediate_subterm t1 (TSeal k t1)
  | SubtermHash t1 : is_immediate_subterm t1 (THash t1).

Definition public_rel_flow_l_auth flow_l : iProp :=
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) ∗
  [∗ map] t ↦ ts ∈ flow_l,
    own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}).

Definition public_rel_flow_r_auth flow_r : iProp :=
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) ∗
  [∗ map] t' ↦ ts ∈ flow_r,
    own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}).

Definition public_rel_flow_inv flow_l flow_r : iProp :=
  public_rel_flow_l_auth flow_l ∗
  public_rel_flow_r_auth flow_r ∗
  ([∗ set] t ∈ dom flow_l, term_meta t (cryptisN.@"public_rel".@"flow") ()) ∗
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()).

Definition protects_superterms_l t ts : iProp :=
  own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_l t tsub : iProp :=
  own public_rel_flow_l (◯ {[ tsub := ◯ (GSet {[ t ]}) ]}).

Definition protects_superterms_r t' ts : iProp :=
  own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}).

Definition protected_by_subterm_r t' tsub : iProp :=
  own public_rel_flow_r (◯ {[ tsub := ◯ (GSet {[ t' ]}) ]}).

Lemma public_rel_flow_l_fresh flow_l t :
  ([∗ set] t' ∈ dom flow_l, term_meta t' (cryptisN.@"public_rel".@"flow") ()) -∗
  term_token t (↑cryptisN.@"public_rel".@"flow") -∗
  ⌜flow_l !! t = None⌝.
Proof.
iIntros "Hmeta Htt".
destruct (flow_l !! t) eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_token with "Htt Hmeta_t") as "[]".
Qed.

Lemma public_rel_flow_r_fresh flow_r t' :
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()) -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"flow") -∗
  ⌜flow_r !! t' = None⌝.
Proof.
iIntros "Hmeta Htts".
destruct (flow_r !! t') eqn:Heq; last done.
iDestruct (big_sepS_elem_of _ _ t' with "Hmeta") as "Hmeta_t"; first by apply elem_of_dom.
by iDestruct (term_meta_spec_token with "Htts Hmeta_t") as "[]".
Qed.

Lemma public_rel_flow_l_lookup flow_l t tsub :
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) -∗
  protected_by_subterm_l t tsub -∗
  ⌜∃ ts, flow_l !! tsub = Some ts ∧ t ∈ ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_l !! tsub) as [ts|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists ts. split; first done.
apply Some_included in Hincl as [Heq | Hincl];
  first by inversion Heq as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply gset_disj_included in Hincl. set_solver.
Qed.

Lemma public_rel_flow_r_lookup flow_r t' t'sub :
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) -∗
  protected_by_subterm_r t' t'sub -∗
  ⌜∃ ts, flow_r !! t'sub = Some ts ∧ t' ∈ ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_r !! t'sub) as [ts|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
exists ts. split; first done.
apply Some_included in Hincl as [Heq | Hincl];
  first by inversion Heq as [H _]; inversion H.
apply auth_frag_included in Hincl.
apply gset_disj_included in Hincl. set_solver.
Qed.

Lemma public_rel_flow_l_lookup_2 flow_l t ts :
  own public_rel_flow_l (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_l)) -∗
  protects_superterms_l t ts -∗
  ⌜flow_l !! t = Some ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_l !! t) as [ts'|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
assert (●{#1 / 2} (GSet ts) ≼ ● (GSet ts') ⋅ ◯ (GSet ts')) as H.
{ by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
apply auth_auth_dfrac_included in H as [_ Heq].
by injection Heq as ->.
Qed.

Lemma public_rel_flow_r_lookup_2 flow_r t' ts :
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) -∗
  protects_superterms_r t' ts -∗
  ⌜flow_r !! t' = Some ts⌝.
Proof.
iIntros "H1 H2".
iCombine "H1 H2" gives "%H".
iPureIntro.
apply auth_both_valid_discrete in H as [Hincl _].
apply singleton_included_l in Hincl as (y & <- & Hincl).
rewrite lookup_fmap in Hincl.
destruct (flow_r !! t') as [ts'|]; last first.
{ apply Some_included_is_Some in Hincl.
  by apply is_Some_None in Hincl. }
assert (●{#1 / 2} (GSet ts) ≼ ● (GSet ts') ⋅ ◯ (GSet ts')) as H.
{ by apply Some_included in Hincl as [H_eq | ?]=> //; rewrite H_eq. }
apply auth_auth_dfrac_included in H as [_ Heq].
by injection Heq as ->.
Qed.

Lemma public_rel_flow_l_ne t tsub tsub1 :
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_l t tsub1 -∗
  ⌜tsub ≠ tsub1⌝.
Proof.
iIntros "Hprot Hprot1".
iIntros (->).
iCombine "Hprot Hprot1" gives "%Hvalid". iPureIntro.
rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
set_solver.
Qed.

Lemma public_rel_flow_r_ne t' t'sub t'sub1 :
  protected_by_subterm_r t' t'sub -∗
  protected_by_subterm_r t' t'sub1 -∗
  ⌜t'sub ≠ t'sub1⌝.
Proof.
iIntros "Hprot Hprot1".
iIntros (->).
iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
iPureIntro.
rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
set_solver.
Qed.

End Flow.

Fixpoint publicly_related t t' : iProp :=
  minted t ∧ minted_spec t' ∧
  match t, t' with
  | TInt n, TInt n' => ⌜n = n'⌝
  | TPair t1 t2, TPair t1' t2' =>
      publicly_related t1 t1' ∧ publicly_related t2 t2'
  | TNonce a, TNonce a' => publicly_linked t t'
  | TKey kt t1, TKey kt' t1' => ⌜kt = kt'⌝ ∧
    match kt with
    | AEnc => publicly_related t1 t1' ∨
              (publicly_linked t t' ∧ linked t1 t1')
    | ADec => publicly_related t1 t1'
    | Sign => publicly_related t1 t1'
    | Verify => publicly_related t1 t1' ∨
                (publicly_linked t t' ∧ linked t1 t1')
    | SEnc => publicly_related t1 t1'
    end
  | TSeal k t1, TSeal k' t1' =>
    (publicly_related k k' ∧ publicly_related t1 t1') ∨
    (publicly_linked t t' ∧ linked k k' ∧ linked t1 t1' ∧
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
    (publicly_linked t t' ∧ linked t1 t1')
  | TNonce a, TSeal k' t1' => publicly_linked t t' ∧ secret_in_r t1' ∧
    □ (match k' with
      | TKey kt' k1' =>
        match kt' with
        | ADec | Sign | Verify => False
        | AEnc | SEnc => secret_in_r k1'
        end
      | _ => False
      end)
  | TSeal k t1, TNonce a' => publicly_linked t t' ∧ secret_in_l t1 ∧
    □ (match k with
      | TKey kt k1 =>
        match kt with
        | ADec |Sign | Verify => False
        | AEnc | SEnc => secret_in_l k1
        end
      | _ => False
      end)
  | _, _ =>
      False (* WIP *)
  end.

#[local] Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 20, no associativity, format "PUB⟨ a , b ⟩").

#[global] Instance publicly_related_persistent t t' : Persistent (PUB⟨t, t'⟩).
Proof. elim/term_ind': t t' => /=; apply _. Qed.

#[global] Instance publicly_related_timeless t t' : Timeless (PUB⟨t, t'⟩).
Proof. elim/term_ind': t t' => /=; apply _. Qed.

Section Invariant.

Definition not_Public st : Prop :=
  match st with
  | Public _ => False
  | _ => True
  end.

Definition public_rel_Private_l_protected pub_l flow_l : Prop :=
  ∀ t st, pub_l !! t = Some st → not_Public st →
    (∃ a, t = TNonce a) ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1).

Definition public_rel_Private_r_protected pub_r flow_r : Prop :=
  ∀ t' st, pub_r !! t' = Some st → not_Public st →
    (∃ a', t' = TNonce a') ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1).

Definition public_rel_Private_protected pub_l pub_r flow_l flow_r : Prop :=
  public_rel_Private_l_protected pub_l flow_l ∧
  public_rel_Private_r_protected pub_r flow_r.

Definition public_rel_Public_bijection pub_l pub_r : Prop :=
  ∀ t t', pub_l !! t = Some (Public t') ↔ pub_r !! t' = Some (Public t).

Definition public_rel_Public_consistent pub_l : iProp :=
  ∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → publicly_related t t'.

Definition public_rel_flow_l_consistent pub_l flow_l : Prop :=
  ∀ t ts, flow_l !! t = Some ts → ts ≠ ∅ →
    set_Forall (is_immediate_subterm t) ts ∧
    ((∃ a, t = TNonce a) ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1)) ∧
    ((pub_l !! t = None) ∨ (∃ st, pub_l !! t = Some st ∧ not_Public st)).

Definition public_rel_flow_r_consistent pub_r flow_r : Prop :=
  ∀ t' ts, flow_r !! t' = Some ts → ts ≠ ∅ →
    set_Forall (is_immediate_subterm t') ts ∧
    ((∃ a', t' = TNonce a') ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1)) ∧
    ((pub_r !! t' = None) ∨ (∃ st, pub_r !! t' = Some st ∧ not_Public st)).

Definition public_rel_flow_consistent pub_l pub_r flow_l flow_r : Prop :=
  public_rel_flow_l_consistent pub_l flow_l ∧
  public_rel_flow_r_consistent pub_r flow_r.

Definition public_rel_inv pub_l pub_r flow_l flow_r : iProp :=
  public_rel_map_inv pub_l pub_r ∗
  public_rel_flow_inv flow_l flow_r ∗
  ⌜public_rel_Private_protected pub_l pub_r flow_l flow_r⌝ ∗
  ⌜public_rel_Public_bijection pub_l pub_r⌝ ∗
  public_rel_Public_consistent pub_l ∗
  ⌜public_rel_flow_consistent pub_l pub_r flow_l flow_r⌝.

Definition public_rel_ctx : iProp :=
  inv cryptisN (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r).

Definition cryptis_rel_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_rel_ctx.

#[global] Instance cryptis_rel_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance cryptis_rel_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

Lemma public_rel_Public_consistent_r pub_l pub_r t t' :
  public_rel_Public_bijection pub_l pub_r →
  pub_r !! t' = Some (Public t) →
  public_rel_Public_consistent pub_l -∗
  publicly_related t t'.
Proof.
move=> Hbij Ht'. iIntros "Hcons". iApply "Hcons". iPureIntro. by apply Hbij.
Qed.

End Invariant.

Section FlowUpdates.

Lemma public_rel_flow_l_extend E t :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"flow") -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t ∅ ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_fresh flow_l t with "Hmeta_flow_l Httf") as "%Hfresh".
iMod (own_update with "Hflow_l") as "[Hflow_l Hflow_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hflow_frag_t" as "[[Hflow_t_frag Hflow_t_frag'] _]".
iMod (term_meta_set (cryptisN.@"public_rel".@"flow") () with "Httf") as "#Hmeta_flow_t"=> //.
iModIntro. iSplitR "Hflow_t_frag' Httm"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ∅]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hflow_t_frag".
{ iSplitL.
  - rewrite /public_rel_flow_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub Hst.
  destruct (HPriv_l _ _ Hpub Hst) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. exists t1sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide; first naive_solver.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (Hsubs & [?|(t1sub & ts2 & ? & ?)] & Hpub).
  + naive_solver.
  + do 2 (split=> //). right. exists t1sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_flow_r_extend E t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"flow") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' ∅ ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_fresh flow_r t' with "Hmeta_flow_r Httf") as "%Hfresh".
iMod (own_update with "Hflow_r") as "[Hflow_r Hflow_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hflow_frag_t'" as "[[Hflow_t'_frag Hflow_t'_frag'] _]".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"flow") () with "Httf") as "#Hmeta_flow_t'"=> //.
iModIntro. iSplitR "Hflow_t'_frag' Httm"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ∅]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hflow_t'_frag".
{ iSplitL.
  - rewrite /public_rel_flow_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub Hst.
  destruct (HPriv_r _ _ Hpub Hst) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. exists t1'sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide; first naive_solver.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (Hsubs & [?|(t1'sub & ts2 & ? & ?)] & Hpub).
  + naive_solver.
  + do 2 (split=> //). right. exists t1'sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_flow_l_extend_2 E t t1' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"flow") -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t ∅ ∗
          pending_in_l t t1'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_fresh flow_l t with "Hmeta_flow_l Httf") as "%Hfresh".
iMod (own_update with "Hflow_l") as "[Hflow_l Hflow_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hflow_frag_t" as "[[Hflow_t_frag Hflow_t_frag'] _]".
iMod (term_meta_set (cryptisN.@"public_rel".@"flow") () with "Httf") as "#Hmeta_flow_t"=> //.
iModIntro. iSplitR "Hflow_t_frag' Httm"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ∅]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hflow_t_frag".
{ iSplitL.
  - rewrite /public_rel_flow_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub Hst.
  destruct (HPriv_l _ _ Hpub Hst) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. exists t1sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide; first naive_solver.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (Hsubs & [?|(t1sub & ts2 & ? & ?)] & Hpub).
  + naive_solver.
  + do 2 (split=> //). right. exists t1sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_flow_r_extend_2 E t' t1 :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"flow") -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' ∅ ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_fresh flow_r t' with "Hmeta_flow_r Httf") as "%Hfresh".
iMod (own_update with "Hflow_r") as "[Hflow_r Hflow_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (GSet ∅) ⋅ ◯ (GSet ∅)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hflow_frag_t'" as "[[Hflow_t'_frag Hflow_t'_frag'] _]".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"flow") () with "Httf") as "#Hmeta_flow_t'"=> //.
iModIntro. iSplitR "Hflow_t'_frag' Httm"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ∅]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hflow_t'_frag".
{ iSplitL.
  - rewrite /public_rel_flow_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub Hst.
  destruct (HPriv_r _ _ Hpub Hst) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. exists t1'sub, ts1.
  rewrite lookup_insert_ne; naive_solver.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide; first naive_solver.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (Hsubs & [?|(t1'sub & ts2 & ? & ?)] & Hpub).
  + naive_solver.
  + do 2 (split=> //). right. exists t1'sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
Qed.

Lemma public_rel_flow_l_grow E t ts tsup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  tsup ∉ ts →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t (ts ∪ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hl_frac Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet (ts ∪ {[ tsup ]})))
    (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ tsup ]}) with ({[ tsup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∪ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_grow E t' ts t'sup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  t'sup ∉ ts →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∪ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t' ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hr_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∪ {[ t'sup ]})))
    (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ t'sup ]}) with ({[ t'sup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∪ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(t'sub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (t'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_grow_2 E a tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a) tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l (TNonce a) ∅ -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l (TNonce a) {[ tsup ]} ∗
          protected_by_subterm_l tsup (TNonce a) ∗
          term_token (TNonce a) (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hl_frac Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l (TNonce a) with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hflt".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hflt with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[TNonce a := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  + exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = TNonce a)) as [->|?].
    - exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  by left.
Qed.

Lemma public_rel_flow_r_grow_2 E a' t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a') t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r (TNonce a') ∅ -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r (TNonce a') {[ t'sup ]} ∗
          protected_by_subterm_r t'sup (TNonce a') ∗
          term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hr_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r (TNonce a') with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt' with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[TNonce a' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  + exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = TNonce a')) as [->|?].
    - exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  by left.
Qed.

Lemma public_rel_flow_l_grow_3 E t tsub tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protects_superterms_l t ∅ -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          protected_by_subterm_l t tsub ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hl_frac Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hflt".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hflt with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Hprot Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; last by left.
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (tsub = t)) as [->|?].
  + set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_grow_3 E t' t'sub t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  protects_superterms_r t' ∅ -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          protected_by_subterm_r t' t'sub ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hr_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt' with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Hprot Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; last by left.
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (t'sub = t')) as [->|?].
  + set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_grow_4 E t t1' ts tsup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  tsup ∉ ts →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t (ts ∪ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet (ts ∪ {[ tsup ]})))
    (● (GSet (ts ∪ {[ tsup ]})) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ tsup ]}) with ({[ tsup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∪ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts2) as (? & [?|(t1sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_grow_4 E t' t1 ts t'sup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  t'sup ∉ ts →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' (ts ∪ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t' ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hts Hni Hsub) "#(_ & _ & Hinv) Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∪ {[ t'sup ]})))
    (● (GSet (ts ∪ {[ t'sup ]})) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ts) with (● GSet ts ⋅ ◯ (GSet ∅)) at 2.
  apply auth_local_update=> //.
  replace (ts ∪ {[ t'sup ]}) with ({[ t'sup ]} ∪ ts) by set_solver.
  apply gset_disj_alloc_empty_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∪ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts2) as (? & [?|(t1'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by (apply set_Forall_union; [done|by apply set_Forall_singleton]).
  split; last done.
  destruct Hchain as [?|(t'sub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (t'sub = t')) as [->|?].
  + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t'sub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_grow_5 E a t1' tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a) tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l (TNonce a) ∅ -∗
  pending_in_l (TNonce a) t1' -∗
  |={E}=> protects_superterms_l (TNonce a) {[ tsup ]} ∗
          protected_by_subterm_l tsup (TNonce a) ∗
          pending_in_l (TNonce a) t1'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hfrag") as "%Hpltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hflt".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hflt with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iAssert (public_rel_map_l_auth pub_l) with "[Hmap_l Hmap_l_frag]" as "Hmap_l".
{ rewrite /public_rel_map_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hl Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[TNonce a := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  + exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = TNonce a)) as [->|?].
    - exists (TNonce a), ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  right. by exists (Private t1').
Qed.

Lemma public_rel_flow_r_grow_5 E a' t1 t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a') t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r (TNonce a') ∅ -∗
  pending_in_r t1 (TNonce a') -∗
  |={E}=> protects_superterms_r (TNonce a') {[ t'sup ]} ∗
          protected_by_subterm_r t'sup (TNonce a') ∗
          pending_in_r t1 (TNonce a').
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hfrag") as "%Hprtst'".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt' with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iAssert (public_rel_map_r_auth pub_r) with "[Hmap_r Hmap_r_frag]" as "Hmap_r".
{ rewrite /public_rel_map_r_auth. iFrame. }
iModIntro. iSplitR "Hr_frac Hr Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[TNonce a' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  + exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = TNonce a')) as [->|?].
    - exists (TNonce a'), ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; first by left; eauto.
  right. by exists (Private t1).
Qed.

Lemma public_rel_flow_l_grow_6 E t t1' tsub tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protects_superterms_l t ∅ -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          protected_by_subterm_l t tsub ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hfrag") as "%Hpltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hflt".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hflt with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hflt.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iAssert (public_rel_map_l_auth pub_l) with "[Hmap_l Hmap_l_frag]" as "Hmap_l".
{ rewrite /public_rel_map_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hl Hprot Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t1 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  + exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1sub, ts1. by rewrite lookup_insert_ne.
- split; last done.
  move=> t1 ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & [?|(t1sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1sub = t)) as [->|?].
    - exists t, ({[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1.
  split; first by apply set_Forall_singleton.
  split; last by right; exists (Private t1').
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (tsub = t)) as [->|?].
  + set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_grow_6 E t' t1 t'sub t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  protects_superterms_r t' ∅ -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          protected_by_subterm_r t' t'sub ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hfrag") as "%Hprtst'".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt' with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iAssert (public_rel_map_r_auth pub_r) with "[Hmap_r Hmap_r_frag]" as "Hmap_r".
{ rewrite /public_rel_map_r_auth. iFrame. }
iModIntro. iSplitR "Hr_frac Hr Hprot Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t1' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  + exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t1'sub, ts1. by rewrite lookup_insert_ne.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & [?|(t1'sub & ts2 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t1'sub = t')) as [->|?].
    - exists t', ({[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t1'.
  split; first by apply set_Forall_singleton.
  split; last by right; exists (Private t1).
  destruct Hprot as (ts2 & ? & ?).
  right. destruct (decide (t'sub = t')) as [->|?].
  + set_solver.
  + exists t'sub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink E t ts tsup t1 :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protected_by_subterm_l tsup t1 -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t1 ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1 Htt".
iPoseProof (public_rel_flow_l_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot1") as "(%ts1 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hprot1 Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?].
    * exists t1, ts1. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?].
      + exists t1, ts1. by rewrite lookup_insert_ne.
      + exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?].
    * exists t1, ts1. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink E t' ts t'sup t1' :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protected_by_subterm_r t'sup t1' -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t1' ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hprot1 Htts".
iPoseProof (public_rel_flow_r_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot1") as "(%ts1 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hprot1 Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?].
    * exists t1', ts1. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?].
      + exists t1', ts1. by rewrite lookup_insert_ne.
      + exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?].
    * exists t1', ts1. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink_2 E t ts tsup :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protects_superterms_l tsup ∅ -∗
  term_token tsup (↑cryptisN.@"public_rel".@"map") -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protects_superterms_l tsup ∅ ∗
          term_token tsup (↑cryptisN.@"public_rel".@"map") ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l tsup with "Hmeta_map_l Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac_sup") as "%Hfltsup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by congruence.
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink_2 E t' ts t'sup :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protects_superterms_r t'sup ∅ -∗
  term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protects_superterms_r t'sup ∅ ∗
          term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hr_frac_sup Htts_sup Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r t'sup with "Hmeta_map_r Htts_sup") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac_sup") as "%Hfrt'sup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hr_frac_sup Htts_sup Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by congruence.
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink_3 E t ts tsup t' :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  publicly_linked tsup t' -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #Hpub Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (publicly_linked_lookup_l with "Hmap_l Hpub") as "%Hpltsupt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
have Hfltsup : ∀ ts, flow_l !! tsup = Some ts → ts ≠ ∅ → False.
{ move=> ts1 Hflow Hts1.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts2. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts2) as (? & [?|(t2sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by case: (Hfltsup _ Hflow Hts2).
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink_3 E t' ts t'sup t :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  publicly_linked t t'sup -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot #Hpub Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (publicly_linked_lookup_r with "Hmap_r Hpub") as "%Hprtt'sup".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
have Hfrt'sup : ∀ ts, flow_r !! t'sup = Some ts → ts ≠ ∅ → False.
{ move=> ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts2. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts2 Hflow Hts2.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts2) as (? & [?|(t2'sub & ts3 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts3 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by case: (Hfrt'sup _ Hflow Hts2).
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts3. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts2 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts2 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts2. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink_4 E t t1' ts tsup t1 :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protected_by_subterm_l tsup t1 -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t1 ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1 Hfrag".
iPoseProof (public_rel_flow_l_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot1") as "(%ts2 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hprot1 Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?].
    * exists t1, ts2. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts3. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts3) as (? & [?|(t2sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?].
      + exists t1, ts2. by rewrite lookup_insert_ne.
      + exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?].
    * exists t1, ts2. by rewrite lookup_insert_ne.
    * exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink_4 E t' t1 ts t'sup t1' :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protected_by_subterm_r t'sup t1' -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t1' ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hprot1 Hfrag".
iPoseProof (public_rel_flow_r_ne with "Hprot Hprot1") as "%Hne".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot1") as "(%ts2 & % & %)".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hprot1 Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?].
    * exists t1', ts2. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts3. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts3) as (? & [?|(t2'sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?].
      + exists t1', ts2. by rewrite lookup_insert_ne.
      + exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?].
    * exists t1', ts2. by rewrite lookup_insert_ne.
    * exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink_5 E t t1' ts tsup :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protects_superterms_l tsup ∅ -∗
  term_token tsup (↑cryptisN.@"public_rel".@"map") -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protects_superterms_l tsup ∅ ∗
          term_token tsup (↑cryptisN.@"public_rel".@"map") ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l tsup with "Hmeta_map_l Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac_sup") as "%Hfltsup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts3. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts3) as (? & [?|(t2sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by congruence.
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink_5 E t' t1 ts t'sup :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protects_superterms_r t'sup ∅ -∗
  term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protects_superterms_r t'sup ∅ ∗
          term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot Hr_frac_sup Htts_sup Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r t'sup with "Hmeta_map_r Htts_sup") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac_sup") as "%Hfrt'sup".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hr_frac_sup Htts_sup Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts3. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts3) as (? & [?|(t2'sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by congruence.
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_l_shrink_6 E t t1' ts tsup t' :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  publicly_linked tsup t' -∗
  pending_in_l t t1' -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          pending_in_l t t1'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #Hpub Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (publicly_linked_lookup_l with "Hmap_l Hpub") as "%Hpltsupt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_l_cons _ _ Hfltts Hts) as (Hsubs & Hchain & Hpub).
have Hfltsup : ∀ ts, flow_l !! tsup = Some ts → ts ≠ ∅ → False.
{ move=> ts2 Hflow Hts2.
  destruct (Hflow_l_cons _ _ Hflow Hts2) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[Hl_frac2 Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
iModIntro. iSplitR "Hl_frac Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; last done.
  move=> t2 ? Hpub1 Hst1.
  destruct (HPriv_l _ _ Hpub1 Hst1) as [? | (t2sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2sub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t2)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2sub, ts3. by rewrite lookup_insert_ne.
- split; last done.
  move=> t2 ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_l_cons _ _ Hflow Hts3) as (? & [?|(t2sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2sub = t)) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (tsup = t2)) as [->|?]; first by case: (Hfltsup _ Hflow Hts3).
      exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t)) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (tsup = t)) as [->|?]; first by set_solver.
    exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

Lemma public_rel_flow_r_shrink_6 E t' t1 ts t'sup t :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  publicly_linked t t'sup -∗
  pending_in_r t1 t' -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          pending_in_r t1 t'.
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hr_frac Hprot #Hpub Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (publicly_linked_lookup_r with "Hmap_r Hpub") as "%Hprtt'sup".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
have Hts : ts ≠ ∅ by set_solver.
destruct (Hflow_r_cons _ _ Hfrt'ts Hts) as (Hsubs & Hchain & Hpub).
have Hfrt'sup : ∀ ts, flow_r !! t'sup = Some ts → ts ≠ ∅ → False.
{ move=> ts2 Hflow Hts2.
  destruct (Hflow_r_cons _ _ Hflow Hts2) as (_ & _ & [?|(st & ? & Hst)]); first congruence.
  by destruct st; [congruence | destruct Hst | congruence | congruence]. }
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[Hr_frac2 Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iCombine "Hr Hprot" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hfrt'ts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] _]".
iModIntro. iSplitR "Hr_frac Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame. }
iPureIntro. split; last split; [|done|].
- split; first done.
  move=> t2' ? Hpub1 Hst1.
  destruct (HPriv_r _ _ Hpub1 Hst1) as [? | (t2'sub & ts3 & ? & ?)]; first eauto.
  right. destruct (decide (t2'sub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t2')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists t2'sub, ts3. by rewrite lookup_insert_ne.
- split; first done.
  move=> t2' ts3 Hflow Hts3.
  rewrite lookup_insert in Hflow; case_decide as Heq; last first.
  { destruct (Hflow_r_cons _ _ Hflow Hts3) as (? & [?|(t2'sub & ts4 & ? & ?)] & ?);
      first naive_solver.
    do 2 (split=> //). right. destruct (decide (t2'sub = t')) as [->|?].
    - assert (ts4 = ts) as -> by congruence.
      destruct (decide (t'sup = t2')) as [->|?]; first by case: (Hfrt'sup _ Hflow Hts3).
      exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
    - exists t2'sub, ts4. by rewrite lookup_insert_ne. }
  injection Hflow as <-. subst t2'.
  split; first by move=> x Hx; apply Hsubs; set_solver.
  split; last done.
  destruct Hchain as [?|(tsub & ts3 & ? & ?)]; first by left.
  right. destruct (decide (tsub = t')) as [->|?].
  + assert (ts3 = ts) as -> by congruence.
    destruct (decide (t'sup = t')) as [->|?]; first by set_solver.
    exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver.
  + exists tsub, ts3. by rewrite lookup_insert_ne.
Qed.

End FlowUpdates.

Section MapUpdates.

Lemma public_rel_map_l_extend E t t' tsub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          linked_in_l t t' ∗
          pending_in_l t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iMod (own_update with "Hmap_l") as "[Hmap_l Hmap_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (Private t') ⋅ ◯ Some (Private t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t" as "[[Hmap_t_frag Hmap_t_frag'] Hmap_frag_t]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iModIntro. iSplitR "Hprot Hmap_frag_t Hmap_t_frag'"; last by iFrame.
iModIntro. iExists (<[t := Private t']> pub_l), pub_r.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_t_frag".
{ iSplitL.
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; first naive_solver.
  by iApply "Hpub_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hflow Hts1.
destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_r_extend E t t' t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          linked_in_r t t' ∗
          pending_in_r t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iMod (own_update with "Hmap_r") as "[Hmap_r Hmap_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (Private t) ⋅ ◯ Some (Private t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t'" as "[[Hmap_t'_frag Hmap_t'_frag'] Hmap_frag_t']".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iModIntro. iSplitR "Hprot Hmap_frag_t' Hmap_t'_frag'"; last by iFrame.
iModIntro. iExists pub_l, (<[t' := Private t]> pub_r).
iFrame. iFrame "#".
iSplitL "Hmap_r Hmap_r_frag Hmap_t'_frag".
{ iSplitL.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split.
- split; first done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver.
- rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_l_extend_2 E a t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> linked_in_l (TNonce a) t' ∗
          pending_in_l (TNonce a) t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l (TNonce a) with "Hmeta_map_l Htt") as "%Hfresh".
iMod (own_update with "Hmap_l") as "[Hmap_l Hmap_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a) (● Some (Private t') ⋅ ◯ Some (Private t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t" as "[[Hmap_t_frag Hmap_t_frag'] Hmap_frag_t]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iModIntro. iSplitR "Hmap_frag_t Hmap_t_frag'"; last by iFrame.
iModIntro. iExists (<[TNonce a := Private t']> pub_l), pub_r, flow_l, flow_r.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_t_frag".
{ iSplitL.
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; first naive_solver.
  by iApply "Hpub_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hflow Hts1.
destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_r_extend_2 E t a' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> linked_in_r t (TNonce a') ∗
          pending_in_r t (TNonce a').
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_fresh pub_r (TNonce a') with "Hmeta_map_r Htts") as "%Hfresh".
iMod (own_update with "Hmap_r") as "[Hmap_r Hmap_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a') (● Some (Private t) ⋅ ◯ Some (Private t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t'" as "[[Hmap_t'_frag Hmap_t'_frag'] Hmap_frag_t']".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iModIntro. iSplitR "Hmap_frag_t' Hmap_t'_frag'"; last by iFrame.
iModIntro. iExists pub_l, (<[TNonce a' := Private t]> pub_r), flow_l, flow_r.
iFrame. iFrame "#".
iSplitL "Hmap_r Hmap_r_frag Hmap_t'_frag".
{ iSplitL.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iPureIntro. split; last split.
- split; first done. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver.
- rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver.
- split; first done.
  move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma linked_extend E t t' tsub t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗ protected_by_subterm_r t' t'sub ∗
          linked t t' ∗
          pending_in_l t t' ∗
          pending_in_r t t'.
Proof.
iIntros (HE) "#Hctx Hprot Hprot1 Htt Htts".
iPoseProof (public_rel_map_l_extend t t' with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_rel_map_r_extend t t' with "Hctx Hprot1 Htts") as ">[? [??]]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_2 E a t' t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          linked (TNonce a) t' ∗
          pending_in_l (TNonce a) t' ∗
          pending_in_r (TNonce a) t'.
Proof.
iIntros (HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_rel_map_l_extend_2 a t' with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_rel_map_r_extend (TNonce a) t' with "Hctx Hprot Htts") as ">[? [??]]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_3 E t a' tsub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          linked t (TNonce a') ∗
          pending_in_l t (TNonce a') ∗
          pending_in_r t (TNonce a').
Proof.
iIntros (HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_rel_map_l_extend t (TNonce a') with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_rel_map_r_extend_2 t a' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma linked_extend_4 E a a' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> linked (TNonce a) (TNonce a') ∗
          pending_in_l (TNonce a) (TNonce a') ∗
          pending_in_r (TNonce a) (TNonce a').
Proof.
iIntros (HE) "#Hctx Htt Htts".
iPoseProof (public_rel_map_l_extend_2 a a' with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_rel_map_r_extend_2 a a' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /linked.
by iFrame.
Qed.

Lemma public_rel_lock_Secret_l E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  pending_in_l t t' -∗
  |={E}=> secret_in_l t.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltt'".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some Secret ⋅ ◯ Some Secret)
    (● Some Secret ⋅ ◯ Some Secret)); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Secret. }
iDestruct "Hl" as "[_ #Hl]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := Secret]> pub_l), pub_r, flow_l, flow_r.
rewrite /public_rel_inv.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag".
{ rewrite /public_rel_map_l_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplit.
{ iPureIntro. split; last done. move=> t1 st Hpub Hst.
  rewrite lookup_insert in Hpub; case_decide; last by eapply HPriv_l.
  simplify_eq. exact: (HPriv_l _ _ Hpltt' I). }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; first naive_solver.
  by iApply "Hpub_consistent". }
iPureIntro. split; last done.
move=> t1 ts1 Hflow Hts1.
destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_lock_Secret_r E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  pending_in_r t t' -∗
  |={E}=> secret_in_r t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprtt'".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some Secret ⋅ ◯ Some Secret)
    (● Some Secret ⋅ ◯ Some Secret)); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Secret. }
iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists pub_l, (<[t' := Secret]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv.
iFrame. iFrame "#".
iSplitL "Hmap_r Hmap_r_frag".
{ rewrite /public_rel_map_r_auth fmap_insert big_sepM_insert_delete dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplit.
{ iPureIntro. split; first done. move=> t1' st Hpub Hst.
  rewrite lookup_insert in Hpub; case_decide; last by eapply HPriv_r.
  simplify_eq. exact: (HPriv_r _ _ Hprtt' I). }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iPureIntro. split; first done.
move=> t1' ts1 Hflow Hts1.
destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_secret_l E t tsub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗ secret_in_l t.
Proof.
iIntros (HE) "#Hctx Hprot Htt".
iMod (public_rel_map_l_extend t t with "Hctx Hprot Htt") as "(Hprot & _ & Hpend)"=> //.
iMod (public_rel_lock_Secret_l with "Hctx Hpend") as "#?"=> //.
by iFrame.
Qed.

Lemma public_rel_secret_r E t' t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗ secret_in_r t'.
Proof.
iIntros (HE) "#Hctx Hprot Htts".
iMod (public_rel_map_r_extend t' t' with "Hctx Hprot Htts") as "(Hprot & _ & Hpend)"=> //.
iMod (public_rel_lock_Secret_r with "Hctx Hpend") as "#?"=> //.
by iFrame.
Qed.

Lemma public_rel_secret_l_2 E a :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> secret_in_l (TNonce a).
Proof.
iIntros (HE) "#Hctx Htt".
iMod (public_rel_map_l_extend_2 a (TNonce a) with "Hctx Htt") as "[_ Hpend]"=> //.
by iMod (public_rel_lock_Secret_l with "Hctx Hpend") as "#?".
Qed.

Lemma public_rel_secret_r_2 E a' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> secret_in_r (TNonce a').
Proof.
iIntros (HE) "#Hctx Htts".
iMod (public_rel_map_r_extend_2 (TNonce a') a' with "Hctx Htts") as "[_ Hpend]"=> //.
by iMod (public_rel_lock_Secret_r with "Hctx Hpend") as "#?".
Qed.

(*
You will probably need a custom version of this lemma tailored to the
declassification you want to attempt.

Example:
Say you have (nonce, msg) ↦ Private (nonce', msg'), where
PUB⟨msg, msg'⟩. flow_l !! nonce = {[ (nonce, msg) ]},
flow_r !! nonce' = {[ (nonce', msg') ]}.

When trying to change it to (nonce, msg) ↦ Public (nonce', msg'),
proving the publicly_linked (nonce, msg) (nonce', msg') -∗
PUB⟨(nonce, msg), (nonce', msg')⟩ precondition will require that
you have publicly_linked nonce nonce' in the recursive case.

But to get that, you will need to show that flow_l !! nonce = ∅ and
flow_r !! nonce' = ∅. Since (nonce, msg) and (nonce', msg') can
have no other protectors, you will need to transition them to Public,
which will require you to prove PUB⟨(nonce, msg), (nonce', msg')⟩.
This is circular.

To get around this, you should open the invariant and do all of the
transitions at once. This depends on the structure of the terms you
are trying to declassify and the nature of the recursive flow chain,
so you need to come up with your own custom lemma. Feel free to use
these lemmas as templates.

PS: If the declassification is deterministic, you can directly
construct t ↦ Public t' from the tokens instead of going through
t ↦ Private t' first (public_rel_extend).

Since publicly_linked t t' → linked t t', you can use it to
prove PUB.
*)
Lemma public_rel_lock_Public E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  pending_in_l t t' -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Hl_frac Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltt'".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprtt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl". iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (Public t') ⋅ ◯ Some (Public t'))
    (● Some (Public t') ⋅ ◯ Some (Public t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Public. }
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (Public t) ⋅ ◯ Some (Public t))
    (● Some (Public t) ⋅ ◯ Some (Public t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Public. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := Public t']> pub_l), (<[t' := Public t]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_l_auth /public_rel_map_r_auth.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_r Hmap_r_frag".
{ iSplitL "Hmap_l Hmap_l_frag"; last iSplitL "Hmap_r Hmap_r_frag".
  - rewrite /public_rel_map_l_auth.
    rewrite fmap_insert big_sepM_insert_delete.
    iFrame.
  - rewrite /public_rel_map_r_auth.
    rewrite fmap_insert big_sepM_insert_delete.
    iFrame.
  - rewrite !dom_insert_lookup_L=> //.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite !lookup_insert; repeat case_decide; naive_solver. }
iSplitL "Hrel Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; subst.
  - injection Hpub as <-. iApply "Hrel". iFrame "#".
  - by iApply "Hpub_consistent". }
iPureIntro. split.
- move=> t1 ts1 Hflow Hts1.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_lock_Public_l E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  pending_in_l t t' -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Hl_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltt'".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (Public t') ⋅ ◯ Some (Public t'))
    (● Some (Public t') ⋅ ◯ Some (Public t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Public. }
iMod (own_update with "Hmap_r") as "[Hmap_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (Public t) ⋅ ◯ Some (Public t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := Public t']> pub_l), (<[t' := Public t]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_l_auth /public_rel_map_r_auth.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_r Hmap_r_frag".
{ iSplitL "Hmap_l Hmap_l_frag"; last iSplitL "Hmap_r Hmap_r_frag".
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert_delete /=.
    iFrame.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite (dom_insert_lookup_L pub_l)=> //.
    rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite !lookup_insert; repeat case_decide; naive_solver. }
iSplitL "Hrel Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; subst.
  - injection Hpub as <-. iApply "Hrel". iFrame "#".
  - by iApply "Hpub_consistent". }
iPureIntro. split.
- move=> t1 ts1 Hflow Hts1.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_lock_Public_r E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  pending_in_r t t' -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Htt Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprtt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update with "Hmap_l") as "[Hmap_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (Public t') ⋅ ◯ Some (Public t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Some (Public t) ⋅ ◯ Some (Public t))
    (● Some (Public t) ⋅ ◯ Some (Public t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock_Public. }
iDestruct "Hr" as "[_ #Hr]". iDestruct "Hl" as "[_ #Hl]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := Public t']> pub_l), (<[t' := Public t]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_l_auth /public_rel_map_r_auth.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_r Hmap_r_frag".
{ iSplitL "Hmap_l Hmap_l_frag"; last iSplitL "Hmap_r Hmap_r_frag".
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert_delete /=.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    rewrite dom_insert_lookup_L => //.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite !lookup_insert; repeat case_decide; naive_solver. }
iSplitL "Hrel Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; subst.
  - injection Hpub as <-. iApply "Hrel". iFrame "#".
  - by iApply "Hpub_consistent". }
iPureIntro. split.
- move=> t1 ts1 Hflow Hts1.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (publicly_linked t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> publicly_linked t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Htt Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  [%HPriv_l %HPriv_r] & %Hbij & Hpub_consistent &
                  [%Hflow_l_cons %Hflow_r_cons])".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh_l".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh_r".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iMod (own_update with "Hmap_l") as "[Hmap_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● Some (Public t') ⋅ ◯ Some (Public t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh_l //. }
iMod (own_update with "Hmap_r") as "[Hmap_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● Some (Public t) ⋅ ◯ Some (Public t)));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh_r //. }
iDestruct "Hl" as "[_ #Hl]". iDestruct "Hr" as "[_ #Hr]".
iModIntro. iSplitL; last by iFrame "#".
iModIntro. iExists (<[t := Public t']> pub_l), (<[t' := Public t]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_l_auth /public_rel_map_r_auth.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_r Hmap_r_frag".
{ iSplitL "Hmap_l Hmap_l_frag"; last iSplitL "Hmap_r Hmap_r_frag".
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite !dom_insert_L.
    rewrite !big_sepS_insert; try by apply not_elem_of_dom.
    iFrame "#". }
iSplit.
{ iPureIntro. split.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver.
  - move=> ??. rewrite lookup_insert; case_decide; naive_solver. }
iSplit.
{ iPureIntro. rewrite /public_rel_Public_bijection in Hbij. move=> ??.
  rewrite !lookup_insert; repeat case_decide; naive_solver. }
iSplitL "Hrel Hpub_consistent".
{ iIntros (??) "%Hpub".
  rewrite lookup_insert in Hpub; case_decide; subst.
  - injection Hpub as <-. iApply "Hrel". iFrame "#".
  - by iApply "Hpub_consistent". }
iPureIntro. split.
- move=> t1 ts1 Hflow Hts1.
  destruct (Hflow_l_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
- move=> t1' ts1 Hflow Hts1.
  destruct (Hflow_r_cons _ _ Hflow Hts1) as (? & ? & ?).
  do 2 (split=> //). rewrite lookup_insert; case_decide; naive_solver.
Qed.

End MapUpdates.

End PublicRel.

Notation "PUB⟨ a , b ⟩" := (publicly_related a b)
  (at level 20, no associativity, format "PUB⟨ a , b ⟩").

Lemma public_relGS_alloc `{!relocG Σ} E :
  public_relGpreS Σ →
  ⊢ |={E}=> ∃ (H : public_relGS Σ),
              public_rel_ctx.
Proof.
move=> ?; iStartProof.
iMod term_metaGS_alloc as "[% #?]".
iMod term_meta_specGS_alloc as "[% #?]".
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_rel_map_l Hmap_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (optionUR stateR)))))
  as "[%public_rel_map_r Hmap_r]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (gset_disjUR term)))))
  as "[%public_rel_flow_l Hflow_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR (gset_disjUR term)))))
  as "[%public_rel_flow_r Hflow_r]"; first by apply auth_auth_valid.
pose (Hpub := Public_relGS _ _ _ _ _
                public_rel_map_l public_rel_map_r
                public_rel_flow_l public_rel_flow_r).
iExists Hpub.
iMod (inv_alloc cryptisN _
        (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r)%I
        with "[Hmap_l Hmap_r Hflow_l Hflow_r]") as "#Hinv"; last by iFrame "#".
iModIntro. iExists ∅, ∅, ∅, ∅.
rewrite /public_rel_inv /public_rel_map_inv /public_rel_flow_inv
        /public_rel_map_l_auth /public_rel_map_r_auth
        /public_rel_flow_l_auth /public_rel_flow_r_auth
        !fmap_empty !dom_empty_L !big_sepM_empty !big_sepS_empty.
iFrame. rewrite !left_id.
iSplit; [|iSplit; [|iSplit]].
- iPureIntro. split; move=> t ts; by rewrite lookup_empty => ?.
- iPureIntro. move=> t t'. rewrite !lookup_empty. by split=> ?.
- iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
- iPureIntro. split; move=> t ts; by rewrite lookup_empty => ?.
Qed.

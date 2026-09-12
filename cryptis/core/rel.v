From iris.algebra Require Import auth cmra ofe gmap gset local_updates.
From iris.base_logic.lib Require Import own.
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
  split=> // s.
  change (ε ⋅ s) with (state_op_instance ε s).
  case: s => [ts|t|] //=.
  + f_equiv; set_solver.
  + case_bool_decide=> //; set_solver.
  Qed.

  Canonical Structure stateR := discreteR state state_ra_mixin.
  Canonical Structure stateUR := Ucmra state state_ucmra_mixin.

  #[global] Instance stateR_discrete : CmraDiscrete stateR.
  Proof. by split; first apply _. Qed.

  #[global] Instance state_core_id (st : state) : CoreId st.
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
  #[local] public_relGpreS_flow :: inG Σ (authUR (gmapUR term (authUR (gset_disjUR term))));
  #[local] public_relGpreS_term_meta :: term_metaGpreS Σ;
  #[local] public_relGpreS_prop :: savedPropG Σ;
}.

Class public_relGS Σ := Public_relGS {
  #[global] maps_inG :: inG Σ (authUR (gmapUR term (authUR stateUR)));
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
  #[GFunctor (authUR (gmapUR term (authUR stateUR)));
    GFunctor (authUR (gmapUR term (authUR (gset_disjUR term))));
    term_metaΣ;
    savedPropΣ].

#[global] Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).

Implicit Types t : term.
Implicit Types st : state.
Implicit Types pub_l pub_r : gmap term state.
Implicit Types flow_l flow_r : gmap term (gset term).
Implicit Types P : term -> term -> iProp.

Definition public_rel_map_l_auth pub_l : iProp :=
    own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) ∗
    [∗ map] t ↦ st ∈ pub_l, match st with
                              | Private _ => own public_rel_map_l (◯ {[ t := ●{#1/2} st ]})
                              | _ => emp
                              end.

Definition public_rel_map_r_auth pub_r : iProp :=
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) ∗
  [∗ map] t' ↦ st ∈ pub_r, match st with
                            | Private _ => own public_rel_map_r (◯ {[ t' := ●{#1/2} st ]})
                            | _ => emp
                            end.

Definition public_rel_map_l_frag t st : iProp :=
  own public_rel_map_l (◯ {[ t := ●{#1/2} st ]}).

Definition public_rel_map_r_frag t' st : iProp :=
  own public_rel_map_r (◯ {[ t' := ●{#1/2} st ]}).

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

Lemma public_rel_map_l_lookup pub_l t st :
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  public_rel_map_l_frag t st -∗
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

Lemma public_rel_map_r_lookup pub_r t' st :
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  public_rel_map_r_frag t' st -∗
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

Lemma public_rel_map_l_lookup_locked pub_l t t' :
  own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l)) -∗
  public_rel_map_l_locked t t' -∗
  ⌜pub_l !! t = Some (Public t')⌝.
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
have Hop : Public t' ⋅ z = state_op_instance (Public t') z by [].
rewrite Hop in Heq Hval *.
destruct z as [ts|t2|]; simpl in *; repeat case_bool_decide; simpl in *;
  solve [ done | destruct Hval ].
Qed.

Lemma public_rel_map_r_lookup_locked pub_r t t' :
  own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r)) -∗
  public_rel_map_r_locked t t' -∗
  ⌜pub_r !! t' = Some (Public t)⌝.
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
have Hop : Public t ⋅ z = state_op_instance (Public t) z by [].
rewrite Hop in Heq Hval *.
destruct z as [ts|t2|]; simpl in *; repeat case_bool_decide; simpl in *;
  solve [ done | destruct Hval ].
Qed.

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
    own public_rel_flow_l (◯ {[ t := ●{#1/2} (GSet ts) ]}) ∗
    ([∗ set] tsup ∈ ts, ⌜is_immediate_subterm t tsup⌝) ∗
    ⌜ts ≠ ∅ → (∃ a, t = TNonce a) ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1)⌝.

Definition public_rel_flow_r_auth flow_r : iProp :=
  own public_rel_flow_r (● ((λ ts, ● GSet ts ⋅ ◯ GSet ts) <$> flow_r)) ∗
  [∗ map] t' ↦ ts ∈ flow_r,
    own public_rel_flow_r (◯ {[ t' := ●{#1/2} (GSet ts) ]}) ∗
    ([∗ set] t'sup ∈ ts, ⌜is_immediate_subterm t' t'sup⌝) ∗
    ⌜ts ≠ ∅ → (∃ a', t' = TNonce a') ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1)⌝.

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

Lemma publicly_related_TInv_l :
  ∀ t t', is_inv t → (PUB⟨t, t'⟩ = False)%I.
Proof. by case. Qed.

Lemma publicly_related_TExp_l :
  ∀ t t', is_exp t → (PUB⟨t, t'⟩ = False)%I.
Proof. by case. Qed.

Lemma publicly_related_TMul_l :
  ∀ t t', is_mul t → (PUB⟨t, t'⟩ = False)%I.
Proof. by case. Qed.

#[global] Instance publicly_related_persistent t t' : Persistent (PUB⟨t, t'⟩).
Proof.
elim: t t'=> /=; try apply _.
- move=> t IH Hmul Hinv t'.
  rewrite publicly_related_TInv_l ?is_inv_TInv //.
  apply _.
- move=> t IH Hexp ts IHts Hatom Htsne Htssort Htsninv t'.
  rewrite publicly_related_TExp_l ?is_exp_TExpN //; last by case_bool_decide.
  apply _.
- move=> ts IHts Hatom Htssort Htsninv Htsne t'.
  rewrite publicly_related_TMul_l; first by apply _.
  by apply is_mul_TMulN.
Qed.

#[global] Instance publicly_related_timeless t t' : Timeless (PUB⟨t, t'⟩).
Proof.
elim: t t'=> /=; try apply _.
- move=> t IH Hmul Hinv t'.
  rewrite publicly_related_TInv_l ?is_inv_TInv //.
  apply _.
- move=> t IH Hexp ts IHts Hatom Htsne Htssort Htsninv t'.
  rewrite publicly_related_TExp_l ?is_exp_TExpN //; last by case_bool_decide.
  apply _.
- move=> ts IHts Hatom Htssort Htsninv Htsne t'.
  rewrite publicly_related_TMul_l; first by apply _.
  by apply is_mul_TMulN.
Qed.

Definition public_rel_map_inv pub_l pub_r : iProp :=
  public_rel_map_l_auth pub_l ∗
  public_rel_map_r_auth pub_r ∗
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) ∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()).

Definition public_rel_Public_consistent pub_l pub_r : iProp :=
  ⌜∀ t t', pub_l !! t = Some (Public t') ↔ pub_r !! t' = Some (Public t)⌝ ∗
  (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → publicly_related t t').

Definition public_rel_flow_inv flow_l flow_r : iProp :=
  public_rel_flow_l_auth flow_l ∗
  public_rel_flow_r_auth flow_r ∗
  ([∗ set] t ∈ dom flow_l, term_meta t (cryptisN.@"public_rel".@"flow") ()) ∗
  ([∗ set] t' ∈ dom flow_r, term_meta_spec t' (cryptisN.@"public_rel".@"flow") ()).

Definition public_rel_Private_l_protected pub_l flow_l : Prop :=
  ∀ t ts, pub_l !! t = Some (Private ts) →
    (∃ a, t = TNonce a) ∨ (∃ tsub ts1, flow_l !! tsub = Some ts1 ∧ t ∈ ts1).

Definition public_rel_Private_r_protected pub_r flow_r : Prop :=
  ∀ t' ts, pub_r !! t' = Some (Private ts) →
    (∃ a', t' = TNonce a') ∨ (∃ t'sub ts1, flow_r !! t'sub = Some ts1 ∧ t' ∈ ts1).

Definition public_rel_Private_protected pub_l pub_r flow_l flow_r : iProp :=
  ⌜public_rel_Private_l_protected pub_l flow_l⌝ ∗
  ⌜public_rel_Private_l_protected pub_r flow_r⌝.

Definition public_rel_flow_l_consistent pub_l flow_l : Prop :=
  ∀ t ts, flow_l !! t = Some ts → ts ≠ ∅ →
    (pub_l !! t = None) ∨ (∃ ts1, pub_l !! t = Some (Private ts1)).

Definition public_rel_flow_r_consistent pub_r flow_r : Prop :=
  ∀ t' ts, flow_r !! t' = Some ts → ts ≠ ∅ →
    (pub_r !! t' = None) ∨ (∃ ts1, pub_r !! t' = Some (Private ts1)).

Definition public_rel_flow_consistent pub_l pub_r flow_l flow_r : iProp :=
  ⌜public_rel_flow_l_consistent pub_l flow_l⌝ ∗
  ⌜public_rel_flow_l_consistent pub_r flow_r⌝.

Definition public_rel_inv pub_l pub_r flow_l flow_r : iProp :=
  public_rel_map_inv pub_l pub_r ∗
  public_rel_flow_inv flow_l flow_r ∗
  public_rel_Public_consistent pub_l pub_r ∗
  public_rel_Private_protected pub_l pub_r flow_l flow_r ∗
  public_rel_flow_consistent pub_l pub_r flow_l flow_r.

Definition public_rel_ctx : iProp :=
  inv cryptisN (∃ pub_l pub_r flow_l flow_r, public_rel_inv pub_l pub_r flow_l flow_r).

Definition cryptis_rel_ctx : iProp :=
  term_meta_ctx ∗ term_meta_spec_ctx ∗ public_rel_ctx.

#[global] Instance cryptis_rel_ctx_has_term_meta_ctx : HasTermMetaCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[H _]". Qed.

#[global] Instance cryptis_rel_ctx_has_term_meta_spec_ctx : HasTermMetaSpecCtx cryptis_rel_ctx.
Proof. split; last apply _. by iIntros "#[_ [H _]]". Qed.

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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
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
    iFrame. iSplit; first done.
    iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts1 ?) "(? & ? & %Hprot)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot in Hts1 as [?|(t1sub & ts2 & ?)]; first eauto.
    right. exists t1sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro.
  move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. exists t1sub, ts1.
  rewrite lookup_insert_ne; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
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
    iFrame. iSplit; first done.
    iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts1 ?) "(? & ? & %Hprot)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot in Hts1 as [?|(t1'sub & ts2 & ?)]; first eauto.
    right. exists t1'sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro.
  move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. exists t1'sub, ts1.
  rewrite lookup_insert_ne; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_l_extend_2 E t ts :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token t (↑cryptisN.@"public_rel".@"flow") -∗
  public_rel_map_l_frag t (Private ts) -∗
  |={E}=> protects_superterms_l t ∅ ∗
          public_rel_map_l_frag t (Private ts).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
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
    iFrame. iSplit; first done.
    iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts1 ?) "(? & ? & %Hprot)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot in Hts1 as [?|(t1sub & ts2 & ?)]; first eauto.
    right. exists t1sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro.
  move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. exists t1sub, ts1.
  rewrite lookup_insert_ne; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_r_extend_2 E t' ts :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"flow") -∗
  public_rel_map_r_frag t' (Private ts) -∗
  |={E}=> protects_superterms_r t' ∅ ∗
          public_rel_map_r_frag t' (Private ts).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Httf Httm".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap_inv &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
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
    iFrame. iSplit; first done.
    iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts1 ?) "(? & ? & %Hprot)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot in Hts1 as [?|(t1'sub & ts2 & ?)]; first eauto.
    right. exists t1'sub, ts2.
    rewrite lookup_insert_ne; naive_solver.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro.
  move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. exists t1'sub, ts1.
  rewrite lookup_insert_ne; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
iIntros (HE Hne Hni Hsub) "#(_ & _ & Hinv) Hl_frac Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
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
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_union; last by set_solver.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? %Hprot]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    apply Hprot in Hne as [?|(tsub & ts1 & ?)]; first eauto.
    right. destruct (decide (tsub = t)) as [->|?].
    + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists tsub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t1sub & ts2 & ?)]; first eauto.
    right. destruct (decide (t1sub = t)) as [->|?].
    + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t1sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
    set_solver.
  - exists t1sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
iIntros (HE Hne Hni Hsub) "#(_ & _ & Hinv) Hr_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
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
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_union; last by set_solver.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? %Hprot]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    apply Hprot in Hne as [?|(t'sub & ts1 & ?)]; first eauto.
    right. destruct (decide (t'sub = t')) as [->|?].
    + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t'sub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t'sub & ts2 & ?)]; first eauto.
    right. destruct (decide (t'sub = t')) as [->|?].
    + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t'sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
    set_solver.
  - exists t1'sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l (TNonce a) with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[TNonce a := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? _]".
  iFrame.
  iSplitR; first by eauto.
  iApply (big_sepM_mono with "Hflow_l_frag").
  iIntros (t1 ts1 ?) "(? & ? & %Hprot)".
  iFrame. iPureIntro. move=> Hts1.
  apply Hprot in Hts1 as [?|(tsub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (tsub = TNonce a)) as [->|?].
  - exists (TNonce a), {[ tsup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists tsub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  - exists (TNonce a), {[ tsup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r (TNonce a') with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[TNonce a' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? _]".
  iFrame.
  iSplitR; first by eauto.
  iApply (big_sepM_mono with "Hflow_r_frag").
  iIntros (t1' ts1 ?) "(? & ? & %Hprot)".
  iFrame. iPureIntro. move=> Hts1.
  apply Hprot in Hts1 as [?|(t'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t'sub = TNonce a')) as [->|?].
  - exists (TNonce a'), {[ t'sup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t'sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  - exists (TNonce a'), {[ t'sup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1'sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow ?.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ tsup ]} with ({[ tsup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] Hl]".
iModIntro. iSplitR "Hl_frac Hl Hprot Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? _]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    destruct Hprot as (ts1 & ? & ?).
    right. destruct (decide (tsub = t)) as [->|?].
    + set_solver.
    + exists tsub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t1sub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (t1sub = t)) as [->|?].
    + set_solver.
    + exists t1sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  - set_solver.
  - exists t1sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
  change (● GSet ∅) with (● GSet ∅ ⋅ ◯ GSet (∅ : gset term)) at 2.
  apply auth_local_update=> //.
  replace {[ t'sup ]} with ({[ t'sup ]} ∪ (∅ : gset term)) by set_solver.
  apply gset_disj_alloc_local_update.
  set_solver. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] Hr]".
iModIntro. iSplitR "Hr_frac Hr Hprot Htts"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? _]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    destruct Hprot as (ts1 & ? & ?).
    right. destruct (decide (t'sub = t')) as [->|?].
    + set_solver.
    + exists t'sub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t1'sub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (t1'sub = t')) as [->|?].
    + set_solver.
    + exists t1'sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  - set_solver.
  - exists t1'sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_l_grow_4 E t ts1 ts tsup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  tsup ∉ ts →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  public_rel_map_l_frag t (Private ts1) -∗
  |={E}=> protects_superterms_l t (ts ∪ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t ∗
          public_rel_map_l_frag t (Private ts1).
Proof.
iIntros (HE Hne Hni Hsub) "#(_ & _ & Hinv) Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
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
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_union; last by set_solver.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? %Hprot]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    apply Hprot in Hne as [?|(tsub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (tsub = t)) as [->|?].
    + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists tsub, ts2. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts2 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts2.
    apply Hprot1 in Hts2 as [?|(t1sub & ts3 & ? & ?)]; first eauto.
    right. destruct (decide (t1sub = t)) as [->|?].
    + exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t1sub, ts3. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  - exists t, (ts ∪ {[ tsup ]}). rewrite lookup_insert_eq.
    set_solver.
  - exists t1sub, ts2. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_r_grow_4 E t' ts1 ts t'sup :
  ↑cryptisN ⊆ E →
  ts ≠ ∅ →
  t'sup ∉ ts →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  public_rel_map_r_frag t' (Private ts1) -∗
  |={E}=> protects_superterms_r t' (ts ∪ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t' ∗
          public_rel_map_r_frag t' (Private ts1).
Proof.
iIntros (HE Hne Hni Hsub) "#(_ & _ & Hinv) Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
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
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_union; last by set_solver.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? %Hprot]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    apply Hprot in Hne as [?|(t'sub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (t'sub = t')) as [->|?].
    + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t'sub, ts2. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts2 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts2.
    apply Hprot1 in Hts2 as [?|(t'sub & ts3 & Hrtsubts3 & ?)]; first eauto.
    right. destruct (decide (t'sub = t')) as [->|?].
    + exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
      set_solver.
    + exists t'sub, ts3. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ts2 Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts3 & Hrt1'subts3 & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  - exists t', (ts ∪ {[ t'sup ]}). rewrite lookup_insert_eq.
    set_solver.
  - exists t1'sub, ts3. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow ?.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_l_grow_5 E a ts tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a) tsup →
  cryptis_rel_ctx -∗
  protects_superterms_l (TNonce a) ∅ -∗
  public_rel_map_l_frag (TNonce a) (Private ts) -∗
  |={E}=> protects_superterms_l (TNonce a) {[ tsup ]} ∗
          protected_by_subterm_l tsup (TNonce a) ∗
          public_rel_map_l_frag (TNonce a) (Private ts).
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hfrag") as "%Hpltst".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iDestruct (big_sepM_delete _ _ (TNonce a) _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
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
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? _]".
  iFrame.
  iSplitR; first by eauto.
  iApply (big_sepM_mono with "Hflow_l_frag").
  iIntros (t1 ts1 ?) "(? & ? & %Hprot)".
  iFrame. iPureIntro. move=> Hts1.
  apply Hprot in Hts1 as [?|(t1sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  - exists (TNonce a), {[ tsup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = TNonce a)) as [->|?].
  - exists (TNonce a), {[ tsup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_r_grow_5 E a' ts t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm (TNonce a') t'sup →
  cryptis_rel_ctx -∗
  protects_superterms_r (TNonce a') ∅ -∗
  public_rel_map_r_frag (TNonce a') (Private ts) -∗
  |={E}=> protects_superterms_r (TNonce a') {[ t'sup ]} ∗
          protected_by_subterm_r t'sup (TNonce a') ∗
          public_rel_map_r_frag (TNonce a') (Private ts).
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hfrag") as "%Hprt'st".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ (TNonce a') _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
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
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? _]".
  iFrame.
  iSplitR; first by eauto.
  iApply (big_sepM_mono with "Hflow_r_frag").
  iIntros (t1' ts1 ?) "(? & ? & %Hprot)".
  iFrame. iPureIntro. move=> Hts1.
  apply Hprot in Hts1 as [?|(t1'sub & ts2 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  - exists (TNonce a'), {[ t'sup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1'sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = TNonce a')) as [->|?].
  - exists (TNonce a'), {[ t'sup ]}. rewrite lookup_insert_eq.
    set_solver.
  - exists t1'sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_l_grow_6 E t ts tsub tsup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t tsup →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protects_superterms_l t ∅ -∗
  public_rel_map_l_frag t (Private ts) -∗
  |={E}=> protects_superterms_l t {[ tsup ]} ∗
          protected_by_subterm_l tsup t ∗
          protected_by_subterm_l t tsub ∗
          public_rel_map_l_frag t (Private ts).
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hl_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hfrag") as "%Hpltst".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hfltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t _ Hfltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]}))
    (● (GSet {[ tsup ]}) ⋅ ◯ (GSet {[ tsup ]})));
    first by rewrite lookup_fmap Hfltts.
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
iSplitL "Hflow_l Hflow_l_frag Hl_frac2 Hl_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hl_cons" as "[? _]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    destruct Hprot as (ts1 & ? & ?).
    right. destruct (decide (tsub = t)) as [->|?].
    * set_solver.
    * exists tsub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t1 ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t1sub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (t1sub = t)) as [->|?].
    + set_solver.
    + exists t1sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t1 ? Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (t1sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1sub = t)) as [->|?].
  - set_solver.
  - exists t1sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
Qed.

Lemma public_rel_flow_r_grow_6 E t' ts t'sub t'sup :
  ↑cryptisN ⊆ E →
  is_immediate_subterm t' t'sup →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  protects_superterms_r t' ∅ -∗
  public_rel_map_r_frag t' (Private ts) -∗
  |={E}=> protects_superterms_r t' {[ t'sup ]} ∗
          protected_by_subterm_r t'sup t' ∗
          protected_by_subterm_r t' t'sub ∗
          public_rel_map_r_frag t' (Private ts).
Proof.
iIntros (HE Hsub) "#(_ & _ & Hinv) Hprot Hr_frac Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hfrag") as "%Hprt'st".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hr_frac") as "%Hfrt'ts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iDestruct (big_sepM_delete _ _ t' _ Hfrt'ts with "Hflow_r_frag") as "[[Hr_frac2 Hr_cons] Hflow_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hflow_r Hr") as "[Hflow_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]}))
    (● (GSet {[ t'sup ]}) ⋅ ◯ (GSet {[ t'sup ]})));
    first by rewrite lookup_fmap Hfrt'ts.
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
iSplitL "Hflow_r Hflow_r_frag Hr_frac2 Hr_cons".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  rewrite big_sepS_singleton.
  iDestruct "Hr_cons" as "[? _]".
  iFrame.
  iSplitR.
  - iSplit; first done.
    iPureIntro. move=> _.
    destruct Hprot as (ts1 & ? & ?).
    right. destruct (decide (t'sub = t')) as [->|?].
    * set_solver.
    * exists t'sub, ts1. by rewrite lookup_insert_ne.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t1' ts1 ?) "(? & ? & %Hprot1)".
    iFrame. iPureIntro. move=> Hts1.
    apply Hprot1 in Hts1 as [?|(t1'sub & ts2 & ? & ?)]; first eauto.
    right. destruct (decide (t1'sub = t')) as [->|?].
    + set_solver.
    + exists t1'sub, ts2. by rewrite lookup_insert_ne. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t1' ? Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (t1'sub & ts1 & ? & ?)]; first eauto.
  right. destruct (decide (t1'sub = t')) as [->|?].
  - set_solver.
  - exists t1'sub, ts1. by rewrite lookup_insert_ne. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ?? Hflow.
rewrite lookup_insert in Hflow; case_decide; naive_solver.
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
iAssert ⌜t1 ≠ t⌝%I as %Hne.
{ iIntros (->).
  iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
  iPureIntro.
  rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
  rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
  set_solver. }
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot1") as "%Hlt1".
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2,
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  destruct (decide (t2 = tsup)) as [->|?].
  - destruct Hlt1 as (ts0 & ? & ?).
    exists t1, ts0. by rewrite lookup_insert_ne.
  - exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hprot1 Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_r_shrink E t' ts t'sup t1 :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protected_by_subterm_r t'sup t1 -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t1 ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1 Htt".
iAssert ⌜t1 ≠ t'⌝%I as %Hne.
{ iIntros (->).
  iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
  iPureIntro.
  rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
  rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
  set_solver. }
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot1") as "%Hlt1".
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2,
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  destruct (decide (t2 = t'sup)) as [->|?].
  - destruct Hlt1 as (ts0 & ? & ?).
    exists t1, ts0. by rewrite lookup_insert_ne.
  - exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hprot1 Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
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
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l tsup with "Hmeta_map_l Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac_sup") as "%Hltsup".
have Hne : t ≠ tsup.
{ move=> ?. subst tsup. rewrite Hltts in Hltsup. injection Hltsup as ->. set_solver. }
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ tsup →
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ tsup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2]. congruence. }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ tsup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
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
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r t'sup with "Hmeta_map_r Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac_sup") as "%Hltsup".
have Hne : t' ≠ t'sup.
{ move=> ?. subst t'sup. rewrite Hltts in Hltsup. injection Hltsup as ->. set_solver. }
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ t'sup →
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ t'sup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2]. congruence. }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ t'sup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_l_shrink_3 E t ts tsup t' :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  public_rel_elem tsup t' -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          term_token t (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #[Hlocked _] Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iPoseProof (public_rel_map_l_lookup_locked with "Hmap_l Hlocked") as "%Hpub_sup".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
have Hsup_empty : ∀ ts', flow_l !! tsup = Some ts' → ts' ≠ ∅ → False.
{ move=> ts' Hlk Hne'.
  destruct (Hflow_l_cons _ _ Hlk Hne') as [?|(? & ?)]; congruence. }
have Hne : t ≠ tsup.
{ move=> ?. subst tsup. apply (Hsup_empty _ Hltts). set_solver. }
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ tsup →
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iAssert (public_rel_map_l_auth pub_l) with "[Hmap_l Hmap_l_frag]" as "Hmap_l".
{ rewrite /public_rel_map_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ tsup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2].
      by apply (Hsup_empty _ Ht2). }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ tsup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_r_shrink_3 E t' ts t'sup t :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  public_rel_elem t t'sup -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          term_token_spec t' (↑cryptisN.@"public_rel".@"map").
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #[_ Hlocked] Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iPoseProof (public_rel_map_r_lookup_locked with "Hmap_r Hlocked") as "%Hpub_sup".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
have Hsup_empty : ∀ ts', flow_r !! t'sup = Some ts' → ts' ≠ ∅ → False.
{ move=> ts' Hlk Hne'.
  destruct (Hflow_r_cons _ _ Hlk Hne') as [?|(? & ?)]; congruence. }
have Hne : t' ≠ t'sup.
{ move=> ?. subst t'sup. apply (Hsup_empty _ Hltts). set_solver. }
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ t'sup →
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iAssert (public_rel_map_r_auth pub_r) with "[Hmap_r Hmap_r_frag]" as "Hmap_r".
{ rewrite /public_rel_map_r_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Htt"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ t'sup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2].
      by apply (Hsup_empty _ Ht2). }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ t'sup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_l_shrink_4 E t ts1 ts tsup t1 :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protected_by_subterm_l tsup t1 -∗
  public_rel_map_l_frag t (Private ts1) -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protected_by_subterm_l tsup t1 ∗
          public_rel_map_l_frag t (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1 Hfrag".
iAssert ⌜t1 ≠ t⌝%I as %Hne.
{ iIntros (->).
  iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
  iPureIntro.
  rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
  rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
  set_solver. }
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot1") as "%Hlt1".
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2,
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  destruct (decide (t2 = tsup)) as [->|?].
  - destruct Hlt1 as (ts0 & ? & ?).
    exists t1, ts0. by rewrite lookup_insert_ne.
  - exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hprot1 Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_r_shrink_4 E t' ts1 ts t'sup t1 :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protected_by_subterm_r t'sup t1 -∗
  public_rel_map_r_frag t' (Private ts1) -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protected_by_subterm_r t'sup t1 ∗
          public_rel_map_r_frag t' (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hprot1 Hfrag".
iAssert ⌜t1 ≠ t'⌝%I as %Hne.
{ iIntros (->).
  iPoseProof (own_valid_2 with "Hprot Hprot1") as "%Hvalid".
  iPureIntro.
  rewrite -auth_frag_op singleton_op -auth_frag_op in Hvalid.
  rewrite auth_frag_valid singleton_valid auth_frag_valid gset_disj_valid_op in Hvalid.
  set_solver. }
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  Hmap &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot1") as "%Hlt1".
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2,
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  destruct (decide (t2 = t'sup)) as [->|?].
  - destruct Hlt1 as (ts0 & ? & ?).
    exists t1, ts0. by rewrite lookup_insert_ne.
  - exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hprot1 Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_l_shrink_5 E t ts1 ts tsup :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  protects_superterms_l tsup ∅ -∗
  term_token tsup (↑cryptisN.@"public_rel".@"map") -∗
  public_rel_map_l_frag t (Private ts1) -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          protects_superterms_l tsup ∅ ∗
          term_token tsup (↑cryptisN.@"public_rel".@"map") ∗
          public_rel_map_l_frag t (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l tsup with "Hmeta_map_l Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac_sup") as "%Hltsup".
have Hne : t ≠ tsup.
{ move=> ?. subst tsup. rewrite Hltts in Hltsup. injection Hltsup as ->. set_solver. }
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ tsup →
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ tsup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2]. congruence. }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ tsup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_r_shrink_5 E t' ts1 ts t'sup :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  protects_superterms_r t'sup ∅ -∗
  term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") -∗
  public_rel_map_r_frag t' (Private ts1) -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          protects_superterms_r t'sup ∅ ∗
          term_token_spec t'sup (↑cryptisN.@"public_rel".@"map") ∗
          public_rel_map_r_frag t' (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot Hl_frac_sup Htt_sup Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r t'sup with "Hmeta_map_r Htt_sup") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac_sup") as "%Hltsup".
have Hne : t' ≠ t'sup.
{ move=> ?. subst t'sup. rewrite Hltts in Hltsup. injection Hltsup as ->. set_solver. }
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ t'sup →
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iModIntro. iSplitR "Hl_frac Hl_frac_sup Htt_sup Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ t'sup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2]. congruence. }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ t'sup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_l_shrink_6 E t ts1 ts tsup t' :
  ↑cryptisN ⊆ E →
  tsup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_l t ts -∗
  protected_by_subterm_l tsup t -∗
  public_rel_elem tsup t' -∗
  public_rel_map_l_frag t (Private ts1) -∗
  |={E}=> protects_superterms_l t (ts ∖ {[ tsup ]}) ∗
          public_rel_map_l_frag t (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #[Hlocked _] Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iPoseProof (public_rel_map_l_lookup_locked with "Hmap_l Hlocked") as "%Hpub_sup".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hl_frac") as "%Hltts".
have Hsup_empty : ∀ ts', flow_l !! tsup = Some ts' → ts' ≠ ∅ → False.
{ move=> ts' Hlk Hne'.
  destruct (Hflow_l_cons _ _ Hlk Hne') as [?|(? & ?)]; congruence. }
have Hne : t ≠ tsup.
{ move=> ?. subst tsup. apply (Hsup_empty _ Hltts). set_solver. }
iDestruct (big_sepM_delete _ _ t _ Hltts with "Hflow_l_frag") as "[[Hl_frac2 Hl_cons] Hflow_l_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_l Hl") as "[Hflow_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet (ts ∖ {[ tsup ]})))
    (● (GSet (ts ∖ {[ tsup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ tsup →
    flow_l !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t := ts ∖ {[ tsup ]}]> flow_l !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t)) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t, (ts ∖ {[ tsup ]}). rewrite lookup_insert_eq. set_solver. }
iAssert (public_rel_map_l_auth pub_l) with "[Hmap_l Hmap_l_frag]" as "Hmap_l".
{ rewrite /public_rel_map_l_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, (<[t := ts ∖ {[ tsup ]}]> flow_l), flow_r.
iFrame. iFrame "#".
iSplitL "Hflow_l Hflow_l_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_l_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_l_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ tsup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2].
      by apply (Hsup_empty _ Ht2). }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; last done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ tsup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_l _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iSplit; last done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_l_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_flow_r_shrink_6 E t' ts1 ts t'sup t :
  ↑cryptisN ⊆ E →
  t'sup ∈ ts →
  cryptis_rel_ctx -∗
  protects_superterms_r t' ts -∗
  protected_by_subterm_r t'sup t' -∗
  public_rel_elem t t'sup -∗
  public_rel_map_r_frag t' (Private ts1) -∗
  |={E}=> protects_superterms_r t' (ts ∖ {[ t'sup ]}) ∗
          public_rel_map_r_frag t' (Private ts1).
Proof.
iIntros (HE Hin) "#(_ & _ & Hinv) Hl_frac Hprot #[_ Hlocked] Hfrag".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iPoseProof (public_rel_map_r_lookup_locked with "Hmap_r Hlocked") as "%Hpub_sup".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hl_frac") as "%Hltts".
have Hsup_empty : ∀ ts', flow_r !! t'sup = Some ts' → ts' ≠ ∅ → False.
{ move=> ts' Hlk Hne'.
  destruct (Hflow_r_cons _ _ Hlk Hne') as [?|(? & ?)]; congruence. }
have Hne : t' ≠ t'sup.
{ move=> ?. subst t'sup. apply (Hsup_empty _ Hltts). set_solver. }
iDestruct (big_sepM_delete _ _ t' _ Hltts with "Hflow_r_frag") as "[[Hl_frac2 Hl_cons] Hflow_r_frag]".
iDestruct "Hl_cons" as "[#Hsub %Hprot]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iCombine "Hl Hprot" as "Hl".
iMod (own_update_2 with "Hflow_r Hl") as "[Hflow_r Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet (ts ∖ {[ t'sup ]})))
    (● (GSet (ts ∖ {[ t'sup ]})) ⋅ ◯ (GSet ∅)));
    first by rewrite lookup_fmap Hltts.
  apply auth_local_update=> //.
  apply gset_disj_dealloc_local_update. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] _]".
have Hwit : ∀ t2 tsub ts2, t2 ≠ t'sup →
    flow_r !! tsub = Some ts2 → t2 ∈ ts2 →
    ∃ tsub' ts2', <[t' := ts ∖ {[ t'sup ]}]> flow_r !! tsub' = Some ts2' ∧ t2 ∈ ts2'.
{ move=> t2 tsub ts2 Hne2 Hlk Hin2.
  destruct (decide (tsub = t')) as [->|?];
    last by exists tsub, ts2; rewrite lookup_insert_ne.
  assert (ts2 = ts) as -> by congruence.
  exists t', (ts ∖ {[ t'sup ]}). rewrite lookup_insert_eq. set_solver. }
iAssert (public_rel_map_r_auth pub_r) with "[Hmap_r Hmap_r_frag]" as "Hmap_r".
{ rewrite /public_rel_map_r_auth. iFrame. }
iModIntro. iSplitR "Hl_frac Hfrag"; last by iFrame.
iModIntro. iExists pub_l, pub_r, flow_l, (<[t' := ts ∖ {[ t'sup ]}]> flow_r).
iFrame. iFrame "#".
iSplitL "Hflow_r Hflow_r_frag Hl_frac2".
{ iSplitL; last by rewrite dom_insert_lookup_L.
  rewrite /public_rel_flow_r_auth fmap_insert.
  rewrite big_sepM_insert_delete.
  iFrame.
  iSplitR.
  - iSplit.
    + iApply (big_sepS_subseteq with "Hsub"). set_solver.
    + iPureIntro. move=> Hne'.
      have Hne0 : ts ≠ ∅ by set_solver.
      apply Hprot in Hne0 as [?|(tsub & ts2 & ? & ?)]; first eauto.
      right. by eapply Hwit.
  - iApply (big_sepM_mono with "Hflow_r_frag").
    iIntros (t2 ts2 Ht2) "(? & ? & %Hprot2)".
    iFrame. iPureIntro. move=> Hne2.
    have Hne2sup : t2 ≠ t'sup.
    { move=> ?. subst t2. apply lookup_delete_Some in Ht2 as [_ Ht2].
      by apply (Hsup_empty _ Ht2). }
    apply Hprot2 in Hne2 as [?|(tsub & ts3 & ? & ?)]; first eauto.
    right. by eapply Hwit. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit; first done.
  iPureIntro. move=> t2 ts2 Hpub.
  have Hne2sup : t2 ≠ t'sup.
  { move=> ?. subst t2. congruence. }
  destruct (HPriv_r _ _ Hpub) as [? | (tsub & ts3 & ? & ?)]; first eauto.
  right. by eapply Hwit. }
iSplit; first done.
iPureIntro. move=> t2 ts2 Hflow Hne2.
rewrite lookup_insert in Hflow; case_decide; last by eauto.
simplify_eq. apply (Hflow_r_cons _ _ Hltts). set_solver.
Qed.

Lemma public_rel_map_l_extend E t t' tsub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          private_rel_elem_l t t' ∗
          public_rel_map_l_frag t (Private {[ t' ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup with "Hflow_l Hprot") as "%Hprot".
iMod (own_update with "Hmap_l") as "[Hmap_l Hmap_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (Private {[ t' ]}) ⋅ ◯ (Private {[ t' ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t" as "[[Hmap_t_frag Hmap_t_frag'] Hmap_frag_t]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iModIntro. iSplitR "Hprot Hmap_frag_t Hmap_t_frag'"; last by iFrame.
iModIntro. iExists (<[t := Private {[ t' ]}]> pub_l), pub_r.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_t_frag".
{ iSplitL.
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit; last first.
  { iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; first naive_solver.
    by iApply "Hpub_rel". }
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; last done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_r_extend E t t' t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          private_rel_elem_r t t' ∗
          public_rel_map_r_frag t' (Private {[ t ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hprot Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_r_lookup with "Hflow_r Hprot") as "%Hprot".
iMod (own_update with "Hmap_r") as "[Hmap_r Hmap_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (Private {[ t ]}) ⋅ ◯ (Private {[ t ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t'" as "[[Hmap_t'_frag Hmap_t'_frag'] Hmap_frag_t']".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iModIntro. iSplitR "Hprot Hmap_frag_t' Hmap_t'_frag'"; last by iFrame.
iModIntro. iExists pub_l, (<[t' := Private {[ t ]}]> pub_r).
iFrame. iFrame "#".
iSplitL "Hmap_r Hmap_r_frag Hmap_t'_frag".
{ iSplitL.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit; last by iIntros (??) "%Hpub"; iApply "Hpub_rel".
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; first done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_l_extend_2 E a t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem_l (TNonce a) t' ∗
          public_rel_map_l_frag (TNonce a) (Private {[ t' ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htt".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & Hflow_r & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l (TNonce a) with "Hmeta_map_l Htt") as "%Hfresh".
iMod (own_update with "Hmap_l") as "[Hmap_l Hmap_frag_t]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a) (● (Private {[ t' ]}) ⋅ ◯ (Private {[ t' ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t" as "[[Hmap_t_frag Hmap_t_frag'] Hmap_frag_t]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iModIntro. iSplitR "Hmap_frag_t Hmap_t_frag'"; last by iFrame.
iModIntro. iExists (<[TNonce a := Private {[ t' ]}]> pub_l), pub_r, flow_l, flow_r.
iFrame. iFrame "#".
iSplitL "Hmap_l Hmap_l_frag Hmap_t_frag".
{ iSplitL.
  - rewrite /public_rel_map_l_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; first naive_solver.
    by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; last done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_r_extend_2 E t a' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem_r t (TNonce a') ∗
          public_rel_map_r_frag (TNonce a') (Private {[ t ]}).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  (Hflow_l & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_fresh pub_r (TNonce a') with "Hmeta_map_r Htts") as "%Hfresh".
iMod (own_update with "Hmap_r") as "[Hmap_r Hmap_frag_t']".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ (TNonce a') (● (Private {[ t ]}) ⋅ ◯ (Private {[ t ]})));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iDestruct "Hmap_frag_t'" as "[[Hmap_t'_frag Hmap_t'_frag'] Hmap_frag_t']".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iModIntro. iSplitR "Hmap_frag_t' Hmap_t'_frag'"; last by iFrame.
iModIntro. iExists pub_l, (<[TNonce a' := Private {[ t ]}]> pub_r), flow_l, flow_r.
iFrame. iFrame "#".
iSplitL "Hmap_r Hmap_r_frag Hmap_t'_frag".
{ iSplitL.
  - rewrite /public_rel_map_r_auth fmap_insert.
    rewrite big_sepM_insert=> //.
    iFrame.
  - rewrite dom_insert_L.
    rewrite big_sepS_insert; last by apply not_elem_of_dom.
    iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit; last by iIntros (??) "%Hpub"; iApply "Hpub_rel".
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; first done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma private_rel_extend E t t' tsub t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  protected_by_subterm_r t' t'sub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗ protected_by_subterm_r t' t'sub ∗
          private_rel_elem t t' ∗
          public_rel_map_l_frag t (Private {[ t' ]}) ∗
          public_rel_map_r_frag t' (Private {[ t ]}).
Proof.
iIntros (HE) "#Hctx Hprot Hprot1 Htt Htts".
iPoseProof (public_rel_map_l_extend t t' with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_rel_map_r_extend t t' with "Hctx Hprot1 Htts") as ">[? [??]]"=> //.
rewrite /private_rel_elem.
by iFrame.
Qed.

Lemma private_rel_extend_2 E a t' t'sub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_r t' t'sub -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_r t' t'sub ∗
          private_rel_elem (TNonce a) t' ∗
          public_rel_map_l_frag (TNonce a) (Private {[ t' ]}) ∗
          public_rel_map_r_frag t' (Private {[ TNonce a ]}).
Proof.
iIntros (HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_rel_map_l_extend_2 a t' with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_rel_map_r_extend (TNonce a) t' with "Hctx Hprot Htts") as ">[? [??]]"=> //.
rewrite /private_rel_elem.
by iFrame.
Qed.

Lemma private_rel_extend_3 E t a' tsub :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  protected_by_subterm_l t tsub -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> protected_by_subterm_l t tsub ∗
          private_rel_elem t (TNonce a') ∗
          public_rel_map_l_frag t (Private {[ TNonce a' ]}) ∗
          public_rel_map_r_frag (TNonce a') (Private {[ t ]}).
Proof.
iIntros (HE) "#Hctx Hprot Htt Htts".
iPoseProof (public_rel_map_l_extend t (TNonce a') with "Hctx Hprot Htt") as ">[? [??]]"=> //.
iPoseProof (public_rel_map_r_extend_2 t a' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /private_rel_elem.
by iFrame.
Qed.

Lemma private_rel_extend_4 E a a' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  term_token (TNonce a) (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec (TNonce a') (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> private_rel_elem (TNonce a) (TNonce a') ∗
          public_rel_map_l_frag (TNonce a) (Private {[ TNonce a' ]}) ∗
          public_rel_map_r_frag (TNonce a') (Private {[ TNonce a ]}).
Proof.
iIntros (HE) "#Hctx Htt Htts".
iPoseProof (public_rel_map_l_extend_2 a a' with "Hctx Htt") as ">[? ?]"=> //.
iPoseProof (public_rel_map_r_extend_2 a a' with "Hctx Htts") as ">[? ?]"=> //.
rewrite /private_rel_elem.
by iFrame.
Qed.

Lemma public_rel_map_l_grow E t ts t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  public_rel_map_l_frag t (Private ts) -∗
  |={E}=> private_rel_elem_l t t' ∗
          public_rel_map_l_frag t (Private (ts ∪ {[ t' ]})).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hl_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & Hmap_r & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltst".
iDestruct (big_sepM_delete _ _ t _ Hpltst with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Private (ts ∪ {[ t' ]}) ⋅ ◯ Private (ts ∪ {[ t' ]}))
    (● Private (ts ∪ {[ t' ]}) ⋅ ◯ Private (ts ∪ {[ t' ]})));
    first by rewrite lookup_fmap Hpltst /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_grow. }
iDestruct "Hl" as "[[Hl_frac Hl_frac2] #Hl']".
iAssert (own public_rel_map_l (◯ {[ t := ◯ Private {[ t' ]} ]})) as "Hl".
{ assert (Private (ts ∪ {[t']}) = Private ts ⋅ Private {[t']}) as -> by done.
  by iDestruct "Hl'" as "[_ Hl']". }
iClear "Hl'".
iModIntro. iSplitR "Hl_frac2"; last by iFrame; iFrame "#".
iModIntro. iExists (<[t := Private (ts ∪ {[ t' ]})]> pub_l), pub_r, flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_l_auth.
iAssert ([∗ map] k ↦ y ∈ {[ t := Private (ts ∪ {[ t' ]})]}, match y with
    | Private _ => own public_rel_map_l (◯ {[ k := ●{#1/2} y]})
    | _ => emp
    end)%I with "[Hl_frac]" as "Hl_frac".
{ by rewrite big_sepM_singleton. }
iCombine "Hmap_l_frag Hl_frac" as "Hmap_l_frag".
rewrite -big_sepM_union; last by apply map_disjoint_singleton_r, lookup_delete_eq.
rewrite -insert_union_singleton_r; last by apply lookup_delete_eq.
rewrite insert_delete_eq.
iFrame. iFrame "#".
iSplitL "Hmap_l".
{ rewrite fmap_insert dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; first naive_solver.
    by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; last done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; last done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_map_r_grow E t ts t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  public_rel_map_r_frag t' (Private ts) -∗
  |={E}=> private_rel_elem_r t t' ∗
          public_rel_map_r_frag t' (Private (ts ∪ {[ t ]})).
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  (Hmap_l & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprt'st".
iDestruct (big_sepM_delete _ _ t' _ Hprt'st with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]}))
    (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]})));
    first by rewrite lookup_fmap Hprt'st /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_grow. }
iDestruct "Hr" as "[[Hr_frac Hr_frac2] #Hr']".
iAssert (own public_rel_map_r (◯ {[ t' := ◯ Private {[ t ]} ]})) as "Hl".
{ assert (Private (ts ∪ {[t]}) = Private ts ⋅ Private {[t]}) as -> by done.
  by iDestruct "Hr'" as "[_ Hr']". }
iClear "Hr'".
iModIntro. iSplitR "Hr_frac2"; last by iFrame; iFrame "#".
iModIntro. iExists pub_l, (<[t' := Private (ts ∪ {[ t ]})]> pub_r), flow_l, flow_r.
rewrite /public_rel_inv /public_rel_map_r_auth.
iAssert ([∗ map] k ↦ y ∈ {[ t' := Private (ts ∪ {[ t ]})]}, match y with
    | Private _ => own public_rel_map_r (◯ {[ k := ●{#1/2} y]})
    | _ => emp
    end)%I with "[Hr_frac]" as "Hr_frac".
{ by rewrite big_sepM_singleton. }
iCombine "Hmap_r_frag Hr_frac" as "Hmap_r_frag".
rewrite -big_sepM_union; last by apply map_disjoint_singleton_r, lookup_delete_eq.
rewrite -insert_union_singleton_r; last by apply lookup_delete_eq.
rewrite insert_delete_eq.
iFrame. iFrame "#".
iSplitL "Hmap_r".
{ rewrite fmap_insert dom_insert_lookup_L=> //.
  iFrame. iFrame "#". }
iSplitL "Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplit; last by iIntros (??) "%Hpub"; iApply "Hpub_rel".
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplitL; first done.
  iPureIntro. move=> ??.
  rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit; first done.
iPureIntro. move=> ???.
rewrite lookup_insert; case_decide; naive_solver.
Qed.

(*
You will probably need a custom version of this lemma tailored to the
declassification you want to attempt.

Example:
Say you have (nonce, msg) ↦ Private {[ nonce', msg' ]}, where
PUB⟨msg, msg'⟩. flow_l !! nonce = {[ (nonce, msg) ]},
flow_r !! nonce' = {[ (nonce', msg') ]}.

When trying to change it to (nonce, msg) ↦ Public (nonce', msg'),
proving the public_rel_elem (nonce, msg) (nonce', msg') -∗
PUB⟨(nonce, msg), (nonce', msg')⟩ precondition will require that
you have public_rel_elem nonce nonce' in the recursive case.

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
t ↦ Private {[ t' ]} first (public_rel_extend_4).

Since public_rel_elem t t' → private_rel_elem t t', you can use it to
prove PUB.
*)
Lemma public_rel_extend E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (public_rel_elem t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  public_rel_map_l_frag t (Private {[ t' ]}) -∗
  public_rel_map_r_frag t' (Private {[ t ]}) -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Hl_frac Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltt'".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprtt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl". iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t') ⋅ ◯ (Public t'))
    (● (Public t') ⋅ ◯ (Public t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t) ⋅ ◯ (Public t))
    (● (Public t) ⋅ ◯ (Public t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
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
iSplitL "Hrel Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplitR.
  - iPureIntro. move=> ??.
    rewrite !lookup_insert; repeat case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; subst.
    + injection Hpub as <-. iApply "Hrel". iFrame "#".
    + by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_extend_2 E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (public_rel_elem t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  public_rel_map_l_frag t (Private {[ t' ]}) -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Hl_frac Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_lookup with "Hmap_l Hl_frac") as "%Hpltt'".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t _ Hpltt' with "Hmap_l_frag") as "[Hl_frac2 Hmap_l_frag]".
iCombine "Hl_frac Hl_frac2" as "Hl".
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iMod (own_update_2 with "Hmap_l Hl") as "[Hmap_l Hl]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t') ⋅ ◯ (Public t'))
    (● (Public t') ⋅ ◯ (Public t'))); first by rewrite lookup_fmap Hpltt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
iMod (own_update with "Hmap_r") as "[Hmap_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (Public t) ⋅ ◯ (Public t)));
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
iSplitL "Hrel Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplitR.
  - iPureIntro. move=> ??.
    rewrite !lookup_insert; repeat case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; subst.
    + injection Hpub as <-. iApply "Hrel". iFrame "#".
    + by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_extend_3 E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (public_rel_elem t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  public_rel_map_r_frag t' (Private {[ t ]}) -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Htt Hr_frac".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh".
iPoseProof (public_rel_map_r_lookup with "Hmap_r Hr_frac") as "%Hprtt'".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iDestruct (big_sepM_delete _ _ t' _ Hprtt' with "Hmap_r_frag") as "[Hr_frac2 Hmap_r_frag]".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iCombine "Hr_frac Hr_frac2" as "Hr".
iMod (own_update with "Hmap_l") as "[Hmap_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (Public t') ⋅ ◯ (Public t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh //. }
iMod (own_update_2 with "Hmap_r Hr") as "[Hmap_r Hr]".
{ apply auth_update.
  eapply (singleton_local_update _ _ _ _ (● (Public t) ⋅ ◯ (Public t))
    (● (Public t) ⋅ ◯ (Public t))); first by rewrite lookup_fmap Hprtt' /=.
  etransitivity.
  apply state_core_id_local_update.
  apply state_local_update_lock. }
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
iSplitL "Hrel Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplitR.
  - iPureIntro. move=> ??.
    rewrite !lookup_insert; repeat case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; subst.
    + injection Hpub as <-. iApply "Hrel". iFrame "#".
    + by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
Qed.

Lemma public_rel_extend_4 E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  (public_rel_elem t t' -∗ PUB⟨t, t'⟩) -∗
  protects_superterms_l t ∅ -∗
  protects_superterms_r t' ∅ -∗
  term_token t (↑cryptisN.@"public_rel".@"map") -∗
  term_token_spec t' (↑cryptisN.@"public_rel".@"map") -∗
  |={E}=> public_rel_elem t t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) Hrel Hprot Hprot1 Htt Htts".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  ([Hflow_l Hflow_l_frag] & [Hflow_r Hflow_r_frag] & #Hmeta_flow_l & #Hmeta_flow_r) &
                  Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (public_rel_map_l_fresh pub_l t with "Hmeta_map_l Htt") as "%Hfresh_l".
iPoseProof (public_rel_map_r_fresh pub_r t' with "Hmeta_map_r Htts") as "%Hfresh_r".
iPoseProof (public_rel_flow_l_lookup_2 with "Hflow_l Hprot") as "%Hfltts".
iPoseProof (public_rel_flow_r_lookup_2 with "Hflow_r Hprot1") as "%Hfrt'ts".
iMod (term_meta_set (cryptisN.@"public_rel".@"map") () with "Htt") as "#Hmeta_map_t"=> //.
iMod (term_meta_spec_set (cryptisN.@"public_rel".@"map") () with "Htts") as "#Hmeta_map_t'"=> //.
iMod (own_update with "Hmap_l") as "[Hmap_l Hl]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t (● (Public t') ⋅ ◯ (Public t')));
    last by apply auth_both_valid.
  rewrite lookup_fmap Hfresh_l //. }
iMod (own_update with "Hmap_r") as "[Hmap_r Hr]".
{ apply auth_update_alloc.
  apply (alloc_singleton_local_update _ t' (● (Public t) ⋅ ◯ (Public t)));
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
iSplitL "Hrel Hpub_consistent".
{ iDestruct "Hpub_consistent" as "[%Hpub_eq Hpub_rel]".
  iSplitR.
  - iPureIntro. move=> ??.
    rewrite !lookup_insert; repeat case_decide; naive_solver.
  - iIntros (??) "%Hpub".
    rewrite lookup_insert in Hpub; case_decide; subst.
    + injection Hpub as <-. iApply "Hrel". iFrame "#".
    + by iApply "Hpub_rel". }
iSplitL "HPriv_prot".
{ iDestruct "HPriv_prot" as "[%HPriv_l %HPriv_r]".
  iSplit.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver.
  - iPureIntro. move=> ??.
    rewrite lookup_insert; case_decide; naive_solver. }
iDestruct "Hflow_consistent" as "[%Hflow_l_cons %Hflow_r_cons]".
iSplit.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
- iPureIntro. move=> ???.
  rewrite lookup_insert; case_decide; naive_solver.
Qed.

Notation public_rel_map_l_own pub_l :=
  (own public_rel_map_l (● ((λ st, ● st ⋅ ◯ st) <$> pub_l))).
Notation public_rel_map_r_own pub_r :=
  (own public_rel_map_r (● ((λ st, ● st ⋅ ◯ st) <$> pub_r))).

(* Non-free terms (inverses, exponentials, products) are never publicly
   related, on either side. *)

#[local] Lemma publicly_related_nonfree_l t t' :
  is_inv t ∨ is_exp t ∨ is_mul t → PUB⟨t, t'⟩ -∗ False.
Proof.
case: t => /= [n|a b|a|kt s|k b|s|pt wf nf] H; try by case: H => [[]|[[]|[]]].
by iIntros "[]".
Qed.

#[local] Lemma publicly_related_nonfree_r t t' :
  is_inv t' ∨ is_exp t' ∨ is_mul t' → PUB⟨t, t'⟩ -∗ False.
Proof.
case: t' => /= [n|a b|a|kt s|k b|s|pt wf nf] H; try by case: H => [[]|[[]|[]]].
by case: t => /= *; iIntros "[]".
Qed.

#[local] Lemma nonfree_TInv t :
  negb (is_mul t) → negb (is_inv t) →
  is_inv (TInv t) ∨ is_exp (TInv t) ∨ is_mul (TInv t).
Proof. move=> Hmul Hinv. left. by rewrite is_inv_TInv. Qed.

#[local] Lemma nonfree_TExpN t ts :
  negb (is_exp t) → atomic ts → ts ≠ [] → invs_canceled ts →
  is_inv (TExpN t ts) ∨ is_exp (TExpN t ts) ∨ is_mul (TExpN t ts).
Proof.
move=> ????. right; left. rewrite is_exp_TExpN //. by case_bool_decide.
Qed.

#[local] Lemma nonfree_TMulN ts :
  wf_mul_list ts →
  is_inv (TMulN ts) ∨ is_exp (TMulN ts) ∨ is_mul (TMulN ts).
Proof. move=> ?. right; right. by apply is_mul_TMulN. Qed.

(* Constructor lemmas. *)

Lemma publicly_related_TInt n1 n2 :
  PUB⟨TInt n1, TInt n2⟩ ⊣⊢ ⌜n1 = n2⌝.
Proof. done. Qed.

Lemma publicly_related_TInt_term n (t2 : term) :
  PUB⟨TInt n, t2⟩ -∗ ⌜t2 = TInt n⌝.
Proof.
case: t2 => /= *; try by iIntros "[]".
by iIntros (->).
Qed.

Lemma publicly_related_term_TInt (t1 : term) n :
  PUB⟨t1, TInt n⟩ -∗ ⌜t1 = TInt n⌝.
Proof.
case: t1 => /= *; try by iIntros "[]".
by iIntros (->).
Qed.

Lemma publicly_related_TPair t11 t12 t21 t22 :
  PUB⟨TPair t11 t12, TPair t21 t22⟩ ⊣⊢
  PUB⟨t11, t21⟩ ∧ PUB⟨t12, t22⟩.
Proof. done. Qed.

Lemma publicly_related_TPair_term t11 t12 (t2 : term) :
  PUB⟨TPair t11 t12, t2⟩ -∗
  ∃ t21 t22, ⌜t2 = TPair t21 t22⌝.
Proof.
case: t2 => /= *; try by iIntros "[]".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_term_TPair (t1 : term) t21 t22 :
  PUB⟨t1, TPair t21 t22⟩ -∗
  ∃ t11 t12, ⌜t1 = TPair t11 t12⌝.
Proof.
case: t1 => /= *; try by iIntros "[]".
iIntros "_". by eauto.
Qed.

Lemma publicly_related_TNonce a1 a2 :
  PUB⟨TNonce a1, TNonce a2⟩ ⊣⊢
  public_rel_elem (TNonce a1) (TNonce a2).
Proof. done. Qed.

Lemma publicly_related_TKey kt1 kt2 t1 t2 :
  PUB⟨TKey kt1 t1, TKey kt2 t2⟩ ⊣⊢
  ⌜kt1 = kt2⌝ ∧
  match kt1 with
  | AEnc => PUB⟨t1, t2⟩ ∨
            (public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ private_rel_elem t1 t2)
  | ADec => PUB⟨t1, t2⟩
  | Sign => PUB⟨t1, t2⟩
  | Verify => PUB⟨t1, t2⟩ ∨
              (public_rel_elem (TKey kt1 t1) (TKey kt2 t2) ∧ private_rel_elem t1 t2)
  | SEnc => PUB⟨t1, t2⟩
  end.
Proof. done. Qed.

Lemma publicly_related_TSeal k1 k2 t1 t2 :
  PUB⟨TSeal k1 t1, TSeal k2 t2⟩ ⊣⊢
  (PUB⟨k1, k2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (public_rel_elem (TSeal k1 t1) (TSeal k2 t2) ∧
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
Proof. done. Qed.

Lemma publicly_related_THash t1 t2 :
  PUB⟨THash t1, THash t2⟩ ⊣⊢
  PUB⟨t1, t2⟩ ∨
  (public_rel_elem (THash t1) (THash t2) ∧ private_rel_elem t1 t2).
Proof. done. Qed.

(* Minted-ness. Every ghost fragment recorded in the invariant comes with a
   term_meta, which implies minted; structural cases recurse. *)

#[local] Lemma public_rel_elem_minted pub_l pub_r t t' :
  public_rel_map_l_own pub_l -∗
  public_rel_map_r_own pub_r -∗
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) -∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()) -∗
  public_rel_elem t t' -∗
  minted t ∗ minted_spec t'.
Proof.
iIntros "Hl Hr #Hmeta_l #Hmeta_r [Hlock_l Hlock_r]".
iDestruct (public_rel_map_l_lookup_locked with "Hl Hlock_l") as %Hl.
iDestruct (public_rel_map_r_lookup_locked with "Hr Hlock_r") as %Hr.
iSplit.
- iApply (term_meta_minted _ (cryptisN.@"public_rel".@"map") ()).
  iApply (big_sepS_elem_of _ _ t with "Hmeta_l"). by apply elem_of_dom.
- iApply (term_meta_spec_minted_spec _ (cryptisN.@"public_rel".@"map") ()).
  iApply (big_sepS_elem_of _ _ t' with "Hmeta_r"). by apply elem_of_dom.
Qed.

#[local] Lemma publicly_related_minted_aux pub_l pub_r t :
  public_rel_map_l_own pub_l -∗
  public_rel_map_r_own pub_r -∗
  ([∗ set] t ∈ dom pub_l, term_meta t (cryptisN.@"public_rel".@"map") ()) -∗
  ([∗ set] t' ∈ dom pub_r, term_meta_spec t' (cryptisN.@"public_rel".@"map") ()) -∗
  ∀ t', PUB⟨t, t'⟩ -∗ minted t ∗ minted_spec t'.
Proof.
elim: t => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH
           |t _ Hmul Hinv|t _ Hexp ts _ Hatom Htsne Htssort Htsninv
           |ts _ Hatom Htssort Htsninv Htsne];
  iIntros "Hl Hr #Hmeta_l #Hmeta_r" (t') "#Hpub".
- iDestruct (publicly_related_TInt_term with "Hpub") as %->.
  by rewrite minted_TInt minted_spec_TInt.
- iDestruct (publicly_related_TPair_term with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  iPoseProof (IHa with "Hl Hr Hmeta_l Hmeta_r Ha") as "#[??]".
  iPoseProof (IHb with "Hl Hr Hmeta_l Hmeta_r Hb") as "#[??]".
  rewrite minted_TPair minted_spec_TPair. by iSplit; iSplit.
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  by iApply (public_rel_elem_minted with "Hl Hr Hmeta_l Hmeta_r Hpub").
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[<- Hpub]".
  destruct kt;
    try (iDestruct "Hpub" as "[Hpub|[Hpub _]]";
         last by iApply (public_rel_elem_minted with "Hl Hr Hmeta_l Hmeta_r Hpub"));
    iPoseProof (IH with "Hl Hr Hmeta_l Hmeta_r Hpub") as "#[??]";
    rewrite minted_TKey minted_spec_TKey; by iSplit.
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[[Hk Hb]|(Hpub & _)]";
    last by iApply (public_rel_elem_minted with "Hl Hr Hmeta_l Hmeta_r Hpub").
  iPoseProof (IHk with "Hl Hr Hmeta_l Hmeta_r Hk") as "#[??]".
  iPoseProof (IHb with "Hl Hr Hmeta_l Hmeta_r Hb") as "#[??]".
  rewrite minted_TSeal minted_spec_TSeal. by iSplit; iSplit.
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[Hpub|[Hpub _]]";
    last by iApply (public_rel_elem_minted with "Hl Hr Hmeta_l Hmeta_r Hpub").
  iPoseProof (IH with "Hl Hr Hmeta_l Hmeta_r Hpub") as "#[??]".
  rewrite minted_THash minted_spec_THash. by iSplit.
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TInv Hmul Hinv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TExpN Hexp Hatom Htsne Htsninv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TMulN (conj Hatom (conj Htssort (conj Htsninv Htsne)))) with "Hpub") as "[]".
Qed.

Lemma publicly_related_minted E t t' :
  ↑cryptisN ⊆ E →
  cryptis_rel_ctx -∗
  PUB⟨t, t'⟩ -∗
  |={E}=> minted t ∗ minted_spec t'.
Proof.
iIntros (HE) "#(_ & _ & Hinv) #Hpub".
iInv "Hinv" as ">(%pub_l & %pub_r & %flow_l & %flow_r &
                  ([Hmap_l Hmap_l_frag] & [Hmap_r Hmap_r_frag] & #Hmeta_map_l & #Hmeta_map_r) &
                  Hflow & Hpub_consistent & HPriv_prot & Hflow_consistent)".
iPoseProof (publicly_related_minted_aux
             with "Hmap_l Hmap_r Hmeta_map_l Hmeta_map_r Hpub") as "#[??]".
iModIntro. iSplitL; last by iModIntro; iSplit.
iModIntro. iExists pub_l, pub_r, flow_l, flow_r. iFrame. by iFrame "#".
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
iIntros "#Hk #[[_ Ht]|(_ & _ & _ & #Hrest)]"; first done.
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
rewrite [term_of_aenc_key]unlock /=.
iSplit; first by iIntros "[_ ?]".
by iIntros "?"; iSplit.
Qed.

Lemma publicly_related_aenc_key_term (k1 : aenc_key) (k2 : term) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k2' : aenc_key), ⌜k2 = k2'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: k2 => /= [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt wf nf]; try by iIntros "[]".
iIntros "[<- _]". by iExists (AEncKey s2).
Qed.

Lemma publicly_related_term_aenc_key (k1 : term) (k2 : aenc_key) :
  PUB⟨k1, k2⟩ -∗
  ∃ (k1' : aenc_key), ⌜k1 = k1'⌝.
Proof.
rewrite [term_of_aenc_key]unlock /=.
case: k1 => /= [n1|a1 b1|a1|kt1 s1|k1 b1|s1|pt wf nf]; try by iIntros "[]".
iIntros "[-> _]". by iExists (AEncKey s1).
Qed.

Lemma publicly_related_aenc_key (k1 k2 : aenc_key) :
  PUB⟨Spec.pkey k1, Spec.pkey k2⟩ ⊣⊢
  PUB⟨k1, k2⟩ ∨
  (public_rel_elem (Spec.pkey k1) (Spec.pkey k2) ∧
   private_rel_elem (seed_of_aenc_key k1) (seed_of_aenc_key k2)).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
iSplit; first by iIntros "[_ ?]".
by iIntros "?"; iSplit.
Qed.

Lemma publicly_related_aenc_key_pkey_term (sk1 : aenc_key) (k2 : term) :
  PUB⟨Spec.pkey sk1, k2⟩ -∗
  ∃ (sk2' : aenc_key), ⌜k2 = Spec.pkey sk2'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: k2 => /= [n2|a2 b2|a2|kt2 s2|k2 b2|s2|pt wf nf]; try by iIntros "[]".
iIntros "[<- _]". by iExists (AEncKey s2).
Qed.

Lemma publicly_related_term_aenc_key_pkey (k1 : term) (sk2 : aenc_key) :
  PUB⟨k1, Spec.pkey sk2⟩ -∗
  ∃ (sk1' : aenc_key), ⌜k1 = Spec.pkey sk1'⌝.
Proof.
rewrite /Spec.pkey [term_of_aenc_key]unlock /=.
case: k1 => /= [n1|a1 b1|a1|kt1 s1|k1 b1|s1|pt wf nf]; try by iIntros "[]".
iIntros "[-> _]". by iExists (AEncKey s1).
Qed.

Lemma publicly_related_aenc (sk1 sk2 : aenc_key) N (t1 t2 : term) :
  PUB⟨Spec.enc (Spec.pkey sk1) (Tag N) t1,
      Spec.enc (Spec.pkey sk2) (Tag N) t2⟩ ⊣⊢
  (PUB⟨Spec.pkey sk1, Spec.pkey sk2⟩ ∧ PUB⟨t1, t2⟩) ∨
  (public_rel_elem (Spec.enc (Spec.pkey sk1) (Tag N) t1)
                   (Spec.enc (Spec.pkey sk2) (Tag N) t2) ∧
   private_rel_elem (Spec.pkey sk1) (Spec.pkey sk2) ∧
   private_rel_elem (Spec.tag (Tag N) t1) (Spec.tag (Tag N) t2) ∧
   □ (PUB⟨sk1, sk2⟩ → PUB⟨t1, t2⟩)).
Proof.
rewrite publicly_related_adec_key'.
rewrite /Spec.enc /Spec.pkey [term_of_aenc_key]unlock /= publicly_related_tag.
iSplit.
- iIntros "#[[Hk [_ Ht]]|(Hel & Hpk & Hpt & #Hrest)]"; first by iLeft; iSplit.
  iRight. do 3 (iSplit; first done).
  iIntros "!> #Hs". iDestruct "Hrest" as "[_ Hrest]".
  by iDestruct ("Hrest" with "Hs") as "[_ ?]".
- iIntros "#[[Hk Ht]|(Hel & Hpk & Hpt & #Hrest)]"; first by iLeft; iSplit; last iSplit.
  iRight. do 3 (iSplit; first done).
  iIntros "!>". iSplit; first done.
  iIntros "#Hs". iSplit; first done. by iApply "Hrest".
Qed.

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

#[local] Lemma public_rel_map_l_lookup_elem pub_l t t' :
  public_rel_map_l_own pub_l -∗
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
  public_rel_map_r_own pub_r -∗
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

#[local] Lemma is_immediate_subterm_TInt tsub n :
  ¬ is_immediate_subterm tsub (TInt n).
Proof. by inversion 1. Qed.

#[local] Lemma is_immediate_subterm_TPair tsub t1 t2 :
  is_immediate_subterm tsub (TPair t1 t2) → tsub = t1 ∨ tsub = t2.
Proof. inversion 1; eauto. Qed.

#[local] Lemma is_immediate_subterm_TKey tsub kt t :
  is_immediate_subterm tsub (TKey kt t) → tsub = t.
Proof. by inversion 1. Qed.

#[local] Lemma is_immediate_subterm_TSeal tsub k t :
  is_immediate_subterm tsub (TSeal k t) → tsub = k ∨ tsub = t.
Proof. inversion 1; eauto. Qed.

#[local] Lemma is_immediate_subterm_THash tsub t :
  is_immediate_subterm tsub (THash t) → tsub = t.
Proof. by inversion 1. Qed.

(** The pure facts recorded by the invariant about one side ([pub], [flow]
    stand for either [pub_l], [flow_l] or [pub_r], [flow_r]). *)
Record public_rel_facts pub flow : Prop := {
  public_rel_facts_flow_sub : ∀ tsub ts,
    flow !! tsub = Some ts → set_Forall (is_immediate_subterm tsub) ts;
  public_rel_facts_flow_chain : ∀ tsub ts,
    flow !! tsub = Some ts → ts ≠ ∅ →
    (∃ a, tsub = TNonce a) ∨ (∃ tsub' ts', flow !! tsub' = Some ts' ∧ tsub ∈ ts');
  public_rel_facts_Private_protected : public_rel_Private_l_protected pub flow;
  public_rel_facts_flow_consistent : public_rel_flow_l_consistent pub flow;
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
  public_rel_map_l_own pub_l -∗
  ∀ t', PUB⟨t, t'⟩ -∗ False.
Proof.
move=> Hfacts.
elim: t => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH
           |t _ Hmul Hinv|t _ Hexp ts _ Hatom Htsne Htssort Htsninv
           |ts _ Hatom Htssort Htsninv Htsne] Hprot;
  iIntros "Hauth" (t') "#Hpub".
- case: (public_rel_protected_inv Hfacts Hprot) => _ [[a Ha]|[tsub [ts [_ [_ Hsub]]]]] //.
  by case: (is_immediate_subterm_TInt Hsub).
- iDestruct (publicly_related_TPair_term with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: (public_rel_protected_inv Hfacts Hprot) => _ [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  case: (is_immediate_subterm_TPair Hsub) => ?; subst tsub.
  + iApply (IHa (or_intror Hprot') with "Hauth Ha").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[Hl _]".
  iDestruct (public_rel_map_l_lookup_locked with "Hauth Hl") as %Hlookup.
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub _.
  by case: (HnotPub _ Hlookup).
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[<- Hpub]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  move: (is_immediate_subterm_TKey Hsub) => ?; subst tsub.
  destruct kt;
    try (by iApply (IH (or_intror Hprot') with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[[Hl _] _]]";
     [ by iApply (IH (or_intror Hprot') with "Hauth Hpub")
     | iDestruct (public_rel_map_l_lookup_locked with "Hauth Hl") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  iDestruct "Hpub" as "[[Hk Hb]|[[Hl _] _]]"; last first.
  { iDestruct (public_rel_map_l_lookup_locked with "Hauth Hl") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  case: (is_immediate_subterm_TSeal Hsub) => ?; subst tsub.
  + iApply (IHk (or_intror Hprot') with "Hauth Hk").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t' => /= *; try by iDestruct "Hpub" as "[]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_l !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  move: (is_immediate_subterm_THash Hsub) => ?; subst tsub.
  iDestruct "Hpub" as "[Hpub|[[Hl _] _]]";
    first by iApply (IH (or_intror Hprot') with "Hauth Hpub").
  iDestruct (public_rel_map_l_lookup_locked with "Hauth Hl") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TInv Hmul Hinv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TExpN Hexp Hatom Htsne Htsninv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TMulN (conj Hatom (conj Htssort (conj Htsninv Htsne)))) with "Hpub") as "[]".
Qed.

#[local] Lemma publicly_related_protected_r pub_r flow_r t' :
  public_rel_facts pub_r flow_r →
  (∃ ts, pub_r !! t' = Some (Private ts)) ∨ (∃ ts, flow_r !! t' = Some ts ∧ ts ≠ ∅) →
  public_rel_map_r_own pub_r -∗
  ∀ t, PUB⟨t, t'⟩ -∗ False.
Proof.
move=> Hfacts.
elim: t' => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH
            |u _ Hmul Hinv|u _ Hexp ts _ Hatom Htsne Htssort Htsninv
            |ts _ Hatom Htssort Htsninv Htsne] Hprot;
  iIntros "Hauth" (t) "#Hpub".
- case: (public_rel_protected_inv Hfacts Hprot) => _ [[a Ha]|[tsub [ts [_ [_ Hsub]]]]] //.
  by case: (is_immediate_subterm_TInt Hsub).
- iDestruct (publicly_related_term_TPair with "Hpub") as %(a' & b' & ->).
  rewrite publicly_related_TPair. iDestruct "Hpub" as "[Ha Hb]".
  case: (public_rel_protected_inv Hfacts Hprot) => _ [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  case: (is_immediate_subterm_TPair Hsub) => ?; subst tsub.
  + iApply (IHa (or_intror Hprot') with "Hauth Ha").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[_ Hr]".
  iDestruct (public_rel_map_r_lookup_locked with "Hauth Hr") as %Hlookup.
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub _.
  by case: (HnotPub _ Hlookup).
- case: t => /= *; try by iDestruct "Hpub" as "[]".
  iDestruct "Hpub" as "[-> Hpub]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  move: (is_immediate_subterm_TKey Hsub) => ?; subst tsub.
  destruct kt;
    try (by iApply (IH (or_intror Hprot') with "Hauth Hpub"));
    (iDestruct "Hpub" as "[Hpub|[[_ Hr] _]]";
     [ by iApply (IH (or_intror Hprot') with "Hauth Hpub")
     | iDestruct (public_rel_map_r_lookup_locked with "Hauth Hr") as %Hlookup;
       by case: (HnotPub _ Hlookup) ]).
- case: t => /= *; try by iDestruct "Hpub" as "[]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  iDestruct "Hpub" as "[[Hk Hb]|[[_ Hr] _]]"; last first.
  { iDestruct (public_rel_map_r_lookup_locked with "Hauth Hr") as %Hlookup.
    by case: (HnotPub _ Hlookup). }
  case: (is_immediate_subterm_TSeal Hsub) => ?; subst tsub.
  + iApply (IHk (or_intror Hprot') with "Hauth Hk").
  + iApply (IHb (or_intror Hprot') with "Hauth Hb").
- case: t => /= *; try by iDestruct "Hpub" as "[]".
  case: (public_rel_protected_inv Hfacts Hprot) => HnotPub [[? ?]|[tsub [ts [Hts [Hin Hsub]]]]] //.
  have Hprot' : ∃ ts', flow_r !! tsub = Some ts' ∧ ts' ≠ ∅.
  { exists ts. split=> //. set_solver. }
  move: (is_immediate_subterm_THash Hsub) => ?; subst tsub.
  iDestruct "Hpub" as "[Hpub|[[_ Hr] _]]";
    first by iApply (IH (or_intror Hprot') with "Hauth Hpub").
  iDestruct (public_rel_map_r_lookup_locked with "Hauth Hr") as %Hlookup.
  by case: (HnotPub _ Hlookup).
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TInv Hmul Hinv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TExpN Hexp Hatom Htsne Htsninv) with "Hpub") as "[]".
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TMulN (conj Hatom (conj Htssort (conj Htsninv Htsne)))) with "Hpub") as "[]".
Qed.

(** If [t] is publicly related to [t2] and privately related to [t2'], then
    [t2 = t2'] (given injectivity for [t] itself). *)
#[local] Lemma publicly_related_private_rel_elem_l pub_l flow_l t :
  public_rel_facts pub_l flow_l →
  (public_rel_map_l_own pub_l -∗
   □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
   ∀ t2 t2', PUB⟨t, t2⟩ -∗ PUB⟨t, t2'⟩ -∗ ⌜t2 = t2'⌝) →
  public_rel_map_l_own pub_l -∗
  □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
  ∀ t2 t2', PUB⟨t, t2⟩ -∗ private_rel_elem_l t t2' -∗ ⌜t2 = t2'⌝.
Proof.
move=> Hfacts IH. iIntros "Hauth #Hrel" (t2 t2') "#H1 #[H2|H2]".
- iDestruct (public_rel_map_l_lookup_elem with "Hauth H2") as %[(ts & Hts & _)|Hpub].
  + by iPoseProof (publicly_related_protected_l Hfacts (or_introl (ex_intro _ ts Hts))
                    with "Hauth H1") as "[]".
  + iPoseProof ("Hrel" $! t t2' with "[//]") as "H2'".
    by iApply (IH with "Hauth Hrel H1 H2'").
- iDestruct (public_rel_map_l_lookup_locked with "Hauth H2") as %Hpub.
  iPoseProof ("Hrel" $! t t2' with "[//]") as "H2'".
  by iApply (IH with "Hauth Hrel H1 H2'").
Qed.

#[local] Lemma publicly_related_private_rel_elem_r pub_r flow_r t' :
  public_rel_facts pub_r flow_r →
  (public_rel_map_r_own pub_r -∗
   □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
   ∀ t1 t1', PUB⟨t1, t'⟩ -∗ PUB⟨t1', t'⟩ -∗ ⌜t1 = t1'⌝) →
  public_rel_map_r_own pub_r -∗
  □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
  ∀ t1 t1', PUB⟨t1, t'⟩ -∗ private_rel_elem_r t1' t' -∗ ⌜t1 = t1'⌝.
Proof.
move=> Hfacts IH. iIntros "Hauth #Hrel" (t1 t1') "#H1 #[H2|H2]".
- iDestruct (public_rel_map_r_lookup_elem with "Hauth H2") as %[(ts & Hts & _)|Hpub].
  + by iPoseProof (publicly_related_protected_r Hfacts (or_introl (ex_intro _ ts Hts))
                    with "Hauth H1") as "[]".
  + iPoseProof ("Hrel" $! t1' t' with "[//]") as "H2'".
    by iApply (IH with "Hauth Hrel H1 H2'").
- iDestruct (public_rel_map_r_lookup_locked with "Hauth H2") as %Hpub.
  iPoseProof ("Hrel" $! t1' t' with "[//]") as "H2'".
  by iApply (IH with "Hauth Hrel H1 H2'").
Qed.

#[local] Lemma publicly_related_part_bij_l pub_l flow_l t1 :
  public_rel_facts pub_l flow_l →
  public_rel_map_l_own pub_l -∗
  □ (∀ t t', ⌜pub_l !! t = Some (Public t')⌝ → PUB⟨t, t'⟩) -∗
  ∀ t2 t2', PUB⟨t1, t2⟩ -∗ PUB⟨t1, t2'⟩ -∗ ⌜t2 = t2'⌝.
Proof.
move=> Hfacts.
elim: t1 => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH
            |t _ Hmul Hinv|t _ Hexp ts _ Hatom Htsne Htssort Htsninv
            |ts _ Hatom Htssort Htsninv Htsne];
  iIntros "Hauth #Hrel" (t2 t2') "#H1 #H2".
- iDestruct (publicly_related_TInt_term with "H1") as %->.
  by iDestruct (publicly_related_TInt_term with "H2") as %->.
- iDestruct (publicly_related_TPair_term with "H1") as %(a2 & b2 & ->).
  iDestruct (publicly_related_TPair_term with "H2") as %(a2' & b2' & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct (IHa with "Hauth Hrel Ha Ha'") as %->.
  by iDestruct (IHb with "Hauth Hrel Hb Hb'") as %->.
- case: t2 => /= *; try by iDestruct "H1" as "[]".
  case: t2' => /= *; try by iDestruct "H2" as "[]".
  by iApply (public_rel_elem_agree_l with "H1 H2").
- have IH' := publicly_related_private_rel_elem_l Hfacts IH.
  case: t2 => /= *; try by iDestruct "H1" as "[]".
  case: t2' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[<- H1]". iDestruct "H2" as "[<- H2]".
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
  case: t2 => /= *; try by iDestruct "H1" as "[]".
  case: t2' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[[Hk1 Hb1]|(Hel1 & [Hpk1 _] & [Hpb1 _] & _)]";
  iDestruct "H2" as "[[Hk2 Hb2]|(Hel2 & [Hpk2 _] & [Hpb2 _] & _)]".
  + iDestruct (IHk with "Hauth Hrel Hk1 Hk2") as %->.
    by iDestruct (IHb with "Hauth Hrel Hb1 Hb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk1 Hpk2") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb1 Hpb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk2 Hpk1") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb2 Hpb1") as %->.
  + iDestruct (public_rel_elem_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- have IH' := publicly_related_private_rel_elem_l Hfacts IH.
  case: t2 => /= *; try by iDestruct "H1" as "[]".
  case: t2' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[H1|[Hel1 [Hpriv1 _]]]";
  iDestruct "H2" as "[H2|[Hel2 [Hpriv2 _]]]".
  + by iDestruct (IH with "Hauth Hrel H1 H2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->.
  + iDestruct (public_rel_elem_agree_l with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TInv Hmul Hinv) with "H1") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TExpN Hexp Hatom Htsne Htsninv) with "H1") as "[]".
- by iDestruct (publicly_related_nonfree_l _ (nonfree_TMulN (conj Hatom (conj Htssort (conj Htsninv Htsne)))) with "H1") as "[]".
Qed.

#[local] Lemma publicly_related_part_bij_r pub_r flow_r t2 :
  public_rel_facts pub_r flow_r →
  public_rel_map_r_own pub_r -∗
  □ (∀ t t', ⌜pub_r !! t' = Some (Public t)⌝ → PUB⟨t, t'⟩) -∗
  ∀ t1 t1', PUB⟨t1, t2⟩ -∗ PUB⟨t1', t2⟩ -∗ ⌜t1 = t1'⌝.
Proof.
move=> Hfacts.
elim: t2 => [n|a IHa b IHb|a|kt s IH|k IHk b IHb|s IH
            |t _ Hmul Hinv|t _ Hexp ts _ Hatom Htsne Htssort Htsninv
            |ts _ Hatom Htssort Htsninv Htsne];
  iIntros "Hauth #Hrel" (t1 t1') "#H1 #H2".
- iDestruct (publicly_related_term_TInt with "H1") as %->.
  by iDestruct (publicly_related_term_TInt with "H2") as %->.
- iDestruct (publicly_related_term_TPair with "H1") as %(a1 & b1 & ->).
  iDestruct (publicly_related_term_TPair with "H2") as %(a1' & b1' & ->).
  rewrite !publicly_related_TPair.
  iDestruct "H1" as "[Ha Hb]". iDestruct "H2" as "[Ha' Hb']".
  iDestruct (IHa with "Hauth Hrel Ha Ha'") as %->.
  by iDestruct (IHb with "Hauth Hrel Hb Hb'") as %->.
- case: t1 => /= *; try by iDestruct "H1" as "[]".
  case: t1' => /= *; try by iDestruct "H2" as "[]".
  by iApply (public_rel_elem_agree_r with "H1 H2").
- have IH' := publicly_related_private_rel_elem_r Hfacts IH.
  case: t1 => /= *; try by iDestruct "H1" as "[]".
  case: t1' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[-> H1]". iDestruct "H2" as "[-> H2]".
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
  case: t1 => /= *; try by iDestruct "H1" as "[]".
  case: t1' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[[Hk1 Hb1]|(Hel1 & [_ Hpk1] & [_ Hpb1] & _)]";
  iDestruct "H2" as "[[Hk2 Hb2]|(Hel2 & [_ Hpk2] & [_ Hpb2] & _)]".
  + iDestruct (IHk with "Hauth Hrel Hk1 Hk2") as %->.
    by iDestruct (IHb with "Hauth Hrel Hb1 Hb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk1 Hpk2") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb1 Hpb2") as %->.
  + iDestruct (IHk' with "Hauth Hrel Hk2 Hpk1") as %->.
    by iDestruct (IHb' with "Hauth Hrel Hb2 Hpb1") as %->.
  + iDestruct (public_rel_elem_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as -> ->.
- have IH' := publicly_related_private_rel_elem_r Hfacts IH.
  case: t1 => /= *; try by iDestruct "H1" as "[]".
  case: t1' => /= *; try by iDestruct "H2" as "[]".
  iDestruct "H1" as "[H1|[Hel1 [_ Hpriv1]]]";
  iDestruct "H2" as "[H2|[Hel2 [_ Hpriv2]]]".
  + by iDestruct (IH with "Hauth Hrel H1 H2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H1 Hpriv2") as %->.
  + by iDestruct (IH' with "Hauth Hrel H2 Hpriv1") as %->.
  + iDestruct (public_rel_elem_agree_r with "Hel1 Hel2") as %Heq.
    by injection Heq as ->.
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TInv Hmul Hinv) with "H1") as "[]".
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TExpN Hexp Hatom Htsne Htsninv) with "H1") as "[]".
- by iDestruct (publicly_related_nonfree_r _ (nonfree_TMulN (conj Hatom (conj Htssort (conj Htsninv Htsne)))) with "H1") as "[]".
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

End Rel.

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
iMod (own_alloc (● (∅ : gmapUR term (authUR stateUR))))
  as "[%public_rel_map_l Hmap_l]"; first by apply auth_auth_valid.
iMod (own_alloc (● (∅ : gmapUR term (authUR stateUR))))
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
rewrite /public_rel_Public_consistent /public_rel_Private_protected
        /public_rel_flow_consistent.
iSplit; last iSplit.
- iSplit.
  + iPureIntro. move=> t t'. rewrite !lookup_empty. by split=> ?.
  + iIntros (t t') "%Hcontra". by rewrite lookup_empty in Hcontra.
- iSplit; iPureIntro; move=> t ts; by rewrite lookup_empty => ?.
- iSplit; iPureIntro; move=> t ts; by rewrite lookup_empty => ?.
Qed.

From cryptis Require Import mathcomp_compat lib.
From mathcomp Require Import ssreflect.
From mathcomp Require eqtype ssrbool path.
From deriving Require Import deriving.
From stdpp Require Import gmap.
From iris.heap_lang Require Import notation.
From iris.heap_lang Require Import primitive_laws.
From cryptis.core.term Require Import base.

Lemma tsize_TPair t1 t2 :
  tsize (TPair t1 t2) = S (tsize t1 + tsize t2).
Proof. by rewrite tsize_eq. Qed.

Lemma tsize_TExpN_exp t ts t' : t' ∈ ts → tsize t' < tsize (TExpN t ts).
Proof.
elim: ts => [|t'' ts IH].
- by rewrite elem_of_nil.
- rewrite elem_of_cons; case => [->|/IH t'_ts].
  + by case: (tsize_TExpN_lt t ts t'').
  + case: (tsize_TExpN_lt t ts t'') => ??; lia.
Qed.

Lemma tsize_TExp_exp t1 t2 : tsize t2 < tsize (TExp t1 t2).
Proof. apply: tsize_TExpN_exp. rewrite elem_of_cons. by auto. Qed.

Canonical termO := leibnizO term.

Global Instance TExpN_proper : Proper ((=) ==> (≡ₚ) ==> (=)) TExpN.
Proof.
move=> t _ <- ts1 ts2 ts12.
by apply/TExpN_perm/(ssrbool.introT perm_Perm).
Qed.

Lemma TExpC2 g t1 t2 : TExpN g [t1; t2] = TExpN g [t2; t1].
Proof.
suff -> : [t1; t2] ≡ₚ [t2; t1] by [].
exact/Permutation_swap.
Qed.

Global Instance term_inhabited : Inhabited term.
Proof. exact: (populate (TInt 0)). Qed.

Global Instance aenc_key_inhabited : Inhabited aenc_key :=
  populate (AEncKey inhabitant).

Global Instance sign_key_inhabited : Inhabited sign_key :=
  populate (SignKey inhabitant).

Global Instance senc_key_inhabited : Inhabited senc_key :=
  populate (SEncKey inhabitant).

Definition term_eq_dec : EqDecision term :=
  Eval hnf in def_eq_decision _.
Global Existing Instance term_eq_dec.

Definition aenc_key_eq_dec : EqDecision aenc_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance aenc_key_eq_dec.

Definition senc_key_eq_dec : EqDecision senc_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance senc_key_eq_dec.

Definition sign_key_eq_dec : EqDecision sign_key :=
  Eval hnf in def_eq_decision _.
Global Existing Instance sign_key_eq_dec.

Inductive subterm (t : term) : term → Prop :=
| STRefl : subterm t t
| STPair1 t1 t2 of subterm t t1 : subterm t (TPair t1 t2)
| STPair2 t1 t2 of subterm t t2 : subterm t (TPair t1 t2)
| STKey kt t' of subterm t t' : subterm t (TKey kt t')
| STSeal1 k t' of subterm t k : subterm t (TSeal k t')
| STSeal2 k t' of subterm t t' : subterm t (TSeal k t')
| STHash t' of subterm t t' : subterm t (THash t')
| STExp1 t' ts of negb (is_exp t') & subterm t t' : subterm t (TExpN t' ts)
| STExp2 t' t'' ts of negb (is_exp t') & subterm t t'' & t'' ∈ ts : subterm t (TExpN t' ts).

Section ValOfTerm.

Fixpoint val_of_term_rec t : val :=
  match t with
  | TInt n =>
    (#TOp0_tag, (#TInt_tag, #n))
  | TPair t1 t2 =>
    (#TOp2_tag, (#TPair_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | TNonce l =>
    (#TOp0_tag, (#TNonce_tag, #l))%V
  | TKey kt t =>
    (#TOp1_tag, ((#TKey_tag, repr kt), val_of_term_rec t))%V
  | TSeal t1 t2 =>
    (#TOp2_tag, (#TSeal_tag, val_of_term_rec t1, val_of_term_rec t2))%V
  | THash t =>
    (#TOp1_tag, ((#THash_tag, #()), val_of_term_rec t))%V
  | TExpN' pt pts _ =>
    (#TExp_tag, (val_of_pre_term pt,
                 repr_list (map val_of_pre_term pts)))%V
  end.

Definition val_of_term_aux : seal val_of_term_rec. by eexists. Qed.
Definition val_of_term : term -> val := unseal val_of_term_aux.
Lemma val_of_term_unseal : val_of_term = val_of_term_rec.
Proof. exact: seal_eq. Qed.
Coercion val_of_term : term >-> val.
Global Instance repr_term : Repr term := val_of_term.

Global Instance repr_aenc_key : Repr aenc_key := λ k, repr (k : term).
Global Instance repr_senc_key : Repr senc_key := λ k, repr (k : term).
Global Instance repr_sign_key : Repr sign_key := λ k, repr (k : term).

Lemma val_of_pre_term_unfold t :
  val_of_pre_term (unfold_term t) = val_of_term t.
Proof.
rewrite val_of_term_unseal.
elim/term_ind': t => //=; try by move=> *; congruence.
Qed.

End ValOfTerm.

Global Instance val_of_term_inj : Inj (=) (=) val_of_term.
Proof.
move=> t1 t2 e_t1t2; apply: unfold_term_inj.
apply: val_of_pre_term_inj.
by rewrite !val_of_pre_term_unfold.
Qed.

Global Instance countable_term : Countable term.
Proof. exact: def_countable. Qed.

Global Instance countable_aenc_key : Countable aenc_key.
Proof. exact: def_countable. Qed.

Global Instance countable_sign_key : Countable sign_key.
Proof. exact: def_countable. Qed.

Global Instance countable_senc_key : Countable senc_key.
Proof. exact: def_countable. Qed.

Global Instance infinite_term : Infinite term.
Proof.
pose int_of_term (t : term) :=
  if t is TInt n then Some n else None.
apply (inj_infinite TInt int_of_term).
by move=> n; rewrite /int_of_term.
Qed.

Definition term_height t :=
  PreTerm.height (unfold_term t).

Definition nonces_of_term_def (t : term) :=
  nonces_of_pre_term (unfold_term t).
Arguments nonces_of_term_def /.
Definition nonces_of_term_aux : seal nonces_of_term_def. by eexists. Qed.
Definition nonces_of_term := unseal nonces_of_term_aux.
Lemma nonces_of_term_unseal : nonces_of_term = nonces_of_term_def.
Proof. exact: seal_eq. Qed.

Lemma nonces_of_termE' t :
  nonces_of_term t =
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | TNonce l => {[l]}
  | TKey _ t => nonces_of_term t
  | TSeal t1 t2 => nonces_of_term t1 ∪ nonces_of_term t2
  | THash t => nonces_of_term t
  | TExpN' pt pts _ => nonces_of_pre_term (PreTerm.PTExp pt pts)
  end.
Proof.
by rewrite nonces_of_term_unseal; case: t => //=.
Qed.

Lemma nonces_of_term_TExpN t ts :
  nonces_of_term (TExpN t ts)
  = nonces_of_term t ∪ ⋃ map nonces_of_term ts.
Proof.
rewrite nonces_of_term_unseal /nonces_of_term_def unfold_TExpN.
rewrite /PreTerm.exp seq.size_map seq.size_eq0.
case: eqtype.eqP => [->|tsN0] //=; first set_solver.
rewrite -[@seq.cat]/@app -[@seq.map]/@map; set ts' := _ ++ _.
set ts'' := path.sort _ _; have -> : ts'' ≡ₚ ts'.
  by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
rewrite /ts' map_app union_list_app_L map_map [LHS]assoc_L; congr (_ ∪ _).
rewrite -unfold_base -unfold_exps -[@seq.map]/@map.
case: (ssrbool.boolP (is_exp t)) => [tX|tNX].
- rewrite unfold_base /= -[ @map ]/@seq.map unfold_exps /=.
  by case: (t) tX => //= pt pts ? _.
- rewrite base_expN // exps_expN //=; set_solver.
Qed.

Definition nonces_of_termE := (nonces_of_term_TExpN, nonces_of_termE').

Fixpoint ssubterms_pre_def t : gset term :=
  let subterms_pre_def t := {[fold_term t]} ∪ ssubterms_pre_def t in
  match t with
  | PreTerm.PT0 (O0Int _) => ∅
  | PreTerm.PT2 O2Pair t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT0 (O0Nonce _) => ∅
  | PreTerm.PT1 (O1Key _) t => subterms_pre_def t
  | PreTerm.PT2 O2Seal t1 t2 => subterms_pre_def t1 ∪ subterms_pre_def t2
  | PreTerm.PT1 O1Hash t => subterms_pre_def t
  | PreTerm.PTExp t ts => subterms_pre_def t ∪ ⋃ map subterms_pre_def ts
  end.

Definition subterms_def t := {[t]} ∪ ssubterms_pre_def (unfold_term t).
Arguments subterms_def /.
Definition subterms_aux : seal subterms_def. by eexists. Qed.
Definition subterms := unseal subterms_aux.
Lemma subterms_unseal : subterms = subterms_def.
Proof. exact: seal_eq. Qed.

Lemma subtermsE' t :
  subterms t =
  {[t]} ∪
  match t with
  | TInt _ => ∅
  | TPair t1 t2 => subterms t1 ∪ subterms t2
  | TNonce _ => ∅
  | TKey _ t => subterms t
  | TSeal t1 t2 => subterms t1 ∪ subterms t2
  | THash t => subterms t
  | TExpN' pt pts _ => ssubterms_pre_def (PreTerm.PTExp pt pts)
  end.
Proof.
rewrite subterms_unseal /=.
case: t =>> //=; try by rewrite ?unfold_termK.
Qed.

Lemma subterms_TExpN t ts :
  negb (is_exp t) →
  subterms (TExpN t ts) = {[TExpN t ts]} ∪ (subterms t ∪ ⋃ (subterms <$> ts)).
Proof.
rewrite subterms_unseal /subterms_def => /is_trueP tNX.
rewrite unfold_TExpN /PreTerm.exp seq.size_map seq.size_eq0.
case: (ssrbool.altP eqtype.eqP) => [->|tsN0] /=.
  rewrite TExpN0; set_solver.
rewrite -unfold_base unfold_termK base_expN //; congr (_ ∪ (_ ∪ _)).
rewrite -unfold_exps exps_expN //=.
rewrite (_ : path.sort _ _ ≡ₚ seq.map unfold_term ts); last first.
  by apply/(ssrbool.elimT perm_Perm); rewrite path.perm_sort.
by rewrite map_map; congr (⋃ _); apply: map_ext => ?; rewrite unfold_termK.
Qed.

Definition subtermsE := (subterms_TExpN, subtermsE').

Ltac solve_subtermsP :=
  intros;
  repeat match goal with
  | H : context[subterms (?X ?Y)] |- _ =>
      rewrite [subterms (X Y)]subtermsE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma subtermsP t1 t2 : subterm t1 t2 ↔ t1 ∈ subterms t2.
Proof.
split.
- elim: t2 /; try by intros; rewrite subtermsE; set_solver.
  move=> t' t'' ts t'NX _ IH ?; rewrite subtermsE //.
  do 2![rewrite elem_of_union; right].
  rewrite elem_of_union_list; exists (subterms t''); split => //.
  by rewrite elem_of_list_fmap; eauto.
- elim: t2; try by solve_subtermsP.
  move=> t IHt /is_trueP tNX ts IHts /is_trueP tsN0 _.
  rewrite subtermsE // !elem_of_union elem_of_union_list elem_of_singleton.
  case=> [-> | [/IHt ?|sub]]; eauto using subterm.
  case: sub => _ [] /elem_of_list_fmap [] t' [] -> t'_ts sub.
  suffices: subterm t1 t' by eauto using subterm.
  elim: {t IHt tNX tsN0} ts IHts t'_ts sub => /= [_|t ts IH [IHt IHts]].
    by rewrite elem_of_nil.
  by rewrite elem_of_cons; case => [->|?] //; eauto.
Qed.

Ltac solve_nonces_of_termP :=
  intros;
  repeat match goal with
  | H : context[nonces_of_term (?X ?Y)] |- _ =>
      rewrite [nonces_of_term (X Y)]nonces_of_termE /= in H
  | H : _ ∈ {[_]} |- _ =>
      rewrite elem_of_singleton in H;
      rewrite {}H
  | H : _ ∈ _ ∪ _ |- _ =>
      rewrite elem_of_union in H;
      destruct H
  | H : _ ∈ ∅ |- _ =>
      rewrite elem_of_empty in H;
      destruct H
  | H1 : ?P, H2 : ?P -> ?Q |- _ =>
      move/(_ H1) in H2
  end;
  eauto using subterm.

Lemma nonces_of_termP a t : subterm (TNonce a) t ↔ a ∈ nonces_of_term t.
Proof.
split.
- elim: t /; try by intros; rewrite nonces_of_termE; set_solver.
  move=> t t' ts _ IH t'_ts.
  rewrite nonces_of_termE elem_of_union; right.
  rewrite elem_of_union_list; exists (nonces_of_term t'); split => //.
  by rewrite elem_of_list_fmap; eauto.
- elim: t; try by solve_nonces_of_termP.
  move=> t IHt /is_trueP tNX ts IHts _ _.
  rewrite nonces_of_termE !elem_of_union elem_of_union_list.
  case=> [/IHt ?|sub]; eauto using subterm.
  case: sub => _ [] /elem_of_list_fmap [] t' [] -> t'_ts sub.
  suffices: subterm (TNonce a) t' by eauto using subterm.
  elim: {t tNX IHt} ts IHts t'_ts sub => /= [_|t ts IH [IHt IHts]].
    by rewrite elem_of_nil.
  by rewrite elem_of_cons; case => [->|?] //; eauto.
Qed.

Lemma subterm_nonces_of_term t1 t2 :
  subterm t1 t2 → nonces_of_term t1 ⊆ nonces_of_term t2.
Proof.
elim: t2 / => //.
- move=> ???.
  rewrite [nonces_of_term (TPair _ _)]nonces_of_termE.
  set_solver.
- move=> ???.
  rewrite [nonces_of_term (TPair _ _)]nonces_of_termE.
  set_solver.
- move=> ???.
  rewrite [nonces_of_term (TKey _ _)]nonces_of_termE.
  set_solver.
- move=> ???.
  rewrite [nonces_of_term (TSeal _ _)]nonces_of_termE.
  set_solver.
- move=> ???.
  rewrite [nonces_of_term (TSeal _ _)]nonces_of_termE.
  set_solver.
- move=> ???.
  rewrite [nonces_of_term (THash _)]nonces_of_termE.
  set_solver.
- move=> ???. rewrite nonces_of_term_TExpN. set_solver.
- move=> t2 t2' ts ? sub sub' t2'_ts.
  rewrite nonces_of_term_TExpN.
  have ?: nonces_of_term t2' ⊆ ⋃ map nonces_of_term ts.
    move=> t t_t2'. rewrite elem_of_union_list.
    exists (nonces_of_term t2'). split => //.
    rewrite elem_of_list_fmap. by eauto.
  set_solver.
Qed.

Definition Tag_def (N : namespace) :=
  TInt (Zpos (encode N)).
Definition Tag_aux : seal Tag_def. by eexists. Qed.
Definition Tag := unseal Tag_aux.
Lemma Tag_unseal : Tag = Tag_def. Proof. exact: seal_eq. Qed.

Global Instance Tag_inj : Inj (=) (=) Tag.
Proof. by rewrite Tag_unseal => ?? [] /(inj _ _ _). Qed.

Module Spec.

Implicit Types N : term.

Definition is_seal_key k :=
  match k with
  | TKey AEnc _ | TKey Sign _ | TKey SEnc _ => true
  | _ => false
  end.

Definition public_key_type kt :=
  match kt with
  | AEnc | Verify => true
  | _ => false
  end.

Definition skey t :=
  match t with
  | TKey AEnc t => TKey ADec t
  | TKey Verify t => TKey Sign t
  | _ => t
  end.

Definition pkey t :=
  match t with
  | TKey ADec t => TKey AEnc t
  | TKey Sign t => TKey Verify t
  | _ => t
  end.

Lemma aenc_pkey_inj (sk1 sk2 : aenc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma sign_pkey_inj (sk1 sk2 : sign_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Lemma senc_pkey_inj (sk1 sk2 : senc_key) :
  pkey sk1 = pkey sk2 → sk1 = sk2.
Proof. by rewrite keysE; case: sk1 sk2 => [?] [?] [->]. Qed.

Definition tag_def N (t : term) :=
  TPair N t.
Definition tag_aux : seal tag_def. by eexists. Qed.
Definition tag := unseal tag_aux.
Lemma tag_unseal : tag = tag_def. Proof. exact: seal_eq. Qed.

Lemma is_nonce_tag N t : is_nonce (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Lemma is_exp_tag N t : is_exp (tag N t) = false.
Proof. by rewrite tag_unseal. Qed.

Definition untag_def N (t : term) :=
  match t with
  | TPair N' t =>
    if decide (N = N') then Some t else None
  | _ => None
  end.
Definition untag_aux : seal untag_def. by eexists. Qed.
Definition untag := unseal untag_aux.
Lemma untag_unseal : untag = untag_def. Proof. exact: seal_eq. Qed.

Lemma tagK N t : untag N (tag N t) = Some t.
Proof.
rewrite untag_unseal tag_unseal /untag_def /tag_def /=.
by rewrite decide_True_pi.
Qed.

#[global]
Instance tag_inj : Inj2 (=) (=) (=) tag.
Proof.
rewrite tag_unseal /tag_def => c1 t1 c2 t2 [] e ->.
split=> //; by apply: inj e.
Qed.

Lemma untagK N t1 t2 :
  untag N t1 = Some t2 ->
  t1 = tag N t2.
Proof.
rewrite untag_unseal tag_unseal /=.
case: t1=> [] // N' t1 /=.
by case: decide => // <- [<-].
Qed.

Lemma untag_tag_ne N1 N2 t :
  N1 ≠ N2 →
  Spec.untag N1 (Spec.tag N2 t) = None.
Proof.
move=> neq; rewrite Spec.untag_unseal Spec.tag_unseal /=.
rewrite decide_False //.
Qed.

Variant untag_spec N t : option term → Type :=
| UntagSome t' of t = Spec.tag N t' : untag_spec N t (Some t')
| UntagNone of (∀ t', t ≠ Spec.tag N t') : untag_spec N t None.

Lemma untagP N t : untag_spec N t (Spec.untag N t).
Proof.
case e: (Spec.untag N t) => [t'|]; constructor.
- by rewrite (Spec.untagK _ _ _ e).
- move=> t' e'; by rewrite e' Spec.tagK in e.
Qed.

Definition to_int t :=
  if t is TInt n then Some n else None.

Variant to_int_spec t : option Z → Type :=
| AsIntSome n of t = TInt n : to_int_spec t (Some n)
| AsIntNone of (∀ n, t ≠ TInt n) : to_int_spec t None.

Lemma to_intP t : to_int_spec t (Spec.to_int t).
Proof. by case: t => *; constructor; congruence. Qed.

Definition untuple t :=
  match t with
  | TPair t1 t2 => Some (t1, t2)
  | _ => None
  end.

Fixpoint proj t n {struct t} :=
  match t, n with
  | TPair t _, 0 => Some t
  | TPair _ t, S n => proj t n
  | _, _ => None
  end.

Definition to_key k : option (key_type * term) :=
  match k with
  | TKey kt t => Some (kt, t)
  | _ => None
  end.

Definition open_key k : option term :=
  match to_key k with
  | Some (kt, t) =>
      match kt with
      | AEnc => Some (TKey ADec t)
      | Sign => Some (TKey Verify t)
      | SEnc => Some (TKey SEnc t)
      | _ => None
      end
  | _ => None
  end.

Lemma open_key_aenc (sk : aenc_key) :
  open_key (Spec.pkey sk) = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_sign (sk : sign_key) :
  open_key sk = Some (Spec.pkey sk).
Proof. by rewrite keysE. Qed.

Lemma open_key_senc (sk : senc_key) :
  open_key sk = @Some term sk.
Proof. by rewrite keysE. Qed.

Lemma open_key_aencK pk (sk : aenc_key) :
  open_key pk = @Some term sk → pk = pkey sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: pk => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_signK k (sk : sign_key) :
  open_key k = Some (Spec.pkey sk) → k = sk.
Proof.
rewrite keysE; case: sk => seed /=.
by case: k => //= - [] // ?; case=> ->.
Qed.

Lemma open_key_sencK k' (k : senc_key) :
  open_key k' = @Some term k → k' = k.
Proof.
rewrite keysE; case: k => seed /=.
by case: k' => //= - [] // ?; case=> ->.
Qed.

Definition open k t : option term :=
  match t with
  | TSeal k_t t =>
    if decide (open_key k_t = Some k) then Some t else None
  | _ => None
  end.

Variant open_spec k t : option term → Type :=
| OpenSome k_t t'
  of open_key k_t = Some k & t = TSeal k_t t'
  : open_spec k t (Some t')
| OpenNone : open_spec k t None.

Lemma openP k t : open_spec k t (open k t).
Proof.
case: t; eauto using open_spec => k_t t /=.
by case: decide => [e|_]; eauto using open_spec.
Qed.

Definition is_key t :=
  match t with
  | TKey kt _ => Some kt
  | _ => None
  end.

Variant is_key_spec t : option key_type → Type :=
| IsKeySome kt k of t = TKey kt k : is_key_spec t (Some kt)
| IsKeyNone of (∀ kt k, t ≠ TKey kt k) : is_key_spec t None.

Lemma is_keyP t : is_key_spec t (is_key t).
Proof.
case: t; try by right.
by move=> kt t; eleft.
Qed.

Definition has_key_type kt t :=
  match is_key t with
  | Some kt' => bool_decide (kt = kt')
  | None => false
  end.

Definition of_list_aux : seal (foldr TPair (TInt 0)). by eexists. Qed.
Definition of_list := unseal of_list_aux.
Lemma of_list_unseal : of_list = foldr TPair (TInt 0).
Proof. exact: seal_eq. Qed.

Lemma of_list_tsize t ts : t ∈ ts → tsize t < tsize (of_list ts).
Proof.
rewrite of_list_unseal; elim: ts => [|t' ts IH] //=.
- by rewrite elem_of_nil.
- rewrite tsize_TPair elem_of_cons; case=> [<-|/IH t_ts]; lia.
Qed.

Lemma is_nonce_of_list ts : is_nonce (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Lemma is_exp_of_list ts : is_exp (of_list ts) = false.
Proof. by rewrite of_list_unseal; case: ts. Qed.

Fixpoint to_list t : option (list term) :=
  match t with
  | TInt 0 => Some []
  | TPair t1 t2 =>
    match to_list t2 with
    | Some l => Some (t1 :: l)
    | None => None
    end
  | _ => None
  end.

Lemma of_listK l : to_list (of_list l) = Some l.
Proof. rewrite of_list_unseal; by elim: l => //= t l ->. Qed.

Lemma to_listK t ts :
  to_list t = Some ts →
  t = of_list ts.
Proof.
rewrite of_list_unseal /=; elim/term_ind': t ts => //.
  by case=> [] // _ [<-].
move=> t _ ts' IH /= ts.
case e: to_list => [ts''|] // [<-].
by rewrite /= (IH _ e).
Qed.

Inductive to_list_spec : term → option (list term) → Type :=
| ToListSome ts : to_list_spec (of_list ts) (Some ts)
| ToListNone t  : to_list_spec t None.

Lemma to_listP t : to_list_spec t (to_list t).
Proof.
case e: to_list => [ts|]; last constructor.
by rewrite (to_listK _ _ e); constructor.
Qed.

Lemma of_list_inj : Inj eq eq of_list.
Proof.
move=> ts1 ts2 e; apply: Some_inj.
by rewrite -of_listK e of_listK.
Qed.

Definition enc k c t := TSeal k (tag c t).

Definition dec k c t :=
  match open k t with
  | Some t => untag c t
  | None => None
  end.

Variant dec_spec k c t : option term → Type :=
| DecSome k_t t'
  of open_key k_t = Some k
  &  t = TSeal k_t (tag c t')
  : dec_spec k c t (Some t')
| DecNone : dec_spec k c t None.

Lemma decP k c t : dec_spec k c t (dec k c t).
Proof.
rewrite /dec.
case: openP; eauto using dec_spec.
move=> {}k_t {}t e ->.
case: untagP; eauto using dec_spec.
move=> {}t ->; eauto using dec_spec.
Qed.

Lemma decK k1 k2 c t t' :
  open_key k1 = Some k2 →
  dec k2 c t = Some t' →
  t = TSeal k1 (tag c t').
Proof.
rewrite /Spec.dec /=.
case: t => [] //= k_t t.
case: decide => // k_t_k2 k1_k2 /untagK <-.
rewrite /open_key in k_t_k2 k1_k2.
case: k_t k1 => [] // kt1 ? [] //= kt2 ? in k_t_k2 k1_k2 *.
case: kt1 kt2 => [] //= [] //= in k_t_k2 k1_k2 *; congruence.
Qed.

Definition zero : term := TInt 0.

End Spec.

Arguments repr_term /.
Arguments Spec.tag_def /.
Arguments Spec.untag_def /.

#[global]
Existing Instance Spec.of_list_inj.

Lemma subterm_tag c t1 t2 : subterm t1 t2 → subterm t1 (Spec.tag c t2).
Proof. by rewrite Spec.tag_unseal; eauto using subterm. Qed.

#[global]
Hint Resolve STRefl : core.

Lemma exps_TExpN t ts : exps (TExpN t ts) ≡ₚ exps t ++ ts.
Proof.
apply/(ssrbool.elimT perm_Perm).
rewrite exps_TExpN.
by rewrite path.perm_sort seq.perm_cat2l.
Qed.

Lemma is_exp_TExpN t ts :
  is_exp (TExpN t ts) = implb (bool_decide (ts = [])) (is_exp t).
Proof.
rewrite is_exp_TExpN -eq_op_bool_decide implb_orb.
by case: ts.
Qed.

Lemma base_exps_inj t1 t2 :
  base t1 = base t2 →
  exps t1 ≡ₚ exps t2 →
  t1 = t2.
Proof.
move=> eb /(ssrbool.introT perm_Perm) ?.
by apply: base_exps_inj.
Qed.

Lemma TExp_TExpN t1 ts1 t2 : TExp (TExpN t1 ts1) t2 = TExpN t1 (t2 :: ts1).
Proof.
by rewrite TExpNA -[@seq.cat]/@app [_ ++ _]comm.
Qed.

Lemma base_expN t : ¬ is_exp t → base t = t.
Proof.
move=> tNX; apply: base_expN.
apply/(ssrbool.introN ssrbool.idP).
by rewrite is_trueP.
Qed.

Lemma exps_expN t : ¬ is_exp t → exps t = [].
Proof.
move=> tNX; apply: exps_expN.
apply/(ssrbool.introN ssrbool.idP).
by rewrite is_trueP.
Qed.

Lemma TExp0 t : TExpN t [] = t.
Proof.
apply: base_exps_inj; first by rewrite base_TExpN.
by rewrite exps_TExpN app_nil_r.
Qed.

Lemma is_exp_base t : ¬ is_exp (base t).
Proof.
rewrite (ssrbool.negbTE (is_exp_base t)) /=. by auto.
Qed.
Hint Resolve is_exp_base : core.

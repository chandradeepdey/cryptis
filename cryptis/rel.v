From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import gset_bij mono_list.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term minted public.

From reloc Require Import reloc.
From cryptis.core Require Import minted_spec.
From cryptis.core Require Import term_meta_spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation public_relGpreS Σ := (inG Σ (gset_bijUR term term)).

Class public_relGS Σ := Public_relGS {
  #[local] public_relGpreS_inG :: public_relGpreS Σ;
  public_rel_name  : gname;
}.

Definition public_relΣ : gFunctors := #[GFunctor (gset_bijUR term term)].

Global Instance subG_public_relGpreS Σ : subG public_relΣ Σ → public_relGpreS Σ.
Proof. solve_inG. Qed.

Implicit Types (pub: gset (term * term)) (t: term).

Section Rel.

Context `{!relocG Σ, !public_relGS Σ}.

Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Definition public_rel_auth pub : iProp :=
  own public_rel_name (gset_bij_auth (DfracOwn 1) pub).

Definition public_rel_frag t1 t2 : iProp :=
  own public_rel_name (gset_bij_elem t1 t2).

Definition cryptis_rel_N := nroot .@ "cryptis_rel".

Definition double_squiggle_pre (P: term -d> term -d> iPropO) t1 t2 :=
  (□ (∀ t2', ▷ P t1 t2' -∗ ▷ ⌜t2 = t2'⌝) ∧
  □ (∀ t1', ▷ P t1' t2 -∗ ▷ ⌜t1 = t1'⌝))%I.

#[local] Instance double_squiggle_pre_persistent P t1 t2 : Persistent (double_squiggle_pre P t1 t2).
Proof. apply _. Qed.

Definition publicly_related_pre (P: term -d> term -d> iPropO) : term -d> term -d> iPropO :=
  fix publicly_related_pre t1 t2 {struct t1} : iProp :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      publicly_related_pre t11 t21 ∧ publicly_related_pre t12 t22
  | TNonce l1, TNonce l2 => public_rel_frag t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => publicly_related_pre t1' t2' ∨
              (public_rel_frag t1 t2 ∧ double_squiggle_pre P t1' t2')
    | ADec => publicly_related_pre t1' t2'
    | Sign => publicly_related_pre t1' t2'
    | Verify => publicly_related_pre t1' t2' ∨
                (public_rel_frag t1 t2 ∧ double_squiggle_pre P t1' t2')
    | SEnc => publicly_related_pre t1' t2'
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (publicly_related_pre k1 k2 ∧ publicly_related_pre t1' t2') ∨
    (public_rel_frag t1 t2 ∧ double_squiggle_pre P k1 k2 ∧ double_squiggle_pre P t1' t2' ∧
    □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | AEnc => publicly_related_pre k1 k2 → publicly_related_pre t1' t2'
        | ADec => False
        | Sign => publicly_related_pre t1' t2' → publicly_related_pre k1 k2
        | Verify => False
        | SEnc => publicly_related_pre k1 k2 → publicly_related_pre t1' t2'
        end
      | _, _ => False
      end))
  | THash t1', THash t2' =>
    publicly_related_pre t1' t2' ∨
    (public_rel_frag t1 t2 ∧ double_squiggle_pre P t1' t2')
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

Local Definition publicly_related_def : term -d> term -d> iPropO :=
  fixpoint (publicly_related_pre).
Local Definition publicly_related_aux : seal publicly_related_def. Proof. by eexists. Qed.
Definition publicly_related := publicly_related_aux.(unseal).
Local Lemma publicly_related_unseal : publicly_related = publicly_related_def.
Proof. rewrite -publicly_related_aux.(seal_eq) //. Qed.

Definition double_squiggle := double_squiggle_pre publicly_related.

Lemma publicly_related_unfold :
  ∀ t1 t2, publicly_related t1 t2 ⊣⊢
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      publicly_related t11 t21 ∧ publicly_related t12 t22
  | TNonce l1, TNonce l2 => public_rel_frag t1 t2
  | TKey kt1 t1', TKey kt2 t2' => ⌜kt1 = kt2⌝ ∧
    match kt1 with
    | AEnc => publicly_related t1' t2' ∨
              (public_rel_frag t1 t2 ∧ double_squiggle t1' t2')
    | ADec => publicly_related t1' t2'
    | Sign => publicly_related t1' t2'
    | Verify => publicly_related t1' t2' ∨
                (public_rel_frag t1 t2 ∧ double_squiggle t1' t2')
    | SEnc => publicly_related t1' t2'
    end
  | TSeal k1 t1', TSeal k2 t2' =>
    (publicly_related k1 k2 ∧ publicly_related t1' t2') ∨
    (public_rel_frag t1 t2 ∧ double_squiggle k1 k2 ∧ double_squiggle t1' t2' ∧
    □ (match k1, k2 with
      | TKey kt1 k1, TKey kt2 k2 => ⌜kt1 = kt2⌝ ∧
        match kt1 with
        | AEnc => publicly_related k1 k2 → publicly_related t1' t2'
        | ADec => False
        | Sign => publicly_related t1' t2' → publicly_related k1 k2
        | Verify => False
        | SEnc => publicly_related k1 k2 → publicly_related t1' t2'
        end
      | _, _ => False
      end))
  | THash t1', THash t2' =>
    publicly_related t1' t2' ∨
    (public_rel_frag t1 t2 ∧ double_squiggle t1' t2')
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

Lemma public_open_public k1 k2 t1 t2 :
  publicly_related k1 k2 -∗
  publicly_related t1 t2 -∗
  publicly_related (TSeal k1 t1) (TSeal k2 t2).
Proof.
  iIntros "#Hk #Ht".
  rewrite [publicly_related (TSeal _ _) _]publicly_related_unfold.
  iLeft; auto.
Qed.

Lemma private_open_public k1 k2 t1 t2 :
  public_rel_frag (TSeal k1 t1) (TSeal k2 t2) -∗
  double_squiggle k1 k2 -∗
  double_squiggle t1 t2 -∗
  publicly_related (TSeal k1 t1) (TSeal k2 t2).
Proof.
  iIntros "#H #IHk #IHt".
  rewrite publicly_related_unfold.
  iRight.
Admitted.

(*
Prove that publicly related is preserved by all operations, including open
Prove that publicly related is a partial bijection.
publicly_related t1 t2 ∧ publicly_related t1 t2' → ▷ t2 = t2'
*)

End Rel.

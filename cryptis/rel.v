From mathcomp Require Import ssreflect.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap list excl.
From iris.algebra Require Import functions.
From iris.base_logic.lib Require Import saved_prop invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis Require Import lib gmeta nown.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PartBij.

Variable T : Type.
Context `{!EqDecision T, !Countable T}.

Implicit Types (R : gset (T * T)) (x y : T).

Definition part_bij R : Prop :=
  ∀ x y x' y', (x, y) ∈ R → (x', y') ∈ R → (x = x' ↔ y = y').

Lemma part_bij_insert x y R :
  part_bij R →
  (∀ x' y', (x', y') ∈ R → x ≠ x' ∧ y ≠ y') →
  part_bij ({[(x, y)]} ∪ R).
Proof.
move=> R_bij fresh x1 y1 x2 y2.
rewrite !elem_of_union !elem_of_singleton.
case=> [[-> ->]|H1] [[-> ->]|H2].
- by split; eauto.
- have [??] := fresh _ _ H2; split; intros; congruence.
- have [??] := fresh _ _ H1; split; intros; congruence.
- exact: R_bij.
Qed.

End PartBij.

Definition term_part_bijR := authUR (gsetUR (term * term)).

Class publicGpreS Σ := PublicGPreS {
  publicGpreS_term_part_bij : inG Σ term_part_bijR;
  publicGpreS_meta : metaGS Σ;
}.

Local Existing Instance publicGpreS_term_part_bij.
Local Existing Instance publicGpreS_meta.

Class publicGS Σ := PublicGS {
  public_inG : publicGpreS Σ;
  public_term_part_bij_name : gname;
}.

Global Existing Instance public_inG.

Definition publicΣ : gFunctors :=
  #[GFunctor term_part_bijR; metaΣ].

Global Instance subG_publicGpreS Σ : subG publicΣ Σ → publicGpreS Σ.
Proof. solve_inG. Qed.

Section Rel.

Context `{!heapGS Σ, !publicGS Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Notation iPropI := (iPropI Σ).

Implicit Types (k : senc_key) (t : term) (R : gset (term * term)).

Definition enc_rel_auth t R : iProp :=
  nown public_term_part_bij_name (nroot.@"enc".@t) (● R) ∗
  ⌜part_bij R⌝.

Definition enc_rel_frag t t1 t2 : iProp :=
  nown public_term_part_bij_name (nroot.@"enc".@t) (◯ {[(t1, t2)]}).

Lemma enc_rel_alloc t1 t2 t R :
  (∀ t1' t2', (t1', t2') ∈ R → t1 ≠ t1' ∧ t2 ≠ t2') →
  enc_rel_auth t R ==∗
  enc_rel_auth t ({[(t1, t2)]} ∪ R) ∗
  enc_rel_frag t t1 t2.
Proof.
iIntros "%fresh [own %bij_R]".
iMod (nown_update with "own") as "[auth frag]".
{ apply: auth_update_alloc.
  apply: (gset_local_update _ _ ({[(t1, t2)]} ∪ R)).
  set_solver. }
rewrite -gset_op auth_frag_op nown_op.
iDestruct "frag" as "[frag _]".
iModIntro. iFrame. iPureIntro. exact: part_bij_insert.
Qed.

Definition nonce_rel_auth R : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce") (● R) ∗
  ⌜part_bij R⌝.

Definition nonce_rel_frag t1 t2 : iProp :=
  nown public_term_part_bij_name (nroot.@"nonce") (◯ {[(t1, t2)]}).

Lemma nonce_rel_alloc t1 t2 R :
  (∀ t1' t2', (t1', t2') ∈ R → t1 ≠ t1' ∧ t2 ≠ t2') →
  nonce_rel_auth R ==∗
  nonce_rel_auth ({[(t1, t2)]} ∪ R) ∗
  nonce_rel_frag t1 t2.
Proof.
iIntros "%fresh [own %bij_R]".
iMod (nown_update with "own") as "[auth frag]".
{ apply: auth_update_alloc.
  apply: (gset_local_update _ _ ({[(t1, t2)]} ∪ R)).
  set_solver. }
rewrite -gset_op auth_frag_op nown_op.
iDestruct "frag" as "[frag _]".
iModIntro. iFrame. iPureIntro. exact: part_bij_insert.
Qed.

Fixpoint public t1 t2 : iProp :=
  match t1, t2 with
  | TInt n1, TInt n2 => ⌜n1 = n2⌝
  | TPair t11 t12, TPair t21 t22 =>
      public t11 t21 ∧ public t12 t22
  | TNonce _, TNonce _ => nonce_rel_frag t1 t2
  | TKey kt1 t1, TKey kt2 t2 =>
      False (* FIXME *)
  | TSeal k1 t1, TSeal k2 t2 =>
      ⌜k1 = k2⌝ ∧ enc_rel_frag k1 t1 t2
  | THash _, THash _ =>
      False (* FIXME *)
  | TExpN' _ _ _, TExpN' _ _ _ =>
      False (* FIXME *)
  | _, _ =>
      False (* WIP *)
  end.

Lemma public_TSeal k R t1 t2 :
  (∀ t1' t2', (t1', t2') ∈ R → t1 ≠ t1' ∧ t2 ≠ t2') →
  enc_rel_auth k R ==∗
  enc_rel_auth k ({[(t1, t2)]} ∪ R) ∗
  public (TSeal k t1) (TSeal k t2).
Proof.
iIntros "%fresh H●".
iMod (enc_rel_alloc _ fresh with "H●") as "[H● H◯]".
by iFrame.
Qed.

End Rel.

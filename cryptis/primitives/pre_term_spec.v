(* These proofs take much longer to check than the rest of the
development. Since they don't have many dependencies, they are left in their own
file to avoid slowing down the compilation process. *)

From cryptis Require Import lib.
From mathcomp Require Import ssreflect.
From mathcomp Require order.
From stdpp Require Import gmap.
From iris.algebra Require Import agree auth gset gmap.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From cryptis.core Require Import pre_term.
From cryptis.primitives Require Import notations pre_term.
From reloc Require Import reloc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Proofs.

Context `{!relocG Σ}.
Notation nonce := loc.

Implicit Types E : coPset.
Implicit Types a : nonce.
Implicit Types pt : PreTerm.pre_term.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.
Implicit Types N : namespace.

Lemma tp_eq_term_op0 E j (o1 o2 : term_op0) :
  nclose specN ⊆ E →
  refines_right j (eq_term_op0 (repr o1) (repr o2)) -∗
  |={E}=> ∃ v, refines_right j v ∗ ⌜v = #(bool_decide (o1 = o2))⌝.
Proof.
iIntros "%HE Hj".
case: o1 o2 => [n1|a1] [n2|a2] /=; tp_lam j; tp_pures j => //; simpl; auto.
all: iFrame; iPureIntro; congr (# (LitBool _)); apply: bool_decide_ext;
  intuition congruence.
Qed.

Lemma tp_eq_key_type E j (o1 o2 : key_type) :
  nclose specN ⊆ E →
  refines_right j (eq_key_type (repr o1) (repr o2)) -∗
  |={E}=> ∃ v, refines_right j v ∗ ⌜v = #(bool_decide (o1 = o2))⌝.
Proof.
iIntros "%HE Hj".
case: o1 o2 => [] [] /=; tp_lam j; tp_pures j => //; simpl; auto.
Qed.

Lemma tp_eq_term_op1 E j (o1 o2 : term_op1) :
  nclose specN ⊆ E →
  refines_right j (eq_term_op1 (repr o1) (repr o2)) -∗
  |={E}=> ∃ v, refines_right j v ∗ ⌜v = #(bool_decide (o1 = o2))⌝.
Proof.
iIntros "%HE Hj".
case: o1 o2 => [o1|] [o2|] /=; tp_lam j; tp_pures j => //; simpl; auto.
iPoseProof (tp_eq_key_type _ _ _ HE with "Hj") as ">[% [Hj ->]]"; iFrame.
iPureIntro.
congr (# (LitBool _)). apply: bool_decide_ext.
intuition congruence.
Qed.

Lemma tp_eq_term_op2 E j (o1 o2 : term_op2) :
  nclose specN ⊆ E →
  refines_right j (eq_term_op2 (repr o1) (repr o2)) -∗
  |={E}=> ∃ v, refines_right j v ∗ ⌜v = #(bool_decide (o1 = o2))⌝.
Proof.
iIntros "%HE Hj".
case: o1 o2 => [] [] /=; tp_lam j; tp_pures j => //; simpl; auto.
Qed.

Lemma tp_eq_pre_term_aux E j (pt1 pt2 : PreTerm.pre_term) :
  nclose specN ⊆ E →
  refines_right j (eq_term (repr pt1) (repr pt2)) -∗
  |={E}=> ∃ v, refines_right j v ∗
               (⌜v = #(bool_decide (pt1 = pt2))⌝).
Proof.
intros HE.
elim: pt1 pt2 j => [o1|o1 t1 IH1|o1 t11 IH1 t12 IH2|t1 IHt1 ts1 IHts1];
case=> [o2|o2 t2|o2 t21 t22|t2 ts2] j;
iIntros "Hj";
tp_rec j; tp_pures j=> //; simpl; auto.
- iPoseProof (tp_eq_term_op0 _ _ _ HE with "Hj") as ">[% [Hj ->]]"; iFrame.
  iPureIntro; congr (# (LitBool _)).
  apply: bool_decide_ext; intuition congruence.
- tp_bind j (eq_term_op1 _ _).
  rewrite refines_right_bind.
  iPoseProof (tp_eq_term_op1 _ _ _ HE with "Hj") as ">[% [Hj ->]]".
  case: bool_decide_reflect=> e1;
  rewrite -refines_right_bind /=.
  + tp_pures j.
    iPoseProof (IH1 t2 with "Hj") as ">[% [Hj ->]]"; iFrame.
    iPureIntro; congr (# (LitBool _)).
    apply: bool_decide_ext; intuition congruence.
  + tp_pures j; iFrame.
    rewrite bool_decide_false //; congruence.
- tp_bind j (eq_term_op2 _ _).
  rewrite refines_right_bind.
  iPoseProof (tp_eq_term_op2 _ _ _ HE with "Hj") as ">[% [Hj ->]]".
  case: bool_decide_reflect=> e1;
  rewrite -refines_right_bind /=.
  + tp_pures j.
    tp_bind j (eq_term _ _).
    rewrite refines_right_bind.
    iPoseProof (IH1 t21 with "Hj") as ">[% [Hj ->]]".
    case: bool_decide_reflect=> e2;
    rewrite -refines_right_bind /=.
    * tp_pures j.
      iPoseProof (IH2 t22 with "Hj") as ">[% [Hj ->]]"; iFrame.
      iPureIntro; congr (# (LitBool _)).
      apply: bool_decide_ext; intuition congruence.
    * tp_pures j; iFrame.
      rewrite bool_decide_false //; congruence.
  + tp_pures j; iFrame.
    rewrite bool_decide_false //; congruence.
- tp_bind j (eq_term _ _).
  rewrite refines_right_bind.
  iPoseProof (IHt1 t2 with "Hj") as ">[% [Hj ->]]"; iFrame.
  case: bool_decide_reflect=> e1;
  rewrite -refines_right_bind /=.
  + tp_pures j.
    admit.
  + tp_pures j; iFrame.
    rewrite bool_decide_false //; congruence.
Admitted.

Lemma twp_eq_term_op1 E (o1 o2 : term_op1) :
  ⊢ WP (eq_term_op1 (repr o1) (repr o2)) @ E
    [{ v, ⌜v = #(bool_decide (o1 = o2))⌝}].
Proof.
case: o1 o2 => [o1|] [o2|] /=; wp_lam; wp_pures => //.
iApply twp_wand. wp_apply twp_eq_key_type.
iIntros (?) "->". iPureIntro.
congr (# (LitBool _)). apply: bool_decide_ext.
intuition congruence.
Qed.

Lemma twp_eq_pre_term E (pt1 pt2 : PreTerm.pre_term) Ψ :
  Ψ #(bool_decide (pt1 = pt2)) ⊢
  WP (eq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
iIntros "H".
iApply twp_wand; first iApply twp_eq_pre_term_aux.
by iIntros (?) "->".
Qed.

Import ssrbool seq path.

Import ssreflect.eqtype ssreflect.order.

Lemma twp_leq_pre_term E (pt1 pt2 : PreTerm.pre_term) Ψ :
  Ψ #(pt1 <= pt2)%O ⊢
  WP (leq_term (repr pt1) (repr pt2)) @ E [{ Ψ }].
Proof.
rewrite /= val_of_pre_term_unseal.
elim: pt1 pt2 Ψ
  => [n1|t11 IH1 t12 IH2|l1|kt1 t1 IH1|t11 IH1 t12 IH2|t1 IH|t1 IHt1 ts1 IHts1];
case=> [n2|t21 t22|l2|kt2 t2|t21 t22|t2|t2 ts2] /= Ψ;
iIntros "post"; wp_rec; wp_pures; try by iApply "post".
- rewrite PreTerm.leqE /= (_ : (_ <= _)%O = bool_decide (n1 ≤ n2)%Z) //.
  exact/(sameP (Z.leb_spec0 _ _))/bool_decide_reflect.
- rewrite -{1 2}val_of_pre_term_unseal; wp_bind (eq_term _ _).
  rewrite PreTerm.leqE /=; iApply twp_eq_pre_term.
  rewrite eq_op_bool_decide; case: eqP => [->|_]; wp_pures.
    by iApply IH2.
  by iApply IH1.
- by rewrite PreTerm.leqE /=; iApply twp_leq_loc.
- rewrite PreTerm.leqE /=; case: eqP => [->|neq].
    rewrite bool_decide_eq_true_2 //; wp_pures; by iApply IH1.
  rewrite bool_decide_eq_false_2; last first.
    move=> [e]; apply: neq.
    by apply: int_of_key_type_inj.
  wp_pures.
  by case: kt1 kt2 {neq} => [] [].
- rewrite PreTerm.leqE /=; wp_bind (eq_term _ _).
  rewrite -{1 2}val_of_pre_term_unseal; iApply twp_eq_pre_term.
  rewrite eq_op_bool_decide; case: eqP => [->|neq]; wp_pures.
    by iApply IH2.
  by iApply IH1.
- rewrite PreTerm.leqE /=; by iApply IH.
- rewrite PreTerm.leqE /=; wp_bind (eq_term _ _).
  rewrite -{1 2}val_of_pre_term_unseal.
  iApply twp_eq_pre_term; rewrite eq_op_bool_decide.
  case: eqP=> [->|neq]; wp_pures; last by iApply IHt1.
  rewrite -!repr_list_val -val_of_pre_term_unseal; iApply twp_leq_list => //.
  + move=> pt1 pt2 Ψ'; iIntros "_ post".
    by iApply twp_eq_pre_term; rewrite eq_op_bool_decide; iApply "post".
  + move/foldr_in in IHts1.
    move=> ????; iIntros "_ post".
    by rewrite /= val_of_pre_term_unseal; iApply IHts1 => //; iApply "post".
  + by iIntros "_".
Qed.

End Proofs.

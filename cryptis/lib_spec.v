From stdpp Require Import base countable gmap.
From iris.heap_lang Require Import lang notation proofmode.
From iris.heap_lang.lib Require Import nondet_bool.
From iris.algebra Require Import gmap gset auth reservation_map.
From iris.base_logic Require Import gen_heap invariants.
From mathcomp Require ssrbool order path.
From deriving Require deriving.
From cryptis Require Export mathcomp_compat.
From cryptis.lib Require Export repr list list_match.

From cryptis Require Import lib.
From cryptis Require Import lib.adequacy.
From reloc Require Import reloc.

(* THIS IS A VERY GROSS HACK *)
Lemma heapGS_heapGpreS Σ `{!heapGS Σ} : heapGpreS Σ.
Proof.
  case: heapGS0 => Hinv Hgen_heap Hinv_heap Hproph_map _ Hstep_cnt.
  constructor => //.
  { case: Hinv => Hwsat Hlc; constructor.
    { by case: Hwsat. }
    { by case: Hlc. } }
  { by case: Hgen_heap. }
  { by case: Hinv_heap. }
  { by case: Hproph_map. }
Qed.

Lemma pure_twp_tp Σ E j e (v: val) :
  pure_expr e →
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e [{ v', ⌜v' = v⌝ }]) →
  ∀ `{!relocG Σ},
  nclose specN ⊆ E →
  refines_right j e ={E}=∗
  refines_right j v.
Proof.
  move=> Hpure Hinv HE.
  have H := heap_twp_pure_exec _ _ _ Hpure Hinv.
  have heapGpreS0: heapGpreS Σ by apply heapGS_heapGpreS; apply _.
  apply H in heapGpreS0 as (v' & Hev' & ->).
  clear Hinv H.
  move=> ?.
  rewrite /refines_right.
  apply rtc_nsteps in Hev' as (n & Hev').
  have H2: PureExec True n e v by rewrite /PureExec //.
  iApply step_pure=> //.
Qed.

Section NonDetProofs.

Context `{!relocG Σ}.

Implicit Types E : coPset.
Implicit Types v : val.
Implicit Types Ψ : val → iProp Σ.

Lemma tp_nondet_bool E j (b : bool) :
  nclose specN ⊆ E →
  refines_right j (nondet_bool #()) ={E}=∗
  refines_right j #b.
Proof.
move=> HE.
iIntros "Hj".
tp_rec j. tp_alloc j as l "Hl".
tp_pures j.
tp_bind j (Fork _).
rewrite refines_right_bind.
set j' := (RefId _ _).
tp_fork j' => /=.
rewrite -refines_right_bind => /=.
clear j'.
tp_pures j.
iIntros "%j' Hj'".
case : b; last tp_store j'.
all: tp_load j=> //.
Qed.

Lemma rel_nondet_bool (Ψ: val -> val -> iProp Σ) :
  ▷ (∀ (b1: bool), ∃ (b2: bool), Ψ #b1 #b2) -∗
  REL nondet_bool #() << nondet_bool #() : Ψ.
Proof.
iIntros "HΨ".
rel_bind_l (nondet_bool #()). iApply refines_wp_l.
iApply nondet_bool_spec => //=.
iModIntro.
iIntros (b1) "_".
iPoseProof ("HΨ" $! b1) as "[%b2 HΨ]".
rel_bind_r (nondet_bool #()). iApply refines_step_r.
iIntros (j) "Hj".
iPoseProof (tp_nondet_bool with "Hj") as ">Hj" => //.
iFrame. rel_values.
Qed.

Lemma tp_nondet_nat_loop E j (m : nat) (n : nat) :
  nclose specN ⊆ E →
  refines_right j (nondet_nat_loop #m) ={E}=∗
  refines_right j #(n + m)%nat.
Proof.
move=> HE.
elim : n m j => [|n' IHn'] m j; iIntros "Hj";
tp_rec j; tp_bind j (nondet_bool _); rewrite refines_right_bind;
  set j' := RefId _ _.
- iPoseProof ((tp_nondet_bool _ _ true HE) with "Hj") as ">Hj".
  rewrite -refines_right_bind => /=.
  by tp_pures j.
- iPoseProof ((tp_nondet_bool _ _ false HE) with "Hj") as ">Hj".
  rewrite -refines_right_bind => /=.
  tp_pures j.
  have ->: (m + 1)%Z = (m + 1)%nat by lia.
  iPoseProof (IHn' with "Hj") as ">Hj".
  have ->: (n' + (m + 1))%nat = S (n' + m) by lia.
  done.
Qed.

Lemma tp_nondet_nat E j (n: nat) :
  nclose specN ⊆ E →
  refines_right j (nondet_nat #()) ={E}=∗
  refines_right j #n.
Proof.
move=> HE.
iIntros "Hj". tp_lam j.
iPoseProof (tp_nondet_nat_loop _ _ 0 n HE with "Hj") as ">Hj".
have ->: (n + 0)%nat = n by lia.
done.
Qed.

Lemma rel_nondet_nat (Ψ: val -> val -> iProp Σ) :
  (∀ (n1: nat), ∃ (n2: nat), Ψ #n1 #n2) -∗
  REL nondet_nat #() << nondet_nat #() : Ψ.
Proof.
iIntros "HΨ".
rel_bind_l (nondet_nat #()). iApply refines_wp_l.
iApply wp_nondet_nat => //=.
iIntros (n1).
iPoseProof ("HΨ" $! n1) as "[%n2 HΨ]".
rel_bind_r (nondet_nat #()). iApply refines_step_r.
iIntros (j) "Hj".
iPoseProof (tp_nondet_nat with "Hj") as ">Hj" => //.
iFrame. rel_values.
Qed.

Lemma tp_nondet_int E j (n : Z) :
  nclose specN ⊆ E →
  refines_right j (nondet_int #()) ={E}=∗
  refines_right j #n.
Proof.
move=> HE.
iIntros "Hj"; rewrite /nondet_int; tp_pures j.
tp_bind j (nondet_nat _).
rewrite refines_right_bind.
set j' := RefId _ _.
pose n' := if (0 <=? n)%Z then Z.to_nat n else Z.to_nat (-n).
iPoseProof (tp_nondet_nat _ _ n' HE with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
clear j'.
tp_pures j.
tp_bind j (nondet_bool _).
rewrite refines_right_bind.
set j' := RefId _ _.
iPoseProof (tp_nondet_bool _ _ (0 <=? n)%Z HE with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
clear j'.
case Hn: (0 <=? n)%Z in n' *; tp_pures j.
- by have ->: n = n' by lia.
- by have ->: n = (- n')%Z by lia.
Qed.

Lemma rel_nondet_int (Ψ: val -> val -> iProp Σ) :
  (∀ (n1: Z), ∃ (n2: Z), Ψ #n1 #n2) -∗
  REL nondet_int #() << nondet_int #() : Ψ.
Proof.
iIntros "HΨ".
rel_bind_l (nondet_int #()). iApply refines_wp_l.
iApply wp_nondet_int => //=.
iIntros (n1).
iPoseProof ("HΨ" $! n1) as "[%n2 HΨ]".
rel_bind_r (nondet_int #()). iApply refines_step_r.
iIntros (j) "Hj".
iPoseProof (tp_nondet_int with "Hj") as ">Hj" => //.
iFrame. rel_values.
Qed.

End NonDetProofs.

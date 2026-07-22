From iris.heap_lang.lib Require Import nondet_bool.
From reloc Require Import reloc.
From cryptis Require Import lib.
From cryptis.lib Require adequacy.
From cryptis.lib Require Export list_spec list_match_spec.

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
  ↑specN ⊆ E →
  refines_right j e ={E}=∗
  refines_right j v.
Proof.
  move=> Hpure Hinv HE.
  have H := adequacy.heap_twp_pure_exec _ _ _ Hpure Hinv.
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
Implicit Types b : bool.
Implicit Types m n : nat.
Implicit Types x : Z.
Implicit Types Ψ : val → val → iProp Σ.

Lemma rel_nondet_bool_l K e Ψ :
  (∀ b, REL fill K (#b : expr) << e : Ψ) -∗
  REL fill K (nondet_bool #()) << e : Ψ.
Proof.
iIntros "H". iApply refines_wp_l.
wp_apply nondet_bool_spec=> //.
eauto.
Qed.

Lemma rel_nondet_bool_r K e b Ψ :
  (REL e << fill K (#b : expr) : Ψ) -∗
  REL e << fill K (nondet_bool #()) : Ψ.
Proof.
iIntros "H".
rel_rec_r. rel_alloc_r l as "Hl".
rel_pures_r.
rel_fork_r j as "Hj".
rel_pures_r.
case: b; last tp_store j.
all: rel_load_r=> //.
Qed.

#[local] Lemma rel_nondet_nat_loop_r K e m n Ψ :
  (REL e << fill K (#(n + m)%nat : expr) : Ψ) -∗
  REL e << fill K (nondet_nat_loop #m) : Ψ.
Proof.
elim : n m => [|n' IHn'] m /=; iIntros "H";
rel_rec_r.
- rel_apply_r (rel_nondet_bool_r _ _ true).
  by rel_pures_r.
- rel_apply_r (rel_nondet_bool_r _ _ false).
  rel_pures_r.
  have ->: (m + 1)%Z = m + 1 by lia.
  have <-: n' + (m + 1) = S (n' + m) by lia.
  by iPoseProof (IHn' with "H") as "H".
Qed.

Lemma rel_nondet_nat_l K e Ψ :
  (∀ n, REL fill K (#n : expr) << e : Ψ) -∗
  REL fill K (nondet_nat #()) << e : Ψ.
Proof.
iIntros "H". iApply refines_wp_l.
by wp_apply wp_nondet_nat.
Qed.

Lemma rel_nondet_nat_r K e n Ψ :
  (REL e << fill K (#n: expr) : Ψ) -∗
  REL e << fill K (nondet_nat #()) : Ψ.
Proof.
iIntros "H". rel_rec_r.
rel_apply_r (rel_nondet_nat_loop_r _ _ 0 n).
have ->: n + 0 = n by lia.
done.
Qed.

Lemma rel_nondet_int_l K e Ψ :
  (∀ n : Z, REL fill K (#n : expr) << e : Ψ) -∗
  REL fill K (nondet_int #()) << e : Ψ.
Proof.
iIntros "H". iApply refines_wp_l.
by wp_apply wp_nondet_int.
Qed.

Lemma rel_nondet_int_r K e (n : Z) Ψ :
  (REL fill K e << fill K (#n : expr) : Ψ) -∗
  REL fill K e << fill K (nondet_int #()) : Ψ.
Proof.
iIntros "H". rel_rec_r.
pose n' := if (0 <=? n)%Z then Z.to_nat n else Z.to_nat (-n).
rel_apply_r (rel_nondet_nat_r _ _ n').
rel_pures_r.
rel_apply_r (rel_nondet_bool_r _ _ (0 <=? n)%Z).
case Hn: (0 <=? n)%Z in n' *; rel_pures_r.
- by have ->: n = n' by lia.
- by have ->: n = (- n')%Z by lia.
Qed.

End NonDetProofs.

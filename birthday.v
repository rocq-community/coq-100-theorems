(*
MIT License

Copyright (c) 2017 Jean-Marie Madiot, INRIA

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Fixpoint appears x l :=
  match l with
  | [] => false
  | y :: l => if Nat.eqb x y then true else appears x l
  end.

Fixpoint collision l :=
  match l with
  | [] => false
  | x :: l => if appears x l then true else collision l
  end.

Definition enumerate n := seq 0 n.

Fixpoint picks {A} n (l : list A) : list (list A) :=
  match n with
  | O => [[]]
  | S n => map (fun x => fst x :: snd x) (list_prod l (picks n l))
  end.

Lemma appears_In_iff x l:
  In x l <-> appears x l = true.
Proof.
  induction l as [|a l IH]; [easy|].
  cbn. rewrite IH.
  destruct (Nat.eq_decidable x a) as [->|E].
  - rewrite Nat.eqb_refl. tauto.
  - assert (x =?a = false) as ->
      by (apply Nat.eqb_neq; assumption).
    apply not_eq_sym in E. tauto.
Qed.

Corollary appears_false_iff x l:
  ~ In x l <-> appears x l = false.
Proof.
  destruct (appears x l) eqn:H.
  - apply appears_In_iff in H.
    split; [contradiction|discriminate].
  - split; [reflexivity|].
    intros _ E%appears_In_iff.
    rewrite H in E. discriminate.
Qed.

Lemma collision_NoDup_iff l:
  NoDup l <-> collision l = false.
Proof.
  split; intro H.
  - induction H; [reflexivity|].
    cbn. destruct (appears x l) eqn:E.
    + apply appears_In_iff in E. contradiction.
    + assumption.
  - induction l as [|a l IH]; [constructor|].
    cbn in H. destruct (appears a l) eqn:E.
    + discriminate H.
    + constructor.
      * apply appears_false_iff. assumption.
      * apply IH. assumption.
Qed.

Lemma Zlength_picks {A} n (l : list A) :
  Zlength (picks n l) = Z.pow (Zlength l) (Z.of_nat n).
Proof.
  rewrite Zlength_correct.
  induction n. reflexivity. simpl (length _).
  rewrite map_length, prod_length.
  change (S n) with (1 + n).
  rewrite Nat2Z.inj_add, Z.pow_add_r, Z.pow_1_r.
  rewrite <-IHn.
  rewrite Nat2Z.inj_mul, Zlength_correct.
  reflexivity.
  all: lia.
Qed.

Fixpoint partial_fact k n (* = n! / (n-k)! *) :=
  (match k with
   | O => 1
   | S k => n * partial_fact k (n - 1)
   end)%Z.

Definition no {A} (f : A -> bool) x := negb (f x).

Lemma cartesian_product_filters {A B} (f : A -> bool) (g : B -> bool) xs ys :
  list_prod (filter f xs) (filter g ys) =
  filter (fun p => andb (f (fst p)) (g (snd p))) (list_prod xs ys).
Proof.
  revert ys.
  induction xs; intros ys; auto.
  simpl.
  rewrite filter_app.
  rewrite <-IHxs.
  destruct (f a) eqn:Ha.
  - simpl. f_equal.
    clear -Ha.
    induction ys as [| b ys IHys]; auto.
    simpl. destruct (f a), (g b); simpl; congruence.
  - rewrite IHxs.
    match goal with |- ?a = _ => transitivity ([] ++ a) end. reflexivity.
    f_equal.
    induction ys as [| b ys IHys]; auto.
    simpl. destruct (f a), (g b); simpl; try congruence.
Qed.

Lemma picks_remove k a l :
  picks k (filter (no (Nat.eqb a)) l) =
  filter (no (appears a)) (picks k l).
Proof.
  induction k. reflexivity.
  simpl. rewrite IHk. clear IHk.
  generalize (picks k l); intros ll.
  rewrite cartesian_product_filters.
  induction (list_prod l ll) as [| a0 l0 IHl0]. simpl. reflexivity.
  simpl.
  rewrite <-IHl0.
  unfold no.
  simpl.
  destruct (a =? fst a0). reflexivity.
  simpl.
  destruct (appears a (snd a0)); reflexivity.
Qed.

Lemma appears_filter x l f :
  appears x l = false -> appears x (filter f l) = false.
Proof.
  intros H%appears_false_iff. apply appears_false_iff.
  intros E%filter_In. tauto.
Qed.

Lemma collision_filter l f :
  collision l = false -> collision (filter f l) = false.
Proof.
  intros H%collision_NoDup_iff. apply collision_NoDup_iff.
  apply NoDup_filter. assumption.
Qed.

Lemma collision_count l :
  collision l = false -> Forall (fun x1 : nat => count_occ Nat.eq_dec l x1 = 1) l.
Proof.
  intros H%collision_NoDup_iff.
  apply Forall_forall. intros x Hx.
  apply NoDup_count_occ'; assumption.
Qed.

Lemma length_no_collision_picks k l :
  collision l = false ->
  Zlength (filter (no collision) (picks k l)) =
  partial_fact k (Zlength l).
Proof.
  rewrite Zlength_correct.
  revert l; induction k; intros l Hcol. reflexivity.
  simpl.
  set (l1 := l) at 1 3.
  assert (Huniq : Forall (fun x1 => count_occ Nat.eq_dec l x1 = 1) l1).
  { apply collision_count; auto. }
  clearbody l1.
  induction l1 as [| a l1 IHl1]. reflexivity.
  simpl.
  rewrite map_app, filter_app, app_length.
  rewrite Zlength_cons, Z.mul_succ_l, Nat2Z.inj_add.
  rewrite Z.add_comm. f_equal.
  - rewrite IHl1. auto.
    inversion Huniq; auto.
  - clear IHl1.
    rewrite map_map. simpl.
    pose (l' := filter (no (Nat.eqb a)) l).
    assert (El' : Zlength l' = (Zlength l - 1)%Z).
    {
      apply Forall_inv in Huniq.
      cut (Zlength l' + 1 = Zlength l)%Z.
      { intros <-. lia. }
      unfold l'.
      do 2 rewrite Zlength_correct.
      change 1%Z with (Z.of_nat 1).
      rewrite <-Nat2Z.inj_add.
      f_equal.
      rewrite <-Huniq.
      clear IHk k Hcol l' Huniq.
      induction l as [| b l IHl]. reflexivity. simpl.
      rewrite <-IHl.
      unfold no.
      destruct (Nat.eq_dec b a).
      - subst. rewrite Nat.eqb_refl. simpl. lia.
      - replace (a =? b) with false; simpl. reflexivity.
        symmetry. apply Nat.eqb_neq. auto.
    }
    assert (Hl' : collision l' = false).
    {
      unfold l'. generalize (no (Nat.eqb a)); intros f.
      clear -Hcol.
      apply collision_filter; auto.
    }
    rewrite <-El'.
    rewrite <-IHk; auto.
    f_equal.
    transitivity (length (map (fun x => a :: x) (filter (no collision) (picks k l')))).
    2: rewrite map_length; reflexivity.
    f_equal.
    unfold l'.
    apply Forall_inv in Huniq.
    clear IHk El' l' Hl' l1.
    rewrite picks_remove.
    induction (picks k l) as [| l' ll' IHll']. reflexivity.
    simpl.
    unfold no at 1 5.
    simpl.
    destruct (appears a l'). simpl; congruence.
    simpl.
    unfold no at 3.
    destruct (collision l'); simpl; congruence.
Qed.

(* TODO: lemma filter_length in Coq 8.18 *)
Lemma length_filter {A} (f : A -> bool) l :
  length (filter f l) + length (filter (no f) l) = length l.
Proof.
  unfold no.
  induction l; auto. simpl.
  destruct (f a); simpl; lia.
Qed.

Lemma Zlength_filter {A} (f : A -> bool) l :
  (Zlength (filter f l) = Zlength l - Zlength (filter (no f) l))%Z.
Proof.
  repeat rewrite Zlength_correct.
  rewrite <-(length_filter f l). lia.
Qed.

Lemma enumerate_no_collisions n : collision (enumerate n) = false.
Proof. apply collision_NoDup_iff, seq_NoDup. Qed.

Theorem birthday_paradox :
  let l := picks 23 (enumerate 365) in
  2 * length (filter collision l) > length l.
Proof.
  intros l; unfold l.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z.inj_mul.
  repeat rewrite <-Zlength_correct.
  rewrite Zlength_filter.
  rewrite length_no_collision_picks
    by apply enumerate_no_collisions.
  repeat rewrite Zlength_picks.
  reflexivity.
Qed.

Theorem birthday_paradox_min :
  let l := picks 22 (enumerate 365) in
  2 * length (filter collision l) < length l.
Proof.
  intros l; unfold l.
  apply Nat2Z.inj_lt.
  rewrite Nat2Z.inj_mul.
  repeat rewrite <-Zlength_correct.
  rewrite Zlength_filter.
  rewrite length_no_collision_picks
    by apply enumerate_no_collisions.
  repeat rewrite Zlength_picks.
  reflexivity.
Qed.

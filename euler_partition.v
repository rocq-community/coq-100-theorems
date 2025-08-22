(*
MIT License

Copyright (c) 2025 Keisuke Nakano

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

From mathcomp Require Import all_ssreflect fintype zify.
From HB Require Import structures.
Unset Implicit Arguments. Set Strict Implicit.

Lemma iffE (b1 b2 : bool) : (b1 -> b2) -> (b2 -> b1) -> b1 = b2.
Proof. by move=> H1 H2; apply: Bool.eq_true_iff_eq. Qed.

Lemma sval_inj [T : Type] (p : {pred T}) : injective (@sval T p).
Proof. by move=> [??][??]/=?; subst; f_equal; apply: eq_irrelevance. Qed.

Lemma path_leqE (n : nat) (s : seq nat) :
  path leq n s = all (leq n) s && sorted leq s.
Proof. by rewrite (path_sortedE leq_trans). Qed.

Lemma all_leqS {i : nat} {s : seq nat} :
  i \notin s -> all (leq i) s -> all (leq i.+1) s.
Proof.
  by move=> /negP N/allP A; apply /allP=> j/[dup]/A;
  rewrite leq_eqVlt=> /orP[/eqP<-|].
Qed.

Lemma dvdn_sumn_pow2 {n : nat} {s : seq nat} :
    all (leq n) s -> 2 ^ n %| sumn [seq 2 ^ m | m <- s].
Proof. by elim: s=> //m s IH/=/andP[?]/IH/dvdn_addl->; rewrite dvdn_exp2l. Qed.

Notation oddn := odd.
Notation opartn := (fun n : nat => n %/ 2 ^ logn 2 n). (* n %/ n`_2 *)
Notation pnat := { n : nat | is_true (0 < n) }.
(* Coercion pnat_nat (n : pnat) := sval n. *)
Notation lep := (fun m n : pnat => sval m <= sval n).
Section PositiveNat.
  Definition odd (n : pnat) : bool := odd (sval n).

  Definition mulp (m n : pnat) : pnat.
    exists (sval m * sval n); abstract by move: m n=> [m pm][n pn]/=; lia.
  Defined.

  Definition pow2 (m : nat) : pnat. exists (2 ^ m); abstract by lia. Defined.

  Lemma oddn_opartn (n : pnat) : oddn (opartn (sval n)).
  Proof.
    have p2: prime 2 by [].
    by move: n=> [n pn]/=; move: (pfactor_coprime p2 pn)=> [m]/[swap]->/[dup]m2;
    rewrite coprime2n (logn_Gauss _ m2) (pfactorK _ p2) mulnK.
  Qed.

  Lemma logn_mulp (m n : pnat) :
    odd m -> logn 2 (sval (mulp m n)) = logn 2 (sval n).
  Proof.
    by move: m n=> [m pm] [n pn]/=; rewrite /odd/mulp/= -coprime2n=> m2;
    rewrite logn_Gauss.
  Qed.

  Lemma logn_pow2 (n : nat) : logn 2 (sval (pow2 n)) = n.
  Proof. by rewrite /pow2/= pfactorK. Qed.

  Definition opart (n : pnat) : pnat.
    exists (opartn (sval n));
    abstract by move: (sval n %/ 2 ^ logn 2 (sval n)) (oddn_opartn n); lia.
  Defined.

  Lemma opartE {n : pnat} {i : nat} : odd n -> opart (mulp n (pow2 i)) = n.
  Proof.
    by rewrite /opart=> /logn_mulp H; apply: sval_inj;
    rewrite /sval {}H logn_pow2/=; case: n=> n//=_; rewrite mulnK; lia.
  Qed.

  Definition ppart (n : pnat) : nat := logn 2 (sval n).

  Lemma ppartE {n : pnat} {i : nat} : odd n -> ppart (mulp n (pow2 i)) = i.
  Proof. by rewrite /ppart=> /logn_mulp->; rewrite logn_pow2. Qed.

  Lemma mulp_pow2E (n : pnat) : mulp (opart n) (pow2 (ppart n)) = n.
  Proof.
    by apply sval_inj=> /=; rewrite /ppart divnK // pfactor_dvdnn.
  Qed.

  Lemma mulp_pow2_inj {m1 n1 m2 n2} :
    odd m1 -> odd m2 ->
    (mulp m1 (pow2 n1) == mulp m2 (pow2 n2)) = (m1 == m2) && (n1 == n2).
  Proof.
    move=> m1o m2o; apply iffE.
    - by move=> /eqP E; move: (f_equal opart E) (f_equal ppart E);
      rewrite !opartE // !ppartE // => <-<-; rewrite !eqxx.
    - by move=> /andP[]/eqP<-/eqP<-; rewrite eqxx.
  Qed.

  Lemma uniq_map_ppart (m : pnat) (s : seq pnat) :
    uniq s -> uniq [seq ppart n | n <- s & opart n == m].
  Proof.
    by elim : s=> //n s IH/=/andP[/negP N/IH{}IH]; case nm: (opart n == m)=> //;
    rewrite /= -(rwP andP) -(rwP negP); split=> // /mapP/=[k];
    rewrite mem_filter=> /andP[/eqP Ek ks Ep];
    move: nm ks; rewrite -(mulp_pow2E k) Ek -Ep=> /eqP<-; rewrite mulp_pow2E.
  Qed.
End PositiveNat.

Notation sump ns := (sumn [seq sval i | i <- ns]).
Section PNatSeq.
  Section SumPNatSeq.
    Lemma sump_sort (leT : rel pnat) (ns : seq pnat) :
      sump (sort leT ns) = sump ns.
    Proof. by rewrite !sumnE !big_map; apply: perm_big; rewrite perm_sort. Qed.

    Lemma sump_cat (ns1 ns2 : seq pnat) :
      sump (ns1 ++ ns2) = sump ns1 + sump ns2.
    Proof. by rewrite !sumnE map_cat big_cat. Qed.

    Lemma sump_flatten (ss : seq (seq pnat)) :
      sump (flatten ss) = sumn [seq sump s | s <- ss].
    Proof. by elim: ss=> //=s ss; rewrite sump_cat=> /=->. Qed.
  End SumPNatSeq.

  Lemma pnats_spec (n : nat) : all [eta leq 1] (iota 1 n).
  Proof. by elim: n=> //n IH; rewrite -(addn1 n) iotaD all_cat IH. Qed.
  Definition pnats (n : nat) : seq pnat := sval (all_sigP (pnats_spec n)).

  Fixpoint all_pnats (len mx : nat) : seq (seq pnat) :=
    match len with
      | 0 => [:: [::]]
      | len'.+1 =>
          [::] :: [seq i :: s | i <- pnats mx, s <- all_pnats len' mx]
      end.

  Lemma uniq_all_pnats len mx : uniq (all_pnats len mx).
  Proof.
    elim: len=> //=len IH; apply /andP; split.
    - by apply /negP=> /allpairsP/=[][n s][].
    - apply: allpairs_uniq=> //.
      + by rewrite /pnats; case: all_sigP=> /=s/(f_equal uniq);
        rewrite iota_uniq (map_inj_uniq (sval_inj _))=> <-.
      + by move=> [/=n s][m t] _ _[->->].
  Qed.

  Lemma mem_all_pnats s len mx :
    all (fun i : pnat => sval i <= mx) s -> size s <= len ->
    s \in all_pnats len mx.
  Proof.
    by elim: len s=> [|len IH] [|n s]//=/andP[]Hn/IH/[apply]Hs;
    rewrite in_cons/=; apply: allpairs_f=> //;
    rewrite /pnats; case: all_sigP=> /=t/(f_equal (fun s => sval n \in s));
    rewrite mem_iota add1n ltnS {}Hn (mem_map (sval_inj _)) andbT=> <-; case: n.
  Qed.

  Lemma sorted_lep_perm {s1 s2 : seq pnat} :
    sorted lep s2 -> perm_eq s1 s2 -> sort lep s1 = s2.
  Proof.
    have tot: total lep by move=> m n; apply: leq_total.
    have trs: transitive lep by move=> m n p; apply: leq_trans.
    by move=> S2 P12; rewrite -(sorted_sort trs S2);
    apply /(perm_sortP tot trs)=> //x y/anti_leq; apply: sval_inj.
  Qed.

  Lemma sorted_sort_lep (s : seq pnat) : sorted lep (sort lep s).
  Proof. by apply /sort_sorted=> m n; apply: leq_total. Qed.
End PNatSeq.

Section Partition.
  Variable n : nat.

  Definition is_partition : {pred seq pnat} :=
    fun s => (sump s == n) && sorted lep s.

  Inductive partition : Type := Part of { s : seq pnat | is_partition s }.
  Coercion partition_sval '(Part p) : seq pnat := sval p.

  Lemma unPartK : cancel (fun '(Part p) => p) Part. Proof. by case. Qed.
  HB.instance Definition _ := Countable.copy partition (can_type unPartK).

  Lemma Part_inj : injective Part. Proof. by move=> ??[]. Qed.

  Lemma partition_inj : injective partition_sval.
  Proof. by move=> [[??]][[??]]/=?; subst; f_equal; apply sval_inj. Qed.

  Section EnumType.
    Definition partition_enum : seq partition :=
      [seq Part s | s <- sval (all_sigP (filter_all _ (all_pnats n n)))].

    Lemma partition_enumP : Finite.axiom partition_enum.
    Proof.
      move=> /=p; rewrite /partition_enum count_uniq_mem;
      case: all_sigP=> [pss E]/=.
      - case: p=> s; rewrite (mem_map Part_inj) 
          -(mem_map (sval_inj is_partition)) -{}E mem_filter {pss}.
        case: s=> /=s/[dup]/andP[/eqP<-_]->; rewrite mem_all_pnats=> //=.
        + by elim: s=> //=m s; rewrite leq_addr; apply: sub_all=> k; lia.
        + by elim: s=> //=[][/=m pm]s; lia.
      - by rewrite (map_inj_uniq Part_inj) 
          -(map_inj_uniq (sval_inj is_partition)) -E;
        apply /filter_uniq /uniq_all_pnats. 
    Qed.
    HB.instance Definition _ := isFinite.Build partition partition_enumP.
  End EnumType.  
End Partition.

Section PowersSeq.
  Lemma bin_rect {P : nat -> Type} :
    P 0 -> (forall n, P n -> P n.*2) -> (forall n, P n -> P n.*2.+1) ->
    forall n, P n.
  Proof.
    move=> P0 P1 P2 n; elim: n {-2}n (leqnn n)=> [|m IH] n.
    - by rewrite leqn0=> /eqP->.
    - rewrite leq_eqVlt; case nm: (n == m.+1)=> /=; last by apply: IH.
      move: nm=> /eqP->_; case on: (oddn m.+1).
      + have->: m.+1 = m.+1./2.*2.+1 by rewrite halfK on subn1.
        by apply /P2/IH; lia.
      + by move: on=> /negbT/even_halfK<-; apply /P1/IH; lia.
  Qed.

  Notation is_pows := (fun (n : nat) (bs : seq nat) =>
    [&& n == sumn [seq 2 ^ i | i <- bs], uniq bs & sorted leq bs]).

  Lemma sumn_double (bs : seq nat) :
    (sumn [seq 2 ^ i | i <- bs]).*2 =
    sumn [seq 2 ^ i | i <- [seq i.+1 | i <- bs]].
  Proof.
    by rewrite -muln2 !sumnE big_distrl/= big_map -map_comp/comp big_map;
    apply: eq_big=> //i; rewrite expnSr.
  Qed.

  Lemma is_pows_even (n : nat) (bs : seq nat) :
    is_pows n bs = is_pows n.*2 [seq i.+1 | i <- bs].
  Proof.
    rewrite /=map_inj_uniq; last by move=> ??[].
    by rewrite -(@eqn_pmul2r 2) // !muln2 sumn_double; do 2 f_equal;
    elim: bs=> [|i bs IH]//=; rewrite !path_leqE IH all_map.
  Qed.

  Lemma is_pows_odd (n : nat) (bs : seq nat) :
    is_pows n bs = is_pows n.*2.+1 (0 :: [seq i.+1 | i <- bs]).
  Proof.
    move: (is_pows_even n); rewrite /=add1n eqSS path_leqE=> ->;
    have->/=: 0 \notin [seq i.+1 | i <- bs] by elim: bs.
    have->//=: all (leq 0) [seq i.+1 | i <- bs] by elim: bs.
  Qed.

  Lemma is_pows_cons {n i : nat} {bs : seq nat} :
    is_pows n (i :: bs) =
    [&& i == logn 2 n, all (leq i.+1) bs, 2 ^ i <= n & is_pows (n - 2^i) bs].
  Proof.
    rewrite /=path_leqE -!andbA; apply: iffE.
    - by move=> /and5P[]/eqP->/[swap]->/all_leqS/[apply]/[dup]Ls->->;
      rewrite leq_addr addnC addnK eqxx !andbT -(divnK (dvdn_sumn_pow2 Ls))
        mulnC expnSr -mulnA -mulnSr mulnC logn_Gauss ?pfactorK // 
        coprime2n oddS mul2n odd_double.
    - move=> /and5P[_/allP/=ASbs H/eqP<-/andP[->->]]/=; apply /and3P; split.
      + by lia.
      + by apply /negP=> /ASbs; rewrite ltnn.
      + by rewrite andbT; apply /allP=> /=j/ASbs/ltnW.
  Qed.

  Lemma pows_total (n : nat) : { bs : seq nat | is_pows n bs }.
  Proof.
    move: n; apply: bin_rect=> [|n [bs ?]|n [bs ?]].
    - by exists [::]; rewrite eqxx.
    - by exists [seq i.+1 | i <- bs]; rewrite -is_pows_even.
    - by exists (0 :: [seq i.+1 | i <- bs]); rewrite -is_pows_odd.
  Qed.

  Lemma pows_functional {n : nat} {bs1 bs2 : seq nat} :
    is_pows n bs1 -> is_pows n bs2 -> bs1 = bs2.
  Proof.
    elim: bs1 n bs2=> [|i1 bs1 IH] n [|i2 bs2]//=.
    1, 2: rewrite ?big_nil ?big_cons//=; lia.
    by rewrite !is_pows_cons=> /and4P[]/eqP<-_ _/IH{}IH/and4P[]/eqP->_ _/IH<-.
  Qed.

  Definition pows (n : nat) : seq nat := sval (pows_total n).

  Lemma pows_uniq (n : nat) : uniq (pows n).
  Proof. by rewrite /pows; case: pows_total=> bs/=/and3P[]. Qed.

  Lemma pows0 : pows 0 = [::].
  Proof. by rewrite /pows; case: pows_total=> [][|b bs]//=/and3P[]; lia. Qed.

  Lemma pows_even (n : nat) : pows n.*2 = [seq i.+1 | i <- pows n].
  Proof.
    by rewrite /pows; case: (pows_total n)=> /=[bs1];
    rewrite is_pows_even; case: pows_total=> /=[bs2]; apply: pows_functional.
  Qed.

  Lemma pows_odd (n : nat) : pows n.*2.+1 = 0 :: [seq i.+1 | i <- pows n].
  Proof.
    by rewrite /pows; case: (pows_total n)=> /=[bs1];
    rewrite is_pows_odd; case: pows_total=> /=[bs2] H1 H2;
    apply: (pows_functional H1)=> /=.
  Qed.

  Lemma pows_pow (i : nat) : pows (2 ^ i) = [:: i].
  Proof.
    elim: i=> [|i IH].
    - by rewrite expn0 -{1}double0 pows_odd // pows0.
    - by rewrite expnS mul2n pows_even IH.
  Qed.

  Lemma sumn_pows (n : nat) : sumn [seq 2 ^ i | i <- pows n] = n.
  Proof.
    move: n; apply: bin_rect=> [|n IH|n IH].
    - by rewrite pows0.
    - by rewrite pows_even -{2}IH/= sumn_double.
    - by rewrite pows_odd -{2}IH/= sumn_double add1n.
  Qed.

  Lemma pows_sumn (s : seq nat) :
    uniq s -> sorted leq s -> pows (sumn [seq 2 ^ i | i <- s]) = s.
  Proof.
    elim: s=> [_ _|i s IH]/=.
    - by rewrite pows0.
    - rewrite path_leqE=> /andP[Ns Us]/andP[]/(all_leqS Ns){Ns}
        /dvdn_sumn_pow2/[swap]/(IH Us){IH Us}{3}<-; move: (sumn _) i;
      apply: bin_rect=> [|n IH|n IH] i.
      + by rewrite pows0 addn0 pows_pow.
      + rewrite expnS -mul2n dvdn_pmul2l //; move: i=> [|i].
        * by rewrite addSn add0n mul2n pows_odd pows_even.
        * by rewrite {2}expnS !mul2n -doubleD !pows_even=> /IH->.
      + have H: oddn (n.*2.+1) by lia.
        by rewrite expnS mul2n=> /dvdn_odd/(_ H){H}; lia.
  Qed.
End PowersSeq.

Section SeqUtils.
  Context [T : eqType].

  Lemma undup_cons {x : T} {u s : seq T} :
    undup s = x :: u -> (undup [seq y <- s | y != x] == u) && (x \in s).
  Proof.
    elim: s u=> [|z s IH] u//=; rewrite in_cons; case zs: (z \in s).
    - by move=> /IH/andP[]/eqP<-->; rewrite orbT andbT;
      case zx: (z == x)=> //=; rewrite mem_filter zx zs.
    - by move=> []?; subst z; rewrite eqxx/= andbT=> <-{IH u}; apply /eqP;
      elim: s zs=> [//|y s IH]//=/negP/negP; rewrite in_cons negb_or eq_sym
      => /andP[]yx/negPf xs; rewrite yx/= mem_filter yx (IH xs).
  Qed.

  Lemma eq_filter_map_count_mem [T' : eqType] {p : T -> bool}
    (f : T -> nat -> T') (s : seq T) :
    let t := [seq x <- s | p x] in
    [seq f z (count_mem z s) | z <- undup t] =
    [seq f z (count_mem z t) | z <- undup t].
  Proof.
    by rewrite /= -eq_in_map=> x;
    rewrite mem_undup mem_filter count_filter=> /andP[] px xs; f_equal;
    apply: eq_count=> y/=; case: eqP=> //->.
  Qed.
End SeqUtils.

Section FinUtils.
  Context [T : finType].

  Section LeqCard.
    Context [p1 p2 : {pred T}] [f12 f21 : T -> T].
    Hypothesis f121K : {in p1, cancel f12 f21}.
    Hypothesis f12p1 : {in p1, forall x, f12 x \in p2}.

    Lemma can_card_leq : #| p1 | <= #| p2 |.
    Proof.
      by rewrite -(card_in_imset (can_in_inj f121K)); apply: subset_leq_card;
      apply /subsetP=> y/imsetP[] x/f12p1 H->.      
    Qed.
  End LeqCard.

  Section EqCard.
    Context [p1 p2 : {pred T}] [f12 f21 : T -> T].
    Hypothesis f121K : {in p1, cancel f12 f21}.
    Hypothesis f212K : {in p2, cancel f21 f12}.
    Hypothesis f12p1 : {in p1, forall x, f12 x \in p2}.
    Hypothesis f21p2 : {in p2, forall x, f21 x \in p1}.

    Lemma can_card_eq : #| p1 | = #| p2 |.
    Proof.
      by rewrite (rwP eqP) eqn_leq (can_card_leq f121K) // (can_card_leq f212K).
    Qed.
  End EqCard.
End FinUtils.

Section LiftPartitionMap.
  Lemma mem_partition [n] (P : {pred seq pnat}) (p : partition n) :
    p \in [set p : partition n | P p ] = (P p) && is_partition n p.
  Proof. by case: p=> [][s sp]; rewrite in_set/=sp andbT. Qed.

  Class Liftable (f : seq pnat -> seq pnat) :=
    { liftable : forall n s, is_partition n s -> is_partition n (f s) }.

  Definition lift_map (f : seq pnat -> seq pnat) `{Liftable f}
    (n : nat) (p : partition n) : partition n :=
    Part n (exist _ (f p) (let '(Part (exist s ps)) := p in liftable n s ps)).

  Section LiftMap.
    Context [n : nat] [P1 P2 : {pred seq pnat}].
    Context [f12 f21 : seq pnat -> seq pnat] `{Liftable f12} `{Liftable f21}.

    Lemma lift_mapK :
      {in [predI P1 & is_partition n], cancel f12 f21} ->
      {in [set p : partition n | P1 p],
          cancel (lift_map f12 n) (lift_map f21 n)}.
    Proof.
      by move=> fK p; rewrite mem_partition=> /fK E; apply: partition_inj.
    Qed.

    Lemma lift_map_onto :
      {in [predI P1 & is_partition n], forall p, f12 p \in P2} ->
      {in [set p : partition n | P1 p],
          forall p, lift_map f12 n p \in [set p : partition n | P2 p] }.
    Proof. by move=> P p; rewrite (mem_partition P1)=> /P; rewrite in_set. Qed.
  End LiftMap.
End LiftPartitionMap.

Definition uniq_odd (s : seq pnat) : seq pnat :=
  sort lep (flatten [seq nseq (sval (pow2 (ppart x))) (opart x) | x <- s]).

Instance Liftable_uniq_odd : Liftable uniq_odd.
Proof.
  refine {| liftable n s := _ |};
  rewrite /is_partition sorted_sort_lep andbT sump_sort=> /andP[]/eqP<-{n}_;
  apply /eqP; elim: s=> //i s/=; rewrite sump_cat=> /=->; f_equal.
  have-> n (p : pnat): sump (nseq n p) = sval p * n 
    by rewrite mulnC; elim: n=> //=n->.
  by rewrite /ppart/opart/= divnK // pfactor_dvdnn.
Qed.

Definition odd_uniq (s : seq pnat) : seq pnat :=
  sort lep [seq mulp m (pow2 i) | m <- undup s, i <- pows (count_mem m s)].

Instance Liftable_odd_uniq : Liftable odd_uniq.
Proof.
  refine {| liftable n s := _ |}; rewrite /is_partition sorted_sort_lep andbT
    sump_sort=> /andP[]/eqP<-{n}_; apply /eqP;
  move: {-1}(undup s) (erefl (undup s))=> /=u; elim: u s=> /=[|m u IH] s.
  - by move=> /undup_nil->.
  - have H: (fun i => mulp m (pow2 i)) =1 (mulp m) \o pow2 by move=> i.
    move: (eq_map H)=> ->; rewrite map_comp/= sump_cat.
    have-> t: sump [seq mulp m i | i <- t] = sval m * sump t
      by elim: t=> [|n t IHt]; rewrite mulnC //= {}IHt/=; lia.
    rewrite -map_comp/comp/= sumn_pows=> /undup_cons/andP[]/eqP E ms.
    have->: sump s = sval m * count_mem m s + sump [seq i <- s | i != m]
      by elim: s {IH E ms}=> [|n s IH]; rewrite mulnC //=IH; 
      case: eqP=> /=[->|]; lia.
    by rewrite -(IH _ E) !sump_flatten -!map_comp/comp/=; do 2 f_equal;
    apply eq_in_map=> n; rewrite -E mem_undup mem_filter
    => /andP[]nm ns; do 4 f_equal; elim: s {IH H E ms ns}=> //=k s->;
    case km: (k == m)=> //=; move: km nm=> /eqP->; rewrite eq_sym=> /negPf->.
Qed.

Lemma uniq_odd_onto n :
  {in [predI uniq & is_partition n], forall s, all odd (uniq_odd s)}.
Proof.
  by move=> s _; rewrite all_sort; apply /allP=> /=m/flattenP[]/=ks/mapP[]/=k
  _->; rewrite mem_nseq=> /andP[_/eqP->]; apply: oddn_opartn.
Qed.

Lemma odd_uniq_onto n :
  {in [predI all odd & is_partition n], forall s, uniq (odd_uniq s)}.
Proof.
  move=> s/and3P[/allP/=so sm ss]; rewrite sort_uniq; apply: allpairs_uniq_dep.
  - by apply: undup_uniq.
  - by move=> /=k _; apply: pows_uniq.
  - by move=> /=mi1 mi2/allpairsPdep/=[m1][i1][m1s i1b->]/=
      /allpairsPdep/=[m2][i2][m2s i2b->]/= /eqP/[dup]E;
    move: m1s m2s; rewrite !mem_undup=> /so m1o/so m2o;
    rewrite mulp_pow2_inj=> ///andP[/eqP<-/eqP<-].
Qed.

Lemma odd_uniqK n :
  {in [predI all odd & is_partition n], cancel odd_uniq uniq_odd}.
Proof.
  move=> s/and3P[/allP/=so sm ss]; apply sorted_lep_perm=> //.
  apply (@perm_trans _ 
           (flatten
              [seq nseq (sval (pow2 (ppart x))) (opart x)
              | x <- [seq mulp m (pow2 i)
                     | m <- undup s, i <- pows (count_mem m s)]]));
  first by apply: perm_flatten; apply: perm_map; rewrite perm_sort. 
  rewrite map_flatten -map_comp/=; apply: perm_trans (perm_count_undup _).
  have->: [seq (map (fun x => nseq (sval (pow2 (ppart x))) (opart x)) \o
               (fun m => [seq mulp m (pow2 i) | i <- pows (count_mem m s)])) m
          | m <- undup s]
        = [seq [seq nseq (sval (pow2 i)) m | i <- pows (count_mem m s)]
          | m <- undup s]
    by apply eq_in_map=> /=m; rewrite mem_undup -map_comp/comp=> /so mo; 
    apply: eq_map=> i; rewrite (ppartE mo) (opartE mo).
  match goal with |- is_true (perm_eq ?s1 ?s2) =>
                     suff->: s1 = s2 by apply: perm_refl end.
  move: {-1}(undup s) (erefl (undup s))=> u {sm ss so};
  elim: u s=> //=m u IH s/undup_cons/andP[]/eqP E _.
  rewrite -E (eq_filter_map_count_mem
                (fun z n => [seq nseq (sval (pow2 i)) z | i <- pows n]))
             (eq_filter_map_count_mem (fun z n => nseq n z)) flatten_cat E 
             (IH _ E); f_equal.
  have-> t:
    flatten [seq nseq (2 ^ i) m | i <- t] = nseq (sumn [seq 2 ^ i | i <- t]) m
    by elim: t=> //k t/=->; rewrite nseqD.
  by rewrite sumn_pows.
Qed.

Lemma mem_uniq_odd (s : seq pnat) :
  uniq s -> uniq_odd s =i [seq opart m | m <- s].
Proof.
  by move=> Us/=m; rewrite mem_sort; elim: s Us=> [|x s IH]//=/andP[H]/IH{}IH;
  rewrite mem_cat in_cons mem_nseq IH; have-> //: 0 < 2 ^ ppart x by lia.
Qed.

Lemma pows_count_uniq_odd (s : seq pnat) (m : pnat) :
  uniq s -> perm_eq (pows (count_mem m (uniq_odd s)))
                    [seq ppart x | x <- s & opart x == m].
Proof.
  move=> Us; apply: uniq_perm.
  - by apply: pows_uniq.
  - by apply: uniq_map_ppart.
  - rewrite count_sort count_flatten -map_comp/comp/=
      (eq_map (fun x => count_nseq (pred1 m) (2 ^ ppart x) (opart x)) s).
    have->: sumn [seq pred1 m (opart x) * 2 ^ ppart x | x <- s] =
            sumn [seq 2 ^ i | i <- [seq ppart x | x <- s & opart x == m]]
      by elim: s {Us}=> //=x s->; case xm: (opart x == m)=> //; rewrite mul1n.
    set u := [seq ppart x | x <- s & opart x == m];
    have Pu: perm_eq [seq 2 ^ i | i <- u] [seq 2 ^ i | i <- sort leq u]
      by rewrite -(perm_sort leq) sort_map; apply: perm_map;
      rewrite perm_sort perm_sym perm_sort.
    rewrite (perm_sumn Pu) pows_sumn. 
    + by move=> x; rewrite mem_sort.
    + by rewrite sort_uniq; apply: uniq_map_ppart.
    + by apply: sort_sorted.
Qed.

Lemma uniq_oddK n :
  {in [predI uniq & is_partition n], cancel uniq_odd odd_uniq}.
Proof.
  move=> s/=/and3P[Us _ Ss]; apply: sorted_lep_perm=> //;
  apply (@perm_trans _ 
            [seq mulp k (pow2 i)
            | k <- undup [seq opart m | m <- s],
              i <- [seq ppart x | x <- s & opart x == k]]);
  first apply: perm_allpairs_dep=> /=.
  - by apply /perm_undup/mem_uniq_odd.
  - by move=> m _; apply: pows_count_uniq_odd.
  - apply: uniq_perm=> //; last (move=> /=m; apply: iffE).
    + have: {in [seq opart m | m <- s], forall m : pnat, odd m}
        by move=> /=m/mapP/=[k _->]; rewrite /odd/opart; apply oddn_opartn.
      move: [seq opart m | m <- s]=> os H; apply allpairs_uniq_dep=> //=.
      * by apply: undup_uniq.
      * by move=> /=k _; apply: uniq_map_ppart.
      * by move=> /=[m1 i1][m2 i2]/=/allpairsPdep/=[k1][j1][];
        rewrite mem_undup=> /H k1o _[]->->/allpairsPdep/=[k2][j2][];
        rewrite mem_undup=> /H k2o _[]->->/eqP;
        rewrite (mulp_pow2_inj k1o k2o)=> /andP[/eqP<-/eqP<-].
    + by move=> /allpairsPdep/=[k][j][Hk Hj]->{m};
      move: Hk Hj; rewrite mem_undup=> /mapP/=[m] _->{k}/mapP/=[k];
      rewrite mem_filter=> /andP[]/eqP<-k_s->; rewrite mulp_pow2E.
    + move=> m_s; apply /flattenP=> /=.
      exists [seq mulp (opart m) (pow2 i)
             | i <- [seq ppart x | x <- s & opart x == opart m]].
      * by apply: map_f; rewrite mem_undup; apply: map_f.
      * by rewrite -{1}(mulp_pow2E m); do 2 apply /map_f;
        rewrite mem_filter eqxx m_s.
Qed.

Theorem Euler's_Partition (n : nat) :
  #| [set s : partition n | uniq s ] | = 
  #| [set s : partition n | all odd s ] |.
Proof.
  apply: can_card_eq 
           (lift_mapK (uniq_oddK n)) (lift_mapK (odd_uniqK n))
           (lift_map_onto (uniq_odd_onto n)) (lift_map_onto (odd_uniq_onto n)).
Qed.

(* monae: Monadic equational reasoning in Coq                                 *)
(* Copyright (C) 2020 monae authors, license: LGPL-2.1-or-later               *)
Require Import Reals Lra.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra reals Rstruct.
From infotheo Require Import ssrR Rstruct_ext Reals_ext proba.
From infotheo Require Import Reals_ext realType_ext.
Require Import monae_lib hierarchy monad_lib fail_lib proba_lib.

(******************************************************************************)
(*                            Monty Hall example                              *)
(*                                                                            *)
(* Module Set3 == a small theory about sets of three elements                 *)
(*   Sample lemma: bcoin13E_pair == matching choices: the elements h and p    *)
(*   independently chosen at random will match one third of the time          *)
(*                                                                            *)
(* Section monty_proba == Monty Hall with the probability monad               *)
(* Section monty_nondeter == nondeterministic Monty Hall                      *)
(* Section forgetful_monty == with the exceptProbMonad                        *)
(*                                                                            *)
(* references:                                                                *)
(* - J. Gibbons, R. Hinze, Just do it: simple monadic equational reasoning,   *)
(* ICFP 2011                                                                  *)
(* - J. Gibbons, Unifying Theories of Programming with Monads, UTP 2012       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.
Local Open Scope reals_ext_scope.

Module Set3.
Section set3.

Variable X : finType.
Hypothesis X3 : #|X| = 3.

Definition a := enum_val (cast_ord (esym X3) ord0).
Definition b := enum_val (cast_ord (esym X3) (lift ord0 ord0)).
Definition c := enum_val (cast_ord (esym X3) (lift ord0 (lift ord0 ord0))).

Lemma enumE : enum X = [:: a; b; c].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE X3.
case=> [_|]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/c (enum_val_nth a).
move=> n; rewrite -cardE X3; by case: n.
Qed.

Lemma a_neq_b : a != b. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma a_neq_c : a != c. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma b_neq_c : b != c. Proof. by apply/eqP => /enum_val_inj. Qed.

Lemma neq_a x : x != a -> (x == b) || (x == c).
Proof. have : x \in X by []. by rewrite -mem_enum enumE !inE => /orP[->|]. Qed.

Lemma neq_b x : x != b -> (x == a) || (x == c).
Proof.
have : x \in X by [].
rewrite -mem_enum enumE !inE => /orP[-> //|/orP[] /eqP ->];
  by rewrite ?eqxx // orbT.
Qed.

Lemma neq_c x : x != c -> (x == a) || (x == b).
Proof.
have : x \in X by [].
rewrite -mem_enum enumE !inE => /orP[-> //|/orP[] /eqP ->];
  by rewrite ?eqxx // orbT.
Qed.

Definition another (h p : X) : X := odflt a [pick d | d != h & d != p].

Lemma another_in d d' : another d d' \in enum X.
Proof. by rewrite mem_enum. Qed.

Lemma another_ab : another a b = c.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ c).
by rewrite eq_sym a_neq_c eq_sym b_neq_c.
Qed.

Lemma another_ac : another a c = b.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ b).
by rewrite eq_sym a_neq_b b_neq_c.
Qed.

Lemma another_bc : another b c = a.
Proof.
rewrite /another; case: pickP => /= [x|].
have : x \in enum X by rewrite mem_enum.
by rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx //= ?andbF.
move/(_ a).
by rewrite a_neq_b a_neq_c.
Qed.

Lemma another_sym h p : another h p = another p h.
Proof. rewrite /another; congr odflt; apply eq_pick => ?; by rewrite andbC. Qed.

Lemma another_notin h p : another h p \notin [:: h; p].
Proof.
rewrite /another; case: pickP => [x /andP[xh xp]|] /=.
  by rewrite !inE negb_or xh xp.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->; rewrite ?eqxx /= ?orbT /= ?negb_or.
move/(_ b); by rewrite eq_sym a_neq_b.
move/(_ c); by rewrite eq_sym a_neq_c eq_sym b_neq_c.
move/(_ b); by rewrite eq_sym a_neq_b b_neq_c.
move/(_ c); by rewrite eq_sym b_neq_c eq_sym a_neq_c.
move/(_ a); by rewrite a_neq_b.
move/(_ a); by rewrite a_neq_b a_neq_c.
move/(_ b); by rewrite b_neq_c eq_sym a_neq_b.
move/(_ a); by rewrite a_neq_c a_neq_b.
move/(_ a); by rewrite a_neq_c.
Qed.

Lemma filter_another h p : h != p -> enum X \\ [:: h; p] = [:: another h p].
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx //= !inE ?eqxx ?orbT /=;
    rewrite ?(negbTE a_neq_b) ?(negbTE a_neq_c) ?(negbTE b_neq_c) ?orbF /=;
    rewrite ?(eq_sym c) ?(negbTE b_neq_c) /= ?(negbTE a_neq_c) /=;
    rewrite ?(eq_sym b) ?(negbTE a_neq_b) /= => _.
by rewrite another_ab.
by rewrite another_ac.
by rewrite another_sym another_ab.
by rewrite another_bc.
by rewrite another_sym another_ac.
by rewrite another_sym another_bc.
Qed.

Lemma another_another p h : h != p -> another p (another h p) = h.
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx // => _; rewrite ?another_ab ?another_ac ?another_bc //.
by rewrite another_sym another_bc.
by rewrite (another_sym b) another_ab another_ac.
by rewrite another_sym another_ac.
by rewrite (another_sym c) another_ac another_ab.
by rewrite (another_sym c) another_bc another_sym another_ab.
Qed.

(*NB: Lemma filter1_another h p : h != p -> enum X \\ [:: p] =i [:: h; another h p]?*)
Lemma filter1_another h p : h != p ->
  enum X \\ [:: p] = [:: h; another h p] \/ enum X \\ [:: p] = [:: another h p; h].
Proof.
have : h \in enum X by rewrite mem_enum.
rewrite enumE !inE => /or3P[] /eqP ->;
  (have : p \in enum X by rewrite mem_enum);
    rewrite enumE !inE => /or3P[] /eqP ->;
    rewrite ?eqxx // => _; rewrite ?another_ab ?another_ac ?another_bc //.
by rewrite /= !inE a_neq_b eqxx /= eq_sym b_neq_c; left.
by rewrite /= !inE a_neq_c b_neq_c eqxx; left.
by rewrite /= !inE eqxx /= eq_sym a_neq_b eq_sym a_neq_c another_sym another_ab; left.
rewrite /= !inE a_neq_c b_neq_c eqxx /=; by right.
rewrite /= !inE eqxx /= eq_sym a_neq_b eq_sym a_neq_c another_sym another_ac; by right.
rewrite /= !inE a_neq_b eqxx /= eq_sym b_neq_c another_sym another_bc; by right.
Qed.

Lemma size_filter2 d d' : 0 < size (enum X \\ [:: d; d']).
Proof.
rewrite size_filter -has_count; apply/hasP.
by exists (another d d'); [rewrite another_in | exact: another_notin].
Qed.

Lemma filter_pred1 h : enum X \\ [:: h] != [::].
Proof.
rewrite -has_filter; apply/hasP.
exists (another h h); first by rewrite mem_enum.
by move: (another_notin h h); apply: contra; rewrite !inE => ->.
Qed.

Lemma head_filter def h p x : x \in [:: h; p] -> head def (enum X \\ [:: h; p]) != x.
Proof.
move=> xhp.
have : x \notin enum X \\ [:: h; p] by rewrite mem_filter xhp.
apply: contra => /eqP {1}<-.
rewrite -nth0 mem_nth // lt0n size_eq0 -has_filter; apply/hasP.
by exists (another h p); [rewrite mem_enum | rewrite another_notin].
Qed.

Local Open Scope proba_monad_scope.
Local Open Scope mprog.

Lemma uniform_unfold {M : probMonad real_realType} (P : rel X) def d :
  uniform def (enum X) >>= (fun p => Ret (P d p)) =
    Ret (P d a) <|(/ 3)%coqR%:pr|> (Ret (P d b) <|(/ 2)%coqR%:pr|> Ret (P d c)) :> M _.
Proof.
rewrite [LHS](_ : _ = fmap (fun p => P d p) (uniform def (enum X))); last first.
  by rewrite fmapE; bind_ext; case.
by rewrite -(compE (fmap _)) -(uniform_naturality _ true) enumE.
Qed.

Lemma uniform_unfold_pair {M : probMonad real_realType} def (P : rel X) :
  uniform (def, def) (cp (enum X) (enum X)) >>= (fun hp => Ret (P hp.1 hp.2)) =
  Ret (P a a) <|(/ 9)%coqR%:pr|> (Ret (P a b) <|(/ 8)%coqR%:pr|> (Ret (P a c) <|(/ 7)%coqR%:pr|>
 (Ret (P b a) <|(/ 6)%coqR%:pr|> (Ret (P b b) <|(/ 5)%coqR%:pr|> (Ret (P b c) <|(/ 4)%coqR%:pr|>
 (Ret (P c a) <|(/ 3)%coqR%:pr|> (Ret (P c b) <|(/ 2)%coqR%:pr|> Ret (P c c)))))))) :> M _.
Proof.
rewrite [LHS](_ : _ = fmap (uncurry P) (uniform (def, def) (cp (enum X) (enum X)))); last first.
  rewrite fmapE; bind_ext; by case.
by rewrite -(compE (fmap _)) -(uniform_naturality _ true) enumE.
Qed.

(* matching choices: the elements h and p independently chosen at random
   will match one third of the time *)
Lemma bcoin13E_pair {M : probMonad real_realType} def (f : bool -> M bool) :
  uniform (def, def) (cp (enum X) (enum X)) >>= (fun hp => f (hp.1 == hp.2)) =
  bcoin (/ 3)%coqR%:pr >>= f.
Proof.
transitivity (uniform (def, def) (cp (enum X) (enum X)) >>= (fun hp => Ret (hp.1 == hp.2) >>= f)).
  bind_ext => -[h p] /=; by rewrite bindretf.
rewrite -bindA uniform_unfold_pair !eqxx.
rewrite (negbTE a_neq_c).
rewrite (eq_sym b) (negbTE a_neq_b).
rewrite (negbTE b_neq_c).
rewrite 2!(eq_sym c) (negbTE a_neq_c).
rewrite (negbTE b_neq_c).
by rewrite choiceA_compute /= -uFFTE.
Qed.

Lemma bcoin23E_pair {M : probMonad real_realType} def :
  uniform (def, def) (cp (enum X) (enum X)) >>= (fun hp => Ret (hp.1 != hp.2)) =
  bcoin (/ 3)%coqR.~%:pr :> M _.
Proof.
pose P := fun a b : X => a != b.
transitivity (uniform (def, def) (cp (enum X) (enum X)) >>=
    (fun hp => Ret (P hp.1 hp.2)) : M _).
  by bind_ext.
rewrite uniform_unfold_pair {}/P !eqxx.
rewrite (negbTE a_neq_c).
rewrite (eq_sym b) (negbTE a_neq_b).
rewrite (negbTE b_neq_c).
rewrite 2!(eq_sym c) (negbTE a_neq_c).
rewrite (negbTE b_neq_c).
by rewrite choiceA_compute /= -uTTFE.
Qed.

Local Close Scope mprog.
Local Close Scope proba_monad_scope.

End set3.
End Set3.

Section monty.
Variable door : finType.
Hypothesis card_door : #|door| = 3%nat.
Let A := Set3.a card_door.
Let B := Set3.b card_door.
Let C := Set3.c card_door.
Let doors := enum door.

Definition monty {M : monad} (hide pick : M door)
  (tease strategy : door -> door -> M door) :=
  (do h <- hide ;
  do p <- pick ;
  do t <- tease h p ;
  do s <- strategy p t ;
  Ret (s == h))%Do.

Local Open Scope proba_monad_scope.

Section monty_proba.
Variable def : door.

Definition hide {M : probMonad real_realType} : M door := uniform def doors.

Definition pick {M : probMonad real_realType} : M door := uniform def doors.

Definition tease {M : probMonad real_realType} (h p : door) : M door := uniform def (doors \\ [:: h ; p]).

Definition switch {N : monad} (p t : door) : N door :=
  Ret (head def (doors \\ [:: p ; t])).

Definition stick {N : monad} (p t : door) : N door := Ret p.

Context {M : probMonad [realType of R]}.

Definition play (strategy : door -> door -> M door) :=
  monty hide pick tease strategy.

Lemma play_strategy strategy : play strategy =
  (do hp <- uniform (def, def) (cp doors doors) ;
  let h := hp.1 in let p := hp.2 in
  do t <- tease h p ;
  do s <- strategy p t;
  Ret (s == h))%Do.
Proof.
rewrite -mpair_uniform; last 2 first.
  by rewrite /doors Set3.enumE.
  by rewrite /doors Set3.enumE.
rewrite /play /monty /mpair bindA; bind_ext => x.
rewrite bindA.
by under [RHS]eq_bind do rewrite bindretf.
Qed.

Lemma hide_pickE D (f : door -> door -> M D) :
  hide >>= (fun h => pick >>= f h) =
  uniform (def, def) (cp doors doors) >>= (fun hp => f hp.1 hp.2).
Proof.
transitivity (mpair (hide, pick) >>= (fun hp => f hp.1 hp.2)).
  rewrite bindA; bind_ext => x.
  by rewrite bindA; under [RHS]eq_bind do rewrite bindretf.
by rewrite mpair_uniform // /doors Set3.enumE.
Qed.

Lemma play_stick : play stick = bcoin (/ 3)%coqR%:pr.
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors);
                  let h := hp.1 in let p := hp.2 in
                  do t <- tease h p ; Ret (p == h) : M _)%Do.
  bind_ext => x /=.
  by under eq_bind do rewrite bindretf.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp =>
              let h := hp.1 in let p := hp.2 in
              Ret (h == p)) : M _).
  (* t unused and uniform side effect-free, so tease can be eliminated *)
  bind_ext => -[x1 x2] /=.
  by rewrite /tease uniform_inde eq_sym.
by rewrite Set3.bcoin13E_pair // bindmret.
Qed.

Lemma play_switch : play switch = bcoin (/ 3)%coqR.~%:pr.
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; Ret ((head def (doors \\ [:: hp.2; t])) == hp.1) : M _)%Do.
  bind_ext => -[h p].
  by rewrite [_.1]/= [_.2]/=; under eq_bind do rewrite bindretf.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp =>
  if hp.1 == hp.2 then Ret false else Ret true : M _)).
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=.
  case: ifPn => [/eqP|] hp.
    rewrite -{2}hp.
    With (rewrite (_ : _ == _ = false)) Open (X in _ >>= X).
      by apply/negbTE/(Set3.head_filter card_door); rewrite inE eqxx.
    reflexivity.
    by rewrite /tease uniform_inde.
  rewrite /tease.
  (* TODO: could be cleaner *)
  rewrite Set3.filter_another //.
  rewrite uniform_singl // -/(head _) bindretf.
  rewrite (_ : head _ _ = h) ?eqxx //.
  rewrite Set3.filter_another /=; last first.
    move: (Set3.another_notin card_door h p).
    rewrite !inE negb_or => /andP[_]; by rewrite eq_sym.
  by rewrite Set3.another_another.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp => Ret (hp.1 != hp.2)) : M _).
  bind_ext => -[h p]; by case: ifPn.
exact: Set3.bcoin23E_pair.
Qed.

End monty_proba.

Section monty_nondeter.
Variables def : door.

Definition hide_n {M : altMonad} : M door := arbitrary def doors.

Definition tease_n {M : altMonad} (h p : door) : M door :=
  arbitrary def (doors \\ [:: h; p]).

Variable M : altProbMonad real_realType.

Definition play_n (strategy : door -> door -> M door) : M bool :=
  monty hide_n (pick def : M _) tease_n strategy.

Lemma monty_choice_your_choice_combine :
  (do h <- hide_n ; do p <- pick def : M _; Ret (h, p) =
   (do p <- pick def : M _; Ret (A, p)) [~]
   (do p <- pick def : M _ ; Ret (B, p)) [~]
   (do p <- pick def : M _; Ret (C, p)))%Do.
Proof.
pose k (h : door) : M _ := pick def >>= (fun p => Ret (h, p)).
transitivity (hide_n >>= k); first by [].
transitivity ((Ret A [~] Ret B [~] Ret C) >>= k).
  rewrite /hide_n /doors Set3.enumE /arbitrary /foldr1 [in LHS]/=.
  by rewrite -[in RHS]altA [in RHS]altC -[in RHS]altA.
by rewrite 2!alt_bindDl 3!bindretf.
Qed.

Let try (d : door) : M _ := pick def >>= (fun p => Ret (d, p)).

Local Open Scope mprog.

Lemma try_uFFT d : fmap (uncurry (fun a b => a == b)) (try d) = uFFT.
Proof.
rewrite fmapE /try bindA.
under eq_bind do rewrite bindretf.
rewrite /pick /monty.pick.
transitivity ((Ret A <| (/ 3)%coqR%:pr |> (Ret B <| (/ 2)%coqR%:pr |> Ret C)) >>= (fun p => Ret (d == p)) : M _).
  congr bind; by rewrite /doors Set3.enumE 2!uniform_cons.
rewrite 2!choice_bindDl 3!bindretf.
rewrite /uFFT 2!uniform_cons.
rewrite uniform_singl // [head _ _]/=.
have : d \in doors by rewrite mem_enum.
rewrite /doors Set3.enumE !inE => /or3P[] /eqP ->.
- rewrite eqxx (negbTE (Set3.a_neq_b _)) (negbTE (Set3.a_neq_c _)).
  rewrite choiceC.
  erewrite choiceA.
    reflexivity.
  rewrite /= /onem; split.
    rewrite -RmultE -RminusE -R1E; field.
  rewrite -RmultE -!RminusE -R1E; field.
- rewrite eq_sym (negbTE (Set3.a_neq_b _)) eqxx (negbTE (Set3.b_neq_c _)).
  congr (_ <| _ |> _).
  rewrite choiceC (@choice_ext (/ 2)%coqR%:pr) //= /onem.
  rewrite -RminusE -R1E; field.
by rewrite eq_sym (negbTE (Set3.a_neq_c _)) eq_sym (negbTE (Set3.b_neq_c _)) eqxx.
Qed.

Lemma hide_pick_nondeter :
  (do h <- hide_n; do p <- pick def : M _; Ret (h == p) = uFFT)%Do.
Proof.
transitivity (fmap (uncurry (fun a b => a == b))
  (do h <- hide_n; do p <- pick def : M _; Ret (h, p)))%Do.
rewrite fmapE !bindA; bind_ext => y1.
  by rewrite !bindA; under [RHS]eq_bind do rewrite bindretf.
rewrite monty_choice_your_choice_combine -!/(try _).
by rewrite 2!alt_fmapDr !try_uFFT 2!altmm.
Qed.

Lemma monty_stick : play_n stick = bcoin (/ 3)%coqR%:pr.
Proof.
rewrite /play_n /monty /stick.
transitivity (hide_n >>= (fun h => (pick def : M _) >>=
    (fun p => tease_n h p >> Ret (p == h)))).
  by bind_ext => d; bind_ext => d'; under eq_bind do rewrite bindretf.
transitivity (hide_n >>= (fun h => (pick def : M _) >>=
    (fun p => Ret (h == p)))).
  bind_ext => d; bind_ext => d'.
  by rewrite arbitrary_inde // 1?eq_sym // Set3.size_filter2.
by rewrite hide_pick_nondeter uFFTE.
Qed.

Lemma bcoin23E :
  arbitrary def doors >>= (fun h => uniform def doors >>= (fun p => Ret (h != p))) =
  bcoin (/ 3)%coqR.~%:pr :> M _.
Proof.
transitivity (arbitrary def doors >>= (fun h => uniform def doors >>=
    (fun p => Ret (h, p) >>= (fun x => Ret (x.1 != x.2) : M _)))).
  by bind_ext => h; under [RHS]eq_bind do rewrite bindretf.
transitivity ((arbitrary def doors >>= (fun h => uniform def doors >>=
    (fun p => Ret (h, p) : M _))) >>= (fun x => Ret (x.1 != x.2))).
  by rewrite bindA; under [RHS]eq_bind do rewrite bindA.
rewrite monty_choice_your_choice_combine /pick /monty.pick 2!alt_bindDl.
have K : forall D, (uniform def doors >>= (fun p : door => Ret (D, p))) >>=
                (fun x : door * door => Ret (x.1 != x.2)) =
              uniform def doors >>= (fun p : door => Ret (D != p)) :> M _.
  move=> D; rewrite bindA.
  by under eq_bind do rewrite bindretf.
rewrite 3!K !(@Set3.uniform_unfold _ _ _ (fun a b => a != b)) !eqxx /=.
rewrite Set3.a_neq_b Set3.b_neq_c Set3.a_neq_c eq_sym Set3.a_neq_b eq_sym.
rewrite Set3.a_neq_c eq_sym Set3.b_neq_c choicemm.
rewrite (@choiceC _ _ _ (/2)%coqR%:pr).
rewrite (@choiceA _ _ _ _ _ (/ 2)%coqR%:pr (/ 3)%coqR.~%:pr); last first.
  rewrite /onem /=; split.
    rewrite -RmultE -RminusE -R1E; field.
  rewrite -RmultE -!RminusE -R1E; field.
rewrite choicemm.
rewrite (@choiceA _ _ _ _ _ (/ 2)%coqR%:pr (/ 3)%coqR.~%:pr); last first.
  rewrite /onem /=; split.
    rewrite -RmultE -RminusE -R1E; field.
  rewrite -RmultE -!RminusE -R1E; field.
by rewrite choicemm choiceC /= 2!altmm.
Qed.

Lemma monty_switch : play_n (switch def) = bcoin (/ 3)%coqR.~%:pr.
Proof.
rewrite {1}/play_n {1}/monty /switch.
transitivity (hide_n >>= (fun h => pick def >>= (fun p => tease_n h p
    >>= (fun t => Ret (h == head def (doors \\ [:: p; t]))))) : M _).
  by bind_ext => d; bind_ext => d'; under eq_bind do rewrite bindretf eq_sym.
transitivity (hide_n >>= (fun h => pick def >>= (fun p => tease_n h p
    >> if h == p then Ret false else Ret true)) : M _).
  bind_ext => h; bind_ext => p; rewrite /tease_n.
  case: ifPn => [/eqP|] hp.
    rewrite -{2}hp.
    With (rewrite (_ : _ == _ = false)) Open (X in _ >>= X).
      by apply/negbTE; rewrite eq_sym; apply/(Set3.head_filter card_door); rewrite inE eqxx.
    reflexivity.
    by rewrite arbitrary_inde // Set3.size_filter2.
  rewrite Set3.filter_another // !arbitrary1 2!bindretf.
  rewrite Set3.filter_another //; last first.
    move: (Set3.another_notin card_door h p).
    rewrite !inE negb_or => /andP[_]; by rewrite eq_sym.
  by rewrite Set3.another_another //= eqxx.
transitivity (hide_n >>= (fun h => pick def >>= (fun p => Ret (h != p))) : M _).
  bind_ext => h; bind_ext => p.
  by rewrite /tease_n arbitrary_inde ?Set3.size_filter2 //; case: ifPn.
rewrite /hide_n /pick /monty.pick.
by rewrite bcoin23E.
Qed.

End monty_nondeter.

Section forgetful_monty.

Variable M : exceptProbMonad real_realType.
Variable def : door.

Definition tease_f (h p : door) : M door :=
  uniform def (doors \\ [:: p]) >>= (fun t => if t == h then fail else Ret t).

Definition play_f (strategy : door -> door -> M door) :=
  monty (hide def) (pick def) tease_f strategy.

Lemma tease_fE (h p : door) : let d := head def (doors \\ [:: h; p]) in
  tease_f h p = if h == p then uniform def (doors \\ [:: h])
                          else fail <| (/ 2)%coqR%:pr |> Ret d : M _.
Proof.
move=> d.
case: ifPn => [/eqP <-|hp].
  rewrite /tease_f.
  transitivity (uniform def (doors \\ [:: h]) >>= Ret : M _).
    rewrite uniform_notin //.
    exact: Set3.filter_pred1.
    by move=> ?; rewrite mem_filter inE => /andP[].
  by rewrite bindmret.
have Hd : d = Set3.another card_door h p by rewrite {}/d Set3.filter_another.
rewrite /tease_f.
transitivity (uniform def [:: h; d] >>= (fun t => if t == h then fail else Ret t) : M _).
  have hd : h != d.
    rewrite Hd.
    apply: contra (Set3.another_notin card_door h p) => /eqP <-.
    by rewrite mem_head.
  move: (Set3.filter1_another card_door hp); rewrite -/doors -Hd => -[] -> //.
  by rewrite uniform2.
rewrite uniform_cons (_ : _%:pr = (/ 2)%coqR%:pr)%R; last first.
  by apply val_inj => /=; lra.
rewrite uniform_singl // [head _ _]/= choice_bindDl 2!bindretf eqxx ifF //.
by apply/negbTE/(Set3.head_filter card_door); rewrite inE eqxx.
Qed.

Lemma monty_f_stick :
  play_f (@stick _) =
    Ret true <| (/ 3)%coqR%:pr |> (fail <| (/ 2)%coqR%:pr |> (Ret false : M _)).
Proof.
rewrite /play_f /monty hide_pickE.
rewrite /stick.
under eq_bind do rewrite bindretf tease_fE fun_if if_arg uniform_inde.
Open (X in _ >>= X).
  transitivity (if x.1 == x.2 then Ret true
    else fail <| (/ 2)%coqR%:pr |> ret _ (head def (doors \\ [:: x.1; x.2])) >> Ret false : M _).
    case: ifPn => [/eqP <-|hp]; first by rewrite eqxx.
    by rewrite eq_sym (negbTE hp).
  reflexivity.
under eq_bind do rewrite choice_bindDl bindfailf bindretf.
rewrite (Set3.bcoin13E_pair _ def (fun b => if b then Ret true else fail <| (/ 2)%coqR%:pr |> Ret false : M _)) //.
rewrite /bcoin.
by rewrite choice_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

Lemma monty_f_switch :
  play_f (@switch def _) =
    Ret false <| (/ 3)%coqR%:pr |> (fail <| (/ 2)%coqR%:pr |> (Ret true : M _)).
Proof.
rewrite /play_f /monty hide_pickE /switch.
Open (X in _ >>= X).
  under eq_bind do rewrite bindretf.
  over.
under eq_bind do rewrite tease_fE fun_if if_arg.
Open (X in _ >>= X).
transitivity (if x.1 == x.2 then uniform def (doors \\ [:: x.1]) >> Ret false
  else
   fail <| (/ 2)%coqR%:pr |> ret _ (head def (doors \\ [:: x.1; x.2])) >>= (fun x0 =>
   Ret (head def (doors \\ [:: x.2; x0]) == x.1)) : M _).
  case: x => h p; rewrite [_.1]/= [_.2]/=; case: ifPn => // /eqP <-.
  transitivity (uniform def (doors \\ [:: h]) >>= (fun x0 =>
    if head def (doors \\ [:: h; x0]) == h then Ret true else Ret false) : M _).
    bind_ext => x; by case: ifPn.
  rewrite uniform_notin //.
  exact: Set3.filter_pred1.
  move=> x; rewrite mem_filter inE=> _; by rewrite Set3.head_filter // inE eqxx.
  reflexivity.
transitivity (uniform (def, def) (cp doors doors) >>= (fun x =>
  if x.1 == x.2 then Ret false else fail <| (/ 2)%coqR%:pr |>
   Ret (head def (doors \\ [:: x.2; head def (doors \\ [:: x.1; x.2])]) == x.1)) : M _).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => [?| hp]; first by rewrite uniform_inde.
  by rewrite choice_bindDl (@bindfailf M) bindretf.
transitivity (
  uniform (def, def) (cp doors doors) >>= (fun x =>
  if x.1 == x.2
  then Ret false
  else (fail : M _) <| (/ 2)%coqR%:pr |> (Ret true : M _))).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => // hp; congr (_ <| _ |> Ret _).
  apply/eqP.
  rewrite (_ : _ \\ _ = [:: h]) //.
  rewrite Set3.filter_another; last by rewrite eq_sym Set3.head_filter // !inE eqxx orbT.
  by rewrite Set3.filter_another //= Set3.another_another.
rewrite (Set3.bcoin13E_pair _ def (fun b => if b then Ret false else fail <| (/ 2)%coqR%:pr |> Ret true)) //.
by rewrite choice_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

End forgetful_monty.

End monty.

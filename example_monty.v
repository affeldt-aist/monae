Require Import Reals Lra.
From mathcomp Require Import all_ssreflect.
From infotheo Require Import ssrR Reals_ext proba.
Require Import monae_lib hierarchy monad_lib fail_lib proba_lib.

(******************************************************************************)
(*                            Monty Hall example                              *)
(*                                                                            *)
(*             Module Set3 == a small theory about sets of three elements     *)
(*     Section monty_proba == Monty Hall with the probability monad           *)
(*  Section monty_nondeter == nondeterministic Monty Hall                     *)
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

Module Set3.
Section set3.

Variable X : finType.
Hypothesis HX : #|X| = 3.

Definition a := enum_val (cast_ord (esym HX) ord0).
Definition b := enum_val (cast_ord (esym HX) (lift ord0 ord0)).
Definition c := enum_val (cast_ord (esym HX) (lift ord0 (lift ord0 ord0))).

Lemma enumE : enum X = [:: a; b; c].
Proof.
apply (@eq_from_nth _ a); first by rewrite -cardE HX.
case=> [_|]; first by rewrite [X in _ = X]/= {2}/a (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/b (enum_val_nth a).
case=> [_|]; first by rewrite [X in _ = X]/= {1}/c (enum_val_nth a).
move=> n; rewrite -cardE HX; by case: n.
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

End set3.
End Set3.

Section monty.

Variable door : finType.
Hypothesis card_door : #|door| = 3%nat.

Let A := Set3.a card_door.
Let B := Set3.b card_door.
Let C := Set3.c card_door.
Let doors := enum door.

Lemma size_filter_doors d d' : 0 < size (doors \\ [:: d; d']).
Proof.
rewrite size_filter -has_count; apply/hasP.
exists (Set3.another card_door d d'); last exact: Set3.another_notin.
by rewrite Set3.another_in.
Qed.

(* TODO *)
Lemma head_filter def h p : forall x, x \in [:: h; p] -> head def (doors \\ [:: h; p]) != x.
Proof.
move=> x xhp.
have : x \notin doors \\ [:: h; p] by rewrite mem_filter xhp.
apply: contra => /eqP {1}<-.
rewrite -nth0 mem_nth // lt0n size_eq0 -has_filter; apply/hasP.
exists (Set3.another card_door h p); first by rewrite /doors mem_enum.
by rewrite Set3.another_notin.
Qed.

(* TODO *)
Lemma filter_pred1 h : doors \\ [:: h] != [::].
Proof.
rewrite -has_filter; apply/hasP.
exists (Set3.another card_door h h); first by rewrite mem_enum.
move: (Set3.another_notin card_door h h); apply: contra; by rewrite !inE => ->.
Qed.

Definition monty {M : monad} (hide pick : M door)
  (tease strategy : door -> door -> M door) : M bool :=
  (do h <- hide ;
  do p <- pick ;
  do t <- tease h p ;
  do s <- strategy p t ;
  Ret (s == h))%Do.

Local Open Scope proba_monad_scope.

Section monty_proba.

Let def := A.
Variable M : probMonad.
Let unif_door M := @uniform M _ def.
Let head := head def.
Let unif_pair := @uniform M _ (def, def).

Definition hide {N : probMonad} : N door := unif_door _ doors.

Definition pick {N : probMonad} : N door := unif_door _ doors.

Definition tease (h p : door) : M door := unif_door _ (doors \\ [:: h ; p]).

Definition switch {N : monad} (p t : door) : N door := Ret (head (doors \\ [:: p ; t])).

Definition stick {N : monad} (p t : door) : N door := Ret p.

Definition play (strategy : door -> door -> M door) : M bool :=
  monty hide pick tease strategy.

Lemma play_strategy strategy : play strategy =
  (do hp <- unif_pair (cp doors doors) ;
  let h := hp.1 in let p := hp.2 in
  do t <- tease h p ;
  do s <- strategy p t;
  Ret (s == h))%Do.
Proof.
rewrite /unif_pair -mpair_uniform; last 2 first.
  by rewrite /doors Set3.enumE.
  by rewrite /doors Set3.enumE.
rewrite /play /monty /mpair bindA; bind_ext => x.
rewrite bindA.
by rewrite_ bindretf.
Qed.

Local Open Scope mprog.

Lemma uniform_doors_unfold (P : rel door) :
  uniform (def, def) (cp doors doors) >>= (fun hp => Ret (P hp.1 hp.2)) =
  Ret (P A A) <|(/ 9)%:pr|> (Ret (P A B) <|(/ 8)%:pr|> (Ret (P A C) <|(/ 7)%:pr|>
 (Ret (P B A) <|(/ 6)%:pr|> (Ret (P B B) <|(/ 5)%:pr|> (Ret (P B C) <|(/ 4)%:pr|>
 (Ret (P C A) <|(/ 3)%:pr|> (Ret (P C B) <|(/ 2)%:pr|> Ret (P C C)))))))) :> M _.
Proof.
rewrite [LHS](_ : _ = fmap (uncurry P) (uniform (def, def) (cp doors doors))); last first.
  rewrite fmapE; bind_ext; by case.
rewrite -(compE (fmap _)) -(uniform_naturality _ true); last first.
  by rewrite /doors Set3.enumE.
by rewrite /doors Set3.enumE.
Qed.

(* matching choices: the doors h and p independently chosen at random
   will match one third of the time *)
Lemma bcoin13E (f : bool -> M bool) :
  uniform (def, def) (cp doors doors) >>= (fun hp => f (hp.1 == hp.2)) =
  bcoin (/ 3)%:pr >>= f.
Proof.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp => Ret (hp.1 == hp.2) >>= f)).
  bind_ext => -[h p] /=; by rewrite bindretf.
rewrite -bindA uniform_doors_unfold !eqxx.
rewrite (negbTE (Set3.a_neq_c card_door)).
rewrite (eq_sym B) (negbTE (Set3.a_neq_b card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
rewrite 2!(eq_sym C) (negbTE (Set3.a_neq_c card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
by rewrite choiceA_compute /= -uFFTE.
Qed.

Lemma bcoin23E :
  uniform (def, def) (cp doors doors) >>= (fun hp => Ret (hp.1 != hp.2)) =
  bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
pose P := fun a b : door => a != b.
transitivity
  (uniform (def, def) (cp doors doors) >>= (fun hp => Ret (P hp.1 hp.2)) : M _).
  by bind_ext.
rewrite uniform_doors_unfold {}/P !eqxx.
rewrite (negbTE (Set3.a_neq_c card_door)).
rewrite (eq_sym B) (negbTE (Set3.a_neq_b card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
rewrite 2!(eq_sym C) (negbTE (Set3.a_neq_c card_door)).
rewrite (negbTE (Set3.b_neq_c card_door)).
by rewrite choiceA_compute /= -uTTFE.
Qed.

Lemma hide_pickE D (f : door -> door -> M D) :
  hide >>= (fun h => pick >>= f h) =
  uniform (def, def) (cp doors doors) >>= (fun hp => f hp.1 hp.2).
Proof.
transitivity (mpair (hide, pick) >>= (fun hp => f hp.1 hp.2)).
  rewrite bindA; bind_ext => x.
  rewrite bindA; by rewrite_ bindretf.
by rewrite mpair_uniform // /doors Set3.enumE.
Qed.

Lemma play_stick : play stick = bcoin (/ 3)%:pr.
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors) ;
                  let h := hp.1 in let p := hp.2 in
                  do t <- tease h p ; Ret (p == h))%Do.
  bind_ext => x /=.
  by rewrite_ bindretf.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp =>
              let h := hp.1 in let p := hp.2 in
              Ret (h == p)) : M _).
  (* t unused and uniform side effect-free, so tease can be eliminated *)
  bind_ext => -[x1 x2] /=.
  by rewrite /tease /unif_door uniform_inde eq_sym.
by rewrite bcoin13E bindmret.
Qed.

Lemma play_switch : play switch = bcoin (@Prob.mk (2/3) H23).
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; Ret ((head (doors \\ [:: hp.2; t])) == hp.1))%Do.
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=; by rewrite_ bindretf.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp =>
  if hp.1 == hp.2 then Ret false else Ret true : M _)).
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=.
  case: ifPn => [/eqP|] hp.
    rewrite -{2}hp.
    With (rewrite (_ : _ == _ = false)) Open (X in _ >>= X).
      apply/negbTE/head_filter; by rewrite inE eqxx.
    reflexivity.
    by rewrite /tease /unif_door uniform_inde.
  rewrite /tease /unif_door.
  (* TODO: could be cleaner *)
  rewrite Set3.filter_another //.
  rewrite uniform_singl // -/(head _) bindretf.
  rewrite (_ : head _ = h) ?eqxx //.
  rewrite Set3.filter_another /=; last first.
    move: (Set3.another_notin card_door h p).
    rewrite !inE negb_or => /andP[_]; by rewrite eq_sym.
  by rewrite Set3.another_another.
transitivity (uniform (def, def) (cp doors doors) >>= (fun hp => Ret (hp.1 != hp.2)) : M _).
  bind_ext => -[h p]; by case: ifPn.
exact: bcoin23E.
Qed.

End monty_proba.

Section monty_nondeter.

Definition hide_n {M : altMonad} : M door := arbitrary A doors.

Definition tease_n {M : altMonad} (h p : door) : M door :=
  arbitrary A (doors \\ [:: h; p]).

Variable M : altProbMonad.

Let pick : M door := @pick _.
Definition play_n (strategy : door -> door -> M door) : M bool :=
  monty hide_n pick tease_n strategy.

Lemma monty_choice_your_choice_combine :
  (do h <- hide_n ; do p <- pick; Ret (h, p) =
   (do p <- pick; Ret (A, p)) [~]
   (do p <- pick; Ret (B, p)) [~]
   (do p <- pick; Ret (C, p)))%Do.
Proof.
pose k (h : door) := pick >>= (fun p => Ret (h, p)).
transitivity (hide_n >>= k); first by [].
transitivity ((Ret A [~] Ret B [~] Ret C) >>= k).
  rewrite /hide_n /doors Set3.enumE /arbitrary /foldr1 [in LHS]/=.
  by rewrite -[in RHS]altA [in RHS]altC -[in RHS]altA.
by rewrite 2!alt_bindDl 3!bindretf.
Qed.

Let try (d : door) := pick >>= (fun p => Ret (d, p)).

Local Open Scope mprog.

Lemma try_uFFT d : fmap (uncurry (fun a b => a == b)) (try d) = uFFT.
Proof.
rewrite fmapE /try bindA.
rewrite_ bindretf.
rewrite /pick /monty.pick.
transitivity ((Ret A <| (/ 3)%:pr |> (Ret B <| (/ 2)%:pr |> Ret C)) >>= (fun p => Ret (d == p)) : M _).
  congr Bind; by rewrite /doors Set3.enumE 2!uniform_cons.
rewrite 2!prob_bindDl 3!bindretf.
rewrite /uFFT 2!uniform_cons.
rewrite uniform_singl // [head _ _]/=.
have : d \in doors by rewrite mem_enum.
rewrite /doors Set3.enumE !inE => /or3P[] /eqP ->.
- rewrite eqxx (negbTE (Set3.a_neq_b _)) (negbTE (Set3.a_neq_c _)).
  rewrite choiceC.
  erewrite choiceA.
    reflexivity.
  rewrite /= /onem; lra.
- rewrite eq_sym (negbTE (Set3.a_neq_b _)) eqxx (negbTE (Set3.b_neq_c _)).
  congr (_ <| _ |> _).
  rewrite choiceC (@choice_ext (/ 2)%:pr) //= /onem; lra.
by rewrite eq_sym (negbTE (Set3.a_neq_c _)) eq_sym (negbTE (Set3.b_neq_c _)) eqxx.
Qed.

Lemma hide_pick_nondeter : (do h <- hide_n; do p <- pick; Ret (h == p) = uFFT)%Do.
Proof.
transitivity (fmap (uncurry (fun a b => a == b)) (do h <- hide_n; do p <- pick; Ret (h, p)))%Do.
rewrite fmapE !bindA; bind_ext => y1.
  rewrite !bindA; by rewrite_ bindretf.
rewrite monty_choice_your_choice_combine -!/(try _).
by rewrite 2!naturality_nondeter !try_uFFT 2!altmm.
Qed.

Lemma monty_stick : play_n stick = bcoin (/ 3)%:pr.
Proof.
rewrite /play_n /monty /stick.
transitivity (
  hide_n >>= (fun h : door => pick >>= (fun p : door => tease_n h p >> Ret (p == h)))
).
  by bind_ext => d; bind_ext => d'; rewrite_ bindretf.
transitivity (
  hide_n >>= (fun h : door => pick >>= (fun p : door => Ret (h == p)))
).
  bind_ext => d; bind_ext => d'.
  by rewrite arbitrary_inde // 1?eq_sym // size_filter_doors.
by rewrite hide_pick_nondeter uFFTE.
Qed.

Lemma uniform_doors_unfold' (P : rel door) def d :
  uniform def doors >>= (fun p => Ret (P d p)) = Ret (P d A) <|(/ 3)%:pr|> (Ret (P d B) <|(/ 2)%:pr|> Ret (P d C)) :> M _.
Proof.
rewrite [LHS](_ : _ = fmap (fun p => P d p) (uniform def doors)); last first.
  rewrite fmapE; bind_ext; by case.
rewrite -(compE (fmap _)) -(uniform_naturality _ true); last first.
  by rewrite /doors Set3.enumE.
by rewrite /doors Set3.enumE.
Qed.

Lemma bcoin23E' :
  arbitrary A doors >>= (fun h : door => uniform A doors >>= (fun p : door => Ret (h != p) : M _)) =
  bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
transitivity (
  arbitrary A doors >>= (fun h : door => uniform A doors >>= (fun p : door => Ret (h, p) >>= (fun x => Ret (x.1 != x.2) : M bool)))
).
  by bind_ext => h; rewrite_ bindretf.
transitivity (
  (arbitrary A doors >>= (fun h : door => uniform A doors >>= (fun p : door => Ret (h, p) : M _))) >>= (fun x => Ret (x.1 != x.2) : M bool)
).
  by rewrite bindA; rewrite_ bindA.
rewrite monty_choice_your_choice_combine /pick /monty.pick 2!alt_bindDl.
have K : forall D, (uniform A doors >>= (fun p : door => Ret (D, p))) >>= (fun x : door * door => Ret (x.1 != x.2)) = (uniform A doors >>= (fun p : door => Ret (D != p))) :> M _.
  move=> D; rewrite bindA.
  by rewrite_ bindretf.
rewrite 3!K !(@uniform_doors_unfold' (fun a b => a != b)) !eqxx /=.
rewrite Set3.a_neq_b Set3.b_neq_c Set3.a_neq_c eq_sym Set3.a_neq_b eq_sym.
rewrite Set3.a_neq_c eq_sym Set3.b_neq_c choicemm.
rewrite (@choiceC _ _ (/2)%:pr) (@choiceA _ _ _ _ (/ 2)%:pr (@Prob.mk _ H23)%:pr); last first.
  by rewrite /onem /=; split; field.
rewrite choicemm.
rewrite (@choiceA _ _ _ _ (/ 2)%:pr (@Prob.mk _ H23)%:pr); last first.
  by rewrite /onem /=; split; field.
rewrite choicemm choiceC /onem /=.
set X := (X in _ <| X |> _).
have -> : X = @Prob.mk (2 / 3) H23 by apply prob_ext => /=; field.
by rewrite 2!altmm /bcoin.
Qed.

Lemma monty_switch : play_n switch = bcoin (@Prob.mk (2/3) H23).
Proof.
rewrite {1}/play_n {1}/monty /switch.
transitivity (
  hide_n >>=
  (fun h : door => pick >>= (fun p : door => tease_n h p >>= (fun t : door => Ret (h == head A (doors \\ [:: p; t])))))
).
  by bind_ext => d; bind_ext => d'; rewrite_ bindretf; rewrite_ eq_sym.
transitivity (
  hide_n >>= (fun h : door => pick >>= (fun p : door => tease_n h p >> if h == p then Ret false else Ret true))
).
  bind_ext => h; bind_ext => p; rewrite /tease_n.
  case: ifPn => [/eqP|] hp.
    rewrite -{2}hp.
    With (rewrite (_ : _ == _ = false)) Open (X in _ >>= X).
      apply/negbTE; rewrite eq_sym; apply/head_filter; by rewrite inE eqxx.
    reflexivity.
    by rewrite arbitrary_inde // size_filter_doors.
  rewrite Set3.filter_another // !arbitrary1 2!bindretf.
  rewrite Set3.filter_another //; last first.
    move: (Set3.another_notin card_door h p).
    rewrite !inE negb_or => /andP[_]; by rewrite eq_sym.
  by rewrite Set3.another_another //= eqxx.
transitivity (hide_n >>= (fun h : door => pick >>= (fun p : door => Ret (h != p)) : M _)).
  bind_ext => h; bind_ext => p.
  by rewrite /tease_n arbitrary_inde ?size_filter_doors //; case: ifPn.
rewrite /hide_n /pick /monty.pick.
by rewrite bcoin23E'.
Qed.

End monty_nondeter.

Section forgetful_monty.

Variable M : exceptProbMonad.
Let def := A.
Let unif_door : _ -> M _ := @uniform _ _ def.

Definition tease_f (h p : door) : M door :=
  unif_door (doors \\ [:: p]) >>= (fun t => if t == h then Fail else Ret t).

Definition play_f (strategy : door -> door -> M door) : M bool :=
  monty hide pick tease_f strategy.

Lemma tease_fE (h p : door) : let d := head def (doors \\ [:: h; p]) in
  tease_f h p = if h == p then unif_door (doors \\ [:: h])
                          else (Fail : M _) <| (/ 2)%:pr |> (Ret d : M _).
Proof.
move=> d.
case: ifPn => [/eqP <-|hp].
  rewrite /tease_f.
  transitivity (unif_door (doors \\ [:: h]) >>= Ret).
    rewrite /unif_door uniform_notin //.
    exact: filter_pred1.
    move=> ?; by rewrite mem_filter inE => /andP[].
  by rewrite bindmret.
have Hd : d = Set3.another card_door h p by rewrite {}/d Set3.filter_another.
rewrite /tease_f.
transitivity (unif_door [:: h; d] >>= (fun t => if t == h then Fail else Ret t)).
  have hd : h != d.
    rewrite Hd.
    apply: contra (Set3.another_notin card_door h p) => /eqP <-.
    by rewrite mem_head.
  move: (Set3.filter1_another card_door hp); rewrite -/doors -Hd => -[] -> //.
  by rewrite /unif_door uniform2.
rewrite /unif_door uniform_cons (_ : _%:pr = (/ 2)%:pr)%R; last first.
  by apply prob_ext => /=; lra.
rewrite uniform_singl // [head _ _]/= prob_bindDl 2!bindretf eqxx ifF //.
apply/negbTE/head_filter; by rewrite inE eqxx.
Qed.

Lemma monty_f_stick :
  play_f (@stick _) =
    Ret true <| (/ 3)%:pr |> ((Fail : M _) <| (/ 2)%:pr |> (Ret false : M _)).
Proof.
rewrite /play_f /monty hide_pickE.
rewrite /stick.
rewrite_ bindretf.
rewrite_ tease_fE.
rewrite_ fun_if.
rewrite_ if_arg.
rewrite_ uniform_inde.
Open (X in _ >>= X).
  transitivity (if x.1 == x.2
    then Ret true
    else ((Fail : M _) <| (/ 2)%:pr |> @RET M _ (head def (doors \\ [:: x.1; x.2]))) >> Ret false).
    case: ifPn => [/eqP <-|hp]; first by rewrite eqxx.
    by rewrite eq_sym (negbTE hp).
  reflexivity.
rewrite_ prob_bindDl.
rewrite_ (@bindfailf M). (* TODO *)
rewrite_ bindretf.
rewrite (bcoin13E (fun b => if b then Ret true else (Fail : M _) <| (/ 2)%:pr |> (Ret false : M _))).
rewrite /bcoin.
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

Lemma monty_f_switch :
  play_f (@switch _) =
    Ret false <| (/ 3)%:pr |> ((Fail : M _) <| (/ 2)%:pr |> (Ret true : M _)).
Proof.
rewrite /play_f /monty hide_pickE /switch.
Open (X in _ >>= X).
  rewrite_ bindretf.
  reflexivity.
rewrite_ tease_fE.
rewrite_ fun_if.
rewrite_ if_arg.
Open (X in _ >>= X).
transitivity (if x.1 == x.2
  then unif_door (doors \\ [:: x.1]) >> Ret false
  else
   ((Fail : M _) <| (/ 2)%:pr |> @RET M _ (head def (doors \\ [:: x.1; x.2]))) >>= (fun x0 =>
   Ret (head A (doors \\ [:: x.2; x0]) == x.1))).
  case: x => h p; rewrite [_.1]/= [_.2]/=; case: ifPn => // /eqP <-.
  transitivity (unif_door (doors \\ [:: h]) >>= (fun x0 =>
    if (head A (doors \\ [:: h; x0]) == h) then Ret true else Ret false)).
    bind_ext => x; by case: ifPn.
  rewrite {1}/unif_door uniform_notin //.
  exact: filter_pred1.
  move=> x; rewrite mem_filter inE=> _; by rewrite head_filter // inE eqxx.
  reflexivity.
transitivity (uniform (A, A) (cp doors doors) >>= (fun x =>
  if x.1 == x.2
  then Ret false
  else
   (Fail : M _)
   <| (/ 2)%:pr |>
   (@RET M _ (head A (doors \\ [:: x.2; head def (doors \\ [:: x.1; x.2])]) == x.1)) : M _)).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => [?| hp]; first by rewrite uniform_inde.
  by rewrite prob_bindDl (@bindfailf M) bindretf.
transitivity (
  uniform (A, A) (cp doors doors) >>= (fun x =>
  if x.1 == x.2
  then Ret false
  else (Fail : M _) <| (/ 2)%:pr |> (Ret true : M _))).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => // hp; congr (_ <| _ |> Ret _).
  apply/eqP.
  rewrite (_ : _ \\ _ = [:: h]) //.
  rewrite Set3.filter_another; last by rewrite eq_sym head_filter // !inE eqxx orbT.
  by rewrite Set3.filter_another //= Set3.another_another.
rewrite (bcoin13E (fun b => if b then Ret false else (Fail : M _) <| (/ 2)%:pr |> (Ret true : M _))).
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

End forgetful_monty.

End monty.

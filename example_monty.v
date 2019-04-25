Require Import Reals Lra ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From infotheo Require Import ssrR Reals_ext proba.
Require Import monad proba_monad.

(* from gibbons2011icfp and gibbonsUTP2012

Contents:
- Module Set3.
    a small theory about sets of three elements for the Monty Hall example
- Section monty
  + using the probabilistic choice only
  + probabilistic choice and non-deterministic choice
  + Section forgetful_monty.
    probabilistic choice and exception
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  do h <- hide ;
  do p <- pick ;
  do t <- tease h p ;
  do s <- strategy p t ;
  Ret (s == h).

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
  do hp <- unif_pair (cp doors doors) ;
  let h := hp.1 in let p := hp.2 in
  do t <- tease h p ;
  do s <- strategy p t;
  Ret (s == h).
Proof.
rewrite /unif_pair -mpair_uniform; last 2 first.
  by rewrite /doors Set3.enumE.
  by rewrite /doors Set3.enumE.
rewrite /play /monty /mpair bindA; bind_ext => x.
rewrite bindA.
by rewrite_ bindretf.
Qed.

Lemma uniform_doors_unfold (P : rel door) :
  do hp <- uniform (def, def) (cp doors doors); Ret (P hp.1 hp.2) =
  Ret (P A A) <|`Pr / 9|> (Ret (P A B) <|`Pr / 8|> (Ret (P A C) <|`Pr / 7|>
 (Ret (P B A) <|`Pr / 6|> (Ret (P B B) <|`Pr / 5|> (Ret (P B C) <|`Pr / 4|>
 (Ret (P C A) <|`Pr / 3|> (Ret (P C B) <|`Pr / 2|> Ret (P C C)))))))) :> M _.
Proof.
rewrite [LHS](_ : _ = fmap (uncurry P) (uniform (def, def) (cp doors doors))); last first.
  rewrite fmapE; bind_ext; by case.
rewrite {1}/fmap -(compE (M # _)) -(uniform_naturality _ true); last first.
  by rewrite /doors Set3.enumE.
by rewrite /doors Set3.enumE.
Qed.

(* matching choices: the doors h and p independently chosen at random
   will match one third of the time *)
Lemma bcoin13E (f : bool -> M bool) :
  do hp <- uniform (def, def) (cp doors doors); f (hp.1 == hp.2) =
  do b <- bcoin (`Pr /3); f b.
Proof.
transitivity (do hp <- uniform (def, def) (cp doors doors); Ret (hp.1 == hp.2) >>= f).
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
  do hp <- uniform (def, def) (cp doors doors); Ret (hp.1 != hp.2) =
  bcoin (@Prob.mk (2/3) H23) :> M _.
Proof.
pose P := fun a b : door => a != b.
transitivity
  (do hp <- uniform (def, def) (cp doors doors); Ret (P hp.1 hp.2) : M _).
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
  do h <- hide ; do p <- pick ; f h p =
  do hp <- uniform (def, def) (cp doors doors) ; f hp.1 hp.2.
Proof.
transitivity (do hp <- mpair (hide, pick); f hp.1 hp.2).
  rewrite bindA; bind_ext => x.
  rewrite bindA; by rewrite_ bindretf.
by rewrite mpair_uniform // /doors Set3.enumE.
Qed.

Lemma play_stick : play stick = bcoin (`Pr /3).
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors) ;
                  let h := hp.1 in let p := hp.2 in
                  do t <- tease h p ; Ret (p == h)).
  bind_ext => x /=.
  by rewrite_ bindretf.
transitivity (do hp <- uniform (def, def) (cp doors doors) ;
              let h := hp.1 in let p := hp.2 in
              Ret (h == p) : M _).
  (* t unused and uniform side effect-free, so tease can be eliminated *)
  bind_ext => -[x1 x2] /=.
  by rewrite /tease /unif_door uniform_inde eq_sym.
by rewrite bcoin13E bindmret.
Qed.

Lemma play_switch : play switch = bcoin (@Prob.mk (2/3) H23).
Proof.
rewrite {1}/play {1}/monty hide_pickE.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; do s <- Ret (head (doors \\ [:: hp.2; t])); Ret (s == hp.1)).
  by [].
transitivity (do hp <- uniform (def, def) (cp doors doors);
  do t <- tease hp.1 hp.2; Ret ((head (doors \\ [:: hp.2; t])) == hp.1)).
  bind_ext => -[h p].
  rewrite [_.1]/= [_.2]/=; by rewrite_ bindretf.
transitivity (do hp <- uniform (def, def) (cp doors doors);
  if hp.1 == hp.2 then Ret false else Ret true : M _).
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
transitivity (do hp <- uniform (def, def) (cp doors doors); Ret (hp.1 != hp.2) : M _).
  bind_ext => -[h p]; by case: ifPn.
exact: bcoin23E.
Qed.

End monty_proba.

Section monty_nondeter.

Variable M : altProbMonad.

Definition hide_n : M door := arbitrary A doors.
Definition tease_n (h p : door) : M door := arbitrary A (doors \\ [:: h; p]).
Let pick : M door := @pick _.
Definition play_n (strategy : door -> door -> M door) : M bool :=
  monty hide_n pick tease_n strategy.

Lemma monty_choice_your_choice_combine :
  do h <- hide_n ; do p <- pick; Ret (h, p) =
  (do p <- pick; Ret (A, p)) [~]
  (do p <- pick; Ret (B, p)) [~]
  (do p <- pick; Ret (C, p)).
Proof.
pose k (h : door) := do p <- pick; Ret (h, p).
transitivity (do h <- hide_n; k h); first by [].
transitivity (do h <- (Ret A [~] Ret B [~] Ret C); k h).
  rewrite /hide_n /doors Set3.enumE /arbitrary /foldr1 [in LHS]/=.
  by rewrite -[in RHS]altA [in RHS]altC -[in RHS]altA.
by rewrite 2!alt_bindDl 3!bindretf.
Qed.

Let try (d : door) := do p <- pick; Ret (d, p).

Lemma try_uFFT d : fmap (uncurry (fun a b => a == b)) (try d) = uFFT.
Proof.
rewrite fmapE /try bindA.
rewrite_ bindretf.
rewrite /pick /monty.pick.
transitivity (do p <- Ret A <| `Pr /3 |> (Ret B <| `Pr /2 |> Ret C); Ret (d == p) : M _).
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
  rewrite choiceC (@choice_ext (`Pr /2)) //= /onem; lra.
by rewrite eq_sym (negbTE (Set3.a_neq_c _)) eq_sym (negbTE (Set3.b_neq_c _)) eqxx.
Qed.

Lemma hide_pick_nondeter : do h <- hide_n; do p <- pick; Ret (h == p) = uFFT.
Proof.
transitivity (fmap (uncurry (fun a b => a == b)) (do h <- hide_n; do p <- pick; Ret (h, p))).
  rewrite fmapE !bindA; bind_ext => y1.
  rewrite !bindA; by rewrite_ bindretf.
rewrite monty_choice_your_choice_combine -!/(try _).
by rewrite 2!naturality_nondeter !try_uFFT 2!altmm.
Qed.

End monty_nondeter.

Section forgetful_monty.

Variable M : exceptProbMonad.
Let def := A.
Let unif_door : _ -> M _ := @uniform _ _ def.

Definition tease_f (h p : door) : M door :=
  do t <- unif_door (doors \\ [:: p]); if t == h then Fail else Ret t.

Definition play_f (strategy : door -> door -> M door) : M bool :=
  monty hide pick tease_f strategy.

Lemma tease_fE (h p : door) : let d := head def (doors \\ [:: h; p]) in
  tease_f h p = if h == p then unif_door (doors \\ [:: h])
                          else (Fail : M _) <| `Pr /2 |> (Ret d : M _).
Proof.
move=> d.
case: ifPn => [/eqP <-|hp].
  rewrite /tease_f.
  transitivity (do t <- unif_door (doors \\ [:: h]); Ret t).
    rewrite /unif_door uniform_notin //.
    exact: filter_pred1.
    move=> ?; by rewrite mem_filter inE => /andP[].
  by rewrite bindmret.
have Hd : d = Set3.another card_door h p by rewrite {}/d Set3.filter_another.
rewrite /tease_f.
transitivity (do t <- unif_door [:: h; d]; if t == h then Fail else Ret t).
  have hd : h != d.
    rewrite Hd.
    apply: contra (Set3.another_notin card_door h p) => /eqP <-.
    by rewrite mem_head.
  move: (Set3.filter1_another card_door hp); rewrite -/doors -Hd => -[] -> //.
  by rewrite /unif_door uniform2.
rewrite /unif_door uniform_cons (_ : `Pr _ = `Pr /2)%R; last first.
  by apply prob_ext => /=; lra.
rewrite uniform_singl // [head _ _]/= prob_bindDl 2!bindretf eqxx ifF //.
apply/negbTE/head_filter; by rewrite inE eqxx.
Qed.

Lemma monty_f_stick :
  play_f (@stick _) =
    Ret true <| `Pr /3 |> ((Fail : M _) <| `Pr /2 |> (Ret false : M _)).
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
    else do _ <- (Fail : M _) <| `Pr /2 |> (Ret (head def (doors \\ [:: x.1; x.2])) : M _); Ret false).
    case: ifPn => [/eqP <-|hp]; first by rewrite eqxx.
    by rewrite eq_sym (negbTE hp).
  reflexivity.
rewrite_ prob_bindDl.
rewrite_ (@bindfailf M). (* TODO *)
rewrite_ bindretf.
rewrite (bcoin13E (fun b => if b then Ret true else (Fail : M _) <| `Pr / 2 |> (Ret false : M _))).
rewrite /bcoin.
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

Lemma monty_f_switch :
  play_f (@switch _) =
    Ret false <| `Pr /3 |> ((Fail : M _) <| `Pr /2 |> (Ret true : M _)).
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
  then do x0 <- unif_door (doors \\ [:: x.1]); Ret false
  else
   do x0 <- (Fail : M _) <| `Pr /2 |> (Ret (head def (doors \\ [:: x.1; x.2])) : M _);
   Ret (head A (doors \\ [:: x.2; x0]) == x.1)).
  case: x => h p; rewrite [_.1]/= [_.2]/=; case: ifPn => // /eqP <-.
  transitivity (do x0 <- unif_door (doors \\ [:: h]);
    if (head A (doors \\ [:: h; x0]) == h) then Ret true else Ret false).
    bind_ext => x; by case: ifPn.
  rewrite {1}/unif_door uniform_notin //.
  exact: filter_pred1.
  move=> x; rewrite mem_filter inE=> _; by rewrite head_filter // inE eqxx.
  reflexivity.
transitivity (do x <- uniform (A, A) (cp doors doors);
  if x.1 == x.2
  then Ret false
  else
   (Fail : M _)
   <| `Pr /2 |>
   (Ret (head A (doors \\ [:: x.2; head def (doors \\ [:: x.1; x.2])]) == x.1) : M _)).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => [?| hp]; first by rewrite uniform_inde.
  by rewrite prob_bindDl (@bindfailf M) bindretf.
transitivity (
  do x <- uniform (A, A) (cp doors doors);
  if x.1 == x.2
  then Ret false
  else (Fail : M _) <| `Pr /2 |> (Ret true : M _)).
  bind_ext => -[h p]; rewrite [_.1]/= [_.2]/=.
  case: ifPn => // hp; congr (_ <| _ |> Ret _).
  apply/eqP.
  rewrite (_ : _ \\ _ = [:: h]) //.
  rewrite Set3.filter_another; last by rewrite eq_sym head_filter // !inE eqxx orbT.
  by rewrite Set3.filter_another //= Set3.another_another.
rewrite (bcoin13E (fun b => if b then Ret false else (Fail : M _) <| `Pr /2 |> (Ret true : M _))).
by rewrite prob_bindDl 2!bindretf.
(* TODO: flattening choices *)
Qed.

End forgetful_monty.

End monty.

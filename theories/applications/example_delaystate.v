From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.
Require Import preamble hierarchy monad_lib fail_lib state_lib.

Local Open Scope monae_scope.
Notation "a '≈' b" := (wBisim a b).

Local Open Scope do_notation.

Section delaystatenat_example.
Variable M : delayStateMonad nat.

Definition factds_body: nat -> M (unit + nat)%type :=
fun (m:nat) => ((do s <- (@get nat M) ;
              match m with
             |O => do _ <- (@put nat M s) ;
                 (@ret M _ (inl tt))
           |m'.+1 => do _<- (@put nat M (m * s )) ; (@ret M _ (inr m'))
         end)).
(*
Definition factds_body: nat -> M (unit + nat)%type :=
fun (m:nat) => (((@get nat M)) >>= (fun s => match m with
           |O => (@put nat M s) >> (@ret M _ (inl tt))
           |m'.+1 => (@put nat M (m * s )) >> (@ret M _ (inr m'))
         end)).
*)

Definition factds := while factds_body.
Fixpoint fact (n:nat): nat := match n with |O => 1 |m.+1 => n * fact m end.
Definition sumds_body:nat -> M (unit + nat)%type :=
fun (m:nat) => (((@get nat M)) >>= (fun s => (@put nat M (m + s ))))
>> (*((@get nat M) >>=fun (k:nat) =>*) match m with
           |O => (@ret M _ (inl tt))
           |m'.+1 => (@ret M _ (inr m'))
         end.

Lemma factE (n:nat) : factds n ≈ (@get _ M) >>= (fun s => let res := fact n in (@put _ M (res * s)) >> (@ret M _ tt)).
Proof.
rewrite/factds/factds_body.
elim: n => /= [| n' IH].
rewrite fixpointE /=.
rewrite !bindA.
apply: bindfwB => a.
by rewrite bindA bindretf /= mulSn mul0n addn0.
rewrite/factds/factds_body fixpointE /=.
rewrite bindA.
apply: bindfwB => a.
rewrite bindA bindretf /=.
move: IH.
set h:= while _ _.
move => IH.
(*have H: forall (a: unit), (fun x => h ) a ≈ (fun x => get >>= (fun s : nat => put (sum n' + s) >> Ret tt)) a.
  by [].*)
apply: wBisim_trans.
apply: bindfwB => a'.
apply IH.
rewrite -bindA -bindA -bindA.
rewrite putget.
rewrite bindA bindA.
rewrite bindretf.
rewrite -bindA.
rewrite putput.
by rewrite mulnA (mulnC (fact n') _).
Qed.

Definition sumds := while sumds_body.
Fixpoint sum (n:nat) : nat := match n with |O => 0 |m.+1 => n + sum m end.

Lemma sumE (n:nat) : sumds n ≈ (@get _ M) >>= (fun s => let res := sum n in (@put _ M (res + s)) >> (@ret M _ tt)).
Proof.
rewrite/sumds/sumds_body.
elim: n => /= [| n' IH].
rewrite fixpointE.
rewrite bindA bindA.
apply: bindfwB => a.
by rewrite bindA bindretf /=.
rewrite/sumds/sumds_body fixpointE. About eq_bind.
rewrite bindA bindA.
apply: bindfwB => a.
rewrite bindA bindretf /=.
move: IH.
set h:= while _ _.
move => IH.
(*have H: forall (a: unit), (fun x => h ) a ≈ (fun x => get >>= (fun s : nat => put (sum n' + s) >> Ret tt)) a.
  by [].*)
apply: wBisim_trans.
apply: bindfwB => a'.
apply IH.
rewrite -bindA -bindA -bindA.
rewrite putget.
rewrite bindA bindA.
rewrite bindretf.
rewrite -bindA.
rewrite putput.
rewrite addnCA.
Search (_ + _ + _).
by rewrite addnA.
Qed.

(*
Lemma sumE (n: nat) : (@put _ M (sum n)) ≈ (@put _ M 0) >> sumds n.
Proof.*)
(*
rewrite/sumds/sumds_body.
elim: n => /= [|n'].
- set h := while _ .
  have H : forall (a: unit), (fun a => h 0) a ≈ (fun a => ((get >> Ret (inl tt)) >>= sum_rect (fun=> M unit) Ret h)) a .
    subst h.
    move => a.
    rewrite fixpointE /=.
    have -> : (fun n => put (n + 0)) = put.
      move => t.
      apply funext => n.
      by rewrite addn0.
    rewrite getput.
    by rewrite bindskipf.
  rewrite (bindfwB _ _ _ _ _ H).
  rewrite -bindA -bindA.
  rewrite putget.
  rewrite bindA bindA bindretf bindretf /=.
  (*putの構造を見ないと示せない*)
    *)
End delaystatenat_example.
Section delaystateseq_example.
Variable M : delayStateMonad (seq nat).

Definition bubblesortd_body1 (i: nat)(j: nat): M (unit + nat)%type :=
  do s <- get;
  if i < j then let sj := nth 0 s j in let sjp := nth 0 s (j-1) in
                                       if sj < sjp then do _ <- put (set_nth 0 s (j-1) sj);
                                                        do s' <- get;
                                                        do _ <- put (set_nth 0 s' j (sjp)); Ret (inr (j-1))
                                       else Ret (inr (j-1))
  else Ret (inl tt).
Definition bubblesortd_body2 (i: nat): M (unit + nat)%type :=
do s <- get;
let len := length s in if i == len
                       then Ret (inl tt)
                       else do _ <- ((while (bubblesortd_body1 i)) (len - 1));
                            Ret (inr (i.+1)).
Definition bubblesortd := while bubblesortd_body2.
(*implimentations in software foundation vol.3 selection*)
Fixpoint select (x: nat) (l: seq nat) : nat * seq nat :=
  match l with
  | [::] => (x, [::])
  | h :: t =>
    if x <= h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.
Definition selsort_body (l12:seq nat*seq nat): M ( seq nat + (seq nat * seq nat))%type :=
  match l12 with (l1,l2) => match l1 with
                              |[::] => @ret _ _ (inl l2)
                              |h :: t => let (m, res) := select h t in @ret _ _ (inr (res , app l2 (m :: nil)))
                      end
end.
Fail Fixpoint selsort (l : list nat) : list nat :=
  match l with
  | [::] => [::]
  | x :: r => let (y, r') := select x r
            in y :: selsort r'
end.
Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => [::] (* ran out of fuel *)
  | [::], _ => [::]
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.
Definition selsortd := while selsort_body.
Let testseq := 5::7::2::3::8::1::4::9::nil.
Definition stselsort_body (l: seq nat) : M (seq nat + seq nat)%type :=
   (@get _ M) >>= fun l' =>
match l with
    |[::] => @ret _ _ (inl l')
    |h::tl => let (m, res) := select h tl in (@put _ M) (app l' (m::nil)) >> @ret _ _ (inr res)
end.
Definition stselsort := while stselsort_body.
(*
Lemma selsortE (l: seq nat) : wBisimDS (stselsort l) ((@get _ M'') >>= (fun s => (@bind Delay _ )  _ (selsortd (l, [::])) (fun res =>  (@put _ M'' (app s res)) >> @ret M'' _ (app s res)))).

Lemma selsortE (l: seq nat) : wBisimDS (stselsort l) (let n := length l in (@get _ M'') >>= (fun s => let res := selsort l n in (@put _ M'' (app s res)) >> @ret _ _ (app s res))).
Proof.
set n := length l.

remember (length l).
elim: n Heqn0. *)
(*
Lemma selsortE (l: seq nat): wBisimDS (@put _ M'' [::] >>selsort (l, [::])) ((@put _ M'' [::]) >>  (stselsort l)).
Proof.
elim: l => [|l' l IH].
- rewrite/selsort/stselsort/selsort_body/stselsort_body.
  setoid_symmetry.
  set h1 := whileDS _ _ .
  set h2 := whileDS _ _.
     sum_rect (fun=> DS (seq nat) (seq nat)) Ret (whileDS (fun l : seq nat => get >>= (fun l' : seq nat => match l with
                                                                                                           | [::] => put [::] >> Ret (inl l')
                                                                                                           | h :: tl => let (m, res) := select h tl in put (l' ++ [:: m])%list >> Ret (inr res)
                                                                                                           end)))) [::]) .
 
 ((get >>= (fun l' : seq nat => put [::] >> Ret (inl l'))) >>=
     sum_rect (fun=> DS (seq nat) (seq nat)) Ret (whileDS (fun l : seq nat => get >>= (fun l' : seq nat => match l with
                                                                                                           | [::] => put [::] >> Ret (inl l')
                                                                                                           | h :: tl => let (m, res) := select h tl in put (l' ++ [:: m])%list >> Ret (inr res)
                                                                                                           end)))) 
*)
(*
Fixpoint listsum (s: seq nat) := match s with |nil => 0 |hd :: tl => hd + listsum tl end.
(*
Definition collatzs2_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat))%type :=
match nml with (n,m,l) =>
if (l %% 4 == 1) && (n == 1) then @ret _ _ (inl (m,l))
else if (n == 1) then @ret _ _ (inr (m+1,m+1,0))
                 else if (n %% 2) == 0 then @ret _ _ (inr (n./2,m,l+1))
                               else @ret _ _(inr (3*n + 1, m, l+1))
end.
*)

*)


Definition collatzs1_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) => (@get _ M) >>= fun s' => (put (n :: s')) >>
if n==1 then if (l %% 4 == 1) then @ret _ _ (inl(inl (m,l))) else put [::] >> @ret _ _ (inl(inr (m+1, m+1, 0)))
         else if (n %% 2 == 0) then @ret _ _ (inr (n./2,m,l+1))
                               else @ret _ _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs1 (n: nat) := while (while collatzs1_body) (n,n,0).
Definition collatzs2_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat))%type :=
match nml with (n,m,l) => (@get _ M) >>= fun s' => (put (n :: s')) >>
if (l %% 4 == 1) && (n == 1) then @ret _ _ (inl (m,l))
else if (n == 1) then put [::] >> @ret _ _ (inr (m+1,m+1,0))
                 else if (n %% 2) == 0 then @ret _ _ (inr (n./2,m,l+1))
                               else @ret _ _(inr (3*n + 1, m, l+1))
end.
Definition collatzs2 (n:nat):= while collatzs2_body (n,n,0).
Lemma collatzstepE (n:nat): collatzs1 n ≈ collatzs2 n.
Proof.
rewrite/collatzs1/collatzs2.
rewrite -codiagonalE.
apply whilewB.
move => [[n' m] l].
rewrite/collatzs1_body/collatzs2_body.
case/boolP: (l %% 4 == 1) => Hl //=.
- case/boolP: (n' == 1) => Hn' //=.
  + rewrite Hl fmapE. 
    rewrite bindA.
    rewrite (bindfwB) //= => a.
    by rewrite bindA bindretf /=.
  + case/boolP: (n' %% 2 == 0) => He //=.
    * rewrite fmapE /= bindA.
      rewrite bindfwB //= => a.
      by rewrite bindA bindretf /=.
    * rewrite fmapE /= bindA bindfwB //= => a.
      by rewrite bindA bindretf /=.
- case/boolP: (n' == 1) => Hn' //=.
  + rewrite ifN //= fmapE bindA.
    rewrite bindfwB //= => a.
    by rewrite  bindA bindA bindretf. 
  + case/boolP: (n' %% 2 == 0) => He //=.
    * rewrite fmapE /= bindA bindfwB //= => a.
      by rewrite bindA bindretf /=.
    * rewrite fmapE /= bindA bindfwB //= => a.
      by rewrite bindA bindretf //=.
Qed.


(*
Fixpoint listsum (s: seq nat) := match s with |nil => 0 |hd :: tl => hd + listsum tl end.

Definition collatzs2_body (nm:nat*nat) : M'' (nat + nat*nat)%type :=
match nm with (n,m) => (@get _ M'') >>= fun s' => (put (n :: s')) >> (@get _ M'' ) >>= fun s => let l := listsum s in if (l %% 4 == 1) && (n == 1)
                                                                   then @ret M'' _ (inl l)
                                                                   else if (n == 1) then put [::] >> @ret _ _ (inr (m+1,m+1))
                                                                        else if (n %% 2) == 0 then @ret _ _ (inr (n./2,m))
                                                                             else @ret _ _(inr (3*n + 1, m))
end.
Definition collatzs2 := while collatzs2_body. *)
(*
Definition collatzs1_body (nm: nat*nat) : M'' ((nat + nat*nat) + nat*nat)%type :=
match nm with (n,m) => (@get _ M'') >>= fun s' => (put (n :: s')) >> (@get _ M'') >>= fun s =>  let l := listsum s in
if n==1 then if (l %% 4 == 1) then @ret _ _ (inl(inl l)) else put [::] >> @ret _ _ (inl(inr (m+1, m+1)))
         else if (n %% 2 == 0) then @ret _ _ (inr (n./2,m))
                               else @ret _ _ (inr (3*n + 1, m))
end.
Definition collatzs1 := while (while collatzs1_body).
Lemma collatzsE (n m: nat): (collatzs1 (n,m)) ≈ (collatzs2 (n,m)).
Proof.
rewrite/collatzs1/collatzs2.
rewrite -codiagonalE.
apply whilewB. 
move => [n' m'].
rewrite/collatzs1_body/collatzs2_body.
simpl.
case/boolP: (n' == 1) => Hn' //=.
- simpl. *)
(*状態を見て再帰をするかどうか判断すると計算が進まなくなり不可能になる*)

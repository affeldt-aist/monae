From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
Require Import hierarchy.
Require Import Lia.

Local Open Scope monae_scope.

Section delayexample.

Notation "a '≈' b" := (wBisim a b).
Variable M : delayMonad.
Fixpoint fact (n:nat) :nat := match n with
                          |O => 1
                          |S n' => n * fact n'
                          end.
Definition fact_body: nat * nat -> M (nat + nat*nat)%type := fun (a: nat * nat) =>
                                            match a with
                                            |(O, a2) => ret _ (inl a2)
                                             |(S n', a2) => ret _ (inr (n', a2 * (S n') ))
                                            end .
Definition factdelay := fun (nm:nat*nat) => while fact_body nm.
Lemma eq_fact_factdelay :forall n m, factdelay (n,m) ≈ ret nat (m * fact n).
Proof.
move => n.
rewrite/factdelay.
elim: n.
- move =>m.
  by rewrite fixpointE //= bindretf muln1 //=.
- move => n IH m.
  by rewrite fixpointE //= bindretf //= IH mulnA.
Qed.
Definition collatzm_body (m:nat) (n:nat) : M (nat + nat)%type :=
  if n == 1 then ret _ (inl m)
  else if n %%2 == 0 then ret _ (inr (n./2))
       else ret _ (inr (3 * n + 1)).
Definition collatzm (m:nat) := fun n => while (collatzm_body m) n.
Definition delaymul (m:nat) (d: M nat) :M nat := d >>= (fun n => ret _ (m * n)).
Lemma collatzm_mul : forall (m n p: nat), delaymul p (collatzm m n)  ≈ collatzm (p * m ) n . 
Proof.
move => m n p.
rewrite /collatzm /delaymul.
rewrite naturalityE.
set x := (x in while x).
set y := collatzm_body (p*m).
have <-: x = y.
  apply boolp.funext => q.
  subst x y.
  case_eq (q == 1) => Hs.
  + by rewrite /collatzm_body Hs bindretf //= fmapE bindretf //=.
  + rewrite/collatzm_body Hs.
  case He: (q %% 2 == 0).
  * by rewrite bindretf //= fmapE bindretf //=.
  * by rewrite bindretf //= fmapE bindretf //=.
done.
Qed.
Definition minus1_body (nm: nat*nat)  :M ((nat + nat*nat) + nat*nat)%type:= match nm with
                                                                |(O, m) => match m with
                                                                         |O => ret _ (inl (inl O))
                                                                         |S m' => ret _ (inl (inr (m', m')))
                                                                         end
                                                                |(S n', m) => ret _ (inr (n', m ))
                                                                end.
Definition minus1 := fun nm => while (while minus1_body) nm.
Definition minus2_body (nm: nat*nat) : M (nat + nat*nat)%type := match nm with
                                                      |(O,m) => match m with
                                                                |O => ret _ (inl O)
                                                                |S m' => ret _ (inr (m', m'))
                                                                end
                                                      |(S n', m) => ret _ (inr (n',m))
                                                      end.
Definition minus2 := fun nm => while minus2_body nm.
Lemma eq_minus : forall (nm: nat*nat), minus1 nm  ≈  minus2 nm.
Proof.
move => nm.
rewrite/minus1 /minus2.
rewrite -codiagonalE.
apply: whilewB.
move => [n m].
  case: n.
  + case: m => //= .
     * by rewrite fmapE bindretf.
     * move => n.
       by rewrite fmapE bindretf.
  + move => n //=.
    by rewrite fmapE bindretf.
Qed.
Definition collatzs1_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat))%type :=
match nml with (n,m,l) =>
if (l %% 4 == 1) && (n == 1) then ret _ (inl (m,l))
else if (n == 1) then ret _ (inr (m+1,m+1,0))
                 else if (n %% 2) == 0 then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs1 (n:nat):= while collatzs1_body (n,n,0).
Definition collatzs2'_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) =>
if n== 1 then ret _ (inl(inr (m+1, m+1, l)))
         else if (n %% 2 == 0) then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
Definition collatzs2_body (nml: nat*nat*nat) : M (nat*nat + nat*nat*nat)%type:=
match nml with (n,m,l) => if (l %% 4 == 1) then ret _ (inl (m,l)) else (while collatzs2'_body (n,n,0)) end.
Definition collatzs2 (n: nat) := (while collatzs2_body) (n,n,0).

Definition collatzaux_body (nml: nat*nat*nat) : M ((nat*nat + nat*nat*nat) + nat*nat*nat)%type :=
match nml with (n,m,l) =>
if n== 1 then if (l %% 4 == 1) then ret _ (inl(inl (m,l))) else ret _ (inl(inr (m+1, m+1, 0)))
         else if (n %% 2 == 0) then ret _ (inr (n./2,m,l+1))
                               else ret _ (inr (3*n + 1, m, l+1))
end.
(*
Lemma collatstepcE (n: nat): collatzs1 n ≈ collatzs2 n.  
Proof.
have: forall n, collatzs2_body (n,n,0) ≈ (while _ _ collatzaux_body) (n,n,0).
  move => n'.
  rewrite/collatzaux_body/collatzs2_body.  
  simpl.
  apply: wBisim_trans.
    + apply fixpointE.
    + simpl.
      case_eq (n' == 1) => Hn.
      * rewrite bindretf. simpl.
        rewrite wBisim_sym.
        apply: wBisim_trans.
        apply fixpointE.
        simpl. rewrite Hn. rewrite bindretf. simpl. apply wBisim_refl.
      * case_eq (n' %% 2 == 0) => He.
        ** simpl. rewrite bindretf. simpl. rewrite wBisim_sym. apply: wBisim_trans.
           apply fixpointE. simpl. rewrite Hn. rewrite He. simpl. rewrite bindretf. simpl. rewrite/collatzs2'_body.




  case_eq (l %% 4 == 1) => Hl.
  - case_eq (p == 1) => Hp. 
    + rewrite wBisim_sym.
      apply: wBisim_trans.
      * apply fixpointE.
      * rewrite //= Hp Hl bindretf //=. 
        by apply wBisim_refl.
    + rewrite wBisim_sym.
      apply: wBisim_trans.
      * apply fixpointE.
      * simpl.
        rewrite Hp.
        case_eq (p %% 2 == 0) => Hp'.
        ** rewrite bindretf.
           simpl.

rewrite //= Hp Hl bindretf //=. 
        by apply wBisim_refl.
rewrite/collatzs1/collatzs2.
rewrite/collatzs1_body/collatzs2_body. 
rewrite wBisim_sym.
apply wpreserve.
- case_eq (p == 1) => Hp //=.
  + by apply wBisim_refl. 
  + 
*)

Definition divide5_body (f:nat -> M nat)(nm: nat*nat):M(nat + nat*nat)%type := 
match nm with (n,m) => 
  if m %% 5 == 0 then ret _ (inl m) 
                 else f n >>= (fun x => ret _ (inr (n.+1 , x))) end.

Definition dividefac1 (n: nat):= while (divide5_body (fun n => factdelay (n, 1))) (n,1).
Definition dividefac2 (n: nat):= while (divide5_body (fun n => ret _ (fact n))) (n,1).
Lemma eq_dividefac: forall n, dividefac1 n ≈ dividefac2 n.
Proof.
move => n.
rewrite/dividefac1/dividefac2.
apply whilewB.
move => [k l].
case/boolP: (l %% 5 == 0) => Hl //=.
- by rewrite Hl.
- rewrite !ifN // bindretf.
  rewrite bindmwB; last by apply (eq_fact_factdelay k 1).
  by rewrite bindretf mul1n.
Qed.
Definition fastexp_body (nmk: nat*nat*nat) :M (nat + nat*nat*nat)%type :=
match  nmk with (n,m,k) => if n == 0 then ret _ (inl m)
                           else (if odd n then ret _ (inr (n.-1 , m*k, k))
                                 else ret _ (inr (n./2, m, k*k) )) end.
Definition fastexp (n m k: nat) := while fastexp_body (n,m,k).
Fixpoint exp (n k: nat) := match n with |O => 1 | S n' => k*exp n' k end.
Lemma expE_aux (n:nat):n <= n.*2.
Proof.
elim: n => //= n IH.
rewrite doubleS.
rewrite ltnS.
apply (leq_trans IH).
apply leqnSn.
Qed.
Lemma expE: forall n m k, fastexp n m k ≈ ret nat (m * expn k n).
Proof.
move => n.
rewrite/fastexp/fastexp_body.
elim: n {-2}n (leqnn n) => n.
- rewrite leqn0 => /eqP H0 m k.
  by rewrite H0 fixpointE /= bindretf //= expn0 mulnS muln0 addn0.
- move => IH [|m'] Hmn m k.
  + by rewrite fixpointE //= bindretf //= mulnS muln0 addn0.
  + case/boolP: (odd (m'.+1)) => Hm'.
    * by rewrite fixpointE Hm' //= bindretf //= IH //= expnSr (mulnC (k^m') k) mulnA.
    * rewrite fixpointE //= ifN //= bindretf //= IH.
      ** by rewrite uphalfE mulnn -expnM mul2n (even_halfK Hm').
      ** rewrite ltnS in Hmn.
         rewrite leq_uphalf_double.
         apply (leq_trans Hmn).
         apply expE_aux.
Qed.
Definition mc91_body (nm: nat*nat):M (nat + nat*nat)%type :=
  match nm with (n, m) => if n==0 then ret _ (inl m)
                          else if m > 100 then ret _ (inr (n.-1,m - 10))
                                          else ret _ (inr (n.+1,m + 11))
end.
Definition mc91 (n m: nat):= while mc91_body (n.+1,m).
Lemma mc91succE (n m: nat): 90 <= m < 101 -> mc91 n m ≈ mc91 n (m.+1).
Proof.
(*
move => /andP [Hmin Hmax].
rewrite/mc91/mc91_body.
rewrite fixpointE /=.
rewrite -/mc91_body/mc91.
move: Hmax.
rewrite ltnNge.
case:ifP => //= Hf _.
rewrite bindretf /= fixpointE /=.
have H100 : 100 = 89 + 11. by [].
rewrite H100 ltn_add2r Hmin bindretf /=. fixpointE /= fixpointE /=.
have ->: m + 11 - 10 = m.+1.
  rewrite -addnBA // /=.
  have -> : 11 - 10 = 1. by [].
  by rewrite addn1.
by [].*)

move => /andP [Hmin Hmax].
rewrite/mc91/mc91_body fixpointE /=.
move: Hmax.
rewrite ltnNge.
case:ifP => //= Hf _.
rewrite bindretf /= fixpointE /=.
have H100 : 100 = 89 + 11. by [].
rewrite H100 ltn_add2r Hmin bindretf fixpointE /= fixpointE /=.
have ->: m + 11 - 10 = m.+1.
  rewrite -addnBA // /=.
  have -> : 11 - 10 = 1. by [].
  by rewrite addn1.
by [].
Qed.
Lemma nmSleq (n:nat) (m:nat): n<= m.+1 -> n = m.+1 \/ n <= m.
Proof.
move=> H.
  case: (leqP n m) => [Hleq | Hnleq].
  - by right.
  - left. apply/eqP. by rewrite eqn_leq H Hnleq.
Qed.
Lemma eq_sub (n m: nat) : n <= m -> m - n = 0 -> m = n.
Proof. by move => Hleq Hmn;rewrite -(addn0 n) -Hmn -addnCB addnBl_leq //. Qed.
Lemma leq_exists (n m: nat): n < m -> exists k, n + k = m.
Proof.
elim: m.
- by rewrite ltn0.
- move => m IH.
  move/nmSleq => [Hn|Hn].
  + exists 1.
    by rewrite addn1.
  + move: Hn.
    move/IH => [k Hn].
    exists (k + 1).
    by rewrite addnA Hn addn1.
Qed.
Lemma mc91E_aux (m n : nat):90 <= m <= 101 -> mc91 n m ≈ mc91 n 101.
Proof.
move => /andP [Hmin Hmax].
case/boolP: (m < 101).
- move/leq_exists => [k Hn].
  move: m Hmin Hmax Hn.
  elim: k.
  + move => m Hmin Hmax.
    rewrite addn0 => Hm.
    by rewrite Hm.
  + move => l IH m Hmin.
    move/nmSleq => [H101 | Hm].
    * by rewrite H101 => _.
    * rewrite -addn1 (addnC l 1) addnA mc91succE //.
      ** rewrite addn1.
         apply IH => //.
         rewrite -(addn1 m).
         by apply ltn_addr.
      ** apply/andP.
         by split => //.
- rewrite -leqNgt => H100.
  have -> : m = 101.
    apply anti_leq => //.
    apply/andP.
    by split => //= .
  by [].
Qed.
Lemma mc91_101E (n: nat): mc91 n 101 ≈ ret _ 91.
Proof.
elim: n => [|n IH]; rewrite/mc91/mc91_body fixpointE bindretf/=.
- by rewrite fixpointE bindretf.
- by rewrite -/mc91_body // -/(mc91 n 91) mc91E_aux // IH.
Qed.
Lemma mc91E (n m : nat): m <= 101 -> mc91 n m ≈ ret _ 91.
Proof.
move => H101.
case/boolP: (90 <= m).
- move => H89.
  move: (conj H89 H101) => /andP Hm.
  by rewrite mc91E_aux // mc91_101E.
- rewrite -leqNgt -ltnS.
  move/ltnW/subnKC.
  set k:= 90 - m.
  clearbody k.
  elim: k {-2}k (leqnn k) n m {H101} => k.
  + rewrite leqn0 => /eqP H0 n m.
    rewrite H0 (addn0 m) => ->.
    by rewrite mc91E_aux // mc91_101E.
  + move =>IH k' Hk n m Hm.
(*
    move/(f_equal (subn^~ k')): Hm.
    rewrite addnK => ->. *)
    have -> : m = 90 - k' by rewrite -Hm addnK.
    rewrite/mc91/mc91_body fixpointE //=.
    rewrite ifF; last by rewrite ltn_subRL addnC.
    rewrite bindretf /= -/mc91_body -/(mc91 _ _).
    case/boolP : (k' <= 11) => Hk'.
      * rewrite mc91E_aux ?mc91_101E //.
          lia.
      * rewrite -ltnNge in Hk'.
        by rewrite (IH (k' - 11)) // ; lia.
Qed.

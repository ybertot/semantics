Require Import ZArith List Lia.

Set Implicit Arguments.
Section types.
Variable string : Type.
Variable string_dec : forall a b:string, {a=b}+{a<>b}.

Inductive aexpr0 : Type :=
  avar (s : string) | anum (n :Z) | aplus (a1 a2:aexpr0) |
    array_read (s : string) (e : aexpr0).

Inductive bexpr0 : Type :=  blt (_ _ : aexpr0).

Inductive instr0 : Type :=
  assign (_ : string) (_ : aexpr0) | sequence (_ _: instr0)
 | while (_ :bexpr0)(_ : instr0) | skip |
   array_set (s : string) (index : aexpr0) (val : aexpr0).

Fixpoint lookup (A:Type)(l:list(string*A))(def:A)(x:string): A :=
  match l with nil => def
  | (y,a)::tl => if string_dec y x then a else lookup tl def x
  end.

End types.

Arguments anum [string].
Arguments skip {string}.

Module Type little_syntax.
Parameter string : Set.

Parameter string_dec : forall a b:string, {a=b}+{a<>b}.
Parameter false_cst : string.
Parameter true_cst : string.
Parameter between_cst : string.
Parameter ge_cst : string.
Parameter le_cst : string.
Parameter lt : string -> string -> Prop.

Axiom lt_irrefl : forall x, ~lt x  x.
Axiom lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

Axiom all_distinct :
  lt between_cst false_cst /\ lt false_cst ge_cst /\
  lt ge_cst le_cst /\ lt le_cst true_cst.

Definition aexpr := aexpr0 string.
Definition bexpr := bexpr0 string.
Definition instr := instr0 string.

End little_syntax.

Module little(S : little_syntax).

Import S.

Definition env := list(string*Z).

Definition array_env := list (string * list Z).

Inductive array_at : list Z -> nat -> Z -> Prop :=
  a_at0 : forall l v, array_at (v :: l) 0 v
| a_atS : forall l a n v, array_at l n v -> array_at (a :: l) (S n) v.

Inductive ar_find : array_env -> string -> list Z -> Prop :=
| ar_fd1 : forall ar l x, ar_find ((x, l) :: ar) x l
| ar_fd2 : forall ar l l' x y, x <> y ->
  ar_find ar x l -> ar_find ((y, l') :: ar) x l.

Fixpoint lookup (r:env)(name:string){struct r} : option Z :=
  match r with
    nil => None
  | (a,b)::tl => if (string_dec a name) then Some b else lookup tl name
  end.

Fixpoint ar_lookup (r:array_env)(name:string){struct r} : option (list Z) :=
  match r with
    nil => None
  | (a,b)::tl => if (string_dec a name) then Some b else ar_lookup tl name
  end.

Inductive aeval : env -> array_env -> aexpr -> Z -> Prop :=
  ae_int : forall r r_a n, aeval r r_a (anum n) n
| ae_var : forall (r : env) (r_a : array_env)
    (x : string) (v : Z), lookup r x = Some v ->
    aeval r r_a (avar x) v
| ae_plus : forall r r_a e1 e2 v1 v2,
              aeval r r_a e1 v1 -> aeval r r_a e2 v2 ->
              aeval r r_a (aplus e1 e2) (v1 + v2)
| ae_ar : forall r r_a ind x vi v l,
              aeval r r_a ind vi -> (0 <= vi)%Z ->
              ar_lookup r_a x = Some l ->
              nth_error l (Z.abs_nat vi) = Some v ->
              aeval r r_a (array_read x ind) v.

Global Hint Resolve ae_int ae_var ae_plus ae_ar : core.

Inductive beval : env -> array_env -> bexpr -> bool -> Prop :=
| be_lt1 : forall r r_a e1 e2 v1 v2,
            aeval r r_a e1 v1 -> aeval r r_a e2 v2 ->
            (v1 < v2)%Z -> beval r r_a (blt e1 e2) true
| be_lt2 : forall r r_a e1 e2 v1 v2,
            aeval r r_a e1 v1 -> aeval r r_a e2 v2 ->
            (v2 <= v1)%Z -> beval r r_a (blt e1 e2) false.

Definition bind (A B:Type)(v:option A)(f:A->option B) :
     option B :=
  match v with Some x => f x | None => None end.
Arguments bind : default implicits.

Fixpoint uf {A : Type} (r:list (string * A))(x:string)(v:A)
  : option(list (string * A)) :=
    match r with
      nil => None
    | (y,n')::tl =>
      if string_dec y x then
        Some((x,v)::tl)
      else
        bind (uf tl x v) (fun tl' => Some ((y,n')::tl'))
    end.

Inductive ar_update : list Z -> nat -> Z -> list Z -> Prop :=
| ar_up1 : forall l v v', ar_update (v :: l) 0%nat v' (v' :: l)
| ar_up2 : forall l l' n v v',
   ar_update l n v' l' -> ar_update (v :: l) (S n) v' (v :: l').

Inductive ars_update : array_env -> string -> nat -> Z -> array_env -> Prop:=
| ars_up1 : forall r_a l l' x i v,
   ar_update l i v l' ->
   ars_update ((x, l) :: r_a) x i v ((x, l') :: r_a)
| ars_up2 : forall r_a r_a' x y l i v,
    x <> y ->
    ars_update r_a x i v r_a' ->
    ars_update ((y, l) :: r_a) x i v ((y, l) :: r_a').

Fixpoint set_nth (l : list Z) (i : nat) (v : Z) : option (list Z) :=
  match l, i with
  | a :: tl, 0%nat => Some (v :: tl)
  | a :: tl, S i' =>
    bind (set_nth tl i' v) (fun tl' => Some (a :: tl'))
  | _, _ => None
  end.

Fixpoint ar_uf (r_a : array_env) (x : string) (i : nat) (v : Z) :
  option array_env :=
  match r_a with
    nil => None
  | (y, l') :: tl =>
    if string_dec x y then
      bind (set_nth l' i v) (fun l'' => Some ((y, l'') :: tl))
    else
      bind (ar_uf tl x i v)
      (fun tl' => Some ((y, l') :: tl'))
  end.

Inductive exec : env -> array_env ->instr->env-> array_env ->Prop :=
| SN1 : forall r r_a, exec r r_a skip r r_a
| SN2 : forall r r' r_a x e v, 
  aeval r r_a e v -> 
  uf r x v = Some r' -> exec r r_a (assign x e) r' r_a
| SN3 : forall r r' r'' r_a r_a' r_a'' i1 i2,
    exec r r_a i1 r' r_a' -> exec r' r_a' i2 r'' r_a'' ->
    exec r r_a (sequence i1 i2) r'' r_a''
| SN4 : forall r r' r'' r_a r_a' r_a'' b i,
    beval r r_a b true ->
    exec r r_a i r' r_a' -> 
    exec r' r_a' (while b i) r''  r_a'' -> exec r r_a (while b i) r'' r_a''
| SN5 : forall r r_a b i,
    beval r r_a b false -> exec r r_a (while b i) r r_a
| SN6 : forall r r_a r_a' x ind e indv v,
   aeval r r_a e v ->
   aeval r r_a ind indv ->
   (0 <= indv)%Z ->
   ar_uf r_a x (Z.abs_nat indv) v = Some r_a' ->
   exec r r_a (array_set x ind e) r r_a'.

Global Hint Resolve be_lt1 be_lt2 SN1 SN2 SN3 SN4 SN5 SN6 : core.

Inductive sos_step : env->array_env -> instr->instr-> env ->
  array_env ->Prop :=
  SOS1 : forall r r_a r' x e v,
   aeval r r_a e v -> 
   uf r x v = Some r' ->
   sos_step r r_a (assign x e) skip r' r_a
| SOS2 : forall r r_a i2, sos_step r r_a (sequence skip i2) i2 r r_a
| SOS3 : forall r r_a r' r_a' i1 i1' i2,
               sos_step r r_a i1 i1' r' r_a'->
               sos_step r r_a (sequence i1 i2)(sequence i1' i2) r' r_a'
| SOS4 :
     forall r r_a b i, beval r r_a b true ->
       sos_step r r_a (while b i) (sequence i (while b i)) r r_a
| SOS5 :
     forall r r_a b i, beval r r_a b false ->
       sos_step r r_a (while b i) skip r r_a
| SOS5' :
   forall r r_a r_a' x ind e indv v,
   aeval r r_a e v ->
   aeval r r_a ind indv ->
   (0 <= indv)%Z ->
   ar_uf r_a x (Z.abs_nat indv) v = Some r_a' ->
   sos_step r r_a (array_set x ind e) skip r r_a'.

Inductive sos_star : env-> array_env->
   instr->instr->env->array_env->Prop :=
  SOS6 : forall r r_a i, sos_star r r_a i i r r_a
| SOS7 : forall r r' r'' r_a r_a' r_a'' i i' i'',
             sos_step r r_a i i' r' r_a' -> sos_star r' r_a' i' i'' r'' r_a''->
             sos_star r r_a i i'' r'' r_a''.

Global Hint Resolve SOS1 SOS2 SOS3 SOS5 SOS5' SOS4 SOS6 SOS7 : core.

Lemma sos_star_trans :
   forall r r' r'' r_a r_a' r_a'' i i' i'',
    sos_star r r_a i i' r' r_a' -> sos_star r' r_a' i' i'' r'' r_a'' ->
    sos_star r r_a i i'' r'' r_a''.
Proof.
induction 1; eauto.
Qed.

Lemma sos_sequence_aux : forall r r_a i is r' r_a',
  sos_star r r_a i is r' r_a' -> is = skip ->
  forall i' i'' r'' r_a'', sos_star r' r_a' i' i'' r'' r_a'' ->
  sos_star r r_a (sequence i i') i'' r'' r_a''.
Proof.
induction 1; intros; try (subst i); eauto.
(* Before using modules,the previous line finished off the proof. *)
apply SOS7 with (r':=r')(r_a' := r_a') (i':=sequence i' i'0); auto.
Qed.

Lemma sos_sequence : forall  r r' r'' r_a r_a' r_a'' i i',
  sos_star r r_a i skip r' r_a' -> sos_star r' r_a' i' skip r'' r_a'' ->
  sos_star r r_a (sequence i i') skip r'' r_a''.
Proof.
  intros; eapply sos_sequence_aux; eauto.
Qed.

Global Hint Resolve sos_sequence : core.

Lemma sn_imp_sos :
 forall r r' r_a r_a' i,  exec r r_a i r' r_a' -> sos_star r r_a i skip r' r_a'.
Proof.
  intros r r' r_a r_a' i H; elim H; eauto.
Qed.

Lemma sos_sequence_assoc_aux : forall r r' r_a r_a' i i',
  sos_star r r_a i i' r' r_a' -> i' = skip ->
  forall i1 i2 i3, i = (sequence i1 (sequence i2 i3)) ->
  sos_star r r_a (sequence (sequence i1 i2) i3) skip r' r_a'.
Proof.
induction 1; intros; subst; try discriminate.
match goal with id : sos_step _ _ _ _ _ _ |- _ =>
   inversion id; subst; eauto end.
(* Before the change in module structure, the proof was over here. *)
match goal with id : sos_star _ _ _ _ _ _ |- _ =>
   apply SOS7 with (2:=id);auto end.
apply SOS7 with (i':=sequence (sequence i1' i2) i3)(r':=r')(r_a':= r_a'); auto.
Qed.

Lemma sos_sequence_assoc : forall r r' r_a r_a' i1 i2 i3,
  sos_star r r_a (sequence i1 (sequence i2 i3)) skip r' r_a' ->
  sos_star r r_a (sequence (sequence i1 i2) i3) skip r' r_a'.
Proof.
intros; eapply sos_sequence_assoc_aux; eauto.
Qed.

Lemma sos_step_imp_sn : forall r r' r_a r_a' i i',
  sos_step r r_a i i' r' r_a' ->  forall r'' r_a'',
  exec r' r_a' i' r'' r_a'' ->
  exec r r_a i r'' r_a''.
Proof.
 induction 1; intros r2 ra2 Hexec; try (inversion Hexec; subst; eauto).
Qed.

Lemma sos_imp_sn_aux : forall r r_a i is r' r_a',
  sos_star r r_a i is r' r_a' -> is = skip -> exec r r_a i r' r_a'.
Proof.
 induction 1; intros; subst; eauto.
 eapply sos_step_imp_sn; eauto.
Qed.

Lemma sos_imp_sn : forall r r_a i r' r_a',
  sos_star r r_a i skip r' r_a' -> exec r r_a i r' r_a'.
Proof.
  intros; eapply sos_imp_sn_aux; eauto.
Qed.

Theorem sos_eq_sn : forall r r_a i r' r_a',
  sos_star r r_a i skip r' r_a' <-> exec r r_a i r' r_a'.
Proof.
 intros; split; [apply sos_imp_sn | apply sn_imp_sos]; assumption.
Qed.

Definition Z_to_option_nat (z : Z) :=
  if (z <? 0)%Z then None else Some (Z.abs_nat z).

Fixpoint af (r:env)(r_a : array_env) (a:aexpr) {struct a}: option Z :=
  match a with
    avar index => lookup r index
  | anum n => Some n
  | aplus e1 e2 =>
     bind (af r r_a e1)
     (fun v1 => bind (af r r_a e2) (fun v2 => Some (v1+v2)%Z))
  | array_read a i =>
     bind (af r r_a i)
     (fun vi => bind (Z_to_option_nat vi)
       (fun nvi => 
          bind (ar_lookup r_a a)
            (fun l => (nth_error l nvi))))
   end.

Definition bf (r:env) (r_a : array_env) (b:bexpr) : option bool :=
  let (e1, e2) := b in
  bind (af r r_a e1)
    (fun v1 => bind (af r r_a e2)
      (fun v2 =>
       if Zlt_bool v1 v2 then Some true else Some false)).


Definition bind2 (A B C:Type)(v:option(A*B))
  (f: A->B->option C) :option C:=
  match v with Some(a,b) => f a b | None => None end.
Arguments bind2 : default implicits.

Definition bind3 (A B C D:Type)(v:option(A*B*C))
  (f: A->B->C->option D) :option D:=
  match v with Some(a,b,c) => f a b c| None => None end.
Arguments bind3 : default implicits.

Definition eq_skip (i:instr) : {i=skip}+{i<>skip}.
case i; auto; right; discriminate.
Defined.

Fixpoint f_sos (r:env)(r_a : array_env) (i:instr) :
  option (env*array_env*instr) :=
  match i with
    skip => None
  | assign x e =>
    bind (bind (af r r_a e) (fun n => uf r x n))
      (fun r' => Some(r', r_a, skip))
  | sequence i1 i2 =>
    if eq_skip i1 then Some(r, r_a, i2) else
    bind3 (f_sos r r_a i1) (fun r' r_a' i' => Some(r', r_a', sequence i' i2))
  | while b i =>
    bind (bf r r_a b)
      (fun v => if v then Some(r, r_a, sequence i (while b i))
                else Some(r, r_a, skip))
  | array_set a ind e =>
    bind (af r r_a e) (fun v =>
    bind (af r r_a ind) (fun indv =>
    bind (Z_to_option_nat indv) (fun i =>
    bind (ar_uf r_a a i v) (fun r_a' =>
      Some(r, r_a', skip)))))
  end.

Fixpoint f_star (n:nat)(r:env)(r_a : array_env)(i:instr){struct n}
   :option(env*array_env*instr) :=
  match n with
    0%nat => Some(r,r_a,i)
  | S n =>
    if eq_skip i then
       Some(r,r_a, i)
    else
        bind3 (f_sos r r_a i) (fun r' r_a' i' => f_star n r' r_a' i')
  end.

Lemma aeval_lookup :
  forall r r_a e n, aeval r r_a e n ->
    forall name, e = avar name -> lookup r name = Some n.
Proof.
 intros r r_a e n H; elim H; simpl.
 intros; discriminate.
 now intros r0 r_a0 x v hlk x' Heq; injection Heq; intros; subst.
discriminate.
discriminate.
Qed.

Lemma Z_to_option_natP v :
  (0 <= v)%Z -> Z_to_option_nat v = Some (Z.abs_nat v).
Proof.
rewrite <- Z.nlt_ge; unfold Z_to_option_nat, Z.lt, Z.ltb.
now destruct (v ?=0)%Z eqn:cmpv; intuition.
Qed.

Lemma array_at_nth_error l n v :
  array_at l n v -> nth_error l n = Some v.
Proof.
induction 1; auto.
Qed.

Lemma aeval_f :
  forall r r_a e n, aeval r r_a e n -> af r r_a e = Some n.
Proof.
 induction 1; simpl; auto.
 rewrite IHaeval1; simpl; rewrite IHaeval2; simpl; auto.
 rewrite IHaeval; simpl.
 rewrite Z_to_option_natP; simpl; auto.
now rewrite H1; simpl; rewrite H2.
Qed.

Lemma beval_f :
  forall r r_a e b, beval r r_a e b -> bf r r_a e = Some b.
Proof.
  induction 1; simpl;
  rewrite aeval_f with (1:= H);
  rewrite aeval_f with (1:= H0);simpl;
  generalize (Zlt_cases v1 v2); case (Zlt_bool v1 v2); auto;
  intros H'; assert False by lia; contradiction.
Qed.

Lemma sos_step_f_sos :
  forall r r_a i i' r' r_a', sos_step r r_a i i' r' r_a' ->
   f_sos r r_a i = Some(r', r_a', i').
Proof with eauto.
  induction 1...
  unfold f_sos, bind...
  match goal with id : _ |- _ => rewrite aeval_f with (1:=id) end.
  now match goal with id : _ |- _ => rewrite id end.
  simpl.
  case (eq_skip i1).
   intros; subst; inversion H.
   intros; rewrite IHsos_step; eauto.
  simpl; match goal with id :_ |- _ => rewrite beval_f with (1:=id); auto end.
  simpl; match goal with id :_ |- _ => rewrite beval_f with (1:=id); auto end.
  simpl; match goal with id :_ |- _ => rewrite aeval_f with (1 := id); auto end.
  simpl; match goal with id :_ |- _ => rewrite aeval_f with (1 := id); auto end.
  simpl; match goal with id :_ |- _ =>
          rewrite Z_to_option_natP with (1 := id); auto end.
  simpl; match goal with id :_ |- _ => rewrite id; auto end.
Qed.

Ltac find_deep_bind a :=
  match a with
    bind ?a _ => find_deep_bind a
  | bind2 ?a _ => find_deep_bind a
  | bind3 ?a _ => find_deep_bind a
  | _ => a
  end.

Ltac unbind_hyp H v Heq :=
  match type of H with
  |  bind ?a ?b = Some _ =>
     let c := find_deep_bind a in
     (case_eq c; [intros v Heq | intros Heq]; rewrite Heq in H;
     [simpl in H | discriminate H])
  |  bind2 ?a ?b = Some _ =>
     let c := find_deep_bind a in
     case_eq c; [intros v Heq | intros Heq]; rewrite Heq in H;
     [simpl in H | discriminate H]
  |  bind3 ?a ?b = Some _ =>
     let c := find_deep_bind a in
     case_eq c; [intros v Heq | intros Heq]; rewrite Heq in H;
     [simpl in H | discriminate H]
  end.

Lemma af_eval :
  forall r r_a e v, af r r_a e = Some v -> aeval r r_a e v.
Proof with eauto.
  induction e; intros v...
  simpl; intros Heq; injection Heq; intros; subst...
  simpl; case_eq (af r r_a e2); case_eq (af r r_a e1);
     try (intros;discriminate).
  intros v1 Heq1 v2 Heq2 Heq; injection Heq; intros; subst...
  simpl; case_eq (af r r_a e); simpl.
  unfold Z_to_option_nat.
  intros z afz updates. 
  unbind_hyp updates indn Heq.
  unbind_hyp updates l Heq'.
  revert Heq; case_eq (z <? 0)%Z; try discriminate.
  intros zpos; assert (0 <= z)%Z by lia.
  intros indneq; injection indneq; intros indneq'.
  apply ae_ar with (vi := z)(l := l); subst...
discriminate.
Qed.

Global Hint Resolve af_eval Z.ge_le : core.

Lemma bf_eval :
  forall r r_a e v, bf r r_a e = Some v -> beval r r_a e v.
Proof with eauto with zarith.
  intros r r_a (e1,e2) v;simpl.
  case_eq (af r r_a e1); case_eq (af r r_a e2); try (intros; discriminate).
  intros v1 Heq1 v2 Heq2; unfold bind.
  generalize (Zlt_cases v2 v1); destruct (Zlt_bool v2 v1);
  intros comp Heq; injection Heq; intros; subst v...
Qed.

Global Hint Resolve bf_eval : core.


Lemma f_sos_sos_step :
 forall r r_a i r' r_a' i', f_sos r r_a i = Some(r', r_a', i') ->
  sos_step r r_a i i' r' r_a'.
Proof with eauto.
intros r r_a i r' r_a'; induction i; intros i' H.
simpl in H; unbind_hyp H v1 He; unbind_hyp H r1 Hu;
  injection H; intros; subst...
simpl in H.
destruct (eq_skip i1).
now subst i1; injection H; intros; subst...
unbind_hyp H p H1; destruct p as [[p1 p2] p3]; injection H; intros; subst...
simpl in H; unbind_hyp H t Ht; destruct t; injection H; intros; subst...
simpl in H; discriminate.
simpl in H; unbind_hyp H p H1.
unbind_hyp H v H2.
unbind_hyp H n H3.
unbind_hyp H r_a2 H4.
injection H; intros; subst...
eapply SOS5'; try eapply af_eval; try eassumption.
unfold Z_to_option_nat in H3; destruct (v <? 0)%Z eqn:cmpv; try discriminate.
lia.
unfold Z_to_option_nat in H3; destruct (v <? 0)%Z eqn:cmpv; try discriminate.
assert (cmpv' : (0 <= v)%Z) by lia.
now injection H3; intros H3'; rewrite H3'.
Qed.

Global Hint Resolve f_sos_sos_step : core.

Lemma f_star_sem : forall n r r_a i r' r_a' i', 
 f_star n r r_a i = Some(r',r_a', i')->
 sos_star r r_a i i' r' r_a'.
Proof with eauto.
 induction n; intros r r_a i r' r_a' i' H.
now  simpl in H; injection H; intros; subst; eauto.
 simpl in H.
destruct (eq_skip i).
now subst i; injection H; intros; subst...
unbind_hyp H p H1; destruct p as [[r1 r_a1] i1]...
Qed.

Lemma f_star_exec : forall n r r_a i r' r_a',
  f_star n r r_a i = Some(r', r_a' ,skip) -> exec r r_a i r' r_a'.
Proof.
intros; apply sos_imp_sn; eapply f_star_sem; eauto.
Qed.

Lemma sos_star_f : forall r r_a i r' r_a' i', sos_star r r_a i i' r' r_a' ->
  exists n, f_star n r r_a i = Some(r', r_a', i').
induction 1.
exists 0%nat; simpl; auto.
case_eq (eq_skip i); intros Hi Hi'.
rewrite Hi in H; inversion H.
destruct IHsos_star as [n Hn]; exists (S n); simpl; rewrite Hi'.
rewrite sos_step_f_sos with (1:= H); auto.
Qed.

Lemma f_star_eq_sos :
 forall r r_a i r' r_a' i', 
 (exists n, f_star n r r_a i = Some(r', r_a', i'))
   <-> sos_star r r_a i i' r' r_a'.
Proof.
 intros r i r' i'; split;
  [intros [n Hn]; apply f_star_sem with n; auto| apply sos_star_f; auto].
Qed.

End little.

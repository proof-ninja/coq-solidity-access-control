Require Import Result Error SolidityBase Program.
Require Dict.

Require Import String.
Open Scope string_scope.
(*
  IAccessControl.sol: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/IAccessControl.sol
  AccessControl.sol: https://github.com/OpenZeppelin/openzeppelin-contracts/blob/master/contracts/access/AccessControl.sol
 *)

Inductive role : Set :=
| Admin
| Minter
| Pauser
| Burner.

Parameter role_eq_dec: forall x y: role, {x = y} + {x <> y}.

Module Roles.
  Parameter t : Set.
  Parameter has : role -> address -> t -> bool.
  Parameter set : role -> address -> bool -> t -> t.
  Axiom same : forall t1 t2,
    (forall r acc, has r acc t1 = has r acc t2) -> t1 = t2.

  Axiom has_set : forall r acc (t0: t) b, has r acc (set r acc b t0) = b.
  Axiom has_set_other : forall r1 r2 acc1 acc2 (t0: t) b, r1 <> r2 \/ acc1 <> acc2 ->
                                            has r2 acc2 (set r1 acc1 b t0) = has r2 acc2 t0.
  Lemma set_set : forall r acc t0 b1 b2,
      set r acc b2 (set r acc b1 t0) = set r acc b2 t0.
  Proof.
    intros r acc t0 b1 b2. apply same. intros r0 acc0.
    destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec r r0)(address_eq_dec acc acc0)).
    + destruct a. subst acc0 r0.
      now do 2 rewrite has_set.
    + now do 3 (rewrite has_set_other; [|now idtac]).
  Qed.
End Roles.

Definition roleData := Roles.t.

Record storage : Set := {
    roles: Roles.t
}.

Inductive operation : Set :=
| HasRole (role: bytes32) (account : address)
(*| GetRoleAdmin (role : bytes32)*)
| GrantRole (role : role)(account : address)
| RevokeRole (role : role)(account : address)
(*| RenonceRole (role : bytes32)(callerConfirmation : address)*)
.

Definition sender : Set := address.

Parameter next : operation -> sender -> storage -> result storage error.

Axiom HasRoleS : forall role account sender storage,
    next (HasRole role account) sender storage = Success storage.

Axiom GrantRoleS : forall role account sender storage,
    Roles.has Admin sender storage.(roles) = true ->
    next (GrantRole role account) sender storage
    = Success ({|roles := Roles.set role account true storage.(roles) |}).

Axiom GrantRoleE : forall role account sender storage,
    Roles.has Admin sender storage.(roles) = false ->
    next (GrantRole role account) sender storage
    = Error "GrantRole".

Axiom RevokeRoleS : forall role acc sender storage,
    Roles.has Admin sender storage.(roles) = true ->
    next (RevokeRole role acc) sender storage
    = Success ({|roles := Roles.set role acc false storage.(roles) |}).

Axiom RevokeRoleE : forall role account sender storage,
    Roles.has Admin sender storage.(roles) = false ->
    next (RevokeRole role account) sender storage
    = Error "RevokeRole".


Lemma next_inv : forall (op: operation) (sender : address) (s1 s2: storage),
    next op sender s1 = Success s2 ->
    exists op' sender', next op' sender' s2 = Success s1.
Proof.
  destruct op; intros sender [rs1] [rs2].
  - (* op = HasRole の場合 *)
    rewrite HasRoleS.
    exists (HasRole role0 account), sender.
    now rewrite HasRoleS.
  - (* op = GrantRole の場合 *)
    destruct (Roles.has Admin sender rs1) eqn: is_sender_admin; [|now rewrite GrantRoleE].
    rewrite GrantRoleS; [|now auto]. injection 1. intros eqs2.
    destruct (Roles.has role0 account rs1) eqn: has_role.
    + (* s1ですでにrole0権限を持っている場合は s1=s2 *)
      exists (GrantRole role0 account), sender. rewrite <- eqs2. rewrite GrantRoleS.
      * simpl. rewrite Roles.set_set.
        do 2 f_equal. apply Roles.same. intros r acc.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 r)(address_eq_dec account acc)).
        -- destruct a. subst r acc. now rewrite Roles.has_set, has_role.
        -- now rewrite Roles.has_set_other.
      * simpl. destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 Admin)(address_eq_dec account sender)).
        -- destruct a. subst role0 account. now rewrite Roles.has_set.
        -- now rewrite Roles.has_set_other.
    + (* s1でrole0を持っていなかった場合 *)
      exists (RevokeRole role0 account), sender. rewrite <- eqs2.
      rewrite RevokeRoleS.
      * do 2 f_equal. simpl.
        rewrite Roles.set_set.
        apply Roles.same. intros r acc.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 r)(address_eq_dec account acc)).
        -- destruct a. subst r acc. now rewrite Roles.has_set, has_role.
        -- now rewrite Roles.has_set_other.
      * simpl. destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 Admin)(address_eq_dec account sender)).
        -- destruct a. subst role0 account. now rewrite Roles.has_set.
        -- now rewrite Roles.has_set_other.
  - (* op = RevokeRole の場合 *)
    destruct (Roles.has Admin sender rs1) eqn: is_sender_admin; [|now rewrite RevokeRoleE].
    rewrite RevokeRoleS; [|now auto]. simpl. injection 1. intros eqs2.
    rewrite <- eqs2.
    destruct (Roles.has role0 account rs1) eqn: has_role.
    + (* 実行前のs1でrole0の権限があった場合 *)
      exists (GrantRole role0 account), sender.
      rewrite GrantRoleS.
      * (* *)
        do 2 f_equal. simpl. rewrite Roles.set_set.
        apply Roles.same. intros r acc.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 r)(address_eq_dec account acc)).
        -- destruct a. subst r acc. now rewrite Roles.has_set, has_role.
        -- now rewrite Roles.has_set_other.
      * (* s2 で senderがAdminである必要がある *)
        simpl.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 Admin)(address_eq_dec account sender)).
        -- destruct a. subst role0 account. rewrite Roles.has_set.
           (* ??? : false = true ??? *)
           admit.
        -- now rewrite Roles.has_set_other, is_sender_admin.
    + (* 実行前のs1ですでにrole0の権限がない場合 : s1=s2 *)
      exists (RevokeRole role0 account), sender.
      rewrite RevokeRoleS. simpl.
      * do 2 f_equal.
        rewrite Roles.set_set. apply Roles.same. intros r acc.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 r)(address_eq_dec account acc)).
        -- destruct a. subst r acc. now rewrite Roles.has_set, has_role.
        -- now rewrite Roles.has_set_other.
      * simpl.
        destruct (Sumbool.sumbool_and _ _ _ _ (role_eq_dec role0 Admin)(address_eq_dec account sender)).
        -- destruct a. subst role0 account. now rewrite has_role in is_sender_admin.
        -- now rewrite Roles.has_set_other.
Admitted.

Inductive reach : storage -> storage -> Prop :=
| ReachSS : forall s: storage, reach s s
| ReachStep : forall (s1 s2 s3: storage) (op: operation) (sd: address),
    next op sd s2 = Success s3 -> reach s1 s2 ->
    reach s1 s3.

Lemma reach_cons : forall (s1' s1 s2 : storage)(op : operation) (sender: address),
    reach s1 s2 -> next op sender s1' = Success s1 ->
    reach s1' s2.
Proof.
  intros s1' s1 s2 op sender reach_s1s2 nexts1'.
  revert op sender nexts1'.
  induction reach_s1s2; intros op0 sender next1.
  - apply (ReachStep _ s1' _ op0 sender next1).
    now apply ReachSS.
  - apply (ReachStep _ s2 _ op sd); [assumption|].
    now apply (IHreach_s1s2 op0 sender).
Qed.

Theorem soundness : forall (initial_storage st: storage),
    reach initial_storage st -> reach st initial_storage.
Proof.
  intros s1 s2 reach_s1s2.
  induction reach_s1s2.
  - now apply ReachSS.
  - destruct (next_inv _ _ _ _ H) as [op' [sender' next']].
    now apply (reach_cons _ s2 _ op' sender').
Qed.

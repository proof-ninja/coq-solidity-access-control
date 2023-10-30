Require Import List Sumbool.
Import ListNotations.

Section Dict.

Variables K V : Set.
Variable eq_key_dec : forall (x y: K), {x = y} + {x <> y}.

Definition t : Set := list (K * V).

Definition empty : t := [].

Definition find (key: K) (dict : t) : option V :=
  let opt :=
    List.find
      (fun '(k,v) => if eq_key_dec k key then true else false)
      dict
  in
  option_map snd opt.


Definition delete key dict : t :=
  List.filter (fun '(k,v) =>
(*                 proj1_sig (bool_of_sumbool (sumbool_not _ _ (eq_key_dec k key)))) dict.*)
                 if eq_key_dec k key then false
                 else true) dict.

Definition update key value dict : t :=
  (key, value) :: (delete key dict).

Definition size (dict: t) : nat :=
  List.length dict.

Definition Forall (P: K -> V -> Prop) (dict: t) : Prop :=
  List.Forall (fun '(k, v) => P k v) dict.

Definition Forall_dec (P: K -> V -> Prop) (P_dec: forall (k: K) (v: V), {P k v} + {~P k v}) dict:
  {Forall P dict} + {~Forall P dict}.
refine (List.Forall_dec (fun '(k, v) => P k v) (fun '(k, v) => P_dec k v) dict).
Defined.

End Dict.

Arguments find [K V ].
Arguments delete [K V].
Arguments update [K V].
Arguments size [K V].
Arguments Forall [K V].
Arguments Forall_dec [K V P].

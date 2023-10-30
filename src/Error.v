Require Import String.
Open Scope string_scope.

Definition t := string.
Notation error := t.

Definition AuthenticationError : t := "Authenticatoin Error".
Definition CannotPrivilegeOperation: t := "Cannot Privilege Operation".

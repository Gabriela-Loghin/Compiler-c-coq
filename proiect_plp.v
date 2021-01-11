Require Import Arith.
Require Import Ascii.
Require Import Nat.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Scheme Equality for string.
Local Open Scope string_scope.

Inductive NaturaL : Type :=
| TypeNat : nat -> NaturaL
| ErrorNat : NaturaL. 

Inductive BooleaN : Type :=
| TypeBool : bool -> BooleaN
| ErrorBool : BooleaN.

Inductive StringS : Type :=
| TypeString : string -> StringS
| ErrorString : StringS.

Inductive Types : Type := 
| Nats (n : NaturaL)
| Bools (b : BooleaN)
| undeclared : Types
| assign : Types
| default : Types
|Error.

Definition eqb_string (x y : String.string) : bool :=
  if string_dec x y then true else false.

Coercion TypeNat : nat >-> NaturaL.
Coercion TypeBool : bool >-> BooleaN.
Coercion TypeString : string >->StringS.

Scheme Equality for Types.

Definition Env := string -> Types.

Coercion Nats : NaturaL >-> Types.
Coercion Bools : BooleaN >-> Types.

(*EXPRESII ARITMETICE *)
Inductive AExp :=
| a_variabila : string -> AExp
| a_numar : NaturaL -> AExp
| a_plus : AExp -> AExp -> AExp
| a_mul : AExp -> AExp -> AExp
| a_minus : AExp -> AExp -> AExp
| a_mod : AExp -> AExp -> AExp 
| a_div : AExp -> AExp -> AExp.

Inductive Var := n | i | x | y | sum.

(*Notatii folosite pentru expresii aritmetice*)

Notation "A +' B" := (a_plus A B) (at level 48).
Notation "A -' B" := (a_minus A B) (at level 48).
Notation "A /' B" := (a_div A B) (at level 46).
Notation "A *' B" := (a_mul A B) (at level 46).
Notation "A %' B" := (a_mod A B) (at level 47).

Coercion a_numar: NaturaL >-> AExp.
Coercion a_variabila: string >-> AExp.

Check "y".
Check( 10 %' 2).


Definition pluses (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => TypeNat(a + b)
| TypeBool a, TypeBool b => match a,b with
                    | true, true => TypeNat 2
                    | false, false => TypeNat 0
                    | _, _ => TypeNat 1
                    end
| TypeNat a, TypeBool b => match b with
                   | true => TypeNat (a + 1)
                   | false => TypeNat (a + 0)
                   end
| TypeBool a, TypeNat b => match a with
                   | true => TypeNat (1 + b)
                   | false => TypeNat (0 + b)
                   end 
| _, _ => ErrorNat
end. 


Compute (pluses true true).
Compute (pluses false false).
Compute (pluses 20 20).

Definition minuses (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => TypeNat(a - b)
| TypeBool a, TypeBool b => match a, b with
                    | true, false => TypeNat 1
                    | _, _ => TypeNat 0
                    end
| TypeNat a, TypeBool b => match b with
                   | true => TypeNat (a - 1)
                   | false => TypeNat a
                   end
| TypeBool a, TypeNat b => match a with
                   | true => TypeNat (1 - b)
                   | false => TypeNat (0 - b)
                   end 
| _, _ => ErrorNat
end. 

Compute (minuses 10 11).
Compute (minuses 10 true).
Compute (minuses 43 false).
Compute (minuses true false).
Compute (minuses false true).
Compute (minuses false 5).

Definition inmultiri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => TypeNat(a * b)
| TypeBool a, TypeBool b => match a, b with
                    | true, true => TypeNat 1
                    | _, _ => TypeNat 0
                    end
| TypeNat a, TypeBool b => match b with
                   | true => TypeNat a
                   | false => TypeNat 0
                   end
| TypeBool a, TypeNat b => match a with
                   | true => TypeNat b
                   | false => TypeNat 0
                   end 
| _, _ => ErrorNat
end.

Compute (inmultiri 20 100).
Compute (inmultiri 17 true). 
Compute (inmultiri false 19).
Compute (inmultiri true false).
Compute (inmultiri true true).

Definition impartiri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => match b with
                          | 0 => ErrorNat
                          | _ => TypeNat(div a b)
                          end
| TypeBool a, TypeBool b => match a, b with
                            | true, true => TypeNat 1
                            | false, true => TypeNat 0
                            | _, _ => ErrorNat
                            end
| TypeNat a, TypeBool b => match b with
                           | true => TypeNat a
                           | false => ErrorNat
                           end
| TypeBool a, TypeNat b => match a, b with
                           | _, 0 => ErrorNat
                           | true, _ => TypeNat (div 1 b)
                           | false, _ => TypeNat 0
                           end 
| _, _ => ErrorNat
end.

Compute (impartiri 18 9).
Compute (impartiri 23 3).
Compute (impartiri 29 true).
Compute (impartiri 29 false).
Compute (impartiri false true).
Compute (impartiri true true).

Definition modes (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => match b with
                          | 0 => ErrorNat
                          | _ => TypeNat(modulo a b)
                          end
| TypeBool a, TypeBool b => match a, b with
                            | true, true => TypeNat 0
                            | false, true => TypeNat 0
                            | _, _ => ErrorNat
                            end
| TypeNat a, TypeBool b => match b with
                           | true => TypeNat 0
                           | false => ErrorNat
                           end
| TypeBool a, TypeNat b => match a, b with
                           | _, 0 => ErrorNat
                           | true, _ => TypeNat (modulo 1 b)
                           | false, _ => TypeNat 0
                           end 
| _, _ => ErrorNat
end.

Compute (modes 24 6).
Compute (modes 29 6).
Compute (modes 28 true).
Compute (modes 28 false).
Compute (modes false true).
Compute (modes true false).


Fixpoint A_Eval (exp : AExp) (env : Env) : Types :=
match exp with
| a_numar a => a
| a_variabila a => env a
| a_plus a b => pluses (A_Eval a env) (A_Eval b env)
| a_minus a b => minuses (A_Eval a env) (A_Eval b env)
| a_mul a b => inmultiri (A_Eval a env) (A_Eval b env)
| a_div a b => impartiri (A_Eval a env) (A_Eval b env)
| a_mod a b => modes (A_Eval a env) (A_Eval b env)
end.

Reserved Notation "A =[ S ]=> N" (at level 70). 


(*Inductive aeval : AExp -> Env -> Types -> Prop :=
| const : forall a sigma, a_numar a =[ sigma ]=> a
| var : forall v sigma, a_variabila v =[ sigma ]=> (sigma v) 
| add' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[ sigma ]=> n
| min' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[ sigma ]=> n
| mul' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| div' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    negb(Nat.eqb i2 0) = true ->
    n = i1 / i2 ->
    a1 /' a2 =[ sigma ]=> n
| mod' : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    negb(Nat.eqb i2 0) = true ->
    n = i1 mod i2 ->
    a1 %' a2 =[ sigma ]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).  *)  

Inductive BExp :=
| btrue 
| bfalse
| b_egal : AExp -> AExp -> BExp (* sintaxa pentru egal *)
| b_less : AExp -> AExp -> BExp
| b_lessequal : AExp -> AExp -> BExp
| b_greater : AExp -> AExp -> BExp
| b_greaterequal : AExp -> AExp -> BExp
| b_notegal : AExp -> AExp -> BExp
| b_not : BExp -> BExp (*sintaxa pentru not*)
| b_and : BExp -> BExp -> BExp (*sintaxa pentru and *)
| b_or : BExp -> BExp -> BExp (*sintaxa pentru or*)
(*| b_xor : BExp -> BExp -> BExp*). (*sintaxa pentru xor*)

(*Notatii  pentru expresii booleane*)
Notation "! A" := (b_not A) (at level 52).
Notation "A &&' B" := (b_and A B) (at level 53).
Notation "A ||' B" := (b_or A B) (at level 54).
(*Notation "A \\' B " := (b_xor A B) (at level 54).*)
Notation "A <' B" := (b_less A B) (at level 70, no associativity).
Notation "A <=' B" := (b_lessequal A B) (at level 70, no associativity).
Notation "A >' B" := (b_greater A B) (at level 70, no associativity).
Notation "A >=' B" := (b_greaterequal A B) (at level 70, no associativity).
Notation "A ==' B" := (b_egal A B) (at level 70, no associativity).
Notation "A !=' B" := (b_notegal A B) (at level 70, no associativity).

Check 4 +' 5.
Check (btrue &&' bfalse ).
Check ( ! btrue).
Check( btrue ||' bfalse).
(*Check( btrue \\' bfalse).*)
Check( 1 <' 2).
Check( 1 <=' 2).

Definition not_uri (a : Types) :=
match a with
| TypeNat a => match a with
               | 0 => TypeBool true
               | _ => TypeBool false
               end
| TypeBool a => match a with
               | true => TypeBool false
               | false => TypeBool true
               end
| _ => ErrorBool
end.

Compute ( not_uri true).
Compute ( not_uri false).
Compute ( not_uri 0).
Compute ( not_uri 12).

Definition and_uri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => match a, b with
                          | _, 0 => TypeBool false
                          | 0, _ => TypeBool false
                          | _, _ => TypeBool true
                          end
| TypeBool a, TypeBool b => match a, b with
                            | _, false => TypeBool false
                            | false, _ => TypeBool false
                            | _, _ => TypeBool true
                            end
| TypeNat a, TypeBool b => match a, b with
                           | 0, _ => TypeBool false
                           | _, false => TypeBool false
                           | _, _ => TypeBool true
                           end
| TypeBool a, TypeNat b => match a, b with
                           | false, _ => TypeBool false
                           | _, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute ( and_uri 0 1).
Compute ( and_uri  false 10) .
Compute ( and_uri true true ).
Compute ( and_uri 12 17).



Definition or_uri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => match a, b with
                          | 0, 0 => TypeBool false
                          | _, _ => TypeBool true
                          end
| TypeBool a, TypeBool b => match a, b with
                            | false, false => TypeBool false
                            | _, _ => TypeBool true
                            end
| TypeNat a, TypeBool b => match a, b with
                           | 0, false => TypeBool false
                           | _, _ => TypeBool true
                           end
| TypeBool a, TypeNat b => match a, b with
                           | false, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute ( or_uri  11 12).
Compute ( or_uri  false true).
Compute ( or_uri  false false).
Compute ( or_uri  0 false).


Definition less_uri ( a b : Types) :=
match a , b with
| TypeNat a, TypeNat b => TypeBool (ltb a b)
| TypeBool a, TypeBool b => match a, b with
                            | false, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat a, TypeBool b => match a, b with
                           | 0, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool a, TypeNat b => match a, b with
                           | false, 0 => TypeBool false
                           | true, 0 => TypeBool false
                           | true, 1 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute ( less_uri 12 13).
Compute ( less_uri 13 12 ).
Compute ( less_uri true 13).

Definition lessequal_uri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => TypeBool (Nat.leb a b)
| TypeBool a, TypeBool b => match a, b with
                            | false, _ => TypeBool true
                            | true, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat a, TypeBool b => match a, b with
                           | 0, _ => TypeBool true
                           | 1, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool a, TypeNat b => match a, b with
                           | true, 0 => TypeBool false
                           | _, _ => TypeBool true
                           end 
| _, _ => ErrorBool
end.

Compute ( lessequal_uri true true).
Compute ( lessequal_uri false true).
Compute ( lessequal_uri 12 14).
Compute ( lessequal_uri 14 12).
Compute ( lessequal_uri true 10).
Compute ( lessequal_uri true false).

Definition greater_uri (a b : Types) := not_uri (lessequal_uri a b). 
Definition greaterequal_uri (a b : Types) := not_uri (less_uri a b).

Compute ( greater_uri true false).
Compute ( greater_uri 10 true).
Compute ( greaterequal_uri true true).
Compute ( greaterequal_uri 17 17 ).
Compute ( greaterequal_uri 15 16).


Definition equal_uri (a b : Types) :=
match a, b with
| TypeNat a, TypeNat b => TypeBool (Nat.eqb a b)
| TypeBool a, TypeBool b => match a, b with
                            | false, false => TypeBool true
                            | true, true => TypeBool true
                            | _, _ => TypeBool false
                            end
| TypeNat a, TypeBool b => match a, b with
                           | 0, false => TypeBool true
                           | 1, true => TypeBool true
                           | _, _ => TypeBool false
                           end
| TypeBool a, TypeNat b => match a, b with
                           | true, 1 => TypeBool true
                           | false, 0 => TypeBool true
                           | _, _ => TypeBool false
                           end 
| _, _ => ErrorBool
end.

Compute (equal_uri 9 9).
Compute (equal_uri false true).
Compute (equal_uri true true).
Compute (equal_uri true 1).
Compute (equal_uri false 0).
Compute (equal_uri 8 true).


Definition notequal_uri (a b : Types) := not_uri (equal_uri a b).

Compute (notequal_uri 9 9).
Compute (notequal_uri false true).
Compute (notequal_uri true true).
Compute (notequal_uri true 1).
Compute (notequal_uri false 0).
Compute (notequal_uri 8 true).

Fixpoint BEval (exp : BExp) (env : Env) : Types :=
match exp with
| btrue => true
| bfalse => false
| b_not a => not_uri (BEval a env)
| b_and a b => and_uri (BEval a env) (BEval b env)
| b_or a b => or_uri (BEval a env) (BEval b env) 
| b_less a b => less_uri (BEval a env) (BEval b env)
| b_lessequal a b => lessequal_uri (BEval a env) (BEval b env)
| b_greater a b => greater_uri (BEval a env) (BEval b env)
| b_greaterequal a b => greaterequal_uri (BEval a env) (BEval b env)
| b_egal a b => equal_uri (BEval a env) (BEval b env)
| b_notegal a b => notequal_uri (BEval a env) (BEval b env)
end.






 
  






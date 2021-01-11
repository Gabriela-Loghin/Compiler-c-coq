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


Inductive Types :=
| undecl : Types
| assign : Types
| default : Types
| nat_type : NaturaL -> Types
| bool_type : BooleaN -> Types.

Definition eqb_string (x y : String.string) : bool :=
  if string_dec x y then true else false.

Coercion TypeNat : nat >-> NaturaL.
Coercion TypeBool : bool >-> BooleaN.
Coercion TypeString : string >->StringS.

Scheme Equality for Types.

Definition Env := string -> nat.


Inductive list (T : Type) : Type :=
| null
| cons (t : T) (l : list T).

Check cons NaturaL 4 (cons NaturaL 3 (null NaturaL)).
Check cons BooleaN false (cons BooleaN true (null BooleaN)).

Arguments null {T}.
Notation "[]" := null.

Notation "{ X , .. , Y }" := (cons NaturaL X .. (cons NaturaL Y []) ..).
Notation "{ X ; .. ; Y }" := (cons BooleaN X .. (cons BooleaN Y []) ..).
Notation "{ X ;;; .. ;;; Y }" := (cons StringS X .. (cons StringS Y []) ..).

Check {1, 2, 3}.
Check {false; true; true; false}.

Definition listanat1 := {1, 2, 3, 4, 5}.
Definition listanat2 := {1, 4, 6, 8, 9}.
Definition listabool := {true; false; true; false; false}.
Definition listastring := { "gabriel" ;;; "gabriela" }.

 Inductive Vectori : Type :=
| vector_natural : list NaturaL -> Vectori
| vector_boolean : list BooleaN -> Vectori
| vector_string : list StringS -> Vectori
| Matrice : list Vectori -> Vectori. 


Check vector_natural listanat1.
Check vector_boolean listabool.

Notation "{ X & .. & Y }" := (cons Vectori X .. (cons Vectori Y []) ..).
Check Matrice { (vector_natural listanat1) & ( vector_natural listanat2) }.

Notation "'[Natural]' = V " := (vector_natural V) (at level 20).
Notation "'[Boolean]' = V " := (vector_boolean V) (at level 20).
Notation "'[String]' = V " := (vector_string V) (at level 20).
Notation "'[[Matrice]]' = V" := (Matrice V) (at level 20).


Definition vector_nat := [Natural] = listanat1.
Definition vector_bool := [Boolean] = listabool.
Definition vector_string1 := [String] = listastring.


Compute vector_nat.
Compute vector_bool.
Compute vector_string.


(*EXPRESII ARITMETICE *)
Inductive AExp :=
| a_variabila : string -> AExp
| a_numar : nat -> AExp
| a_plus : AExp -> AExp -> AExp
| a_mul : AExp -> AExp -> AExp
| a_min : AExp -> AExp -> AExp
| a_mod : AExp -> AExp -> AExp 
| a_div : AExp -> AExp -> AExp.

Inductive Var := n | i | x | y | sum.

(*Notatii folosite pentru expresii aritmetice*)

Notation "A +' B" := (a_plus A B) (at level 48).
Notation "A -' B" := (a_min A B) (at level 48).
Notation "A /' B" := (a_div A B) (at level 46).
Notation "A *' B" := (a_mul A B) (at level 46).
Notation "A %' B" := (a_mod A B) (at level 47).

Coercion a_numar: nat >-> AExp.
Coercion a_variabila: string >-> AExp.

Check "y".
Check( 1 %' 2).

Fixpoint aeval (a : AExp)(env : Env) : nat :=
  match a with
    | a_variabila var => env var
    | a_numar n' => n'
    | a_plus a1 a2 => (aeval a1 env) + (aeval a2 env)
    | a_mul a1 a2 => (aeval a1 env) * (aeval a2 env)
    | a_min a1 a2 => if (Nat.leb (aeval a1 env) (aeval a2 env))
                    then 0
                    else (aeval a1 env) - (aeval a2 env)
    | a_div a1 a2 => if (Nat.eqb (aeval a2 env) 0)
                    then 0
                    else (aeval a1 env) / (aeval a2 env)
    | a_mod a1 a2 => if (Nat.eqb (aeval a2 env) 0)
                    then (aeval a1 env)
                    else ((aeval a1 env) mod (aeval a2 env))
end.

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

Definition beval (b : BExp)(env : Env) : bool :=
  match b with 
  | btrue => true
  | bfalse => false
  | b_not a1 => false
  | b_and a1 a2 => false
  | b_or a1 a2 => true
  | b_less a1 a2 => Nat.ltb (aeval a1 env) (aeval a2 env)
  | b_lessequal a1 a2 => Nat.leb (aeval a1 env)(aeval a2 env)
  | b_greater a1 a2 => Nat.ltb (aeval a2 env)(aeval a1 env)
  | b_greaterequal a1 a2 => Nat.leb (aeval a2 env)(aeval a1 env)
  | b_egal a1 a2 => Nat.eqb (aeval a1 env)(aeval a2 env)
  | b_notegal a1 a2 => negb (Nat.eqb (aeval a1 env)(aeval a2 env))
end.

(* Functii predefinite *)
Inductive Functii :=
| Max : AExp -> AExp -> Functii
| Min : AExp -> AExp -> Functii
| Egal : AExp -> AExp -> Functii
| Putere : AExp -> AExp -> Functii.

Notation "'Max' '(' A , B ')'" := (Max A B) (at level 50).
Notation "'Min' '(' A , B ')'" := (Min A B) (at level 50).
Notation "'Egal' '(' A , B ')'" := (Egal A B) (at level 50).
Notation "'Putere' '(' A , B ')'" := (Putere A B) (at level 57).

Check ( Max(1, 2) ).
Check ( Min(1, 2) ).
Check ( Egal(19 +' 23 *' 3, 22 /' 4 -' 2) ).
Check ( Putere(2, 3) ).

Inductive Stmt : Type :=
(*DECLARARI*)
| declarareNatural :  string -> Stmt
| declarareBoolean :  string -> Stmt
| declarareString :  string -> Stmt

(*ATRIBURI*)
| atribuireNatural : string -> AExp -> Stmt
| atribuireBoolean : string -> BExp -> Stmt
| atribuireString : string -> AExp -> Stmt

(*INITIALIZARI*)
| initializareNatural : string -> AExp -> Stmt
| initializareBoolean : string -> BExp -> Stmt
| initializareString : string -> AExp -> Stmt

(*INSTRUCTIUNI*)
| pop : string -> Stmt
| secventa : Stmt -> Stmt -> Stmt
| incrementare : string -> AExp -> Stmt (*sintaxa pentru incrementare*)
| decrementare : string -> AExp -> Stmt (*sintaxa pentru decrementare*)
| if_then_else : BExp -> Stmt -> Stmt -> Stmt
| if_then : BExp -> Stmt -> Stmt 
| while_do : BExp -> Stmt -> Stmt 
| for_do : Stmt -> BExp -> Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| functie : string -> Stmt -> Stmt
| comentariu  : string -> Stmt (*sintaxa pentru comentarii*)

(*VECTORI*)
| declarare_vector_natural : string -> Stmt
| declarare_vector_boolean : string -> Stmt
| declarare_vector_string : string -> Stmt
| declarare_matrice : string -> Stmt

| initializare_vector_natural : string -> list NaturaL -> Stmt
| initializare_vector_boolean : string -> list BooleaN -> Stmt
| initializare_vector_string : string -> list StringS-> Stmt
| initializare_matrice : string -> list Vectori -> Stmt

| element: string -> nat -> Stmt

| valoareElemNatural : string -> nat -> NaturaL -> Stmt
| valoareElemBoolean : string -> nat -> BooleaN -> Stmt
| valoareElemString : string -> nat -> StringS-> Stmt
| valoareElemMatrice : string -> nat -> Vectori -> Stmt

| adaugareNatural : string -> NaturaL -> Stmt
| adaugareBoolean : string -> BooleaN -> Stmt
| adaugareString : string -> StringS -> Stmt
| adaugareMatrice : string -> Vectori -> Stmt 

| eliminare : string -> Stmt.

 
Notation "'natural' S" := (declarareNatural S) (at level 79).
Notation "'boolean' S" := (declarareBoolean S) (at level 79).
Notation "'char' S" := (declarareString S) (at level 79).

Notation "S =nat= X" := (atribuireNatural S X) (at level 80).
Notation "S =bool= X" := (atribuireBoolean S X) (at level 80).
Notation "S =string= X" := (atribuireString S X) (at level 80).

Notation "'natural' S ::= A" := (initializareNatural S A) (at level 78).
Notation "'boolean' S [=] A" := (initializareBoolean S A) (at level 78).
Notation "'char' S [=] A" := (initializareString S A) (at level 78).

Notation "S1 ;; S2" := (secventa S1 S2 ) (at level 98, left associativity).
Notation "I ++" := (incrementare I 1) (at level 60).
Notation "D --" := (decrementare D 1) (at level 60).
Notation "'If' ( A ) 'Then' ( S1 ) 'Else' ( S2 ) 'EndIF'" := (if_then_else A S1 S2) (at level 97).
Notation "'If' ( A ) 'Then' ( S ) 'EndIF1'" := (if_then A S ) (at level 97).
Notation "'While' ( C ) # S # 'EndWhile' " := (while_do C S) (at level 97).
Notation "'For' ( S1 ';' C ';' S2 ) { S3 }  'EndF'" := (for_do S1 C S2 S3) (at level 97).



Notation "'Break'" := (break) (at level 97).
Notation "'Continue'" := (continue) (at level 97).
Notation " // A \\  " := (comentariu A) (at level 99).
Notation " 'f' ( A ) { B } " := (functie A B) (at level 90).
Notation "'switch'  'case' ( A ) ( B ) ( 'case' ( C )  ( D ) 'default' ( E ))" := (if_then_else A B (if_then_else C D E)) (at level 66).

Notation "[Is_V_Natural] V" := (declarare_vector_natural V) (at level 79).
Notation "[Is_V_Boolean] V" := (declarare_vector_boolean V) (at level 79).
Notation "[Is_V_String] V" := (declarare_vector_string V) (at level 79).
Notation "[Is_V_Matrice] V" := (declarare_matrice V) (at level 79).

Notation "[Natural] V ::= W" := (initializare_vector_natural V W) (at level 79).
Notation "[Boolean] V ::= W" := (initializare_vector_boolean V W) (at level 79).
Notation "[String] V ::= W" := (initializare_vector_string V W) (at level 79).
Notation "[[Matrice]] V ::= W" := (initializare_matrice V W) (at level 79).

Notation "V [ P ]" := (element V P)(at level 79).

Notation "V [ P ] :n= W" := (valoareElemNatural V P W) (at level 78). 
Notation "V [ P ] :b= W" := (valoareElemBoolean V P W) (at level 78). 
Notation "V [ P ] :s= W" := (valoareElemString V P W) (at level 78). 
Notation "V [ P ] :m= W" := (valoareElemMatrice V P W) (at level 78). 

Notation "pushnat( V ) X" := (adaugareNatural V X) (at level 79).
Notation "pushbool( V ) X" := (adaugareBoolean V X) (at level 79).
Notation "pushstring( V ) X" := (adaugareString V X) (at level 79).
Notation "pushmatrice( V ) X" := (adaugareMatrice V X) (at level 79).

Notation "pop ( V )" := (pop V) (at level 79).

Check ( char "c" ) .
Check( boolean "aux").
Check( natural "i").
Check ("i" =nat= 1).
Check( "i" =bool= btrue).
Check( "i" =string= "c").
Check( "i" ++).
Check( "a" --).
Check( Break).
Check( Continue).
Check(  // "acesta este un comentariu" \\ ).
Check( If ( btrue ) Then ( "i" =nat= 1 ) EndIF1 ).
Check( "s" [ 23 ] :n= 434).
Check( "s" [ 23 ] :b= TypeBool true).
Check( pushnat( "v" ) 43 ).
Check( pushbool( "v" ) TypeBool true ).
Check( pushstring( "v" ) "string" ).
Check( pop ( "v" ) ).

Definition program1 :=
boolean "is_bool";;
"is_bool" =bool= btrue ;;
"is_bool" =bool= btrue &&' bfalse ;;
[Is_V_Natural] "vec";;
pushnat( "vec" ) 1 ;;
pushnat( "vec" ) 2 ;;
pop ("vec");;
pushnat( "vec" ) 3 ;;
natural "t";;
"t" =nat= 0 ;;
natural "x" ;;
"t" =nat= 4 ;;
While ( "x" <=' 1000 ) #
	"x" ++ ;;
	If ( "x" %' 3 ==' 0 ) Then ( "x" =nat= "x" +' 3 ;; "t" =nat= "t" +' 1 ) EndIF1
 # EndWhile.
Check program1.


Definition program2 :=
natural "a" ;;
natural "b" ;;
natural "c" ;; // "exemplu de comentariu" \\ ;;
"c" =nat= "a" +' "b" ;;
"c" ++ ;;
Break ;;
natural  "i" ;;
natural "p" ;;
If ( btrue ) Then ( "i" =nat= 1 ) EndIF1 .

Check program2.



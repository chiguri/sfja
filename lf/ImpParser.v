(** * ImpParser: Coqでの字句解析と構文解析 *)
(* begin hide *)
(** * ImpParser: Lexing and Parsing in Coq *)
(* end hide *)

(* begin hide *)
(** The development of the Imp language in [Imp.v] completely ignores
    issues of concrete syntax -- how an ascii string that a programmer
    might write gets translated into abstract syntax trees defined by
    the datatypes [aexp], [bexp], and [com].  In this chapter, we
    illustrate how the rest of the story can be filled in by building
    a simple lexical analyzer and parser using Coq's functional
    programming facilities. *)
(* end hide *)
(** [Imp.v]でのImp言語の開発は、具象構文の問題を完全に無視しています。
    つまり、プログラマが書く文字列をデータ型[aexp]、[bexp]、[com]で定義された抽象構文木にどうやって変換するか、という問題です。
    この章では、Coqの関数プログラミング機能によって簡単な字句解析器と構文解析器（パーサ）を構築することで、この残っている問題を終わらせます。 *)

(* begin hide *)
(** It is not important to understand all the details here (and
    accordingly, the explanations are fairly terse and there are no
    exercises).  The main point is simply to demonstrate that it can
    be done.  You are invited to look through the code -- most of it
    is not very complicated, though the parser relies on some
    "monadic" programming idioms that may require a little work to
    make out -- but most readers will probably want to just skim down
    to the Examples section at the very end to get the punchline. *)
(* end hide *)
(** ここでやることは、細部まで理解する必要はありません（説明はかなり少なく、練習問題もありません。）
    一番のポイントは単に、それができることを示すことです。
    コードを眺めてみて欲しいところです。ほとんどの部分はそれほど複雑ではありません。
    ただパーサはある「モナド的」プログラミング法をしているので、理解するのにちょっと骨が折れるかもしれません。
    もっとも、ほとんどの読者は、一番最後の「例」の場所まで流し読みしたくなるでしょう。 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Import ListNotations.
From LF Require Import Maps Imp.

(* ################################################################# *)
(* begin hide *)
(** * Internals *)
(* end hide *)
(** * 内部処理 *)

(* ================================================================= *)
(* begin hide *)
(** ** Lexical Analysis *)
(* end hide *)
(** ** 字句解析 *)

Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)   (* space *)
           (n =? 9))   (* tab *)
      (orb (n =? 10)   (* linefeed *)
           (n =? 13)). (* Carriage return. *)

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12=3  223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.
Proof. reflexivity. Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Parsing *)
(* end hide *)
(** ** 構文解析 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Options With Errors *)
(* end hide *)
(** *** Error付きOption *)

(* begin hide *)
(** An [option] type with error messages: *)
(* end hide *)
(** エラーメッセージを付けた[option]です。 *)

Inductive optionE (X:Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

(* begin hide *)
(** Some syntactic sugar to make writing nested match-expressions on
    optionE more convenient. *)
(* end hide *)
(** ネストされたoptionEの上のマッチ式をより簡単に書くための構文糖衣。 *)

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3"
   := (match e1 with
       | SomeE p => e2
       | NoneE _ => e3
       end)
   (right associativity, p pattern,
    at level 60, e1 at next level, e2 at next level).

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Generic Combinators for Building Parsers *)
(* end hide *)
(** *** パーサ構築のための一般コンビネータ *)

Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ =>
      NoneE "Too many recursive calls"
  | _, NoneE _ =>
      SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') =>
      many_helper p (t :: acc) steps' xs'
  end.

(** A (step-indexed) parser that expects zero or more [p]s: *)

Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

(* begin hide *)
(** A parser that expects a given token, followed by [p]: *)
(* end hide *)
(** [p]の前のトークンを設定するパーサ *)

Definition firstExpect {T} (t : token) (p : parser T)
                     : parser T :=
  fun xs => match xs with
            | x::xs' =>
              if string_dec x t
              then p xs'
              else NoneE ("expected '" ++ t ++ "'.")
            | [] =>
              NoneE ("expected '" ++ t ++ "'.")
            end.

(* begin hide *)
(** A parser that expects a particular token: *)
(* end hide *)
(** 特定のトークンを設定するパーサ *)

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** A Recursive-Descent Parser for Imp *)
(* end hide *)
(** *** Impの再帰下降パーサ *)

(* begin hide *)
(** Identifiers: *)
(* end hide *)
(** 識別子 *)

Definition parseIdentifier (xs : list token)
                         : optionE (string * list token) :=
match xs with
| [] => NoneE "Expected identifier"
| x::xs' =>
    if forallb isLowerAlpha (list_of_string x) then
      SomeE (x, xs')
    else
      NoneE ("Illegal identifier:'" ++ x ++ "'")
end.

(* begin hide *)
(** Numbers: *)
(* end hide *)
(** 数値 *)

Definition parseNumber (xs : list token)
                     : optionE (nat * list token) :=
match xs with
| [] => NoneE "Expected number"
| x::xs' =>
    if forallb isDigit (list_of_string x) then
      SomeE (fold_left
               (fun n d =>
                  10 * n + (nat_of_ascii d -
                            nat_of_ascii "0"%char))
               (list_of_string x)
               0,
             xs')
    else
      NoneE "Expected number"
end.

(* begin hide *)
(** Parse arithmetic expressions *)
(* end hide *)
(** 算術式の構文解析 *)

Fixpoint parsePrimaryExp (steps:nat)
                         (xs : list token)
                       : optionE (aexp * list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
      TRY ' (i, rest) <- parseIdentifier xs ;;
          SomeE (AId i, rest)
      OR
      TRY ' (n, rest) <- parseNumber xs ;;
          SomeE (ANum n, rest)
      OR
      ' (e, rest) <- firstExpect "(" (parseSumExp steps') xs ;;
      ' (u, rest') <- expect ")" rest ;;
      SomeE (e,rest')
  end

with parseProductExp (steps:nat)
                     (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parsePrimaryExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps'))
                          steps' rest ;;
    SomeE (fold_left AMult es e, rest')
  end

with parseSumExp (steps:nat) (xs : list token)  :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseProductExp steps' xs ;;
    ' (es, rest') <-
        many (fun xs =>
                TRY ' (e,rest') <-
                    firstExpect "+"
                                (parseProductExp steps') xs ;;
                    SomeE ( (true, e), rest')
                OR
                ' (e, rest') <-
                    firstExpect "-"
                                (parseProductExp steps') xs ;;
                SomeE ( (false, e), rest'))
        steps' rest ;;
      SomeE (fold_left (fun e0 term =>
                          match term with
                          | (true,  e) => APlus e0 e
                          | (false, e) => AMinus e0 e
                          end)
                       es e,
             rest')
  end.

Definition parseAExp := parseSumExp.

(* begin hide *)
(** Parsing boolean expressions: *)
(* end hide *)
(** ブール式の構文解析 *)

Fixpoint parseAtomicExp (steps:nat)
                        (xs : list token)  :=
match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
     TRY ' (u,rest) <- expect "true" xs ;;
         SomeE (BTrue,rest)
     OR
     TRY ' (u,rest) <- expect "false" xs ;;
         SomeE (BFalse,rest)
     OR
     TRY ' (e,rest) <- firstExpect "~"
                                   (parseAtomicExp steps')
                                   xs ;;
         SomeE (BNot e, rest)
     OR
     TRY ' (e,rest) <- firstExpect "("
                                   (parseConjunctionExp steps')
                                   xs ;;
         ' (u,rest') <- expect ")" rest ;;
         SomeE (e, rest')
     OR
     ' (e, rest) <- parseProductExp steps' xs ;;
     TRY ' (e', rest') <- firstExpect "="
                                  (parseAExp steps') rest ;;
         SomeE (BEq e e', rest')
     OR
     TRY ' (e', rest') <- firstExpect "<="
                                      (parseAExp steps') rest ;;
         SomeE (BLe e e', rest')
     OR
     NoneE "Expected '=' or '<=' after arithmetic expression"
end

with parseConjunctionExp (steps:nat)
                         (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (e, rest) <- parseAtomicExp steps' xs ;;
    ' (es, rest') <- many (firstExpect "&&"
               (parseAtomicExp steps'))
            steps' rest ;;
    SomeE (fold_left BAnd es e, rest')
  end.

Definition parseBExp := parseConjunctionExp.

Check parseConjunctionExp.

Definition testParsing {X : Type}
           (p : nat ->
                list token ->
                optionE (X * list token))
           (s : string) :=
  let t := tokenize s in
  p 100 t.

(*
Eval compute in
  testParsing parseProductExp "x.y.(x.x).x".

Eval compute in
  testParsing parseConjunctionExp "~(x=x&&x*x<=(x*x)*x)&&x=x".
*)

(* begin hide *)
(** Parsing commands: *)
(* end hide *)
(** コマンドの構文解析 *)

Fixpoint parseSimpleCommand (steps:nat)
                            (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    TRY ' (u, rest) <- expect "SKIP" xs ;;
        SomeE (SKIP%imp, rest)
    OR
    TRY ' (e,rest) <-
            firstExpect "TEST"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "THEN"
                        (parseSequencedCommand steps') rest ;;
        ' (c',rest'') <-
            firstExpect "ELSE"
                        (parseSequencedCommand steps') rest' ;;
        ' (tt,rest''') <-
            expect "END" rest'' ;;
       SomeE(TEST e THEN c ELSE c' FI%imp, rest''')
    OR
    TRY ' (e,rest) <-
            firstExpect "WHILE"
                        (parseBExp steps') xs ;;
        ' (c,rest') <-
            firstExpect "DO"
                        (parseSequencedCommand steps') rest ;;
        ' (u,rest'') <-
            expect "END" rest' ;;
        SomeE(WHILE e DO c END%imp, rest'')
    OR
    TRY ' (i, rest) <- parseIdentifier xs ;;
        ' (e, rest') <- firstExpect "::=" (parseAExp steps') rest ;;
        SomeE ((i ::= e)%imp, rest')
    OR
        NoneE "Expecting a command"
end

with parseSequencedCommand (steps:nat)
                           (xs : list token) :=
  match steps with
  | 0 => NoneE "Too many recursive calls"
  | S steps' =>
    ' (c, rest) <- parseSimpleCommand steps' xs ;;
    TRY ' (c', rest') <-
            firstExpect ";;"
                        (parseSequencedCommand steps') rest ;;
        SomeE ((c ;; c')%imp, rest')
    OR
    SomeE (c, rest)
  end.

Definition bignumber := 1000.

Definition parse (str : string) : optionE com :=
  let tokens := tokenize str in
  match parseSequencedCommand bignumber tokens with
  | SomeE (c, []) => SomeE c
  | SomeE (_, t::_) => NoneE ("Trailing tokens remaining: " ++ t)
  | NoneE err => NoneE err
  end.

(* ################################################################# *)
(* begin hide *)
(** * Examples *)
(* end hide *)
(** * 例 *)

Example eg1 : parse "
  TEST x = y + 1 + 2 - y * 6 + 3 THEN
    x ::= x * 1;;
    y ::= 0
  ELSE
    SKIP
  END  "
=
  SomeE (
      TEST "x" = "y" + 1 + 2 - "y" * 6 + 3 THEN
        "x" ::= "x" * 1;;
        "y" ::= 0
      ELSE
        SKIP
      FI)%imp.
Proof. cbv. reflexivity. Qed.

Example eg2 : parse "
  SKIP;;
  z::=x*y*(x*x);;
  WHILE x=x DO
    TEST (z <= z*z) && ~(x = 2) THEN
      x ::= z;;
      y ::= z
    ELSE
      SKIP
    END;;
    SKIP
  END;;
  x::=z  "
=
  SomeE (
      SKIP;;
      "z" ::= "x" * "y" * ("x" * "x");;
      WHILE "x" = "x" DO
        TEST ("z" <= "z" * "z") && ~("x" = 2) THEN
          "x" ::= "z";;
          "y" ::= "z"
        ELSE
          SKIP
        FI;;
        SKIP
      END;;
      "x" ::= "z")%imp.
Proof. cbv. reflexivity. Qed.

(* Wed Jan 9 12:02:46 EST 2019 *)

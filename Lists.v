(** * Lists: 直積、リスト、オプション *)
(*
(** * Lists: Working with Structured Data *)
*)

Require Export Induction.
Module NatList.

(* ################################################################# *)
(*
(** * Pairs of Numbers *)
*)
(** * 数のペア *)

(*
(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one, as here: *)
*)
(** [Inductive] による型定義では、各構成子は任意の個数の引数を取ることができました。
    [true] や [O] のように引数のないもの、 [S] のようにひとつのもの、また、ふたつ以上の取るものも以下のように定義することができます。 *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(*
(** This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]." *)
*)
(** この定義は以下のように読めます。
    「数のペアを構成する方法がただひとつある。それは、構成子 [pair] を [nat] 型のふたつの引数に適用することである。」 *)

Check (pair 3 5).

(** Here are two simple functions for extracting the first and
    second components of a pair.  The definitions also illustrate how
    to do pattern matching on two-argument constructors. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(*
(** Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can tell Coq to allow this with a [Notation]
    declaration. *)
*)
(** ペアはよく使うものなので、 [pair x y] ではなく、数学の標準的な記法で [(x, y)] と書けるとよいでしょう。
    このような記法を使うためには [Notation] 宣言を使います。 *)

Notation "( x , y )" := (pair x y).

(*
(** The new pair notation can be used both in expressions and in
    pattern matches (indeed, we've actually seen this already in the
    previous chapter, in the definition of the [minus] function --
    this works because the pair notation is also provided as part of
    the standard library): *)
*)
(** こうして定義したペアの新しい記法（notation）は、式だけでなくパターンマッチに使うこともできます。
   （実際には、パターンマッチで使っている様子は既に[minus]関数を定義する際に見ています。
   この時点で動いていたのは、同じペアの記法が標準ライブラリの一部として提供されているからです。） *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(*
(** Let's try to prove a few simple facts about pairs.

    If we state things in a particular (and slightly peculiar) way, we
    can complete proofs with just reflexivity (and its built-in
    simplification): *)
*)
(** それでは、数のペアに関する簡単な事実をいくつか証明してみましょう。
 
    一定の（一種独特な）形式で書いておくと、単に reflexivity（と組み込みの簡約）だけで証明できます。 *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(*
(** But [reflexivity] is not enough if we state the lemma in a more
    natural way: *)
*)
(** しかし、補題を以下のようにより自然な書き方をした場合、[reflexivity]では足りません。 *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
  (* なにも変わらない！ *)
Abort.

(*
(** We have to expose the structure of [p] so that [simpl] can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct]. *)
*)
(** [simpl] で [fst] や [snd] の中のパターンマッチを実行できるよう、 [p] の構造を明らかにする必要があります。
    これには [destruct] を使います。 *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(*
(** Notice that, unlike its behavior with [nat]s, [destruct]
    generates just one subgoal here.  That's because [natprod]s can
    only be constructed in one way. *)
*)
(** [nat] の場合と異なり、 [destruct] でサブゴールが増えることはありません。
    これは、 [natprod] の構成法がひとつしかないからです。 *)

(*
(** **** Exercise: 1 star (snd_fst_is_swap)  *)
*)
(** **** 練習問題: ★ (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 1 star, optional (fst_swap_is_snd)  *)
*)
(** **** 練習問題: ★ (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(*
(** * Lists of Numbers *)
*)
(** * 数のリスト *)

(*
(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)
*)
(** ペアの定義を一般化することで、数の「リスト(_list_)」は次のように表すことができます。
    「リストは、空のリストであるか、または数と他のリストをペアにしたものである。」 *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(*
(** For example, here is a three-element list: *)
*)
(** たとえば、次の定義は要素が三つのリストです *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(*
(** As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)
*)
(** ペアの場合と同じく、リストをプログラミング言語で馴染んだ記法で書くことができると便利でしょう。
    次の宣言では [::] を中置の [cons] 演算子として使えるようにし、角括弧をリストを構成するための外置（outfix）記法として使えるようにしています。 *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(*
(** It is not necessary to understand the details of these
    declarations, but in case you are interested, here is roughly
    what's going on.  The [right associativity] annotation tells Coq
    how to parenthesize expressions involving several uses of [::] so
    that, for example, the next three declarations mean exactly the
    same thing: *)
*)
(** この宣言を詳細まで理解する必要はありませんが、興味のある読者のために簡単に説明しておきます。
    [right associativity] アノテーションは複数の [::] を使った式にどのように括弧を付けるか指示するものです。
    例えば、次の三つの宣言はすべて同じ意味に解釈されます。 *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(*
(** The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

   the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
   will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than [1
   + (2 :: [3])].

   (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
   you read them in a .v file.  The inner brackets, around 3, indicate
   a list, but the outer brackets, which are invisible in the HTML
   rendering, are there to instruct the "coqdoc" tool that the bracketed
   part should be displayed as Coq code rather than running text.)

   The second and third [Notation] declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. *)
*)
(** [at level 60] の部分は [::] を他の中置演算子といっしょに使っている式にどのように括弧を付けるかを指示するものです。
    例えば、 [+] を [plus] に対する level 50 の中置記法として定義したので、
[[
  Notation "x + y" := (plus x y) 
                      (at level 50, left associativity). 
]]
    [+] は [::] よりも強く結合し、 [1 + 2 :: [3]] は期待通り、 [1 + (2 :: [3])] ではなく [(1 + 2) :: [3]] と構文解析されます。
 
    （.v ファイルを読んでいるときには "[1 + 2 :: [3]]" のような書き方は少し読みにくいように感じるでしょう。
    内側の 3 の左右の角括弧はリストを表すものですが、外側の括弧は "coqdoc" 用の命令で、角括弧内の部分をそのままのテキストではなく Coq のコードとして表示するよう指示するものです。
    この角括弧は生成された HTML には現れません。）
 
    上の二番目と三番目の [Notation] 宣言は標準的なリストの記法を導入するためのものです。
    三番目の [Notation] の右辺は、 n 引数の記法を二項構成子の入れ子に変換する記法を定義するための Coq の構文の例です。 *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(*
(** A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)
*)
(** リストを操作するために便利な関数がいくつかあります。
    例えば、 [repeat] 関数は数 [n] と [count] を取り、各要素が [n] で長さ [count] のリストを返します。 *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(*
(** The [length] function calculates the length of a list. *)
*)
(** [length] 関数はリストの長さを計算します。 *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(*
(** The [app] function concatenates (appends) two lists. *)
*)
(** [app] 関数はふたつのリストを連結(append)します。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(*
(** Actually, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)
*)
(** [app] はこの後でよく使うので、中置演算子を用意しておくと便利でしょう。 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Head (with default) and Tail *)
*)
(** *** 先頭（デフォルト値付き）と後ろ *)

(*
(** Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first
    element (the "tail").
    Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.  *)
*)
(** もうふたつリストを使った例を見てみましょう。
    [hd] 関数はリストの最初の要素（先頭—— head）を返し、 [tl] は最初の要素を除いたもの（後ろ―― tail）を返します。
    空のリストには最初の要素はありませんから、その場合に返す値を引数として渡しておかなければなりません。 *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(*
(** *** Exercises *)
*)
(** *** 練習問題 *)

(*
(** **** Exercise: 2 stars, recommended (list_funs)  *)
*)
(** **** 練習問題: ★★, recommended (list_funs) *)
(*
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)
*)
(** 以下の [nonzeros]、 [oddmembers]、 [countoddmembers] の定義を完成させなさい。
    どのように動くかは続くテストから考えてください。 *)

Fixpoint nonzeros (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* FILL IN HERE *) Admitted.

Definition countoddmembers (l:natlist) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars, advanced (alternate)  *)
*)
(** **** 練習問題: ★★★, advanced (alternate) *)
(*
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)
*)
(** [alternate] の定義を完成させなさい。
    この関数は、ふたつのリストから交互に要素を取り出しひとつに「綴じ合わせる」関数です。
    具体的な例は下のテストを見てください。
 
    注意: [alternate] の自然な定義のひとつは、 Coq の要求する「[Fixpoint] による定義は『明らかに停止する』ものでなければならない」という性質を満たすことができません。
    このパターンにはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長な方法を探してみてください。
    （新しい対の定義を必要とする解法もありますが、それ以外にもあります。） *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* FILL IN HERE *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(*
(** *** Bags via Lists *)
*)
(** *** リストを使ったバッグ *)

(*
(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    implementation is to represent a bag of numbers as a list. *)
*)
(** バッグ（[bag]、または多重集合—— [multiset]）は集合のようなものですが、それぞれの要素が一度きりではなく複数回現れることのできるようなものを言います。
    バッグの実装としてありうるのは数のバッグをリストで表現するというものでしょう。 *)

Definition bag := natlist.

(*
(** **** Exercise: 3 stars, recommended (bag_functions)  *)
*)
(** **** 練習問題: ★★★, recommended (bag_functions) *)
(*
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)
*)
(** バッグに対する [count]、 [sum]、 [add]、 [member] 関数の定義を完成させなさい。 *)

Fixpoint count (v:nat) (s:bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(*
(** All these proofs can be done just by [reflexivity]. *)
*)
(** 下の証明はすべて [reflexivity] だけでできます。 *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

(*
(** Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)
*)
(** 多重集合の [sum] （直和、または非交和）は集合の [union] （和）と同じようなものです。
    [sum a b] は [a] と [b] の両方の要素を持つ多重集合です。
    （数学者は通常、多重集合の [union] にもう少し異なる定義を与えます。それが、この関数の名前を [union] にしなかった理由です。）
    [sum] のヘッダには引数の名前を与えませんでした。
    さらに、 [Fixpoint] ではなく [Definition] を使っています。
    ですから、引数に名前がついていたとしても再帰的な処理はできません。
    問題をこのように設定したのは、 [sum] を（定義済みの関数を使うといった）別の方法で定義できないか考えさせるためです。 *)

Definition sum : bag -> bag -> bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars, optional (bag_more_functions)  *)
*)
(** **** 練習問題: ★★★, optional (bag_more_functions) *)
(*
(** Here are some more bag functions for you to practice with. *)
*)
(** 練習として、さらにいくつかの関数を作成してください。 *)

(*
(** When remove_one is applied to a bag without the number to remove,
   it should return the same bag unchanged. *)
*)
(** [remove_one] を削除しようとしている数のないバッグに適用した場合は、同じバッグを変更せずに返す。 *)

Fixpoint remove_one (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* FILL IN HERE *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars, recommendedM (bag_theorem)  *)
*)
(** **** 練習問題: ★★★, recommended (bag_theorem) *)
(*
(** Write down an interesting theorem [bag_theorem] about bags
    involving the functions [count] and [add], and prove it.  Note
    that, since this problem is somewhat open-ended, it's possible
    that you may come up with a theorem which is true, but whose proof
    requires techniques you haven't learned yet.  Feel free to ask for
    help if you get stuck! *)
*)
(** [count] や [add] を使ったバッグに関する面白い定理を書き、それを証明しなさい。
    この問題はいわゆる自由課題で、真であっても、証明にまだ習っていない技法を使わなければならない定理を思いついてしまうかもしれません。
    証明に行き詰まってしまったら気軽に質問してください。 *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)

(** [] *)

(* ################################################################# *)
(*
(** * Reasoning About Lists *)
*)
(** * リストに関する推論 *)

(*
(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)
*)
(** 数の場合と同じく、リスト処理関数についての簡単な事実はもっぱら簡約のみで証明できることがあります。
    たとえば、次の定理は [reflexivity] で行われる簡約だけで証明できます。 *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(*
(** ... because the [[]] is substituted into the
    "scrutinee" (the value being "scrutinized" by the match) in the
    definition of [app], allowing the match itself to be
    simplified. *)
*)
(** これは、 [[]] が [app] の定義における「被検査体(scrutinee)」（パターンマッチで「検査(scrutinize)」される式/訳注：matchの直後に書いた式）に代入され、パターンマッチが簡約できるようになるからです。 *)
(* 訳注：scrutineeはあまり見ない語だが、Scalaでは使っているようだ。なお、他の部分から推測するとscrutineeは式であって値ではないはず。 *)

(*
(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)
*)
(** またこれも数の場合と同じように、未知のリストの形（空であるかどうか）に応じた場合分けも有効です。 *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(*
(** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)
*)
(** ここで、 [nil] の場合がうまく行くのは、 [tl nil = nil] と定義したからです。
    ここでは、 [destruct] タクティックの [as] で [n] と [l'] のふたつの名前を導入しました。
    これは、リストの [cons] 構成子が引数をふたつ（構成するリストの頭部と尾部）取ることに対応しています。 *)

(*
(** Usually, though, interesting theorems about lists require
    induction for their proofs. *)
*)
(** ただし、リストに関する興味深い定理の証明には、帰納法が必要になるのが普通です。 *)

(* ----------------------------------------------------------------- *)
(*
(** *** Micro-Sermon *)
*)
(** *** お小言 *)

(*
(** Simply reading example proof scripts will not get you very far!
    It is important to work through the details of each one, using Coq
    and thinking about what each step achieves.  Otherwise it is more
    or less guaranteed that the exercises will make no sense when you
    get to them.  'Nuff said. *)
*)
(** 単に例題の証明を読んでいるだけでは大きな進歩は望めません！
    各証明を実際に Coq で動かし、各ステップがその証明にどのようにかかわっているか考え、道筋をていねいになぞっていくことが大切です。
    そうしなければ、演習に取り組んでも何の意味もありません。
    お小言終わり。 *)
(* 訳注：'Nuff said = Enough said もう十分だ、これ以上言うな、などの意味だが自分で言ってるからよくわからない。 *)

(* ================================================================= *)
(*
(** ** Induction on Lists *)
*)
(** ** リスト上の帰納法 *)

(*
(** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either [true] or [false]; a number
    can be either [O] or [S] applied to another number; a list can be
    either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)
*)
(** [natlist] のようなデータ型に対して帰納法で証明をするのは、普通の自然数に対する帰納法よりも馴染みにくさを感じたことでしょう。
    しかし、考え方は同様に単純です。
    [Inductive] 宣言では、宣言した構成子を使って構築できる値の集合を定義しています。
    例えば、ブール値では [true] と [false] のいずれかであり、数では [O] か数に対する [S] のいずれか、リストであれば [nil] か数とリストに対する [cons] のいずれかです。
 
    さらに言えば、帰納的に定義された集合の要素になるのは、宣言した構成子を互いに適用したものだけです。
    このことがそのまま帰納的に定義された集合に関する推論の方法になります。
    すなわち、数は [O] であるか、より小さい数に [S] を適用したものであるかのいずれかです。
    リストは [nil] であるか、何らかの数とより小さいリストに [cons] を適用したものです。
    他のものも同様です。
    ですから、あるリスト [l] に関する命題 [P] があり、 [P] がすべてのリストに対して成り立つことを示したい場合には、次のように推論します。
 
      - まず、 [l] が [nil] のとき [P] が [l] について成り立つことを示す。
 
      - それから、 [l] が [cons n l'] であるとき、ある数 [n] とより小さいリスト [l'] に対して、 [P] が [l'] について成り立つと仮定すれば [P] が [l] についても成り立つことを示す。
 
    大きなリストはそれより小さなリストからのみ作り出され、少しずつ [nil] に近付いて行きます。
    よって、このふたつの言明からすべてのリスト [l] に関して [P] が真であることが言えます。
    具体的な例で説明しましょう。 *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(*
(** Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case. Once again, this Coq proof is not especially
    illuminating as a static written document -- it is easy to see
    what's going on if you are reading the proof in an interactive Coq
    session and you can see the current goal and context at each
    point, but this state is not visible in the written-down parts of
    the Coq proof.  So a natural-language proof -- one written for
    human readers -- will need to include more explicit signposts; in
    particular, it will help the reader stay oriented if we remind
    them exactly what the induction hypothesis is in the second
    case. *)
*)
(** 自然数上の帰納法と同様に、[induction]タクティックでの[as ...]節は[cons]の場合の残りのリストに[l1']と名前を付けるために使われています。
    蒸し返すようですが、この Coq の証明はこうして単に静的なテキストとして読んでいる限り、さほど明白で分かりやすいものではありません。
    Coq の証明は、 Coq を対話的に動かしながらポイントごとに「現在のゴールは何か」「コンテキストに何が出ているか」を見て、証明が今どうなっているかを読み下していくことで理解されるようになっています。
    しかし、このような証明の途中経過は、全てが証明結果として書き出されるわけではありません。
    だからこそ、人間向けの自然言語での証明には証明の筋道がわかるように証明の指針を書いておく必要があるのです。
    特に、読者が流れを見失わないよう、ふたつめの場合分けで使う帰納法の仮定が何だったのかわかるようにしておくのは有益なはずです。 *)

(** For comparison, here is an informal proof of the same theorem. *)

(*
(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)
*)
(** 定理: 任意のリスト [l1]、 [l2]、 [l3] について、
    [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]
    が成り立つ。
 
    証明: [l1] についての帰納法で証明する
 
    - まず、 [l1 = []] と仮定して
[[
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3) 
]]
     を示す。これは [++] の定義から自明である。
 
   - 次に [l1 = n::l1'] かつ
[[
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3) 
]]
     （帰納法の仮定）と仮定して
[[
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3) 
]]
     を示す。 [++] の定義から、この式は以下のように変形できる。
[[
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)) 
]]
     これは帰納法の仮定から直接導かれる。  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing function
    [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [rev] *)

(*
(** Now let's prove some theorems about our newly defined [rev].
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case... *)
*)
(** 新しく定義した [rev] に関する定理を証明してみましょう。
    ここまで見てきたものよりも難易度の高いものですが、リストを反転しても長さの変わらないことを証明します。
    下の方法では、ふたつめの場合分けで行き詰まってしまいます。 *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    (* ここで行き詰まる。ゴールは [++] に関する等式だが、
       コンテキスト中にも大域環境中にも使えそうな等式はない。
       帰納法の仮定を使って少しだけ進めることもできはする。 *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
    (* が、ここで何もできなくなる。 *)
Abort.

(*
(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and prove it as a separate
    lemma. *)
*)
(** この [++] と [length] に関する等式が成り立つことを示せれば証明が先に進むはずです。
    この式を取り出して別個の補題として証明してみましょう。 *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(*
(** Now we can complete the original proof. *)
*)
(** これで、元々の証明ができるようになりました。 *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(*
(** For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show

        length ([] ++ l2) = length [] + length l2,

      which follows directly from the definitions of
      [length] and [++].

    - Next, suppose [l1 = n::l1'], with

        length (l1' ++ l2) = length l1' + length l2.

      We must show

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)
*)
(** 対比として、この二つの定理の非形式的な証明を見てみましょう
 
    定理: 二つのリスト [l1] と [l2] について、 [length (l1 ++ l2) = length l1 + length l2] が成り立つ。
 
    証明: [l1] についての帰納法で証明する。
 
    - まず、 [l1 = []] と仮定して
[[
        length ([] ++ l2) = length [] + length l2 
]]
      を示す。これは [length] と [++] の定義から直接導かれる。
 
    - 次に、 [l1 = n::l1'] かつ
[[
        length (l1' ++ l2) = length l1' + length l2 
]]
      と仮定して、
[[
        length ((n::l1') ++ l2) = length (n::l1') + length l2) 
]]
      を示す。これは [length] と [++] の定義および帰納法の仮定から明らかである。 [] *)

(*
(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show

          length (rev []) = length [],

        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with

          length (rev l') = length l'.

        We must show

          length (rev (n :: l')) = length (n :: l').

        By the definition of [rev], this follows from

          length ((rev l') ++ [n]) = S (length l')

        which, by the previous lemma, is the same as

          length (rev l') + length [n] = S (length l').

        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)
*)
(** 定理: 任意のリスト [l] について [length (rev l) = length l] が成り立つ。
 
    証明: [l] についての帰納法で証明する。
 
      - まず、 [l = []] と仮定して
[[
          length (rev []) = length [] 
]]
        を示す。これは [length] と [rev] の定義から直接導かれる
 
      - 次に、 [l = n::l'] かつ
[[
          length (rev l') = length l' 
]]
        と仮定して、
[[
          length (rev (n :: l')) = length (n :: l') 
]]
        を示す。 [rev] の定義から次のように変形できる。
[[
          length ((rev l') ++ [n]) = S (length l') 
]]
        これは、先程の補題から、次のものと同じである。
[[
          length (rev l') + length [n] = S (length l') 
]]
        これは、[length] の定義および帰納法の仮定から明らかである。 [] *)

(*
(** The style of these proofs is rather longwinded and pedantic.
    After the first few, we might find it easier to follow proofs that
    give fewer details (which can easily work out in our own minds or
    on scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    like this: *)
*)
(** こういった証明のスタイルは、長ったらしく杓子定規な感じがします。
    最初の何回かは別にして、それ以後は、細かいところは省略してしまって（必要なら頭の中や紙の上で追うのは簡単ですから）、自明でないところにだけ注目した方がわかりやすいでしょう。
    そのように省略がちに書けば、上の証明は次のようになります。 *)

(*
(** _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l] (this follows by a straightforward induction on [l]).
     The main property again follows by induction on [l], using the
     observation together with the induction hypothesis in the case
     where [l = n'::l']. [] *)
*)
(** 定理:
     任意のリスト [l] について [length (rev l) = length l] が成り立つ。
 
    証明: まず、任意の [l] について [length (l ++ [n]) = S (length l)] であることに注目する（これは [l] についての帰納法から自明である）。
     もとの性質については、 [l] についての帰納法から示し、 [l = n'::l'] の場合については、上の性質と帰納法の仮定から導かれる。 [] *)

(*
(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for our
    present purposes. *)
*)
(** どちらのスタイルの方が好ましいかは、読み手の証明への馴れや、彼らが今まで触れてきた証明がどちらに近いかに依ります。
    本書の目的としては冗長なスタイルの方が無難でしょう。 *)

(* ================================================================= *)
(** ** [Search] *)

(*
(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Typing
    [Search foo] will cause Coq to display a list of all theorems
    involving [foo].  For example, try uncommenting the following line
    to see a list of theorems that we have proved about [rev]: *)
*)
(** これまで見てきたように、定理を証明するには既に証明した定理を、例えば[rewrite]を通じて、使うことができます。
    しかし、定理を使うためにはその名前を知らなければなりません！
    使えそうな定理の名前をすべて覚えておくのはとても大変です。
    今まで証明した定理を覚えておくだけでも大変なのに、その名前となったら尚更です。
 
    Coq の [Search] コマンドはこのような場合にとても便利です。
    [Search foo] とすると、 [foo] に関する証明がすべて表示されます。
    例えば、次の部分のコメントを外せば、これまで [rev] に関して証明した定理が表示されます。 *)

(*  Search rev. *)
(** Search rev. *)

(*
(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    If you are using ProofGeneral, you can run [Search] with [C-c
    C-a C-a]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)
*)
(** 続く練習問題に取り組む際や読み進める際には、常に [Search] コマンドのことを頭の隅に置いておくといいでしょう。
    そうすることでずいぶん時間の節約ができるはずです。
 
    もし ProofGeneral を使っているのなら、 [C-c C-a C-a] とキー入力をすることで [Search] コマンドを使うことができます。
    その結果をエディタに貼り付けるには [C-c C-;] を使うことができます。 *)

(* ================================================================= *)
(*
(** ** List Exercises, Part 1 *)
*)
(** ** リストについての練習問題 (1) *)

(*
(** **** Exercise: 3 starsM (list_exercises)  *)
*)
(** **** 練習問題: ★★★ (list_exercises) *)
(*
(** More practice with lists: *)
*)
(** リストについてさらに練習しましょう。 *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

(*
(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)
*)
(** 次の問題には簡単な解法があります。
    こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。 *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

(*
(** An exercise about your implementation of [nonzeros]: *)
*)
(** 前に書いた [nonzeros] 関数に関する練習問題です。 *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (beq_natlist)  *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(*
(** ** List Exercises, Part 2 *)
*)
(** ** リストについての練習問題 (2) *)

(*
(** **** Exercise: 3 stars, advanced (bag_proofs)  *)
*)
(** **** 練習問題: ★★★, advanced (bag_proofs) *)
(*
(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)
*)
(** 上で見たバッグについて、以下の定理を証明しなさい。 *)

Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(*
(** The following lemma about [leb] might help you in the next proof. *)
*)
(** 以下の [leb] に関する補題は、この次の証明に使えるかもしれません。 *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 3 stars, optionalM (bag_count_sum)  *)
*)
(** **** 練習問題: ★★★, optional (bag_count_sum) *)
(*
(** Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it.  (You may
    find that the difficulty of the proof depends on how you defined
    [count]!) *)
*)
(** バッグについて [count] と [sum] を使った定理を考え、それを証明しなさい。
    （[count]の定義によって証明の難易度が変わるかもしれません。） *)
(* FILL IN HERE *)
(** [] *)

(*
(** **** Exercise: 4 stars, advancedM (rev_injective)  *)
*)
(** **** 練習問題: ★★★★, advanced (rev_injective) *)
(*
(** Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(There is a hard way and an easy way to do this.) *)
*)
(** [rev] 関数が単射である、すなわち
[[
    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2 
]]
であることを証明しなさい。
 
（この練習問題には簡単な解法と難しい解法があります。） *)

(* FILL IN HERE *)
(** [] *)

(* ################################################################# *)
(*
(** * Options *)
*)
(** * オプション *)

(** Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(*
(** (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)
*)
(** （HTML版では上の例での証明部分の常套句が消えています。
    もし見たければ直後の四角をクリックしてください。）
 
    この機会に、 Coq のプログラミング言語としての機能として、条件式を紹介しておきましょう。 *)


Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(*
(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually supports conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)
*)
(** Coq の条件式（if式）は他の言語に見られるものとほとんど同じですが、少しだけ一般化されています。
    Coq には 組み込みのブーリアン型がないため、 Coq の条件式では、実際には、構成子のふたつある任意の帰納型に対する分岐ができます。
    条件部の式が [Inductive] の定義の最初の構成子に評価された場合には真、ふたつめの構成子に評価された場合には偽と見做されます。 *)

(*
(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)
*)
(** 次の関数は、 [natoption] 型から [nat] の値を取り出し、 [None] の場合には与えられたデフォルト値を返します。 *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(*
(** **** Exercise: 2 stars (hd_error)  *)
*)
(** **** 練習問題: ★★ (hd_error)  *)
(*
(** Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)
*)
(** 同じ考え方を使って、以前定義した [hd] 関数を修正し、 [nil] の場合に返す値を渡さなくて済むようにしなさい。 *)

Definition hd_error (l : natlist) : natoption
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 1 star, optional (option_elim_hd)  *)
*)
(** **** 練習問題: ★, optional (option_elim_hd) *)
(*
(** This exercise relates your new [hd_error] to the old [hd]. *)
*)
(** 新しい [hd_error] と古い [hd] の関係についての練習問題です。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id : nat -> id.

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish.

    We'll also need an equality test for [id]s: *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Exercise: 1 star (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(*
(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or by applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)
*)
(** この宣言は次のように読めます。
    「[partial_map] を構成する方法はふたつある。
      構成子 [empty] で空の部分写像を表現するか、構成子 [record] をキーと値と既存の [partial_map] に適用してキーと値の対応を追加した [partial_map] を構成するかのいずれかである。」 *)

(** The [update] function overrides the entry for a given key in a
    partial map (or adds a new entry if the given key is not already
    present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(*
(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)
*)
(** 最後に、 [find] 関数は、 [partial_map] から与えられたキーに対応する値を探し出すものです。
    キーが見つからなかった場合には [None] を返し、キーが [val] に結び付けられていた場合には [Some val] を返します。
    同じキーが複数の値に結び付けられている場合には、最初に見つけた値を返します。 *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.


(** **** Exercise: 1 star (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)
End PartialMap.

(** **** Exercise: 2 starsM (baz_num_elts)  *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?  (Answer in English
    or the natural language of your choice.)

(* FILL IN HERE *)
*)
(** [] *)

(** $Date: 2016-12-17 23:53:20 -0500 (Sat, 17 Dec 2016) $ *)


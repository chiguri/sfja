(** * Poly:多相性と高階関数 *)
(* begin hide *)
(** * Poly: Polymorphism and Higher-Order Functions *)
(* end hide *)

(* Final reminder: Please do not put solutions to the exercises in
   publicly accessible places.  Thank you!! *)
(* 最後にもう一度：誰でも見える場所に課題の答えを置かないでください。
   よろしくお願いします。 *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

(* ################################################################# *)
(* begin hide *)
(** * Polymorphism *)
(* end hide *)
(** * ポリモルフィズム（多相性）(Polymorphism) *)

(* begin hide *)
(** In this chapter we continue our development of basic
    concepts of functional programming.  The critical new ideas are
    _polymorphism_ (abstracting functions over the types of the data
    they manipulate) and _higher-order functions_ (treating functions
    as data).  We begin with polymorphism. *)
(* end hide *)
(** この章では、関数型プログラミングの基本的なコンセプトを進めていきます。
    特に重要な新しいアイディアは、「多相性(_polymorphism_)」（関数が扱うデータの型に関する抽象化）と「高階関数(_higher-order function_)」（関数のデータとしての取り扱い）です。
    まず多相性から始めましょう。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Polymorphic Lists *)
(* end hide *)
(** ** 多相的なリスト *)

(* begin hide *)
(** For the last couple of chapters, we've been working just
    with lists of numbers.  Obviously, interesting programs also need
    to be able to manipulate lists with elements from other types --
    lists of strings, lists of booleans, lists of lists, etc.  We
    _could_ just define a new inductive datatype for each of these,
    for example... *)
(* end hide *)
(** ここまでは、数値のリストについて学んできました。
    もちろん、数値以外の、文字列、ブール値、リストといったものを要素として持つリストを扱えるプログラムは、より興味深いものとなるでしょう。
    これまで学んできたことだけでも、実は新しい帰納的なデータ型を作ることはできるのです。
    例えば次のように... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(* begin hide *)
(** ... but this would quickly become tedious, partly because we
    have to make up different constructor names for each datatype, but
    mostly because we would also need to define new versions of all
    our list manipulating functions ([length], [rev], etc.) for each
    new datatype definition. *)
(* end hide *)
(** ... しかし、こんなことをやっていると、すぐに嫌になってしまうでしょう。
    その理由の一つは、データ型ごとに違ったコンストラクタの名前をつけなければならないことですが、もっと大変なのは、こういったリストを扱う関数（[length]、[rev]など）を、新しく対応した型ごとに作る必要が出てくることです。 *)

(* begin hide *)
(** To avoid all this repetition, Coq supports _polymorphic_
    inductive type definitions.  For example, here is a _polymorphic
    list_ datatype. *)
(* end hide *)
(** この無駄な繰り返し作業を無くすため、Coqは多相的な帰納的データ型の定義をサポートしています。
    これを使うと、多相的なリストは以下のように書くことができます。 *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(* begin hide *)
(** This is exactly like the definition of [natlist] from the
    previous chapter, except that the [nat] argument to the [cons]
    constructor has been replaced by an arbitrary type [X], a binding
    for [X] has been added to the header, and the occurrences of
    [natlist] in the types of the constructors have been replaced by
    [list X].  (We can re-use the constructor names [nil] and [cons]
    because the earlier definition of [natlist] was inside of a
    [Module] definition that is now out of scope.)

    What sort of thing is [list] itself?  One good way to think
    about it is that [list] is a _function_ from [Type]s to
    [Inductive] definitions; or, to put it another way, [list] is a
    function from [Type]s to [Type]s.  For any particular type [X],
    the type [list X] is an [Inductive]ly defined set of lists whose
    elements are of type [X]. *)
(* end hide *)
(** これは、前の章にある[natlist]の定義とほとんどそっくりですが、コンストラクタ[cons]の引数の型が[nat]であったのに対し、任意の型を表す[X]がそれに変わっています。
    この[X]はヘッダに加えられた[X]と結びつけられ、さらに[natlist]であったものが[list X]に置き換わっています。
    （ここで、コンストラクタに[nil]や[cons]といった名前を付けられるのは、最初に定義した[natlist]が[Module]の中で定義されていて、ここからはスコープの外になっているからです。）
 
    それでは、[list]とはいったい何なのか、ということを正確に考えて見ましょう。
    これを考える一つの手がかりは、リストが「型を引数にとり、帰納的な定義を返す関数である」と考えることです。
    あるいは「型を引数にとり、型を返す関数」と考えてもいいかもしれません。
    任意の型[X]について、[list X]という型は、帰納的に定義されたリストの集合で、その要素の型が[X]となっているものと考えることもできます。*)

Check list.
(* ===> list : Type -> Type *)

(* begin hide *)
(** The parameter [X] in the definition of [list] automatically
    becomes a parameter to the constructors [nil] and [cons] -- that
    is, [nil] and [cons] are now polymorphic constructors; when we use
    them, we must now provide a first argument that is the type of the
    list they are building. For example, [nil nat] constructs the
    empty list of type [nat]. *)
(* end hide *)
(** 定義中の[list]のパラメータ[X]はコンストラクタである[nil]や[cons]の引数にもなります。
    つまり、[nil]も[cons]も多相的なコンストラクタになっているということです。
    コンストラクタの使用時には、何のリストを作るかを第一引数として与える必要があります。
    例えば、[nil nat]は[nat]の空リストを構成します。 *)

Check (nil nat).
(* ===> nil nat : list nat *)

(** Similarly, [cons nat] adds an element of type [nat] to a list of
    type [list nat]. Here is an example of forming a list containing
    just the natural number 3. *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

(** What might the type of [nil] be? We can read off the type [list X]
    from the definition, but this omits the binding for [X] which is
    the parameter to [list]. [Type -> list X] does not explain the
    meaning of [X]. [(X : Type) -> list X] comes closer. Coq's
    notation for this situation is [forall X : Type, list X]. *)

Check nil.
(* ===> nil : forall X : Type, list X *)

(** Similarly, the type of [cons] from the definition looks like
    [X -> list X -> list X], but using this convention to explain the
    meaning of [X] results in the type [forall X, X -> list X -> list
    X]. *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** (Side note on notation: In .v files, the "forall" quantifier
    is spelled out in letters.  In the generated HTML files and in the
    way various IDEs show .v files (with certain settings of their
    display controls), [forall] is usually typeset as the usual
    mathematical "upside down A," but you'll still see the spelled-out
    "forall" in a few places.  This is just a quirk of typesetting:
    there is no difference in meaning.) *)

(* begin hide *)
(** Having to supply a type argument for each use of a list
    constructor may seem an awkward burden, but we will soon see
    ways of reducing that burden. *)
(* end hide *)
(** リストのコンストラクタに毎回型引数を与えることは無駄な手間だと感じるかもしれません。
    すぐにこれを回避する方法について見ていきます。 *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(* begin hide *)
(** (We've written [nil] and [cons] explicitly here because we haven't
    yet defined the [ [] ] and [::] notations for the new version of
    lists.  We'll do that in a bit.) *)
(* end hide *)
(** （ここでは[nil]や[cons]を明示的に記述していますが、それは我々がまだ[[]]や[::]の表記法(notation)をまだ定義していないからです。
    この後でやります） *)

(* begin hide *)
(** We can now go back and make polymorphic versions of all the
    list-processing functions that we wrote before.  Here is [repeat],
    for example: *)
(* end hide *)
(** それでは少し話を戻して、以前書いたリスト処理関数を多相版に作り直していきましょう。
    [repeat]関数は以下のようになります。 *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** As with [nil] and [cons], we can use [repeat] by applying it
    first to a type and then to an element of this type (and a number): *)
(** [nil]や[cons]と同様に、[repeat]も型を最初に適用してからその型の要素（そして続いて数）に適用できます。 *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

(* begin hide *)
(** To use [repeat] to build other kinds of lists, we simply
    instantiate it with an appropriate type parameter: *)
(* end hide *)
(** この[repeat]を別の型のリストに使いたい場合は、適切な型を与えるだけで済みます。 *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.


(* begin hide *)
(** **** Exercise: 2 stars, standard (mumble_grumble)  

    Consider the following two inductively defined types. *)
(* end hide *)
(** **** 練習問題: ★★, standard (mumble_grumble)
 
    以下の2つの帰納的に定義された型を考える。 *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* begin hide *)
(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]  *)
(* end hide *)
(** 以下の項の中から、型が[grumble X]の形で付けられるものを選びなさい。
    （「はい」か「いいえ」を各行に追加しなさい）
      - [d (b a 5)] 
      - [d mumble (b a 5)] 
      - [d bool (b a 5)] 
      - [e bool true] 
      - [e mumble (b c 0)] 
      - [e bool (b c 0)] 
      - [c]   *)
(* FILL IN HERE *)
End MumbleGrumble.

(* Do not modify the following line: *)
Definition manual_grade_for_mumble_grumble : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Type Annotation Inference *)
(* end hide *)
(** *** 型注釈推論 *)

(* begin hide *)
(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)
(* end hide *)
(** それでは、[repeat]関数の定義をもう一度書いてみましょう。
    ただし今回は、引数の型を指定しないでおきます。
    Coqはこれを受け入れてくれるでしょうか？ *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* begin hide *)
(** Indeed it will.  Let's see what type Coq has assigned to [repeat']: *)
(* end hide *)
(** うまくいったようです。
    Coqが[repeat']にどのような型を設定したのか確認してみましょう。 *)

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(* begin hide *)
(** It has exactly the same type as [repeat].  Coq was able
    to use _type inference_ to deduce what the types of [X], [x], and
    [count] must be, based on how they are used.  For example, since
    [X] is used as an argument to [cons], it must be a [Type], since
    [cons] expects a [Type] as its first argument; matching [count]
    with [0] and [S] means it must be a [nat]; and so on.

    This powerful facility means we don't always have to write
    explicit type annotations everywhere, although explicit type
    annotations are still quite useful as documentation and sanity
    checks, so we will continue to use them most of the time.  You
    should try to find a balance in your own code between too many
    type annotations (which can clutter and distract) and too
    few (which forces readers to perform type inference in their heads
    in order to understand your code). *)
(* end hide *)
(** 両者は全く同じ型であることが分かります。
    Coqは「型推論(_type inference_)」という機構を持っていて、これを使い、[X]と[x]と[count]の型が何であるべきかを、その使われ方から導き出します。
    例えば、[X]が[cons]の最初の引数として使われたことがあれば、[cons]が最初の引数として[Type]を期待しているのでそれに違いありません。
    さらに[count]が[0]や[S]とマッチされているので、それは[nat]に違いない、といった具合です。
 
    このパワフルな機構の存在は、型情報を常にそこら中に書かなければならないわけではない、ということを意味します。
    しかし、型を明示的に書くことは、ドキュメントとして、または整合性を確かめるという点で意味があるので、以降もほとんどは型を書いていきます。
    これからは自分の書くコードで、型指定を書くところ、書かないところのバランスを考えていく必要があります（多すぎればコードが目障りな型指定で読みにくくなりますし、少なすぎるとプログラムを読む人に型推論させなければならなくなります）。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Type Argument Synthesis *)
(* end hide *)
(** *** 型引数の構成（Synthesis） *)

(* begin hide *)
(** To use a polymorphic function, we need to pass it one or
    more types in addition to its other arguments.  For example, the
    recursive call in the body of the [repeat] function above must
    pass along the type [X].  But since the second argument to
    [repeat] is an element of [X], it seems entirely obvious that the
    first argument can only be [X] -- why should we have to write it
    explicitly?

    Fortunately, Coq permits us to avoid this kind of redundancy.  In
    place of any type argument we can write a "hole" [_], which can be
    read as "Please try to figure out for yourself what belongs here."
    More precisely, when Coq encounters a [_], it will attempt to
    _unify_ all locally available information -- the type of the
    function being applied, the types of the other arguments, and the
    type expected by the context in which the application appears --
    to determine what concrete type should replace the [_].

    This may sound similar to type annotation inference -- indeed, the
    two procedures rely on the same underlying mechanisms.  Instead of
    simply omitting the types of some arguments to a function, like

      repeat' X x count : list X :=

    we can also replace the types with [_]

      repeat' (X : _) (x : _) (count : _) : list X :=

    to tell Coq to attempt to infer the missing information.

    Using holes, the [repeat] function can be written like this: *)
(* end hide *)
(** 多相的な関数を使うには、通常の引数に加えて型を一つ以上渡さなければなりません。
    例えば、[repeat]関数内での再帰呼び出しには、型[X]として渡されたものをそのまま渡すことになります。
    しかし[repeat]の二つ目の引数が[X]型である以上、最初の引数は明らかに[X]以外あり得ないのではないか、とも考えられます。
    それならばなぜわざわざそれを書く必要があるのでしょう。
 
    幸いなことに、Coqではこの種の冗長性を避けることができます。
    型を引数に渡すところではどこでも「穴(hole)」[_]を書くことができるのです。
    これは「ここにあるべきものを見つけてください」という意味です。
    もう少し正確に言うと、Coqが[_]を見つけると、手近に集められる情報を集めて「単一化(_unify_)」します。
    集められる情報は、適用されている関数の型や、その適用が現れている文脈から予想される型などですが、それを使って[_]と置き換えるべき具体的な型を決定するのです。
 
    これを聞くと、型推論と同じじゃないかと思われるかもしれません。
    実際、この二つの機能は水面下にあるメカニズムではつながっています。
    次のように単に引数の型を省略する代わりに
[[
      repeat' X x count : list X := 
]]
    このように、型を[_]で書くことができるということです。
[[
      repeat' (X : _) (x : _) (count : _) : list X := 
]]
    いずれも、Coqに、欠落している情報を推論させるもので、ちょうど引数を構成することに相当します。
 
    穴を使うと、[repeat]関数は以下のように書けます。 *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* begin hide *)
(** In this instance, we don't save much by writing [_] instead of
    [X].  But in many cases the difference in both keystrokes and
    readability is nontrivial.  For example, suppose we want to write
    down a list containing the numbers [1], [2], and [3].  Instead of
    writing this... *)
(* end hide *)
(** この例では、[X]を[_]に省略することをあまりしていません。
    しかし多くの場合、入力の容易さと読みやすさの両方で違いが現れます。
    例えば、[1],[2],[3]の三つの数値を保持するリストを書きたい場合を考えてみましょう。
    以下のように書く代わりに... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(* begin hide *)
(** ...we can use holes to write this: *)
(* end hide *)
(** ...穴を使って以下のように書くことができます。 *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Implicit Arguments *)
(* end hide *)
(** *** 暗黙の引数 *)

(* begin hide *)
(** We can go further and even avoid writing [_]'s in most cases by
    telling Coq _always_ to infer the type argument(s) of a given
    function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists its argument names, with curly braces
    around any arguments to be treated as implicit.  (If some
    arguments of a definition don't have a name, as is often the case
    for constructors, they can be marked with a wildcard pattern
    [_].) *)
(* end hide *)
(** さらに先に進めて、プログラムにほとんど[_]を書かなくてすむように、特定の関数の引数については「常に」型推論するよう指定できます。
 
    [Arguments]命令は関数（や構成子）に対し、引数の名前を波括弧で覆うことで暗黙のものとすることができます。
    （構成子でよく起こるのですが、もし名前がない変数を暗黙にしたい場合はワイルドカードパターンとして[_]を指定します。） *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** Now, we don't have to supply type arguments at all: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* begin hide *)
(** Alternatively, we can declare an argument to be implicit
    when defining the function itself, by surrounding it in curly
    braces instead of parens.  For example: *)
(* end hide *)
(** また、関数定義の中で、引数を暗黙のものにすることもできます。
    その際は、次のように引数を丸括弧の代わりに波括弧で囲みます。 *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(* begin hide *)
(** (Note that we didn't even have to provide a type argument to the
    recursive call to [repeat''']; indeed, it would be invalid to
    provide one!)

    We will use the latter style whenever possible, but we will
    continue to use explicit [Argument] declarations for [Inductive]
    constructors.  The reason for this is that marking the parameter
    of an inductive type as implicit causes it to become implicit for
    the type itself, not just for its constructors.  For instance,
    consider the following alternative definition of the [list]
    type: *)
(* end hide *)
(** （ここで注意してほしいのは、再帰呼び出しの[repeat''']ではもうすでに型を引数で指定していない、ということです。
    また、渡そうとするのは誤りとなります。）
 
    これからは、定義時に指定する後者の書き方をできるだけ使っていくことにします。
    ただし、[Inductive]の構成子では[Arguments]を明示的に書くようにします。
    というのも、帰納型のパラメータを暗黙にするのは、型そのもののパラメータを暗黙にするのであって、構成子のパラメータだけを暗黙にするわけではないからです。
    例えば、以下のように[list]を定義したとしましょう。 *)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** Because [X] is declared as implicit for the _entire_ inductive
    definition including [list'] itself, we now have to write just
    [list'] whether we are talking about lists of numbers or booleans
    or anything else, rather than [list' nat] or [list' bool] or
    whatever; this is a step too far. *)

(** Let's finish by re-implementing a few other standard list
    functions on our new polymorphic lists... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(* begin hide *)
(** One small problem with declaring arguments [Implicit] is
    that, occasionally, Coq does not have enough local information to
    determine a type argument; in such cases, we need to tell Coq that
    we want to give the argument explicitly just this time.  For
    example, suppose we write this: *)
(* end hide *)
(** 引数を暗黙的に宣言することには、小さな問題が一つあります。
    時折、Coqが型を特定するために必要な情報を十分に集められない時があるのです。
    そういう場合には、その時だけ明示してやります。
    例えば、もし次のように書いたとします。 *)

Fail Definition mynil := nil.

(* begin hide *)
(** (The [Fail] qualifier that appears before [Definition] can be
    used with _any_ command, and is used to ensure that that command
    indeed fails when executed. If the command does fail, Coq prints
    the corresponding error message, but continues processing the rest
    of the file.)

    Here, Coq gives us an error because it doesn't know what type
    argument to supply to [nil].  We can help it by providing an
    explicit type declaration (so that Coq has more information
    available when it gets to the "application" of [nil]): *)
(* end hide *)
(** （[Definition]の前にある[Fail]という修飾子は、実行すると失敗することを表します。
    この修飾子はどのコマンドにも使えます。
    もし指定したコマンドが失敗すると、Coqがエラーメッセージを出しますが、処理を続行します。）
 
    この定義ではCoqがエラーを出します。
    [nil]にどんな型を与えれば良いかわからないからです。
    このようなときは、型宣言を明示的に行うことができます（これによって[nil]を何に「適用したか」という情報が与えられます）。 *)

Definition mynil : list nat := nil.

(* begin hide *)
(** Alternatively, we can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)
(* end hide *)
(** それとは別に、関数名の前に[@]を付けることで暗黙的に宣言された引数を明示的に与えることができます。 *)

Check @nil.

Definition mynil' := @nil nat.

(* begin hide *)
(** Using argument synthesis and implicit arguments, we can
    define convenient notation for lists, as before.  Since we have
    made the constructor type arguments implicit, Coq will know to
    automatically infer these when we use the notations. *)
(* end hide *)
(** 引数の構成と暗黙の引数をつかうことで、リストに関する便利な表記法を定義できます。
    コンストラクタの型引数を暗黙的に記述すれば、Coqはその表記法を使ったときに型を自動的に推論してくれます。 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* begin hide *)
(** Now lists can be written just the way we'd hope: *)
(* end hide *)
(** これで、我々の望む書き方ができるようになりました。 *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Exercises *)
(* end hide *)
(** *** 練習問題 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (poly_exercises)  

    Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (poly_exercises)
 
    ここにあるいくつかの練習問題は、List.vにあったものと同じですが、多相性の練習になります。
    以下の証明を完成させなさい。 *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (more_poly_exercises)  

    Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Polymorphic Pairs *)
(* end hide *)
(** ** 多相的な対 *)

(* begin hide *)
(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_, often called _products_: *)
(* end hide *)
(** 次も同様に、前の章で作った数値の対を多相的な対に一般化することを考えます。
    これは「直積(_products_)」とも呼ばれます。 *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(* begin hide *)
(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)
(* end hide *)
(** リストと同様、型引数を暗黙にし、その表記法を定義します。 *)

Notation "( x , y )" := (pair x y).

(* begin hide *)
(** We can also use the [Notation] mechanism to define the standard
    notation for product _types_: *)
(* end hide *)
(** また、直積「型」の、より標準的な表記法も登録しておきます。 *)

Notation "X * Y" := (prod X Y) : type_scope.

(* begin hide *)
(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types.  This avoids a clash with
    the multiplication symbol.) *)
(* end hide *)
(** （[type_scope]というアノテーションは、この省略形が、型を解析する際のみ使われることを示しています。
    これによって、[*]が乗算の演算子と衝突することを避けています。*)

(* begin hide *)
(** It is easy at first to get [(x,y)] and [X*Y] confused.
    Remember that [(x,y)] is a _value_ built from two other values,
    while [X*Y] is a _type_ built from two other types.  If [x] has
    type [X] and [y] has type [Y], then [(x,y)] has type [X*Y]. *)
(* end hide *)
(** 最初のうちは、[(x,y)]と[X*Y]の違いに混乱するかもしれません。
    覚えてほしいのは、[(x,y)]が対の「値」を二つの値から構成するもので、[X*Y]は対の「型」を二つの型から構成するものだということです。
    値[x]が[X]型で、値[y]が[Y]型なら、値[(x,y)]は[X*Y]型となります。 *)

(* begin hide *)
(** The first and second projection functions now look pretty
    much as they would in any functional programming language. *)
(* end hide *)
(** 対の最初の要素、2番目の要素を返す射影関数は他のプログラミング言語で書いたものと大体同じになります。 *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* begin hide *)
(** The following function takes two lists and combines them
    into a list of pairs.  In other functional languages, it is often
    called [zip]; we call it [combine] for consistency with Coq's
    standard library. *)
(* end hide *)
(** 次の関数は二つのリストを引数にとり、一つの"対のリスト"を作成します。
    他の関数型言語で[zip]関数と呼ばれているものですが、ここではCoqの標準ライブラリに合わせる形で[combine]と呼ぶことにします。 *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (combine_checks)  

    Try answering the following questions on paper and
    checking your answers in Coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)
    - What does

        Compute (combine [1;2] [false;false;true;true]).

      print? 

    [] *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (combine_checks)
 
    次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。
    - 関数[combine]の型は何でしょう （[Check @combine]の出力結果は？）
    - それでは
[[
        Compute (combine [1;2] [false;false;true;true]). 
]]
      は何を出力する？
 
    []  *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (split)  

    The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (split)
 
    [split]関数は[combine]と全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。
    多くの関数型言語で[unzip]と呼ばれているものです。
 
    [split]関数の定義を完成させ、続くテストを通過することも確認しなさい。 *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Polymorphic Options *)
(* end hide *)
(** ** 多相的なオプション *)

(* begin hide *)
(** One last polymorphic type for now: _polymorphic options_,
    which generalize [natoption] from the previous chapter.  (We put
    the definition inside a module because the standard library
    already defines [option] and it's this one that we want to use
    below.) *)
(* end hide *)
(** 最後に、多相的なオプションに取り組みます。
    この型は、前の章の[natoption]を一般化したものになります。
    （[option]は標準ライブラリで定義されていて、後ほどそちらを使いたいので、ここでは定義をモジュール内に入れています。） *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(* begin hide *)
(** We can now rewrite the [nth_error] function so that it works
    with any type of lists. *)
(* end hide *)
(** [nth_error]関数を、色々な型のリストで使えるように定義し直しましょう。 *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (hd_error_poly)  

    Complete the definition of a polymorphic version of the
    [hd_error] function from the last chapter. Be sure that it
    passes the unit tests below. *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (hd_error_poly)
 
    前の章に出てきた[hd_error]関数の多相版を定義しなさい。
    次の単体テストでの確認も忘れずに。 *)

Definition hd_error {X : Type} (l : list X) : option X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* begin hide *)
(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)
(* end hide *)
(** 再び、暗黙の引数を明示してみましょう。
    関数名の前に[@]をつければいいのでしたね。 *)

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Functions as Data *)
(* end hide *)
(** * データとしての関数 *)

(* begin hide *)
(** Like many other modern programming languages -- including
    all functional languages (ML, Haskell, Scheme, Scala, Clojure,
    etc.) -- Coq treats functions as first-class citizens, allowing
    them to be passed as arguments to other functions, returned as
    results, stored in data structures, etc. *)
(* end hide *)
(** 他の多くの近代的なプログラミング言語（MLやHaskell、Scheme、Scala、Clojureなどの関数型言語を含む）同様、Coqは関数を第1級に属するものとして取り扱います。
    第1級に属するということは、他の関数の引数として渡したり、結果として返したり、データ構造の中に含めたりできる、ということです。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Higher-Order Functions *)
(* end hide *)
(** ** 高階関数 *)

(* begin hide *)
(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)
(* end hide *)
(** 関数を操作する関数を、一般に「高階(_higher-order_)」関数と呼びます。
    例えば次のようなものです。 *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(* begin hide *)
(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)
(* end hide *)
(** ここで引数[f]は（[X]から[X]への）関数です。
    [doit3times]の内容は、値[n]に対して関数[f]を3回適用するものです。 *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Filter *)
(* end hide *)
(** ** フィルター(Filter)関数 *)

(* begin hide *)
(** Here is a more useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)
(* end hide *)
(** 次に紹介するのは、もっと有用な高階関数です。
    これは、[X]型のリストと、[X]についての述語（[X]を引数にとり、[bool]を返す関数）を引数にとり、リストの要素に「フィルター(filter)」をかけて、述語の結果が[true]となった要素だけのリストを返す関数です。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(* begin hide *)
(** For example, if we apply [filter] to the predicate [evenb]
    and a list of numbers [l], it returns a list containing just the
    even members of [l]. *)
(* end hide *)
(** 例えば、この[filter]関数に述語として[evenb]と数値のリスト[l]を与えると、リスト[l]の要素のうち偶数の要素だけが含まれるリストとなって返ります。 *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(* begin hide *)
(** We can use [filter] to give a concise version of the
    [countoddmembers] function from the [Lists] chapter. *)
(* end hide *)
(** この[filter]を使うことで、 [Lists.v]にある[countoddmembers]関数をもっと簡潔に書くことができます。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Anonymous Functions *)
(* end hide *)
(** ** 無名（匿名）関数 *)

(* begin hide *)
(** It is arguably a little sad, in the example just above, to
    be forced to define the function [length_is_1] and give it a name
    just to be able to pass it as an argument to [filter], since we
    will probably never use it again.  Moreover, this is not an
    isolated example: when using higher-order functions, we often want
    to pass as arguments "one-off" functions that we will never use
    again; having to give each of these functions a name would be
    tedious.

    Fortunately, there is a better way.  We can construct a function
    "on the fly" without declaring it at the top level or giving it a
    name. *)
(* end hide *)
(** 少し悲しいことに、上の例では、[filter]の引数とするために、多分以降全く使われないであろう関数[length_is_1]をわざわざ定義して名付けなければなりませんでした。
    このようなことは、この例だけの問題ではありません。
    高階関数を使うときは、引数として以降では全く使わない「一度きり」の関数を渡すことがよくあります。
    こういう関数にいちいち名前を考えるのは、退屈以外の何物でもありません。
 
    幸いなことに、いい方法があります。
    関数を、トップレベルで宣言することも名前を付けることもなく、「その場で(on the fly)」作ることができるのです。 *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

(* begin hide *)
(** Here is the [filter] example, rewritten to use an anonymous
    function. *)
(* end hide *)
(** 次は[filter]の例を、無名関数を使って書き換えた例です。 *)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard (filter_even_gt7)  

    Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)
(* end hide *)
(** **** 練習問題: ★★, standard (filter_even_gt7)
 
    [Fixpoint]の代わりに[filter]関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出す[filter_even_gt7]関数を書きなさい。 *)

Definition filter_even_gt7 (l : list nat) : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (partition)  

    Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)
(* end hide *)
(** **** 練習問題: ★★★, standard (partition)
 
    [filter]関数を使って、[partition]関数を書きなさい。
[[
      partition : forall X : Type, 
                  (X -> bool) -> list X -> list X * list X 
]]
   [partition]関数は、型[X]と[X]の値がある条件を満たすかを調べる述語（[X -> bool]型の関数）と[list X]の値を引数に与えると、リストの対を返します。
   対の最初の要素は、与えられたリストのうち、条件を満たす要素だけのリストで、二番目の要素は、条件を満たさないもののリストです。
   二つのリストの要素の順番は、元のリストの順と同じでなければなりません。*)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
(* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Map *)
(* end hide *)
(** ** マップ(Map)関数 *)

(* begin hide *)
(** Another handy higher-order function is called [map]. *)
(* end hide *)
(** もう一つ、便利な高階関数として[map]を挙げます。 *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(* begin hide *)
(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)
(* end hide *)
(** これは、関数[f]とリスト[ l = [n1, n2, n3, ...] ]を引数にとり、関数[f]を[l]の各要素に適用した[ [f n1, f n2, f n3,...] ]というリストを返します。
    例えばこのようなものです。 *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(* begin hide *)
(** The element types of the input and output lists need not be
    the same, since [map] takes _two_ type arguments, [X] and [Y]; it
    can thus be applied to a list of numbers and a function from
    numbers to booleans to yield a list of booleans: *)
(* end hide *)
(** 入力されるリストの要素の型と、出力されるリストの要素の型は同じである必要はありません。
    [map]は、2つの型変数[X]と[Y]を取ります。
    これにより、次の例では、数値のリストと、数値を受け取り[bool]値を返す関数から、[bool]型のリストを返しています。 *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity.  Qed.

(* begin hide *)
(** It can even be applied to a list of numbers and
    a function from numbers to _lists_ of booleans to
    yield a _list of lists_ of booleans: *)
(* end hide *)
(** [map]は、数値のリストと、「数値から[bool]型のリストへの関数」を引数にとることで、「[bool]型のリストのリスト」を返すこともできます。 *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (map_rev)  

    Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)
(* end hide *)
(** **** 練習問題: ★★★, standard (map_rev)
 
    [map]と[rev]が可換であることを示しなさい。
    補題をたてて証明する必要があるでしょう。 *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (flat_map)  

    The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (flat_map)
 
    [map]関数は、[list X]から[list Y]へのマップを、型[X -> Y]の関数を使って実現しています。
    同じような関数[flat_map]を定義しましょう。
    これは[list X]から[list Y]へのマップですが、[X -> list Y]となる関数[f]を使用します。
    このため、次のように要素ごとの関数[f]の結果を平坦化してやる必要があります。
[[
        flat_map (fun n => [n;n+1;n+2]) [1;5;10] 
      = [1; 2; 3; 5; 6; 7; 10; 11; 12] 
]]
 *)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** Lists are not the only inductive type for which [map] makes sense.
    Here is a [map] for the [option] type: *)
(* end hide *)
(** リスト以外にも[map]関数が定義できるような帰納型はあります。
    次の定義は、[option]型のために[map]関数を定義したものです。 *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (implicit_args)  

    The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)

    [] *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (implicit_args)
 
    [filter]や[map]関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。
    暗黙の型引数定義に使われている波括弧を丸括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかどうかをCoqでチェックしなさい。
    （この練習問題はここに書かないようにしましょう。
    あとで簡単に戻せるように、このファイルをコピーして編集し、終わった後捨てるのが一番楽だと思います。）
 
    []  *)

(* ================================================================= *)
(* begin hide *)
(** ** Fold *)
(* end hide *)
(** ** 畳み込み（Fold）関数 *)

(* begin hide *)
(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)
(* end hide *)
(** さらにパワフルな高階関数[fold]に話を移します。
    この関数はGoogleの分散フレームワーク「map/reduce」でいうところの「[reduce]」操作の元になったものです。 *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* begin hide *)
(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

       fold plus [1;2;3;4] 0

    yields

       1 + (2 + (3 + (4 + 0))).

    Some more examples: *)
(* end hide *)
(** 直観的に[fold]は、与えられたリストの各要素の間に、与えられた二項演算子[f]を挟み込むように挿入していくような操作です。
    例えば、[ fold plus [1,2,3,4] ]は、直感的に[1+2+3+4]と同じ意味です。
    ただし正確には、二番めの引数に、[f]に最初に与える"初期値"が必要になります。例えば
[[
       fold plus [1;2;3;4] 0 
]]
    は、次のように解釈されます。
[[
       1 + (2 + (3 + (4 + 0))) 
]]
    もう少し例を見ていきましょう。 *)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* begin hide *)
(** **** Exercise: 1 star, advanced (fold_types_different)  

    Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)
(* end hide *)
(** **** 練習問題: ★, advanced (fold_types_different)
 
    [fold]関数が[X]と[Y]2つの型引数をとっていて、関数[f]が[X]と[Y]の値を引数にとり[Y]を返すようになっていることに注目してください。
    [X]と[Y]が別々の型となっていることで、便利になるような場面を考えなさい。 *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_fold_types_different : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Functions That Construct Functions *)
(* end hide *)
(** ** 関数を構築する関数 *)

(* begin hide *)
(** Most of the higher-order functions we have talked about so
    far take functions as arguments.  Let's look at some examples that
    involve _returning_ functions as the results of other functions.
    To begin, here is a function that takes a value [x] (drawn from
    some type [X]) and returns a function from [nat] to [X] that
    yields [x] whenever it is called, ignoring its [nat] argument. *)
(* end hide *)
(** これまで見てきた高階関数は、ほとんどが関数を引数にとるものでした。
    ここでは、関数が別の関数の戻り値になるような例を見ていきましょう。
    まず、（型[X]の）値[x]を引数としてとり、「[nat]型の引数から[X]型の戻り値を返す関数」を返す関数を考えます。
    返す関数は、与えられた[nat]型の引数に関係なく、生成時に与えられた値[x]を常に返すものです。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* begin hide *)
(** In fact, the multiple-argument functions we have already
    seen are also examples of passing functions as data.  To see why,
    recall the type of [plus]. *)
(* end hide *)
(** 実は、我々がすでに見た、複数の引数を持つ関数は、関数をデータとして渡すサンプルになっているのです。
    どういうことかは、[plus]関数の型を思い出せば分かります。 *)

Check plus.
(* ==> nat -> nat -> nat *)

(* begin hide *)
(** Each [->] in this expression is actually a _binary_ operator
    on types.  This operator is _right-associative_, so the type of
    [plus] is really a shorthand for [nat -> (nat -> nat)] -- i.e., it
    can be read as saying that "[plus] is a one-argument function that
    takes a [nat] and returns a one-argument function that takes
    another [nat] and returns a [nat]."  In the examples above, we
    have always applied [plus] to both of its arguments at once, but
    if we like we can supply just the first.  This is called _partial
    application_. *)
(* end hide *)
(** [->]は、型同士の二項演算子です。
    さらに、この演算子は右結合であるため、[plus]関数の型は[nat -> (nat -> nat)]の省略です。
    これをよく読むと「[plus]は[nat]型の引数を一つ取り、引数が[nat]型一つで[nat]型を返す関数を返す」となります。
    以前の例では[plus]に二つの引数を一緒に与えていましたが、もし望むなら最初の一つだけを与えることもできます。
    これを「部分適用(_partial application_)」といいます。 *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(* ################################################################# *)
(* begin hide *)
(** * Additional Exercises *)
(* end hide *)
(** * さらなる練習問題 *)

Module Exercises.

(* begin hide *)
(** **** Exercise: 2 stars, standard (fold_length)  

    Many common functions on lists can be implemented in terms of
    [fold].  For example, here is an alternative definition of [length]: *)
(* end hide *)
(** **** 練習問題: ★★, standard (fold_length)
 
    リストに関する多くの一般的な関数は[fold]を使って実装できます。
    例えば、次に示すのは[length]の別な実装です。 *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(* begin hide *)
(** Prove the correctness of [fold_length].  (Hint: It may help to
    know that [reflexivity] simplifies expressions a bit more
    aggressively than [simpl] does -- i.e., you may find yourself in a
    situation where [simpl] does nothing but [reflexivity] solves the
    goal.) *)
(* end hide *)
(** [fold_length]が正しいことを証明しなさい。
    （ヒント：[reflexivity]は[simpl]よりも簡単化を進めます。
    そのため、[simpl]では何も起こらないのに[reflexivity]が証明してしまうようなゴールもありえます。） *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (fold_map)  

    We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)
(* end hide *)
(** **** 練習問題: ★★★, standard (fold_map)
 
    [map]関数も[fold]を使って書くことができます。
    以下の[fold_map]を完成させなさい。 *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* begin hide *)
(** Write down a theorem [fold_map_correct] in Coq stating that
   [fold_map] is correct, and prove it.  (Hint: again, remember that
   [reflexivity] simplifies expressions a bit more aggressively than
   [simpl].) *)
(* end hide *)
(** [fold_map]の正しさを示す定理をCoqで書き、証明しなさい。
    （ヒント・再掲：[reflexivity]は[simpl]よりも簡単化を進めます。） *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, advanced (currying)  

    In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)
(* end hide *)
(** **** 練習問題: ★★, advanced (currying)
 
    Coqでは、[f : A -> B -> C]という関数の型は[A -> (B -> C)]型と同じです。
    このことは、もし関数[f]に[A]の値を与えると、[f' : B -> C]という型の関数が戻り値として返ってくるということです。
    さらに、[f']に[B]の値を与えると[C]の値が返ってきます。
    これは部分適用の[plus3]でやった通りです。
    このように、複数の引数を、関数を返す関数を通じて処理することを、論理学者ハスケル・カリーにちなんで「カリー化(_currying_)」と呼んでいます。
 
    逆に、[A -> B -> C]型の関数を[(A * B) -> C]型の関数に変換することもできます。
    これを「アンカリー化(_uncurrying_)」といいます。
    アンカリー化された二項演算は、二つの引数を同時に対の形で与える必要があり、部分適用はできません。 *)

(* begin hide *)
(** We can define currying as follows: *)
(* end hide *)
(** カリー化は以下のように定義できます。 *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(* begin hide *)
(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)
(* end hide *)
(** 練習問題として、その逆の[prod_uncurry]を定義し、二つの関数が互いに逆関数であることを証明しなさい。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** As a (trivial) example of the usefulness of currying, we can use it
    to shorten one of the examples that we saw above: *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

(* begin hide *)
(** Thought exercise: before running the following commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]? *)
(* end hide *)
(** 考える練習: 次のコマンドを実行する前に、[prod_curry]と[prod_uncurry]の型を考えなさい。 *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, advanced (nth_error_informal)  

    Recall the definition of the [nth_error] function:

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.

   Write an informal proof of the following theorem:

   forall X n l, length l = n -> @nth_error X l n = None
*)
(* end hide *)
(** **** 練習問題: ★★, advanced (nth_error_informal)
 
    [nth_error]関数の定義を思い出してください。
[[
   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X := 
     match l with 
     | [] => None 
     | a :: l' => if n =? O then Some a else nth_error l' (pred n) 
     end. 
]]
   次の定理の、非形式的な証明を書きなさい。
[[
   forall X n l, length l = n -> @nth_error X l n = None 
]]
 *)
(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(* begin hide *)
(** The following exercises explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church.  We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. *)
(* end hide *)
(** 以降の練習問題では、自然数を定義する他の方法として、「チャーチ数(_Church numerals_)」と呼ばれる、数学者アロンゾ・チャーチ(Alonzo Church)にちなむ方法を見ていきます。
    自然数[n]を、関数[f]を取り[f]を[n]回繰り返し適用するものとして表現します。 *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(* begin hide *)
(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it.  Thus: *)
(* end hide *)
(** ではこの方法でどのように数値を表すのか見ていきます。
    [f]を1回だけ適用するというのは、単に適用するだけです。
    つまり、次のようになります。 *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(* begin hide *)
(** Similarly, [two] should apply [f] twice to its argument: *)
(* end hide *)
(** 同様に、[two]は引数に2回[f]を適用するものです。 *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* begin hide *)
(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"?  The answer is actually simple: just return the
    argument untouched. *)
(* end hide *)
(** [zero]の定義は少し変わっています。
    0回関数を適用するとは一体どういうことでしょうか？
    答えは簡単です：単に引数に何もしなければいいのです。 *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* begin hide *)
(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  Notice in
    particular how the [doit3times] function we've defined previously
    is actually just the Church representation of [3]. *)
(* end hide *)
(** 一般に、数値[n]は[fun X f x => f (f ... (f x) ...)]のような形で、[f]が[n]回出現するものになります。
    つまり、以前定義した[doit3times]関数は実はちょうどチャーチ数での[3]を表していることになります。 *)

Definition three : cnat := @doit3times.

(* begin hide *)
(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)
(* end hide *)
(** 以下の関数の定義を完成させなさい。
    また、[reflexivity]を使えば証明できる以下の単体テストを通過することを確かめなさい。 *)

(* begin hide *)
(** **** Exercise: 1 star, advanced (church_succ)  *)
(* end hide *)
(** **** 練習問題: ★, advanced (church_succ)  *)

(* begin hide *)
(** Successor of a natural number: given a Church numeral [n],
    the successor [succ n] is a function that iterates its
    argument once more than [n]. *)
(* end hide *)
(** 自然数の+1：チャーチ数[n]について、[succ n]は[n]回とさらにもう一回繰り返す関数です。 *)
Definition succ (n : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, advanced (church_plus)  *)
(* end hide *)
(** **** 練習問題: ★, advanced (church_plus) *)

(* begin hide *)
(** Addition of two natural numbers: *)
(* end hide *)
(** 二つの自然数の加算： *)
Definition plus (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, advanced (church_mult)  *)
(* end hide *)
(** **** 練習問題: ★★, advanced (church_mult)  *)

(* begin hide *)
(** Multiplication: *)
(* end hide *)
(** 乗算： *)
Definition mult (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, advanced (church_exp)  *)
(* end hide *)
(** **** 練習問題: ★★, advanced (church_exp)  *)

(* begin hide *)
(** Exponentiation: *)
(* end hide *)
(** 冪： *)

(* begin hide *)
(** (_Hint_: Polymorphism plays a crucial role here.  However,
    choosing the right type to iterate over can be tricky.  If you hit
    a "Universe inconsistency" error, try iterating over a different
    type.  Iterating over [cnat] itself is usually problematic.) *)
(* end hide *)
(** （ヒント：ここでは多相性が非常に重要な役割を果たします。
    しかし、適切な型を指定するのは結構面倒です。
    もし"Universe inconsistency"というエラーに遭遇した場合、他の型を試してみてください。
    [cnat]に関して[cnat]で繰り返すのは問題を起こすものなのです。） *)

Definition exp (n m : cnat) : cnat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

End Church.

End Exercises.


(* Wed Jan 9 12:02:44 EST 2019 *)

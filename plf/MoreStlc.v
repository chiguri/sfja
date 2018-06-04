(** * MoreStlc: 単純型付きラムダ計算についてさらに *)
(* begin hide *)
(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)
(* end hide *)
 
Set Warnings "-notation-overridden,-parsing".
Require Import Maps.
Require Import Types.
Require Import Smallstep.
Require Import Stlc.

(* ################################################################# *)
(* begin hide *)
(** * Simple Extensions to STLC *)
(* end hide *)
(** * STLCの単純な拡張 *)

(* begin hide *)
(** The simply typed lambda-calculus has enough structure to make its
    theoretical properties interesting, but it is not much of a
    programming language.

    In this chapter, we begin to close the gap with real-world
    languages by introducing a number of familiar features that have
    straightforward treatments at the level of typing. *)
(* end hide *)
(** 単純型付きラムダ計算は理論的性質を興味深いものにするには十分な構造を持っていますが、プログラミング言語といえるようなものではありません。
 
    この章では、型における扱いが明らかないくつもの馴染み深い機能を導入することで、実世界の言語とのギャップを埋め始めます。*)

(* ================================================================= *)
(* begin hide *)
(** ** Numbers *)
(* end hide *)
(** ** 数値 *)

(** As we saw in exercise [stlc_arith] at the end of the [StlcProp]
    chapter, adding types, constants, and primitive operations for
    natural numbers is easy -- basically just a matter of combining
    the [Types] and [Stlc] chapters.  Adding more realistic
    numeric types like machine integers and floats is also
    straightforward, though of course the specifications of the
    numeric primitives become more fiddly. *)

(* ================================================================= *)
(* begin hide *)
(** ** Let Bindings *)
(* end hide *)
(** ** [let]束縛 *)

(* begin hide *)
(** When writing a complex expression, it is useful to be able
    to give names to some of its subexpressions to avoid repetition
    and increase readability.  Most languages provide one or more ways
    of doing this.  In OCaml (and Coq), for example, we can write [let
    x=t1 in t2] to mean "reduce the expression [t1] to a value and
    bind the name [x] to this value while reducing [t2]."

    Our [let]-binder follows OCaml in choosing a standard
    _call-by-value_ evaluation order, where the [let]-bound term must
    be fully reduced before reduction of the [let]-body can begin.
    The typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body (which is then
    the type of the whole [let] expression).

    At this point in the book, it's probably easier simply to look at
    the rules defining this new feature than to wade through a lot of
    English text conveying the same information.  Here they are: *)
(* end hide *)
(** 複雑な式を書くとき、部分式に名前をつけられると便利なことがよくあります。
    同じことを繰り返すのを避けることができ、またしばしば可読性が向上します。
    ほとんどの言語はこのための1つ以上の方法を持っています。
    例えばOCaml（およびCoq）では、 [let x=t1 in t2] と書くと「式[t1]を簡約して、その結果を名前[x]に束縛して[t2]を簡約する」ことを意味します。
 
    ここで導入する[let]束縛子はOCamlに従って値呼び(call-by-value)評価順序とします。
    つまり、[let]本体の評価が始まる前に[let]束縛項は完全に評価されます。
    型付け規則[T_Let]は、[let]の型が次の手順で計算されることを示しています:
    まず[let]束縛項の型の計算、次にその型の束縛によるコンテキストの拡張、さらにこの拡張されたコンテキストでの[let]本体の型の計算をします（これが[let]式全体の型になります）。
 
    本資料のこの時点では、新しい機能の定義のためにたくさんの日本語の文章を読み通すより、同じ情報を伝える規則を単に見る方が、おそらく簡単でしょう。以下がその規則です: *)

(* begin hide *)
(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | let x=t in t      let-binding
*)
(* end hide *)
(** 構文:
<<
       t ::=                項
           | ...               （前と同じ他の項）
           | let x=t in t      let束縛
>>
 *)

(* begin hide *)
(**
    Reduction:

                                 t1 ==> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 ==> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 ==> [x:=v1]t2

    Typing:

             Gamma |- t1 : T1      Gamma & {{x-->T1}} |- t2 : T2
             ---------------------------------------------------        (T_Let)
                        Gamma |- let x=t1 in t2 : T2
*)
(* end hide *)
(**
    簡約:
<<
                                 t1 ==> t1' 
                     ----------------------------------               (ST_Let1) 
                     let x=t1 in t2 ==> let x=t1' in t2 
 
                        ----------------------------              (ST_LetValue) 
                        let x=v1 in t2 ==> [x:=v1]t2 
>>
    型付け:
<<
             Gamma |- t1 : T1      Gamma & {{x-->T1}} |- t2 : T2 
             ---------------------------------------------------        (T_Let) 
                        Gamma |- let x=t1 in t2 : T2 
>>
 *)

(* ================================================================= *)
(* begin hide *)
(** ** Pairs *)
(* end hide *)
(** ** 対 *)

(* begin hide *)
(** Our functional programming examples in Coq have made
    frequent use of _pairs_ of values.  The type of such a pair is
    called a _product type_.

    The formalization of pairs is almost too simple to be worth
    discussing.  However, let's look briefly at the various parts of
    the definition to emphasize the common pattern. *)
(* end hide *)
(** ここまでのCoqを用いた関数プログラミングの例では、値の対(_pairs_)を頻繁に使ってきました。
    そのような対の型は「直積型(_product type_)」と呼ばれます。
 
    対の形式化はほとんど議論する余地がないほど簡単です。
    しかし、共通パターンを強調するため、定義のいろいろな部分をちょっと見てみましょう。 *)

(* begin hide *)
(** In Coq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our pairs this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:

       \x : Nat*Nat.
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
*)
(* end hide *)
(** Coqでは、対の構成要素を抽出する基本的な方法は、パターンマッチング(_pattern matching_)です。
    別の方法としては、[fst]と[snd]、つまり、1番目と2番目の要素の射影操作を基本操作として持つ方法があります。
    お遊びで、対をこの方法でやってみましょう。
    例えば、数値の対をとり、その和と差の対を返す関数の書き方は次の通りです:
<<
       \x : Nat*Nat. 
          let sum = x.fst + x.snd in 
          let diff = x.fst - x.snd in 
          (sum,diff) 
>>
 *)

(* begin hide *)
(** Adding pairs to the simply typed lambda-calculus, then, involves
    adding two new forms of term -- pairing, written [(t1,t2)], and
    projection, written [t.fst] for the first projection from [t] and
    [t.snd] for the second projection -- plus one new type constructor,
    [T1*T2], called the _product_ of [T1] and [T2].  *)
(* end hide *)
(** これから、単純型付きラムダ計算に対を追加するには、2つの新しい項の形を追加することが含まれます。
    1つは対で [(t1,t2)] と書きます。もう1つは射影で、第1射影は [t.fst]、第2射影は [t.snd]と書きます。
    さらに1つの型コンストラクタ [T1*T2] を追加します。
    これを[T1]と[T2]の直積と呼びます。 *)

(* begin hide *)
(** Syntax:

       t ::=                Terms
           | (t,t)             pair
           | t.fst             first projection
           | t.snd             second projection
           | ...

       v ::=                Values
           | (v,v)             pair value
           | ...

       T ::=                Types
           | T * T             product type
           | ...
*)
(* end hide *)
(** 構文:
<<
       t ::=                項
           | (t,t)             対
           | t.fst             第1射影
           | t.snd             第2射影
           | ... 
 
       v ::=                値
           | (v,v)             対値
           | ... 
 
       T ::=                型
           | T * T             直積型
           | ... 
>>
 *)

(* begin hide *)
(** For reduction, we need several new rules specifying how pairs and
    projection behave. *)
(* end hide *)
(** 簡約については、対と射影がどう振る舞うかを規定するいくつかの新しい規則が必要です。 *)
(* begin hide *)
(**

                              t1 ==> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) ==> (t1',t2)

                              t2 ==> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) ==> (v1,t2')

                              t1 ==> t1'
                          ------------------                          (ST_Fst1)
                          t1.fst ==> t1'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst ==> v1

                              t1 ==> t1'
                          ------------------                          (ST_Snd1)
                          t1.snd ==> t1'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd ==> v2
*)
(* end hide *)
(** 
<<
                              t1 ==> t1' 
                         --------------------                        (ST_Pair1) 
                         (t1,t2) ==> (t1',t2) 
 
                              t2 ==> t2' 
                         --------------------                        (ST_Pair2) 
                         (v1,t2) ==> (v1,t2') 
 
                              t1 ==> t1' 
                          ------------------                          (ST_Fst1) 
                          t1.fst ==> t1'.fst 
 
                          ------------------                       (ST_FstPair) 
                          (v1,v2).fst ==> v1 
 
                              t1 ==> t1' 
                          ------------------                          (ST_Snd1) 
                          t1.snd ==> t1'.snd 
 
                          ------------------                       (ST_SndPair) 
                          (v1,v2).snd ==> v2 
>>
 *)

(* begin hide *)
(** Rules [ST_FstPair] and [ST_SndPair] say that, when a fully
    reduced pair meets a first or second projection, the result is
    the appropriate component.  The congruence rules [ST_Fst1] and
    [ST_Snd1] allow reduction to proceed under projections, when the
    term being projected from has not yet been fully reduced.
    [ST_Pair1] and [ST_Pair2] reduce the parts of pairs: first the
    left part, and then -- when a value appears on the left -- the right
    part.  The ordering arising from the use of the metavariables [v]
    and [t] in these rules enforces a left-to-right evaluation
    strategy for pairs.  (Note the implicit convention that
    metavariables like [v] and [v1] can only denote values.)  We've
    also added a clause to the definition of values, above, specifying
    that [(v1,v2)] is a value.  The fact that the components of a pair
    value must themselves be values ensures that a pair passed as an
    argument to a function will be fully reduced before the function
    body starts executing. *)
(* end hide *)
(** 規則[ST_FstPair]と[ST_SndPair]は、完全に簡約された対が第1射影または第2射影に遭遇したとき、結果が対応する要素であると言っています。
    合同規則[ST_Fst1]と[ST_Snd1]は、射影の対象の項が完全に評価されきっていないとき、対象の簡約を認めるものです。
    [ST_Pair1]と[ST_Pair2]は対の構成部分の簡約です。
    最初に左の部分を簡約し、それが値となったら、次に右の部分を簡約します。
    これらの規則内におけるメタ変数[v]と[t]の使い方は、対に関して左から右に評価する戦略(left-to-right evaluation strategy)であることを規定します。
    （暗黙の慣習として、[v]や[v1]などのメタ変数は値のみを指すものとしています。）
    また値の定義に節を加え、[(v1,v2)] が値であることを規定しています。
    値の対自体が値でなければならないという事実は、関数の引数として渡された対が、関数の本体の実行が開始される前に完全に簡約されることを保証します。 *)

(* begin hide *)
(** The typing rules for pairs and projections are straightforward. *)
(* end hide *)
(** 対と射影の型付け規則はそのまま直ぐに得られます。 *)
(* begin hide *)
(**

               Gamma |- t1 : T1       Gamma |- t2 : T2
               ---------------------------------------                 (T_Pair)
                       Gamma |- (t1,t2) : T1*T2

                        Gamma |- t1 : T11*T12
                        ---------------------                           (T_Fst)
                        Gamma |- t1.fst : T11

                        Gamma |- t1 : T11*T12
                        ---------------------                           (T_Snd)
                        Gamma |- t1.snd : T12
*)
(* end hide *)
(** 
<<
               Gamma |- t1 : T1       Gamma |- t2 : T2 
               ---------------------------------------                 (T_Pair) 
                       Gamma |- (t1,t2) : T1*T2 
 
                        Gamma |- t1 : T11*T12 
                        ---------------------                           (T_Fst) 
                        Gamma |- t1.fst : T11 
 
                        Gamma |- t1 : T11*T12 
                        ---------------------                           (T_Snd) 
                        Gamma |- t1.snd : T12 
>>
 *)

(* begin hide *)
(** [T_Pair] says that [(t1,t2)] has type [T1*T2] if [t1] has
   type [T1] and [t2] has type [T2].  Conversely, [T_Fst] and [T_Snd]
   tell us that, if [t1] has a product type [T11*T12] (i.e., if it
   will reduce to a pair), then the types of the projections from
   this pair are [T11] and [T12]. *)
(* end hide *)
(** [T_Pair]は、[t1]が型[T1]を持ち、[t2]が型[T2]を持つならば、 [(t1,t2)] が型 [T1*T2] を持つことを言っています。
    逆に、[T_Fst]と[T_Snd]は、[t1]が直積型[T11*T12]を持つ（つまり評価結果が対になる）ならば、射影の型は[T11]と[T12]になることを定めます。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Unit *)
(* end hide *)
(** ** [Unit]型 *)

(* begin hide *)
(** Another handy base type, found especially in languages in
    the ML family, is the singleton type [Unit]. *)
(* end hide *)
(** もう一つの便利な基本型は、MLファミリーの言語に特に見られるものですが、1要素の型[Unit]です。 *)
(* begin hide *)
(** It has a single element -- the term constant [unit] (with a small
    [u]) -- and a typing rule making [unit] an element of [Unit].  We
    also add [unit] to the set of possible values -- indeed, [unit] is
    the _only_ possible result of reducing an expression of type
    [Unit]. *)
(* end hide *)
(** この型は要素を1つ持ちます。それは項定数[unit]です（先頭の文字は小文字の[u]です）。
    型付け規則は [unit]を[Unit]の要素と定めます。
    取りうる値の集合にも[unit]を加えます。
    実際、[unit]は型[Unit]の式の評価結果としてとり得る唯一の値です。 *)

(* begin hide *)
(** Syntax:

       t ::=                Terms
           | unit              unit value
           | ...

       v ::=                Values
           | unit              unit
           | ...

       T ::=                Types
           | Unit              Unit type
           | ...

    Typing:

                         --------------------                          (T_Unit)
                         Gamma |- unit : Unit
*)
(* end hide *)
(** 構文:
<<
       t ::=                項
           | unit              unit値
           | ... 
 
       v ::=                値
           | unit              unit 
           | ... 
 
       T ::=                型
           | Unit              Unit型
           | ... 
>>
    型付け:
<<
                         --------------------                          (T_Unit) 
                         Gamma |- unit : Unit 
>>
 *)

(* begin hide *)
(** It may seem a little strange to bother defining a type that
    has just one element -- after all, wouldn't every computation
    living in such a type be trivial?

    This is a fair question, and indeed in the STLC the [Unit] type is
    not especially critical (though we'll see two uses for it below).
    Where [Unit] really comes in handy is in richer languages with
    _side effects_ -- e.g., assignment statements that mutate
    variables or pointers, exceptions and other sorts of nonlocal
    control structures, etc.  In such languages, it is convenient to
    have a type for the (trivial) result of an expression that is
    evaluated only for its effect. *)
(* end hide *)
(** 1つの要素だけしか持たない型を定義することにわずらわされるのは、少々奇妙なことに見えるかもしれません。
    結局のところ、このような型に属する計算は自明なものだけではないのでしょうか？
 
    これは妥当な質問です。
    実際STLCでは[Unit]型は特別、問題ではありません（ちょっと後でこの型の使い道を二つ見ることになりますが）。
    [Unit]が本当に便利なのはよりリッチな言語で副作用(_side effects_)を持つ場合です。
    例えば、変更可能な変数やポインタについての代入文や、例外その他のローカルではないコントロール機構を持つ場合、などです。
    そのような言語では、副作用のためだけに評価される式の(どうでもよい)結果のための型が便利なのです。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Sums *)
(* end hide *)
(** ** 直和 *)

(* begin hide *)
(** Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify employees in an accounting
   application using _either_ their name _or_ their id number.
   A search function might return _either_ a matching value _or_ an
   error code.

   These are specific examples of a binary _sum type_ (sometimes called
   a _disjoint union_), which describes a set of values drawn from 
   one of two given types, e.g.:

       Nat + Bool
*)
(* end hide *)
(** 多くのプログラムでは2つの異なった形を持つ値を扱うことが求められます。
   例えばアカウント処理をするアプリケーションの認証で、名前か、「または」、IDナンバーを使うという場合があります。
   探索関数は、マッチした値か、「または」、エラーコードを返すかもしれません。
 
   これらは、2項の直和型(_sum type_ または _disjoint union_)の例です。
   直和型は2つの与えられた型の一方から抽出した値の集合にあたります。
   例えば次のようなものです。
<<
       Nat + Bool 
>>
 *)
(* begin hide *)
(** We create elements of these types by _tagging_ elements of
    the component types.  For example, if [n] is a [Nat] then [inl n]
    is an element of [Nat+Bool]; similarly, if [b] is a [Bool] then
    [inr b] is a [Nat+Bool].  The names of the tags [inl] and [inr]
    arise from thinking of them as functions

       inl : Nat -> Nat + Bool
       inr : Bool -> Nat + Bool

    that "inject" elements of [Nat] or [Bool] into the left and right
    components of the sum type [Nat+Bool].  (But note that we don't
    actually treat them as functions in the way we formalize them:
    [inl] and [inr] are keywords, and [inl t] and [inr t] are primitive
    syntactic forms, not function applications.) *)
(* end hide *)
(** この型の要素を、それぞれの構成部分の型の要素にタグ付けする(_tagging_)ことで生成します。
   例えば、[n]が[Nat]ならば [inl n] は [Nat+Bool] の要素です。
   同様に、[b]が[Bool]ならば [inr b] は [Nat+Bool] の要素です。
   タグの名前[inl]と[inr]は、これらのタグを関数と考えるところから出ています。
 
<<
       inl : Nat -> Nat + Bool 
       inr : Bool -> Nat + Bool 
>>
 
   これらの関数は、[Nat]または[Bool]の要素を直和型[Nat+Bool]の左部分または右部分に注入("inject")します。
   （しかし、実際にはこれらを関数としては扱いません。
   [inl]と[inr]はキーワードで、[inl t] と [inr t] は基本構文形であり、関数適用ではありません。） *)

(* begin hide *)
(** In general, the elements of a type [T1 + T2] consist of the
    elements of [T1] tagged with the token [inl], plus the elements of
    [T2] tagged with [inr]. *)
(* end hide *)
(** 一般に、型 [T1 + T2] の要素は [T1]の要素に[inl]をタグ付けしたものと、
   [T2]の要素に[inr]をタグ付けしたものから成ります。 *)

(* begin hide *)
(** One important usage of sums is signaling errors:

      div : Nat -> Nat -> (Nat + Unit) =
      div =
        \x:Nat. \y:Nat.
          if iszero y then
            inr unit
          else
            inl ...
*)
(* end hide *)
(** 直和型の重要な用途の一つに、エラー報告があります。
<< 
      div : Nat -> Nat -> (Nat + Unit) = 
      div = 
        \x:Nat. \y:Nat. 
          if iszero y then 
            inr unit 
          else 
            inl ... 
>>
 *)
(* begin hide *)
(** The type [Nat + Unit] above is in fact isomorphic to [option
    nat] in Coq -- i.e., it's easy to write functions that translate
    back and forth. *) 
(* end hide *)
(** この型 [Nat + Unit] は Coq における [option nat] と同型です。
    つまり、簡単に両方向へ変換する関数が書けます。 *)

(* begin hide *)
(** To _use_ elements of sum types, we introduce a [case]
    construct (a very simplified form of Coq's [match]) to destruct
    them. For example, the following procedure converts a [Nat+Bool]
    into a [Nat]: *)
(* end hide *)
(** 直和型の要素を「利用する」ために、分解する構文として[case]構文を導入します（これはCoqの[match]の非常に単純化された形です）。
   例えば、以下の手続きは、[Nat+Bool] を[Nat]に変換します: *)
(* begin hide *)
(** 

    getNat =
      \x:Nat+Bool.
        case x of
          inl n => n
        | inr b => if b then 1 else 0
*)
(* end hide *)
(**  
<<
    getNat = 
      \x:Nat+Bool. 
        case x of 
          inl n => n 
        | inr b => if b then 1 else 0 
>>
 *)
(* begin hide *)
(** More formally... *)
(* end hide *)
(** より形式的に... *)

(* begin hide *)
(** Syntax:

       t ::=                Terms
           | inl T t           tagging (left)
           | inr T t           tagging (right)
           | case t of         case
               inl x => t
             | inr x => t
           | ...

       v ::=                Values
           | inl T v           tagged value (left)
           | inr T v           tagged value (right)
           | ...

       T ::=                Types
           | T + T             sum type
           | ...
*)
(* end hide *)
(** 構文:
<<
       t ::=                項
           | inl T t           タグ付け（左）
           | inr T t           タグ付け（右）
           | case t of         case 
               inl x => t 
             | inr x => t 
           | ... 
 
       v ::=                値
           | inl T v           タグ付き値（左）
           | inr T v           タグ付き値（右）
           | ... 
 
       T ::=                型
           | T + T             直和型
           | ... 
>>
 *)

(* begin hide *)
(** Reduction:


                              t1 ==> t1'
                        ----------------------                         (ST_Inl)
                        inl T t1 ==> inl T t1'

                              t1 ==> t1'
                        ----------------------                         (ST_Inr)
                        inr T t1 ==> inr T t1'

                              t0 ==> t0'
                   -------------------------------------------       (ST_Case)
                   case t0 of inl x1 => t1 | inr x2 => t2 ==>
                   case t0' of inl x1 => t1 | inr x2 => t2

            ----------------------------------------------         (ST_CaseInl)
            case (inl T v0) of inl x1 => t1 | inr x2 => t2
                           ==>  [x1:=v0]t1

            ----------------------------------------------         (ST_CaseInr)
            case (inr T v0) of inl x1 => t1 | inr x2 => t2
                           ==>  [x2:=v0]t2
*)
(* end hide *)
(**  簡約:
<<
                              t1 ==> t1' 
                        ----------------------                         (ST_Inl) 
                        inl T t1 ==> inl T t1' 
 
                              t1 ==> t1' 
                        ----------------------                         (ST_Inr) 
                        inr T t1 ==> inr T t1' 
 
                              t0 ==> t0' 
                   -------------------------------------------       (ST_Case) 
                   case t0 of inl x1 => t1 | inr x2 => t2 ==> 
                   case t0' of inl x1 => t1 | inr x2 => t2  
 
            ----------------------------------------------         (ST_CaseInl) 
            case (inl T v0) of inl x1 => t1 | inr x2 => t2 
                           ==>  [x1:=v0]t1 
 
            ----------------------------------------------         (ST_CaseInr) 
            case (inr T v0) of inl x1 => t1 | inr x2 => t2 
                           ==>  [x2:=v0]t2 
>>
*)

(* begin hide *)
(** Typing:

                          Gamma |- t1 :  T1
                     ----------------------------                       (T_Inl)
                     Gamma |- inl T2 t1 : T1 + T2

                           Gamma |- t1 : T2
                     ----------------------------                       (T_Inr)
                     Gamma |- inr T1 t1 : T1 + T2

                         Gamma |- t0 : T1+T2
                       Gamma , x1:T1 |- t1 : T
                       Gamma , x2:T2 |- t2 : T
         ---------------------------------------------------           (T_Case)
         Gamma |- case t0 of inl x1 => t1 | inr x2 => t2 : T


    We use the type annotation in [inl] and [inr] to make the typing 
    relation simpler, similarly to what we did for functions. *)
(* end hide *)
(** 型付け:
<<
                          Gamma |- t1 :  T1 
                     ----------------------------                       (T_Inl) 
                     Gamma |- inl T2 t1 : T1 + T2 
 
                           Gamma |- t1 : T2 
                     ----------------------------                       (T_Inr) 
                     Gamma |- inr T1 t1 : T1 + T2 
 
                         Gamma |- t0 : T1+T2 
                       Gamma , x1:T1 |- t1 : T 
                       Gamma , x2:T2 |- t2 : T 
         ---------------------------------------------------           (T_Case) 
         Gamma |- case t0 of inl x1 => t1 | inr x2 => t2 : T 
>>
    [inl]と[inr]の形に型を付記する理由は、関数に対して行ったのと同様、型付け規則を単純にするためです。 *)

(* begin hide *)
(** Without this extra information, the typing rule [T_Inl], for
    example, would have to say that, once we have shown that [t1] is
    an element of type [T1], we can derive that [inl t1] is an element
    of [T1 + T2] for _any_ type [T2].  For example, we could derive both
    [inl 5 : Nat + Nat] and [inl 5 : Nat + Bool] (and infinitely many
    other types).  This peculiarity (technically, a failure of
    uniqueness of types) would mean that we cannot build a
    typechecking algorithm simply by "reading the rules from bottom to
    top" as we could for all the other features seen so far.

    There are various ways to deal with this difficulty.  One simple
    one -- which we've adopted here -- forces the programmer to
    explicitly annotate the "other side" of a sum type when performing
    an injection.  This is a bit heavy for programmers (so real
    languages adopt other solutions), but it is easy to understand and
    formalize. *)
(* end hide *)
(** この情報がなければ、型推論規則[T_Inl]は、例えば、[t1]が型[T1]の要素であることを示した後、「任意の」型[T2]について [inl t1] が [T1 + T2] の要素であることを導出できます。
    例えば、[inl 5 : Nat + Nat] と [inl 5 : Nat + Bool] の両方（および無数の型）が導出できます。
    この奇妙さ（技術的に言えば型の一意性の欠如）は、型チェックアルゴリズムを、ここまでやってきたように「規則を下から上に読む」という単純な方法で構築することができなくなることを意味します。
 
    この問題を扱うのにはいろいろな方法があります。
    簡単なものの1つは、ここで採用する方法ですが、単射を実行するときに直和型の「別の側」をプログラマが明示的に付記することを強制するというものです。
    これはプログラマにはかなり重い作業です（そのため実際の言語は別の解法を採用しています）。
    しかし、理解と形式化は容易な方法です。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Lists *)
(* end hide *)
(** ** リスト *)

(* begin hide *)
(** The typing features we have seen can be classified into _base
    types_ like [Bool], and _type constructors_ like [->] and [*] that
    build new types from old ones.  Another useful type constructor is
    [List].  For every type [T], the type [List T] describes
    finite-length lists whose elements are drawn from [T].

    In principle, we could encode lists using pairs, sums and
    _recursive_ types. But giving semantics to recursive types is
    non-trivial. Instead, we'll just discuss the special case of lists
    directly.

    Below we give the syntax, semantics, and typing rules for lists.
    Except for the fact that explicit type annotations are mandatory
    on [nil] and cannot appear on [cons], these lists are essentially
    identical to those we built in Coq.  We use [lcase] to destruct
    lists, to avoid dealing with questions like "what is the [head] of
    the empty list?" *)
(* end hide *)
(** ここまで見てきた型付け機能は、[Bool]のような基本型(_base types_)と、古い型から新しい型を構築する[->]や[*]のような型コンストラクタ(_type constructors_)に分類できます。
    もう一つの有用な型コンストラクタが[List]です。
    すべての型[T]について、型 [List T] は[T]から抽出したものを要素とする有限長リストを表します。
 
    原理的には、直積型や直和型、再帰型(_recursive_ types)を用いることでリストを定義できます。
    しかし、再帰型に意味を与えることは簡単ではありません。
    その代わりに、リストの特別な場合を直接議論します。
 
    以下にリストの構文、意味、型付け規則を与えます。
    [nil]に対して明示的に型を付記することが必須であり、[cons]には付記できないという点を除けば、ここで定義されたリストは本質的にCoqで構築したものと同じです。
    リストを分解するために[lcase]を使います。
    これは「空リストの[head]は何か？」というような問題を扱うことを避けるためです。 *)

(* begin hide *)
(** For example, here is a function that calculates the sum of
    the first two elements of a list of numbers:

      \x:List Nat.
      lcase x of nil => 0
         | a::x' => lcase x' of nil => a
                       | b::x'' => a+b
*)
(* end hide *)
(** 従って、例えば、数値リストの最初の2つの要素の和を計算する関数は次の通りです:
<<
      \x:List Nat. 
      lcase x of nil => 0 
         | a::x' => lcase x' of nil => a 
                       | b::x'' => a+b 
>>
 *)
(* begin hide *)
(**
    Syntax:

       t ::=                Terms
           | nil T
           | cons t t
           | lcase t of nil => t | x::x => t
           | ...

       v ::=                Values
           | nil T             nil value
           | cons v v          cons value
           | ...

       T ::=                Types
           | List T            list of Ts
           | ...
*)
(* end hide *)
(**
    構文:
<<
       t ::=                項
           | nil T 
           | cons t t 
           | lcase t of nil => t | x::x => t 
           | ... 
 
       v ::=                値
           | nil T             nil値
           | cons v v          cons値
           | ... 
 
       T ::=                型
           | List T            Tのリスト
           | ... 
>>
 *)

(* begin hide *)
(** Reduction:

                                 t1 ==> t1'
                       --------------------------                    (ST_Cons1)
                       cons t1 t2 ==> cons t1' t2

                                 t2 ==> t2'
                       --------------------------                    (ST_Cons2)
                       cons v1 t2 ==> cons v1 t2'

                              t1 ==> t1'
                ----------------------------------------             (ST_Lcase1)
                (lcase t1 of nil => t2 | xh::xt => t3) ==>
                (lcase t1' of nil => t2 | xh::xt => t3)

               -----------------------------------------          (ST_LcaseNil)
               (lcase nil T of nil => t2 | xh::xt => t3)
                                ==> t2

            -----------------------------------------------      (ST_LcaseCons)
            (lcase (cons vh vt) of nil => t2 | xh::xt => t3)
                          ==> [xh:=vh,xt:=vt]t3
*)
(* end hide *)
(** 簡約:
<<
                                 t1 ==> t1' 
                       --------------------------                    (ST_Cons1) 
                       cons t1 t2 ==> cons t1' t2 
 
                                 t2 ==> t2' 
                       --------------------------                    (ST_Cons2) 
                       cons v1 t2 ==> cons v1 t2' 
 
                              t1 ==> t1' 
                ----------------------------------------             (ST_Lcase1) 
                (lcase t1 of nil => t2 | xh::xt => t3) ==> 
                (lcase t1' of nil => t2 | xh::xt => t3) 
 
               -----------------------------------------          (ST_LcaseNil) 
               (lcase nil T of nil => t2 | xh::xt => t3) 
                                ==> t2 
 
            -----------------------------------------------      (ST_LcaseCons) 
            (lcase (cons vh vt) of nil => t2 | xh::xt => t3) 
                          ==> [xh:=vh,xt:=vt]t3 
>>
 *)

(* begin hide *)
(** Typing:

                          -----------------------                       (T_Nil)
                          Gamma |- nil T : List T

                Gamma |- t1 : T      Gamma |- t2 : List T
                -----------------------------------------              (T_Cons)
                       Gamma |- cons t1 t2: List T

                        Gamma |- t1 : List T1
                           Gamma |- t2 : T
                   Gamma , h:T1, t:List T1 |- t3 : T
          -------------------------------------------------           (T_Lcase)
          Gamma |- (lcase t1 of nil => t2 | h::t => t3) : T
*)
(* end hide *)
(** 型付け:
<<
                          -----------------------                       (T_Nil) 
                          Gamma |- nil T : List T 
 
                Gamma |- t1 : T      Gamma |- t2 : List T 
                -----------------------------------------              (T_Cons) 
                       Gamma |- cons t1 t2: List T 
 
                        Gamma |- t1 : List T1 
                           Gamma |- t2 : T 
                   Gamma , h:T1, t:List T1 |- t3 : T 
          -------------------------------------------------           (T_Lcase) 
          Gamma |- (lcase t1 of nil => t2 | h::t => t3) : T 
>>
 *)

(* ================================================================= *)
(* begin hide *)
(** ** General Recursion *)
(* end hide *)
(** ** 一般再帰 *)

(* begin hide *)
(** Another facility found in most programming languages (including
    Coq) is the ability to define recursive functions.  For example,
    we might like to be able to define the factorial function like
    this:

      fact = \x:Nat.
                if x=0 then 1 else x * (fact (pred x)))

   Note that the right-hand side of this binder mentions the variable
   being bound -- something that is not allowed by our formalization of
   [let] above.  

   Directly formalizing this "recursive definition" mechanism is possible, 
   but it requires a bit of extra effort: in particular, we'd have to 
   pass around an "environment" of recursive function definitions in 
   the definition of the [step] relation. *)
(* end hide *)
(** （Coqを含む）ほとんどのプログラミング言語に現れるもう1つの機構が、再帰関数を定義する機能です。
    例えば、階乗関数を次のように定義できるとよいと思うでしょう:
<<
      fact = \x:Nat. 
                if x=0 then 1 else x * (fact (pred x))) 
>>
   この束縛子の中では、上で導入した[let]と異なり、右辺の変数[fact]が束縛されることになります。
 
   直接「再帰的定義」を形式化することも可能ですが、なかなかの作業が必要になります。
   特に[step]内で再帰関数定義の「環境(environment)」を持ち回る必要があるでしょう。 *)

(* begin hide *)
(** Here is another way of presenting recursive functions that is equally
    powerful (though not quite as convenient for the programmer) and 
    more straightforward to formalize: instead of writing recursive 
    definitions, we define a _fixed-point operator_ called [fix] 
    that performs the "unfolding" of the recursive definition in the 
    right-hand side as needed, during reduction.  

    For example, instead of 

      fact = \x:Nat.
                if x=0 then 1 else x * (fact (pred x)))

    we will write:

      fact =
          fix
            (\f:Nat->Nat.
               \x:Nat.
                  if x=0 then 1 else x * (f (pred x)))
*)
(* end hide *)
(** ここでは、同じくらい強力な、また直接の形式化が容易な形での再帰関数の定義方法を取ります（プログラマにとっては不便を強いられることになりますが）。
    再帰的定義を書く代わりに、[fix]という名前の「不動点演算子(_fixed-point operator_)」を定義します。
    不動点演算子は、簡約の過程で必要に応じて再帰的定義の右辺に「展開」("unfold")するものです。
 
    例えば、
<<
      fact = \x:Nat. 
                if x=0 then 1 else x * (fact (pred x))) 
>>
    のように書く代わりに、次のように書きます。
<<
      fact = 
          fix 
            (\f:Nat->Nat. 
               \x:Nat. 
                  if x=0 then 1 else x * (f (pred x))) 
>>
 *)
(* begin hide *)
(** We can derive the latter from the former as follows:

      - In the right-hand side of the definition of [fact], replace 
        recursive references to [fact] by a fresh variable [f].

      - Add an abstraction binding [f] at the front, with an 
        appropriate type annotation.  (Since we are using [f] in place 
        of [fact], which had type [Nat->Nat], we should require [f]
        to have the same type.)  The new abstraction has type 
        [(Nat->Nat) -> (Nat->Nat)].

      - Apply [fix] to this abstraction.  This application has  
        type [Nat->Nat].

      - Use all of this as the right-hand side of an ordinary 
        [let]-binding for [fact].  
*)
(* end hide *)
(** 前者の書き方から、以下のようにして後者の書き方を得ます。
 
      - [fact]の定義の右辺から再帰的定義の対象である[fact]という名前を新しい変数名[f]で置き換えます。
 
      - [f]を束縛する抽象を、適切な方注釈と共に追加します。
        （[f]を[fact]の代わりに使っているので、[fact]が型[Nat->Nat]を持っていることから、[f]に同じ型[Nat->Nat]を付けます。）
        全体の型は[(Nat->Nat) -> (Nat->Nat)]になります。
 
      - この抽象に[fix]を適用します。
        その結果の型は[Nat->Nat]になります。
 
      - この全体を、[fact]に対する通常の[let]束縛の右辺として利用します。
 *)

(* begin hide *)
(** The intuition is that the higher-order function [f] passed
    to [fix] is a _generator_ for the [fact] function: if [f] is
    applied to a function that "approximates" the desired behavior of
    [fact] up to some number [n] (that is, a function that returns
    correct results on inputs less than or equal to [n] but we don't
    care what it does on inputs greater than [n]), then [f] returns a
    slightly better approximation to [fact] -- a function that returns
    correct results for inputs up to [n+1].  Applying [fix] to this
    generator returns its _fixed point_, which is a function that
    gives the desired behavior for all inputs [n].

    (The term "fixed point" is used here in exactly the same sense as
    in ordinary mathematics, where a fixed point of a function [f] is
    an input [x] such that [f(x) = x].  Here, a fixed point of a
    function [F] of type [(Nat->Nat)->(Nat->Nat)] is a function [f] of
    type [Nat->Nat] such that [F f] behaves the same as [f].) *)
(* end hide *)
(** 直観的には[fix]に渡される高階関数[f]は[fact]関数の生成器(_generator_)です。
    [f]が、[fact]に求められる振る舞いを[n]まで「近似」する関数（つまり、[n]以下の入力に対しては正しい結果を返すが[n]より大きい入力に関してはどうでもいい関数）に適用されるとき、[f]はより良い近似、つまり、[n+1]まで正しい答えを返す関数、を返します。
    [fix]をこの生成器に適用すると、生成器の「不動点(_fixed point_)」を返します。
    この不動点は、すべての入力[n]について求められる振る舞いをする関数です。
 
    （ここでは不動点("fixed point")という用語を通常の数学と同じ意味で使っています。
    通常の数学では、関数[f]の不動点とは、[f(x) = x] となる入力 [x] のことです。
    ここでは、型 [(Nat->Nat)->(Nat->Nat)] を持つ関数[F]の不動点は、[Nat->Nat]型の関数[f]のうち、[F f]が[f]と同じように振る舞うものです。） *)

(* begin hide *)
(** Syntax:

       t ::=                Terms
           | fix t             fixed-point operator
           | ...

   Reduction:

                                t1 ==> t1'
                            ------------------                        (ST_Fix1)
                            fix t1 ==> fix t1'

               --------------------------------------------         (ST_FixAbs)
               fix (\xf:T1.t2) ==> [xf:=fix (\xf:T1.t2)] t2

   Typing:

                           Gamma |- t1 : T1->T1
                           --------------------                         (T_Fix)
                           Gamma |- fix t1 : T1
*)
(* end hide *)
(** 構文:
<<
       t ::=                項
           | fix t             不動点演算子
           | ... 
>>
   簡約:
<<
                                t1 ==> t1' 
                            ------------------                       (ST_Fix1) 
                            fix t1 ==> fix t1' 
 
               --------------------------------------------         (ST_FixAbs) 
               fix (\xf:T1.t2) ==> [xf:=fix (\xf:T1.t2)] t2 
>>
   型付け:
<<
                           Gamma |- t1 : T1->T1 
                           --------------------                        (T_Fix) 
                           Gamma |- fix t1 : T1 
>>
 *)

(* begin hide *)
(** Let's see how [ST_FixAbs] works by reducing [fact 3 = fix F 3],
    where 

    F = (\f. \x. if x=0 then 1 else x * (f (pred x)))
>> 
    (type annotations are omitted for brevity).

    fix F 3

[==>] [ST_FixAbs] + [ST_App1]

    (\x. if x=0 then 1 else x * (fix F (pred x))) 3

[==>] [ST_AppAbs]

    if 3=0 then 1 else 3 * (fix F (pred 3))

[==>] [ST_If0_Nonzero]

    3 * (fix F (pred 3))

[==>] [ST_FixAbs + ST_Mult2]

    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 3))

[==>] [ST_PredNat + ST_Mult2 + ST_App2]

    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 2)

[==>] [ST_AppAbs + ST_Mult2]

    3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))

[==>] [ST_If0_Nonzero + ST_Mult2]

    3 * (2 * (fix F (pred 2)))

[==>] [ST_FixAbs + 2 x ST_Mult2]

    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))

[==>] [ST_PredNat + 2 x ST_Mult2 + ST_App2]

    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 1))

[==>] [ST_AppAbs + 2 x ST_Mult2]

    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))

[==>] [ST_If0_Nonzero + 2 x ST_Mult2]

    3 * (2 * (1 * (fix F (pred 1))))

[==>] [ST_FixAbs + 3 x ST_Mult2]

    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))

[==>] [ST_PredNat + 3 x ST_Mult2 + ST_App2]

    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 0)))

[==>] [ST_AppAbs + 3 x ST_Mult2]

    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))

[==>] [ST_If0Zero + 3 x ST_Mult2]

    3 * (2 * (1 * 1))

[==>] [ST_MultNats + 2 x ST_Mult2]

    3 * (2 * 1)

[==>] [ST_MultNats + ST_Mult2]

    3 * 2

[==>] [ST_MultNats]

    6
*)
(* end hide *)
(** [fact 3 = fix F 3] の動きを追うことで、 [ST_FixAbs] がどのように動くのか見ます。
    ここで、[F]は以下の式とします。
<<
    F = (\f. \x. if x=0 then 1 else x * (f (pred x))) 
>> 
    （可読性のために型注釈は省略します。）
<<
    fix F 3 
>>
[==>] [ST_FixAbs] + [ST_App1] 
<<
    (\x. if x=0 then 1 else x * (fix F (pred x))) 3 
>>
[==>] [ST_AppAbs] 
<<
    if 3=0 then 1 else 3 * (fix F (pred 3)) 
>>
[==>] [ST_If0_Nonzero] 
<<
    3 * (fix F (pred 3)) 
>>
[==>] [ST_FixAbs + ST_Mult2] 
<<
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 3)) 
>>
[==>] [ST_PredNat + ST_Mult2 + ST_App2] 
<<
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 2) 
>>
[==>] [ST_AppAbs + ST_Mult2] 
<<
    3 * (if 2=0 then 1 else 2 * (fix F (pred 2))) 
>>
[==>] [ST_If0_Nonzero + ST_Mult2] 
<<
    3 * (2 * (fix F (pred 2))) 
>>
[==>] [ST_FixAbs + 2 x ST_Mult2] 
<<
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 2))) 
>>
[==>] [ST_PredNat + 2 x ST_Mult2 + ST_App2] 
<<
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 1)) 
>>
[==>] [ST_AppAbs + 2 x ST_Mult2] 
<<
    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1)))) 
>>
[==>] [ST_If0_Nonzero + 2 x ST_Mult2] 
<<
    3 * (2 * (1 * (fix F (pred 1)))) 
>>
[==>] [ST_FixAbs + 3 x ST_Mult2] 
<<
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 1)))) 
>>
[==>] [ST_PredNat + 3 x ST_Mult2 + ST_App2] 
<<
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 0))) 
>>
[==>] [ST_AppAbs + 3 x ST_Mult2] 
<<
    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0))))) 
>>
[==>] [ST_If0Zero + 3 x ST_Mult2] 
<<
    3 * (2 * (1 * 1)) 
>>
[==>] [ST_MultNats + 2 x ST_Mult2] 
<<
    3 * (2 * 1) 
>>
[==>] [ST_MultNats + ST_Mult2] 
<<
    3 * 2 
>>
[==>] [ST_MultNats] 
<<
    6
>>
 *)

(* begin hide *)
(** One important point to note is that, unlike [Fixpoint]
    definitions in Coq, there is nothing to prevent functions defined
    using [fix] from diverging. *)
(* end hide *)
(** 重要な点として、Coqの[Fixpoint]と異なり、[fix]での定義は発散するような関数も書けます。 *)

(* begin hide *)
(** **** Exercise: 1 star, optional (halve_fix)  *)
(* end hide *)
(** **** 練習問題: ★, optional (halve_fix) *)
(* begin hide *)
(** Translate this informal recursive definition into one using [fix]:

      halve =
        \x:Nat.
           if x=0 then 0
           else if (pred x)=0 then 0
           else 1 + (halve (pred (pred x))))

(* FILL IN HERE *)
*)
(* end hide *)
(** 次の再帰的定義を[fix]を用いた定義に直しなさい:
<<
      halve = 
        \x:Nat. 
           if x=0 then 0 
           else if (pred x)=0 then 0 
           else 1 + (halve (pred (pred x)))) 
>>
(* FILL IN HERE *) 
 *)
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, optional (fact_steps)  *)
(* end hide *)
(** **** 練習問題: ★, optional (fact_steps) *)
(* begin hide *)
(** Write down the sequence of steps that the term [fact 1] goes
    through to reduce to a normal form (assuming the usual reduction
    rules for arithmetic operations).

    (* FILL IN HERE *)
*)
(* end hide *)
(** 項 [fact 1] が正規形まで簡約されるステップ列を書き下しなさい（ただし、算術演算については通常の簡約規則を仮定します）。
 
    (* FILL IN HERE *) 
 *)
(** [] *)

(* begin hide *)
(** The ability to form the fixed point of a function of type [T->T]
    for any [T] has some surprising consequences.  In particular, it
    implies that _every_ type is inhabited by some term.  To see this,
    observe that, for every type [T], we can define the term

    fix (\x:T.x)

    By [T_Fix]  and [T_Abs], this term has type [T].  By [ST_FixAbs]
    it reduces to itself, over and over again.  Thus it is a
    _diverging element_ of [T].

    More usefully, here's an example using [fix] to define a
    two-argument recursive function:

    equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if m=0 then iszero n
             else if n=0 then false
             else eq (pred m) (pred n))
*)
(* end hide *)
(** 任意の[T]について型 [T->T] の関数の不動点が記述できる形ができたことから、驚くようなことが起こります。
    特に、すべての型が何らかの項に住まれている(inhabited)ということが導かれます。
    これを確認するため、すべての型[T]について、項
[[
    fix (\x:T.x) 
]]
    が定義できることを見てみましょう。
    [T_Fix]と[T_Abs]から、この項は型[T]を持ちます。
    [ST_FixAbs]より、この項を簡約すると何度やっても自分自身になります。
    したがって、この項は[T]の発散要素(_diverging element_)です。
 
    より有用なこととして、次は[fix]を使って2引数の再帰関数を定義する例です:
<<
    equal = 
      fix 
        (\eq:Nat->Nat->Bool. 
           \m:Nat. \n:Nat. 
             if m=0 then iszero n 
             else if n=0 then false 
             else eq (pred m) (pred n)) 
>>
 *)
(* begin hide *)
(** And finally, here is an example where [fix] is used to define a
    _pair_ of recursive functions (illustrating the fact that the type
    [T1] in the rule [T_Fix] need not be a function type):

      evenodd =
        fix
          (\eo: (Nat->Bool * Nat->Bool).
             let e = \n:Nat. if n=0 then true  else eo.snd (pred n) in
             let o = \n:Nat. if n=0 then false else eo.fst (pred n) in
             (e,o))

      even = evenodd.fst
      odd  = evenodd.snd
*)
(* end hide *)
(** そして最後に、次は[fix]を使って再帰関数の対を定義する例です（この例は、規則[T_Fix]の型[T1]は関数型ではなくてもよいことを示しています）:
<<
      evenodd = 
        fix 
          (\eo: (Nat->Bool * Nat->Bool). 
             let e = \n:Nat. if n=0 then true  else eo.snd (pred n) in 
             let o = \n:Nat. if n=0 then false else eo.fst (pred n) in 
             (e,o)) 
 
      even = evenodd.fst 
      odd  = evenodd.snd 
>>
 *)

(* ================================================================= *)
(* begin hide *)
(** ** Records *)
(* end hide *)
(** ** レコード *)

(* begin hide *)
(** As a final example of a basic extension of the STLC, let's look
    briefly at how to define _records_ and their types.  Intuitively,
    records can be obtained from pairs by two straightforward
    generalizations: they are n-ary (rather than just binary) and
    their fields are accessed by _label_ (rather than position). *)
(* end hide *)
(** STLCの基本拡張の最後の例として、
    レコード(_records_)とその型をどのように形式化するかをちょっと見てみましょう。
    直観的には、レコードは組に二つの一般化をほどこすことで得られます。
    （二つの代わりに）n-要素の組とすること、そして（位置の代わりに）「ラベル(_label_)」で要素へアクセスできることです。 *)

(* begin hide *)
(** Syntax:

       t ::=                          Terms
           | {i1=t1, ..., in=tn}         record
           | t.i                         projection
           | ...

       v ::=                          Values
           | {i1=v1, ..., in=vn}         record value
           | ...

       T ::=                          Types
           | {i1:T1, ..., in:Tn}         record type
           | ...

   The generalization from products should be pretty obvious.  But 
   it's worth noticing the ways in which what we've actually written is
   even _more_ informal than the informal syntax we've used in previous 
   sections and chapters: we've used "[...]" in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side condition that the labels of a record should not contain any
   repetitions. *)
(* end hide *)
(** 構文:
<<
       t ::=                          項
           | {i1=t1, ..., in=tn}         レコード
           | t.i                         射影
           | ... 
 
       v ::=                          値
           | {i1=v1, ..., in=vn}         レコード値
           | ... 
 
       T ::=                          型
           | {i1:T1, ..., in:Tn}         レコード型
           | ... 
>>
   直積からの一般化はかなり明確です。
   しかし、ここで実際に記述したものは、以前の章で書いたものよりかなり非形式的であることは注意しておくべきです。
   いろいろなところで、"[...]"を「これらを何個か」という意味で使っていますし、レコードに同じラベルが繰り返し出てきてはいけない、という通常の付加条件を明示的に述べることを省いています。 *)

(* begin hide *)
(**
   Reduction:

                              ti ==> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti, ...}
                 ==> {i1=v1, ..., im=vm, in=ti', ...}

                              t1 ==> t1'
                            --------------                           (ST_Proj1)
                            t1.i ==> t1'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i ==> vi

   Again, these rules are a bit informal.  For example, the first rule
   is intended to be read "if [ti] is the leftmost field that is not a
   value and if [ti] steps to [ti'], then the whole record steps..."
   In the last rule, the intention is that there should only be one
   field called i, and that all the other fields must contain values. *)
(* end hide *)
(** 
   簡約:
<<
                              ti ==> ti' 
                 ------------------------------------                  (ST_Rcd) 
                     {i1=v1, ..., im=vm, in=ti, ...} 
                 ==> {i1=v1, ..., im=vm, in=ti', ...} 
 
                              t1 ==> t1' 
                            --------------                           (ST_Proj1) 
                            t1.i ==> t1'.i 
 
                      -------------------------                    (ST_ProjRcd) 
                      {..., i=vi, ...}.i ==> vi 
>>
   これらの規則も、やはりちょっと非形式的です。
   例えば、最初の規則は「[ti]が値でないフィールドのうち最も左のもので、[ti]は[ti']にステップで進むならば、レコード全体のステップは...」と読まれることを意図しています。
   最後の規則では、i と呼ばれるフィールドは1つだけで、他のすべてのフィールドは値を持っていることを意図しています。 *)

(* begin hide *)
(**
   The typing rules are also simple:

            Gamma |- t1 : T1     ...     Gamma |- tn : Tn
          --------------------------------------------------            (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                    Gamma |- t : {..., i:Ti, ...}
                    -----------------------------                      (T_Proj)
                          Gamma |- t.i : Ti
*)
(* end hide *)
(** 
   型付けも簡単です:
<<
            Gamma |- t1 : T1     ...     Gamma |- tn : Tn 
          --------------------------------------------------            (T_Rcd) 
          Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn} 
 
                    Gamma |- t : {..., i:Ti, ...} 
                    -----------------------------                      (T_Proj) 
                          Gamma |- t.i : Ti 
>>
 *)

(* begin hide *)
(** There are several ways to approach formalizing the above
    definitions.

      - We can directly formalize the syntactic forms and inference
        rules, staying as close as possible to the form we've given
        them above.  This is conceptually straightforward, and it's
        probably what we'd want to do if we were building a real
        compiler (in particular, it will allow us to print error
        messages in the form that programmers will find easy to
        understand).  But the formal versions of the rules will not be
        very pretty or easy to work with, because all the [...]s above
        will have to be replaced with explicit quantifications or
        comprehensions.  For this reason, records are not included in
        the extended exercise at the end of this chapter.  (It is
        still useful to discuss them informally here because they will
        help motivate the addition of subtyping to the type system
        when we get to the [Sub] chapter.)

      - Alternatively, we could look for a smoother way of presenting
        records -- for example, a binary presentation with one
        constructor for the empty record and another constructor for
        adding a single field to an existing record, instead of a
        single monolithic constructor that builds a whole record at
        once.  This is the right way to go if we are primarily
        interested in studying the metatheory of the calculi with
        records, since it leads to clean and elegant definitions and
        proofs.  Chapter [Records] shows how this can be done.

      - Finally, if we like, we can avoid formalizing records
        altogether, by stipulating that record notations are just
        informal shorthands for more complex expressions involving
        pairs and product types.  We sketch this approach in the next
        section. *)
(* end hide *)
(** 上述の定義を精密にする方法はいくつもあります。
 
      - 構文の形と推論規則を、上記の形になるべく近いまま直接形式化するという方法があります。
        これは概念的に「直球」で、もし本当のコンパイラを作るならば、おそらくいちばん合っているでしょう。
        特に、形式化の中にエラーメッセージのプリントを含めることができるので、プログラマが理解するのが容易になるでしょう。
        しかし、規則の形式化版はまったくきれいにはなりませんし、扱いも難しいものになります。
        というのも、[...]で省略した部分を全て明示的に定量化し、理解しなければならないからです。
        このため、レコードによる拡張は本章の追加課題にも入れていません。
        （それでもここで非形式的に議論しておくのは、[Sub]章における部分型付けのモチベーションになるからです。）
 
      - 別の方法として、レコードを表現する、よりスムーズな方法を探すことができます。
        例えば、1つのコンストラクタでレコード全体を一度に作るのではなく、空レコードに対応する1つのコンストラクタと、存在するレコードに1つのフィールドを追加する別のコンストラクタの2つで表現するという方法があります。
        この方法は、レコードについての計算のメタ理論に一番の興味がある場合には正しい方法です。
        なぜなら、この方法をとると、きれいで優雅な定義と証明が得られるからです。
        [Records]章では、この方法がどのように行えるかを示しています。
 
      - 最後に、望むならば、レコードを形式化することを完全に避けることができます。
        このためには、レコード記法は、対と直積型を含むより複雑な式の単なる非形式的な略記法である、と規定します。
        次節では、このアプローチの概略を与えます。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Encoding Records (Optional) *)
(* end hide *)
(** *** レコードのエンコード (Optional) *)

(* begin hide *)
(** Let's see how records can be encoded using just pairs and [unit].  

    First, observe that we can encode arbitrary-size _tuples_ using
    nested pairs and the [unit] value.  To avoid overloading the pair
    notation [(t1,t2)], we'll use curly braces without labels to write
    down tuples, so [{}] is the empty tuple, [{5}] is a singleton
    tuple, [{5,6}] is a 2-tuple (morally the same as a pair),
    [{5,6,7}] is a triple, etc.

      {}                 ---->  unit
      {t1, t2, ..., tn}  ---->  (t1, trest)
                                where {t2, ..., tn} ----> trest

    Similarly, we can encode tuple types using nested product types:

      {}                 ---->  Unit
      {T1, T2, ..., Tn}  ---->  T1 * TRest
                                where {T2, ..., Tn} ----> TRest

    The operation of projecting a field from a tuple can be encoded
    using a sequence of second projections followed by a first projection:

      t.0        ---->  t.fst
      t.(n+1)    ---->  (t.snd).n

    Next, suppose that there is some total ordering on record labels,
    so that we can associate each label with a unique natural number.
    This number is called the _position_ of the label.  For example,
    we might assign positions like this:

      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      bar     1395
      ...     ...
      foo     4460
      ...     ...

    We use these positions to encode record values as tuples (i.e., as
    nested pairs) by sorting the fields according to their positions.
    For example:

      {a=5, b=6}      ---->   {5,6}
      {a=5, c=7}      ---->   {5,unit,7}
      {c=7, a=5}      ---->   {5,unit,7}
      {c=5, b=3}      ---->   {unit,3,5}
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}

    Note that each field appears in the position associated with its
    label, that the size of the tuple is determined by the label with
    the highest position, and that we fill in unused positions with
    [unit].

    We do exactly the same thing with record types:

      {a:Nat, b:Nat}      ---->   {Nat,Nat}
      {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}

    Finally, record projection is encoded as a tuple projection from
    the appropriate position:

      t.l  ---->  t.(position of l)

    It is not hard to check that all the typing rules for the original
    "direct" presentation of records are validated by this
    encoding.  (The reduction rules are "almost validated" -- not
    quite, because the encoding reorders fields.) *)
(* end hide *)
(** では、レコードを[unit]と対で表現する方法を見ていきましょう。
 
    最初に、任意のサイズの「組(_tuple_)」が対と[unit]値のネストでエンコードできることを確認します。
    対の記法 [(t1,t2)] を混用するのを避けるため、組を書き下すためにはラベルを持たない中カッコ([{..}])を使います。
    つまり、[{}]は0個組、[{5}]は一つ組、[{5,6}]は二つ組（事実上対と同じ）、[{5,6,7}]は三つ組、等です。
<<
    {}                 ---->  unit 
    {t1, t2, ..., tn}  ---->  (t1, trest) 
                              ただし {t2, ..., tn} ----> trest
>>
    同様に、組の型を直積型のネストでエンコードすることができます。
<<
    {}                 ---->  Unit 
    {T1, T2, ..., Tn}  ---->  T1 * TRest 
                              ただし {T2, ..., Tn} ----> TRest
>>
    組のフィールドの射影演算は、第2射影の列に続く第1射影としてエンコードできます:
<<
    t.0        ---->  t.fst 
    t.(n+1)    ---->  (t.snd).n 
>>
 
    次に、レコードラベルに何らかの全順序があり、そのため各ラベルに一意に自然数が関連づけられると仮定します。
    この数をラベルの「ポジション(_position_)」と呼びます。
    例えば、以下のようにポジションが定められるとします:
<<
      LABEL   POSITION 
      a       0 
      b       1 
      c       2 
      ...     ... 
      bar     1395 
      ...     ... 
      foo     4460 
      ...     ... 
>>
    このポジションを、レコード値を組(つまりネストされた対)でエンコードするために使います。
    つまり、フィールドをそのポジションでソートします。
    例えば:
<<
      {a=5, b=6}      ---->   {5,6} 
      {a=5, c=7}      ---->   {5,unit,7} 
      {c=7, a=5}      ---->   {5,unit,7} 
      {c=5, b=3}      ---->   {unit,3,5} 
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8} 
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8} 
>>
    以下のことに注意します。
    各フィールドはそのラベルに関連づけられたポジションに現れます。
    また、組の大きさは、最大のポジションを持つラベルによって決定されます。
    そして、使われていないポジションは[unit]で埋められます。
 
    レコードの型についてもまったくおなじことをします:
<<
      {a:Nat, b:Nat}      ---->   {Nat,Nat} 
      {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat} 
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat} 
>>
    最後に、レコードの射影は適切なポジションについての組の射影でエンコードされます:
<<
      t.l  ---->  t.(position of l) 
>>
    レコードのオリジナルの「直接の」表現に対するすべての型付け規則が、このエンコードで正しいことをチェックするのは難しいことではありません。
    （簡約規則は正しさを「ほぼ」確認できます。完全に、ではありません。
    なぜなら、フィールドの並べ直しによってフィールドの簡約順序が変わりうるためです。） *)

(* begin hide *)
(** Of course, this encoding will not be very efficient if we
    happen to use a record with label [foo]!  But things are not
    actually as bad as they might seem: for example, if we assume that
    our compiler can see the whole program at the same time, we can
    _choose_ the numbering of labels so that we assign small positions
    to the most frequently used labels.  Indeed, there are industrial
    compilers that essentially do this! *)
(* end hide *)
(** もちろん、ラベル[foo]を持つレコードをたまたま使ったときには、このエンコードはあまり効率的ではありません。
    しかしこの問題は見た目ほど深刻ではありません。
    もし、コンパイラがプログラム全体を同時に見ることができると仮定するなら、ラベルの番号づけをうまく選んで、一番よく使われるラベルに小さいポジションを与えることができます。
    実際、商用のコンパイラで本質的にこれをやっているものもあります! *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Variants (Optional) *)
(* end hide *)
(** *** バリアント (Optional) *)

(* begin hide *)
(** Just as products can be generalized to records, sums can be
    generalized to n-ary labeled types called _variants_.  Instead of
    [T1+T2], we can write something like [<l1:T1,l2:T2,...ln:Tn>]
    where [l1],[l2],... are field labels which are used both to build
    instances and as case arm labels.

    These n-ary variants give us almost enough mechanism to build
    arbitrary inductive data types like lists and trees from
    scratch -- the only thing missing is a way to allow _recursion_ in
    type definitions.  We won't cover this here, but detailed
    treatments can be found in many textbooks -- e.g., Types and
    Programming Languages [Pierce 2002]. *)
(* end hide *)
(** 直積がレコードに一般化できたのと同様、直和は n-個のラベルを持った型「バリアント」(_variants_)に一般化できます。
    [T1+T2] の代わりに [<l1:T1,l2:T2,...ln:Tn>] のように書くことができます。
    ここで[l1]、[l2]、... はフィールドラベルで、インスタンスの構成と、case のラベルの両方に使われます。
 
    n-個のバリアントは、リストや木構造のような任意の帰納的データ型をゼロから構築するのに必要なメカニズムのほとんどを与えます。
    唯一足りないのは、型定義の再帰です。ここではこの話題は扱いません。
    ただ、詳細な扱いはいろいろなテキストブックに書かれています。
    例えば "Types and Programming Languages" [Pierce 2002] です。*)

(* ################################################################# *)
(* begin hide *)
(** * Exercise: Formalizing the Extensions *)
(* end hide *)
(** * 練習問題: 拡張を形式化する *)

(* begin hide *)
(** **** Exercise: 5 stars (STLC_extensions)  *)
(* end hide *)
(** **** 練習問題: ★★★★★ (STLC_extensions) *)
(* begin hide *)
(** In this exercise, you will formalize some of the extensions
    described in this chapter.  We've provided the necessary additions
    to the syntax of terms and types, and we've included a few
    examples that you can test your definitions with to make sure they
    are working as expected.  You'll fill in the rest of the
    definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:
     - numbers
     - sums
     - lists
     - unit

    You need to complete the implementations for:
     - pairs 
     - let (which involves binding)
     - [fix]

    A good strategy is to work on the extensions one at a time, in two
    passes, rather than trying to work through the file from start to
    finish in a single pass.  For each definition or proof, begin by
    reading carefully through the parts that are provided for you,
    referring to the text in the [Stlc] chapter for high-level
    intuitions and the embedded comments for detailed mechanics. *)
(* end hide *)
(** この課題では、本章で説明した拡張の形式化をしてもらいます。
    項と型の構文の必要な拡張は提示しておきました。
    また、読者が、自分の定義が期待された通りに動作するかをテストすることができるように、いくつかの例を示しておきました。
    読者は定義の残りの部分を埋め、それに合わせて証明を拡張しなさい。
 
    （訳注：この章のここ以降はすべてこの練習問題の内部です。
    埋めるのはその中の「ここを埋めなさい」という部分です。
    なお、以下の記述はCoq記述内の埋め込みコメントを読まないと理解できない部分があると思いますが、HTML化したものでは埋め込みコメントが表示されていないかもしれません。
    その場合はHTML化前のCoqソースを見てください。）
 
    取りかかるために、以下のものに関しては実装しておきました:
      - 数値
      - 直和
      - リスト
      - Unit型
 
    読者は、以下のものに関する実装を完成させなさい:
      - 直積
      - let (束縛を含む)
      - [fix]
 
    よい戦略は、ファイルの最初から最後までを1パスで行おうとせずに、2パスで拡張項目を一つづつやることです。
    定義または証明のそれぞれについて、提示されたパーツを注意深く読むことから始めなさい。
    その際に、ハイレベルの直観については[Stlc]章のテキストを参照し、詳細の機構については、埋め込まれたコメントを参照しなさい。 *)

Module STLCExtended.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Syntax *)
(* end hide *)
(** *** 構文 *)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty
  | TUnit  : ty
  | TProd  : ty -> ty -> ty
  | TSum   : ty -> ty -> ty
  | TList  : ty -> ty.

Inductive tm : Type :=
  (* pure STLC *)
(** <<
  (* 拡張されていないSTLC *)
>> *)
  | tvar : string -> tm
  | tapp : tm -> tm -> tm
  | tabs : string -> ty -> tm -> tm
  (* numbers *)
(** <<
  (* 数値 *)
>> *)
  | tnat : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm
  (* pairs *)
(** <<
  (* 対 *)
>> *)
  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm
  (* units *)
(** <<
  (* unit *) 
>> *)
  | tunit : tm
  (* let *)
(** <<
  (* let *)
>> *)
  | tlet : string -> tm -> tm -> tm
          (* i.e., [let x = t1 in t2] *)
          (** <<
          (* 例えば、[let x = t1 in t2] *)
>> *)
  (* sums *)
(** <<
  (* 直和 *)
>> *)
  | tinl : ty -> tm -> tm
  | tinr : ty -> tm -> tm
  | tcase : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [case t0 of inl x1 => t1 | inr x2 => t2] *)
(** <<
          (* つまり、[case t0 of inl x1 => t1 | inr x2 => t2] *)
>> *)
  (* lists *)
(** <<
  (* リスト *)
>> *)
  | tnil : ty -> tm
  | tcons : tm -> tm -> tm
  | tlcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [lcase t1 of | nil => t2 | x::y => t3] *)
(** <<
           (* つまり、[lcase t1 of | nil => t2 | x::y => t3] *)
>> *)
  (* fix *)
(** <<
  (* fix *) 
>> *)
  | tfix  : tm -> tm.

(* begin hide *)
(** Note that, for brevity, we've omitted booleans and instead
    provided a single [if0] form combining a zero test and a
    conditional.  That is, instead of writing

       if x = 0 then ... else ...

    we'll write this:

       if0 x then ... else ...
*)
(* end hide *)
(** なお、簡潔にするため、ブール値をなくし、その代わりゼロテストと条件分岐を組み合わせた [if0] 構文を提供しています。
    つまり、
<<
       if x = 0 then ... else ... 
>>
    と書く代わりに、次のように書きます:
<<
       if0 x then ... else ... 
>>
 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Substitution *)
(* end hide *)
(** *** 置換 *)

Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y =>
      if beq_string x y then s else t
  | tabs y T t1 =>
      tabs y T (if beq_string x y then t1 else (subst x s t1))
  | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
  | tnat n =>
      tnat n
  | tsucc t1 =>
      tsucc (subst x s t1)
  | tpred t1 =>
      tpred (subst x s t1)
  | tmult t1 t2 =>
      tmult (subst x s t1) (subst x s t2)
  | tif0 t1 t2 t3 =>
      tif0 (subst x s t1) (subst x s t2) (subst x s t3)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  | tunit => tunit
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  | tinl T t1 =>
      tinl T (subst x s t1)
  | tinr T t1 =>
      tinr T (subst x s t1)
  | tcase t0 y1 t1 y2 t2 =>
      tcase (subst x s t0)
         y1 (if beq_string x y1 then t1 else (subst x s t1))
         y2 (if beq_string x y2 then t2 else (subst x s t2))
  | tnil T =>
      tnil T
  | tcons t1 t2 =>
      tcons (subst x s t1) (subst x s t2)
  | tlcase t1 t2 y1 y2 t3 =>
      tlcase (subst x s t1) (subst x s t2) y1 y2
        (if beq_string x y1 then
           t3
         else if beq_string x y2 then t3
              else (subst x s t3))
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  | _ => t  (* ... and delete this line *)
(** <<
  (* ...そして上の行を消しなさい。 *)
>> *)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Reduction *)
(* end hide *)
(** *** 簡約 *)

(* begin hide *)
(** Next we define the values of our language. *)
(* end hide *)
(** 次にこの言語の値を定義します。 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  (* Numbers are values: *)
  | v_nat : forall n1,
      value (tnat n1)
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpair v1 v2)
  (* A unit is always a value *)
  | v_unit : value tunit
  (* A tagged value is a value:  *)
  | v_inl : forall v T,
      value v ->
      value (tinl T v)
  | v_inr : forall v T,
      value v ->
      value (tinr T v)
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T, value (tnil T)
  | v_lcons : forall v1 vl,
      value v1 ->
      value vl ->
      value (tcons v1 vl).

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tapp (tabs x T11 t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  (* nats *)
  | ST_Succ1 : forall t1 t1',
       t1 ==> t1' ->
       (tsucc t1) ==> (tsucc t1')
  | ST_SuccNat : forall n1,
       (tsucc (tnat n1)) ==> (tnat (S n1))
  | ST_Pred : forall t1 t1',
       t1 ==> t1' ->
       (tpred t1) ==> (tpred t1')
  | ST_PredNat : forall n1,
       (tpred (tnat n1)) ==> (tnat (pred n1))
  | ST_Mult1 : forall t1 t1' t2,
       t1 ==> t1' ->
       (tmult t1 t2) ==> (tmult t1' t2)
  | ST_Mult2 : forall v1 t2 t2',
       value v1 ->
       t2 ==> t2' ->
       (tmult v1 t2) ==> (tmult v1 t2')
  | ST_MultNats : forall n1 n2,
       (tmult (tnat n1) (tnat n2)) ==> (tnat (mult n1 n2))
  | ST_If01 : forall t1 t1' t2 t3,
       t1 ==> t1' ->
       (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  | ST_If0Zero : forall t2 t3,
       (tif0 (tnat 0) t2 t3) ==> t2
  | ST_If0Nonzero : forall n t2 t3,
       (tif0 (tnat (S n)) t2 t3) ==> t3
  (* pairs *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* sums *)
  | ST_Inl : forall t1 t1' T,
        t1 ==> t1' ->
        (tinl T t1) ==> (tinl T t1')
  | ST_Inr : forall t1 t1' T,
        t1 ==> t1' ->
        (tinr T t1) ==> (tinr T t1')
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 ==> t0' ->
        (tcase t0 x1 t1 x2 t2) ==> (tcase t0' x1 t1 x2 t2)
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinl T v0) x1 t1 x2 t2) ==> [x1:=v0]t1
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T,
        value v0 ->
        (tcase (tinr T v0) x1 t1 x2 t2) ==> [x2:=v0]t2
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 ==> t1' ->
       (tcons t1 t2) ==> (tcons t1' t2)
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 ==> t2' ->
       (tcons v1 t2) ==> (tcons v1 t2')
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 ==> t1' ->
       (tlcase t1 t2 x1 x2 t3) ==> (tlcase t1' t2 x1 x2 t3)
  | ST_LcaseNil : forall T t2 x1 x2 t3,
       (tlcase (tnil T) t2 x1 x2 t3) ==> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1  ->
       value vl  ->
       (tlcase (tcons v1 vl) t2 x1 x2 t3) ==> (subst x2 vl (subst x1 v1 t3))
  (* fix *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)

where "t1 '==>' t2" := (step t1 t2).

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Typing *)
(* end hide *)
(** *** 型付け *)

Definition context := partial_map ty.

(* begin hide *)
(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)
(* end hide *)
(** 次に型付け規則を定義します。
    上述の推論規則のほとんど直接の転写です。*)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (update Gamma x T11) |- t12 \in T12 ->
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) ->
      Gamma |- t2 \in T1 ->
      Gamma |- (tapp t1 t2) \in T2
  (* nats *)
  | T_Nat : forall Gamma n1,
      Gamma |- (tnat n1) \in TNat
  | T_Succ : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- (tsucc t1) \in TNat
  | T_Pred : forall Gamma t1,
      Gamma |- t1 \in TNat ->
      Gamma |- (tpred t1) \in TNat
  | T_Mult : forall Gamma t1 t2,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in TNat ->
      Gamma |- (tmult t1 t2) \in TNat
  | T_If0 : forall Gamma t1 t2 t3 T1,
      Gamma |- t1 \in TNat ->
      Gamma |- t2 \in T1 ->
      Gamma |- t3 \in T1 ->
      Gamma |- (tif0 t1 t2 t3) \in T1
  (* pairs *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- (tinl T2 t1) \in (TSum T1 T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |- t2 \in T2 ->
      Gamma |- (tinr T1 t2) \in (TSum T1 T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T,
      Gamma |- t0 \in (TSum T1 T2) ->
      (update Gamma x1 T1) |- t1 \in T ->
      (update Gamma x2 T2) |- t2 \in T ->
      Gamma |- (tcase t0 x1 t1 x2 t2) \in T
  (* lists *)
  | T_Nil : forall Gamma T,
      Gamma |- (tnil T) \in (TList T)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in (TList T1) ->
      Gamma |- (tcons t1 t2) \in (TList T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |- t1 \in (TList T1) ->
      Gamma |- t2 \in T2 ->
      (update (update Gamma x2 (TList T1)) x1 T1) |- t3 \in T2 ->
      Gamma |- (tlcase t1 t2 x1 x2 t3) \in T2
  (* fix *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(* begin hide *)
(** ** Examples *)
(* end hide *)
(** ** 例 *)

(* begin hide *)
(** This section presents formalized versions of the examples from
    above (plus several more).  The ones at the beginning focus on
    specific features; you can use these to make sure your definition
    of a given feature is reasonable before moving on to extending the
    proofs later in the file with the cases relating to this feature.
    The later examples require all the features together, so you'll
    need to come back to these when you've got all the definitions
    filled in. *)
(* end hide *)
(** この節では上述の例（および追加のいくつか）の形式化版を示します。
    最初の方のものは、特定の拡張項目に焦点を当てています。
    ファイルの後の方の、その拡張項目について証明を拡張するところに進む前に、これらの例を使って拡張項目についての自分の定義が適切かを確認することができます。
    後の方の例はいろいろな拡張項目をまとめて必要とします。
    すべての定義を埋めた後、これらの例に戻ってみる必要があるでしょう。*)

Module Examples.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Preliminaries *)
(* end hide *)
(** *** 準備 *)

(* begin hide *)
(** First, let's define a few variable names: *)
(* end hide *)
(** 最初に、いくつか変数名を定義しましょう: *)

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation a := "a".
Notation f := "f".
Notation g := "g".
Notation l := "l".
Notation k := "k".
Notation i1 := "i1".
Notation i2 := "i2".
Notation processSum := "processSum".
Notation n := "n".
Notation eq := "eq".
Notation m := "m".
Notation evenodd := "evenodd".
Notation even := "even".
Notation odd := "odd".
Notation eo := "eo".

(* begin hide *)
(** Next, a bit of Coq hackery to automate searching for typing
    derivations.  You don't need to understand this bit in detail --
    just have a look over it so that you'll know what to look for if
    you ever find yourself needing to make custom extensions to
    [auto].

    The following [Hint] declarations say that, whenever [auto]
    arrives at a goal of the form [(Gamma |- (tapp e1 e1) \in T)], it
    should consider [eapply T_App], leaving an existential variable
    for the middle type T1, and similar for [lcase]. That variable
    will then be filled in during the search for type derivations for
    [e1] and [e2].  We also include a hint to "try harder" when
    solving equality goals; this is useful to automate uses of
    [T_Var] (which includes an equality as a precondition). *)
(* end hide *)
(** 次に、Coq にちょっと手を入れて、型の導出の検索を自動化します。
    詳細を理解する必要はまったくありません。
    ざっと眺めておけば、もし[auto]に独自の拡張をしなければならなくなったとき、何を調べれば良いかがわかるでしょう。
 
    以下の[Hint]宣言は、次のように言っています:
    [auto]が [(has_type G (tapp e1 e2) T)] という形のゴールに到達したときは常に、 [eapply T_App] を考えなさい。
    この結果、中間的な型 T1 の存在変数が残ります。
    （コメントになっている）[lcase]についても同様です。
    その存在変数は、[e1]と[e2]の型導出の探索の仮定で具体化されます。
    またヒントに、等号による比較の形のゴールを解く場合に「より困難なことを試しなさい」ということも追加します。
    これは、[T_Var]（これは事前条件に等号による比較を含みます）を自動的に使用するのに便利です。*)

Hint Extern 2 (has_type _ (tapp _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (has_type _ (tlcase _ _ _ _ _) _) =>
  eapply T_Lcase; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Numbers *)
(* end hide *)
(** *** 数値 *)

Module Numtest.

(* if0 (pred (succ (pred (2 * 0))) then 5 else 6 *)
(** <<
   if0 (pred (succ (pred (2 * 0)))) then 5 else 6
>>
*)
Definition test :=
  tif0
    (tpred
      (tsucc
        (tpred
          (tmult
            (tnat 2)
            (tnat 0)))))
    (tnat 5)
    (tnat 6).

(* begin hide *)
(** Remove the comment braces once you've implemented enough of the
    definitions that you think this should work. *)
(* end hide *)
(** 動くだけ定義が十分に行えたと思ったなら、以降の[Example]のコメントをはずしなさい。*)

(* 
Example typechecks :
  empty |- test \in TNat.
Proof.
  unfold test.
  (* This typing derivation is quite deep, so we need 
     to increase the max search depth of [auto] from the 
     default 5 to 10. *)
  auto 10.
Qed.

Example numtest_reduces :
  test ==>* tnat 5.
Proof.
  unfold test. normalize.
Qed.
*)
(** <<
(* 
Example typechecks : 
  empty |- test \in TNat. 
Proof. 
  unfold test. 
  (* この型導出は非常に深く、そのため[auto]の最大探索深度を、
     デフォルトの5から10に上げなければなりません。 *)
  auto 10. 
Qed. 
 
Example numtest_reduces : 
  test ==>* tnat 5. 
Proof. 
  unfold test. normalize. 
Qed. 
 *)
>> *)

End Numtest.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Products *)
(* end hide *)
(** *** 直積 *)

Module Prodtest.

(* ((5,6),7).fst.snd *)
(** <<
   ((5,6),7).fst.snd
>>
*)
Definition test :=
  tsnd
    (tfst
      (tpair
        (tpair
          (tnat 5)
          (tnat 6))
        (tnat 7))).

(* 
Example typechecks :
  empty |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.
*)
(** <<
(*
Example typechecks : 
  empty |- test \in TNat. 
Proof. unfold test. eauto 15. Qed. 
 
Example reduces : 
  test ==>* tnat 6. 
Proof. unfold test. normalize. Qed. 
*) 
>> *)

End Prodtest.

(* ----------------------------------------------------------------- *)
(** *** [let] *)

Module LetTest.

(* let x = pred 6 in succ x *)
(** <<
   let x = pred 6 in succ x
>>
*)
Definition test :=
  tlet
    x
    (tpred (tnat 6))
    (tsucc (tvar x)).

(* 
Example typechecks :
  empty |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* tnat 6.
Proof. unfold test. normalize. Qed.
*)
(** <<
(*
Example typechecks : 
  empty |- test \in TNat. 
Proof. unfold test. eauto 15. Qed. 
 
Example reduces : 
  test ==>* tnat 6. 
Proof. unfold test. normalize. Qed. 
*) 
>> *)

End LetTest.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Sums *)
(* end hide *)
(** *** 直和 *)

Module Sumtest1.

(* case (inl Nat 5) of
     inl x => x
   | inr y => y *)
(** <<
   case (inl Nat 5) of
     inl x => x 
   | inr y => y 
>>
*)

Definition test :=
  tcase (tinl TNat (tnat 5))
    x (tvar x)
    y (tvar y).

(* 
Example typechecks :
  empty |- test \in TNat.
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tnat 5).
Proof. unfold test. normalize. Qed.
*)
(** <<
(*
Example typechecks : 
  empty |- test \in TNat. 
Proof. unfold test. eauto 15. Qed. 
 
Example reduces : 
  test ==>* (tnat 5). 
Proof. unfold test. normalize. Qed. 
*) 
>> *)

End Sumtest1.

Module Sumtest2.

(* let processSum =
     \x:Nat+Nat.
        case x of
          inl n => n
          inr n => if0 n then 1 else 0 in
   (processSum (inl Nat 5), processSum (inr Nat 5))    *)
(** <<
   let processSum =
     \x:Nat+Nat. 
        case x of 
          inl n => n 
          inr n => if0 n then 1 else 0 in 
   (processSum (inl Nat 5), processSum (inr Nat 5))
>>
*)

Definition test :=
  tlet
    processSum
    (tabs x (TSum TNat TNat)
      (tcase (tvar x)
         n (tvar n)
         n (tif0 (tvar n) (tnat 1) (tnat 0))))
    (tpair
      (tapp (tvar processSum) (tinl TNat (tnat 5)))
      (tapp (tvar processSum) (tinr TNat (tnat 5)))).

(* 
Example typechecks :
  empty |- test \in (TProd TNat TNat).
Proof. unfold test. eauto 15. Qed.

Example reduces :
  test ==>* (tpair (tnat 5) (tnat 0)).
Proof. unfold test. normalize. Qed.
*)
(** <<
(*
Example typechecks : 
  empty |- test \in (TProd TNat TNat). 
Proof. unfold test. eauto 15. Qed. 
 
Example reduces : 
  test ==>* (tpair (tnat 5) (tnat 0)). 
Proof. unfold test. normalize. Qed. 
*) 
>> *)

End Sumtest2.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Lists *)
(* end hide *)
(** *** リスト *)

Module ListTest.

(* let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of
     nil => 0
   | x::y => x*x *)
(** <<
   let l = cons 5 (cons 6 (nil Nat)) in
   lcase l of 
     nil => 0 
   | x::y => x*x 
>>
*)

Definition test :=
  tlet l
    (tcons (tnat 5) (tcons (tnat 6) (tnil TNat)))
    (tlcase (tvar l)
       (tnat 0)
       x y (tmult (tvar x) (tvar x))).

(* 
Example typechecks :
  empty |- test \in TNat.
Proof. unfold test. eauto 20. Qed.

Example reduces :
  test ==>* (tnat 25).
Proof. unfold test. normalize. Qed.
*)
(** <<
(*
Example typechecks : 
  empty |- test \in TNat. 
Proof. unfold test. eauto 20. Qed. 
 
Example reduces : 
  test ==>* (tnat 25). 
Proof. unfold test. normalize. Qed. 
*) 
>> *)

End ListTest.

(* ----------------------------------------------------------------- *)
(** *** [fix] *)

Module FixTest1.

(* fact := fix
             (\f:nat->nat.
                \a:nat.
                   if a=0 then 1 else a * (f (pred a))) *)
(** <<
   fact := fix
             (\f:nat->nat. 
                \a:nat. 
                   if a=0 then 1 else a * (f (pred a)))
>>
*)
Definition fact :=
  tfix
    (tabs f (TArrow TNat TNat)
      (tabs a TNat
        (tif0
           (tvar a)
           (tnat 1)
           (tmult
              (tvar a)
              (tapp (tvar f) (tpred (tvar a))))))).

(* begin hide *)
(** (Warning: you may be able to typecheck [fact] but still have some
    rules wrong!) *)
(* end hide *)
(** （警告: [fact]の型チェックが通るかもしれませんが、それでもいくつかの規則が間違ったままです。） *)

(* 
Example fact_typechecks :
  empty |- fact \in (TArrow TNat TNat).
Proof. unfold fact. auto 10.
Qed.
*)
(** <<
(*
Example fact_typechecks : 
  empty |- fact \in (TArrow TNat TNat). 
Proof. unfold fact. auto 10. 
Qed. 
*) 
>> *)

(* 
Example fact_example:
  (tapp fact (tnat 4)) ==>* (tnat 24).
Proof. unfold fact. normalize. Qed.
*)
(** <<
(*
Example fact_example: 
  (tapp fact (tnat 4)) ==>* (tnat 24). 
Proof. unfold fact. normalize. Qed. 
*) 
>> *)

End FixTest1.

Module FixTest2.

(* map :=
     \g:nat->nat.
       fix
         (\f:[nat]->[nat].
            \l:[nat].
               case l of
               | [] -> []
               | x::l -> (g x)::(f l)) *)
(** <<
   map :=
     \g:nat->nat. 
       fix 
         (\f:[nat]->[nat]. 
            \l:[nat].  
               case l of 
               | [] -> [] 
               | x::l -> (g x)::(f l))
>> *) 
Definition map :=
  tabs g (TArrow TNat TNat)
    (tfix
      (tabs f (TArrow (TList TNat) (TList TNat))
        (tabs l (TList TNat)
          (tlcase (tvar l)
            (tnil TNat)
            a l (tcons (tapp (tvar g) (tvar a))
                         (tapp (tvar f) (tvar l))))))).

(* 
(* Make sure you've uncommented the last [Hint Extern] above... *)
Example map_typechecks :
  empty |- map \in
    (TArrow (TArrow TNat TNat)
      (TArrow (TList TNat)
        (TList TNat))).
Proof. unfold map. auto 10. Qed.

Example map_example :
  tapp (tapp map (tabs a TNat (tsucc (tvar a))))
         (tcons (tnat 1) (tcons (tnat 2) (tnil TNat)))
  ==>* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))).
Proof. unfold map. normalize. Qed.
*)
(** <<
(*
(* 上記の最後の [Hint Extern] のコメントが外されていることを確認すること... *)
Example map_typechecks : 
  empty |- map \in 
    (TArrow (TArrow TNat TNat) 
      (TArrow (TList TNat) 
        (TList TNat))). 
Proof. unfold map. auto 10. Qed. 
 
Example map_example : 
  tapp (tapp map (tabs a TNat (tsucc (tvar a)))) 
         (tcons (tnat 1) (tcons (tnat 2) (tnil TNat))) 
  ==>* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))). 
Proof. unfold map. normalize. Qed. 
*) 
>> *)

End FixTest2.

Module FixTest3.

(* equal =
      fix
        (\eq:Nat->Nat->Bool.
           \m:Nat. \n:Nat.
             if0 m then (if0 n then 1 else 0)
             else if0 n then 0
             else eq (pred m) (pred n))   *)
(** <<
   equal =
      fix 
        (\eq:Nat->Nat->Bool. 
           \m:Nat. \n:Nat. 
             if0 m then (if0 n then 1 else 0) 
             else if0 n then 0 
             else eq (pred m) (pred n))
>> *)

Definition equal :=
  tfix
    (tabs eq (TArrow TNat (TArrow TNat TNat))
      (tabs m TNat
        (tabs n TNat
          (tif0 (tvar m)
            (tif0 (tvar n) (tnat 1) (tnat 0))
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tapp (tvar eq)
                              (tpred (tvar m)))
                      (tpred (tvar n)))))))).

(** <<
(* 
Example equal_typechecks :
  empty |- equal \in (TArrow TNat (TArrow TNat TNat)).
Proof. unfold equal. auto 10.
Qed.
*)

(* 
Example equal_example1:
  (tapp (tapp equal (tnat 4)) (tnat 4)) ==>* (tnat 1).
Proof. unfold equal. normalize. Qed.
*)

(* 
Example equal_example2:
  (tapp (tapp equal (tnat 4)) (tnat 5)) ==>* (tnat 0).
Proof. unfold equal. normalize. Qed.
*)
>> *)

End FixTest3.

Module FixTest4.

(* let evenodd =
         fix
           (\eo: (Nat->Nat * Nat->Nat).
              let e = \n:Nat. if0 n then 1 else eo.snd (pred n) in
              let o = \n:Nat. if0 n then 0 else eo.fst (pred n) in
              (e,o)) in
    let even = evenodd.fst in
    let odd  = evenodd.snd in
    (even 3, even 4)
*)
(** <<
   let evenodd =
         fix 
           (\eo: (Nat->Nat * Nat->Nat). 
              let e = \n:Nat. if0 n then 1 else eo.snd (pred n) in 
              let o = \n:Nat. if0 n then 0 else eo.fst (pred n) in 
              (e,o)) in 
    let even = evenodd.fst in 
    let odd  = evenodd.snd in 
    (even 3, even 4) 
>>
 *)

Definition eotest :=
  tlet evenodd
    (tfix
      (tabs eo (TProd (TArrow TNat TNat) (TArrow TNat TNat))
        (tpair
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 1)
              (tapp (tsnd (tvar eo)) (tpred (tvar n)))))
          (tabs n TNat
            (tif0 (tvar n)
              (tnat 0)
              (tapp (tfst (tvar eo)) (tpred (tvar n))))))))
  (tlet even (tfst (tvar evenodd))
  (tlet odd (tsnd (tvar evenodd))
  (tpair
    (tapp (tvar even) (tnat 3))
    (tapp (tvar even) (tnat 4))))).

(** <<
(* 
Example eotest_typechecks :
  empty |- eotest \in (TProd TNat TNat).
Proof. unfold eotest. eauto 30.
Qed.
*)

(* 
Example eotest_example1:
  eotest ==>* (tpair (tnat 0) (tnat 1)).
Proof. unfold eotest. normalize. Qed.
*)
>> *)

End FixTest4.

End Examples.

(* ================================================================= *)
(* begin hide *)
(** ** Properties of Typing *)
(* end hide *)
(** ** 型付けの性質 *)

(* begin hide *)
(** The proofs of progress and preservation for this enriched system
    are essentially the same (though of course longer) as for the pure
    STLC. *)
(* end hide *)
(** 拡張したシステムの進行と保存の証明は、純粋な単純型付きラムダ計算のものと本質的に同じです（もちろん長くはなりますが）。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Progress *)
(* end hide *)
(** *** 進行 *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
(** <<
  (* 定理: empty |- t : T と仮定する。すると次のいずれかである:
       1. t は値、または
       2. ある t' について t ==> t' 
     証明: 与えられた型導出についての帰納法によって。 *)
>> *)
  intros t T Ht.
  remember empty as Gamma.
  generalize dependent HeqGamma.
  induction Ht; intros HeqGamma; subst.
  - (* T_Var *)
    (* The final rule in the given typing derivation cannot be 
       [T_Var], since it can never be the case that 
       [empty |- x : T] (since the context is empty). *)
(** <<
    (* 与えられた型導出の最後の規則が [T_Var] ではあり得ない。
       なぜなら、この規則では [empty |- x : T] にならないので
       (コンテキストが empty ではない)。*)
>> *)
    inversion H.
  - (* T_Abs *)
    (* If the [T_Abs] rule was the last used, then 
       [t = tabs x T11 t12], which is a value. *)
(** <<
    (* もし [T_Abs] が最後の規則ならば、[t = tm_abs x T11 t12] となるが、これは値である。 *)
>> *)
    left...
  - (* T_App *)
    (* If the last rule applied was T_App, then [t = t1 t2], 
       and we know from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is 
       a value or can take a step. *)
(** <<
    (* 最後の規則が T_App ならば、[t = t1 t2] である。規則の形から
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       となる。帰納法の仮定から、t1 と t2 のそれぞれは値であるかステップを進むことができる。 *)
>> *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = tabs x T11 t12], since abstractions are the 
           only values that can have an arrow type.  But
           [(tabs x T11 t12) t2 ==> [x:=t2]t12] by [ST_AppAbs]. *)
(** <<
        (* [t1] と [t2] がどちらも値のとき、[t1 = tm_abs x T11 t12] となる。
           なぜなら関数抽象は、関数型を持つ唯一の値であるから。しかし、[ST_AppAbs]より
           [(tabs x T11 t12) t2 ==> [x:=t2]t12] となる。 *)
>> *)
        inversion H; subst; try solve_by_invert.
        exists (subst x t2 t12)...
      * (* t2 steps *)
        (* If [t1] is a value and [t2 ==> t2'], 
           then [t1 t2 ==> t1 t2'] by [ST_App2]. *)
(** <<
        (* もし [t1] が値で [t2 ==> t2'] ならば、
           [ST_App2]より [t1 t2 ==> t1 t2'] である。 *)
>> *)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...
    + (* t1 steps *)
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] 
         by [ST_App1]. *)
(** <<
      (* 最後に、もし [t1 ==> t1'] ならば、
         [ST_App1] より [t1 t2 ==> t1' t2] である。 *)
>> *)
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...
  - (* T_Nat *)
    left...
  - (* T_Succ *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      inversion H; subst; try solve_by_invert.
      exists (tnat (S n1))...
    + (* t1 steps *)
      inversion H as [t1' Hstp].
      exists (tsucc t1')...
  - (* T_Pred *)
    right.
    destruct IHHt...
    + (* t1 is a value *)
      inversion H; subst; try solve_by_invert.
      exists (tnat (pred n1))...
    + (* t1 steps *)
      inversion H as [t1' Hstp].
      exists (tpred t1')...
  - (* T_Mult *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is a value *)
        inversion H; subst; try solve_by_invert.
        inversion H0; subst; try solve_by_invert.
        exists (tnat (mult n1 n0))...
      * (* t2 steps *)
        inversion H0 as [t2' Hstp].
        exists (tmult t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp].
      exists (tmult t1' t2)...
  - (* T_If0 *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      inversion H; subst; try solve_by_invert.
      destruct n1 as [|n1'].
      * (* n1=0 *)
        exists t2...
      * (* n1<>0 *)
        exists t3...
    + (* t1 steps *)
      inversion H as [t1' H0].
      exists (tif0 t1' t2 t3)...
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  - (* T_Unit *)
    left...
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  - (* T_Inl *)
    destruct IHHt...
    + (* t1 steps *)
      right. inversion H as [t1' Hstp]...
      (* exists (tinl _ t1')... *)
  - (* T_Inr *)
    destruct IHHt...
    + (* t1 steps *)
      right. inversion H as [t1' Hstp]...
      (* exists (tinr _ t1')... *)
  - (* T_Case *)
    right.
    destruct IHHt1...
    + (* t0 is a value *)
      inversion H; subst; try solve_by_invert.
      * (* t0 is inl *)
        exists ([x1:=v]t1)...
      * (* t0 is inr *)
        exists ([x2:=v]t2)...
    + (* t0 steps *)
      inversion H as [t0' Hstp].
      exists (tcase t0' x1 t1 x2 t2)...
  - (* T_Nil *)
    left...
  - (* T_Cons *)
    destruct IHHt1...
    + (* head is a value *)
      destruct IHHt2...
      * (* tail steps *)
        right. inversion H0 as [t2' Hstp].
        exists (tcons t1 t2')...
    + (* head steps *)
      right. inversion H as [t1' Hstp].
      exists (tcons t1' t2)...
  - (* T_Lcase *)
    right.
    destruct IHHt1...
    + (* t1 is a value *)
      inversion H; subst; try solve_by_invert.
      * (* t1=tnil *)
        exists t2...
      * (* t1=tcons v1 vl *)
        exists ([x2:=vl]([x1:=v1]t3))...
    + (* t1 steps *)
      inversion H as [t1' Hstp].
      exists (tlcase t1' t2 x1 x2 t3)...
  (* fix *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
Qed.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Context Invariance *)
(* end hide *)
(** *** コンテキスト不変性 *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  (* nats *)
  | afi_succ : forall x t,
     appears_free_in x t ->
     appears_free_in x (tsucc t)
  | afi_pred : forall x t,
     appears_free_in x t ->
     appears_free_in x (tpred t)
  | afi_mult1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (tmult t1 t2)
  | afi_mult2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (tmult t1 t2)
  | afi_if01 : forall x t1 t2 t3,
     appears_free_in x t1 ->
     appears_free_in x (tif0 t1 t2 t3)
  | afi_if02 : forall x t1 t2 t3,
     appears_free_in x t2 ->
     appears_free_in x (tif0 t1 t2 t3)
  | afi_if03 : forall x t1 t2 t3,
     appears_free_in x t3 ->
     appears_free_in x (tif0 t1 t2 t3)
  (* pairs *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* sums *)
  | afi_inl : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinl T t)
  | afi_inr : forall x t T,
      appears_free_in x t ->
      appears_free_in x (tinr T t)
  | afi_case0 : forall x t0 x1 t1 x2 t2,
      appears_free_in x t0 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case1 : forall x t0 x1 t1 x2 t2,
      x1 <> x ->
      appears_free_in x t1 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  | afi_case2 : forall x t0 x1 t1 x2 t2,
      x2 <> x ->
      appears_free_in x t2 ->
      appears_free_in x (tcase t0 x1 t1 x2 t2)
  (* lists *)
  | afi_cons1 : forall x t1 t2,
     appears_free_in x t1 ->
     appears_free_in x (tcons t1 t2)
  | afi_cons2 : forall x t1 t2,
     appears_free_in x t2 ->
     appears_free_in x (tcons t1 t2)
  | afi_lcase1 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t1 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase2 : forall x t1 t2 y1 y2 t3,
     appears_free_in x t2 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  | afi_lcase3 : forall x t1 t2 y1 y2 t3,
     y1 <> x ->
     y2 <> x ->
     appears_free_in x t3 ->
     appears_free_in x (tlcase t1 t2 y1 y2 t3)
  (* fix *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  induction H;
    intros Gamma' Heqv...
  - (* T_Var *)
    apply T_Var... rewrite <- Heqv...
  - (* T_Abs *)
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold update, t_update.
    destruct (beq_stringP x y)...
  - (* T_Mult *)
    apply T_Mult...
  - (* T_If0 *)
    apply T_If0...
  (* pair *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  - (* T_Case *)
    eapply T_Case...
    + apply IHhas_type2. intros y Hafi.
      unfold update, t_update.
      destruct (beq_stringP x1 y)...
    + apply IHhas_type3. intros y Hafi.
      unfold update, t_update.
      destruct (beq_stringP x2 y)...
  - (* T_Cons *)
    apply T_Cons...
  - (* T_Lcase *)
    eapply T_Lcase... apply IHhas_type3. intros y Hafi.
    unfold update, t_update.
    destruct (beq_stringP x1 y)...
    destruct (beq_stringP x2 y)...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  - (* T_Abs *)
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_beq_string in Hctx...
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* T_Case *)
  - (* left *)
    destruct IHHtyp2 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_beq_string in Hctx...
  - (* right *)
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_beq_string in Hctx...
  - (* T_Lcase *)
    clear Htyp1 IHHtyp1 Htyp2 IHHtyp2.
    destruct IHHtyp3 as [T' Hctx]... exists T'.
    unfold update, t_update in Hctx.
    rewrite false_beq_string in Hctx...
    rewrite false_beq_string in Hctx...
Qed.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Substitution *)
(* end hide *)
(** *** 置換 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (update Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then
     Gamma |- [x:=v]t : S. *)
(** <<
  (* 定理: もし Gamma,x:U |- t : S かつ empty |- v : U ならば、
     Gamma |- [x:=v]t : S. である。 *)
>> *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow 
     directly from the IH, with the exception of tvar
     and tabs. These aren't automatic because we must
     reason about how the variables interact. *)
  induction t;
(** <<
  (* 証明: 項 t についての帰納法を使う。ほとんどの場合は、帰納仮定から直接示される。
     tvar と tabs だけが例外である。
     これらは自動化できない。変数がどのように相互作用するか推論しなければならないからである。 *)
>> *)
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  - (* tvar *)
    simpl. rename s into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [update Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
(** <<
    (* もし t = y ならば、次が成立する:
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       そして、inversion から [update Gamma x U y = Some S] となる。
       示したいのは [Gamma |- [x:=v]y : S] である。
 
       考慮するのは2つの場合、[x=y] の場合と [x<>y] の場合である。 *)
>> *)
    unfold update, t_update in H1.
    destruct (beq_stringP x y).
    + (* x=y *)
      (* If [x = y], then we know that [U = S], and that 
         [[x:=v]y = v].  So what we really must show is 
         that if [empty |- v : U] then [Gamma |- v : U].  
         We have already proven a more general version
         of this theorem, called context invariance. *)
(** <<
      (* もし [x = y] ならば、[U = S] であり、また [[x:=v]y = v] である。
         これから実際に示さなければならないことは、
         もし [empty |- v : U] ならば [Gamma |- v : U] である、ということである。
         この定理のより一般化されたバージョンを既に証明している。それはコンテキスト不変性である。 *)
>> *)
      subst.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
      inversion HT'.
    + (* x<>y *)
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
(** <<
    (* もし [x <> y] ならば、[Gamma y = Some S] で、置換は何も影響しない。
       [T_Var] より [Gamma |- y : S] を示すことができる。 *)
>> *)
      apply T_Var...
  - (* tabs *)
    rename s into y. rename t into T11.
    (* If [t = tabs y T11 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma,
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 : S].

       We can calculate that
         [x:=v]t = tabs y T11 (if beq_string x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_string x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
(** <<
    (* もし [t = tabs y T11 t0] ならば、次が成立する:
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       帰納仮定より、すべての S と Gamma について
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 : S] となる。
 
       次の計算ができる:
         [x:=v]t = tabs y T11 (if beq_string x y then t0 else [x:=v]t0) 
       そして、示すべきことは [Gamma |- [x:=v]t : T11->T12] である。
       [T_Abs] を使うためには、残っているのは次を示すことである:
         [Gamma,y:T11 |- if beq_string x y then t0 else [x:=v]t0 : T12] 
       2つの場合、[x = y] の場合と [x <> y] の場合を考える。
    *)
>> *)
    apply T_Abs...
    destruct (beq_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that 
       [t0 : T12], so does the latter. *)
(** <<
    (* もし [x = y] ならば、置換は何も影響しない。
       コンテキスト不変性より [Gamma,y:U,y:T11] と [Gamma,y:T11] 
       が同値であることが示される。前者のコンテキストが [t0 : T12] を示すことから、
       後者についても同じことが言える。 *)
>> *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (beq_string y x)...
    + (* x<>y *)
      (* If [x <> y], then the IH and context invariance allow 
         us to show that
           [Gamma,x:U,y:T11 |- t0 : T12]       =>
           [Gamma,y:T11,x:U |- t0 : T12]       =>
           [Gamma,y:T11 |- [x:=v]t0 : T12] *)
(** <<
      (* もし [x <> y] ならば、帰納仮定とコンテキスト不変性より次が示される:
           [Gamma,x:U,y:T11 |- t0 : T12]       =>
           [Gamma,y:T11,x:U |- t0 : T12]       =>
           [Gamma,y:T11 |- [x:=v]t0 : T12] *)
>> *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (beq_stringP y z) as [Hyz|Hyz]...
      subst.
      rewrite false_beq_string...
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  - (* tcase *)
    rename s into x1. rename s0 into x2.
    eapply T_Case...
    + (* left arm *)
      destruct (beq_stringP x x1) as [Hxx1|Hxx1].
      * (* x = x1 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (beq_string x1 z)...
      * (* x <> x1 *)
        apply IHt2. eapply context_invariance...
        intros z Hafi.  unfold update, t_update.
        destruct (beq_stringP x1 z) as [Hx1z|Hx1z]...
        subst. rewrite false_beq_string...
    + (* right arm *)
      destruct (beq_stringP x x2) as [Hxx2|Hxx2].
      * (* x = x2 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (beq_string x2 z)...
      * (* x <> x2 *)
        apply IHt3. eapply context_invariance...
        intros z Hafi.  unfold update, t_update.
        destruct (beq_stringP x2 z)...
        subst. rewrite false_beq_string...
  - (* tlcase *)
    rename s into y1. rename s0 into y2.
    eapply T_Lcase...
    destruct (beq_stringP x y1).
    + (* x=y1 *)
      simpl.
      eapply context_invariance...
      subst.
      intros z Hafi. unfold update, t_update.
      destruct (beq_stringP y1 z)...
    + (* x<>y1 *)
      destruct (beq_stringP x y2).
      * (* x=y2 *)
        eapply context_invariance...
        subst.
        intros z Hafi. unfold update, t_update.
        destruct (beq_stringP y2 z)...
      * (* x<>y2 *)
        apply IHt3. eapply context_invariance...
        intros z Hafi. unfold update, t_update.
        destruct (beq_stringP y1 z)...
        subst. rewrite false_beq_string...
        destruct (beq_stringP y2 z)...
        subst. rewrite false_beq_string...
Qed.

(* ----------------------------------------------------------------- *)
(** *** Preservation *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then 
     [empty |- t' : T]. *)
(** <<
  (* 定理: もし [empty |- t : T] かつ [t ==> t'] ならば、[empty |- t' : T] である。 *)
>> *)
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many 
     cases are contradictory ([T_Var], [T_Abs]).  We show just 
     the interesting ones. *)
(** <<
  (* 証明: 与えられた型導出についての帰納法を使う。
     ほとんどの場合は、 [T_Var] と [T_Abs] の矛盾である。
     興味深いものだけを示す。 *)
>> *)
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    (* If the last rule used was [T_App], then [t = t1 t2], and 
       three rules could have been used to show [t ==> t']: 
       [ST_App1], [ST_App2], and [ST_AppAbs]. In the first two 
       cases, the result follows directly from the IH. *)
(** <<
    (* もし最後の規則が [T_App] ならば、[t = t1 t2] である。
       [t ==> t'] を示すのに使うことができる規則は3つ、[ST_App1]、[ST_App2]、[ST_AppAbs]である。
       最初の2つについては、結果は帰納仮定から直ぐに導かれる。 *)
>> *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      (* For the third case, suppose
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].
         We must show that [empty |- [x:=v2]t12 : T2].
         We know by assumption that
             [empty |- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution preserves 
         typing, and
             [empty |- v2 : T1]
         by assumption, so we are done. *)
(** <<
      (* 3つ目の場合、
           [t1 = tabs x T11 t12] 
         かつ
           [t2 = v2] 
         と仮定する。示すべきは [empty |- [x:=v2]t12 : T2] である。
         仮定から
             [empty |- tabs x T11 t12 : T1->T2] 
         であり、inversion から
             [x:T1 |- t12 : T2] 
         となる。
         substitution_preserves_typing を既に証明しており、また仮定から
             [empty |- v2 : T1] 
         である。これで証明された。 *)
>> *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  (* fst and snd *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* let *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
  (* T_Case *)
  - (* ST_CaseInl *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* ST_CaseInr *)
    inversion HT1; subst.
    eapply substitution_preserves_typing...
  - (* T_Lcase *)
    + (* ST_LcaseCons *)
      inversion HT1; subst.
      apply substitution_preserves_typing with (TList T1)...
      apply substitution_preserves_typing with T1...
  (* fix *)
  (* FILL IN HERE *)
(** <<
  (* ここを埋めなさい *)
>> *)
Qed.

End STLCExtended.
(** [] *)

(** $Date$ *)

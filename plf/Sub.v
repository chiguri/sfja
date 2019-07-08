(** * Sub :サブタイプ *)
(* begin hide *)
(** * Sub: Subtyping *)
(* end hide *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.

(* ################################################################# *)
(* begin hide *)
(** * Concepts *)
(* end hide *)
(** * 概念 *)

(* begin hide *)
(** We now turn to the study of _subtyping_, a key feature
    needed to support the object-oriented programming style. *)
(* end hide *)
(** さて、サブタイプ(_subtyping_)の学習に入ります。
    サブタイプはオブジェクト指向プログラミングをサポートするのに重要な機能の一つです。 *)

(* ================================================================= *)
(* begin hide *)
(** ** A Motivating Example *)
(* end hide *)
(** ** 動機付け *)

(* begin hide *)
(** Suppose we are writing a program involving two record types
    defined as follows:

      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
*)
(* end hide *)
(** 以下に定義する二つのレコード型が出現するプログラムを書いているとしましょう。
<<
      Person  = {name:String, age:Nat} 
      Student = {name:String, age:Nat, gpa:Nat} 
>>
*)

(* begin hide *)
(** In the simply typed lamdba-calculus with records, the term

      (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}

   is not typable, since it applies a function that wants a two-field
   record to an argument that actually provides three fields, while the
   [T_App] rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field.

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used _safely_ in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called _subtyping_.  We say that "[S]
   is a subtype of [T]", written [S <: T], if a value of type [S] can
   safely be used in any context where a value of type [T] is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language -- functions,
   pairs, etc. *)
(* end hide *)
(** レコードを持つ単純型付きラムダ計算では、項
<<
      (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1} 
>>
   は型付けできません。
   なぜなら、これはフィールドが2つのレコードを引数としてとる関数に3つのフィールドを持つレコードが与えられている部分を含んでいて、一方、[T_App]規則は関数の定義域の型は引数の型に完全に一致することを要求するからです。
 
   しかしこれは馬鹿らしいことです。
   実際には関数に、必要とされるものより良い引数を与えているのです！
   この関数の本体がレコード引数[r]に対して行いうることは、そのフィールド[age]を射影することだけです。
   型から許されることは他にはありません。
   すると、他に[gpa]フィールドが存在するか否かは何の違いもないはずです。
   これから、直観的に、この関数は少なくとも[age]フィールドを持つ任意のレコード値に適用可能であるべきと思われます。
 
   一般に、より豊かなフィールドを持つレコードは、そのサブセットのフィールドだけを持つレコードと「任意のコンテキストで少なくとも同等の良さである」と言えるでしょう。
   より長い（多くのフィールドを持つ）レコード型の任意の値は、より短かいレコード型が求められるコンテキストで「安全に」(_safely_)使えるという意味においてです。
   コンテキストがより短かい型のものを求めているときに、より長い型のものを与えた場合、何も悪いことは起こらないでしょう（形式的には、プログラムは行き詰まることはないでしょう）。
 
   ここで働く一般原理はサブタイプ（付け）(_subtyping_)と呼ばれます。
   型[T]の値が求められている任意のコンテキストで型[S]の値が安全に使えるとき、「[S]は[T]のサブタイプである」と言い、 [S <: T] と書きます。
   サブタイプの概念はレコードだけではなく、関数、対、など言語のすべての型コンストラクタに適用されます。 *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(* ================================================================= *)
(* begin hide *)
(** ** Subtyping and Object-Oriented Languages *)
(* end hide *)
(** ** サブタイプとオブジェクト指向言語 *)

(* begin hide *)
(** Subtyping plays a fundamental role in many programming
    languages -- in particular, it is closely related to the notion of
    _subclassing_ in object-oriented languages.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    roughly consists of projecting out the [m] field of [o] and
    applying it to [a1..an].

    The type of an object is called a _class_ -- or, in some
    languages, an _interface_.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the _subclass_ and _subinterface_ relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface [Component] that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared [private].  Classes can give
    _initializers_ that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    _inheritance_.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in [Pierce 2002] (in Bib.v), if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. *)
(* end hide *)
(** サブタイプは多くのプログラミング言語で重要な役割を演じます。
    特に、オブジェクト指向言語のサブクラス(_subclassing_)の概念と近い関係にあります。
 
    JavaやC[#]等のオブジェクトはレコードと考えることができます。
    いくつかのフィールドは関数(「メソッド」)で、いくつかのフィールドはデータ値（「フィールド」または「インスタンス変数」）です。
    オブジェクト[o]のメソッド[m]を引数[a1..an]のもとで呼ぶことは、大雑把に言うと、[o]から[m]フィールドを射影として抽出して、それを[a1..an]に適用することです。
 
    オブジェクトの型は「クラス(_class_)」や、言語によっては「インターフェース(_interface_)」と呼ばれます。
    この両者はどちらも、どのメソッドやどのデータフィールドをオブジェクトが提供するかを表しています。
    クラスやインターフェースは、サブクラス(_subclass_)関係やサブインターフェース(_subinterface_)関係で関係づけられます。
    サブクラス（またはサブインターフェース）に属するオブジェクトには、スーパークラス（またはスーパーインターフェース）に属するオブジェクトのメソッドとフィールドのすべての提供することが求められ、さらに追加で他のメソッドやフィールドを提供することもできます。
 
    サブクラスのオブジェクトをスーパークラスのオブジェクトの場所で使えるという事実は、複雑なライブラリの構築にきわめて便利なほどの柔軟性を提供します。
    例えば、Javaの Swingフレームワークのようなグラフィカルユーザーインターフェースツールキットは、スクリーンに表示できユーザとインタラクションできるグラフィカルな表現を持つすべてのオブジェクトに共通のフィールドとメソッドを集めた、抽象インターフェース[Component]を定義するでしょう。
    そのようなオブジェクトとしては、典型的なGUIのボタン、チェックボックス、スクロールバーなどがあります。
    この共通インターフェースのみに依存するメソッドはこれらのどのオブジェクトにも適用できます。
 
    もちろん、実際のオブジェクト指向言語はこれらに加えてたくさんの機能を持っています。
    例えば、フィールドを更新できます。
    フィールドやメソッドを[private]と宣言できます。
    クラスにオブジェクトを作り上げるための「初期化子(_initializer_)」を定義できます。
    サブクラスのコードが「継承(_inheritance_)」を通じてスーパークラスのコードと協調できます。
    クラスが静的なメソッドやフィールドを持つことができます。
    などなど、です。
 
    ものごとを単純なまま進めるために、これらの問題を扱うことはしません。
    実際、これ以上オブジェクトやクラスについて話すことはありません。
    （もし興味があるなら、 Bib.v 内の [Pierce 2002] にたくさんの議論があります。）
    その代わり、STLCの単純化された設定のもとで、サブクラス/サブインターフェース関係の背後にある核となる概念について学習します。 *)

(* ================================================================= *)
(* begin hide *)
(** ** The Subsumption Rule *)
(* end hide *)
(** ** 包摂規則 *)

(* begin hide *)
(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:

                         Gamma |- t \in S     S <: T
                         ---------------------------                    (T_Sub)
                               Gamma |- t \in T

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)
(* end hide *)
(** この章のゴールは（[MoreStlc]の拡張機能を持つ）単純型付きラムダ計算にサブタイプを追加することです。
    これは2つのステップから成ります：
 
      - 型の間の二項サブタイプ関係(_subtype relation_)を定義します。
 
      - 型付け関係をサブタイプを考慮した形に拡張します。
 
    2つ目のステップは実際はとても単純です。型付け関係にただ1つの規則だけを追加します。
    その規則は、包摂規則(_rule of subsumption_)と呼ばれます：
<<
                         Gamma |- t \in S     S <: T 
                         ---------------------------                    (T_Sub) 
                               Gamma |- t \in T 
>>
    この規則は、直観的には、項について知っている情報のいくらかを「忘れる」ようにしてよいと言っています。 *)

(* begin hide *)
(** For example, we may know that [t] is a record with two
    fields (e.g., [S = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T = {y:B->B}]) so that we can pass [t] to a
    function that requires just a single-field record. *)
(* end hide *)
(** 例えば、[t]が2つのフィールドを持つレコード（例えば、[S = {x:A->A, y:B->B}]）で、フィールドの1つを忘れることにした（[T = {y:B->B}]）とします。
    すると[t]を、1フィールドのレコードを引数としてとる関数に渡すことができるようになります。 *)

(* ================================================================= *)
(* begin hide *)
(** ** The Subtype Relation *)
(* end hide *)
(** ** サブタイプ関係 *)

(* begin hide *)
(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)
(* end hide *)
(** 最初のステップ、関係 [S <: T] の定義はすべてのアクションに関して存在します。
    それぞれの定義を見てみましょう。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Structural Rules *)
(* end hide *)
(** *** 構造規則 *)

(* begin hide *)
(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:

                                   ------                              (S_Refl)
                                   T <: T
*)
(* end hide *)
(** まず最初に、2つの「構造規則」("structural rules")を追加します。
    これらは特定の型コンストラクタからは独立したものです。
    推移(_transitivity_)規則は、直観的には、[S]が[U]よりも（安全、豊かさの面で）良く、[U]が[T]よりも良ければ、[S]は[T]よりも良いというものです。
<<
                              S <: U    U <: T 
                              ----------------                        (S_Trans) 
                                   S <: T 
>>
    そして反射(_reflexivity_)規則は、任意の型はそれ自身と同じ良さを持つというものです。
<<
                                   ------                              (S_Refl) 
                                   T <: T 
>>
*)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Products *)
(* end hide *)
(** *** 直積型 *)

(* begin hide *)
(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)
(* end hide *)
(** 次に、直積型です。
    ある一つの対が他の対のサブタイプであるとは、それぞれの成分が対応するもののサブタイプであることです。
<<
                            S1 <: T1    S2 <: T2 
                            --------------------                        (S_Prod) 
                             S1 * S2 <: T1 * T2 
>>
 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Arrows *)
(* end hide *)
(** *** 関数型 *)

(* begin hide *)
(** The subtyping rule for arrows is a little less intuitive.
    Suppose we have functions [f] and [g] with these types:

       f : C -> Student
       g : (C->Person) -> D

    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its argument to be
    a function yielding a record of type [Person].  Also suppose that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:

                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

    But notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second.

    Here is an example that illustrates this:

       f : Person -> C
       g : (Student -> C) -> D

    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. *)
(* end hide *)
(** 関数型のサブタイプ関係はやや直観から外れます。
    次の型を持つ2つの関数[f]と[g]があるとします：
[[
       f : C -> Student 
       g : (C->Person) -> D 
]]
    つまり、[f]は型[Student]のレコードを返す関数であり、[g]は引数として、型[Person]のレコードを返す関数をとる高階関数です。
    そして、[Student] が [Person] のサブタイプであるとします。
    すると、関数適用 [g f] は、両者の型が正確に一致しないにもかかわらず安全です。
    なぜなら、[g]が[f]について行うことができるのは、[f]を（型[C]の）ある引数に適用することだけだからです。
    その結果は実際には[Student]型のレコード値になります。
    ここで[g]が期待するのは[Person]型のレコードです。
    しかしこれは安全です。なぜなら[g]がすることができるのは、わかっている2つのフィールド（[name]と[age]）を射影することだけで、それは存在するフィールドの一部だからです。
 
    この例から、関数型のサブタイプ規則が以下のようになるべきということが導かれます。
    2つの関数型がサブタイプ関係にあるのは、その結果が次の条件のときです:
<<
                                  S2 <: T2 
                              ----------------                     (S_Arrow_Co) 
                            S1 -> S2 <: S1 -> T2 
>>
    同様に、これを一般化して、2つの関数型のサブタイプ関係を、引数の条件を含めた形にすることができます:
<<
                            T1 <: S1    S2 <: T2 
                            --------------------                      (S_Arrow) 
                            S1 -> S2 <: T1 -> T2 
>>
    ここで注意するのは、引数の型はサブタイプ関係が逆向きになることです。
    [S1->S2] が [T1->T2] のサブタイプであると結論づけるには、[T1]が[S1]のサブタイプでなければなりません。
    関数型のコンストラクタは最初の引数について反変(_contravariant_)であり、
    二番目の引数について共変(_covariant_)であると言います。
 
    このことを表す例を見てみましょう。
[[
       f : Person -> C
       g : (Student -> C) -> D
]]
    関数適用[g f]は安全です。
    なぜなら、[g]の本体での[f]の使い方は、[Student]型の引数に適用することだけだからです。
    [f]は（少なくとも）[Person]のもつフィールドを含んだレコードを要求するだけなので、これはうまく動きます。
    よって、[Student]が[Person]のサブタイプであるため、[Person -> C]は[Student -> C]のサブタイプとなります。
 
    直観的には、型[S1->S2]の関数[f]があるとき、[f]は型[S1]の要素を引数として許容することがわかります。
    明らかに[f]は[S1]の任意のサブタイプ[T1]の要素も引数として許容します。
    [f]の型は同時に[f]が型[S2]の要素を返すことも示しています。
    この値が[S2]の任意のスーパータイプ[T2]に属することも見ることができます。
    つまり、型[S1->S2]の任意の関数[f]は、型[T1->T2]を持つと見ることもできるということです。 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Records *)
(* end hide *)
(** *** レコード *)

(* begin hide *)
(** What about subtyping for record types? *)
(* end hide *)
(** レコード型のサブタイプは何でしょうか？ *)

(* begin hide *)
(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,

    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}

    This is known as "width subtyping" for records. *)
(* end hide *)
(** 基本的直観は、「より小さな」レコードの場所で「より大きな」レコードを使うことは常に安全だということです。
    つまり、レコード型があるとき、さらにフィールドを追加したものは常にサブタイプになるということです。
    もしあるコードがフィールド[x]と[y]を持つレコードを期待していたとき、レコード[x]、[y]、[z]を持つレコードを受けとることは完璧に安全です。
    [z]フィールドは単に無視されるだけです。
    例えば次の通りです。
[[
    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat} 
    {name:String, age:Nat} <: {name:String}  
    {name:String} <: {} 
]]
   これはレコードの「幅サブタイプ(width subtyping)」として知られます。 *)

(* begin hide *)
(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,

    {x:Student} <: {x:Person}

    This is known as "depth subtyping". *)
(* end hide *)
(** レコードの1つのフィールドの型をそのサブタイプで置き換えることでも、レコードのサブタイプを作ることができます。
    もしあるコードが型[T]のフィールド[x]を持つレコードを期待するとき、型[S]が型[T]のサブタイプである限り、型[S]のフィールド[x]を持つレコードが来ても何の問題も起こりません。
    例えば次の通りです。
[[
    {x:Student} <: {x:Person} 
]]
    これは「深さサブタイプ(depth subtyping)」として知られています。 *)

(* begin hide *)
(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

    {name:String,age:Nat} <: {age:Nat,name:String}

    This is known as "permutation subtyping". *)
(* end hide *)
(** 最後に、レコードのフィールドは特定の順番で記述されますが、その順番は実際には問題ではありません。
    例えば次の通りです。
[[
    {name:String,age:Nat} <: {age:Nat,name:String}
]]
    これは「順列サブタイプ(permutation subtyping)」として知られています。 *)

(* begin hide *)
(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:

                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)
(* end hide *)
(** これらをレコードについての単一のサブタイプ規則に形式化することもできはします。
    次の通りです:
<<
                        forall jk in j1..jn, 
                    exists ip in i1..im, such that 
                          jk=ip and Sp <: Tk 
                  ----------------------------------                    (S_Rcd) 
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn} 
>>
    つまり、左のレコードは(少なくとも)右のレコードのフィールドラベルをすべて持ち、両者で共通するフィールドはサブタイプ関係になければならない、ということです。
 
    しかしながら、この規則はかなり重くて読むのが大変なので、3つの簡単な規則に分解されます。
    この3つを[S_Trans]を使って結合することで、同じように作用させることができます。 *)

(* begin hide *)
(** First, adding fields to the end of a record type gives a subtype:

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)
(* end hide *)
(** 最初に、レコード型の最後にフィールドを追加したものはサブタイプになります。
<<
                               n > m 
                 ---------------------------------                 (S_RcdWidth) 
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm} 
>>
    [S_RcdWidth]を使うと、複数のフィールドを持つレコードについて、
    前方のフィールドを残したまま後方のフィールドを取り除くことができます。
    この規則で例えば [{age:Nat,name:String} <: {age:Nat}] を示せます。 *)

(* begin hide *)
(** Second, subtyping can be applied inside the components of a compound
    record type:

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)
(* end hide *)
(** 二つ目では、レコード型の構成要素の内部にサブタイプ規則を適用できます。
<<
                       S1 <: T1  ...  Sn <: Tn 
                  ----------------------------------               (S_RcdDepth) 
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn} 
>>
    例えば [S_RcdDepth]と[S_RcdWidth]を両方使って [{y:Student, x:Nat} <: {y:Person}]を示すことができます。 *)

(* begin hide *)
(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person].  (We
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.)  So we add:

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)
(* end hide *)
(** 三つ目に、サブタイプとしてフィールドの並べ替えを可能にします。
    例えば [{name:String, gpa:Nat, age:Nat} <: Person] であってほしいのです。
    （これはまだ達成されていません。
    [S_RcdDepth]と[S_RcdWidth]だけでは、レコード型の「後」からフィールドを落とすことしかできません。）
    そのため、次の規則が必要です。
<<
         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn} 
         ---------------------------------------------------        (S_RcdPerm) 
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn} 
>>
 *)

(* begin hide *)
(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)
(* end hide *)
(** なお、本格的な言語ではこれらのサブタイプ規則のすべてを採用しているとは限らないことは注記しておくべきでしょう。
    例えばJavaでは
 
    - 各クラスのメンバー（フィールドまたはメソッド）は1つだけインデックスを持ち、サブクラスでメンバーが追加されるたびに新しいインデックスが「右に」追加されます
      （つまり、クラスには並び換えがありません）。
 
    - クラスは複数のインターフェースを実装できます。
      これはインターフェースの「多重継承(multiple inheritance)」と呼ばれます
      （つまり、インターフェースには並び換えがあります）。
 
    - 昔のバージョンでは、サブクラスではスーパークラスのメソッドの引数または結果の型を変えることはできませんでした
      （つまり、depth subtypingまたは関数型サブタイプのいずれかができなかったということです。
      どちらかは見方によります）。 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, recommended (arrow_sub_wrong)  

    Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:

                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2

    Give a concrete example of functions [f] and [g] with the following
    types...

       f : Student -> Nat
       g : (Person -> Nat) -> Nat

    ... such that the application [g f] will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that
    the application gets stuck.)

*)
(* end hide *)
(** **** 練習問題: ★★, standard, recommended (arrow_sub_wrong)
 
    関数型のサブタイプについて、誤って矢印の左右両方とも共変として定義してしまったとする。
<<
                            S1 <: T1    S2 <: T2 
                            --------------------                (S_Arrow_wrong) 
                            S1 -> S2 <: T1 -> T2 
>>
    2つの関数[f]と[g]について、以下の型
[[
       f : Student -> Nat 
       g : (Person -> Nat) -> Nat 
]]
    を満たし、適用[g f]が実行時に行き詰まるような例を挙げなさい。
    （非形式的な構文で構いません。
    行き詰まることの形式的な証明を与える必要もありません。）
 
 *)

(* Do not modify the following line: *)
Definition manual_grade_for_arrow_sub_wrong : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Top *)

(* begin hide *)
(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:

                                   --------                             (S_Top)
                                   S <: Top

    The [Top] type is an analog of the [Object] type in Java and C#. *)
(* 訳注：#を角括弧で囲まなくなったが、表示の影響はないか？ *)
(* end hide *)
(** 最後に、サブタイプ関係の最大要素を定めます。
    他のすべての型のスーパータイプであり、すべての(型付けできる)値が属する型です。
    このために言語に新しい一つの型定数[Top]を追加し、[Top]をサブタイプ関係の他のすべての型のスーパータイプとするサブタイプ規則を定めます:
<<
                                   --------                             (S_Top) 
                                   S <: Top 
>>
    [Top]型はJavaやC#における[Object]型に対応するものです。 *)

(* ----------------------------------------------------------------- *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption

                         Gamma |- t \in S     S <: T
                         ---------------------------                    (T_Sub)
                               Gamma |- t \in T

      to the typing relation, and

    - defining a subtype relation as follows:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(* ================================================================= *)
(** ** Exercises *)

(** **** Exercise: 1 star, standard, optional (subtype_instances_tf_1)  

    Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.
    ([A], [B], and [C] here are base types like [Bool], [Nat], etc.)

    - [T->S <: T->S]

    - [Top->U <: S->Top]

    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]

    - [T->T->U <: S->S->V]

    - [(T->T)->U <: (S->S)->V]

    - [((T->S)->T)->U <: ((S->T)->S)->V]

    - [S*V <: T*U]

    [] *)

(** **** Exercise: 2 stars, standard (subtype_order)  

    The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

Write these types in order from the most specific to the most general.

Where does the type [Top->Top->Student] fit into this order?
That is, state how [Top -> (Top -> Student)] compares with each
of the five types above. It may be unrelated to some of them.  
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_order : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_instances_tf_2)  

    Which of the following statements are true?  Write _true_ or
    _false_ after each one.

      forall S T,
          S <: T  ->
          S->S   <:  T->T

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 

      exists S,
           S <: S->S 

      exists S,
           S->S <: S  

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_instances_tf_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_concepts_tf)  

    Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.

    - There exists a type that is a subtype of every other type.

    - There exists a pair type that is a supertype of every other
      pair type.

    - There exists a pair type that is a subtype of every other
      pair type.

    - There exists an arrow type that is a supertype of every other
      arrow type.

    - There exists an arrow type that is a subtype of every other
      arrow type.

    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].

    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].

*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_concepts_tf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (proper_subtypes)  

    Is the following statement true or false?  Briefly explain your
    answer.  (Here [Base n] stands for a base type, where [n] is
    a string standing for the name of the base type.  See the
    Syntax section below.)

    forall T,
         ~(T = Bool \/ exists n, T = Base n) ->
         exists S,
            S <: T  /\  S <> T
*)

(* Do not modify the following line: *)
Definition manual_grade_for_proper_subtypes : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_1)  
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)

       empty |- (\p:T*Top. p.fst) ((\z:A.z), unit) \in A->A

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_2)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       empty |- (\p:(A->A * B->B). p) ((\z:A.z), (\z:B.z)) \in T

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (small_large_3)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       a:A |- (\p:(A*T). (p.snd) (p.fst)) (a, \z:A.z) \in A

   - What is the _largest_ type [T] that makes the same assertion true?

    [] *)

(** **** Exercise: 2 stars, standard (small_large_4)  
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       exists S,
         empty |- (\p:(A*T). (p.snd) (p.fst)) \in S

   - What is the _largest_ type [T] that makes the same
     assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_4 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_1)  

    What is the _smallest_ type [T] that makes the following
    assertion true?

      exists S t,
        empty |- (\x:T. x x) t \in S
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_2)  

    What is the _smallest_ type [T] that makes the following
    assertion true?

      empty |- (\x:Top. x) ((\z:A.z) , (\z:B.z)) \in T
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (count_supertypes)  

    How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)

    [] *)

(** **** Exercise: 2 stars, standard (pair_permutation)  

    The subtyping rule for product types

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2

    intuitively corresponds to the "depth" subtyping rule for records.
    Extending the analogy, we might consider adding a "permutation" rule

                                   --------------
                                   T1*T2 <: T2*T1

    for products.  Is this a good idea? Briefly explain why or why not.

*)

(* Do not modify the following line: *)
Definition manual_grade_for_pair_permutation : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Formal Definitions *)
(* end hide *)
(** * 形式的定義 *)

(* begin hide *)
(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)
(* end hide *)
(** 上記の議論で使った、形式化する定義のほとんど -- 特に言語の構文と操作的意味 -- は前の章で見たものと同じです。
    ここで必要となるものは型付け規則の包括規則による拡張と、サブタイプ関係を表す帰納的定義の追加です。
    最初に同じ部分をやってみましょう。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Core Definitions *)
(* end hide *)
(** * 中核部の定義 *)

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Syntax *)
(* end hide *)
(** *** 構文 *)

(* begin hide *)
(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like [String], [Float], etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) *)
(* end hide *)
(** この章の残りでは、レコード型は省略して、基底型、ブール型、関数型、[Unit]と[Top]のみ形式化し、直積型は練習問題にします。
    例をおもしろくするために、[String]、[Float]のような、任意の基底型を許しています。
    （これはあくまで例で用いるためだけなので、わざわざこれらへの操作を追加したりはしませんが、そうすることは簡単です。） *)

Inductive ty : Type :=
  | Top   : ty
  | Bool  : ty
  | Base  : string -> ty
  | Arrow : ty -> ty -> ty
  | Unit  : ty
.

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm 
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | unit : tm 
.

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Substitution *)
(* end hide *)
(** *** 置換 *)

(* begin hide *)
(** The definition of substitution remains exactly the same as for the
    pure STLC. *)
(* end hide *)
(** 置換の定義はSTLCと全く同じです。 *)

Fixpoint subst (x:string) (s:tm)  (t:tm) : tm :=
  match t with
  | var y =>
      if eqb_string x y then s else t
  | abs y T t1 =>
      abs y T (if eqb_string x y then t1 else (subst x s t1))
  | app t1 t2 =>
      app (subst x s t1) (subst x s t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test (subst x s t1) (subst x s t2) (subst x s t3)
  | unit =>
      unit 
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ----------------------------------------------------------------- *)
(* begin hide *)
(** *** Reduction *)
(* end hide *)
(** *** 簡約 *)

(* begin hide *)
(** Likewise the definitions of the [value] property and the [step]
    relation. *)
(* end hide *)
(** [value](値)の定義や[step]関係の定義と同様です。 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_true :
      value tru
  | v_false :
      value fls
  | v_unit :
      value unit
.

Hint Constructors value.

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         (app t1 t2) --> (app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         (app v1 t2) --> (app v1  t2')
  | ST_TestTrue : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFalse : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

(* ================================================================= *)
(* begin hide *)
(** ** Subtyping *)
(* end hide *)
(** ** サブタイプ *)

(* begin hide *)
(** Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. *)
(* end hide *)
(** ようやくおもしろい所にやって来ました。
    サブタイプ関係の定義から始め、その重要な技術的性質を調べます。 *)

(* begin hide *)
(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)
(* end hide *)
(** サブタイプの定義は、動機付けの議論のところで概観した通りです。 *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: Top
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (Arrow S1 S2) <: (Arrow T1 T2)
where "T '<:' U" := (subtype T U).

(* begin hide *)
(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)
(* end hide *)
(** なお、基底型（[Bool]と[Base]）について、特別な規則は何ら必要ありません。
    基底型は自動的に([S_Refl]より)自分自身のサブタイプであり、（[S_Top]より）[Top]のサブタイプでもあります。
    そしてこれが必要な全てです。 *)

Hint Constructors subtype.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := (Base "A").
Notation B := (Base "B").
Notation C := (Base "C").

Notation String := (Base "String").
Notation Float := (Base "Float").
Notation Integer := (Base "Integer").

Example subtyping_example_0 :
  (Arrow C Bool) <: (Arrow C Top).
  (* C->Bool <: C->Top *)
Proof. auto. Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (subtyping_judgements)  

    (Leave this exercise [Admitted] until after you have finished adding product
    types to the language -- see exercise [products] -- at least up to 
    this point in the file).

    Recall that, in chapter [MoreStlc], the optional section
    "Encoding Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following
    record types:

    Person := { name : String } 
    Student := { name : String ; gpa : Float } 
    Employee := { name : String ; ssn : Integer }
*)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (subtyping_judgements)
 
    （この練習問題は、練習問題[products]を通じて、言語定義の少なくともファイルのこの場所まで直積型を追加するまで[Admitted]のまま放置しておいてください。）
 
    [MoreStlc]の章では、「レコードのエンコード」という節で、レコードを対によって表現しました。
    この方法を使い、以下のレコード型を表す組型を定義しなさい。
[[
    Person := { name : String }  
    Student := { name : String ; gpa : Float }  
    Employee := { name : String ; ssn : Integer } 
]]
 *)
Definition Person : ty
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition Student : ty
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition Employee : ty
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(* begin hide *)
(** Now use the definition of the subtype relation to prove the following: *)
(* end hide *)
(** それらの型を用いて、以下のサブタイプ関係を示しなさい。 *)

Example sub_student_person :
  Student <: Person.
Proof.
(* FILL IN HERE *) Admitted.

Example sub_employee_person :
  Employee <: Person.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)
(* end hide *)
(** 以下の事実のほとんどは、Coqで証明するのは簡単です。
    練習問題の効果を十分に得るために、どうやって証明するか自分が理解していることを紙に証明を書いて確認しなさい。 *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (subtyping_example_1)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (subtyping_example_1)  *)
Example subtyping_example_1 :
  (Arrow Top Student) <: (Arrow (Arrow C C) Person).
  (* Top->Student <: (C->C)->Person *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (subtyping_example_2)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (subtyping_example_2)  *)
Example subtyping_example_2 :
  (Arrow Top Person) <: (Arrow Person Top).
  (* Top->Person <: Person->Top *)
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

End Examples.

(* ================================================================= *)
(* begin hide *)
(** ** Typing *)
(* end hide *)
(** ** 型付け *)

(* begin hide *)
(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)
(* end hide *)
(** 型付け関係の変更は、包摂規則 [T_Sub] の追加だけです。 *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in Arrow T1 T2 ->
      Gamma |- t2 \in T1 ->
      Gamma |- app t1 t2 \in T2
  | T_True : forall Gamma,
       Gamma |- tru \in Bool
  | T_False : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T
  | T_Unit : forall Gamma,
      Gamma |- unit \in Unit
  (* New rule of subsumption *)
  | T_Sub : forall Gamma t S T,
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(** The following hints help [auto] and [eauto] construct typing
    derivations.  They are only used in a few places, but they give
    a nice illustration of what [auto] can do with a bit more 
    programming.  See chapter [UseAuto] for more on hints. *)

Hint Extern 2 (has_type _ (app _ _) _) =>
  eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

Module Examples2.
Import Examples.

(* begin hide *)
(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. *)
(* end hide *)
(** 以下の練習問題は言語に直積を追加した後に行いなさい。
    それぞれの非形式的な型付けジャッジメントについて、Coqで形式的主張を記述し、それを証明しなさい。 *)

(* begin hide *)
(** **** Exercise: 1 star, standard, optional (typing_example_0)  *)
(* end hide *)
(** **** 練習問題: ★, standard, optional (typing_example_0)  *)
(* empty |- ((\z:A.z), (\z:B.z))
         \in (A->A * B->B) *)
(* FILL IN HERE 

    [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (typing_example_1)  *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (typing_example_1)  *)
(* empty |- (\x:(Top * B->B). x.snd) ((\z:A.z), (\z:B.z))
         \in B->B *)
(* FILL IN HERE 

    [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (typing_example_2)  *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (typing_example_2)  *)
(* empty |- (\z:(C->C)->(Top * B->B). (z (\x:C.x)).snd)
              (\z:C->C. ((\z:A.z), (\z:B.z)))
         \in B->B *)
(* FILL IN HERE 

    [] *)

End Examples2.

(* ################################################################# *)
(* begin hide *)
(** * Properties *)
(* end hide *)
(** * 性質 *)

(* begin hide *)
(** The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter [References]),
    we don't need to change the _statements_ of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. *)
(* end hide *)
(** チェックしたいシステムの根本的性質はいつもと同じく、進行と保存です。
    STLCに参照を拡張したもの（[References]章）とは違い、サブタイプを考慮しても、これらの主張を変化させる必要はありません。
    ただし、それらの証明はもうちょっと複雑になります。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Inversion Lemmas for Subtyping *)
(* end hide *)
(** ** サブタイプの反転補題(Inversion Lemma) *)

(* begin hide *)
(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)
(* end hide *)
(** 型付け関係の性質を見る前に、サブタイプ関係の2つの重要な構造的性質を記しておかなければなりません:
       - [Bool]は[Bool]の唯一のサブタイプです。
       - 関数型のすべてのサブタイプはやはり関数型です。 *)

(* begin hide *)
(** These are called _inversion lemmas_ because they play a
    similar role in proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or
    [T], each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of [S] and
    [T] and the existence of subtype relations between their parts. *)
(* end hide *)
(** これらは反転補題(_inversion lemma_)と呼ばれます。
    これは、証明で組込みの[inversion]タクティックに似た役目をするためです。
    つまり、サブタイプ関係の主張 [S <: T] の導出が存在するという仮定と、[S]や[T]の形についてのいくつかの制約が与えられたとき、それぞれの反転補題は、[S <: T] の導出がどのような形をしていなければならないか、を提示することで、[S] や [T] のより詳細な情報、および [S <: T] が（矛盾なく）存在することを述べます。 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (sub_inversion_Bool)  *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (sub_inversion_Bool)  *)
Lemma sub_inversion_Bool : forall U,
     U <: Bool ->
     U = Bool.
Proof with auto.
  intros U Hs.
  remember Bool as V.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 3 stars, standard (sub_inversion_arrow)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard (sub_inversion_arrow)  *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: Arrow V1 V2 ->
     exists U1 U2,
     U = Arrow U1 U2 /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember (Arrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Canonical Forms *)
(* end hide *)
(** ** 正準形(Canonical Forms) *)

(* begin hide *)
(** The proof of the progress theorem -- that a well-typed
    non-value can always take a step -- doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application [t1 t2]
    where both [t1] and [t2] are values, we need to know that [t1] has
    the _form_ of a lambda-abstraction, so that we can apply the
    [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |- t1 \in T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. *)
(* end hide *)
(** 進行定理（値でない型付け可能な項の計算は進められる）の証明はそれほど大きく変える必要はありません。
    1つだけ小さなリファインメントが必要です。
    問題となる項が関数適用 [t1 t2] で[t1]と[t2]が両方とも値の場合を考えるとき、[t1]がラムダ抽象の形をしており、そのため[ST_AppAbs]簡約規則が適用できることを確認する必要があります。
    もともとのSTLCでは、これは明らかです。
    [t1]が関数型[T11->T12]を持ち、また、関数型の値を与える規則が1つだけ、つまり規則[T_Abs]だけであり、そしてこの規則の結論部の形から、[t1]は関数型にならざるを得ない、ということがわかります。
 
    サブタイプを持つSTLCにおいては、この推論はそのままうまく行くわけではありません。
    その理由は、値が関数型を持つことを示すのに使える規則がもう1つあるからです。
    包摂規則です。
    幸い、このことが大きな違いをもたらすことはありません。
    もし [Gamma |- t1 \in T11->T12] を示すのに使われた最後の規則が包摂規則だった場合、導出のその前の部分で、同様に[t1]が主部(項の部分)である導出があり、帰納法により一番最初には[T_Abs]が使われたことが推論できるからです。
 
    推論のこの部分は次の補題にまとめられています。
    この補題は、関数型の可能な「正準形(canonical forms、つまり値)」を示します。 *)

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (canonical_forms_of_arrow_types)  *)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (canonical_forms_of_arrow_types)  *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in Arrow T1 T2 ->
  value s ->
  exists x S1 s2,
     s = abs x S1 s2.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** Similarly, the canonical forms of type [Bool] are the constants
    [tru] and [fls]. *)
(* end hide *)
(** 同様に、型[Bool]の正準形は定数[tru]と[fls]です。 *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in Bool ->
  value s ->
  s = tru \/ s = fls.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember Bool as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Progress *)
(* end hide *)
(** ** 進行 *)

(* begin hide *)
(** The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas... *)
(* end hide *)
(** 進行性の証明は純粋なSTLCとほぼ同様に進みます。
    ただ何箇所かで正準形補題を使うことを除けば... *)

(* begin hide *)
(** _Theorem_ (Progress): For any term [t] and type [T], if [empty |-
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |- t \in T].  Proceed
    by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [tru], and [fls] are
    already values.  The [T_Var] case is vacuous because variables
    cannot be typed in the empty context.  The remaining cases are
    more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |- t1 \in T1 -> T2], and [empty |-
      t2 \in T1].  Moreover, by the induction hypothesis, either [t1] is
      a value or it steps, and either [t2] is a value or it steps.
      There are three possibilities to consider:

      - Suppose [t1 --> t1'] for some term [t1'].  Then [t1 t2 --> t1' t2]
        by [ST_App1].

      - Suppose [t1] is a value and [t2 --> t2'] for some term [t2'].
        Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1] is a
        value.

      - Finally, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has the
        form [\x:S1.s2] for some [x], [S1], and [s2].  But then
        [(\x:S1.s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_Test], then there
      are terms [t1], [t2], and [t3] such that [t = test t1 then t2 else
      t3], with [empty |- t1 \in Bool] and with [empty |- t2 \in T] and
      [empty |- t3 \in T].  Moreover, by the induction hypothesis,
      either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = tru] or [t1 = fls].  In either
         case, [t] can step, using rule [ST_TestTrue] or [ST_TestFalse].

       - If [t1] can step, then so can [t], by rule [ST_Test].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [S] such that [S <: T] and [empty |- t \in S].  The desired
      result is exactly the induction hypothesis for the typing
      subderivation.

    Formally: *)
(* end hide *)
(** 「定理」（進行）: 任意の項[t]と型[T]について、もし [empty |- t \in T] ならば[t]は値であるか、ある項[t']について [t --> t'] である。
 
    「証明」:[t]と[T]が与えられ、[empty |- t \in T] とする。
    型付けの導出についての帰納法で進める。
 
    （最後の規則が）[T_Abs]、[T_Unit]、[T_True]、[T_False]のいずれかの場合は自明である。
    なぜなら、関数抽象、[unit]、[tru]、[fls]は既に値だからである。
    [T_Var]であることはありえない。
    なぜなら、変数は空コンテキストで型付けできないからである。
    残るのはより興味深い場合である:
 
    - 型付け導出の最後のステップで規則[T_App]が使われた場合、項[t1]、[t2]と型[T1]、[T2]が存在して [t = t1 t2]、[T = T2]、[empty |- t1 \in T1 -> T2]、[empty |- t2 \in T1] となる。
      さらに帰納法の仮定から、[t1]は値であるかステップを進めることができ、[t2]も値であるかステップを進めることができる。
      このとき、3つの場合がある:
 
      - ある項 [t1'] について [t1 --> t1'] とする。このとき[ST_App1]より [t1 t2 --> t1' t2] である。
 
      - [t1]が値であり、ある項[t2']について [t2 --> t2'] とする。
        このとき規則[ST_App2]より [t1 t2 --> t1 t2'] となる。
        なぜなら[t1]が値だからである。
 
      - 最後に[t1]と[t2]がどちらも値とする。
        関数型に対する正準形補題より、[t1]はある[x]、[S1]、[s2]について[\x:S1.s2]という形である。
        しかしすると[t2]が値であることから、[ST_AppAbs]より [(\x:S1.s2) t2 --> [t2/x]s2] となる。
 
    - 導出の最後のステップで規則[T_Test]が使われた場合、項[t1]、[t2]、[t3]があって [t = test t1 then t2 else t3] となり、 [empty |- t1 \in Bool] かつ [empty |- t2 \in T] かつ [empty |- t3 \in T] である。
      さらに、帰納法の仮定より[t1]は値であるかステップを進めることができる。
 
       - もし[t1]が値ならば、ブール値についての正準形補題より [t1 = tru] または [t1 = fls] である。
         どちらの場合でも、規則[ST_TestTrue]または[ST_TestFalse]を使うことによって[t]はステップを進めることができる。
 
       - もし[t1]がステップを進めることができるならば、規則[ST_Test]より[t]もまたステップを進めることができる。
 
    - 導出の最後のステップが規則[T_Sub]による場合、型[S]があって [S <: T] かつ [empty |- t \in S] となっている。
      求める結果は型付け導出の帰納法の仮定そのものである。
    
    形式的には： *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  induction Ht;
    intros HeqGamma; subst...
  - (* T_Var *)
    inversion H.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (app t1 t2')...
    + (* t1 steps *)
      inversion H as [t1' Hstp]. exists (app t1' t2)...
  - (* T_Test *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + assert (t1 = tru \/ t1 = fls)
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
    + inversion H. rename x into t1'. eauto. 
Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Inversion Lemmas for Typing *)
(* end hide *)
(** ** 型付けの反転補題 *)

(* begin hide *)
(** The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement [Gamma |- \x:S1.t2 \in T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)
(* end hide *)
(** 保存定理の証明はサブタイプを追加したことでやはり少し複雑になります。
    その理由は、上述の「サブタイプの反転補題」と同様に、純粋なSTLCでは定義から明らかであった（形式的には、[inversion]タクティックからすぐに得られた）性質が、サブタイプの存在で本当の証明を必要とするようになったためです。
    サブタイプがある場合、同じ[has_type]の主張を導出するのに複数の方法があるのです。
 
    以下の反転補題は、もし関数抽象の型付け主張 [Gamma |- \x:S1.t2 \in T] の導出があるならば、その導出の中に本体[t2]の型を与える部分が含まれている、ということを言うものです。 *)

(* begin hide *)
(** _Lemma_: If [Gamma |- \x:S1.t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |- t2 \in S2] and [S1 -> S2 <: T].

    (Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!)

    _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |-
     \x:S1.t2 \in T].  Cases [T_Var], [T_App], are vacuous as those
     rules cannot be used to give a type to a syntactic abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need: [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |- \x:S1.t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans].

    Formally: *)
(* end hide *)
(** 「補題」: もし [Gamma |- \x:S1.t2 \in T] ならば、型[S2]が存在して [x|->S1; Gamma |- t2 \in S2] かつ [S1 -> S2 <: T] となる。
 
    （この補題は「[T]はそれ自身が関数型である」とは言っていないことに注意します。
    そうしたいところですが、それは成立しません!）
 
    「証明」:[Gamma]、[x]、[S1]、[t2]、[T]を補題の主張に記述された通りとする。
    [Gamma |- \x:S1.t2 \in T] の導出についての帰納法で証明する。
    [T_Var]と[T_App]の場合はあり得ない。
    これらは構文的に関数抽象の形の項に型を与えることはできないからである。
 
     - 導出の最後のステップ使われた規則が[T_Abs]の場合、型[T12]が存在して [T = S1 -> T12] かつ [x:S1; Gamma |- t2 \in T12] である。
       [S2]として[T12]をとると、[S_Refl]より [S1 -> T12 <: S1 -> T12] となり、求める性質が成立する。
 
     - 導出の最後のステップ使われた規則が[T_Sub]の場合、型[S]が存在して [S <: T] かつ [Gamma |- \x:S1.t2 \in S] となる。
       型付け導出の帰納仮定より、型[S2]が存在して [S1 -> S2 <: S] かつ [Gamma, x:S1 |- t2 \in S2] である。
       この[S2]を採用すれば、 [S1 -> S2 <: T] であるから[S_Trans]より求める性質が成立する。
 
    形式的には： *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (abs x S1 t2) \in T ->
     exists S2,
       Arrow S1 S2 <: T
       /\ (x |-> S1 ; Gamma) |- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (abs x S1 t2) as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T12...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

(* begin hide *)
(** Similarly... *)
(* end hide *)
(** 同様に... *)

Lemma typing_inversion_var : forall Gamma x T,
  Gamma |- (var x) \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (var x) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Var *)
    exists T...
  - (* T_Sub *)
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- (app t1 t2) \in T2 ->
  exists T1,
    Gamma |- t1 \in (Arrow T1 T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (app t1 t2) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_App *)
    exists T1...
  - (* T_Sub *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
Qed.

Lemma typing_inversion_true : forall Gamma T,
  Gamma |- tru \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tru as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
  Gamma |- fls \in T ->
  Bool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember fls as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  Gamma |- (test t1 t2 t3) \in T ->
  Gamma |- t1 \in Bool
  /\ Gamma |- t2 \in T
  /\ Gamma |- t3 \in T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (test t1 t2 t3) as t.
  induction Hty; intros;
    inversion Heqt; subst; try solve_by_invert.
  - (* T_Test *)
    auto.
  - (* T_Sub *)
    destruct (IHHty H0) as [H1 [H2 H3]]...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- unit \in T ->
    Unit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember unit as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

(* begin hide *)
(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)
(* end hide *)
(** 型付けについての反転補題と関数型の間のサブタイプの反転補題は「結合補題(combination lemma)」としてまとめることができます。
    この補題は以下で実際に必要になるものを示します。 *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |- (abs x S1 s2) \in (Arrow T1 T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...  Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Context Invariance *)
(* end hide *)
(** ** コンテキスト不変性 *)

(* begin hide *)
(** The context invariance lemma follows the same pattern as in the
    pure STLC. *)
(* end hide *)
(** コンテキスト不変性補題は、純粋なSTLCと同じパターンをとります。 *)

Inductive appears_free_in : string -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (abs y T11 t12)
  | afi_test1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (test t1 t2 t3)
  | afi_test3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (test t1 t2 t3)
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
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold update, t_update. destruct (eqb_stringP x x0)...
  - (* T_Test *)
    apply T_Test... 
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  induction Htyp;
      subst; inversion Hafi; subst...
  - (* T_Abs *)
    destruct (IHHtyp H4) as [T Hctx]. exists T.
    unfold update, t_update in Hctx.
    rewrite <- eqb_string_false_iff in H2.
    rewrite H2 in Hctx... Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Substitution *)
(* end hide *)
(** ** 置換 *)

(* begin hide *)
(** The _substitution lemma_ is proved along the same lines as
    for the pure STLC.  The only significant change is that there are
    several places where, instead of the built-in [inversion] tactic,
    we need to use the inversion lemmas that we proved above to
    extract structural information from assumptions about the
    well-typedness of subterms. *)
(* end hide *)
(** 置換補題(_substitution lemma_)は純粋なSTLCと同じ流れで証明されます。
    唯一の大きな変更点は、いくつかの場所で、
    部分項が型を持つことについての仮定から構造的情報を抽出するために、
    Coqの[inversion]タクティックを使う代わりに上で証明した反転補題を使う必要があることです。 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (x |-> U ; Gamma) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in S.
Proof with eauto.
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  induction t; intros; simpl.
  - (* var *)
    rename s into y.
    destruct (typing_inversion_var _ _ _ Htypt)
        as [T [Hctx Hsub]].
    unfold update, t_update in Hctx.
    destruct (eqb_stringP x y) as [Hxy|Hxy]; eauto;
    subst.
    inversion Hctx; subst. clear Hctx.
    apply context_invariance with empty...
    intros x Hcontra.
    destruct (free_in_context _ _ S empty Hcontra)
        as [T' HT']...
    inversion HT'.
  - (* app *)
    destruct (typing_inversion_app _ _ _ _ Htypt)
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  - (* abs *)
    rename s into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt)
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (Arrow T1 T2)... apply T_Abs...
    destruct (eqb_stringP x y) as [Hxy|Hxy].
    + (* x=y *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold update, t_update.
      destruct (eqb_string y x)...
    + (* x<>y *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold update, t_update.
      destruct (eqb_stringP y z)...
      subst.
      rewrite <- eqb_string_false_iff in Hxy. rewrite Hxy...
  - (* tru *)
      assert (Bool <: S)
        by apply (typing_inversion_true _ _  Htypt)...
  - (* fls *)
      assert (Bool <: S)
        by apply (typing_inversion_false _ _  Htypt)...
  - (* test *)
    assert  ((x |-> U ; Gamma) |- t1 \in Bool
         /\  (x |-> U ; Gamma) |- t2 \in S
         /\  (x |-> U ; Gamma) |- t3 \in S)
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  - (* unit *)
    assert (Unit <: S)
      by apply (typing_inversion_unit _ _  Htypt)... 
Qed.

(* ================================================================= *)
(* begin hide *)
(** ** Preservation *)
(* end hide *)
(** ** 保存 *)

(* begin hide *)
(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and again using inversion lemmas from above to extract structural
    information from typing assumptions. *)
(* end hide *)
(** （型の）保存の証明は以前の章とほとんど同じです。
    適切な場所で置換補題を使い、型付け仮定から構造的情報を抽出するために上述の反転補題をまた使います。 *)

(* begin hide *)
(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |- t \in T] and [t --> t'], then [empty |- t' \in
    T].

    _Proof_: Let [t] and [T] be given such that [empty |- t \in T].  We
    proceed by induction on the structure of this typing derivation,
    leaving [t'] general.  The cases [T_Abs], [T_Unit], [T_True], and
    [T_False] cases are vacuous because abstractions and constants
    don't step.  Case [T_Var] is vacuous as well, since the context is
    empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that
       [t = t1 t2], [T = T2], [empty |- t1 \in T1 -> T2], and
       [empty |- t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S.t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |- s2 \in T2].
       It then follows by the substitution lemma
       ([substitution_preserves_typing]) that [empty |- [x:=t2]
       t12 \in T2] as desired.

      - If the final step of the derivation uses rule [T_Test], then
        there are terms [t1], [t2], and [t3] such that [t = test t1 then
        t2 else t3], with [empty |- t1 \in Bool] and with [empty |- t2
        \in T] and [empty |- t3 \in T].  Moreover, by the induction
        hypothesis, if [t1] steps to [t1'] then [empty |- t1' : Bool].
        There are three cases to consider, depending on which rule was
        used to show [t --> t'].

           - If [t --> t'] by rule [ST_Test], then [t' = test t1' then t2
             else t3] with [t1 --> t1'].  By the induction hypothesis,
             [empty |- t1' \in Bool], and so [empty |- t' \in T] by
             [T_Test].

           - If [t --> t'] by rule [ST_TestTrue] or [ST_TestFalse], then
             either [t' = t2] or [t' = t3], and [empty |- t' \in T]
             follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)
(* 訳注：一カ所型付けの書き方が[empty |- t1' : Bool] になっている。 *)
(* end hide *)
(** 「定理」（保存）： [t]、[t']が項で[T]が型であり、[empty |- t \in T] かつ [t --> t'] ならば、[empty |- t' \in T] である。
 
    「証明」：[t] と [T] が [empty |- t \in T] であるとする。
    証明は、[t']を特化しないまま型付け導出の構造に関する帰納法で進める。
    (最後の規則が)[T_Abs]、[T_Unit]、[T_True]、[T_False]の場合は考えなくて良い。
    なぜなら関数抽象と定数はステップを進めないからである。
    [T_Var]も考えなくて良い。なぜならコンテキストが空だからである。
 
     - もし導出の最後のステップの規則が[T_App]ならば、項[t1] [t2] と型 [T1] [T2] が存在して、[t = t1 t2]、[T = T2]、 [empty |- t1 \in T1 -> T2]、[empty |- t2 \in T1] である。
 
       ステップ関係の定義から、[t1 t2] がステップする方法は3通りである。
       [ST_App1]と[ST_App2]の場合、型付け導出の帰納仮定と[T_App]より求める結果がすぐに得られる。
 
       [t1 t2] のステップが [ST_AppAbs] によるとする。
       するとある型[S]と項[t12]について [t1 = \x:S.t12] であり、かつ [t' = [t2/x]t12] である。
 
       補題[abs_arrow]より、[T1 <: S] かつ [x:S1 |- s2 \in T2] となる。
       すると置換補題（[substitution_preserves_typing]）より、 [empty |- [t2/x]t12 \in T2] となるがこれが求める結果である。
 
      - もし導出の最後のステップで使う規則が[T_Test]ならば、項[t1]、[t2]、[t3]が存在して [t = test t1 then t2 else t3] かつ [empty |- t1 \in Bool] かつ [empty |- t2 \in T] かつ [empty |- t3 \in T]となる。
        さらに帰納法の仮定より、もし[t1]がステップして[t1']に進むならば [empty |- t1' \in Bool] である。
        [t --> t'] を示すために使われた規則によって、3つの場合がある。
 
           - [t --> t'] が規則[ST_Test]による場合、 [t' = test t1' then t2 else t3] かつ [t1 --> t1'] となる。
             帰納法の仮定より [empty |- t1' \in Bool] となり、これから[T_Test]より [empty |- t' \in T] となる。
 
           - [t --> t'] が規則[ST_TestTrue]または[ST_TestFalse]による場合、 [t' = t2] または [t' = t3] であり、仮定から [empty |- t' \in T] となる。
 
     - もし導出の最後のステップで使う規則が[T_Sub]ならば、型[S]が存在して [S <: T] かつ [empty |- t \in S] となる。
       型付け導出についての帰納法の仮定と[T_Sub]の適用から結果がすぐに得られる。 [] *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t --> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  induction HT;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  - (* T_App *)
    inversion HE; subst...
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T... 
Qed.

(* ================================================================= *)
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:

    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e., (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e., (Nat,(Top,(Nat,Top)))

    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. *)

(* ================================================================= *)
(* begin hide *)
(** ** Exercises *)
(* end hide *)
(** ** 練習問題 *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (variations)  

    Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

    - Suppose we add the following typing rule:

                           Gamma |- t \in S1->S2
                    S1 <: T1     T1 <: S1      S2 <: T2
                    -----------------------------------    (T_Funny1)
                           Gamma |- t \in T1->T2

    - Suppose we add the following reduction rule:

                             --------------------         (ST_Funny21)
                             unit --> (\x:Top. x)

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny3)
                               Unit <: Top->Top

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny4)
                               Top->Top <: Unit

    - Suppose we add the following reduction rule:

                             ---------------------      (ST_Funny5)
                             (unit t) --> (t unit)

    - Suppose we add the same reduction rule _and_ a new typing rule:

                             ---------------------       (ST_Funny5)
                             (unit t) --> (t unit)

                           --------------------------    (T_Funny6)
                           empty |- unit \in Top->Top

    - Suppose we _change_ the arrow subtyping rule to:

                          S1 <: T1 S2 <: T2
                          -----------------              (S_Arrow')
                          S1->S2 <: T1->T2

*)
(* end hide *)
(** **** 練習問題: ★★, standard (variations)
 
    この問題の各部分は、Unitとサブタイプを持つSTLCの定義を変更する別々の方法を導きます。
    （これらの変更は累積的ではありません。各部分はいずれも元々の言語から始まります。）
    各部分について、（進行、保存の）性質のうち偽になるものをリストアップしなさい。
    偽になる性質について、反例を示しなさい。
    - 次の型付け規則を追加する:
<<
                           Gamma |- t \in S1->S2 
                    S1 <: T1     T1 <: S1      S2 <: T2 
                    -----------------------------------    (T_Funny1) 
                           Gamma |- t \in T1->T2 
>>
    - 次の簡約規則を追加する:
<<
                             --------------------         (ST_Funny21) 
                             unit --> (\x:Top. x) 
>>
    - 次のサブタイプ規則を追加する:
<<
                               ----------------          (S_Funny3) 
                               Unit <: Top->Top 
>>
    - 次のサブタイプ規則を追加する:
<<
                               ----------------          (S_Funny4) 
                               Top->Top <: Unit 
>>
    - 次の評価規則を追加する:
<<
                             ---------------------      (ST_Funny5) 
                             (unit t) --> (t unit) 
>>
    - 上と同じ評価規則と新たな型付け規則を追加する:
<<
                             ---------------------       (ST_Funny5) 
                             (unit t) --> (t unit) 
 
                           --------------------------    (T_Funny6) 
                           empty |- unit \in Top->Top 
>>
    - 関数型のサブタイプ規則を次のものに変更する:
<<
                          S1 <: T1 S2 <: T2 
                          -----------------              (S_Arrow') 
                          S1->S2 <: T1->T2 
>>
 *)

(* Do not modify the following line: *)
Definition manual_grade_for_variations : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Exercise: Adding Products *)
(* end hide *)
(** * 練習問題: 直積の追加 *)

(* begin hide *)
(** **** Exercise: 5 stars, standard (products)  

    Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension by modifying the definitions and proofs above:

    - Add constructors for pairs, first and second projections,
      and product types to the definitions of [ty] and [tm], and
      extend the surrounding definitions accordingly
      (refer to chapter [MoreSTLC]):

        - value relation
        - substitution
        - operational semantics
        - typing relation

    - Extend the subtyping relation with this rule:

                        S1 <: T1    S2 <: T2
                        --------------------   (S_Prod)
                         S1 * S2 <: T1 * T2

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add a couple of completely new lemmas.) *)
(* end hide *)
(** **** 練習問題: ★★★★★, standard (products)
 
    定義したシステムに対、射影、直積型を追加することは比較的簡単な問題です。
    上の定義や証明を書き換える形でこの拡張を行いなさい:
 
    - 対のコンストラクタ、第1射影、第2射影、直積型を [ty] と [tm] の定義に追加し、それに伴う以下の定義を（[MoreSTLC]章を参考に）拡張しなさい。
 
        - 値関係
        - 置換
        - 操作的意味
        - 型付け関係
 
    - サブタイプ関係に次の規則を追加しなさい。
<<
                        S1 <: T1    S2 <: T2 
                        --------------------   (S_Prod) 
                         S1 * S2 <: T1 * T2 
>>
    - 型付け関係に、[MoreSTLC]の章と同様の、対と射影の規則を拡張しなさい。
 
    - 進行および保存、およびそのための補題の証明を、新しい構成要素を扱うように拡張しなさい。
      （いくつか新しい補題を追加する必要もあるでしょう。） *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_products : option (nat*string) := None.
(** [] *)

(* Fri Feb 8 06:31:30 EST 2019 *)

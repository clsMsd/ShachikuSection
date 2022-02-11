# ラムダ計算入門

## ラムダ計算とは?
> Lambda calculus (also written as λ-calculus) is a formal system in mathematical logic  
> for expressing computation based on function abstraction and application using variable binding and substitution.  
> It is a universal model of computation that can be used to simulate any Turing machine.  
> It was introduced by the mathematician Alonzo Church in the 1930s as part of his research into the foundations of mathematics.  
> (Wikipediaより引用)

ラムダ計算の話に入る前に、単純な算術式の計算について考える。  
例えば、2 * 3 + 1 という式を計算するとき、我々はまず 2 * 3 を 6 に置き換えて 6 + 1 という式を作り、  
さらにそれを 7 に置き換えるという流れで計算を行う。
```
2 * 3 + 1
= 6 + 1
= 7
```
つまり、このような算術式の計算とは式の中のある部分(項)を別の項に置き換えていくことであるといえる  
(このようなある式の項を別の項に置き換えていく手法のことを *項書き換え* という(そのまんまだ...))。  

しかし、普通の算術式の項書き換えのルールは四則演算に限ってもかなり複雑であるし、  
関数や条件分岐のようなものを表現できるような拡張された算術式のルールを作ろうとするとさらに複雑になってしまい、  
計算そのものを研究する上での考察対象としては、不適切という程までではないが、扱いづらい代物である。  

そこで、より単純な項書き換えのルールを持ちながら普通の算術式と同等かそれ以上の計算能力を持つ計算モデルとして考え出されたのがラムダ計算である  
(本当の歴史では計算モデルというよりも論理学の研究の一環で作られたらしいが論理も計算みたいなもんなのでまあええやろ)。  
ラムダ計算は、ラムダ式と呼ばれる式(記号の羅列)に対して機械的なルールに基づき項書き換えを行っていくという計算モデルである。  

ラムダ計算は最も単純なプログラミング言語であると言われることもある。  
(ただし、単純に「チューリング完全ならプログラミング言語」ということになると、普通の算術式(算術式の定義にもよるが、ここではμ再帰関数を表すこととする)もプログラミング言語ということになるし、
型なしラムダ計算はプログラミング言語だが単純型付きラムダ計算はプログラミング言語ではないということになってしまうのでどうなんだ？という感はある。
個人的には
1. 計算機上での処理系の実装が1つ以上存在するか、(少なくとも)かつて存在した
1. 標準入出力を扱うことができる
ような言語をプログラミング言語と呼びたいという思いがある。
(なので Brainf*ck や Unlambda はプログラミング言語であるといえるが LazyK はプログラミング言語ではないと言いたい(個人の感想です)
(あとこの定義だとJavaScriptとかActionScriptみたいに標準入出力の概念がない言語はどうなるんだという問題もある...)))

またラムダ計算は型の有無や強さによって複数のバリエーションがあるが、本記事で単にラムダ計算と書いた場合には基本的に型無しラムダ計算を指すものとする。  

## ラムダ式の文法(Syntax)
```
t ::=       項
   x        変数
   λx.t   ラムダ抽象(関数定義)
   t t    関数適用
```

括弧が省略された場合の関数適用は *左結合* である。
つまり、 `t1 t2 t3` という式は `(t1 t2) t3` と同じ意味であって、`t1 (t2 t3)` ではない。  

括弧が省略された場合のλ抽象の本体はできる限り右側へ拡大する。  
つまり、`λx.λy.x y x` という式は `λx.(λy.(x y x))` と同じ意味であって、 `(λx.(λy.x y) x)` ではない。  
`λx.λy.x y x` という式はさらに省略して `λxy.xyx` と書くことができる。  

しかし，個人的な意見としてラムダ記法自体が慣れるまでかなり分かりづらい上にこのような略記法まで使われると初学者は非常に混乱しがちである(実体験)。  
そこで、しばらくの間は普通のラムダ記法と略記したラムダ記法，さらにJavaScriptでの等価なコードの3パターンを併記することにする。  
またラムダ式にコメントという概念は無いが、この文章中のラムダ式ではJavaScriptと同じコメントの記法を使うものとする。

余談だが，数学で普通に使われる関数の記法は実はかなり良くない(個人の感想です)。  
例えば，数学では f(x) = 2x + 1 のような表記をよくするが，  
よくよく考えるとこれは左辺によって右辺が関数であるかただの式であるかが決まる  
(単に 2x + 1と書いてあればただの式であるが、左辺が f(x) のように書かれていると関数になる)。  
つまり右辺の情報だけではただの式か関数なのか判別できない。
普通、定義式と言ったら「左辺を右辺で定義する」(別に逆でも良いが) はずなので、  
左辺にくるものによって意味が変わるというのは変な話である。  
また、f(x) と書かれていた場合、これはこの式の外で x が定義されていなければ関数そのものを表すが，  
xが定義されていればただの値となる(例えばこの式の上に x = 0 と書かれていれば f(x) は 1 の別の書き方に過ぎない)。  
なので同じ表記でも文脈によって意味が変わってしまう。  
一方でラムダ記法の場合は x + 1 ならただの式、λx.x + 1 なら関数となるので、式と関数の違いが一目瞭然である。  

更に余談だが物理ではもっと雑な記法が使われることがあり，例えばある関数 f(x) に対してそのフーリエ変換を F(ω) と書いたりするが，  
めんどくさがりな物理屋は時々これを f(ω) と書いてフーリエ変換された関数であることを表したりする。  
これは仮引数の文字が変わることで関数の実態が変わっているということなので、よく考えるととんでもないことである。  

## ラムダ式の意味(Semantics)
ラムダ式の評価は次の規則を機械的に適用して行われる。  

### β変換(β簡約)
一言でいうと、関数適用。  
ラムダ式の本体(`.`の後の部分)に現れる仮引数(`λ`の直後の文字)を実引数で置き換える。
例:
`(λx.x) a` → `a`
`(λxy.xy) a` → `λx.(λy.xy) a` → `(λy.a y)`

### α変換
一言でいうと、変数のリネーム。
例えば`λx.x`と`λy.y`という2つの関数は同じであるので前者を後者で置き換える(=式中の`x`を`y`に置換する)ということは自由にできる。  

これ以外にη変換というものもあるが、本質的に重要ではないのとなんだかよく分からんのでこの説明は省略する。

## ラムダ計算とチューリング完全
上で定義したラムダ計算でできることといえば関数の定義と関数の(引数への)適用ぐらいで、足し算や引き算といった四則演算すら定義に含まれていないが、  
(型無し)ラムダ計算はチューリング完全であり、いわゆる普通のコンピューターが行う全ての計算はラムダ計算でも同じように実行できることが知られている。  

### 自然数の計算
ラムダ計算で自然数を表現する方法はいくつかあるが、よく知られたものの1つに *チャーチ数* があり、次のように定義される。  
```
C0 = λfx.x = λf.(λx. x)                // 自然数の 0 に対応
C1 = λfx.fx = λf.(λx. fx)              // 自然数の 1 に対応
C2 = λfx.f(fx) = λf.(λx. f(fx))        // 自然数の 2 に対応
C3 = λfx.f(f(fx)) = λf.(λx. f(f(fx)))  // 自然数の 3 に対応
...
Cn = λfx.f^n(x)
```
(ただし、`f^n(x)` は `f(f(...f(x)))` の意味。  
また `C0 = λfx.x` のような書き方は便宜的なもの(これ以降のラムダ式中に`C0`が出てきたら`λfx.x`と書かれているのと全く同じであると考えて欲しいということ)であって、
ラムダ計算にこのような表記がある訳ではない。)  

このような自然数の表現を *チャーチ数* または *チャーチエンコーディング* という。  
(正確にはチャーチエンコーディングで表現された自然数をチャーチ数と呼ぶ)

定義を見れば分かるように、チャーチ数は「第1引数に受け取った関数を第2引数にn回適用した結果を返す関数」であると言える。  

JavaScriptでの等価なコード
```javascript
const C0 = f => x => x
const C1 = f => x => f(x)
const C2 = f => x => f(f(x))
const C3 = f => x => f(f(f(x)))
const C4 = f => x => f(f(f(f(x))))
const C5 = f => x => f(f(f(f(f(x)))))
// ...(以下同様)

// チャーチ数を普通の自然数に変換する関数
const ToNat = c => {
   let val = 0
   c(x => { val++; return x })(0)
   return val
}

// 普通の自然数をチャーチ数に変換する関数
const ToChurch = n => f => x => {
   let res = x
   for (let i = 0; i < n; i++) {
      res = f(res)
   }
   return res
}

// チャーチ数を普通の自然数に変換する関数(再帰を使ったバージョン)
const ToNatRec = c => c(x => x + 1)(0)

// 普通の自然数をチャーチ数に変換する関数(再帰を使ったバージョン)
const ToChurchRec = n => f => x => n == 0 ? x : ToChurchRec(n - 1)(f)(f(x))

// 実際に確かめる
console.assert(ToNat(C0) == 0)
console.assert(ToNat(C1) == 1)
console.assert(ToNat(C2) == 2)

// JavaScriptでは関数の等値性の判定はできないのでToChurchの正しさは普通の自然数からチャーチ数に変換したあとまた自然数に戻すことで確かめる
console.assert(ToNat(ToChurch(0)) === 0)
console.assert(ToNat(ToChurch(1)) === 1)
console.assert(ToNat(ToChurch(2)) === 2)

console.assert(ToNatRec(C0) == 0)
console.assert(ToNatRec(C1) == 1)
console.assert(ToNatRec(C2) == 2)

console.assert(ToNatRec(ToChurchRec(0)) === 0)
console.assert(ToNatRec(ToChurchRec(1)) === 1)
console.assert(ToNatRec(ToChurchRec(2)) === 2)
```

チャーチ数は自然数の表現である以上、足し算や引き算といった四則演算が定義できる必要がある(できなかったら自然数の表現しているとは言えないので)。  
実際にチャーチ数に対する四則演算の定義をみて見よう。  

あるチャーチ数を受け取りその数に +1 したチャーチ数を返す関数(後者関数: SUCC)は次のように定義できる。
```
SUCC = λnfx.f (n f x) = λn.(λf.(λx. f ((n f) x)))

// SUCC を C0 に適用した場合
SUCC C0
= (λnfx.f (n f x)) (λgy.y)
= (λfx. f ((λgy.y) f x))
= (λfx. f ((λy.y) x))
= (λfx. f x)
= C1

// SUCC を C1 に適用した場合
SUCC C1
= (λnfx.f (n f x)) (λgy.gy)
= (λfx. f ((λgy.gy) f x))
= (λfx. f ((λy.fy) x))
= (λfx. f (f x))
= C2
```

上で述べたようにチャーチ数は「第1引数に受け取った関数を第2引数にn回適用した結果を返す関数」といえるので、  
チャーチ数Cnの第1引数として後者関数を適用すれば、第2引数に後者関数をn回適用した結果、つまり第2引数を +n した結果が得られる。  
つまり足し算を行う関数(PLUS)は次のように定義できる。
```
PLUS = λmn. m SUCC n

// チャーチ数による 0 + 1 の計算
PLUS C0 C1
= (λmn. m SUCC n) (λfx.x) (λfx.fx)
= (λfx.x) SUCC (λfx.fx)
= (λfx.x) (λnfx.f (n f x)) (λfx.fx)
= (λx.x) (λfx.fx)
= (λfx.fx)
= C1

PLUS C1 C0
= (λmn. m SUCC n) (λfx.fx) (λfx.x) 
= (λfx.fx) SUCC (λfx.x)
= (λfx.fx) (λnfx.f (n f x)) (λfx.x)
```

掛け算は足し算をn回繰り返したものなので、次のように定義できる。
```
MULT = λmn. m (PLUS n) C0
```

JavaScriptでの等価なコード
```javascript
const SUCC = n => f => x => f(n(f)(x))
const PLUS = m => n => m(SUCC)(n)
const MULT = m => n => m(PLUS(n))(C0)

// 実際に確かめる
console.assert(ToNat(SUCC(C0)) === 1)
console.assert(ToNat(SUCC(C1)) === 2)
console.assert(ToNat(SUCC(C2)) === 3)

console.assert(ToNat(PLUS(C0)(C0)) === 0)
console.assert(ToNat(PLUS(C0)(C1)) === 1)
console.assert(ToNat(PLUS(C1)(C0)) === 1)
console.assert(ToNat(PLUS(C1)(C2)) === 3)

console.assert(ToNat(MULT(C0)(C0)) === 0)
console.assert(ToNat(MULT(C0)(C1)) === 0)
console.assert(ToNat(MULT(C1)(C0)) === 0)
console.assert(ToNat(MULT(C1)(C2)) === 2)
console.assert(ToNat(MULT(C2)(C3)) === 6)
console.assert(ToNat(MULT(C3)(C3)) === 9)
```

チャーチエンコーディングとは別の自然数の表現として *スコットエンコーディング* というものがあり、次のように定義される。
```
S0 = λfx.x
S1 = λfx.f (λfx.x)
S2 = λfx.f (λfx.f (λfx.x))
S3 = λfx.f (λfx.f (λfx.f (λfx.x)))
...

SUCC = λnfx.f n
```

JavaScriptでの等価なコード
```javascript
const S0 = f => x => x
const S1 = f => x => f(f => x => x)
const S2 = f => x => f(f => x => f(f => x => x))
const S3 = f => x => f(f => x => f(f => x => f(f => x => x)))
const S4 = f => x => f(f => x => f(f => x => f(f => x => f(f => x => x))))
const S5 = f => x => f(f => x => f(f => x => f(f => x => f(f => x => f(f => x => x)))))

const ToNat = s => {
   let val = -1
   while(true) {
      if (typeof s !== "function") { break }
      s = s(x => x)(0)
      val++
   }
   return val
}

const ToScott = n => {
   let res = f => x => x
   for (let i = 0; i < n; i++) {
      res = f => x => f(res)
   }
   return res
}

const ToNatRec = s => {
   const _ToNatRec = n => s => typeof s === "function" ? _ToNatRec(n + 1)(s(x => x)(0)) : n
   return _ToNatRec(-1)
}
const ToScottRec = n => f => x => n === 0 ? x : f(ToScottRec(n - 1))

const SUCC = n => f => x => f(n)
```

ただしこちらはかなり影が薄い。

### 条件分岐
条件分岐をする関数`IFELSE`は、第1引数として`TRUE`か`FALSE`を取り、  
第1引数が`TRUE`なら第2引数を、第1引数が`FALSE`なら第3引数を返すような次の関数として定義できる。
```
TRUE = λxy.x = λx.(λy.x)
FALSE = λxy.y = λx.(λy.y)
IFELSE = λxyz.xyz = λx.(λy.(λz.(x y) z))

// 第1引数が TRUE のときは 第2引数を返す
IFELSE TRUE M N
= (λxyz.xyz) (λxw.x) M N
= (λyz.(λxw.x) y z) M N
= (λz.(λxw.x) M z) N
= (λxw.x) M N
= (λw. M) N
= M

// 第1引数が FALSE のときは 第3引数を返す
IFELSE FALSE M N
= (λxyz.xyz) (λxw.w) M N
= (λyz.(λxw.w) y z) M N
= (λz.(λxw.w) M z) N
= (λxw.w) M N
= (λw.w) N
= N
```

β簡約によってλ式が踊るのをやめてしまった例  
https://twitter.com/youichi_upw/status/1229797660032294912

JavaScriptでの等価なコード
```javascript
const TRUE = x => y => x
const FALSE = x => y => y
const IFELSE = x => y => z => x(y)(z)

// 実際に確かめる
console.log(IFELSE(TRUE)("t")("f")) //=> t
console.log(IFELSE(FALSE)("t")("f")) //=> f
```

### 再帰関数
ラムダ計算には「関数に名前を付ける」という機能が無いので一見すると再帰関数を定義できないように思えるが、  
下に書くYコンビネータというものを使うとラムダ計算でも再帰関数を作ることができる。

```
Y = (λf. (λx. f (x x)) (λx. f (x x)))

Y g
= (λf. (λx. f (x x)) (λx. f (x x))) g
= (λx. g (x x)) (λx. g (x x))
= g ((λx. g (x x)) (λx. g (x x)))
= g (Y g)
```

<!-- ```javascript
const Y = f => (x => f(x(x))(x => f(x(x)))
```

Sum(x) = if x = 0 then 0 else f(x - 1) + x -->

<!-- ```
_SUM = 
SUM = Y _SUM
```

```
Z = λf. (λx. f (λy. x x y)) (λx. f (λy. x x y))
``` -->

## β正規形とチャーチ・ロッサーの定理
ラムダ式がそれ以上β簡約できないとき、そのラムダ式はβ正規形であるという。  
β正規形の例: `λx.x` (関数に適用する実引数が無いのでこれ以上簡約できない = β正規系である)  
β正規形でない例: `(λx.x) y` (実引数(`y`)を適用できるのでまだ簡約できる = β正規系でない)  

ラムダ式はβ正規形の観点から次の3種類に分けられる。
1. β簡約を繰り返すことで必ずβ正規形になるもの、又は既にβ正規形になっているもの  
   例: `(λx.x) y`  
   JavaScriptの等価コード: `(x => x)(y)`  
   簡約の仕方は1通りしか無く、簡約すると `y` になる
1. β簡約を何度繰り返してもβ正規形にならないもの(無限にβ簡約できるもの)  
   例: `(λx.xx)(λx.xx)`  
   JavaScriptの等価コード: `(x => x(x))(x => x(x))`  
   どれだけ簡約を繰り返しても `(λx.xx)(λx.xx)` のままである
1. β簡約の順番により、β正規形になったりならなかったりするもの  
   例: `(λxy.y) ((λx.xx) (λx.xx))`  
   JavaScriptの等価コード: `(x => y => y) ((x => x(x) (x => x(x))`  
   引数部の `((λx.xx)(λx.xx))` から簡約すると上で述べたように無限に簡約が終わらないが、
   `(λxy.y)` から簡約すると第1引数が消えるので `(λy.y)` になる。

「ラムダ式をどの部分からβ簡約をするか」という，β簡約の順番の決め方のことを *評価戦略* 又は *簡約戦略* という。  
上で書いたようにラムダ式は評価戦略によってβ正規形になるかどうかが変わってしまうことがあるのだが、幸いなことに式中の一番左にあるラムダに着目してβ簡約を行って行けば  
(β正規形を持つラムダ式ならば)必ずβ正規形にたどり着けることが知られている(このような一番左側のラムダから簡約を行う評価戦略のことを *最左戦略* という)ので、  
特別な理由が無いなら最左戦略で簡約すればよい。 

任意のラムダ式について、そのラムダ式がβ正規形を持つかどうかを判定するアルゴリズムは存在しないことが知られている。  

また、もしラムダ式がβ正規形を持つならば、そのβ正規形は唯一つであるということが知られている  
(つまり、ラムダ式に対してどのような簡約戦略でβ簡約を行っても、(もしβ簡約が終了するならば)最終的に得られるβ正規形は同じになる)。  
この性質を *合流性*、または *チャーチ・ロッサー性* という。  
これは計算モデルとしては嬉しい性質である。例えば 1 + 1 を計算した結果が計算方法によって 2 になったり 3 になったりしたら困るし、  
実際の計算機でラムダ計算を実装するときに β簡約を複数コアで並行に実行しても結果が変わらないとなれば嬉しいことが分かるだろう。  

ちなみに，ある計算モデルがどのような計算を行っても必ず計算が終了し意味のある値を返すという性質を持つ場合，そのような性質のことを *停止性* という。  
さらに，停止性と合流性の両方を満たすシステムは *完備* であるという。  
例えば四則演算からなる算術式(1 + 2 とか 3 * 4 + 5 のような式)は完備である。  
一方で，上で述べたように(型無し)ラムダ計算は停止性を満たさないので完備ではない。  
また今回は詳しく述べないが，単純型付きラムダ計算は(合流性に加えて)停止性を満たすので完備である。  
またこれも今回は詳しく述べないが，calculus of constructions(CoC) という究極の型付きラムダ計算(?)があるがこれも完備である、らしい。  

よく分かるラムダキューブ
```
::::::::　　　　　　　　  ┌─────────────────────────────────────────┐
::::::::　　　　　　　　  │　また型無しラムダ計算がやられたようだな…    │
:::::　　 ┌──────────────└──────────────────ｖ───┬─────────────────┘
:::::　　 │フフフ…奴は八天王の中でも最弱 … 　　　   │
┌─────────└────────────────ｖ─┬──────────────────┘
│　停止性の保証さえできないとは　│
│　ラムダ計算の面汚しよ         │
└────ｖ───────────────────────┘
　 |ﾐ, ／　 ｀ヽ　/!　　　　  ,.──､
　 |彡/二Oニニ|ノ　　　      /三三三!,　　　　　　|!
　　`,' ＼､､＿,|/-ｬ　　     ト `=j r=ﾚ　　   /ミ !彡
T 爪| /　/￣|/´＿_,ｬ　      |`三三‐/　　　　 |`=､|,='|
/人 ヽ ミ='／|`:::::::/ｲ＿_ ト｀ー く＿＿＿,-,､　_!_ /
/　　`ー─'" |_,.イ､ | |  /､　　 Y　 /| | | j/　ﾐ`┴'彡＼
　　　　  CoC　　　　　　　　System F　   単純型付きラムダ計算
```

一方で停止性が保証されるということはチューリング完全ではないということなので、型なしラムダ計算こそがラムダ計算の中で最強という見方もできる。
```
::::::::　　　　　　　　  ┌─────────────────────────────────────────┐
::::::::　　　　　　　　  │　また型付きラムダ計算がやられたようだな…    │
:::::　　 ┌──────────────└──────────────────ｖ───┬─────────────────┘
:::::　　 │フフフ…奴は計算モデルの中でも最弱 … 　　 │
┌─────────└──────────────────ｖ────────┬────────┘
│ アッカーマン関数さえ表現できないとは    │
│ 計算モデルの面汚しよ                  │
└────ｖ───────────────────────────────┘
　 |ﾐ, ／　 ｀ヽ　/!　　　　  ,.──､
　 |彡/二Oニニ|ノ　　　      /三三三!,　　　　　　|!
　　`,' ＼､､＿,|/-ｬ　　     ト `=j r=ﾚ　　   /ミ !彡
T 爪| /　/￣|/´＿_,ｬ　      |`三三‐/　　　　 |`=､|,='|
/人 ヽ ミ='／|`:::::::/ｲ＿_ ト｀ー く＿＿＿,-,､　_!_ /
/　　`ー─'" |_,.イ､ | |  /､　　 Y　 /| | | j/　ﾐ`┴'彡＼
   チューリングマシン　　　　 μ再帰関数　    型無しラムダ計算
```

## 参考資料
- http://www.kb.ecei.tohoku.ac.jp/~sumii/class/keisanki-software-kougaku-2005/lambda.pdf
- http://www.cs.tsukuba.ac.jp/~kam/complogic/2.pdf
- 型システム入門 第5章
- プログラム意味論
- プログラミング言語の基礎理論
- How did Haskell add Turing-completeness to System F? [https://stackoverflow.com/questions/25255413/how-did-haskell-add-turing-completeness-to-system-f]
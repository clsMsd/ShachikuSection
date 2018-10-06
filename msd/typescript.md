# Typescript

## Typescriptとは?

> TypeScript is a language for application-scale JavaScript. TypeScript adds optional types to JavaScript that support tools for large-scale JavaScript applications for any browser, for any host, on any OS. TypeScript compiles to readable, standards-based JavaScript. (https://github.com/Microsoft/TypeScript より引用)

Microsoftが作ったAltJSの1種

### Altjsとは?

Webフロントエンドの開発をJavascript以外の言語で行いたいというニーズは昔からあり、そのために何か別の言語でコードを書いてそれをJavascriptのコードに変換するという試みが行われていた（いる）。
そのようなJavascriptに変換することを想定した別言語のことを総称してAltjsと呼び、CoffeeScript、Dart、Haxe、Elm、PureScript、AtScriptなどの種類がある。
これらのAltjs(特にCoffeeScript)は2010年代前半ごろに盛り上がりを見せたが、ES2015がリリースされたころから段々と廃れつつある(ように見える)。
(参考: https://trends.google.co.jp/trends/explore?date=all&q=%2Fm%2F0hjc5m0)

### Altjs(CoffeeScript)が廃れた理由

- JavascriptがES2015で色々と機能追加されて、わざわざ別言語を使って開発を行うメリットが薄れた
- Altjs と Javascript の両方を習得する必要が出てくる
- Altjs → Javascript と余計な層が1枚追加されるのでトラブルシュートが大変になる

### Typescriptの特徴

前述のAltjsの欠点を避けるためか、Javascriptとの互換性が非常に強く意識されている。AltjsでありながらJavascriptに静的な型付けを行うことにのみ特化し、他の機能はほぼ取り入れていない。これは次のような利点と欠点を生じる。

利点
- ES2015以降機能が追加されたとはいえ、静的型付けと動的型付けでは越えられない壁があるので、わざわざ別言語を使うメリットがある
- 既にJavascriptを知っている開発者ならTypescriptは容易に習得できる(既存のJavascriptのコードはすべての型がAny型であるTypescriptのコードとみなせる)
- Typescriptのコードはトランスパイルされると型情報を取り除くだけでほぼそのままのJavascriptに変換されるので、トラブルシュートが容易である

欠点
- 何か取り入れて欲しい便利な機能があっても、Javascript側に無い機能は基本的に追加されない
    - 例えば、SwiftのOptional ChainingやC#のnull条件演算子 (`hoge?.fuga`のような書き方) はJS側の対応待ちということで取り入れられていない
- トランスパイル後は型情報が除かれたただのJavascriptのコードになるので、実行時の型チェックはJavascript任せになる

また、Javascriptとの互換性のためか、はたまたHejlsberg先生の趣味なのか、他の言語ではあまり見られない機能があるので紹介していきたい。

#### トランスパイル前後のコードの比較
トランスパイル前
```typescript
let s: string = "abc"
function add(a: number, b: number): number {
    return a + b
}
class Person {
    name: string
    age: number 
    constructor(name: string, age: number) {
        this.name = name
        this.age = age
    }
}
let p = new Person("masuda", 27)
```
トランスパイル後
```javascript
let s = "abc";
function add(a, b) {
    return a + b;
}
class Person {
    constructor(name, age) {
        this.name = name;
        this.age = age;
    }
}
let p = new Person("masuda", 27);

```

## 環境構築
``` 
npm install -g typescript
```
REPLが使いたい人は
```
npm install -g ts-node
```
### トランスパイルして実行
```bash
tsc sample.ts  # sample.jsが生成される
node sample.js
```

### コンパイラオプション
Typescriptはコンパイラオプション次第で割と挙動が変わるので、そのへんを把握しておかないとネットで拾ったサンプルコードがコンパイル通らない！という自体になる。
ハマりがちなコンパイルオプションを↓に挙げる。

- strictNullChecks: `false`にするとすべての型にnullが含まれる。`true`にすると明示的にnullを含めた型でないとnullが含まれない(いわゆるnull安全)。デフォルトでは`false`になっているが、`true`にすることが強く推奨されている。

```typescript
const s: string = null //strictNullChecksがtrueだとコンパイルエラー
```
- noImplicitAny: `true`にすると型推論で`any`型に推論されることが無くなる(明示的に指定しない限り`any`型にならない)。なので次のようなJavascriptのコードはnoImplicitAnyが`true`の場合は正しいTypescriptのコードと見なされない。

```typescript
let a = 1
a = "aaa" // noImplicitAnyがtrueだとコンパイルエラー
```
- strictFunctionTypes: `false`にすると関数の型がBivariantに、`true`にするとContravariantになる、らしい。

```typescript
interface Animal {}
class Dog implements Animal {}
class Cat implements Animal {}

const _animalFunc = (animal: Animal): void => {}
const _dogFunc = (dog: Dog): void => {}

let animalFunc = (animal: Animal): void => {}
let dogFunc = (dog: Dog): void => {}

dogFunc(new Dog()) 
dogFunc = _animalFunc // 問題無し
dogFunc(new Dog())
dogFunc(new Cat()) // コンパイルエラー

animalFunc(new Dog())
animalFunc = _dogFunc　// strictFunctionTypeがtrueだとコンパイルエラー
animalFunc(new Dog())
animalFunc(new Cat()) // コンパイルは通るが実行時型エラー
```

毎回コンパイルオプションを指定するのが面倒な場合は、ソースファイルと同じディレクトリに`tsconfig.json`という設定ファイルを作っておくとそちらを参照してコンパイルしてくれる。
`tsc --init`コマンドで設定ファイルの雛形が生成される。

### 型定義ファイルのインストール
Javascriptのライブラリを使う際に、型定義ファイルが提供されている場合はそれを使うことができる。
```
npm install --save-dev @types/(ライブラリ名)
```

## 基礎文法

### 変数

```typescript
let n: number = 1
n = 2
n = "aaa" // コンパイルエラー

let m = 2 // number型 と推論される
m = "aaa" // 普通の設定だとコンパイルエラー

let s: string = "aaa"
let b: boolean = true

let a: any = 1 // any型にするとなんでも代入できる
a = "aaa"
a = true

let arr: number[] = [1,2,3] // 配列はこう書く
```

### 関数

```typescript
function add(a: number, b: number): number {
    return a + b
}

// 戻り値の型は省略することもできる
function add(a: number, b: number) {
    return a + b
}

const add = function(a: number, b: number): number {
    return a + b
}

const add: (a: number, b: number) => number = function(a, b) {
    return a + b
}
```

### ラムダ式

```typescript
// 右辺に型を書いて左辺の型を推論する
const add = (a: number, b: number): number => a + b

// 左辺に型を書いて右辺の型を推論する
const add: (a: number, b:number) => number = (a, b) => a + b

// 両辺に型を書く
const add: (a: number, b:number) => number = (a: number, b: number): number => a + b
```

### Class 
```typescript
class Person {    
   // public/private/protectedの三種類のアクセス修飾子がある
   // 何も書かないとpublicになる
   name: string
   age: number
   constructor(name: string, age: number) {
      this.name = name
      this.age = age
   }

　　greet(): void {
      console.log(`I'm ${this.name}`)
   }
}

const p = new Person("masuda", 27)
```
次のような書き方もできる
``` typescript
class Person {
   constructor(
      public name: string,
      public age: number
   ) {}
}
```

### Interface
```typescript
interface Person {    
   name: string
   age: number
}
```

同名のinterfaceを別の場所で宣言すると勝手にマージされる
```typescript
// 上の書き方と同じ意味
interface Person {
   name: string
}
interface Person {
   age: number
}
```
Java等の普通の言語と同じように、クラスは単一継承しかできず、インターフェースは多重継承できる。

### Type alias
型に別名を付けることができる。
```typescript
type UserID = string
```
このように単純に組み込み型に別名をつけるだけではあまり意味はないが、次に述べるような色々な機能と組み合わせると効果を発揮する。

## 色々な型

### Structual Subtyping(構造的部分型)

```typescript
interface Flyable {
   fly(): void
}
class Bird {
   constructor(){}
   fly() { console.log("fly") }
}
class AirPlane {
   constructor(){}
   fly() { console.log("fly") }
}

function doFly(a: Flyable): void {
   a.fly()
}

// 継承関係がなくてもflyメソッドを持っていることがコンパイル時に分かればコンパイルが通る
doFly(new Bird())
doFly(new AirPlane())

interface Person {
   name: string
   age: number
}
const p: Person = { name: "masuda", age: 27 } //オブジェクトリテラルでも良い
```

### Never型
値が何もない型として`never`型が用意されている。
`void`型は「値が無いことを表す値」として`null`(と`undefined`)が含まれるが、`never`型には本当に何の値も属さないので、`never`型の変数にはどんな値も割り当てることができない。
```typescript
const a: never = 1 // どんな値を代入しようとしてもコンパイルエラーになる
```
一見すると使いみちが無い型のように見えるが、無限ループする・例外をスローするなどで本当に何も値を返さない関数の戻り値の型を表すことができる。
```typescript
function loop(): never {
   while(true) {
      console.log("loop!!!")
   }
}
function throwNull(): never {
   throw null
}
```
また、以下に述べるようにif文・switch文の条件の網羅性のチェックにも使うことができる。
never型はany型の逆で、任意の型の部分型であると考えられる
```typescript
function anySample<T>(t: T): void {
    const a: Any = t // どんな型の値もany型の変数に代入できる
    const b: T = a   // どんな型の変数もany型の値は代入できない…のが普通の部分的型付けなのだが、Typescriptの場合は代入できる。
                     // これはTypescriptのany型は部分的型付けのTopというよりもむしろコンパイラの型チェックをバイパスするための存在であるためである。
}

function neverSample<T>(t: T): void {
    const n: never = t // どんな型の値もnever型の変数には代入できない(コンパイラエラー)
    const t2: T = n    // どんな型の変数にもnever型の値を代入できる
}
```

### Intersection Type(交差型)
A型かつB型をあらわす型を簡単に表現できる。
```typescript
class Animal {
  // 何か実装
}
interface Flyable {
   fly(): void
}
interface Runnable {
   run(): void
}
interface TimeTravelable {
   timeTravel(): void
}

type Bird = Animal & Flyable
type DeLorean = Flyable & Runnable & TimeTravelable
```
他の言語のようにinterfaceの多重継承を使うのとほぼ同じ意味
```typescript
class Bird extends Animal implements Flyable {
   // ...
}

class DeLorean implements Flyable, Runnable, TimeTravelable {
   // ...
}
```

### Union Type(直和型)
A型またはB型をあらわす型を簡単に表現できる。
ML系言語やSwiftの直和型と違い、値構築子が無い。
この記法はCeylonという言語が元ネタらしい。
```typescript
let s: string | number = 1 // string型またはnumber型の値が代入できる
s = "aaa"

type optional<T> = T | null
let t: optional<string> = null
```
cf) F#とSwiftの直和型
```fsharp
type Option<'a> =
    | Some of 'a
    | None
```
```swift
enum Optional<T> {
   case Some(T)
   case None
}
```
値構築子が無いのでパターンマッチで値を取り出すということが出来ない(そもそもJSにパターンマッチは無いが)。
値を取り出すときには`typeof`演算子で型チェックする。
```typescript
function someFunc(x: number | string): void {
   if (typeof x === "number") {
      // なにか処理(このスコープではxがnumber型であることがコンパイラにより保証される)
   }
   else if (typeof x === "string") {
      // なにか処理(このスコープではxがstring型であることがコンパイラにより保証される)
   }
}
```
せっかくの静的型付けなのに文字列で型チェックするのか…（困惑）となりそうなことろだが、後述するString Literal Typeという機能のおかげで`typeof`演算子はオペランドとしてとりうる文字列が決まっており、スペルミスはコンパイル時にチェックできる。never型を使うと網羅性のチェックもできる。これは、任意の型はnever型との直和型であると考えられるからである。
```typescript
function someFunc(x: number | string): void {
   if (typeof x === "number") {
      // なにか処理
   }
   else if (typeof x === "stling") // タイプミスするとここで怒られる
      // なにか処理    
   }
   else if (typeof x === "boolean") { // 余計な型チェックをする分には怒られない
      // なにか処理(無駄)
   }
   else {
      const y: never = x // 条件を網羅していないとここで怒られる
   }
}
```
組み込み型ではなくクラス等のユーザー定義型で型チェックしたい場合は次のように`type predicate`を返す関数を自分で定義する。

```typescript
class Fish {
   constructor(){}
   swim(): void
}
class Bird {
   constructor(){}
   fly(): void
}
function isFish(animal: Fish | Bird): animal is Fish {
   return (animal as Fish).swim !== undefined
}
function isBird(animal: Fish | Bird): animal is Bird {
   return (animal as Bird).fly !== undefined
}

let animal: Fish | Bird = new Bird()
if (isFish(animal)) {
    animal.swim() // このスコープではanimalがFish型であることがコンパイラによって保証される
} else {
    animal.fly()  // このスコープではanimalがBird型であることがコンパイラによって保証される
}
```

### String or Number Literal Type
文字列や数字のリテラルを列挙型のように使える。

```typescript
type StarCount = 0 | 1 | 2 | 3 | 4 | 5

let count: StarCount = 1
count = 4
count = 6 // コンパイルエラー

// 実態はnumberなので普通に計算できる
function starAverage(starCounts: StarCount[]): number {
    let sum = 0
    for(const elem of starCounts) {
        sum += elem
    }
    return sum / starCounts.length
}

// 網羅性もチェックできる
function scToString(sc: StarCount): string {
    switch(sc) {
       case 0: return "ZERO"
       case 1: return "ONE"
       case 2: return "TWO"
       case 3: return "THREE"
       case 4: return "FOUR"
       case 5: return "FIVE"
       // case 6: return "SIX" // 余計な条件があるとここでコンパイルエラー 
       default:
          const a: never = sc  // 足りない条件があるとここでコンパイルエラー
          return a
    }
}
```

stringやnumberだけでなくオブジェクトリテラルも使えるようだが、これは使わない方がよいだろう・・・
```typescript
type Hoge = {a: 1} | {b: 2}
let h: Hoge = {a: 1}
h = {a: 2} // コンパイルエラー
```

### keyof
`keyof T`で「Tクラス(インターフェース)のプロパティ名の直和型」を表せる。
また、`T[key]` で「keyでアクセスできるTクラス(インターフェース)のプロパティの型」を表せる。

```typescript
interface Person {
   name: string
   age: number
}
type PersonKey = keyof Person // "name" | "age" になる
type PersonNameType = Person["name"] // string になる
```

### Mapped types
他の型から半自動的に新しい型を定義できる機能。

```typescript
type Person = { [P in "name"]: string, [P in "age"]: number }
type DetailedPerson = { name: string, [P in "age" | "height" | "weight"]: number }
type AnotherPerson = { [P in keyof Person]: Person[P] } // Personと同じ定義

type ReadOnly<T> = {
   readonly [P in keyof T]: T[P]
} 
```

### Conditional Type
型レベル三項演算子
```typescript
type MyCondition<T, U, X, Y> = T extends U ? X : Y;
```
TがUに代入可能であればX、そうでなければY

### 実用例(Result型)
```typescript
interface Success<T> {
   kind: "Success"
   value: T
}
interface Failure {
   kind: "Failure"
   description: string
}
type Result<T> = Success<T> | Failure

function safeDiv(a: number, b: number): Result<number> {
   if (b == 0) return { kind: "Failure", description: "zero division error" }
   else return { kind: "Success", value: a / b }
}

const result = safeDiv(3, 0)

switch(result.kind) {
   case "Success":
      console.log(result.value)  // このスコープではSuccess型になっている
      break
   case "Failure":
      console.log(result.description)  // このスコープではFailure型になっている
      break
   case "Unknown": // result.kindは "Success" | "Failure" 型なのでコンパイルエラー
      break
   default:
      const b: never = result
}
```

## 感想
- オブジェクトリテラルによるオブジェクト生成を多用するJavascriptと構造的部分型は相性が良い
- Union Typeの仕組みは面白い
- ラムダ式の型宣言に引数名を書く必要があるのはなぜ・・・？
- 関数の戻り値を型推論するのはやりすぎでは…？(戻り値の型を省略したらvoid型になって欲しい)
- node.jsの作者がdenoというtypescriptの実行環境を作ってるらしいので期待

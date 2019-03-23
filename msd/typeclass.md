# 型クラスについて

## 型クラスとは?

> In computer science, a type class is a type system construct that supports ad hoc polymorphism.  
This is achieved by adding constraints to type variables in parametrically polymorphic types.  
Such a constraint typically involves a type class T and a type variable a, and means that a can  
only be instantiated to a type whose members support the overloaded operations associated with T.   

(wikipedia より引用)  

コンピュータ・サイエンスにおいて、型クラスとはアドホック多相をサポートする型システムの構成要素である。
これはパラメトリック多相型の型変数に制約を加えることで実現される。
このような制約は典型的には型クラスTと型変数aを伴い、a が T に関連したオーバーロードされた操作をサポートするメンバを持つ型としてのみ実体化できるということを意味する。

要するに、ある性質を満たすような型の集合を表す方法であり、「型の型」である。

```haskell
class Show a where
   show:: a -> String

class Eq a where
   (==), (/=) :: a -> a -> Bool
```

## 多相性
型クラスについて説明する前に、多相性(多態性)について説明する。

> In programming languages and type theory, polymorphism is the provision of a single interface to  
entities of different types or the use of a single symbol to represent multiple different types.

(wikipedia より引用)

多相性とは、1つのインターフェースを異なる型の複数の実体に提供すること、又は1つのシンボルを複数の異なる型として表す使用法である。

要するに、「同じ(ように見える)関数や演算子に、異なる型の値を適用すること。又は、そのようなことができるようにする方法」ということ?
多相性には大まかに分けて次の3つの分類がある。
- サブタイピング多相
- アドホック多相
- パラメトリック多相

### アドホック多相
関数(や演算子)のオーバーロード。

```swift
func add(_ x: Int, _ y: Int) -> Int {
   return x + y
}

func add(_ x: Float, _ y: Float) -> Float {
   return x + y
}

add(1, 1)
add(1.5, 1.5)
```
これは、見かけ上同じ関数を呼び出しているだけで、実体としてはコンパイル時に型を見て異なる関数を呼び出している。

### サブタイピング多相
部分型による多相。
オブジェクト指向言語では多相性といえばだいたいこれ。
要するに動物クラスを継承した犬クラスと猫クラスがあって、犬はワンワン鳴いて猫はニャーニャー鳴くというあれである。

```typescript
interface Animal {
   cry(): void
}

class Dog implements Animal {
   constructor() {}
   cry(): void {
      console.log("Bow")
   }
}

class Cat implements Animal {
   constructor() {}
   cry(): void {
      console.log("Mew")
   }
}

let animal: Animal
if (Math.random() > 0.5) {
   animal = new Dog()
} else {
   animal = new Cat()
}
animal.cry()
```
これはアドホック多相の場合と違い、コンパイル時ではなく実行時に`animal`の実際の型に応じた関数が呼び出される。

### パラメトリック多相
ジェネリクス。
例えば、受け取った引数をそのまま返す関数を考えると、この関数はどのような型に対しても同じ実装を与えることができる。

```swift
func id<T>(_ x: T) -> T {
   return x
}
```

```typescript
const id = <T>(x: T): T => x
```

## パラメトリック多相の問題
例えば、2つの数を引数にとって大きい数を返す関数を作ることを考える。
オーバーロードで素朴に実装すると次のようになる

```swift
func max(_ a: Int, _ b: Int) -> Int {
   return a > b ? a : b
}

func max(_ a: Float, _ b: Float) -> Float {
   return a > b ? a : b
}
```

これでは同じ実装を繰り返し書いていて無駄である。
そこで次のようにジェネリックな関数を書いてみる。

```swift
func max<T>(_ a: T, _ b: T) -> T {
   return a > b ? a : b
}
```

しかし、これではコンパイルが通らない。
なぜなら`max`はジェネリックな関数になったので、このままではどんな型でも引数にとることができてしまうが、
関数の本体で比較演算子を使っているので、比較演算子を適用できる型でしか正しく動作しない。

ここで、ジェネリックな関数の型引数に対して、「どんな型でもいいわけでは無いが、比較演算子が使える型なら何でもOK」
という制約を付け加えることができればよい。
このように、「ある性質を満たすような型の集合」を表すのに型クラスが用いられる。
swiftではまさにそういう型を表す`protocol`として`Comparable`が用意されているので、次のように書ける。
(swiftの`protocol`は実質的にはほとんど型クラスと同じである(が、ちょっとだけ違うところもある))

```swift
func max<T: Comparable>(_ a: T, _ b: T) -> T {
   return a > b ? a : b
}
```

## インターフェースとの違い
「型の型」という説明を聞くと、オブジェクト指向言語におけるインターフェースのようなものでは?と思うかもしれない。
その考えはだいたい合っているといえば合っているのだが、型クラスとインターフェースには次のような違いがある。

1. 既存の型に後付できる
1. 型クラスの方が表現力が強い(型に対して複雑な制約を付けることができる)
1. 型になれない

### 既存の型に後付できる
インターフェースの場合、ある型があるインターフェースを実装するには、その型の宣言時にそのインターフェースを実装することを宣言しなくてはならない。

```csharp
interface Animal {
   void cry();
}

class Dog {
   public void cry() {
      Sytem.out.print("Baw");
   }
}

(new Dog()).cry()

class Dog2 extends Dog implements Animal {

}

interface IEquatable {
   bool equal(IEquatable eq)
}

class Complex: IEquatable {
   int re;
   int im;
   Complex(int re, int re) {
      this.re = re
      this.im = im
   }

   public bool equal(IEquatable eq) {
      return this.re == this.re &&
   }
}
```


### 型クラスの方が表現力が強い
インターフェースが表現できる型の制約は、その型がどのようなメソッド(とプロパティ)を持っているかということだけである。
型クラスの場合、どのような関数の引数になれるかという制約を表すことができる。
また、型クラスの場合は、型クラスに適合する型自身を制約の中で使うことができる。

```haskell
class Equatable a where
   equal:: a -> a -> Bool

instance Equatable Int where
   equal x y = x == y

data Complex = Complex { re :: Int, im :: Int } deriving Show

instance Equatable Complex where
   equal cx cy = (re cx) == (re cy) && (im cx) == (im cy)

main = do
   print ( equal Complex { re = 1, im = 1 } Complex { re = 1, im = 1 } )
   print ( equal (1::Int) (1::Int) )
```

```swift
protocol Eq {
   static func equal(lhs: Self, rhs: Self) -> Bool
}

extension Int {
   static func equal(lhs: Int, rhs: Int) -> Bool {
      return lhs == rhs
   }
}

struct Complex {
   var re: Int
   var im: Int
   init(re: Int, im: Int) {
      self.re = re
      self.im = im
   }
}

extension Complex: Eq {
   static func equal(lhs: Complex, rhs: Complex) -> Bool {
      return lhs.re == rhs.re && lhs.im == rhs.im
   }
}
```

### 型になれない
インターフェースは型の型であると同時に、型になることができる。

Java
```java
IComperable a = 1;
```

Haskell
```haskell
a :: Equatable = 1 -- こういうことはできない
```

swiftのprotocolは、型クラス相当の機能を持ちながら、型のように使うこともできる。
```swift
protocol Flyable {
   func fly() 
}

class Bird: Flyable {
   func fly() {
      print("Fly")
   }
}

var a: Flyable = Bird()
```

ただし、型のように使えないprotocolもある。このことについては後述する。
```swift
var a: Equatable = 1 // こういうことはできない
```

## 型クラスの無い言語で型クラス
TypeScriptには言語機能としての機能は無いが、型クラス相当の機能を実現することはできる(他の言語でもほぼ同じ方法でできる)。
基本的な方法として、ジェネリックな関数を使うときに関数の実装を引数として受け取る(依存性の注入)ようにすればよい。

```typescript
class Point2D {
   constructor(public x: number, public y: number) {}
}
class Point3D {
   constructor(public x: number, public y: number, public z: number) {}
}

// 等値性を判定するジェネリックな関数。実装は持たない。
const equal = <T>(lhs: T, rhs: T, equalImpl: (a: T, b: T) => Bool): Bool => equalImpl(lhs, rhs);

// equalの実装
const Point2DEqualImpl = (a: Point2D, b: Point2D): boolean => a.x == b.x && a.y == b.y
const Point3DEqualImpl = (a: Point3D, b: Point3D): boolean => a.x == b.x && a.y == b.y && a.z == b.z

const p1 = new Point2D(1, 1)
const p2 = new Point2D(1, 1)

console.log(equal(p1, p2, Point2DEqualImpl))

const p3 = new Point3D(1, 1, 1)
const p4 = new Point3D(1, 1, 2)

console.log(equal(p3, p4, Point3DEqualImpl))
```

このようにすれば、`equal`の実装(`equalImpl`)を持たない型の変数を引数に渡すことはできないので、
「等値性が判定できる(`equalImpl`が実装されている)型のみを`equal`の引数の型にしたい」という目的が達成できる。
また、インターフェイスと違い単に関数を実装するだけなので型を定義したあとに好きなように後付することもできる。

明示的に型クラスに名前をつけたい場合、次のように書けばよい。

```typescript
class Point2D {
   constructor(public x: number, public y: number) {}
}

class Point3D {
   constructor(public x: number, public y: number, public z: number) {}
}

// 明示的な型クラス
type Eq<T> = (lhs: T, rhs: T) => boolean

const Point2DEq: Eq<Point2D> = (lhs: Point2D, rhs: Point2D) => lhs.x === rhs.x && lhs.y == rhs.y
const Point3DEq: Eq<Point3D> = (lhs: Point3D, rhs: Point3D) => lhs.x === rhs.x && lhs.y == rhs.y && lhs.z == rhs.z

const equal = <T>(eq: Eq<T>) => (lhs: T, rhs: T) => eq(lhs, rhs)

const p1 = new Point2D(1, 1)
const p2 = new Point2D(1, 1)

console.log(equal(Point2DEq)(p1, p2))

const p3 = new Point3D(1, 1, 1)
const p4 = new Point3D(1, 1, 2)

console.log(equal(Point3DEq)(p3, p4))
```

この方法の欠点として、引数として明示的に型ごとに違う関数の実装を渡さなくてはならないのでポリモーフィックではないという点がある。  

## Scalaで型クラス
scalaにはimplicit parameter(暗黙の引数)という機能がある。  
これは、関数呼び出しの際にimplicitが指定された引数があり、スコープ内にimplicit指定された変数・オブジェクトがあり両者の型が一致する場合に  
その変数・オブジェクトが暗黙的に関数の引数として渡される、というものである。
見るからにヤバそうな機能であるが、これを使うとHaskellと同等の型クラスの機能を実現することができる。

```scala
trait Eq [T] {
   def equal(lhs: T, rhs: T): Boolean
}

case class Point2D(x: Int, y: Int)

case class Point3D(x: Int, y: Int, z: Int)

object traitest {
   implicit object Point2DEq extends Eq[Point2D] {
      def equal(lhs: Point2D, rhs: Point2D): Boolean = {
         lhs.x == rhs.x && lhs.y == rhs.y
      }
   }

   implicit object Point3DEq extends Eq[Point3D] {
      def equal(lhs: Point3D, rhs: Point3D): Boolean = {
         lhs.x == rhs.x && lhs.y == rhs.y && rhs.z == lhs.z
      }
   }

   def equal[T](lhs: T, rhs: T)(implicit eq: Eq[T]): Boolean = {
      eq.equal(lhs, rhs)
   }

   def main(args: Array[String]): Unit = {
      val p1 = Point2D(1, 1)
      val p2 = Point2D(1, 1)

      if (equal(p1, p2)) {
         println("Equal")
      } else {
         println("Not Equal")
      }

      val p3 = Point3D(1, 1, 1)
      val p4 = Point3D(1, 1, 2)

      if (equal(p3, p4)) {
         println("Equal")
      } else {
         println("Not Equal")
      }
   }
}
```

## Haskell流の型クラスとTypeScript流の型クラスの違い
(便宜的にTypeScriptで例示した型クラスの実装方法をTypeScript流の型クラスと呼ぶ)  
Haskell流の型クラスの欠点として、一つの型に対して一つの関数の組み合わせしか型クラスになれないということが挙げられる。  
  
例えば、モノイドを表す型クラスを作ったとする。

```haskell
class Monoid a where
   mempty :: a
   mappend:: a -> a -> a
```

次に、Intをモノイドにしようと考える。  
Intは足し算と掛け算についてモノイドであるが、このままではその両方をモノイドにすることができない。

```haskell
-- こういうことはできない
instance Monoid Int where
   mempty = 0
   mappend x y = x + y

instance Monoid Int where
   mempty = 1
   mappend x y = x * y
```

これはHaskellの型クラスがオーバーロード解決の仕組みを併せ持っているからである。  

一方、TypeScript流の型クラスでは、関数呼び出しがポリモーフィックでない代わりに、1つの型に対して複数の関数の組み合わせを同じ型クラスにすることができる。

```typescript
type Monoid<T> = {
   mempty: T
   mappend: (a: T, b: T) => T
}

// 一つの型に対して、複数の演算をモノイドにできる
// (number, +) のモノイド
const NumAddMonoid: Monoid<number> = {
   mempty: 0,
   mappend: (a: number, b: number): number => a + b 
}

// (number, *) のモノイド
const NumMultMonoid: Monoid<number> = {
   mempty: 0,
   mappend: (a: number, b: number): number => a * b 
}

const mappend = <T>(m: Monoid<T>) => (a: T, b: T) => m.mappend(a, b)
```

scalaの場合は、基本的にはデフォルトの実装を使いながら、必要に応じて個々の実装を使うということができる。

```scala
trait Monoid [T] {
   def mempty(): T
   def mappend(lhs: T, rhs: T): T
}

object traitest {
   implicit object IntAddMonoid extends Monoid[Int] {
      def mempty(): Int = 0
      def mappend(lhs: Int, rhs: Int): Int = lhs + rhs
   }

   object IntMultMonoid extends Monoid[Int] {
      def mempty(): Int = 1
      def mappend(lhs: Int, rhs: Int): Int = lhs * rhs
   }

   def mappend[T](lhs: T, rhs: T)(implicit monoid: Monoid[T]): T = {
      monoid.mappend(lhs, rhs)
   }

   def main(args: Array[String]): Unit = {
      println(mappend(1, 2))
      println(mappend(1, 2)(IntMultMonoid))
   }
}
```

## Haskell流の型クラスとTypeScript流の型クラスの違い
(便宜的にTypeScriptで例示した型クラスの実装方法をTypeScript流の型クラスと呼ぶ)  
Haskell流の型クラスの欠点として、一つの型に対して一つの関数の組み合わしか型クラスになれないということが挙げられる。  
  
例えば、モノイドを表す型クラスを作ったとする。

```haskell
class Monoid a where
   mempty :: a
   mappend:: a -> a -> a
```

次に、Intをモノイドにしようと考える。  
Intは足し算と掛け算についてモノイドであるが、このままではその両方をモノイドにすることができない。

```haskell
-- こういうことはできない
instance Monoid Int where
   mempty = 0
   mappend x y = x + y

instance Monoid Int where
   mempty = 1
   mappend x y = x * y
```

これはHaskellの型クラスがオーバーロード解決の仕組みを併せ持っているからである。  

一方、TypeScript流の型クラスでは、関数呼び出しがポリモーフィックでない代わりに、1つの型に対して複数の関数の組み合わせを同じ型クラスにすることができる。

```typescript
type Monoid<T> = {
   mempty: T
   mappend: (a: T, b: T) => T
}

// 一つの型に対して、複数の演算をモノイドにできる
// (number, +) のモノイド
const NumAddMonoid: Monoid<number> = {
   mempty: 0,
   mappend: (a: number, b: number): number => a + b 
}

// (number, *) のモノイド
const NumMultMonoid: Monoid<number> = {
   mempty: 1,
   mappend: (a: number, b: number): number => a * b 
}

const mappend = <T>(m: Monoid<T>) => (a: T, b: T) => m.mappend(a, b)
```

## Selfを含むprotocolの落とし穴
swiftではメソッドの引数・戻り値の型に`Self`を使っているprotocolは型として使うことができない(もう1つ、関連型を使っているprotocolも型となれない)。
端的にいうと、interfaceと同等の機能しか使っていないprotocolは型として使えるが、そうでないprotocolは型として使えないと考えてよい。

次のようなprotocolと、protocolに適合した型があったとする。
```swift
protocol Eq {
   func isEqual(_ another: Self) -> Bool
}

class Point2D: Eq {
   var x: Int
   var y: Int
   init(x: Int, y: Int) {
      self.x = x
      self.y = y
   }

   func isEqual(_ another: Point2D) -> Bool {
      return self.x == another.x && self.y == another.y
   }
}

class Point3D: Eq {
   var x: Int
   var y: Int
   var z: Int
   init(x: Int, y: Int) {
      self.x = x
      self.y = y
   }

   func isEqual(_ another: Point3D) -> Bool {
      return self.x == another.x && self.y == another.y && self.z == another.z
   }
}
```

ここでもし`Eq`が型として使えたとすると、次のようなコードが書けることになる。

```swift
var p1: Eq = Point2D(1, 1)
var p2: Eq = Point3D(1, 1, 1)
p1.isEqual(p2)
```

結局のところ、interfaceとはクラス継承によるサブタイピングの特殊なケースであって、
「あるinterfaceを実装した全てクラスに対して、同じ形のメソッド呼び出しが可能である」ことを保証するものである。
(`Self`を含む)protocolのように、個々のクラスの実装によってメソッドの引数や戻り値の型を変えるのは
interfaceによる多相性の仕組みとは真っ向から対立するものである。

同様の理由で、`Self`を含むprotocolに適合したクラスは継承に制限がかかる。
`Eq`プロトコルに適合した`Point2D`クラスと`Point2D`を継承した`ColoredPoint2D`クラスがあるとする。

```swift
protocol Eq {
    func isEqual(_ another: Self) -> Bool
}

class Point2D {
    var x: Int
    var y: Int
    init (x: Int, y: Int) {
        self.x = x
        self.y = y
    }
}

extension Point2D: Eq {
    func isEqual(_ another: Point2D) -> Bool {
        return self.x == another.x && self.y == another.y
    }
}

class ColoredPoint2D: Point2D {
    var color: Int
    init (x: Int, y: Int, color: Int) {
        self.color = color
        super.init(x: x, y: y)
    }
}
```

`ColoredPoint2D`も`Eq`に適合させようとして、次のようなコードを書くと、
`Redundant conformance of 'ColoredPoint2D' to protocol Eq` というエラーメッセージが表示される。
```swift
extension ColoredPoint2D: Eq {
    func isEqual(_ another: ColoredPoint2D) -> Bool {
        return super.isEqual(another) && self.color == another.color
    }
}
```

要するに`ColoredPoint2D`は`Eq`に適合した`Point2D`を継承しているので、既に`Eq`に適合しているのである。
しかし、ここで`ColoredPoint2D`の等値性判定のために`Point2D`の`isEqual`メソッドを使うことは妥当だろうか?
`Point2D`の`isEqual`メソッドは座標での等値性判定しか行っていないので、`color`が違う`ColoredPoint2D`のインスタンスも同じものとみなされてしまう。

では`ColoredPoint2D`の等値性判定のために`isEqual`をオーバーライドすればよいのでは?と思うかもしれない。
```swift
class ColoredPoint2D: Point2D {
    var color: Int
    init (x: Int, y: Int, color: Int) {
        self.color = color
        super.init(x: x, y: y)
    }

    override func isEqual(_ another: ColoredPoint2D) -> Bool {
        return super.isEqual(another) && self.color == another.color
    }
}
```
しかし、これでは今度は`Method does not override any method from its superclass`というエラーメッセージが表示される。
`func isEqual(_ another: ColoredPoint2D) -> Bool`と`func isEqual(_ another: Point2D) -> Bool` は
メソッドの引数の型が違う(共変になっている)ので、メソッドをオーバーライドしたものとみなされていないのである。

一般に親クラスのメソッドを子クラスでオーバーロードする場合には、引数の型は反変、戻り値の型は共変になっている必要がある
(関数の型の部分型関係のときと同じ考え)。
子クラスは親クラスの部分型になっていなければならない(リスコフの置換原則)、つまりプログラム中で親クラスのインスタンスが
入っている箇所は子クラスのインスタンスを入れても正しく動作する必要がある。
しかし、メソッドのオーバーロード時に上記した以外の型の変性を認めると、実行時に型エラーを起こすコードがコンパイルに通ってしまう。

```swift
// もしもswiftでメソッドの引数の共変性が認められていたら…
class Point2D {
   // 省略
   func isEqual(_ another: Point2D) -> Bool {
        return self.x == another.x && self.y == another.y
    }
}

class ColoredPoint2D: Point2D {
   // 省略
   override func isEqual(_ another: ColoredPoint2D) -> Bool {
        return super.isEqual(another) && self.color == another.color
   }
}

var p1: Point2D = Point2D(1, 1) 
var p2: Point2D = ColoredPoint2D(1, 1, 1)

print(p2.isEqual(p1)) // Point2Dにcolorというプロパティは無いので実行時に型エラーが起きる
```

実際の言語で継承時のメソッドにどのような型の変性が認められるからはまちまちである
(Java, Swiftでは上記の変性が認められている。C#ではメソッドの型は不変である。Eiffelでは引数の共変性が認められており型安全では無くなっている)。
メソッドの型指定に`Self`を含むprotocolに適合したクラスは、クラスを継承した際にこのような型の変性を満たすことができなくなるので
継承との相性が悪いのである。

このような問題は動的型付け言語でも顕在化し、あまり考えずに次のようなpythonのコードを書くと実行時型エラーが発生する
(まあ動的型付け言語は問題ばかりなのでこれくらは大した問題ではないかもしれない)

```python
class Point2D:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def equals(self, another):
        return self.x == another.x and
               self.y == another.y

class ColoredPoint2D(Point2D):
    def __init__(self, x, y, c):
        self.x = x
        self.y = y
        self.c = c

    def equals(self, another):
        return self.x == another.x and
               self.y == another.y and
               self.c == another.c

p1 = Point2D(1, 1)
p2 = ColoredPoint2D(1, 1, "RED")
print(p1.equals(p2)) # => true
print(p2.equals(p1)) # 実行時エラー
```

## 参考資料
https://qiita.com/koher/items/ee31222b7f9b0ead3de7
https://qiita.com/omochimetaru/items/621f1ef62b9798ee5ff5
https://dwango.github.io/scala_text/implicit.html
http://lampwww.epfl.ch/%7Eodersky/talks/wg2.8-boston06.pdf
https://uid0130.blogspot.com/2015/02/is-aoop-inheritance-is-not-subtyping.html

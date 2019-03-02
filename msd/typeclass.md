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
const equalPoint2D = (a: Point2D, b: Point2D): boolean => a.x == b.x && a.y == b.y
const equalPoint3D = (a: Point3D, b: Point3D): boolean => a.x == b.x && a.y == b.y && a.z == b.z

console.log(equal(new Point2D(1, 1), new Point2D(1, 1), equalPoint2D));
console.log(equal(new Point3D(1, 1, 1), new Point3D(1, 1, 2), equalPoint3D));
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

if (equal(Point2DEq)(p1, p2)) console.log("Equal")

const p3 = new Point3D(1, 1, 1)
const p4 = new Point3D(1, 1, 2)

if (equal(Point3DEq)(p3, p4)) console.log("Equal")
```

この方法の欠点として、引数として明示的に型ごとに違う関数の実装を渡さなくてはならないのでポリモーフィックではないという点がある。  

## Scalaで型クラス
scalaにはimplicit parameter(暗黙の引数)という機能がある。  
これは、関数呼び出しの際にimplicitが指定された引数があり、スコープ内にimplicit指定された変数・オブジェクトがある場合に  
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

   object Point2DEq2 extends Eq[Point2D] {
      def equal(lhs: Point2D, rhs: Point2D): Boolean = {
         lhs.x == rhs.x
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
   mempty: 0,
   mappend: (a: number, b: number): number => a * b 
}

const mappend = <T>(m: Monoid<T>) => (a: T, b: T) => m.mappend(a, b)
```


## Selfを含むprotocolの落とし穴

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
```

```swift
class ColoredPoint2D: Point2D {
    var color: Int
    init (x: Int, y: Int, color: Int) {
        self.color = color
        super.init(x: x, y: y)
    }
}
```

```swift
extension ColoredPoint2D: Eq {
    func isEqual(_ another: ColoredPoint2D) -> Bool {
        return super.isEqual(another) && self.color == another.color
    }
}
```

## 参考資料
https://qiita.com/koher/items/ee31222b7f9b0ead3de7
https://qiita.com/omochimetaru/items/621f1ef62b9798ee5ff5
https://dwango.github.io/scala_text/implicit.html
http://lampwww.epfl.ch/%7Eodersky/talks/wg2.8-boston06.pdf
https://uid0130.blogspot.com/2015/02/is-aoop-inheritance-is-not-subtyping.html

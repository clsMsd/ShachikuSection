# ジェネリクスと型の共変・反変について

## 部分型とは?

> In programming language theory, subtyping (also subtype polymorphism or inclusion polymorphism) is a form of type polymorphism in which a subtype is a datatype that is related to another datatype (the supertype) by some notion of substitutability, meaning that program elements, typically subroutines or functions, written to operate on elements of the supertype can also operate on elements of the subtype.
(wikipedia より引用)

ある型Tの値を別の型Sの値に置き換えても全く問題無いような場合、SはTの部分型であるといい、S <: T と書く。
例えば Animalクラスとそれを継承した Dogクラスがあった場合、DogクラスのインスタンスはAnimalクラスのインスタンスを置き換えることができる。

```typescript
class Animal { eat() {} }
class Dog extends Animal { bark() {} }
class Cat extends Animal { meow() {} }

function doEat(animal: Animal) {
    animal.eat();
}

doEat(new Animal())
doEat(new Dog())    // Dog <: Animal なので、Animal型をDog型に置き換えても安全
```

## 不変、共変、反変、双変

Animal型とその部分型であるDog型と、型引数を受ける取るあるジェネリッククラス Container<T> があるとする。
この場合、Container<Animal>型とContainer<Dog>型の間の関係は次のようなものが考えられる。

1. 不変: Container<Animal> と Container<Dog>の間には特になんの関係もないとする
1. 共変: Container<Animal> :> Container<Dog> とする。型引数の関係とジェネリック型の関係が同じなので共変という。
1. 反変: Container<Animal> <: Container<Dog> とする。型引数の関係とジェネリック型の関係が逆転するので反変という。
1. 双変: Container<Animal> :> Container<Dog> かつ Container<Animal> <: Container<Dog> とする。

不変の場合は型安全であり特に何も考えることはなくシンプルであるが、List<Animal> と List<Dog> を変換したりできないので不便である。
双変の場合も考え方はシンプルであるが、型安全性がなくなってしまう。
ここで共変と反変の関係について考えてみる。

## 関数の型の共変と反変

T型の引数を受け取ってU型の戻り値を返す関数の型を、ジェネリック型に見立てて`Func<T, U>`と書くことにする。
まず、引数の共変・反変関係について考える。
`Func<Animal, Void>`と`Func<Dog, Void>`の型付けの関係はどうなるだろうか？
ここで、あるプログラムに含まれる`Func<Dog, Void>`型の関数を、`Func<Animal, Void>`型の関数に置き換えることを想定してみる。
`Func<Dog, Void>`型の関数呼び出しがあったところは、必ず引数としてDog型が来るはずなので、`Func<Animal, Void>`型の関数に置き換えても問題無いはずである。
一方、`Func<Animal, Void>`型の関数を`Func<Dog, Void>`型の関数に置き換えた場合、`Func<Animal, Void>`型の関数呼び出しがあったところは
引数としてCat型などのDog型以外の型が来る可能性があるので安全ではない。
つまり、`Func<Dog, Void>`を、`Func<Animal, Void>`に置き換えることができるので、Func<Animal, Void> <: Func<Dog, Void> となる。

```typescript
type Func<T, U> = (a: T) => U

const AFunc: Func<Animal, Void> = animal => { animal.eat(); }
const DFunc: Func<Dog, Void> = dog => { dog.bark(); }

AFunc(new Animal());
DFunc(new Dog());

// 上の関数を入れ替える
AFunc(new Dog());      // Dog <: Animal なので問題なし
DFunc(new Animal());   // Animal型はbarkを持っているとは限らないのでエラー
```

次に、戻り値の共変・反変関係について考える。
`Func<Void, Animal>`と`Func<Void, Dog>`の型付けの関係はどうなるだろうか？
あるプログラムに含まれる`Func<Void, Animal>`型の関数を、`Func<Void, Dog>`型の関数に置き換えることを想定してみる。
`Func<Void, Animal>`型の関数呼び出しがあったところの式はAnimal型のはずなので、`Func<Void, Dog>`型の関数に置き換えても問題ないはずである。
一方、`Func<Void, Dog>`型の関数を`Func<Void, Animal>`型の関数に置き換えた場合、`Func<Void, Animal>`型の関数呼び出しがあったところの式はDog型とは限らないので安全でない。
つまり、`Func<Void, Animal>`を、`Func<Void, Dog>`に置き換えることができるので、Func<Void, Dog> <: Func<Void, Animal> となる。

```typescript
const AFunc: Func<Void, Animal> = () => new Animal()
const DFunc: Func<Void, Dog> = () => new Dog()

const animal: Animal = AFunc()
const dog: Dog = DFunc()

// 上の関数を入れ替える
const animal: Animal = DFunc() // Dog <: Animal なので問題なし
const dog: Dog = AFunc()       // エラー
```

まとめると、関数の型を引数と戻り値の型を指定するジェネリック型であると考えると、
関数の型は引数に対して反変、戻り値に対して共変な関係にしておけば問題ない

## クラスの型の共変と反変

ジェネリックなクラスに対しても、基本的には関数の型と同じ考えが適用できる。
型引数を受ける取るジェネリッククラス Container<T> について、Containerクラスが`Func<T, 何か>`型のメソッド又は`setter`のみを持つT型のプロパティしか持っていないならばContainerクラスは型引数に対して反変、
逆に`Func<何か, T>`型のメソッド又は`getter`のみを持つT型のプロパティしか持っていないならば型引数に対して共変にすれば安全であるといえる。

言語によってはジェネリッククラスの型引数について、共変・反変を指定することができるものもある(C#, Scala, Kotlin など)。

共変・反変を指定しない場合
```csharp
// このようなコードはコンパイルできない
class Animal {}
class Dog: Animal {}

class Container<T> {
    public T value;
    public Container(T value) {
        SetValue(value);
    }

    public void SetValue(T value) {
        this.value = value;
    }

    public T GetValue() {
        return this.value;
    }
}

class Program {
    static void Main(string[] args) {
        Container<Animal> ac = new Container<Dog>(new Dog()); // コンパイルエラー
        Container<Dog> dc = new Container<Animal>(new Dog()); // コンパイルエラー
    }
}
```

型引数に対して共変と指定した場合
```csharp
// 型引数の前にoutを付けると、型引数をメソッドの引数に使えない代わりに型引数に対して共変になる
interface IContainer<out T> {
    // void SetValue(T value); // 
    T GetValue();
}

class Container<T>: IContainer<T> {
    private T value;
    public Container(T value) {
        SetValue(value);
    }

    public T GetValue() {
        return this.value;
    }
}

class Program {
    static void Main(string[] args) {
        IContainer<Animal> ac = new Container<Dog>(new Dog()); // 型引数に対して共変なのでここは問題なし
        IContainer<Dog> dc = new Container<Animal>(new Dog()); // こっちはコンパイルエラー
    }
}
```

型引数に対して反変と指定した場合
```csharp
// 型引数の前にinを付けると、型引数をメソッドの戻り値に使えない代わりに型引数に対して反変になる
interface IContainer<in T> {
    void SetValue(T value);
    // T GetValue(); // 型引数を戻り値に使うメソッドは持てない(コンパイルエラー)
}

class Container<T>: IContainer<T> {
    private T value;
    public Container(T value) {
        SetValue(value);
    }

    public void SetValue(T value) {
        this.value = value;
    }
}

class Program {
    static void Main(string[] args) {
        IContainer<Animal> ac = new Container<Dog>(new Dog()); // こっちはコンパイルエラー
        IContainer<Dog> dc = new Container<Animal>(new Dog()); // 型引数に対して反変なのでこれは問題なし
    }
}
```

また、JavaやC#では配列に関してはデフォルトで共変になっている。
これは一種の言語自体のバグのようなもので、実行時に型エラーを起こすコードのコンパイルを通すことができてしまい危険である。

コンパイルは通るが実行時でクラッシュする危険なコード

```csharp
object[] oarr = new string[] { "aaa" };
oarr[0] = 1; 
```

ちなみにSwiftの配列もデフォルトで共変だが、Swiftの場合は配列が値型なので安全になっている。
```swift
var darr: [Dog] = [Dog()]
var aarr: [Animal] = darr

aarr[0] = Cat() // 実態がAnimal型の配列なのでCat型を突っ込んでも安全
```

## inheritance

class Animal {
    getPartner(a: Animal): Animal {}
}

class Dog extends Animal {
    getPartner(a: Animal): Animal {}
}

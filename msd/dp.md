# 動的計画法

(この記事のほぼすべては https://qiita.com/drken/items/dc53c683d6de8aeacf5a の丸パクリです)

## A - Frog 1

> N 個の足場があります。 足場には 1,2,…,N と番号が振られています。 各 i (1≤i≤N) について、足場 i の高さは hi です。  
> 最初、足場 1 にカエルがいます。 カエルは次の行動を何回か繰り返し、足場 N まで辿り着こうとしています。  
> - 足場 i にいるとき、足場 i+1 または i+2 へジャンプする。 このとき、ジャンプ先の足場を j とすると、コスト |hi−hj| を支払う。  
> 
> カエルが足場 N に辿り着くまでに支払うコストの総和の最小値を求めてください。
(https://atcoder.jp/contests/dp/tasks/dp_a より引用)

### 1. もらうDP

カエルが足場 i に行く遷移を考えると、
1. i - 1 番目の足場から飛んでくる
1. i - 2 番目の足場から飛んでくる
という2通りの経路が考えられる。

i番目の足場の高さを`h(i)`、i番目の足場にたどり着くのに必要なコストの最小値を `cost(i)` と表すと、
1つ目の経路で足場 i にたどり着くコストの最小値は `cost(i - 1) + abs(h(i) - h(i - 1))`  
2つ目の経路で足場 i にたどり着くコストの最小値は `cost(i - 2) + abs(h(i) - h(i - 2))` となる。

i番目の足場にたどり着くのに必要なコストの最小値は、上の2つの経路でかかるコストのうちの小さい方である。
あとは、`cost(i)`の値を `i = 1, 2, 3 ...` と順番に求めればよい。

```csharp
using System;
using System.Linq;
using static System.Console;

static class Extensions {
   public static int ToInt(this string str) => int.Parse(str);
}

class Program {
   public static void Main(string[] args) {
      var n = ReadLine().ToInt();
      var h = ReadLine().Split(' ').Select(int.Parse).ToArray();

      var dp = new int[n];

      dp[0] = 0;
      dp[1] = Math.Abs(h[0] - h[1]);

      for (int i = 2; i < n; i++) {
         var cost1 = dp[i - 1] + Math.Abs(h[i - 1] - h[i]);
         var cost2 = dp[i - 2] + Math.Abs(h[i - 2] - h[i]);
         
         dp[i] = Math.Min(cost1, cost2);
      }

      WriteLine(dp.Last());
   }
}
```

このように、i番目のノードへの遷移を考える方法を「もらうDP」というらしい。

### 2. 配るDP

もらうDPとは逆に、i番目のノードからの遷移を考える方法もあり、こちらは「配るDP」というらしい。

今回の問題では、カエルが足場 i にいるときに、次の遷移は、
1. i + 1 番目の足場に飛ぶ
1. i + 2 番目の足場に飛ぶ
という2つの経路が考えられる。

先程と同様に、i番目の足場の高さを`h(i)`、i番目の足場にたどり着くのに必要なコストの最小値を `cost(i)` と表すと、
1つ目の経路で足場 i + 1 に行くのにかかるコストは `cost(i) + abs(h(i) - h(i + 1))`  
2つ目の経路で足場 i + 2 に行くのにかかるコストは `cost(i) + abs(h(i) - h(i + 2))`  となる。

ただし、このようにして求めたコストが最小のコストであるかはまだ決定できない。
最小のコストを決定するには、足場 i + 1 については足場 i - 1 から飛んでくるコストと、
足場 i + 2 については足場 i + 1 から飛んでくるコストとの比較が必要である。

```csharp
using System;
using System.Linq;
using static System.Console;

static class Extensions {
   public static int ToInt(this string str) => int.Parse(str);
}

class Program {
   public static void Main(string[] args) {
      var n = ReadLine().ToInt();
      var h = ReadLine().Split(' ').Select(int.Parse).ToArray();

      var dp = new int[n];
      for (int i = 0; i < n; i++) dp[i] = int.MaxValue;

      dp[0] = 0;

      for (int i = 0; i < n - 1; i++) {
         if (i + 1 < n) {
            var cost1 = dp[i] + Math.Abs(h[i + 1] - h[i]);
            if (dp[i + 1] > cost1) dp[i + 1] = cost1;
         }
         if (i + 2 < n) {
            var cost2 = dp[i] + Math.Abs(h[i + 2] - h[i]);
            if (dp[i + 2] > cost2) dp[i + 2] = cost2;
         }
      }

      WriteLine(dp.Last());
   }
}
```

### 3. メモ化再帰

1のもらうDPの考えかたから、一般に`cost(i)`について、  
```
cost(0) == 0
cost(1) == abs(h(1) - h(0))
cost(i) == min(cost(i - 1) + abs(h(i) - h(i - 1)), cost(i - 2) + abs(h(i) - h(i - 2)))
```
という関係式が成り立つことがわかる。　　
この式をそのまま再帰関数として計算すれば、理屈の上では`cost(N)`を求めることができる。  
できるのだが、このまま素直に再帰関数を実装すると計算量が爆発してしまうので、メモ化をして計算量を削減する。

```csharp
using System;
using System.Linq;
using static System.Console;

static class Extensions {
   public static int ToInt(this string str) => int.Parse(str);
}

class Program {
   static int[] h;
   static int[] memo;

   // i番目の足場までの最小コストを求める関数。
   // i番目の足場までの最小コストを求めるには、
   // i-1番目と i-2番目の足場までの最小コストが分かれば良い
   static int rec(int i) {
      if (i == 0) return 0;
      if (i == 1) return Math.Abs(h[0] - h[1]);

      var cost1 = memorec(i - 1) + Math.Abs(h[i - 1] - h[i]);
      var cost2 = memorec(i - 2) + Math.Abs(h[i - 2] - h[i]);

      return Math.Min(cost1, cost2);
   }

   // recをメモ化した関数
   static int memorec(int i) {
      if (memo[i] >= 0) return memo[i];

      var result = rec(i);
      memo[i] = result;
      return result;
   }

   public static void Main(string[] args) {
      var n = ReadLine().ToInt();
      h = ReadLine().Split(' ').Select(int.Parse).ToArray();

      memo = new int[n];
      for (int i = 0; i < n; i++) memo[i] = -1;

      WriteLine(memorec(n - 1));
   }
}
```

## B - Frog 2
> N 個の足場があります。 足場には 1,2,…,N と番号が振られています。  
> 各 i (1≤i≤N) について、足場 i の高さは hi です。最初、足場 1 にカエルがいます。  
> カエルは次の行動を何回か繰り返し、足場 N まで辿り着こうとしています。  
> 足場 i にいるとき、足場 i+1,i+2,…,i+K のどれかへジャンプする。  
> このとき、ジャンプ先の足場を j とすると、コスト |hi−hj| を支払う。  
> カエルが足場 N に辿り着くまでに支払うコストの総和の最小値を求めてください。

A の問題とほぼ同じだが、ジャンプして飛び越せる足場の数が最初に与えられるようになっているので、  
ジャンプして飛び越せる足場の数の範囲からループでコストが最小になるものを探索する。


```cs
using System;
using System.Linq;
using System.Collections.Generic;
using static System.Console;

static class Extensions {
   public static int ToInt(this string str) {
      return int.Parse(str);
   }

   public static int[] readIntArr() {
      return ReadLine().Split(' ').Select(int.Parse).ToArray();
   }

   public static void Fill<T>(this List<T> a, T b) {
      for (var i = 0; i < a.Capacity; i++) {
         a.Add(b);
      }
   } 
}

class Program {
   public static void Main(string[] args) {
      var tmp = Extensions.readIntArr();
      var n = tmp[0];
      var k = tmp[1];
      var h = Extensions.readIntArr();

      var dp = new List<int>(n);
      dp.Fill(System.Int32.MaxValue); 
      dp[0] = 0;
      dp[1] = Math.Abs(h[0] - h[1]);

      for (var i = 2; i < n; i++) {
         for (var j = 1; j <= k; j++) {
            if (i - j < 0) break;
            dp[i] = Math.Min(dp[i], dp[i - j] + Math.Abs(h[i - j] - h[i]));
         }
      }

      WriteLine(dp[n - 1]);
   }
}
```

## D - Knapsack 1
> N 個の品物があって、i 番目の品物の重さは wi、価値は vi で与えられている。
> この N 個の品物から「重さの総和が W を超えないように」いくつか選びます。このとき選んだ品物の価値の総和の最大値を求めよ。
>
>【制約】
> 1≤N≤100
> 1≤W≤10^5
> 1≤wi≤W
> 1≤vi≤10^9
> 入力はすべて整数

有名なナップザック問題。  
普通に解くとNP完全なのでDPする。  

`dp[i][w]`: 0 ~ i 番目までの商品の中から重さが w を越えないように商品の組を選んだときの価値の最大値

W = 8, (w, v) = (3, 3), (4, 5), (5, 6) の場合を例に考える。

まず、重さの総和が 0 の場合、品物を選ぶことができないので価値の総和は 0 である。  

|i\w|0|1|2|3|4|5|6|...|
|--|--|--|--|--|--|--|--|--|
|0|0|?|?|?|?|?|?|?|
|1|0|?|?|?|?|?|?|?|
|2|0|?|?|?|?|?|?|?|

次に、0番目の品物、つまり(v, w) = (3, 3) の品物を選ぶことができる場合を考える。  
この場合、重さの総和が3以上の時はこの品物を選ぶことができ、品物を一つしか選べないのでこれが最適になる。  

|i\w|0|1|2|3|4|5|6|...|
|--|--|--|--|--|--|--|--|--|
|0|0|0|0|3|3|3|3|3|
|1|0|?|?|?|?|?|?|?|
|2|0|?|?|?|?|?|?|?|

次に、0 ~ 1 番目の品物を選ぶことができる場合を考える。  
まず各マスに入る最低限の良い値を考えると、今の状況は先程に加えて品物1を選ぶという選択肢が1つ増えただけの状況なので、  
少なくとも 品物0 だけしか選べない状況よりも良い値をとることができる。  
つまり、各マスには少なくとも1つ上のマスと同じかそれよりも大きな値が入ることになる。  

品物1の重さは4なので、重さの総和が4未満の場合は品物1を選ぶことができない。  
つまり w < 4 のマスは1つ上のマスの値が入る。  

|i\w|0|1|2|3|4|5|6|7|8|9|...|
  |-|-|-|-|-|-|-|-|-|-|-|-|
  |0|0|0|0|3|3|3|3|3|3|3|3|
  |1|0|0|0|3|?|?|?|?|?|?|?|
  |2|0|?|?|?|?|?|?|?|?|?|?|

次に w >= 4 のマスについてだが、品物1を選んだ場合の最も良い値は、1つ上の列で品物1の重さだけ左のマスに品物1の価値を加えた値である。    
なぜなら、総和wで品物1を選んだ場合の最も良い値は、総和がw - (品物1の重さ)で品物1を選ばなかった場合に最も良い値 + 品物1の価値だからである。  
したがって、
1. まず新しい商品を選べるかどうかを調べる  
2-A. (選べない場合) 1つ上のマスの値を採用  
2-B. (選べる場合) 1つ上の列で新しい商品の重さだけ左にあるマスに品物の価値を加えた値(新しい品物を選んだ場合の値)と、  
     1つ上のマスの値(新しい品物を選ばなかった場合の値)を比べて、良い方を採用  
とすれば良い

```cs
using System;
using System.Linq;
using System.Collections.Generic;
using static System.Console;
using static System.Math;

namespace A {
static class Extensions {
   public static int ToInt(this string str) =>
      int.Parse(str);

   public static int[] readIntArr() =>
      ReadLine().Split(' ').Select(int.Parse).ToArray();

   public static long[] readLongArr() =>
      ReadLine().Split(' ').Select(long.Parse).ToArray();
   
   public static void Fill<T>(this List<T> a, T b) {
      for (var i = 0; i < a.Capacity; i++) {
         a.Add(b);
      }
   } 

   public static void Fill<T>(this T[] a, T b) {
      for (var i = 0; i < a.Length; i++) {
         a[i] = b;
      }
   }
}

class Program {
   public static void Main(string[] args) {
      var tmp = Extensions.readIntArr();

      var N = tmp[0];
      var W = tmp[1];
      var w = new long[N + 1];
      var v = new long[N + 1];
      
      for (var i = 1; i < N + 1; i++) {
         var tmp2 = Extensions.readIntArr();
         w[i] = tmp2[0];
         v[i] = tmp2[1];
      }

      var dp = new long[N + 1][];
      for (var i = 0; i < N + 1; i++)
         dp[i] = new long[W + 1];

      for (var i = 1; i <= N; i++) {
         for (var j = 0; j <= W; j++) {
            if (w[i] <= j) {
               dp[i][j] = Max(dp[i - 1][j - w[i]] + v[i], dp[i - 1][j]);
            } else {
               dp[i][j] = dp[i - 1][j];
            }
         }
      }

      WriteLine(dp[N][W]);
   }
}
}
```


## E - Knapsack 2
> N 個の品物があって、i 番目の品物の重さは wi、価値は vi で与えられている。
> この N 個の品物から「重さの総和が W を超えないように」いくつか選びます。このとき選んだ品物の価値の総和の最大値を求めよ。
>
>【制約】
>1≤N≤100
>1≤W≤10^9
>1≤wi≤W
>1≤vi≤10^3
>入力はすべて整数

問題文がDと同じなので同じ問題に見えるかもしれないが、よく見ると制約が違う。  
さっきは重さの総和最大値が 10^5 以下だったのに対し、今回は10^9 以下になっている。  
先程の解法では大体 N * W 回だけループを回す必要があるので、今回の制約では大体 10^11 回程度のループが必要になる。  

そこで発想を変えて、  

`dp[i][v]`: 0 ~ i 番目までの商品の中から価値が v になるように商品の組を選んだときの重さの総和の最小値  
として、  
`dp[N][v]`が W 以下であるような v の最大値を答えとすればよい。  

今回の制約では各品物の価値は 10^3 以下で品物の数も 10^2 以下なので、全商品の価値の総和は 10^5 以下であり、
ループの回数も 10^7 程度になる。  

このように、動的計画法を使って効率的に問題が解けるには問題の制約のおかげであって、  
動的計画法を使ったからといってNP困難な問題が多項式時間で解けるようになる魔法の方法ではないのである。  

```cs
using System;
using System.Linq;
using System.Collections.Generic;
using static System.Console;
using static System.Math;

namespace A {
static class Extensions {
   public static int ToInt(this string str) =>
      int.Parse(str);

   public static int[] readIntArr() =>
      ReadLine().Split(' ').Select(int.Parse).ToArray();

   public static long[] readLongArr() =>
      ReadLine().Split(' ').Select(long.Parse).ToArray();
   
   public static void Fill<T>(this List<T> a, T b) {
      for (var i = 0; i < a.Capacity; i++) {
         a.Add(b);
      }
   } 

   public static void Fill<T>(this T[] a, T b) {
      for (var i = 0; i < a.Length; i++) {
         a[i] = b;
      }
   }
}

class Program {
   public static void Main(string[] args) {
      var tmp = Extensions.readIntArr();

      var N = tmp[0];
      var W = tmp[1];
      var w = new long[N + 1];
      var v = new long[N + 1];
      
      for (var i = 1; i < N + 1; i++) {
         var tmp2 = Extensions.readIntArr();
         w[i] = tmp2[0];
         v[i] = tmp2[1];
      }

      var V = v.Sum();

      var dp = new long[N + 1][];
      for (var i = 0; i < N + 1; i++) {
         dp[i] = new long[V + 1];
         dp[i].Fill(long.MaxValue);
      }
      for (var i = 0; i < N + 1; i++) {
         dp[i][0] = 0;
      }

      for (var i = 1; i <= N; i++) {
         for (var j = 1; j <= V; j++) {
            if (j <= v[i]) {
               dp[i][j] = Min(dp[i - 1][j], w[i]);
            } else
            if (dp[i - 1][j - v[i]] != long.MaxValue) {
               dp[i][j] = Min(dp[i - 1][j], dp[i - 1][j - v[i]] + w[i]);
            } 
         }
      }

      var ams = 0;
      for (var j = 1; j <= V; j++) {
         if (dp[N][j] <= W) ams = j;
      }

      WriteLine(ams);
   }
}
}
```

# 微分方程式の数値解法

## 微分方程式とは？

微分方程式の前にふつうの方程式（代数方程式）について考える。
 $x$ を未知数として、 $x$ についての関係式 $ a_{0} + a_{1}x + a_{2}x^2 + ... + a_{n}x^n = 0 $ 
を $x$ の（n次）方程式といい、方程式を満たす（複素）数 $x$ を見つけることを「方程式を解く」という。

同様に、 $y$ を $x$ についてn回微分可能な未知関数として、$y', y'', ..., y^{(n)} $ についての関係式 $F(x, y, y', ..., y^{(n)}) = 0 $ を 
$y$ に関する n階（常）微分方程式といい、微分方程式を満たす関数 $y(x)$ を見つけることを「微分方程式を解く」という。

### 例題1
たかし君が $t = 0$ の時点で $x = 0$に存在する自宅から出発したとする。
たかし君の移動速度$x'$は $x' = C (C: Constant)$で表されるとする。
時刻$t$でのたかし君の位置$x$を求めよ。

#### 解答
$x' = C$ は $x, t$ を含まない定数関数なので、そのまま積分すればよい。
$x = \int{C}dt + C_0 = Ct + C_0$
初期条件 $x(t = 0) = 0$ を代入し、 $C_0 = 0$。よって
$x(t) = Ct$ が解となる

### 例題2
たかし君の移動速度 $x'$ が $x' = Ct$ だった場合は？

#### 解答
$x' = Ct$ は $x$ を含まないので、そのまま $t$ について積分すればよい。
$x = \int{Ct}dt + C_0 = t^2/2 + C_0 = t^2/2 $

### 例題3
たかし君の移動速度 $x'$ が $x' = Cx$ だった場合は？

#### 解答
$x' = Cx$ は $x$ を含む関数なので、そのままでは $t$ で積分できない（服を買いに行くための服が無いような状況である）
そこで、両辺を $x$ で割り $x'/x = C$ という式を作る。すると、両辺を $t$ で積分すると、
$(左辺) = \int{\frac{x'}{x}}dt = \int{\frac{1}{x}\frac{dx}{dt}}dt = \int{\frac{1}{x}}dx$ となり、 $x$ についての積分に変形できる。
右辺はそのまま積分すればよいので、両辺で積分を実行すると $ln|x| = Ct + C_0 → x = C_0 e^{Ct}$ となる。

一般に $y'$ が $x$ のみを含む関数 $P(x)$ と $y$ のみを含む関数 $Q(y)$ との積で書けるとき、 $y'$ は変数分離可能であるといい、そのような形の微分方程式
$y' = P(x)Q(y)$ を変数分離形という。
変数分離形の微分方程式は、両辺を $Q(y)$ で割って $x$ で積分することで $\int{\frac{1}{Q(y)}}dy = \int{P(x)}dx + C$ と変形できるので積分を実行すれば解が得られる。

このように変数変換や関数変換をうまいこと組み合わせて微分方程式を解く方法を求積法という。
しかし、世の中には求積法で解けない方程式がたくさんある。そこでコンピュータの出番である。

## オイラー法
以下では簡単のため、$x' = f(t, x)$ という形の1階微分方程式について考え、初期条件は $x(0) = x_0$ とする。
たかし君で考えると、たかし君の移動速度が $f(t, x)$ で与えられている場合に時刻 $t$ でのたかし君の位置 $x$ を求めるということである。
もっとも素朴な方法は、ある短い時間 $h$ に着目して、その間はたかし君は同じ速度で走り続けたものと考える方法である。
まず $t = 0$ でのたかし君の速度は $f(0, x_0)$ である。ここから $t = h$ まで同じ速度で走るので $t = h$ でのたかし君の位置 $x_1$ は $x_1 = x_0 + f(0, x_0)h $である。
この時のたかし君の速度は $f(h, x_1)$ となり、また $h$秒間同じ速度で走るので $t = 2h$ では、$x_2 = x_1 + f(h, x_1) h$ となる。
このようにして $x(t)$を求める方法をオイラー法という。

## ホイン法
オイラー法では $t = 0 → h $ の間はたかし君が速度 $v_0 = f(0, x_0)$で走り続け、$t = h$ になった瞬間に $v_1 = f(h, x_1)$で走り始めると仮定していた。
しかし、見方を変えるとたかし君の速度は $t = 0 → h $ の間で $v_0 → v_1 $に変化したと考えることもできる。
そうするとたかし君は $v_0$ で走り続けたと考えるよりも、$v_0$ と $v_1$ の平均 $\frac{v_0 + v_1}{2}$で走り続けたと考えた方が自然である。
したがって、$t = h$でのたかし君の位置 $x_1$ は
$v_0 = f(0, x_0) $
$v_1 = f(h, x_0 + v_0h) $
$x_1 = x_0 + h(v_0 + v_1)/2 $
となる。
$t = h(n+1)$ における位置$x_{n+1}$は
$k_0 = f(t_n, x_n)$
$k_1 = f(t_{n+1}, x_n + k_0h)$
$x_{n+1} = x_n + (k_0 + k_1)h/2$
となる。

## ルンゲクッタ法
ホイン法を更に細かくしたもの。
次の手順で1ステップの計算を行う。

1. $x_0$ での速度 $v_0 = f(0, x_0)$ を求める
1. $x_0$ から速度 $v_0$ で h/2 秒進んだ場合の位置 $x_1 = x_0 + v_0 h/2$ を求める
1. $x_1$ での速度 $v_1 = f(h/2, x_1)$ を求める
1. $x_0$ から速度 $v_1$ で h/2 秒進んだ場合の位置 $x_2 = x_0 + v_1 h/2$ を求める
1. $x_2$ での速度 $v_2 = f(h/2, x_2)$ を求める
1. $x_0$ から速度 $v_2$ で h 秒進んだ場合の位置 $x_3 = x_0 + v_2 h$ を求める
1. $x_3$ での速度 $v_3 = f(h, x_3)$ を求める
1. $v_0$ から $v_3$ までを 1・2・2・1 の比率で重み付けして平均の速さ $v_4 = \frac{v_0 + 2v_1 + 2v_2 + v_3}{6}$ を求める
1. $x_0$ から速度 $v_4$ で h 秒進んだものとして位置 $x_4 = x_0 + v_4 h$ を求める
1. $x_4$ を1ステップ後の位置として決定する

$k_0 = f(t_n, x_n)$
$k_1 = f(t_n + h/2, x_n + k_0 h/2)$
$k_2 = f(t_n + h/2, x_n + k_1 h/2)$
$k_3 = f(t_{n+1}, x_n + k_2 h)$
$x_{n+1} = x_n + (k_0 + 2k_1 + 2k_2 + k_3)h/6 $


## Demo

``` python
import pygame
from pygame.locals import *
import sys
import math

SCREEN_WIDTH = 640
SCREEN_HEIGHT = 480

G = 50000
DELTA_T = 0.1

pygame.init()
screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
pygame.display.set_caption("Runge-Kutta Test")

def force(x, y):
   dx = x - Sun.x
   dy = y - Sun.y
   r = math.sqrt(dx**2 + dy**2)
   fx = - dx*G / r**3
   fy = - dy*G / r**3
   return (fx, fy)

class Star:
   def __init__(self, x, y, vx, vy):
      self.x = x
      self.y = y
      self.vx = vx
      self.vy = vy
   
   def draw(self):
      pygame.draw.circle(screen, self.color, (int(self.x), int(self.y)), 5)

class Sun(Star):
   x = SCREEN_WIDTH / 2
   y = SCREEN_HEIGHT / 2
   color = (0, 0, 0)
   def __init__(self): pass

class EulerStar(Star):
   color = (255, 0, 0)
   def update(self):
      ax, ay = force(self.x, self.y)
      self.vx += ax * DELTA_T
      self.vy += ay * DELTA_T
      self.x += self.vx * DELTA_T
      self.y += self.vy * DELTA_T

class RungeStar(Star):
   color = (0, 255, 0)
   def update(self):
      x0, y0 = self.x, self.y
      vx0, vy0 = self.vx, self.vy

      kx1, ky1 = vx0, vy0
      kvx1, kvy1 = force(x0, y0)
      kx2, ky2 = vx0 + kvx1 * DELTA_T/2, vy0 + kvy1 * DELTA_T/2
      kvx2, kvy2 = force(x0 + kx1 * DELTA_T/2, y0 + ky1 * DELTA_T/2)
      kx3, ky3 = vx0 + kvx2 * DELTA_T/2, vy0 + kvy2 * DELTA_T/2
      kvx3, kvy3 = force(x0 + kx2 * DELTA_T/2, x0 + ky2 * DELTA_T/2)
      kx4, ky4 = vx0 + kvx3 * DELTA_T, vy0 + kvy3 * DELTA_T
      kvx4, kvy4 = force(x0 + kx3 * DELTA_T, y0 + kx3 * DELTA_T)

      self.x += DELTA_T * (kx1 + 2*kx2 + 2*kx3 + kx4) / 6
      self.y += DELTA_T * (ky1 + 2*ky2 + 2*ky3 + ky4) / 6
      self.vx += DELTA_T * (kvx1 + 2*kvx2 + 2*kvx3 + kvx4) / 6
      self.vy += DELTA_T * (kvy1 + 2*kvy2 + 2*kvy3 + kvy4) / 6

def main():
   sun = Sun()
   es = EulerStar(50, 50, 0, 0) # 好きな初期値を入れる
   rs = RungeStar(50, 50, 0, 0) # 好きな初期値を入れる

   while(True):
      screen.fill((255, 255, 255))
      es.update()
      rs.update()
      es.draw()
      rs.draw()
      sun.draw()
      pygame.display.update()
   
      for event in pygame.event.get():
         if event.type == QUIT:
            pygame.quit()
            sys.exit()

if __name__ == "__main__":
      main()
```



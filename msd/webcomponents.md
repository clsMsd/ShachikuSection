# Web Components

## 背景
弊社で開発中のサービスで無料のユーザーには「お金払ってね」のメッセージを出すようにするというものがあるのだが、  
これだとユーザーの操作でメッセージを消されてしまう。  
Devtoolsで消されるのはまあ諦めるとして、ブックマークレットやUser Scriptで一発で消されてしまうと  
こまったことになりそう… という訳で何か対策できないか調べたところ、  
Web ComponentsのShadowDOMというのを使うと多少の対策になりそうだと分かった。  

## Web Componentsとは？
> Web Components is a suite of different technologies allowing you to create reusable custom elements —  
> with their functionality encapsulated away from the rest of your code — and utilize them in your web apps.  
> (https://developer.mozilla.org/en-US/docs/Web/Web_Components より引用)

> Web Components は、再利用可能なカスタム要素を作成し、ウェブアプリの中で利用するための、  
> 一連のテクノロジーです。コードの他の部分から独立した、カプセル化された機能を使って実現します。   
> (https://developer.mozilla.org/ja/docs/Web/Web_Components より引用)

再利用可能なHTML要素(コンポーネント)を作るWeb標準仕様。  
主に
- CustomElement
- ShadowDOM
- HTML Template

の3つからなる

### Custom Element
一言で言うと、「独自のhtmlタグを作る機能」。  
言葉で説明するより実物を見た方が早いと思うので下に具体例を載せる。  

```html
<html>
   <head></head>
   <body>
      <my-div></my-div>
      <script>
         class MyDiv extends HTMLElement {
            constructor() {
               super()
               this.innerHTML = `<div>お金払ってね</div>`
            }
         }

         customElements.define("my-div", MyDiv)
      </script>
   </body>
</html>
```
↑のように感じで，`HTMLElement`を継承した独自クラスを作り，それを`customElements.define`メソッドでCustomElementとして登録することで
独自タグとして使うことができる。

CustomElementを使う際にはいくつかの条件を守る必要がある。  
- JavaScriptではクラス構文以外でもFunctionを使って継承を行うことができるが，CustomElementを作る場合は必ずクラス構文を使わなければならない  
  (従ってES2015に対応していない非モダンブラウザ(IE11)では動作しない。ただしpolyfillはある)
- 独自定義するタグ名には必ず`-`(ハイフン)を含めなければならない
- CustomElementsを定義するJavaScriptは必ずhtml上で**独自タグを使った後**に実行されなければならない。  
  上の例では`<script>`タグを`<my-div>`の上に持っていくと正常に動作しない。

CustomElementはまったく新しいHTML要素となるAutonomous custome element(自律カスタム要素)と，  
既存のHTML要素を拡張するCustomized build-in elementの2種類に分けられる。  
上の例は新しいHTML要素を作っているのでAutonomous custome elementである。  

Customized build-in elementを使うと，例えば以下のようにしてHLSを再生できるVideo要素を作ることができる。  
```html
<html>
   <head>
   </head>
   <body>
      <!-- タグ名の代わりに is属性 に使用するカスタム要素の名前を指定する -->
      <video is="hls-video" src="https://test-streams.mux.dev/x36xhzz/x36xhzz.m3u8" width="400" controls></video>

      <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
      <script>
         class HlsVideo extends HTMLVideoElement { // 拡張したいHTML要素を継承する
            constructor() {
               super()
               if (!Hls.isSupported()) {
                  console.log("hls.js is not supported.")
                  return
               }

               const hls = new Hls()
               hls.loadSource(this.getAttribute("src"))
               hls.attachMedia(this)
            }
         }

         customElements.define("hls-video", HlsVideo, { extends: "video" }) // 第3引数に拡張するHTML要素の名前を指定する
      </script>
   </body>
</html>
```
今回はやっていないが`play`や`pause`等のメソッドをオーバーライドすることもできる。  

一見便利そうだが結局is属性でタグ名を指定するのなら自律カスタム要素で良いのでは？という感じであまりメリットが無い気がする。  
この機能はSafariは未実装なので実際の開発では使わない方が良さそう。  

属性を受け取る場合はコンストラクタか`connectedCallback`で属性を取得すればよい。  
```html
<html>
   <head>
   </head>
   <body>
      <my-div msg="hogehoge"></my-div>
      <script>
         class MyDiv extends HTMLElement {
            constructor() {
               super()
               const msg = this.getAttribute("msg")
               this.innerHTML = `<div>${msg}</div>`
            }
         }

         customElements.define("my-div", MyDiv) 
      </script>
   </body>
</html>
```

ただしこのままでは属性が変化した場合にもメッセージは変化しない。  
動的に属性を変更した場合にメッセージを変化させたい場合は、`observedAttributes`メソッドで監視する属性名を指定した上で、  
`attributeChangedCallback`内に属性が変化した際の処理を書けばよい。
```html
<html>
   <head>
   </head>
   <body>
      <my-div msg="hogehoge"></my-div>
      <script>
         class MyDiv extends HTMLElement {
            constructor() {
               super()
               const msg = this.getAttribute("msg")
               this.innerHTML = `<div>${msg}</div>`
            }

            static get observedAttributes() { return ['msg'] }

            attributeChangedCallback(name, oldValue, newValue) {
               const msg = this.getAttribute("msg")
               this.innerHTML = `<div>${msg}</div>`
            }
         }

         customElements.define("my-div", MyDiv) 
      </script>
   </body>
</html>
```

この例からも分かるように、入力値や内部状態に応じて依存する子要素だけを差分更新したいという場合には  
そういう処理を全部自分で書かないといけないので大変である(VDOMの自前実装)。  

### ShadowDOM
一言でいうと，「外部から隠ぺいされたDOMを作る機能」。

例えば，映像と一緒にお金払ってねメッセージを表示するvideo要素を作ったとする。  
```html
<html>
   <head>
   </head>
   <body>
      <hls-video src="https://test-streams.mux.dev/x36xhzz/x36xhzz.m3u8" width="400"></hls-video>

      <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
      <script>
         class HlsVideo extends HTMLElement {
            constructor() {
               super()
               if (!Hls.isSupported()) {
                  console.log("hls.js is not supported.")
                  return
               }

               const video = document.createElement("video")
               video.width = this.getAttribute("width")
               video.controls = true
               this.appendChild(video)
               const div = document.createElement("div")
               div.innerText = "お金払ってね"
               this.appendChild(div)

               const hls = new Hls()
               hls.loadSource(this.getAttribute("src"))
               hls.attachMedia(video)
            }
         }

         customElements.define("hls-video", HlsVideo)
      </script>
   </body>
</html>
```
お金払いたくない人達はコンソールやブックマークレットから以下のようなコードを実行してメッセージを消そうとするだろう。  
```javascript
document.querySelector("hls-video > div").remove()
```

そこで我々はShadowDOMを使うことでhls-videoの内部実装を隠ぺいし，外部のJavaScriptからのDOMを書き換えを禁止することができる。  
```html
<html>
   <head>
   </head>
   <body>
      <hls-video src="https://test-streams.mux.dev/x36xhzz/x36xhzz.m3u8" width="400"></hls-video>

      <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
      <script>
         class HlsVideo extends HTMLElement {
            constructor() {
               super()
               if (!Hls.isSupported()) {
                  console.log("hls.js is not supported.")
                  return
               }

               const video = document.createElement("video")
               video.width = this.getAttribute("width")
               video.controls = true
               const div = document.createElement("div")
               div.innerText = "お金払ってね"

               const shadowRoot = this.attachShadow({ mode: "closed" })
               shadowRoot.appendChild(video)
               shadowRoot.appendChild(div)

               const hls = new Hls()
               hls.loadSource(this.getAttribute("src"))
               hls.attachMedia(video)
            }
         }

         customElements.define("hls-video", HlsVideo)
      </script>
   </body>
</html>
```
constructorの真ん中あたりで実行している`this.attachShadow({ mode: "close" })`が重要で，  
このメソッドは戻り値としてDOMへの参照を返すので`appendChild`等のメソッドで要素を追加することができるが，  
このDOMの子要素への参照は隠ぺいされてJavaScriptから見えなくなる。  

実はChromeのvideo要素自体もCustomElementとShadowDOMで出来ているので，devtoolsの設定で `Show user agent shadow DOM` にチェックを付けると
videoの内部実装を見ることができる。

### slotとtemplete
独自タグを作ったら子要素を受け取りたくなるのが人情というものだろう[要出典]。  
templateとslotを使うと予め用意したHTMLのテンプレートの一部を外から与えられた要素で置き換えることができる。  

```html
<html>
  <head></head>
  <body>
    <template id="template">
      <div>
        <slot name="title"></slot>
        <slot name="description"></slot>
      </div>
    </template>

    <div id="template-sample">
      <h1 slot="title">タイトル</h1> 
      <p slot="description">説明</p> 
    </div>

    <div id="template-sample">
      <p slot="title">タイトル</p> 
      <h1 slot="description">説明</h1> 
    </div>

    <script>
      const temp = document.getElementById("template")
      for (const e of document.getElementsByClassName("template-sample")) {
        e.attachShadow({ mode: "open" })
          .appendChild(temp.content.cloneNode(true))
      }
    </script>
  </body>
</html>
```

## サンプル
前に作ったマンデルブロ集合を描画するやつをWeb Componentに移植してみた。

```typescript
class MandelbrotSet extends HTMLElement {
  private canvas: HTMLCanvasElement
  private inputX: HTMLInputElement
  private inputY: HTMLInputElement
  private relaodBtn: HTMLButtonElement

  constructor() {
    super()
    const temp = document.createElement("template")
    temp.innerHTML = `
      <slot name="canvas"></slot>
      <br/>
      中心のx座標:<slot name="input-x"></slot>
      <br/>
      中心のy座標:<slot name="input-y"></slot>
      <br/>
      拡大率:<slot name="expansion-rate"</slot>
      <br/>
      <slot name="reload-btn"></slot>
      <br/>
      <button id="dl">画像としてダウンロード</button>
    `
    const sroot = this.attachShadow({ mode: "closed" })
    sroot.appendChild(temp.content.cloneNode(true))

    const canvas = document.createElement("canvas")
    canvas.setAttribute("id", "canvas")
    canvas.setAttribute("width", "400")
    canvas.setAttribute("height", "400")
    canvas.setAttribute("slot", "canvas")
    this.canvas = canvas

    const inputX = document.createElement("input")
    inputX.setAttribute("type", "number")
    inputX.setAttribute("value", "0")
    inputX.setAttribute("slot", "input-x")
    this.inputX = inputX

    const inputY = document.createElement("input")
    inputY.setAttribute("type", "number")
    inputY.setAttribute("value", "0")
    inputY.setAttribute("slot", "input-y")
    this.inputY = inputY

    const reloadBtn = document.createElement("button")
    reloadBtn.innerText = "更新"
    reloadBtn.onclick = this.reload.bind(this)
    reloadBtn.setAttribute("slot", "reload-btn")
    this.relaodBtn = reloadBtn

    this.appendChild(this.canvas)
    this.appendChild(this.inputX)
    this.appendChild(this.inputY)
    this.appendChild(this.relaodBtn)

    renderMB(this.canvas.getContext("2d")!, { x:0, y:0 }, 400)
  }

  reload() {
    const x = parseInt(this.inputX.value)
    const y = parseInt(this.inputY.value)
    renderMB(this.canvas.getContext("2d")!, { x, y }, 400)
  }
}

customElements.define("mandelbrot-set", MandelbrotSet)
```

使う側はHTMLで`<mandelbrot-set></mandelbrot-set>`と書くだけで良い。  

## 実際のところのWeb Componentの使われ方
ネットを見ると「Web Componentの登場でReactやVueがオワコンになるだろう」という意見が稀に良くみられる。  
しかしこの手の意見は現実を何も知らない人が言っているに過ぎない… と思う。  

まずWeb Component自体もはや既に新しい技術ではない。  
2017~2018年頃にモダンブラウザでは一通りの実装は終わっていたし，  
polymerというpolyfillを使えば2015年頃からでも，IEを含む非モダンブラウザでもWeb Componentを使うことができた。  
しかし現実にReactやVueの代わりとしてWeb Componentを使ってWebアプリを実装するということは全くと言ってよい程行われていない。  

実際使ってみると分かるが、Web Componentはあくまで**再利用可能な独自HTML要素**を作る機能という感じで、  
どちらかというとJavaScriptよりもHTMLの利用者にフォーカスしている気がする。  
実際ライブラリとしてCustomElementを配布すれば、ライブラリの利用者からはJavaScript無しに独自HTML要素が使えるので、  
JavaScriptを全く書かない純粋なデザイナーやマークアップエンジニアであってもWeb Componentの恩恵を受けることができる。  
一方でCustomElementを作る側からすると若干機能が不足しているという感じは否めない。  
templateやslotなど無いよりかはあったほうが良いのは間違い無いが、JSXの簡潔なDOM操作に慣れた身からすると  
相変わらず`createElement`や`setAttribute`、`getElementById`等のメソッドでのDOM操作が必要となると  
やはりReact使った方が良いのでは？という気になってしまう。  

今回は詳しく調べていないが、Web Componentsを使ったSPAライブラリとしてlit-htmlやlit-element  
といったものがあるらしいので、実際に開発をする際にはそういうものを使った方が良いかもしれない。  
(しかし独自のUIライブラリに頼らずWeb標準だけでSPAが作れるというのがWeb Componentsのメリットだと思うので、  
こういうライブラリに頼ってしまうなら最初からPreactとかを使うのと変わらないのでは？という感がある)  
(ちなみにlit-htmlのバンドルサイズが3kbなのに対してpreactのサイズがほぼ同じ3kb、  
react + react-dom でも 40kb強程度である)  

Web Componentの現実的な使われ方は，ReactやVue置き換えるものではなく，  
むしろReactとVueの橋渡しをするものだと思っている。  
例えば，現状ではMaterial-UIのようなReact製のUIフレームワークをVueで使ったり，  
逆にVue製のUIフレームワークをReactで使うというのは困難であるが、  
これがWeb Componentの普及により各UIフレームワークがWeb Componentとして配布されるようになれば，  
React製のフレームワークをVueで使う，あるいはその逆ということが簡単にできるようになる。  

ただし、ReactとWeb Componentの相性はあまり良くない  
(ReactのEventはラップされていてWebComponentsとReact間でイベントが伝達されない  
[https://github.com/facebook/react/issues/7901]、  
HooksAPIを使ったFunctionalComponentとCustomElementの相性が悪い、など)。  
現状ではWeb ComponentsのためにわざわざReactを捨てるという選択をすることはあまり無いと思うので、  
ReactとVueで同じUIフレームワークが使えるようになる世界というのはまだまだ先のことになりそうである。  

## ShadowDOMを外から消す方法
上で見たようにShadowDOMを使えばJavaScriptから消されないHTML要素を作ることができるが、
そう単純な話ではない。  

例えばTampermonkey のような拡張機能でページのJavaScriptが実行される前に下のようなUser Scriptが実行されることを防ぐことはできない。  
```javascript
Element.prototype._attachShadow = Element.prototype.attachShadow
Element.prototype.attachShadow = function () {
	return this._attachShadow({ mode: "open" })
}
```

`setInterval`でDOMが消されていないか検知して，消されていた場合にメッセージを表示するという方法もある。
```html
<html>
   <head>
   </head>
   <body>
      <hls-video src="https://test-streams.mux.dev/x36xhzz/x36xhzz.m3u8" width="400"></hls-video>

      <script src="https://cdn.jsdelivr.net/npm/hls.js@latest"></script>
      <script>
         class HlsVideo extends HTMLElement {
            constructor() {
               super()
               if (!Hls.isSupported()) {
                  console.log("hls.js is not supported.")
                  return
               }

               let ctr = 0
               let timerId
               timerId = setInterval(() => {
                  const video = document.createElement("video")
                  video.width = this.getAttribute("width")
                  video.controls = true
                  const div = document.createElement("div")
                  div.innerText = "お金払ってね"

                  const shadowRoot = this.attachShadow({ mode: "closed" })
                  shadowRoot.appendChild(video)
                  shadowRoot.appendChild(div)

                  const hls = new Hls()
                  hls.loadSource(this.getAttribute("src"))
                  hls.attachMedia(video)
                  
                  clearInterval(timerId)
               }, 1)

               setInterval(() => {
                  const msg = document.querySelector("hls-video > div")
                  if (!msg) {
                     document.querySelector("hls-video").remove()
                     document.body.innerText = "お金払ってね！！！"
                  }
               }, 3000)
            }
         }

         customElements.define("hls-video", HlsVideo)
      </script>
   </body>
</html>
```

しかし，これにも対策が存在する。  
例えば`querySelector`自体を書き換えられてしまうとどうしようもない。  
それ以外でも`setTimeout`や`setInterval`で返される`timeoutId`はタイマーごとに単純にインクリメントされるので，  
次のコードを実行されると全てのタイマーが停止させられてしまう。  
```javascript
const timerId = setTimeout(() => {})
for(let i = 0; i < timerId; i++) {
   clearTimeout(i)
}
```

できる限りの対策をするとなると、  
1. 適当な関数を `toString` して `toString` の実装が書き換えなくていないかチェック
1. `attachShadow` `setTimeout` `setInterval` `querySelector` 等の関数を `toString` して実装が書き換えられていないかチェック
1. `MutasionObserver` + タイマーで DOMが書き換えられていないか監視
1. DOMが書き換えられていたらメッセージを表示

とするぐらいが現実的かつそれなりに効果がありそうな落とし所だと思う。  

## 参考資料
https://developer.mozilla.org/ja/docs/Web/Web_Components

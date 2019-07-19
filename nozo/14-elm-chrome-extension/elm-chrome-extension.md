# Elmでchrome拡張をつくる備忘録

友人にElmをおススメされたのでchrome拡張をElmでつくる（適しているかは不明）ことを目標に遊んでみる。

> ## Elm について (はじめに)
> **Elm は JavaScript にコンパイルできる関数型プログラミング言語です。** Elm は JavaScript にコンパイルできる関数型プログラミング言語です。 ウェブサイトやウェブアプリケーションを作るツールという面では React のようなプロジェクトだと言えます。 Elm はシンプルであること、簡単に使えること、高品質であることを大切にしています。
> 
> 公式ドキュメント(翻訳ver)：https://guide.elm-lang.jp/

## 目標のchrome拡張

ページ内で動的に生成されたDOMを検出して通知に表示する拡張 (https://github.com/isNozo/page-observer) をElmで書き直す。

次の機能がElmから使えるようにしたい。

主な機能：
- MutationObserver : DOM の変更を検知 https://developer.mozilla.org/ja/docs/Web/API/MutationObserver
- chrome.notifications : chromeの通知API https://developer.chrome.com/apps/notifications

## Elmのアーキテクチャ

まずはどんなふうにプログラムが書けるのか見てみる。
Elmは次の３つの要素からなる構成が基本となるようだ。

> - Model — アプリケーションの状態
> - Update — 状態を更新する方法
> - View — HTMLとして状態を閲覧する方法
> 
> https://guide.elm-lang.jp/architecture/

簡単なカウンタの例を見てみる。

```elm
import Browser
import Html exposing (Html, button, div, text)
import Html.Events exposing (onClick)

main : Program () Model Msg
main = Browser.sandbox { init = init, view = view, update = update }

-- MODEL                                                                             

type alias Model = { count : Int }

init : Model
init = { count = 0 }

-- VIEW                                                                              

view : Model -> Html Msg
view model =
  div []
    [ button [ onClick Decrement ] [ text "-" ]
    , div [] [ text (String.fromInt model.count) ]
    , button [ onClick Increment ] [ text "+" ]
    ]

-- UPDATE                                                                            

type Msg = Increment | Decrement

update : Msg -> Model -> Model
update msg model =
  case msg of
    Increment -> { count = model.count + 1 }
    Decrement -> { count = model.count - 1 }
```

### Model

このアプリケーションは状態をカウンタ

### View

viewは関数として定義される。関数の型 `Model -> Html Msg` が表すように、アプリケーションの状態を入力に受け取り、表示したいHTMLを返している。

HTMLのタグや属性もすべて関数として定義されていて、上の例は次のHTMLを表現している。

```html
<div>
  <button>-</button>
  <div>0</div>
  <button>+</button>
</div>
```

### Update

updateも関数として定義される。updateはHTMLのボタンが押されたときなどにModelをどのように変更するかを定義する。
ボタンが押されたなどの変化は `Msg` 型として表現し、この例では＋ボタンが押されたら  `Increment` が、－ボタンが押されたら `Decrement` が `Msg` としてupdate関数の第1引数に渡される。
第２引数は現在の `Model` が渡され、 `Msg` の内容に応じて変更した新しい `Model` を返り値として返す。

![](https://guide.elm-lang.jp/effects/diagrams/sandbox.svg)

引用：https://guide.elm-lang.jp/effects/

# 参考文献
- [ファイアウォール ルールの使用 | VPC | Google Cloud](https://cloud.google.com/vpc/docs/using-firewalls?hl=ja)

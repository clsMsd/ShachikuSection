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

```elm
type alias Model = { count : Int }

init : Model
init = { count = 0 }
```

この例ではカウンタとして数値を保持したいので `Int` 型のフィールドを一つ持つレコードを `Model` として定義した。扱いたい値が増えたらこのレコードのフィールドを増やせば簡単に拡張できる。

`Model` の初期値をinitで定義している。

### View

```elm
view : Model -> Html Msg
view model =
  div []
    [ button [ onClick Decrement ] [ text "-" ]
    , div [] [ text (String.fromInt model.count) ]
    , button [ onClick Increment ] [ text "+" ]
    ]
```

viewは関数として定義される。関数の型 `Model -> Html Msg` が表すように、アプリケーションの状態 `Model` を入力に受け取り、表示したいHTMLのかたまり `Html Msg` を返している。`Msg` については後述するがこのHTMLのかたまりは `Msg` で定義されたメッセージを生成しうることを表している。

HTMLのタグや属性もすべて関数として定義されている。

```elm
> div
<function> : List (Html.Attribute msg) -> List (Html msg) -> Html msg
> button
<function> : List (Html.Attribute msg) -> List (Html msg) -> Html msg
> text
<function> : String -> Html msg
> onClick
<function> : msg -> Attribute msg
```

上の例では次のようなHTMLを生成する。

```html
<div>
  <button>-</button>
  <div>0</div>
  <button>+</button>
</div>
```

### Update

```elm
type Msg = Increment | Decrement

update : Msg -> Model -> Model
update msg model =
  case msg of
    Increment -> { count = model.count + 1 }
    Decrement -> { count = model.count - 1 }
```

updateも関数として定義される。型 `Msg -> Model -> Model` は、ボタンが押されたときなど発生したメッセージ `Msg` と現在の `Model` を受け取り、新しい `Model` を返すことを表している。

この例では、`Increment` と `Decerement` の２つのメッセージが発生しうるとして `Msg` を定義している。
そして実際にviewで定義した"+/-"ボタンの `onClick` 属性でこれら２つのメッセージが生成されるように設定している。

```elm
    [ button [ onClick Decrement ] [ text "-" ]
    , div [] [ text (String.fromInt model.count) ]
    , button [ onClick Increment ] [ text "+" ]
    ]
```

## Main

```
main = Browser.sandbox { init = init, view = view, update = update }
```

Elmのエントリポイント(main)として、上記の `init`, `view`, `update` を `Browser.sandbox` に適用したものを渡す。

`Browser.sandbox`関数は`Program () model msg`を返す。これはアプリケーション全体を表す型である。

```
> Browser.sandbox
<function>
    : { init : model, update : msg -> model -> model, view : model -> Html msg }
      -> Program () model msg
```

`Browser.sandbox`は下図のような立ち位置にある。

![](https://guide.elm-lang.jp/effects/diagrams/sandbox.svg)

引用：https://guide.elm-lang.jp/effects/

Elmの世界で定義した`Html`をランタイムシステムに渡して実際にHTMLを描画させ、ランタイムシステム内でボタンがクリックされたりしたときその結果を`Msg`としてElmの世界に返してくれる。

# 参考文献
- 公式ドキュメント(翻訳ver)：https://guide.elm-lang.jp/
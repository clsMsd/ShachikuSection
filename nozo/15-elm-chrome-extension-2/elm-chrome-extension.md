# Elmでchrome拡張をつくる備忘録 その２

今回はchrome拡張の構成とそれをElmで生成する方法を調査する。

## chrome拡張の基本構成

chrome拡張は以下のスクリプト・HTMLで構成される。

- Background Script
  - ブラウザ全体で発生したイベントを処理するスクリプト。例えば、ページの移動、ブックマークの削除、タブを閉じるなどのイベントを検出することができる。
- UI Elements
  - 拡張のUI。拡張のアイコンをクリックすると表示されるポップアップがこれにあたる。その他にも右クリックメニュー、キーボードショートカット、omniboxなどを定義する。
- Content Script
  - ブラウザに表示されたページの内容にアクセスできるスクリプト。ページのDOM情報を取得したり、書き換えたりすることができる。
- Options Page
  - 拡張の設定画面。

また、以下のように各スクリプトは互いにメッセージを送受信することが可能である。

![](./img/messagingarc.png)

引用：https://developer.chrome.com/extensions/overview


# 参考文献
- Develop Extensions - Chrome: developer - Google Chrome, https://developer.chrome.com/extensions/devguide
- 公式ドキュメント(翻訳ver)：https://guide.elm-lang.jp/

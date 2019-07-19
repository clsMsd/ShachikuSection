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

## Elmの基礎

![](https://guide.elm-lang.jp/effects/diagrams/element.svg)

引用：https://guide.elm-lang.jp/effects/

# 参考文献
- [ファイアウォール ルールの使用 | VPC | Google Cloud](https://cloud.google.com/vpc/docs/using-firewalls?hl=ja)

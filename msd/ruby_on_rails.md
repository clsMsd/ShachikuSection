# 速習 Ruby on Rails

## はじめに
先日 "Ruby On Rails In 60 Minutes" という動画を見たので、Ruby on Railsについて紹介する。  

[Ruby On Rails In 60 Minutes](https://www.youtube.com/watch?v=pPy0GQJLZUM&t=536s)

### Ruby on Rails とは
> Rails is a web-application framework that includes everything needed to create database-backed web applications according to the Model-View-Controller (MVC) pattern.
([https://github.com/rails/rails] より引用)

Ruby on Rails (以下Rails) は 2000年代後半 ~ 2010年代前半 にかけて一世を風靡したWeb Application Frameworkであり、  
Ruby自体の普及にも大きな影響を及ぼした。  
よく言われるRailsの特徴として次のものが挙げられる
- MVCパターン:  
   GUIアプリケーションでよく用いられるMVCパターンを採用している…  
   と言いたいところだがRailsが採用しているのは正確には俗にMVC2と呼ばれるパターンでオリジナルのMVCパターンではない。
   さらにややこしいことにMVC2がGUIに逆輸入された…のかは良くわからないが、GUIアプリケーションの開発においてもMVC2のことを指して
   MVCと呼んでいる人もいて(というかそっちの方が多い?)完全にカオスな状況になっている
- モノリシック:  
   ルーティング、テンプレートエンジン、ORM等のWeb開発でほぼ必要と思われるひとまとまりの機能が入っている。
   例えばExpressでWebアプリを作成する場合、ORMは Sequelize, TypedORM, MongoDB などの選択肢があるが、
   Railsの場合はORMにはActiveRecordを使うということが決まっているので、好きなライブラリを自由に組み合わせて開発をしたいという
   人には向いていない。
- 設定よりも規約:  
   煩雑な設定を少なくするため、暗黙の規則が多い。  
   このため慣れている人には便利だが、慣れてない人には何が起きているのか全く分からないということになりがちである。  

以上の特徴から分かるように、Railsは  
「Railsが想定しているようなWebアプリをRailsが想定している作り方(Rails Way と俗に呼ばれる)で作ること」  
に特化しており開発の自由度は低い。  
その反面Railsを熟知している人間がRailsが想定した通りに作れば極めて迅速かつ効率的にWeb開発を行うことができる...と言われている。
(このような開発を俗に「Railに乗る」と言ったりする)

### 2019年にRailsは"あり"か?
ぶっちゃけると2019年現在で新規開発において Rails を採用する利点は  
(チームに既にRailsに詳しいエンジニアが複数人いるなどの理由がない限り)あまり無いと思う。  

Railsが時代にそぐわなくなった理由として次のようなものがよく挙げられる
- SPAで主な処理はブラウザ側で行うので、サーバー側はCRUD操作ができるAPIさえあればよい
- マイクロサービス時代にモノリシックなフレームワークは扱いづらい
- そもそもサーバーレスでやるので重いフレームワーク自体不要

参考:  
(「Railsは終わった」と言われる理由)[https://qiita.com/klriutsa/items/86ac5e94ec99c0d95b61]  
(Railsは2019年も「あり」か？#1（翻訳）)[https://techracho.bpsinc.jp/hachi8833/2019_01_25/68846]

一方でRailsを学ぶことには(2019年現在においても)次のような利点があると思われる。
1. 歴史の追体験  
   良くも悪くもRailsがWeb開発において与えた影響は大きいので、Railsを学ぶことでWeb開発の歴史を追体験できる  
   (この目的なら先に CGI + Perl をやる方が良いかもしれないが)
1. 他のFrameworkを学ぶ上での参考  
   Rails の影響を受けた Framework は多い(CakePHP, Laravel, Grails, ASP.NET MVC, Phoenix など)ので、  
   Rails を知っていると他の Framework をスムーズに学ぶことができる。
1. 資料が豊富  
   良くも悪くもWeb上の資料は豊富にある
1. Ruby3で静的型付けができるようになってRubyが再興する可能性がゼロではない  
   可能性がゼロではない、それはそう(未来は不確定なので)
1. その辺の会社で雇ってもらえそう  
   渋谷周辺にはRails使ってるイケイケWebベンチャーとかありそうなので、infocityが潰れてもRailsが出来ればbun
   その辺の会社で雇ってもらえる[要出典]  

なので、「がっつりリソースを注ぎ込んでバリバリ使いこなせるようになるメリット」は小さいが、  
「とりあえず触ってみて『あーそういうことねRails完全に理解した(わかってない)』状態になるメリット」はそこそこあると思う。  

## 環境構築

1. ruby のインストール
1. rails のインストール

```bash
$ gem install rails
```

## 基礎編

### プロジェクトの作成
```bash
$ rails new SimpleBlog
...(色々表示)
$ cd SimpleBlog
```

### サーバーの起動
```
rails server
```
又は
```
rails s
```

`http://localhost:3000/`を開いてスタートページが立ち上がればOK

### ルーティングの設定(Hello World)

/app/controllers/application_controller.rb
```ruby
class ApplicationController < ActionController::Base
    def hello
        render plain: "hello"
    end
end
```

/config/routes.rb
```ruby
Rails.application.routes.draw do
  root "application#hello"
end
```

http://localhost:3000/hello 
```ruby
Rails.application.routes.draw do
  get "/hello", to: "application#hello"

  # 又は
  get "/hello" => "application#hello"
end
```

### ERBファイルの描画

/app/controllers/application_controller.rb
```ruby
class ApplicationController < ActionController::Base
    def hello
        render "/hello"
    end
end
```

/app/views/hello.html.erb
```html
<h1>HELLO</h1>
```

#### テンプレートに引数を渡す場合

/app/controllers/application_controller.rb
```ruby
class ApplicationController < ActionController::Base
    def hello
        @foo = "FOO"
        render "/hello"
    end
end
```

```erb
<h1>Hello</h1>
<p><%= @foo %></p>
```

### controllerの作成
`rails generate controller (コントローラー名)` 又は `rails g controller (コントローラー名)` でコントローラーを作成する。  

```bash
$ rails generate controller foo

Running via Spring preloader in process 67434
      create  app/controllers/foo_controller.rb
      invoke  erb
      create    app/views/foo
      invoke  test_unit
      create    test/controllers/foo_controller_test.rb
      invoke  helper
      create    app/helpers/foo_helper.rb
      invoke    test_unit
      invoke  assets
      invoke    scss
      create      app/assets/stylesheets/foo.scss
```

コマンド一発で
- コントローラー
- ビュー(ERBファイル)
- テスト
- ヘルパー
- スタイルシート

が生成される。  
railsのコマンドはこのように一発で必要なファイルをまとめて生成してくれるものが多いため、  
慣れている人にとっては便利な反面、慣れていない人にとっては何が起きているのが分かりにくいので注意が必要である。

自動生成したこれらのファイルを一括で削除する場合は、 `rails delete controller コントローラー名` 又は `rails d controller コントローラー名` と打てばよい。

```bash
$ rails g controller foo index                     

Running via Spring preloader in process 67684
      create  app/controllers/foo_controller.rb
       route  get 'foo/index'
      invoke  erb
      create    app/views/foo
      create    app/views/foo/index.html.erb
      invoke  test_unit
      create    test/controllers/foo_controller_test.rb
      invoke  helper
      create    app/helpers/foo_helper.rb
      invoke    test_unit
      invoke  assets
      invoke    scss
      create      app/assets/stylesheets/foo.scss
```

#### アクションとresoucesとresource
Controller にはアクションと呼ばれるリソースの操作のための7つのメソッドがある。  

routes.rb
```ruby
Rails.application.routes.draw do
  resources :photos
end
```

|HTTP動詞|パス|コントローラ#アクション|目的|
|:--|:--|:--|:--|
|GET|/photos|photos#index|すべての写真の一覧を表示|
|GET|/photos/new|photos#new|写真を1つ作成するためのHTMLフォームを返す|
|POST|/photos|photos#create|写真を1つ作成する|
|GET|/photos/:id|photos#show|特定の写真を表示する|
|GET|/photos/:id/edit|photos#edit|写真編集用のHTMLフォームを1つ返す|
|PATCH/PUT|/photos/:id|photos#update|特定の写真を更新する|
|DELETE|/photos/:id|photos#destroy|特定の写真を削除する|
([https://railsguides.jp/routing.html#crud%E3%80%81%E5%8B%95%E8%A9%9E%E3%80%81%E3%82%A2%E3%82%AF%E3%82%B7%E3%83%A7%E3%83%B3]より引用)


概念的に複数のリソースではなく単一のリソースを扱う場合は、`resources`の代わりに`resource`を使う

routes.rb
```ruby
Rails.application.routes.draw do
  resource :photo
end
```

|HTTP動詞|パス|コントローラ#アクション|目的|
|:--|:--|:--|:--|
|GET|/photo|photos#show|写真を表示|
|GET|/photo/new|photos#new|写真を作成するためのHTMLフォームを返す|
|POST|/photo|photos#create|写真を作成する|
|GET|/photos/edit|photos#edit|写真編集用のHTMLフォームを返す|
|PATCH/PUT|/photos|photos#update|写真を更新する|
|DELETE|/photos|photos#destroy|写真を削除する|

### modelの作成
`rails g model (モデル名) (カラム名):(データ型) (カラム名):(データ型) ...`  
例
```bash
rails g model Book title:string author:string publisher:string
```
このコマンドを実行するとRubyのソースファイルとしてのModelは生成されるが、  
Modelに対応するDB上のテーブルはまだ生成されない。  
DB上にテーブルを生成するには次のコマンドを実行する。

```
rake db:migrate
```

RailsのModelはiOSアプリで言うところの Model(ドメインロジックの置き場) + Entity(扱うデータの型) + Repository(DBアクセスのラッパー)
が合体したようなものである。  

### scaffold
一発でModel, View, Controller 全ての雛形を作ってくれる。  

```bash
$ rails g scaffold Comment author:string body:text
/home/masuda/.rbenv/versions/2.6.4/lib/ruby/gems/2.6.0/gems/railties-6.0.0/lib/rails/app_loader.rb:53: warning: Insecure world writable dir /home/masuda/.rbenv/versions in PATH, mode 040777
/home/masuda/.rbenv/versions/2.6.4/bin/ruby: warning: shebang line ending with \r may cause problems
Running via Spring preloader in process 618
      invoke  active_record
      create    db/migrate/20190910120217_create_comments.rb
      create    app/models/comment.rb
      invoke    test_unit
      create      test/models/comment_test.rb
      create      test/fixtures/comments.yml
      invoke  resource_route
       route    resources :comments
      invoke  scaffold_controller
      create    app/controllers/comments_controller.rb
      invoke    erb
      create      app/views/comments
      create      app/views/comments/index.html.erb
      create      app/views/comments/edit.html.erb
      create      app/views/comments/show.html.erb
      create      app/views/comments/new.html.erb
      create      app/views/comments/_form.html.erb
      invoke    test_unit
      create      test/controllers/comments_controller_test.rb
      create      test/system/comments_test.rb
      invoke    helper
      create      app/helpers/comments_helper.rb
      invoke      test_unit
      invoke    jbuilder
      create      app/views/comments/index.json.jbuilder
      create      app/views/comments/show.json.jbuilder
      create      app/views/comments/_comment.json.jbuilder
      invoke  assets
      invoke    scss
      create      app/assets/stylesheets/comments.scss
      invoke  scss
      create    app/assets/stylesheets/scaffolds.scss
```

## 実践編
今回は元ネタの動画を踏襲してRailsで簡単なブログを作成してみる。  

まずはプロジェクトの作成
```
$ rails new SimpleBlog
(...いっぱい出力...)
$ cd SimpleBlog
$ bundle install
```

記事画面を管理するコントローラーを作成する
```
$ rails g controller Posts
```

ルーティングの設定も行う
```ruby
Rails.application.routes.draw do
  resources :posts
end
```

/app/views/posts/index.erb.html
```html
<h1>Posts <h1/>
```

ブラウザで `http://localhost:3000/posts` を開いて `Posts` と表示されていればOK。  

次にブログ記事の投稿画面を作成する。
/app/views/posts/new.erb.html
```html
<h1>Add Post</h1>
<%= form_for :post, url: posts_path do |f| %>
    <%= f.label :title %><br/>
    <%= f.text_field :title %><br/>
    <%= f.label :body %><br/>
    <%= f.text_area :body %><br/>
    <%= f.submit %>
<% end %>
```

ブラウザで `http://localhost:3000/posts/new` を開いてみて作成したHTMLフォームが表示されていればOK

次に投稿を管理するためのモデルを作成する
```
$ rails g model Post title:string body:text
$ rake db:migrate
```

コントローラーでユーザーからの入力を受け取り、DBに保存する
```ruby
class PostsController < ApplicationController
   def create
      @post = Post.new(title: params[:post][:title], body: params[:post][:body])
      @post.save
   end
end
```

ブログの記事を表示するページを作る
/app/views/posts/show.erb.html
```html
<h2><%= @post.title %></h2>
<p><%= @post.body %></p>
```

/app/views/posts/index.erb.html
```html
<h1>Blog Posts</h1>
<% @posts.each do |post| %>
  <h3><%= post.title %></h3>
  <p><%= post.body %></p>
<% end %>
```

```ruby
class PostsController < ApplicationController
   def index
      @posts = Post.all
   end

   def show
      @post = Post.find(params[:id])
   end

   def create
      @post = Post.new(title: params[:post][:title], body: params[:post][:body])
      @post.save
      redirect_to @post
   end
end
```

これで最低限ブログっぽいものはできた。  

次に見栄えを良くするためにBootstrapを使う。  

/app/views/layouts/application.html.erb
```html
<!DOCTYPE html>
<html>
  <head>
    <title>Rorblog</title>
    <%= csrf_meta_tags %>
    <%= csp_meta_tag %>
    
    <%= stylesheet_link_tag 'https://stackpath.bootstrapcdn.com/bootstrap/4.3.1/css/bootstrap.min.css' %>
    <%= stylesheet_link_tag 'application', media: 'all', 'data-turbolinks-track': 'reload' %>
    <%= javascript_pack_tag 'application', 'data-turbolinks-track': 'reload' %>
  </head>

  <body>
    <nav class="navbar navbar-expand-md navbar-dark bg-dark">
      <div class="container">

      <span class="navbar-brand">Simple Blog</span>

      <div class="collapse navbar-collapse">
        <ul class="navbar-nav mr-auto">
          <li class="nav-item active">
            <%= link_to "Home", posts_path, {:class => "nav-link"} %>
          </li>
        </ul>
        <ul class="navbar-nav navbar-right">
          <li class="nav-item active">
          <%= link_to "Create Post", new_post_path, {:class => "nav-link"} %>
          </li>
        </ul>
      </div>
      </div>
    </nav>
    <div class="container">
      <%= yield %>
    </div>
  </body>
</html>
```

/app/views/posts/new.html.erb
```html
<h1>Add Post</h1>
<%= form_for :post, url: posts_path do |f| %>
    <%= f.label :title %><br/>
    <%= f.text_field :title, {:class => "form-control"} %><br/>
    <%= f.label :body %><br/>
    <%= f.text_area :body, {:class => "form-control"} %><br/>
    <%= f.submit({:class => "btn btn-primary"}) %>
<% end %>
```

/app/view/posts/index.html.erb
```html
<h1>Blog Posts</h1>
<% @posts.each do |post| %>
    <div class="card" style="margin-top: 1rem;">
      <div class="card-body">
        <h2 class="card-title"><%= post.title %></h2>
        <p class="card-text"><%= post.body %></p>
      </div>
    </div>
<% end %>
```

/app/view/posts/show.html.erb
```html
<div class="card" style="margin-top: 1rem;">
  <div class="card-body">
    <h2 class="card-title"><%= @post.title %></h2>
    <p class="card-text"><%= @post.body %></p>
  </div>
</div>
```

これでなんかそれっぽいデザインになる。  

次にValidationを追加してみる。  
今回は titleは5文字以上、bodyは10文字以上という制約を加えてみる。  

/app/models/post.rb
```ruby
class Post < ApplicationRecord
    validates :title, presence: true, length: {minimum: 5}
    validates :body, presence: true, length: {minimum: 10}
end
```

これで titleとbodyが制約を満たしていない場合に保存が失敗するようになった。  

失敗時にユーザーに再入力を求めるようにメッセージを表示するようにする。

/app/views/posts/new.html.erb
```html
<h1>Add Post</h1>
<%= form_for :post, url: posts_path do |f| %>
    <% if @post.errors.any? %>
        <% @post.errors.full_messages.each do |msg| %>
            <div class="alert alert-danger"><%= msg %></div>
        <% end %>
    <% end %>
    <%= f.label :title %><br/>
    <%= f.text_field(:title, {:class => "form-control"}) %><br/>
    <%= f.label :body %><br/>
    <%= f.text_area(:body, {:class => "form-control"}) %><br/>
    <%= f.submit({:class => "btn btn-primary"}) %>
<% end %>
```

/app/controllers/posts_controller.rb
```ruby
class PostsController < ApplicationController
   def index
      @posts = Post.all
   end

   def show
      @post = Post.find(params[:id])
   end

   def new
      @post = Post.new
   end

   def create
      @post = Post.new(title: params[:post][:title], body: params[:post][:body])

      if (@post.save)
         # redirect_to "/posts/#{@post.id}" と同じ意味
         redirect_to @post
      else
         render "new"
      end
   end
end
```

失敗時にはエラーメッセージが表示されるようになった。  

次に投稿を編集・削除できるようにする。  

まず index 画面から個々のpostへ飛べるようにリンクボタンを追加する。    
/app/views/posts/index.html.erb
```html
<h1>Blog Posts</h1>
<% @posts.each do |post| %>
    <div class="card" style="margin-top: 1rem;">
      <div class="card-body">
        <h2 class="card-title"><%= post.title %></h2>
        <p class="card-text"><%= post.body %></p>
        <%= link_to "Read More", post_path(post), :class => "btn btn-secondary" %>
      </div>
    </div>
<% end %>
```

次に個々のpost画面に編集・削除ボタンを追加する。  
/app/views/posts/show.html.erb
```html
<div class="card" style="margin-top: 1rem;">
  <div class="card-body">
    <h2 class="card-title"><%= @post.title %></h2>
    <p class="card-text"><%= @post.body %></p>
  </div>
</div>
<hr/>
<%= link_to "Edit", edit_post_path(@post), :class => "btn btn-secondary"%>
<%= link_to "Delete", post_path(@post), method: :delete, data: {confirm: "Are you sure?"}, :class => "btn btn-danger" %>
```

/app/controllers/posts_controller.rb
```ruby
class PostsController < ApplicationController
   def index
      @posts = Post.all
   end

   def show
      @post = Post.find(params[:id])
   end

   def new
      @post = Post.new
   end

   def create
      @post = Post.new(title: params[:post][:title], body: params[:post][:body])

      if (@post.save)
         # redirect_to "/posts/#{@post.id}" と同じ意味
         redirect_to @post
      else
         render "new"
      end
   end

   def edit
      @post = Post.find(params[:id])
   end

   def update
      @post = Post.find(params[:id])

      if (@post.update(title: params[:post][:title], body: params[:post][:body]))
         redirect_to @post
      else
         render "edit"
      end
   end

   def destroy
      @post = Post.find(params[:id])
      @post.destroy
      redirect_to posts_path
   end
end
```

これ投稿の編集・削除ができるようになった。  

最後に誰でも投稿できるとまずいので、認証機能を追加する。  
今回は簡単にhttpのbasic認証を使う。  

/app/controllers/posts_controller.rb
```ruby
class PostsController < ApplicationController
   http_basic_authenticate_with name: "admin", password: "psword", except: [:index, :show]
   
   ...(以下同じ)
```

これで投稿の閲覧以外の操作を行うには認証を受けなければならないようになった。  

## まとめ
君も未経験からRailsエンジニアになって転職してバラ色の人生を送ろう！！！  
参考:  
[https://www.sejuku.net/]
